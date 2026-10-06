"""Rebuild, check exact statements and axioms, audit the direct route, and replay Lean's kernel."""
from pathlib import Path
import hashlib, json, platform, re, subprocess, sys, time

ROOT = Path(__file__).resolve().parent.parent
LOGS = ROOT / 'verification'
LOGS.mkdir(exist_ok=True)
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
START = time.time()
# Never leave a stale success flag in place after a failed rerun.
previous = LOGS / 'current-run.json'
if previous.exists():
    previous.replace(LOGS / 'previous-run.json')

def code_only(text):
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i): depth += 1; i += 2
        elif depth and text.startswith('-/', i): depth -= 1; i += 2
        elif depth: i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i); i = len(text) if j < 0 else j
        else: out.append(text[i]); i += 1
    if depth: raise RuntimeError('Unclosed block comment')
    return ''.join(out)

def run(cmd, log):
    r = subprocess.run(cmd, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (LOGS / log).write_text(r.stdout)
    if r.returncode:
        print(r.stdout, flush=True)
        raise RuntimeError(f'{cmd}: exit {r.returncode}')
    return r.stdout

def snapshot():
    paths = [*ROOT.glob('Riesz/*.lean'), *ROOT.glob('Oscillation/*.lean'), ROOT/'Oscillation.lean',
        ROOT/'lean-toolchain',ROOT/'lakefile.toml',ROOT/'lake-manifest.json',
        ROOT/'README.md',ROOT/'PROOF_MAP.md',*ROOT.glob('scripts/*.lean'),
        *ROOT.glob('scripts/*.py'),*ROOT.glob('*.sh'),ROOT/'verification/manuscript-r65.json',
        ROOT/'verification/tusnady-plane-stoc27-vC-r65.tex',
        ROOT/'verification/tusnady-plane-stoc27-vC-r65.pdf',ROOT/'AUDIT_R65.md',ROOT/'.gitignore',ROOT/'LICENSE',ROOT/'CITATION.cff',
        ROOT/'MANUSCRIPT_LICENSE.md',ROOT/'.github/workflows/verify.yml']
    if any(p.is_symlink() for p in paths): raise RuntimeError('Symlink in verified source inputs')
    return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)}

source_meta=json.loads((ROOT/'verification/manuscript-r65.json').read_text())
for name,key in [(source_meta['source_pdf'],'sha256'),(source_meta['source_tex'],'tex_sha256')]:
    if hashlib.sha256((LOGS/name).read_bytes()).hexdigest()!=source_meta[key]:
        raise RuntimeError('Manuscript hash mismatch: '+name)
before=snapshot()

sources = sorted([*ROOT.glob('Riesz/*.lean'), *ROOT.glob('Oscillation/*.lean'), ROOT/'Oscillation.lean'])
for p in sources + [ROOT/'scripts/Completion.lean']:
    text = code_only(p.read_text())
    if re.search(r'\b(sorry|admit|axiom|unsafe|partial|native_decide|run_tac|run_cmd|elab|macro|syntax)\b|implemented_by|extern', text):
        raise RuntimeError(f'Forbidden proof construction in {p}')
modules = [str(p.relative_to(ROOT).with_suffix('')).replace('/','.') for p in sources]
version = run(['lake','env','lean','--version'], 'lean-version.log').strip()
if 'version 4.34.1,' not in version: raise RuntimeError(version)
manifest = json.loads((ROOT/'lake-manifest.json').read_text())
deps=[]
for package in manifest['packages']:
    p=ROOT/'.lake/packages'/package['name']
    revision=subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()
    dirty=subprocess.check_output(['git','-C',str(p),'status','--porcelain'],text=True).strip()
    if revision != package['rev'] or dirty: raise RuntimeError(f'Dependency changed: {package["name"]}')
    deps.append({'name':package['name'],'revision':revision,'dirty':False})
(LOGS/'dependency-state.json').write_text(json.dumps(deps,indent=2)+'\n')
print('Pinned toolchain and dependencies checked.',flush=True)
run(['lake','build',*modules], 'build.log')
print(f'Built all {len(modules)} local modules.',flush=True)
out=run(['lake','env','lean','scripts/DirectDependencies.lean'],'direct-dependencies.log')
imported=set(re.findall(r'^MODULE (.+)$',out,re.M))
if set(modules)-imported-{'Oscillation'}:
    raise RuntimeError(f'Unaudited modules: {set(modules)-imported}')
names=sorted(set(re.findall(r'^THEOREM (.+)$',out,re.M)))
print('Main theorem uses the r65 all-transition union route; r17 sequential crowding and older global routes excluded.',flush=True)

for filename, log, expected in [('scripts/Axioms.lean','axioms.log',len(names)),('scripts/Completion.lean','completion.log',8)]:
    out=run(['lake','env','lean','-DautoImplicit=false',filename],log)
    if filename.endswith('Axioms.lean'):
        entries=re.findall(r'^AXIOMS (.*?) \[([^\]]*)\]$',out,re.M)
        if {name for name,_ in entries} != set(names): raise RuntimeError('Axiom coverage mismatch')
        reports=[report for _,report in entries]
        report_count=len({name for name,_ in entries})
    else:
        reports=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',out)
        reports += ['']*len(re.findall('does not depend on any axioms',out))
        report_count=len(reports)
    if report_count!=expected: raise RuntimeError(f'{log}: expected {expected} reports, got {report_count}')
    for report in reports:
        actual={x.strip() for x in report.split(',') if x.strip()}
        if actual-ALLOWED: raise RuntimeError(f'{log}: unexpected axioms {actual-ALLOWED}')
    print(f'{filename}: {expected} axiom reports passed.',flush=True)
replay=[]
if '--replay' in sys.argv:
    with (LOGS/'replay.log').open('w') as f:
        replay_modules = [m for m in modules if m != "Oscillation"]
        for i,module in enumerate(replay_modules):
            r=subprocess.run(['lake','env','leanchecker',module],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            row={'module':module,'exit_code':r.returncode,'output':r.stdout}
            replay.append(row)
            f.write(json.dumps(row)+'\n'); f.flush()
            if r.returncode: raise RuntimeError(f'Kernel replay failed: {row}')
            print(f'Kernel replay {i+1}/{len(replay_modules)}: {module}',flush=True)
if snapshot()!=before: raise RuntimeError('Sources changed during verification; rerun.')
(LOGS/'source-sha256.json').write_text(json.dumps(before,indent=2)+'\n')
summary={'passed':True,'time_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
    'schema_version':2,'manuscript_sha256':source_meta['sha256'],'manuscript_tex_sha256':source_meta['tex_sha256'],'elapsed_seconds':round(time.time()-START,1),'platform':platform.platform(),'git_commit':subprocess.run(['git','rev-parse','HEAD'],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL).stdout.strip() or None,'lean':version,
    'local_modules':len(modules),'theorems_audited':len(names),'completion_gates':8,
    'allowed_axioms':sorted(ALLOWED),'main_route':'even-base average-before-maximum gain + all-transition union + bounded differences',
    'legacy_global_route_used':False,'github_run_id':__import__('os').environ.get('GITHUB_RUN_ID'),'kernel_replay':{'requested':'--replay' in sys.argv,'passed_modules':len(replay)},
    'warnings':[line for line in (LOGS/'build.log').read_text().splitlines() if line.startswith('warning:')],
    'replay_results':[{'module':r['module'],'exit_code':r['exit_code']} for r in replay],
    'log_sha256':{str(p.name):hashlib.sha256(p.read_bytes()).hexdigest() for p in LOGS.glob('*.log')}}
summary['record_sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(LOGS.iterdir()) if p.suffix in ('.log','.json') and p.name not in ('current-run.json','previous-run.json','package-sha256.json','manuscript-r65.json')}
(LOGS/'current-run.json').write_text(json.dumps(summary,indent=2)+'\n')
print('VERIFIED: exact theorem statements, standard axioms, direct proof dependencies'+', kernel replay.'*bool(replay),flush=True)
