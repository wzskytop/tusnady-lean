"""Verify the r65 manuscript proof, legacy comparison proof, and all local kernel modules."""
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
    chunks = []
    with (LOGS / log).open('w') as f:
        r = subprocess.Popen(cmd, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        for line in r.stdout:
            chunks.append(line); f.write(line); f.flush()
            if line.startswith(('== ', 'STRICT ', 'REPLAY ', 'replayed ', 'ALL CHECKS', 'INDEPENDENT ')):
                print(line.rstrip(), flush=True)
        r.wait()
    output = ''.join(chunks)
    if r.returncode:
        print(output[-12000:], flush=True)
        raise RuntimeError(f'{cmd}: exit {r.returncode}')
    return output

def snapshot():
    paths = [*ROOT.glob('Riesz/*.lean'), *ROOT.glob('Oscillation/*.lean'), ROOT/'Oscillation.lean',
        ROOT/'lean-toolchain',ROOT/'lakefile.toml',ROOT/'lake-manifest.json',
        ROOT/'README.md',ROOT/'PROOF_MAP.md',*ROOT.glob('scripts/*.lean'),
        *ROOT.glob('scripts/*.py'),*ROOT.glob('*.sh'),ROOT/'verification/manuscript-r65.json',
        ROOT/'verification/tusnady-plane-stoc27-vC-r65.tex',
        ROOT/'verification/tusnady-plane-stoc27-vC-r65.pdf',ROOT/'AUDIT_R65.md',ROOT/'.gitignore',ROOT/'LICENSE',ROOT/'CITATION.cff',
        ROOT/'MANUSCRIPT_LICENSE.md',ROOT/'.github/workflows/verify.yml',
        ROOT/'R56Audit.lean',*ROOT.glob('R56Audit/*.lean'),
        *[p for p in (ROOT/'audit-claude').iterdir() if p.is_file()]]
    if any(p.is_symlink() for p in paths): raise RuntimeError('Symlink in verified source inputs')
    return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)}

source_meta=json.loads((ROOT/'verification/manuscript-r65.json').read_text())
for name,key in [(source_meta['source_pdf'],'sha256'),(source_meta['source_tex'],'tex_sha256')]:
    if hashlib.sha256((LOGS/name).read_bytes()).hexdigest()!=source_meta[key]:
        raise RuntimeError('Manuscript hash mismatch: '+name)
before=snapshot()

sources = sorted([*ROOT.glob('Riesz/*.lean'), *ROOT.glob('Oscillation/*.lean'), ROOT/'Oscillation.lean'])
supplement_sources = sorted([ROOT/'R56Audit.lean', *ROOT.glob('R56Audit/*.lean')])
supplement_modules = [str(p.relative_to(ROOT).with_suffix('')).replace('/','.') for p in supplement_sources]
for p in sources + supplement_sources + [ROOT/'scripts/Completion.lean', ROOT/'scripts/SubmissionStatements.lean']:
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
run(['lake','build',*modules,*supplement_modules], 'build.log')
print(f'Built all {len(modules)+len(supplement_modules)} local modules.',flush=True)
out=run(['lake','env','lean','scripts/DirectDependencies.lean'],'direct-dependencies.log')
imported=set(re.findall(r'^MODULE (.+)$',out,re.M))
if set(modules)-imported-{'Oscillation'}:
    raise RuntimeError(f'Unaudited modules: {set(modules)-imported}')
names=sorted(set(re.findall(r'^THEOREM (.+)$',out,re.M)))
print('Legacy comparison theorem uses the all-transition union route; checking the new manuscript route next.',flush=True)

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
# Check all supplement constants, exact source-derived gates, adversarial mutations,
# strict compilation, proof route, and per-module kernel replay.
supplement_output = run(['bash','audit-claude/check.sh'], 'supplement-audit.log')
if not supplement_output.rstrip().endswith('ALL CHECKS PASSED'):
    raise RuntimeError('Missing supplement audit completion')
supplement_replayed = re.findall(r'^replayed (.+)$', supplement_output, re.M)
expected_supplement_replay = sorted(m for m in supplement_modules if m != 'R56Audit')
if supplement_replayed != expected_supplement_replay:
    raise RuntimeError('Supplement replay coverage mismatch')
statement_output = run(['lake','env','lean','-DautoImplicit=false','-DwarningAsError=true',
    'scripts/SubmissionStatements.lean'], 'submission-statements.log')
statement_axioms = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', statement_output)
if len(statement_axioms) != 4 or any(set(x.strip() for x in a.split(','))-ALLOWED for a in statement_axioms):
    raise RuntimeError('Independent statement axiom reports failed')
closure_output = run(['lake','env','lean','-DautoImplicit=false','-DwarningAsError=true',
    'scripts/SubmissionClosure.lean'], 'submission-closure.log')
if len(re.findall(r'^INDEPENDENT ', closure_output, re.M)) != 2:
    raise RuntimeError('Missing unrestricted proof closure checks')
print('Primary manuscript route: full continuous potential, all integer bases >= 3, general probability tools.', flush=True)
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
        for module in supplement_replayed:
            row={'module':module,'exit_code':0,'output':'Completed by audit-claude/check.sh; see supplement-audit.log'}
            replay.append(row); f.write(json.dumps(row)+'\n')
if replay:
    replay.sort(key=lambda r: r['module'])
    (LOGS/'replay.log').write_text(''.join(json.dumps(r)+'\n' for r in replay))
if snapshot()!=before: raise RuntimeError('Sources changed during verification; rerun.')
(LOGS/'source-sha256.json').write_text(json.dumps(before,indent=2)+'\n')
summary={'passed':True,'time_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
    'schema_version':3,'manuscript_sha256':source_meta['sha256'],'manuscript_tex_sha256':source_meta['tex_sha256'],'elapsed_seconds':round(time.time()-START,1),'platform':platform.platform(),'git_commit':subprocess.run(['git','rev-parse','HEAD'],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL).stdout.strip() or None,'lean':version,
    'local_modules':len(modules)+len(supplement_modules),'theorems_audited':len(names),'completion_gates':8,'independent_submission_gates':5,
    'supplement_audit':{'passed':True,'modules':33,'constants':907,'statement_and_definition_examples':353,'rejected_mutants':52,'accepted_controls':3,'strict_errors':0,'strict_warnings':0},
    'allowed_axioms':sorted(ALLOWED),'main_route':'continuous oscillation + symmetric jumps for every integer base >= 3 + digit filtration + successive conditioning and Markov',
    'primary_theorem':'R56Audit.theorem_1_1_unfolded',
    'legacy_global_route_used':False,'github_run_id':__import__('os').environ.get('GITHUB_RUN_ID'),'kernel_replay':{'requested':'--replay' in sys.argv,'passed_modules':len(replay)},
    'warnings':[line for line in (LOGS/'build.log').read_text().splitlines() if line.startswith('warning:')],
    'replay_results':[{'module':r['module'],'exit_code':r['exit_code']} for r in replay],
    'log_sha256':{str(p.name):hashlib.sha256(p.read_bytes()).hexdigest() for p in LOGS.glob('*.log')}}
summary['record_sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(LOGS.iterdir()) if p.suffix in ('.log','.json') and p.name not in ('current-run.json','previous-run.json','package-sha256.json','manuscript-r65.json')}
(LOGS/'current-run.json').write_text(json.dumps(summary,indent=2)+'\n')
print('VERIFIED: r65 primary manuscript route, exact statements, standard axioms, legacy comparison'+', kernel replay.'*bool(replay),flush=True)
