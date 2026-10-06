"""Package the exact current verified sources and replay evidence; never .lake files."""
from pathlib import Path, PurePosixPath
import hashlib, json, os, sys, tempfile, zipfile

ROOT = Path(__file__).resolve().parent.parent
LOGS = ROOT / 'verification'

def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('Duplicate JSON key: ' + key)
        result[key] = value
    return result

def parse(data):
    return json.loads(data, object_pairs_hook=unique_object)

def digest(data):
    return hashlib.sha256(data).hexdigest()

cache = {}
def read(name):
    p = PurePosixPath(name)
    if p.is_absolute() or '..' in p.parts or str(p) != name:
        raise ValueError('Invalid relative path: ' + name)
    path = ROOT / name
    if any(parent.is_symlink() for parent in [path, *path.parents] if parent != ROOT and ROOT in parent.parents):
        raise ValueError('Symlink input: ' + name)
    if name not in cache:
        cache[name] = path.read_bytes()
    return cache[name]

run = parse(read('verification/current-run.json'))
if run.get('schema_version') != 2 or run.get('passed') is not True:
    raise ValueError('A current successful r65 verification is required')
expected_sources = {str(p.relative_to(ROOT)) for p in [
    *ROOT.glob('Riesz/*.lean'), *ROOT.glob('Oscillation/*.lean'), ROOT/'Oscillation.lean',
    ROOT/'lean-toolchain', ROOT/'lakefile.toml', ROOT/'lake-manifest.json',
    ROOT/'README.md', ROOT/'PROOF_MAP.md', *ROOT.glob('scripts/*.lean'),
    *ROOT.glob('scripts/*.py'), *ROOT.glob('*.sh'), ROOT/'.gitignore', ROOT/'AUDIT_R65.md', ROOT/'LICENSE', ROOT/'CITATION.cff',
    ROOT/'MANUSCRIPT_LICENSE.md', ROOT/'.github/workflows/verify.yml',
    LOGS/'manuscript-r65.json', LOGS/'tusnady-plane-stoc27-vC-r65.tex',
    LOGS/'tusnady-plane-stoc27-vC-r65.pdf']}
manifest = parse(read('verification/source-sha256.json'))
if set(manifest) != expected_sources:
    raise ValueError('Source file set changed; rerun verification')
for name, value in manifest.items():
    if digest(read(name)) != value:
        raise ValueError('Source changed: ' + name)
records = {'lean-version.log', 'build.log', 'direct-dependencies.log', 'axioms.log',
           'completion.log', 'replay.log', 'dependency-state.json', 'source-sha256.json'}
if set(run.get('record_sha256', {})) != records:
    raise ValueError('Incomplete or extra verification record hashes')
for name, value in run['record_sha256'].items():
    if digest(read('verification/' + name)) != value:
        raise ValueError('Record changed: ' + name)
log_names = {s for s in records if s.endswith('.log')}
if set(run.get('log_sha256', {})) != log_names:
    raise ValueError('Unexpected log hash set')
for name, value in run['log_sha256'].items():
    if value != run['record_sha256'][name]:
        raise ValueError('Conflicting record hashes')
modules = sorted(s[:-5].replace('/', '.') for s in expected_sources
                 if s.endswith('.lean') and s.startswith(('Oscillation/', 'Riesz/')))
replay = [parse(line) for line in read('verification/replay.log').decode().split('\n') if line]
expected = [{'module': name, 'exit_code': 0} for name in modules]
if run.get('replay_results') != expected or any(type(r.get('exit_code')) is not int for r in run['replay_results']):
    raise ValueError('Incomplete or failed replay results')
if len(replay) != len(modules):
    raise ValueError('Incomplete replay log')
for row, name in zip(replay, modules):
    if (set(row) != {'module','exit_code','output'} or row['module'] != name
            or type(row['exit_code']) is not int or row['exit_code'] != 0 or not isinstance(row['output'], str)):
        raise ValueError('Invalid replay entry: ' + name)
for key, value in [('local_modules', len(modules)+1), ('completion_gates', 8)]:
    if type(run.get(key)) is not int or run[key] != value:
        raise ValueError('Invalid count: ' + key)
kernel = run.get('kernel_replay', {})
if kernel.get('requested') is not True or type(kernel.get('passed_modules')) is not int or kernel['passed_modules'] != len(modules):
    raise ValueError('Full kernel replay is required')
meta = parse(read('verification/manuscript-r65.json'))
if meta.get('version') != 'r65' or run['manuscript_sha256'] != meta['sha256'] or run['manuscript_tex_sha256'] != meta['tex_sha256']:
    raise ValueError('Wrong manuscript version')
for name, key in [('tusnady-plane-stoc27-vC-r65.tex','tex_sha256'),('tusnady-plane-stoc27-vC-r65.pdf','sha256')]:
    if digest(read('verification/'+name)) != meta[key]:
        raise ValueError('Manuscript mismatch')
output = Path(sys.argv[1] if len(sys.argv)>1 else ROOT.parent/'tusnady-r65-lean-verified.zip').resolve()
if output.suffix != '.zip' or output == ROOT or ROOT in output.parents:
    raise ValueError('ZIP output must be outside the verified project')
output.parent.mkdir(parents=True, exist_ok=True)
manifest_bytes = (json.dumps({name:digest(data) for name,data in sorted(cache.items())},indent=2)+'\n').encode()
fd, temp_name = tempfile.mkstemp(prefix='.'+output.name+'.', suffix='.tmp', dir=output.parent)
try:
    with os.fdopen(fd, 'wb') as stream:
        with zipfile.ZipFile(stream, 'w', zipfile.ZIP_DEFLATED) as archive:
            for name, data in sorted(cache.items()):
                archive.writestr(ROOT.name+'/'+name, data)
            archive.writestr(ROOT.name+'/verification/package-sha256.json', manifest_bytes)
    os.replace(temp_name, output)
finally:
    if os.path.exists(temp_name):
        os.unlink(temp_name)
print(json.dumps({'zip':str(output),'files':len(cache)+1,'sha256':digest(output.read_bytes())},indent=2))
