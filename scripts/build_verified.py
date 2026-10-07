"""Build local proof modules in dependency order, then the umbrella library.

Run verify.py for the independent, no-premise main-theorem completion gate.
"""
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
sources = {str(p.relative_to(ROOT).with_suffix('')).replace('/', '.'): p
           for folder in ('Riesz', 'Oscillation', 'R56Audit') for p in (ROOT / folder).glob('*.lean')}
ordered, visiting, visited = [], set(), set()

def visit(name):
    if name in visited:
        return
    if name in visiting:
        raise SystemExit(f'Import cycle at {name}')
    visiting.add(name)
    for dependency in re.findall(r'^import\s+([\w.]+)', sources[name].read_text(), re.M):
        if dependency in sources:
            visit(dependency)
    visiting.remove(name)
    visited.add(name)
    ordered.append(name)

for name in sorted(sources):
    visit(name)

log = ROOT / 'verification/build.log'
log.parent.mkdir(exist_ok=True)
with log.open('w') as out:
    for name in ordered + ['Oscillation', 'R56Audit']:
        result = subprocess.run(['lake', 'build', name], cwd=ROOT, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        out.write('TARGET ' + name + '\n' + result.stdout + '\n')
        out.flush()
        print(name, 'exit', result.returncode, flush=True)
        if result.returncode:
            print(result.stdout, flush=True)
            sys.exit(result.returncode)
