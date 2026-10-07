"""Source scan (auditor's script; reads the sources as data).

Usage: python3 -I audit-claude/scan.py <archive root>

A quick textual check that complements the checks made on the compiled modules
(`OleanCheck.lean`, `SupplementAudit.lean`, `ArchiveAudit.lean`), which do not depend on how
the sources are written. It scans three groups separately: the archive's library (`Riesz/`,
`Oscillation/`, `Oscillation.lean`), the auditor's supplement (`R56Audit/`, `R56Audit.lean`),
and the check scripts (`scripts/`, `audit-claude/`), which legitimately contain meta code.

It exits with status 1 if

* a library or supplement file contains a proof-bypassing or syntax-changing construct, a
  command that starts with `#`, an invisible character, or a quoted identifier `«…»`;
* a supplement file contains `instance`, `class`, `structure`, `set_option`, an attribute
  (`@[…]` or `attribute`), `_root_`, or a letter outside the list `LETTERS`; or the
  supplement declares anything other than one inductive type with one `deriving` clause;
* the library's instances, structures, options and attributes differ from those recorded
  below.
"""
import re, sys, unicodedata, collections, pathlib

root = pathlib.Path(sys.argv[1])
GROUPS = {
    'library': sorted([*root.glob('Riesz/**/*.lean'), *root.glob('Oscillation/**/*.lean'),
                       root/'Oscillation.lean']),
    'supplement': sorted([*root.glob('R56Audit/**/*.lean'), root/'R56Audit.lean']),
    'scripts': sorted([*root.glob('scripts/**/*.lean'), *root.glob('audit-claude/**/*.lean'),
                       root/'audit-claude/Gates.template']),
}

def strip(text):
    """Remove comments (nested block comments, line comments); keep string literals."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if depth == 0 and text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            out.append(text[i:j+1]); i = j + 1
        elif text.startswith('/-', i): depth += 1; i += 2
        elif depth and text.startswith('-/', i): depth -= 1; i += 2
        elif depth:
            if text[i] == '\n': out.append('\n')
            i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i); i = n if j < 0 else j
        else: out.append(text[i]); i += 1
    assert depth == 0
    return ''.join(out)

FORBIDDEN = {
 'sorry/admit': r'\b(sorry|admit|stop)\b',
 'axiom': r'\baxiom\b',
 'unsafe/partial/opaque': r'\b(unsafe|partial|opaque)\b',
 'native/ofReduce': r'native_decide|ofReduceBool|reduceBool|Lean\.trustCompiler|decide\s*\+native|bv_decide',
 'implemented_by/extern/csimp': r'implemented_by|extern|csimp',
 'meta code': r'\b(run_cmd|run_tac|run_elab|run_meta|elab|elab_rules|macro|macro_rules|syntax|declare_syntax_cat|initialize|builtin_initialize|#eval|#exit)\b',
 'notation': r'\b(notation|notation3|infix|infixl|infixr|prefix|postfix|binder_predicate)\b',
 'scoping tricks': r'\b(export|alias|unseal|seal|irreducible_def|local)\b|\battribute\b',
 'string literal': r'"',
 'quoted identifier': r'[«»]',
 'command starting with #': r'#',
}
# forbidden in the supplement only (the archive has a few of these; they are listed below)
SUPPLEMENT_ONLY = {
 'instance/class/structure': r'\b(instance|class|structure)\b',
 'set_option': r'\bset_option\b',
 'attribute': r'@\[',
 '_root_': r'\b_root_\b',
}
INFO = {
 'instance/structure/inductive/class': r'\b(instance|structure|inductive|class|deriving)\b',
 'set_option': r'\bset_option\b[^\n]*',
 'attributes': r'@\[[^\]]*\]',
}
# what the archive's library contains of these (recorded from the audited zip)
EXPECTED_LIBRARY = {
 'instance/structure/inductive/class': 'instance x4, structure x1',
 'set_option': 'set_option maxHeartbeats 1000000 x8, set_option maxHeartbeats 300000 x1, '
               'set_option maxHeartbeats 600000 x1, set_option maxHeartbeats 800000 x1',
 'attributes': '@[simp] x7',
}
EXPECTED_SUPPLEMENT = {'instance/structure/inductive/class': 'deriving x1, inductive x1',
                       'set_option': 'none', 'attributes': 'none'}
# letters allowed in the supplement outside ASCII (in code and in comments)
LETTERS = set('áöā' 'ˢˣᵐᶜⁿ' 'ΓΔΣΦΩ' 'αβγδεθικλμνξρσφχψω' 'ℓℕℝℤℱ' '𝒮𝒯𝓕𝓗')

failed = False
for group, files in GROUPS.items():
    lines = 0
    hits = collections.defaultdict(list)
    info = collections.defaultdict(collections.Counter)
    nonascii = collections.Counter()
    for p in files:
        raw = p.read_text(encoding='utf-8')
        lines += raw.count('\n')
        code = strip(raw)
        for ch in raw:
            if ord(ch) > 127: nonascii[ch] += 1
            cat = unicodedata.category(ch)
            if (cat in ('Cf', 'Cc', 'Co', 'Cn', 'Zl', 'Zp') and ch != '\n'):
                hits['invisible or control character'].append((p.name, repr(ch)))
        rules = dict(FORBIDDEN)
        if group == 'supplement': rules.update(SUPPLEMENT_ONLY)
        for name, pat in rules.items():
            for m in re.finditer(pat, code):
                hits[name].append((str(p.relative_to(root)), code.count('\n', 0, m.start()) + 1))
        for name, pat in INFO.items():
            for m in re.finditer(pat, code):
                info[name][m.group(0).strip()] += 1
    print(f'== {group}: {len(files)} files, {lines} lines')
    names = [*FORBIDDEN, *(SUPPLEMENT_ONLY if group == 'supplement' else {}),
             'invisible or control character']
    for name in names:
        L = hits[name]
        status = 'none' if not L else f'{len(L)} hit(s): ' + ', '.join(f'{a}:{b}' for a, b in L[:6])
        print(f'   {name}: {status}')
        if L and group != 'scripts': failed = True
    for name in INFO:
        value = 'none' if not info[name] else ', '.join(f'{k} x{v}' for k, v in sorted(info[name].items()))
        expected = {'library': EXPECTED_LIBRARY, 'supplement': EXPECTED_SUPPLEMENT}.get(group, {}).get(name)
        note = ''
        if expected is not None and value != expected:
            note = f'   <-- expected: {expected}'
            failed = True
        print(f'   {name}: {value}{note}')
    letters = sorted(ch for ch in nonascii if unicodedata.category(ch).startswith('L'))
    print('   non-ASCII letters: ' + ' '.join(f'{ch}(U+{ord(ch):04X})' for ch in letters))
    if group == 'supplement':
        bad = [ch for ch in letters if ch not in LETTERS]
        if bad:
            print('   letters outside the allowed list: ' + ' '.join(f'{ch}(U+{ord(ch):04X})' for ch in bad))
            failed = True
print('SCAN FAILED' if failed else 'SCAN PASSED')
sys.exit(1 if failed else 0)
