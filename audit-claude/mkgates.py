"""Expand the gate template into audit-claude/Gates.lean (auditor's script; reads the sources
as data).

Usage: python3 -I audit-claude/mkgates.py audit-claude/Gates.template R56Audit OUT

A template line `--@pin NAME` (optionally `--@pin NAME open=NAMESPACE`) is replaced by

    example <lifted binders> : (∀ <binders>, <statement>) = type_of% (@R56Audit.NAME ...) := rfl

where binders and statement are copied from the header of the theorem NAME in the source
directory. Comments are removed before the sources are searched, so only code can be copied.
The section variables in scope that the header mentions are put first, as Lean does (a
variable is included if the header mentions it, or if an included variable mentions it; an
instance variable is included if all the variables it mentions are). Binder groups up to the
last one that introduces a universe-polymorphic type (`Type*`) are lifted to the `example`,
because two separately elaborated `Type*` would get different universe names.
A line `--@def NAME` marks the hand-written example that follows it as the definition gate
of the definition NAME (names of the supplement are given without `R56Audit.`); the statement
of the example must begin with NAME. (That it is the unfolding of the definition is what the
`rfl` of the example proves; whether the body written there is the right one is for the
reader.) The one line `--@def Side Side.left Side.inside Side.right` marks the fact that
describes the inductive type `Side`. The line `--@archive-routes` starts the part of the
template about the archive's own routes. The lines `--@pinlist`, `--@readlist` and
`--@deflist` are replaced by Lean lists: the statements pinned so far, those of them pinned
before `--@archive-routes`, and the definitions that have a definition gate. All other lines
of the template are copied unchanged.

If the copy of a statement were wrong in any way (a wrong set of section variables, say), the
gate would not be the statement of NAME and Lean would reject the `rfl`.

The script stops if a source file opens a namespace other than `R56Audit` or contains an
indented `theorem`; and at the end it checks that every gate survives the removal of comments
from the generated file, so that no gate can sit inside a comment. The counts it prints are
counts of the generated file without its comments.
"""
import re, sys, glob, os, textwrap

template, srcdir, out = sys.argv[1], sys.argv[2], sys.argv[3]

OPEN, CLOSE = '([{⦃⟨', ')]}⦄⟩'


def strip_comments(text):
    """Remove block comments (nested) and line comments; keep string literals and newlines."""
    res, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if depth == 0 and text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            res.append(text[i:j + 1]); i = j + 1
        elif text.startswith('/-', i):
            depth += 1; i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1; i += 2
        elif depth:
            if text[i] == '\n': res.append('\n')
            i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i); i = n if j < 0 else j
        else:
            res.append(text[i]); i += 1
    if depth:
        sys.exit('unterminated comment')
    return ''.join(res)


def groups_at(s, i):
    """Binder groups starting at position i; returns (groups, position after them)."""
    groups = []
    while True:
        while i < len(s) and s[i].isspace():
            i += 1
        if i < len(s) and s[i] in '([{⦃':
            depth, j = 0, i
            while True:
                if s[j] in OPEN: depth += 1
                elif s[j] in CLOSE:
                    depth -= 1
                    if depth == 0: break
                j += 1
            groups.append(' '.join(s[i:j + 1].split()))
            i = j + 1
        else:
            return groups, i


def bound_names(group):
    """Names bound by a binder group `(a b : T)` / `{a b : T}`; none for instance binders."""
    if group[0] == '[':
        return []
    inner = group[1:-1]
    depth = 0
    for k, ch in enumerate(inner):
        if ch in OPEN: depth += 1
        elif ch in CLOSE: depth -= 1
        elif ch == ':' and depth == 0 and not inner.startswith(':=', k):
            return inner[:k].split()
    sys.exit(f'cannot parse binder {group}')


def split_group(group):
    """`{a b : T}` -> [`{a : T}`, `{b : T}`]; instance binders are kept."""
    names = bound_names(group)
    if len(names) <= 1:
        return [group]
    typ = group[1:-1].split(':', 1)[1].strip()
    return [f'{group[0]}{x} : {typ}{group[-1]}' for x in names]


def word_in(w, text):
    return re.search(r'(?<![\w.])' + re.escape(w) + r"(?![\w'])", text) is not None


# every theorem of the sources: name -> list of (module, variables in scope, groups, statement)
DECLS = {}
for path in sorted(glob.glob(os.path.join(srcdir, '*.lean'))):
    module = os.path.basename(path)[:-5]
    s = strip_comments(open(path, encoding='utf-8').read())
    scopes = [[]]            # stack of lists of section variables (binder groups)
    omit = False
    pos = 0
    for m in re.finditer(r'^[^\n]*$', s, re.M):
        line, pos = m.group(0), m.start()
        if re.match(r'\s+(theorem|lemma)\b', line):
            sys.exit(f'{module}: indented `{line.strip()[:40]}`')
        if re.match(r'\s*namespace\b', line) and line != 'namespace R56Audit':
            sys.exit(f'{module}: unexpected `{line}`')
        if re.match(r'(noncomputable\s+)?section\b', line) or re.match(r'namespace\b', line):
            scopes.append([])
        elif re.match(r'end(\s+[\w.]+)?\s*$', line):
            if len(scopes) == 1:
                sys.exit(f'{module}: unbalanced `end`')
            scopes.pop()
        elif re.match(r'variable\b', line):
            groups, e = groups_at(line, len('variable'))
            if e != len(line) or not groups:
                sys.exit(f'{module}: cannot parse `{line}` (one line of binders expected)')
            for g in groups:
                scopes[-1] += split_group(g)
        elif re.match(r'omit\b', line):
            omit = True
        else:
            d = re.match(r'(theorem|lemma)\s+([^\s:({\[]+)', line)
            if d:
                groups, e = groups_at(s, pos + d.end())
                if s[e] != ':':
                    sys.exit(f'{module}.{d.group(2)}: expected ":" after the binders')
                depth, j = 0, e + 1
                while not (depth == 0 and s.startswith(':=', j)):
                    if s[j] in OPEN: depth += 1
                    elif s[j] in CLOSE: depth -= 1
                    j += 1
                stmt = s[e + 1:j].strip('\n').rstrip()
                inscope = [g for sc in scopes for g in sc]
                DECLS.setdefault(d.group(2), []).append((module, inscope, groups, stmt, omit))
                omit = False
            elif line.strip() and not line[0].isspace() and omit:
                sys.exit(f'{module}: `omit` before something that is not a theorem')
    if len(scopes) != 1:
        sys.exit(f'{module}: unbalanced sections')


def pin(name):
    hits = DECLS.get(name, [])
    if len(hits) != 1:
        sys.exit(f'{name}: {len(hits)} theorems of this name in the sources')
    module, inscope, groups, stmt, omit = hits[0]
    if omit:
        sys.exit(f'{name}: declarations after `omit … in` are not supported')
    own = [x for g in groups for x in bound_names(g)]
    text = ' '.join(groups) + ' ' + stmt
    # the section variables that Lean includes
    included = [False] * len(inscope)
    changed = True
    while changed:
        changed = False
        named = {x for k, g in enumerate(inscope) if included[k] for x in bound_names(g)}
        for k, g in enumerate(inscope):
            if included[k]:
                continue
            names = bound_names(g)
            if names:
                if names[0] not in own and word_in(names[0], text):
                    included[k] = True
            else:
                mentioned = [x for h in inscope for x in bound_names(h) if word_in(x, g)]
                if mentioned and all(x in named and x not in own for x in mentioned):
                    included[k] = True
            if included[k]:
                text += ' ' + g
                changed = True
    allg = [g for k, g in enumerate(inscope) if included[k]] + groups
    lift = 0
    for k, g in enumerate(allg):
        if 'Type*' in g or 'Sort*' in g:
            lift = k + 1
    lifted, rest = allg[:lift], allg[lift:]
    args = []
    for g in lifted:
        args += bound_names(g) or ['_']
    target = f'@R56Audit.{name}' if not args else f'(@R56Audit.{name} {" ".join(args)})'
    head = 'example' + ''.join(' ' + g for g in lifted) + ' :'
    body_lines = [l.rstrip() for l in textwrap.dedent(stmt).split('\n')]
    lines = []
    if rest:
        wrapped = textwrap.wrap(head + ' (∀ ' + ' '.join(rest) + ',', width=96,
                                subsequent_indent='    ', break_long_words=False,
                                break_on_hyphens=False)
        lines += wrapped
        lines += ['      ' + l for l in body_lines]
    else:
        lines += textwrap.wrap(head + ' (', width=96, subsequent_indent='    ',
                               break_long_words=False, break_on_hyphens=False)
        lines += ['      ' + l for l in body_lines]
    lines[-1] += ') ='
    lines.append(f'    type_of% {target} := rfl')
    return '\n'.join(lines), module


def lean_list(indent, name, names):
    text = f'let {name} : List Name := [{", ".join("`" + x for x in names)}]'
    return textwrap.wrap(text, width=96, initial_indent=indent, subsequent_indent=indent + '  ')


lines = open(template, encoding='utf-8').read().split('\n')
res, pinned, to_read, gated, markers = [], [], [], [], []
archive = False
for k, line in enumerate(lines):
    indent = line[:len(line) - len(line.lstrip())]
    m = re.match(r'--@pin\s+(\S+)(?:\s+open=(\S+))?\s*$', line)
    if m:
        full = 'R56Audit.' + m.group(1)
        if full in pinned:
            sys.exit(f'{m.group(1)}: pinned twice')
        pinned.append(full)
        if not archive:
            to_read.append(full)
        text, module = pin(m.group(1))
        res.append(f'-- `{m.group(1)}` ({module})')
        if m.group(2):
            res.append(f'open {m.group(2)} in')
        res.append(text)
        markers.append(text)
    elif line.startswith('--@def '):
        # the example that follows: up to the next blank line
        if k + 1 >= len(lines) or not lines[k + 1].startswith('example'):
            sys.exit(f'`{line}` is not followed by an example')
        e = k + 1
        while e < len(lines) and lines[e].strip():
            e += 1
        block = '\n'.join(lines[k + 1:e])
        groups, c = groups_at(block, len('example'))
        if block[c] != ':':
            sys.exit(f'`{line}`: cannot find the statement of the example')
        for name in line.split()[1:]:
            full = name if name.split('.')[0] in ('Riesz', 'Oscillation') else 'R56Audit.' + name
            short = name.split('.')[-1] if full == name else name
            if short.split('.')[0] == 'Side':
                # the inductive type and its constructors: described by the fact that follows
                ok = word_in(short, block)
            else:
                # the statement starts with the name (possibly inside parentheses)
                ok = re.match(r'[\s(]*(R56Audit\.)?' + re.escape(short) + r"(?![\w'.])",
                              block[c + 1:]) is not None
            if not ok:
                sys.exit(f'`{line}`: the example is not a statement about {short}')
            if full in gated:
                sys.exit(f'{name}: two definition gates')
            gated.append(full)
        markers.append(block)
    elif line.strip() == '--@archive-routes':
        archive = True
    elif line.strip() == '--@pinlist':
        res += lean_list(indent, 'pinned', sorted(pinned))
    elif line.strip() == '--@readlist':
        res += lean_list(indent, 'toRead', sorted(to_read))
    elif line.strip() == '--@deflist':
        res += lean_list(indent, 'gated', gated)
    elif line.lstrip().startswith('--@'):
        sys.exit(f'bad directive: {line}')
    else:
        res.append(line)
text = '\n'.join(res)
# no gate inside a comment: every gate is still there when the comments are removed
code = strip_comments(text)
for block in markers:
    if strip_comments(block) not in code:
        sys.exit('a gate is inside a comment: ' + block.split('\n')[0])
examples = len(re.findall(r'^example\b', code, re.M))
open(out, 'w', encoding='utf-8').write(text)
print(f'{len(pinned)} statement gates written to {out}')
print(f'GATES {examples} examples (comments removed): {len(pinned)} statement gates, '
      f'{len(markers) - len(pinned)} definition gates for {len(gated)} names, '
      f'{examples - len(markers)} other examples')
