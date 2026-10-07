"""Negative test of the statement gates (auditor's script; reads the gate file as data).

    python3 -I audit-claude/mutants.py write audit-claude/Gates.lean OUT.lean
    lake env lean -DautoImplicit=false OUT.lean > OUT.log 2>&1
    python3 -I audit-claude/mutants.py check OUT.lean OUT.log

`write` copies single gates (statement gates and definition gates) and changes one hypothesis,
constant, relation or interval end in each copy; unchanged copies are added as controls.
`check` reads Lean's output: every changed gate must be rejected with a type mismatch reported
at its final `rfl`, and the controls must be accepted.
"""
import re, sys

MUTANTS = [
 ('theorem_1_1', '1 ≤ n →', '2 ≤ n →'),
 ('theorem_1_1', '(3 / 2 : ℝ)', '(2 : ℝ)'),
 ('theorem_1_1', '-A * n', '-A * n * 2'),
 ('theorem_1_1', '≤ supNorm χ P', '< supNorm χ P'),
 ('theorem_1_1_unfolded', '(P i).2 ≤ y', '(P i).2 < y'),
 ('theorem_1_1_unfolded', 'Set.Icc 0 1)', 'Set.Ioo 0 1)'),
 ('corollary_1_2_lower', '< Δ₂ n', '≤ Δ₂ n'),
 ('vertical_comparison', '(hb : 2 ≤ b)', '(hb : 3 ≤ b)'),
 ('vertical_comparison', '2 * |mid', '3 * |mid'),
 ('fact_2_2_general', '(hσ : 0 < σ)', '(hσ : 0 ≤ σ)'),
 ('fact_2_2_general', '(h4i : ∀ i, Integrable (fun ω => X i ω ^ 4) μ) ', ''),
 ('local_gain', '(1 / 4)', '(1 / 3)'),
 ('local_gain', '(hε : ∀ i, |ε i| = 1)', '(hε : ∀ i, |ε i| ≤ 1)'),
 ('lemma_2_4_digits', 'digitSigma n b j', 'digitSigma n b (j + 1)'),
 ('lemma_2_4_digits', '(hj : j < h)', '(hj : j ≤ h)'),
 ('lemma_2_4', 'stageSigma n b j', 'digitSigma n b j'),
 ('lemma_2_5_i', '(hn : 0 < n) ', ''),
 ('lemma_2_5_ii', '(48 / (b : ℝ))', '(47 / (b : ℝ))'),
 ('lemma_2_5_ii', '(hMn : b ^ (h - 1) ≤ n) ', ''),
 ('lemma_2_6_digits', '(2 * h * n)', '(h * n)'),
 ('lemma_2_6_digits', '≤ -lam}', '< -lam}'),
 ('proposition_2_7', '(hb : 3 ≤ b)', '(hb : 2 ≤ b)'),
 ('proposition_2_7', '2048', '2047'),
 ('proposition_2_7', '∃ χ : Fin n → ℤˣ', '∀ χ : Fin n → ℤˣ'),
 ('fact_A_1', '{c : ℝ} (hc : 0 < c)', '{c : ℝ}'),
 ('fact_A_1', 'n * t ^ 2 * c ^ 2 / 2', 'n * t ^ 2 * c ^ 2 / 4'),
 ('fact_A_1', '(hΓindep : IndepFun Γ (fun ω i => ξ i ω) μ) ', ''),
 ('display_18', '< ((b : ℝ) ^ 8)⁻¹', '≤ ((b : ℝ) ^ 8)⁻¹'),
 ('one_rectangle', '(8 * (b : ℝ))', '(4 * (b : ℝ))'),
 ('condExp_digitSigma', '(hb : 0 < b) ', ''),
 ('roadmap_digits', 'Zpot χ b h 0 P +', 'Zpot χ b h 1 P +'),
 ('Zpot_le_two_supNorm', '2 * supNorm χ P', '1 * supNorm χ P'),
 ('ae_setupEvent', 'SetupEvent b P', 'SetupEvent (b + 1) P'),
 ('exists_points', 'Function.Injective P ∧ ', ''),
 ('fluct_le_of_good', '-(3 * h * deltaStar n b h / 4)', '-(3 * h * deltaStar n b h / 2)'),
 ('volume_boundaryStrips', '(hb : 2 ≤ b)', '(hb : 1 ≤ b)'),
 ('volume_innerRegions_lt', '< ENNReal.ofReal (1 / (b : ℝ))', '≤ ENNReal.ofReal (1 / (b : ℝ))'),
 ('integral_prod_le_of_condExp_le', '(hc : ∀ j < h, 0 ≤ c j) ', ''),
 ('condExp_exp_le_cosh', 'Real.cosh (t * c)', 'Real.cosh (t * c / 2)'),
 ('threshold_gt', '(64 * (b : ℝ) ^ (3 / 2 : ℝ))', '(32 * (b : ℝ) ^ (3 / 2 : ℝ))'),
]
# definition gates, found by a piece of text that occurs in exactly one of them
DEF_MUTANTS = [
 ('supNorm χ P = ⨆ z', 'Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1', 'Set.Icc (0 : ℝ) 1 × Set.Ico (0 : ℝ) 1'),
 ('F χ P x y =\n      ∑ i, if', 'Set.Icc (0 : ℝ × ℝ) (x, y)', 'Set.Ioc (0 : ℝ × ℝ) (x, y)'),
 ('cA b = ', '(b : ℝ) ^ 8', '(b : ℝ) ^ 7'),
 ('Zpot χ b h j P =', 'Fin (b ^ (h - j))', 'Fin (b ^ (h - j - 1))'),
 ('vcell b h j v = ', 'Set.Ico', 'Set.Icc'),
 ('digit b k u = ', '% b', '% (b + 1)'),
 ('innerRegion b h j c v =\n      Set.Icc', 'Set.Ico (((v : ℝ) * (b : ℝ) ^ (j + 1) + (b : ℝ) ^ j)', 'Set.Icc (((v : ℝ) * (b : ℝ) ^ (j + 1) + (b : ℝ) ^ j)'),
 ('Heavy b h j P c v ↔', '< innerCount', '≤ innerCount'),
 ('GoodTransition b h j P ↔', '(n : ℝ) / 2 ≤', '(n : ℝ) / 3 ≤'),
 ('deltaStar n b h = ', '1 / (8 *', '1 / (4 *'),
 ('delta b h j P =', '(4 * (b : ℝ) * (b : ℝ) ^ (h - 1))', '(2 * (b : ℝ) * (b : ℝ) ^ (h - 1))'),
 ('IsScale b n h ↔', '→ h\' ≤ h', '→ h\' < h'),
]
CONTROLS = ['proposition_2_7', 'fact_A_1']

def write(gates, out):
    s = open(gates, encoding='utf-8').read()
    head = s[:s.index('/-! ## Section 1.')]
    head = head[:head.index('/-!')] + head[head.index('-/') + 2:]   # without the docstring

    def gate(name):
        m = re.search(r'^-- `' + re.escape(name) + r'` \(\w+\)\n(example.*?:= rfl)\n', s,
                      re.M | re.S)
        if not m:
            sys.exit(f'no gate for {name}')
        return m.group(1)

    # the hand-written gates: blocks of lines starting at a line `example …`, after the
    # generated statement gates have been removed
    hand = re.sub(r'^-- `[^`]+` \(\w+\)\n(?:open [^\n]* in\n)?example.*?:= rfl\n', '', s,
                  flags=re.M | re.S)
    blocks = [m.group(0) for m in re.finditer(r'^example\b[^\n]*(?:\n(?!\n)[^\n]*)*', hand, re.M)]

    def defgate(marker):
        hits = [b for b in blocks if marker in b]
        if len(hits) != 1:
            sys.exit(f'{len(hits)} definition gates contain `{marker}`')
        return hits[0]

    res = [head, '\n']
    for name, a, b in MUTANTS:
        text = ' '.join(gate(name).split())      # one line, so that the patterns match
        if text.count(a) < 1:
            sys.exit(f'{name}: pattern `{a}` not found')
        res.append(f'-- MUTANT {name}: `{a}` -> `{b}`\n' + text.replace(a, b, 1) + '\n\n')
    for marker, a, b in DEF_MUTANTS:
        text = ' '.join(defgate(marker).split())
        if text.count(a) < 1:
            sys.exit(f'{marker}: pattern `{a}` not found')
        label = ' '.join(marker.split())
        res.append(f'-- MUTANT definition `{label}`: `{a}` -> `{b}`\n' + text.replace(a, b, 1) + '\n\n')
    for name in CONTROLS:
        res.append(f'-- CONTROL {name}\n' + ' '.join(gate(name).split()) + '\n\n')
    res.append('-- CONTROL definition\n' + ' '.join(defgate(DEF_MUTANTS[0][0]).split()) + '\n')
    open(out, 'w', encoding='utf-8').write(''.join(res))
    print(f'{len(MUTANTS) + len(DEF_MUTANTS)} mutants and {len(CONTROLS) + 1} controls written')

def check(src, log):
    lines = open(src, encoding='utf-8').read().split('\n')
    text = open(log, encoding='utf-8').read()
    errors = {}
    for m in re.finditer(r':(\d+):(\d+): error(?:\([^)]*\))?: ([^\n]*)', text):
        errors.setdefault(int(m.group(1)), []).append((int(m.group(2)), m.group(3)))
    if re.search(r'\bwarning\b', text):
        print('warnings in the output')
        sys.exit(1)
    total = len(MUTANTS) + len(DEF_MUTANTS)
    rejected, controls, problems = 0, 0, []
    labelled = set()
    for i, l in enumerate(lines, 1):
        if l.startswith('-- MUTANT'):
            labelled.add(i + 1)
            # the only error must be a type mismatch at the closing `rfl` (or `Iff.rfl`)
            gate_line = lines[i]
            closer = 'Iff.rfl' if gate_line.endswith('Iff.rfl') else 'rfl'
            col = len(gate_line) - len(closer)
            if errors.get(i + 1) == [(col, 'Type mismatch')]:
                rejected += 1
            else:
                problems.append(f'not rejected at its `rfl`: {l} ({errors.get(i + 1)})')
        elif l.startswith('-- CONTROL'):
            labelled.add(i + 1)
            controls += 1
            if (i + 1) in errors:
                problems.append(f'control rejected: {errors[i + 1]}')
    stray = sorted(set(errors) - labelled)
    if stray:
        problems.append(f'errors at unexpected lines {stray}')
    for p in problems:
        print(p)
    print(f'MUTANTS: {rejected} of {total} changed gates rejected ({len(MUTANTS)} statements, '
          f'{len(DEF_MUTANTS)} definitions); {controls} controls accepted'
          if not problems else 'MUTANT TEST FAILED')
    sys.exit(1 if problems or rejected != total else 0)

if len(sys.argv) == 4 and sys.argv[1] == 'write':
    write(sys.argv[2], sys.argv[3])
elif len(sys.argv) == 4 and sys.argv[1] == 'check':
    check(sys.argv[2], sys.argv[3])
else:
    sys.exit(__doc__)
