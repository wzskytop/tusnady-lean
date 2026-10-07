import R56Audit

/-!
Environment audit of the supplement (auditor's script; not part of the archive, and not part
of the supplement library).

    lake env lean -DautoImplicit=false -DwarningAsError=true audit-claude/SupplementAudit.lean

It reads the environment after importing the supplement and fails unless:

1. every constant of the modules `R56Audit`, `R56Audit.*` is a definition, a theorem, or part
   of the inductive type `Side` — no `axiom`, `opaque`, `unsafe`, `partial`, `implemented_by`
   or `extern`;
2. the only axioms reached from these constants are `propext`, `Classical.choice`,
   `Quot.sound`. The proof terms themselves are walked, through every constant that occurs in
   a type or a value, Mathlib and core included; the axiom lists that `#print axioms` reads
   from the compiled modules are not used;
3. the instances, the simp lemmas and the definitions with a reducibility attribute that the
   supplement adds are exactly the expected ones: those generated for the inductive type
   `Side` and for two `match` expressions, and the four `abbrev`s;
4. the names declared by the supplement use ASCII characters, `Δ` and `₂` only;
5. every constant of the supplement modules lies in the namespace `R56Audit`, except theorems
   that Lean generates on demand for definitions of other modules (equation and congruence
   lemmas, with reserved names); and no name of the supplement, read without the prefix
   `R56Audit.`, is also the name of a declaration or of an exported alias in the root
   namespace or in a namespace that the check scripts open (`Gates.lean` opens `R56Audit`
   together with `Riesz`, `Riesz.PointSets`, `Oscillation`, `MeasureTheory`,
   `ProbabilityTheory`, for one gate `Oscillation.Direct`, and `Lean`, `Lean.Elab`,
   `Lean.Elab.Command` for its last part) — apart from the names in `expectedClashes`.

The names in `expectedClashes`: `maxOn`, `minOn` are also functions of Lean's core library
(`maxOn f x y` is the one of `x`, `y` at which `f` is larger). The definition gates of `maxOn`
and `minOn` in `Gates.lean` write `R56Audit.maxOn`, `R56Audit.minOn` in full; elsewhere in
`Gates.lean` the two names occur without prefix in statement gates only, where a name read in
the wrong way would make the `rfl` fail. The other names are theorems and one definition that
the archive also declares, in `Oscillation` and in `Oscillation.Direct`; the check scripts use
them with their full names only, or not at all.

(The reading list — which definitions one has to read in order to understand the statements —
is checked at the end of `Gates.lean`.)
-/

open Lean Elab Command

namespace AuditScripts.Supplement

def expectedModules : Nat := 33

def expectedInstances : List Name := [`R56Audit.Side._sizeOf_inst, `R56Audit.instDecidableEqSide]

def expectedSimp : List Name := [`R56Audit.Side.left.sizeOf_spec,
  `R56Audit.Side.inside.sizeOf_spec, `R56Audit.Side.right.sizeOf_spec]

def expectedReducible : List Name := [`R56Audit.digitLaw, `R56Audit.digitSigma,
  `R56Audit.heightSigma, `R56Audit.stageSigma, `R56Audit.Side.casesOn, `R56Audit.Side.ctorElim,
  `R56Audit.Side.ctorElimType, `R56Audit.Side.noConfusion, `R56Audit.Side.noConfusionType,
  `R56Audit.Side.recOn, `R56Audit.Side.inside.elim, `R56Audit.Side.left.elim,
  `R56Audit.Side.right.elim]

/-- Definitions with the attribute `instance_reducible`, which Lean gives to matchers and to
generated instances. -/
def expectedInstanceReducible : List Name := [`R56Audit.Side._sizeOf_inst,
  `R56Audit.instDecidableEqSide, `R56Audit.oldWeight.match_1,
  `R56Audit.prob_exists_supNorm_le_of_pow_le.match_1_1]

/-- Namespaces whose names a check script may use without a prefix. -/
def openNamespaces : List Name := [.anonymous, `MeasureTheory, `ProbabilityTheory, `Riesz,
  `Riesz.PointSets, `Oscillation, `Oscillation.Direct, `Lean, `Lean.Elab, `Lean.Elab.Command]

/-- Names of the supplement that also exist in one of these namespaces. -/
def expectedClashes : List (Name × Name) := [(`R56Audit.maxOn, `maxOn), (`R56Audit.minOn, `minOn),
  (`R56Audit.stageFiltration, `Oscillation.stageFiltration),
  (`R56Audit.stageFiltration._proof_1, `Oscillation.stageFiltration._proof_1),
  (`R56Audit.stageFiltration_apply, `Oscillation.stageFiltration_apply),
  (`R56Audit.integral_exp_centered_le, `Oscillation.integral_exp_centered_le),
  (`R56Audit.proposition_2_7, `Oscillation.Direct.proposition_2_7),
  (`R56Audit.threshold_eq, `Oscillation.Direct.threshold_eq)]

run_cmd do
  let env ← getEnv
  let moduleOf : Name → Option Name := fun n =>
    (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!
  let inSupp : Name → Bool := fun n =>
    match moduleOf n with
    | some m => (`R56Audit).isPrefixOf m
    | none => false
  -- 1. kinds
  let mut modules := 0
  let mut todo : Array Name := #[]
  let mut kinds : Std.HashMap String Nat := {}
  let mut reducible : Array Name := #[]
  let mut instReducible : Array Name := #[]
  let mut clashes : Array (Name × Name) := #[]
  let mut foreign : Array Name := #[]
  let mut chars : Std.HashSet Char := {}
  let mut written : Std.HashMap String Nat := {}
  for h : i in [0:env.header.moduleNames.size] do
    if (`R56Audit).isPrefixOf env.header.moduleNames[i] then
      modules := modules + 1
      for n in env.header.moduleData[i]!.constNames do
        let some ci := env.find? n | throwError "constant {n} not found"
        let kind := match ci with
          | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
        if kind == "axiom" || kind == "opaque" || kind == "quot" then
          throwError "{kind} in the supplement: {n}"
        if ci.isUnsafe || ci.isPartial then throwError "unsafe or partial: {n}"
        if (Compiler.getImplementedBy? env n).isSome then throwError "implemented_by: {n}"
        if isExtern env n then throwError "extern: {n}"
        if (kind == "inductive" || kind == "constructor" || kind == "recursor") &&
            !(`R56Audit.Side).isPrefixOf n then
          throwError "unexpected inductive type: {n}"
        kinds := kinds.insert kind (kinds.getD kind 0 + 1)
        -- declarations written in the sources, as opposed to auxiliary constants
        if !n.isInternal && (← findDeclarationRanges? n).isSome &&
            (kind == "theorem" || kind == "definition") && !(`R56Audit.Side).isPrefixOf n &&
            n != `R56Audit.instDecidableEqSide then
          written := written.insert kind (written.getD kind 0 + 1)
        todo := todo.push n
        match ← liftCoreM (getReducibilityStatus n) with
        | .semireducible => pure ()
        | .reducible => reducible := reducible.push n
        | .instanceReducible => instReducible := instReducible.push n
        | _ => throwError "unexpected reducibility attribute: {n}"
        -- 5. namespaces and name clashes
        let user := privateToUserName n
        if (`R56Audit).isPrefixOf user then
          let short := user.replacePrefix `R56Audit .anonymous
          for ns in openNamespaces do
            if env.contains (ns ++ short) ||
                !(getAliases env (ns ++ short) (skipProtected := false)).isEmpty then
              clashes := clashes.push (user, ns ++ short)
        else
          unless isReservedName env n && kind == "theorem" do
            throwError "constant outside the namespace R56Audit: {n}"
          foreign := foreign.push n
        unless n.isInternal do
          for c in n.toString.toList do
            if c.toNat > 127 then chars := chars.insert c
  unless modules == expectedModules do
    throwError "{modules} supplement modules, expected {expectedModules}"
  let total := todo.size
  IO.println s!"KINDS {modules} modules, {total} constants: {(kinds.toList.map fun (k, v) => s!"{k} {v}").mergeSort}; written in the sources: {written.getD "theorem" 0} theorems, {written.getD "definition" 0} definitions, and the inductive type Side"
  -- 2. axioms, by walking the terms
  let mut seen : Std.HashSet Name := {}
  let mut axioms : Array Name := #[]
  while todo.size > 0 do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "constant {n} not found"
    if let .axiomInfo _ := ci then axioms := axioms.push n
    for m in ci.getUsedConstantsAsSet do
      unless seen.contains m do todo := todo.push m
  for ax in axioms do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "axiom {ax} is reached from the supplement"
  IO.println s!"AXIOMS reached from the {total} constants, through {seen.size} constants in all: {axioms.qsort Name.lt}"
  -- 3. instances, simp lemmas, reducibility
  let insts := ((Meta.instanceExtension.getState env).instanceNames.toList.map (·.1)).filter inSupp
  unless insts.all expectedInstances.contains && expectedInstances.all insts.contains do
    throwError "instances of the supplement: {insts}"
  let simps := (← liftCoreM Meta.getSimpTheorems).lemmaNames.toList.filterMap fun o =>
    match o with
    | Meta.Origin.decl n _ _ => if inSupp n then some n else none
    | _ => none
  unless simps.all expectedSimp.contains && expectedSimp.all simps.contains do
    throwError "simp lemmas of the supplement: {simps}"
  unless reducible.all expectedReducible.contains && expectedReducible.all reducible.contains do
    throwError "reducible definitions of the supplement: {reducible}"
  unless instReducible.all expectedInstanceReducible.contains &&
      expectedInstanceReducible.all instReducible.contains do
    throwError "instance-reducible definitions of the supplement: {instReducible}"
  IO.println s!"ATTRIBUTES instances {insts.length}, simp lemmas {simps.length}, reducible {reducible.size}, instance-reducible {instReducible.size}: as expected (the inductive type Side, four abbrevs, two matchers)"
  -- 4. names
  for c in chars do
    unless c == 'Δ' || c == '₂' do throwError "character {c} (U+{c.toNat}) in a declared name"
  IO.println s!"NAMES non-ASCII characters in declared names: {chars.toList}"
  -- 5. namespaces and name clashes
  unless clashes.all expectedClashes.contains && expectedClashes.all clashes.contains do
    throwError "names of the supplement that exist in an open namespace: {clashes}"
  IO.println s!"NAMESPACES {total - foreign.size} constants in the namespace R56Audit, and {foreign.size} equation or congruence lemmas that Lean generated for definitions of other modules: {foreign.qsort Name.lt}; {clashes.size} names are also names of declarations or aliases in the root namespace or in a namespace opened by the check scripts, the expected ones: {(clashes.map (·.2)).qsort Name.lt}"

end AuditScripts.Supplement
