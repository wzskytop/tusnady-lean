import R56Audit

/-!
What do the results of the supplement use of the archive? (Auditor's script; not part of the
archive, and not part of the supplement library.)

    lake env lean -DautoImplicit=false -DwarningAsError=true audit-claude/Closure.lean

For each root, the script follows every constant that occurs in its statement or in its proof,
through the supplement (`R56Audit.*`) and through the archive (`Riesz.*`, `Oscillation.*`), and
lists the modules it reaches. For Theorem 1.1 and for the lower bound of Corollary 1.2 it also
lists the definitions and theorems of the archive that are reached.
-/

open Lean Elab Command

namespace AuditScripts.Closure

partial def reach (env : Environment) (follow : Name → Bool) (todo : List Name)
    (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n || !follow n then reach env follow rest seen
    else
      let seen := seen.insert n
      match env.find? n with
      | none => reach env follow rest seen
      | some ci => reach env follow (ci.getUsedConstantsAsSet.toList ++ rest) seen

def moduleOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!

def sorted (l : List Name) : List Name :=
  (l.toArray.qsort fun a b => a.toString < b.toString).toList

/-- Roots, with a flag: list the archive declarations that are reached. -/
def roots : List (Name × Bool) := [
  (`R56Audit.theorem_1_1, true), (`R56Audit.corollary_1_2_lower, true),
  (`R56Audit.theorem_1_1_unfolded, false), (`R56Audit.proposition_2_7, false),
  (`R56Audit.lemma_2_4_digits, false), (`R56Audit.lemma_2_4, false),
  (`R56Audit.lemma_2_5_i, false), (`R56Audit.lemma_2_5_ii, false),
  (`R56Audit.lemma_2_5_ii_all, false),
  (`R56Audit.lemma_2_6_digits, false), (`R56Audit.lemma_2_6, false),
  (`R56Audit.local_gain, false), (`R56Audit.vertical_comparison, false),
  (`R56Audit.fact_2_2_general, false), (`R56Audit.fact_A_1, false),
  (`R56Audit.integral_prod_le_of_condExp_le, false),
  (`R56Audit.one_rectangle, false), (`R56Audit.condExp_digitSigma, false),
  (`R56Audit.condExp_nextDigits, false),
  -- for comparison: the routes through the archive's own proof
  (`R56Audit.theorem_1_1_archive, false), (`R56Audit.proposition_2_7_probe, false)]

run_cmd do
  let env ← getEnv
  let inArchive : Name → Bool := fun n =>
    match moduleOf env n with
    | some m => (`Oscillation).isPrefixOf m || (`Riesz).isPrefixOf m
    | none => false
  let inSupplement : Name → Bool := fun n =>
    match moduleOf env n with
    | some m => (`R56Audit).isPrefixOf m
    | none => false
  let nArchive := (env.header.moduleNames.toList.filter fun m =>
    (`Oscillation).isPrefixOf m || (`Riesz).isPrefixOf m).length
  let nSupplement := (env.header.moduleNames.toList.filter fun m =>
    (`R56Audit).isPrefixOf m).length
  IO.println s!"MODULES archive={nArchive} supplement={nSupplement}"
  for (root, detail) in roots do
    unless env.contains root do throwError "unknown root {root}"
    let used := reach env (fun n => inArchive n || inSupplement n) [root] {}
    let mut archive : Std.HashMap Name (List Name) := {}
    let mut supplement : Std.HashMap Name Nat := {}
    for n in used.toList do
      let some m := moduleOf env n | continue
      if inSupplement n then
        supplement := supplement.insert m (supplement.getD m 0 + 1)
      else
        -- definitions, theorems and instances written in the sources (no auxiliary constants)
        let named := !n.isInternal && (← findDeclarationRanges? n).isSome &&
          (match env.find? n with
          | some (.thmInfo _) | some (.defnInfo _) => true
          | _ => false)
        archive := archive.insert m (if named then n :: archive.getD m [] else archive.getD m [])
    IO.println s!"ROOT {root}: supplement modules {supplement.size}, archive modules {archive.size}"
    IO.println s!"  SUPPLEMENT {sorted (supplement.toList.map (·.1))}"
    if detail then
      for m in sorted (archive.toList.map (·.1)) do
        let names := sorted (archive.getD m [])
        IO.println s!"  ARCHIVE {m} ({names.length}): {names}"
    else
      IO.println s!"  ARCHIVE {sorted (archive.toList.map (·.1))}"

end AuditScripts.Closure
