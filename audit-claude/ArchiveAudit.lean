import Oscillation
import Lean.Util.CollectAxioms

/-!
Independent environment audit of the r56 archive (written by the auditor; not part of the
archive). It lists the local modules, the kinds of all their constants, their instances and
environment-extension entries, collects the axioms of every constant (definitions included),
flags anything that is not an ordinary definition or theorem, and prints the local
definitions a reader must read to know what each main statement says. Run with

    lake env lean -DautoImplicit=false audit-claude/ArchiveAudit.lean
-/

open Lean Elab Command

namespace R56Audit

def isLocalModule (m : Name) : Bool :=
  (`Oscillation).isPrefixOf m || (`Riesz).isPrefixOf m

def allowed : List Name := [`propext, `Classical.choice, `Quot.sound]

partial def reachLocal (env : Environment) (isLocal : Name → Bool)
    (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n || !isLocal n then reachLocal env isLocal rest seen
    else
      let seen := seen.insert n
      match env.find? n with
      | none => reachLocal env isLocal rest seen
      | some ci => reachLocal env isLocal (ci.getUsedConstantsAsSet.toList ++ rest) seen

/-- Local constants occurring in the *statement* of `n`, transitively through the values of
local definitions (but not through proofs of theorems). This is what a reader must read to
know what the statement says. -/
partial def readingList (env : Environment) (isLocal : Name → Bool)
    (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n || !isLocal n then readingList env isLocal rest seen
    else
      let seen := seen.insert n
      match env.find? n with
      | none => readingList env isLocal rest seen
      | some ci =>
        let fromType := ci.type.getUsedConstantsAsSet.toList
        let fromValue := match ci with
          | .defnInfo v => v.value.getUsedConstantsAsSet.toList
          | .opaqueInfo v => v.value.getUsedConstantsAsSet.toList
          | .inductInfo v => v.ctors
          | _ => []
        readingList env isLocal (fromType ++ fromValue ++ rest) seen

def mainStatements : List Name := [
  `Oscillation.paper_lower_bound, `Oscillation.planar_tusnady_lower_bound,
  `Oscillation.R65.simultaneous_bound, `Oscillation.R65.all_good_compl_bound,
  `Oscillation.R65.bad_transition_bound, `Oscillation.stage_centered_lower_tail,
  `Oscillation.midpoint_range_comparison, `Oscillation.abs_mean_of_fourth_three]

run_cmd do
  let env ← getEnv
  let isLocal : Name → Bool := fun n =>
    match env.getModuleIdxFor? n with
    | some idx => isLocalModule env.header.moduleNames[idx.toNat]!
    | none => false
  let mut nMod := 0
  let mut kinds : Std.HashMap String Nat := {}
  let mut extensions : Std.HashMap Name Nat := {}
  let mut nAx := 0
  let mut bad : Array String := #[]
  let mut srcDecls := 0
  let mut srcThms := 0
  for h : i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    if isLocalModule m then
      nMod := nMod + 1
      IO.println s!"MODULE {m} consts={env.header.moduleData[i]!.constNames.size}"
      for (ext, entries) in env.header.moduleData[i]!.entries do
        if entries.size > 0 then
          extensions := extensions.insert ext (extensions.getD ext 0 + entries.size)
      for n in env.header.moduleData[i]!.constNames do
        let some ci := env.find? n | continue
        let kind := match ci with
          | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
          | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
        kinds := kinds.insert kind (kinds.getD kind 0 + 1)
        if kind == "axiom" || kind == "opaque" || kind == "quot" then
          bad := bad.push s!"{kind} {n}"
        if ci.isUnsafe then bad := bad.push s!"unsafe {n}"
        if ci.isPartial then bad := bad.push s!"partial {n}"
        if (Compiler.getImplementedBy? env n).isSome then bad := bad.push s!"implemented_by {n}"
        if isExtern env n then bad := bad.push s!"extern {n}"
        -- axioms of every constant, definitions included
        let axioms ← collectAxioms n
        nAx := nAx + 1
        for ax in axioms do
          unless allowed.contains ax do bad := bad.push s!"axiom {ax} used by {n}"
        if (← liftCoreM <| Meta.isInstance n) then
          let type ← liftTermElabM <|
            withOptions (fun o => o.setBool `pp.fullNames true) (Meta.ppExpr ci.type)
          let line := " ".intercalate
            (((type.pretty 1000000).splitOn "\n").map fun l => l.trimAscii.toString)
          IO.println s!"INSTANCE {n} : {line}"
        if let some _ ← findDeclarationRanges? n then
          srcDecls := srcDecls + 1
          if kind == "theorem" then srcThms := srcThms + 1
  for (ext, k) in extensions.toList do IO.println s!"EXT {ext} {k}"
  for (k, v) in kinds.toList do IO.println s!"KIND {k} {v}"
  for b in bad do IO.println s!"BAD {b}"
  IO.println s!"SUMMARY modules={nMod} constants_checked_for_axioms={nAx} bad={bad.size} declarations_with_source_range={srcDecls} theorems_with_source_range={srcThms}"
  -- what the main statements say
  for r in mainStatements do
    unless env.contains r do throwError "missing {r}"
    let some ci := env.find? r | continue
    let rl := readingList env isLocal (ci.type.getUsedConstantsAsSet.toList) {}
    let names := (rl.toList.map toString).toArray.qsort (· < ·)
    IO.println s!"READING {r} ({names.size}): {", ".intercalate names.toList}"
    let used := reachLocal env isLocal [r] {}
    let thms := used.toList.filter fun n => match env.find? n with
      | some (.thmInfo _) => true | _ => false
    IO.println s!"CLOSURE {r}: local constants={used.size} local theorems={thms.length}"

end R56Audit

-- The main statements, printed with full names (no notation can hide a different constant).
set_option pp.fullNames true in
#check @Oscillation.paper_lower_bound
set_option pp.fullNames true in
#print Riesz.PaperLowerBound
set_option pp.fullNames true in
#print Riesz.PointSets.GoodEvent
set_option pp.fullNames true in
#print Riesz.PointSets.unifPts
set_option pp.fullNames true in
#print Riesz.PointSets.colorSum
set_option pp.fullNames true in
#print Riesz.PointSets.badSet
set_option pp.fullNames true in
#print Riesz.PointSets.Δ₂
set_option pp.fullNames true in
#print Riesz.PointSets.rectDisc
#print axioms Oscillation.paper_lower_bound
#print axioms Oscillation.planar_tusnady_lower_bound
