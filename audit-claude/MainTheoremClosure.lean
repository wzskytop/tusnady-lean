import Oscillation
/-!
Which declarations does the proof term of `Oscillation.paper_lower_bound` actually reach?
(Auditor's script; not part of the archive.)

    lake env lean -DautoImplicit=false audit-claude/MainTheoremClosure.lean
-/
open Lean Elab Command

partial def reachLocal' (env : Environment) (isLocal : Name → Bool)
    (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n || !isLocal n then reachLocal' env isLocal rest seen
    else
      let seen := seen.insert n
      match env.find? n with
      | none => reachLocal' env isLocal rest seen
      | some ci => reachLocal' env isLocal (ci.getUsedConstantsAsSet.toList ++ rest) seen

run_cmd do
  let env ← getEnv
  let isLocal : Name → Bool := fun n =>
    match env.getModuleIdxFor? n with
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      (`Oscillation).isPrefixOf m || (`Riesz).isPrefixOf m
    | none => false
  let used := reachLocal' env isLocal [`Oscillation.paper_lower_bound] {}
  for n in [`Oscillation.midpoint_range_comparison, `Oscillation.abs_mean_of_fourth_three,
      `Oscillation.stage_centered_lower_tail, `Oscillation.centered_lower_tail,
      `Oscillation.R65.simultaneous_bound, `Oscillation.R65.bad_transition_bound,
      `Oscillation.R65.all_good_compl_bound, `Oscillation.Direct.proposition_2_7,
      `Oscillation.Direct.union_simultaneous_bound, `Oscillation.Direct.allGood_compl_bound,
      `Oscillation.Direct.paper_bad_transition_bound, `Oscillation.Direct.bucket_bad_transition_bound,
      `Oscillation.gridPotential_drift_even, `Oscillation.local_gridMax_gain,
      `Oscillation.averaged_child_difference_gain, `Oscillation.shifted_rademacher_abs,
      `Oscillation.gridMax_end_comparison, `Oscillation.Direct.point_exp_loss,
      `Oscillation.Direct.loss_tail, `Oscillation.Direct.stage_exp_gain,
      `Oscillation.finAvg_exp_boundedDifferences, `Oscillation.gridPotential_refined_influence,
      `Riesz.PointSets.badSet_measure_zero, `Oscillation.Direct.paperGoodTransition_mass] do
    IO.println s!"{if used.contains n then "USED    " else "NOT USED"} {n}"
  -- modules contributing to the main theorem
  let mut mods : Std.HashMap Name Nat := {}
  for n in used.toList do
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx.toNat]!
      mods := mods.insert m (mods.getD m 0 + 1)
  let all := (env.header.moduleNames.toList.filter fun m =>
    (`Oscillation).isPrefixOf m || (`Riesz).isPrefixOf m)
  let unusedMods := all.filter fun m => !mods.contains m
  IO.println s!"modules used by the main theorem: {mods.size} of {all.length}"
  IO.println s!"modules with no declaration used by the main theorem: {unusedMods}"
