import Oscillation

open Lean Elab Command
namespace DirectAudit

def localModule (m : Name) : Bool :=
  (`Oscillation).isPrefixOf m || (`Riesz).isPrefixOf m

partial def reachable (env : Environment) (localDecl : Name → Bool)
    (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n || !localDecl n then reachable env localDecl rest seen
    else
      match env.find? n with
      | none => reachable env localDecl rest (seen.insert n)
      | some ci => reachable env localDecl (ci.getUsedConstantsAsSet.toList ++ rest) (seen.insert n)

run_cmd do
  let env ← getEnv
  let localDecl : Name → Bool := fun n =>
    match env.getModuleIdxFor? n with
    | some idx => localModule env.header.moduleNames[idx.toNat]!
    | none => false
  let used := reachable env localDecl [`Oscillation.paper_lower_bound] {}
  for n in [`Oscillation.R65.paper_lower_bound, `Oscillation.Direct.paper_lower_bound,
      `Oscillation.Direct.bucket_bad_transition_bound, `Oscillation.Direct.paper_bad_transition_bound,
      `Oscillation.Direct.allGood_compl_bound, `Oscillation.Direct.allGood_subset_good,
      `Oscillation.Direct.union_simultaneous_bound, `Oscillation.Direct.failure_sum,
      `Oscillation.Direct.absorb_all_stages, `Oscillation.Direct.point_exp_loss,
      `Oscillation.averaged_child_difference_gain, `Oscillation.Direct.loss_tail] do
    unless used.contains n do throwError "r65 proof step absent from main theorem: {n}"
    IO.println s!"REQUIRED {n}"
  for n in [`Oscillation.Direct.r17_paper_lower_bound, `Oscillation.Direct.sequential_mass_exp,
      `Oscillation.Direct.stages_crowding_exp, `Oscillation.Direct.r17_simultaneous_bound,
      `Oscillation.Direct.bad_geometry_bound, `Oscillation.Direct.paper_bad_geometry_bound,
      `Oscillation.Direct.paper_bad_geometry_bound_exact, `Oscillation.Direct.paper_simultaneous_bound,
      `Oscillation.fixed_scale_estimate, `Oscillation.paper_lower_bound_of_fixed_scale,
      `Oscillation.pointTerminal_laplace_of_compensated,
      `Oscillation.integral_exp_oscillation_laplace_of_marginal_bound,
      `Oscillation.iid_interior_laplace, `Oscillation.integral_exp_terminal_le_of_compensated,
      `Oscillation.gridMax_half_comparison, `Oscillation.halfGain,
      `Oscillation.sum_halfGain, `Oscillation.rowDifference_abs_gain] do
    if used.contains n then throwError "excluded proof step used by r65 main theorem: {n}"
    IO.println s!"EXCLUDED {n}"
  for h : i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    if localModule m then
      IO.println s!"MODULE {m}"
      for n in env.header.moduleData[i]!.constNames do
        let some ci := env.find? n | continue
        if used.contains n then IO.println s!"USED {n}"
        match ci with
        | .thmInfo _ => IO.println s!"THEOREM {n}"
        | .axiomInfo _ => throwError "custom local axiom: {n}"
        | _ => pure ()
end DirectAudit
