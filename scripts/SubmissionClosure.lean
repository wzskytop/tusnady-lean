import R56Audit
import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for root in [`R56Audit.theorem_1_1_unfolded, `R56Audit.corollary_1_2_lower] do
    let mut todo := #[root]
    let mut seen : NameSet := {}
    let mut axioms : NameSet := {}
    let mut modules : NameSet := {}
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.find? n | throwError "missing {n}"
      if (`Oscillation.Direct).isPrefixOf n || (`Oscillation.R56).isPrefixOf n || (`Oscillation.R65).isPrefixOf n ||
          n == `Oscillation.paper_lower_bound || n == `Oscillation.gridPotential then
        throwError "old proof reached: {n}"
      if let .axiomInfo _ := ci then
        axioms := axioms.insert n
        unless [ `propext, `Classical.choice, `Quot.sound ].contains n do
          throwError "unexpected axiom: {n}"
      if let some i := env.getModuleIdxFor? n then
        let m := env.header.moduleNames[i.toNat]!
        if (`R56Audit).isPrefixOf m then modules := modules.insert m
      for d in ci.getUsedConstantsAsSet do todo := todo.push d
    for required in [`R56Audit.proposition_2_7, `R56Audit.roadmap_digits,
        `R56Audit.local_gain, `R56Audit.fact_2_2_general, `R56Audit.fact_A_1,
        `R56Audit.lemma_2_4_digits, `R56Audit.lemma_2_5_ii,
        `R56Audit.lemma_2_6_digits, `R56Audit.condExp_digitSigma] do
      unless seen.contains required do throwError "missing route node: {required}"
    IO.println s!"INDEPENDENT {root}: {seen.size} constants traversed without module filtering; {modules.size} supplement modules; axioms {axioms.toList}; required paper route present; old proof absent"
