import Oscillation
import Lean.Util.CollectAxioms

open Lean Elab Command

-- Inspect internal Names directly, including generated and private theorems.
run_cmd do
  let env ← getEnv
  for h : i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    if (`Oscillation).isPrefixOf m || (`Riesz).isPrefixOf m then
      for n in env.header.moduleData[i]!.constNames do
        if let some (.thmInfo _) := env.find? n then
          let axioms ← collectAxioms n
          for ax in axioms do
            unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
              throwError "unexpected axiom {ax} in {n}"
          IO.println s!"AXIOMS {n} [{String.intercalate ", " (axioms.toList.map toString)}]"
