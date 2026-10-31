import DPCut
import Lean.Util.CollectAxioms

/-! Fail the check if any project declaration transitively depends on an
admission or an axiom other than Lean's three standard logical axioms.
This checks proof dependencies, not whether an unproved specification has a
witness. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := env.constants.toList.filterMap fun (name, _) =>
    if Name.isPrefixOf `DPCut (privateToUserName name) then some name else none
  let (_, state) := ((roots.forM CollectAxioms.collect).run env).run {}
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := state.axioms.filter fun name => !allowed.contains name
  unless forbidden.isEmpty do
    throwError "Project axiom audit failed: {forbidden}"
  logInfo m!"Project axiom audit passed: {roots.length} declarations; axioms {state.axioms}."
