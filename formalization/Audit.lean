import DPCut
import Lean.Util.CollectAxioms

/-!
# Audit

Run `lake env lean Audit.lean` after `lake build`. This file

1. prints the axioms of the main results, which are only Lean's standard axioms
   `propext`, `Classical.choice`, and `Quot.sound`;
2. checks the same for every declaration of the project, so that no proof is admitted
   with `sorry` and no axiom is added;
3. checks that the proof of `theorem1_machine` uses the machine execution, the SDP
   oracle program, and the ellipsoid solver, and none of the assigned-cost interfaces;
4. checks that the assigned-cost results for Appendix C use no SDP-oracle contract.
-/

#print axioms DPCut.theorem1_machine
#print axioms DPCut.theorem1_statistical
#print axioms DPCut.advanced_composition_statement
#print axioms DPCut.lemma10
#print axioms DPCut.lemma11
#print axioms DPCut.lemma12
#print axioms DPCut.lemma13
#print axioms DPCut.lemma14
#print axioms DPCut.lemma15
#print axioms DPCut.lemma16
#print axioms DPCut.lemma17
#print axioms DPCut.lemma18
#print axioms DPCut.lemma19
#print axioms DPCut.lemma20
#print axioms DPCut.lemma21
#print axioms DPCut.lemma22
#print axioms DPCut.lemma23
#print axioms DPCut.laplace_statement
#print axioms DPCut.theorem38
#print axioms DPCut.lemma28
#print axioms DPCut.lemma29
#print axioms DPCut.theorem30
#print axioms DPCut.corollary31
#print axioms DPCut.private_correlation_clustering
#print axioms DPCut.theorem32
#print axioms DPCut.private_max_cut
#print axioms DPCut.remark33
#print axioms DPCut.theorem34
#print axioms DPCut.lemma35
#print axioms DPCut.theorem36
#print axioms DPCut.theorem1_of_lsw

open Lean Elab Command

/-- The project declarations on which `roots` depend, including the roots. -/
def projectDependencies (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut pending := roots
  let mut visited : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless visited.contains name do
      visited := visited.insert name
      if let some info := env.find? name then
        for dep in info.getUsedConstantsAsSet do
          -- Imported Lean/mathlib declarations cannot depend on this project.
          if Name.isPrefixOf `DPCut (privateToUserName dep) then
            pending := pending.push dep
  return visited

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

run_cmd do
  let env ← getEnv
  let used := projectDependencies env #[``DPCut.theorem1_machine]
  let forbidden : Array Name := #[``DPCut.LSWStatement, ``DPCut.CuttingPlaneFamily,
    ``DPCut.TimedAlgorithm, ``DPCut.ExactSDPOracleCost, ``DPCut.ApproxSDPOracle]
  for name in forbidden do
    if used.contains name then
      throwError "theorem1_machine depends on an assigned-cost interface: {name}"
  let required : Array Name := #[``DPCut.RealMachine.Code.execute,
    ``DPCut.RealMachine.EllipsoidCode.solverProgram_accurate,
    ``DPCut.RealMachine.EllipsoidCode.solverProgram_steps,
    ``DPCut.RealMachine.SDP.oracleProgram_value,
    ``DPCut.TypedMachine.Command.run, ``DPCut.TypedMachine.Budget.execution_bound,
    ``DPCut.TypedMachine.implementedLaw_reference]
  for name in required do
    unless used.contains name do
      throwError "theorem1_machine does not use {name}"
  logInfo "Machine theorem audit passed: no assigned-cost interface; all required execution links present."

run_cmd do
  let env ← getEnv
  let used := projectDependencies env #[``DPCut.hierarchy_reduction_runtime,
    ``DPCut.cc_reduction_runtime, ``DPCut.max_k_reduction_runtime,
    ``DPCut.constrained_reduction_runtime,
    ``DPCut.CappedLSW.cost_polynomial,
    ``DPCut.CappedLSW.capped_release_of_lsw,
    ``DPCut.LSWApplications.private_cc_reduction,
    ``DPCut.LSWApplications.theorem30,
    ``DPCut.LSWApplications.corollary31,
    ``DPCut.LSWApplications.private_correlation_clustering,
    ``DPCut.LSWApplications.theorem32,
    ``DPCut.LSWApplications.private_max_cut,
    ``DPCut.LSWApplications.constrained_cut_general,
    ``DPCut.LSWApplications.theorem34,
    ``DPCut.LSWApplications.theorem36]
  for name in #[``DPCut.ExactSDPOracleCost, ``DPCut.ApproxSDPOracle] do
    if used.contains name then
      throwError "An Appendix C cost result depends on an SDP-oracle contract: {name}"
  logInfo "Appendix C cost audit passed: no SDP-oracle contract."
