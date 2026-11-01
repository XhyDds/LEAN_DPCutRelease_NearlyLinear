import DPCut.ImplementedApplications
import Lean.Util.FoldConsts

/-! Regression checks for the implementation connections, in addition to the
axiom audits. Merely importing an implementation certificate is insufficient.
These checks establish use of the certificates, not an operational cost semantics. -/
open DPCut

-- The actual LSW oracle uses the counted scalar program, including its cost.
example {n : ℕ} (hn : 2 ≤ n) {lam B : ℝ} (hlam : 0 ≤ lam) (hB : 0 ≤ B)
    (q : Weights n × SDPCoordinates.Space n) :
    (SDPCoordinates.oracle hn hlam hB verifiedLinearAlgebra).answer q =
      SDPCoordinates.Counted.answer lam B q := rfl

-- Choosing an LSW family preserves the supplied implementation, so its
-- decoder is the concrete counted decoder, not an arbitrary feasible function.
example (hLSW : LSWStatement) {n : ℕ} (hn : 2 ≤ n)
    (o : Option (SDPCoordinates.Space n)) :
    (SDPCoordinates.decodeArithmetic
      (cuttingPlaneFamily hLSW verifiedLinearAlgebra).implementation hn o).steps =
      (SDPCoordinates.Counted.decode o).steps := by
  rw [cuttingPlaneFamily_implementation]
  rfl

set_option maxHeartbeats 2000000 in
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let checks : Array (Name × Array Name) := #[
    (``DPCut.SDPCoordinates.oracle,
      #[``DPCut.LinearAlgebraImplementation.oracleProgram,
        ``DPCut.LinearAlgebraImplementation.oracle_value,
        ``DPCut.LinearAlgebraImplementation.oracle_cost]),
    (``DPCut.SDPCoordinates.solve,
      #[``DPCut.CostedLaw.mapArithmetic, ``DPCut.LinearAlgebraImplementation.decodeProgram]),
    (``DPCut.SDPCoordinates.solve_law, #[``DPCut.LinearAlgebraImplementation.decode_value]),
    (``DPCut.SDPCoordinates.solve_cost, #[``DPCut.LinearAlgebraImplementation.decode_cost]),
    (``DPCut.ApproxSDPCosted.trials, #[``DPCut.verifiedGaussianBatch]),
    (``DPCut.ApproxSDPCosted.trials_law, #[``DPCut.verifiedGaussianBatch_law]),
    (``DPCut.ApproxSDPCosted.trials_cost, #[``DPCut.verifiedGaussianBatch_cost])]
  let publicRoots : Array Name := #[``DPCut.theorem1_of_lsw,
    ``DPCut.CappedLSW.capped_release_of_lsw,
    ``DPCut.cc_reduction_runtime, ``DPCut.max_k_reduction_runtime,
    ``DPCut.constrained_reduction_runtime, ``DPCut.hierarchy_reduction_runtime,
    ``DPCut.LSWApplications.theorem30, ``DPCut.LSWApplications.theorem32,
    ``DPCut.LSWApplications.theorem34, ``DPCut.LSWApplications.theorem36]
  let connected := #[``DPCut.SDPCoordinates.oracle, ``DPCut.SDPCoordinates.solve_cost,
    ``DPCut.ApproxSDPCosted.trials_law, ``DPCut.ApproxSDPCosted.trials_cost]
  for (root, required) in checks ++ publicRoots.map (fun root => (root, connected)) do
    let mut pending := #[root]
    let mut visited : NameSet := {}
    while !pending.isEmpty do
      let name := pending.back!
      pending := pending.pop
      unless visited.contains name do
        visited := visited.insert name
        -- Do not count proofs merely stored in the constructed certificate as
        -- evidence that the program or theorem actually uses those proofs.
        unless name == ``DPCut.verifiedLinearAlgebra do
          if let some info := env.find? name then
            for dep in info.getUsedConstantsAsSet do
              if Name.isPrefixOf `DPCut (privateToUserName dep) then
                pending := pending.push dep
    for dep in required do
      unless visited.contains dep do
        throwError "Implementation connection missing: {root} must use {dep}"
  logInfo "Implementation audit passed: counted oracle/decoder and verified Gaussian sampling are connected to Theorem 1 and applications."
