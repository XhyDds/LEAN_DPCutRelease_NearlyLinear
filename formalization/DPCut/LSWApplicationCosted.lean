import DPCut.CappedLSWRuntime
import DPCut.LSWCCKernel
import DPCut.ApplicationCosted

/-! Costed Appendix C reductions using the LSW-derived implementations.
The reference exact releases are used only for analysis, never as solver calls. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DPCut.LSWApplications

/-- The same verified primitives and external LSW hypothesis as Theorem 1. -/
def family (hLSW : LSWStatement) : CuttingPlaneFamily :=
  cuttingPlaneFamily hLSW verifiedLinearAlgebra

def costedCC (F : CuttingPlaneFamily) {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (base solver : Weights n → CostedLaw (Partition n)) (w : Weights n) : CostedLaw (Partition n) :=
  (base w).bind fun π₀ => .charge (vectorBlockCost n)
    ((CappedLSW.run F hn p hp Finset.univ (ccResidual π₀ w)).bind fun h =>
      (CostedLaw.sample (bernoulliRounding (ccResidual π₀ h)) (2 * vectorBlockCost n)).bind solver)

lemma costedCC_law (F : CuttingPlaneFamily) {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (base solver : Weights n → CostedLaw (Partition n))
    (Kbase Ksolver : Kernel (Weights n) (Partition n)) [IsMarkovKernel Kbase] [IsMarkovKernel Ksolver]
    (hbase : ∀ w, (base w).law = Kbase w) (hsolver : ∀ w, (solver w).law = Ksolver w) (w : Weights n) :
    (costedCC F hn p hp base solver w).law = ccPrivateKernel F hn p hp Kbase Ksolver w := by
  simp only [costedCC, CostedLaw.bind_law, CostedLaw.charge_law, CostedLaw.sample_law, hbase, hsolver]
  rfl

lemma costedCC_cost (F : CuttingPlaneFamily) {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (base solver : Weights n → CostedLaw (Partition n)) {B S : ℝ≥0∞}
    (hbase : ∀ w, (base w).cost ≤ B) (hsolver : ∀ w, (solver w).cost ≤ S) (w : Weights n) :
    (costedCC F hn p hp base solver w).cost ≤ B + CappedLSW.costBound F n p + 3 * vectorBlockCost n + S := by
  calc
    _ ≤ B + (vectorBlockCost n + (CappedLSW.costBound F n p + (2 * vectorBlockCost n + S))) := by
      apply CostedLaw.bind_cost_le _ _ (hbase w)
      intro π₀
      apply CostedLaw.charge_cost_le
      apply CostedLaw.bind_cost_le _ _ (CappedLSW.run_cost F hn p hp _ _)
      intro h
      exact CostedLaw.bind_cost_le _ _ (le_refl _) hsolver
    _ = _ := by ring

def costedPostprocess (F : CuttingPlaneFamily) {n : ℕ} {α : Type} [MeasurableSpace α]
    (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) (solver : Weights n → CostedLaw α) (w : Weights n) : CostedLaw α :=
  (LSWRelease.run F hn p hp w).bind solver

lemma costedPostprocess_law (F : CuttingPlaneFamily) {n : ℕ} {α : Type} [MeasurableSpace α]
    (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) (solver : Weights n → CostedLaw α)
    (K : Kernel (Weights n) α) (hK : ∀ w, (solver w).law = K w) (w : Weights n) :
    (costedPostprocess F hn p hp solver w).law = (LSWRelease.kernel F hn p hp w).bind K := by
  simp only [costedPostprocess, CostedLaw.bind_law, hK]
  rfl

lemma costedPostprocess_cost (F : CuttingPlaneFamily) {n : ℕ} {α : Type} [MeasurableSpace α]
    (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) (solver : Weights n → CostedLaw α)
    {B : ℝ≥0∞} (hB : ∀ w, (solver w).cost ≤ B) (w : Weights n) :
    (costedPostprocess F hn p hp solver w).cost ≤ LSWRelease.costBound F n p + B :=
  CostedLaw.bind_cost_le _ _ (LSWRelease.run_cost F hn p hp w) hB

lemma cc_composed_cost_polynomial (F : CuttingPlaneFamily) {γ ε s : ℝ}
    (hγ : 0 < γ) (hγ₁ : γ ≤ 1 / 4) (hε : 0 < ε) (hs : 0 < s)
    {B S : ℕ → ℝ≥0∞} (hB : PolynomialVertexBound B) (hS : PolynomialVertexBound S) :
    PolynomialVertexBound (fun n => B n + CappedLSW.costBound F n (ccParameters n γ ε) + 3 * vectorBlockCost n +
      (⌈Real.log (1 / ((n : ℝ)⁻¹ ^ 10)) / s⌉₊ : ℝ≥0∞) * (S n + 2 * vectorBlockCost n)) := by
  have h2 : PolynomialVertexBound (fun _ => (2 : ℝ≥0∞)) := by
    simpa using PolynomialVertexBound.constant 2 (by norm_num)
  have h3 : PolynomialVertexBound (fun _ => (3 : ℝ≥0∞)) := by
    simpa using PolynomialVertexBound.constant 3 (by norm_num)
  exact ((hB.add (CappedLSW.cc_cost_polynomial F hγ hγ₁ hε)).add
    (h3.mul vector_block_polynomial)).add
      ((amplification_repetitions_polynomial hs).mul (hS.add (h2.mul vector_block_polynomial)))

lemma postprocess_composed_cost_polynomial (F : CuttingPlaneFamily) {η ε : ℝ}
    (hη : 0 < η) (hη₁ : η ≤ 1 / 4) (hε : 0 < ε) {B : ℕ → ℝ≥0∞}
    (hB : PolynomialVertexBound B) :
    PolynomialVertexBound (fun n => LSWRelease.costBound F n (applicationParameters n η ε) + B n) :=
  ((LSWRelease.costBound_polynomial F).application hη hη₁ hε).add hB

end DPCut.LSWApplications
