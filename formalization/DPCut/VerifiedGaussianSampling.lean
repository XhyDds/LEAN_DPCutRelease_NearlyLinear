import DPCut.ScalarGaussianSampling
import DPCut.MatrixSPDArithmetic

/-! Covariance Gaussian batches generated from scalar normal draws and the
verified factor/matrix-vector algorithms. -/
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DPCut

def standardBatchProgram (n k : ℕ) : CostedLaw (Fin k → Fin n → ℝ) :=
  (scalarFiniteProduct (Fin k × Fin n) (gaussianReal 0 1)).map
    (fun z i j => z (i,j)) 0

lemma standardBatchProgram_law (n k : ℕ) :
    (standardBatchProgram n k).law = Measure.pi (fun _ : Fin k => standardGaussian n) := by
  rw [standardBatchProgram, CostedLaw.map_law, scalarFiniteProduct_law]
  exact (gaussianProduct_curry n k).map_eq

lemma standardBatchProgram_cost (n k : ℕ) : (standardBatchProgram n k).cost ≤ 2*(k*n) := by
  simpa [standardBatchProgram, CostedLaw.map, Fintype.card_prod] using
    scalarFiniteProduct_cost (Fin k × Fin n) (gaussianReal 0 1)

def countedBatchTransform {n k : ℕ} (L : Mat n) (z : Fin k → Fin n → ℝ) :
    Arithmetic (Fin k → Fin n → ℝ) :=
  Arithmetic.collect fun i => MatrixElimination.Counted.mulVec L (z i)

lemma countedBatchTransform_value {n k : ℕ} (L : Mat n) (z : Fin k → Fin n → ℝ) :
    (countedBatchTransform L z).value = fun i => L *ᵥ z i := by
  simp [countedBatchTransform]

lemma countedBatchTransform_steps {n k : ℕ} (L : Mat n) (z : Fin k → Fin n → ℝ) :
    (countedBatchTransform L z).steps = k*(n*(2*n+1)+1) := by
  simp [countedBatchTransform, Arithmetic.collect_steps, MatrixElimination.Counted.mulVec_steps]

def verifiedGaussianBatch {n : ℕ} (X : Mat n) (k : ℕ) : CostedLaw (Fin k → Fin n → ℝ) :=
  let L := MatrixElimination.Counted.factor X
  .charge L.steps ((standardBatchProgram n k).map
    (fun z => (countedBatchTransform L.value z).value) ((k*(n*(2*n+1)+1) : ℕ) : ℝ≥0∞))

lemma verifiedGaussianBatch_law {n : ℕ} (X : Mat n) (hX : X.PosDef) (k : ℕ) :
    (verifiedGaussianBatch X k).law = gaussianBatch X k := by
  simp only [verifiedGaussianBatch, CostedLaw.charge, CostedLaw.map_law, standardBatchProgram_law,
    MatrixElimination.Counted.factor_value, countedBatchTransform_value]
  exact MatrixElimination.factor_gaussianBatch_law X hX k

lemma verifiedGaussianBatch_cost {n : ℕ} (X : Mat n) (k : ℕ) :
    (verifiedGaussianBatch X k).cost ≤ gaussianBatchCost n k := by
  have hF := MatrixElimination.Counted.factor_steps X
  have hNat : (MatrixElimination.Counted.factor X).steps + 2*(k*n) + k*(n*(2*n+1)+1) ≤
      100*(n+1)^3*(k+1) := by
    nlinarith [Nat.zero_le (n^3), Nat.zero_le (n^2*k), Nat.zero_le (n^3*k)]
  change (MatrixElimination.Counted.factor X).steps +
    ((standardBatchProgram n k).cost + (k*(n*(2*n+1)+1) : ℕ)) ≤ _
  calc
    _ ≤ ((MatrixElimination.Counted.factor X).steps : ℝ≥0∞) +
        (2*((k : ℝ≥0∞)*n) + ((k*(n*(2*n+1)+1) : ℕ) : ℝ≥0∞)) :=
      add_le_add_left (add_le_add_right (standardBatchProgram_cost n k) _) _
    _ = (((MatrixElimination.Counted.factor X).steps + 2*(k*n) + k*(n*(2*n+1)+1) : ℕ) : ℝ≥0∞) := by push_cast; ring
    _ ≤ ((100*(n+1)^3*(k+1) : ℕ) : ℝ≥0∞) := by exact_mod_cast hNat
    _ = gaussianBatchCost n k := by unfold gaussianBatchCost vectorBlockCost; push_cast; ring

end DPCut
