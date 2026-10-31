import DPCut.OneSidedMoment
import DPCut.Lemma10

/-! The unclipped batch witness as a Gaussian quadratic form, for Lemma 11. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal MatrixOrder

namespace DPCut

lemma gaussianProduct_curry (n k : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin k) (Fin n) ℝ)
      (gaussianProduct (Fin k × Fin n))
      (Measure.pi (fun _ : Fin k => standardGaussian n)) := by
  apply MeasurePreserving.symm (MeasurableEquiv.curry (Fin k) (Fin n) ℝ).symm
  refine ⟨(MeasurableEquiv.curry (Fin k) (Fin n) ℝ).symm.measurable, ?_⟩
  apply Eq.symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  have he : (MeasurableEquiv.curry (Fin k) (Fin n) ℝ).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun j => Set.univ.pi (fun i => s (j, i))) := by
    ext z
    simp [MeasurableEquiv.curry, Set.mem_pi, Prod.forall]
  rw [he, Measure.pi_pi]
  simp only [standardGaussian, Measure.pi_pi, Fintype.prod_prod_type]

def batchTransform {n k : ℕ} (X : Mat n) (z : Fin k × Fin n → ℝ) : Fin k → Fin n → ℝ :=
  fun j => (CFC.sqrt X).mulVec (fun i => z (j, i))

lemma measurable_batchTransform {n k : ℕ} (X : Mat n) :
    Measurable (batchTransform (k := k) X) := by
  unfold batchTransform Matrix.mulVec dotProduct
  fun_prop

lemma gaussianProduct_map_batchTransform {n k : ℕ} (X : Mat n) :
    (gaussianProduct (Fin k × Fin n)).map (batchTransform X) = gaussianBatch X k := by
  have he : batchTransform (k := k) X =
      (fun z : Fin k → Fin n → ℝ => fun j => (CFC.sqrt X).mulVec (z j)) ∘
        (MeasurableEquiv.curry (Fin k) (Fin n) ℝ) := rfl
  rw [he, ← Measure.map_map (by
    exact measurable_pi_lambda _ (fun j => (measurable_gaussian_transform X).comp (measurable_pi_apply j)))
    (MeasurableEquiv.curry (Fin k) (Fin n) ℝ).measurable, (gaussianProduct_curry n k).map_eq]
  exact Measure.pi_map_pi (fun _ => (measurable_gaussian_transform X).aemeasurable)

def unclippedScore {n k : ℕ} (D : Weights n) (z : Fin k → Fin n → ℝ) : ℝ :=
  pairing D (fun e => rawWitness z e / 2)

lemma measurable_unclippedScore {n k : ℕ} (D : Weights n) :
    Measurable (unclippedScore (k := k) D) := by
  unfold unclippedScore pairing rawWitness
  fun_prop

def witnessCoefficient {n k : ℕ} (X : Mat n) (j : Fin k) (e : Edge n)
    (r : Fin k × Fin n) : ℝ :=
  if r.1 = j then (CFC.sqrt X) e.val.1 r.2 - (CFC.sqrt X) e.val.2 r.2 else 0

def witnessQuadraticMatrix {n : ℕ} (k : ℕ) (D : Weights n) (X : Mat n) :
    Matrix (Fin k × Fin n) (Fin k × Fin n) ℝ :=
  ∑ j, ∑ e, (D e / (8 * k)) •
    Matrix.vecMulVec (witnessCoefficient X j e) (witnessCoefficient X j e)

lemma witnessCoefficient_dot {n k : ℕ} (X : Mat n) (j : Fin k) (e : Edge n)
    (z : Fin k × Fin n → ℝ) :
    witnessCoefficient X j e ⬝ᵥ z = batchTransform X z j e.val.1 - batchTransform X z j e.val.2 := by
  simp [witnessCoefficient, dotProduct, Fintype.sum_prod_type, batchTransform,
    Matrix.mulVec, sub_mul, Finset.sum_sub_distrib, ite_mul]

lemma witnessQuadraticMatrix_isHermitian {n : ℕ} (k : ℕ) (D : Weights n) (X : Mat n) :
    (witnessQuadraticMatrix k D X).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [witnessQuadraticMatrix, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, star_trivial]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro e _
  ring

lemma quadratic_vecMulVec {ι : Type*} [Fintype ι] (v z : ι → ℝ) :
    quadratic (Matrix.vecMulVec v v) z = (v ⬝ᵥ z) ^ 2 := by
  simp only [quadratic, Matrix.vecMulVec_mulVec, dotProduct_smul]
  rw [dotProduct_comm z v]
  change (v ⬝ᵥ z) * (v ⬝ᵥ z) = (v ⬝ᵥ z) ^ 2
  ring

lemma witnessQuadratic_eq {n k : ℕ} (D : Weights n) (X : Mat n) (z : Fin k × Fin n → ℝ) :
    quadratic (witnessQuadraticMatrix k D X) z = unclippedScore D (batchTransform X z) := by
  simp only [witnessQuadraticMatrix, quadratic, Matrix.sum_mulVec, dotProduct_sum,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  change (∑ j, ∑ e, (D e / (8 * k)) * quadratic
    (Matrix.vecMulVec (witnessCoefficient X j e) (witnessCoefficient X j e)) z) = _
  simp_rw [quadratic_vecMulVec, witnessCoefficient_dot]
  rw [Finset.sum_comm]
  unfold unclippedScore pairing rawWitness
  apply Finset.sum_congr rfl
  intro e _
  dsimp only
  rw [← Finset.mul_sum, ← Finset.sum_div]
  ring

lemma witnessCoefficient_sum_sq {n k : ℕ} (hn : 2 ≤ n) {X : Mat n}
    (hX : X ∈ feasible n) (j : Fin k) (e : Edge n) :
    (∑ r : Fin k × Fin n, witnessCoefficient X j e r ^ 2) = 4 * fractionalQuery X e := by
  simp only [Fintype.sum_prod_type, witnessCoefficient, ite_pow, zero_pow (by norm_num : 2 ≠ 0)]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact sqrt_row_difference_sq (feasible_posDef hn hX).posSemidef hX.2.1 e

lemma witnessQuadratic_trace {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (hk : 0 < k)
    (D : Weights n) {X : Mat n} (hX : X ∈ feasible n) :
    (witnessQuadraticMatrix k D X).trace = pairing D (fractionalQuery X) / 2 := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  simp only [witnessQuadraticMatrix, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  have ht (j : Fin k) (e : Edge n) :
      (Matrix.vecMulVec (witnessCoefficient X j e) (witnessCoefficient X j e)).trace =
        4 * fractionalQuery X e := by
    simpa only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, ← pow_two] using
      witnessCoefficient_sum_sq hn hX j e
  simp_rw [ht]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold pairing
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  field_simp
  ring

/-- The unclipped score has uniformly positive probability of reaching its exact mean. -/
theorem unclippedScore_above_mean {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (hk : 0 < k)
    (D : Weights n) {X : Mat n} (hX : X ∈ feasible n) :
    (1 / 1024 : ℝ) ≤ prob (gaussianBatch X k)
      {z | pairing D (fractionalQuery X) / 2 ≤ unclippedScore D z} := by
  let A := witnessQuadraticMatrix k D X
  have hA : A.IsHermitian := witnessQuadraticMatrix_isHermitian k D X
  have h := gaussian_quadratic_above_mean hA
  rw [(gaussian_quadratic_moments hA).1, witnessQuadratic_trace hn k hk D hX] at h
  unfold prob at h ⊢
  rw [← gaussianProduct_map_batchTransform, Measure.map_apply (measurable_batchTransform X)
    (measurableSet_le measurable_const (measurable_unclippedScore D))]
  convert h using 1
  congr 2
  ext z
  simp only [Set.mem_preimage, Set.mem_setOf_eq, witnessQuadratic_eq, A]

end DPCut
