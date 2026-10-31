import DPCut.SDPGeometry
import DPCut.RelativeMatrix

/-! Attainment and the first-order inequality for the regularized SDP. -/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise

namespace DPCut

lemma matrixOptimizer_first_order {n : ℕ} (hn : 2 ≤ n) {lam : ℝ}
    {A X : Mat n} (hX : IsMatrixOptimizer lam A X) {Y : Mat n} (hY : Y ∈ feasible n) :
    matrixPairing A (Y - X) + lam * (X⁻¹ * (Y - X)).trace ≤ 0 := by
  let f : ℝ → ℝ := fun t => matrixPairing A (X + t • (Y - X)) +
    lam * Real.log (X + t • (Y - X)).det
  have hp : HasDerivAt (fun t : ℝ => matrixPairing A (X + t • (Y - X)))
      (matrixPairing A (Y - X)) 0 := by
    unfold matrixPairing
    convert HasDerivAt.sum (u := Finset.univ) (fun i _ =>
      HasDerivAt.sum (u := Finset.univ) (fun j _ =>
        (((hasDerivAt_id (0 : ℝ)).mul_const ((Y - X) i j)).const_add (X i j)).const_mul
          (A i j))) using 1 <;> simp
    ext t
    simp
  have hf : HasDerivAt f
      (matrixPairing A (Y - X) + lam * (X⁻¹ * (Y - X)).trace) 0 :=
    hp.add ((hasDerivAt_logdet (feasible_posDef hn hX.1) (Y - X)).const_mul lam)
  have hm : IsMaxOn f (Set.Icc 0 1) 0 := by
    intro t ht
    have hseg : X + t • (Y - X) ∈ feasible n := by
      have he : X + t • (Y - X) = (1 - t) • X + t • Y := by module
      rw [he]
      exact feasible_convex n hX.1 hY (sub_nonneg.mpr ht.2) ht.1 (by ring)
    simpa [f] using hX.2 _ hseg
  have ht : (1 : ℝ) ∈ posTangentConeAt (Set.Icc 0 1) 0 := by
    simpa using sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc (0 : ℝ) 1).segment_subset ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩)
  have hl : IsLocalMaxOn f (Set.Icc 0 1) 0 :=
    Filter.eventually_of_mem self_mem_nhdsWithin hm
  simpa using hl.hasFDerivWithinAt_nonpos hf.hasFDerivAt.hasFDerivWithinAt ht

lemma isOptimizer_iff_matrixOptimizer {n : ℕ} (lam : ℝ) (D : Weights n) (X : Mat n) :
    IsOptimizer lam D X ↔ IsMatrixOptimizer lam (objectiveMatrix D) X := by
  constructor
  · rintro ⟨hX, hm⟩
    refine ⟨hX, fun Y hY => ?_⟩
    simpa [matrixPairing_objectiveMatrix D hX, matrixPairing_objectiveMatrix D hY, objective]
      using hm Y hY
  · rintro ⟨hX, hm⟩
    refine ⟨hX, fun Y hY => ?_⟩
    simpa [matrixPairing_objectiveMatrix D hX, matrixPairing_objectiveMatrix D hY, objective]
      using hm Y hY

lemma optimizer_isOptimizer {n : ℕ} (hn : 2 ≤ n) (lam : ℝ) (D : Weights n) :
    IsOptimizer lam D (optimizer lam D) := by
  have he := optimizer_exists hn lam D
  unfold optimizer
  rw [dif_pos he]
  exact Classical.choose_spec he

lemma optimum_eq_objective_optimizer {n : ℕ} (hn : 2 ≤ n) (lam : ℝ) (D : Weights n) :
    optimum lam D = objective lam D (optimizer lam D) := by
  have hx := optimizer_isOptimizer hn lam D
  apply IsGreatest.csSup_eq
  refine ⟨⟨_, hx.1, rfl⟩, ?_⟩
  rintro _ ⟨Y, hY, rfl⟩
  exact hx.2 Y hY

lemma matrixOptimizer_energy {n : ℕ} (hn : 2 ≤ n) {lam : ℝ}
    {A B X Y : Mat n} (hX : IsMatrixOptimizer lam A X) (hY : IsMatrixOptimizer lam B Y) :
    lam * covarianceDistance X Y ^ 2 ≤ matrixPairing (B - A) (Y - X) := by
  have hx := matrixOptimizer_first_order hn hX hY.1
  have hy := matrixOptimizer_first_order hn hY hX.1
  have hneg : X - Y = -(Y - X) := by abel
  rw [hneg, Matrix.mul_neg, Matrix.trace_neg] at hy
  have hp : matrixPairing B (-(Y - X)) = -matrixPairing B (Y - X) := by
    simp only [matrixPairing, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib]
  rw [hp] at hy
  rw [covarianceDistance_sq (feasible_posDef hn hX.1) (feasible_posDef hn hY.1),
    Matrix.sub_mul, Matrix.trace_sub, matrixPairing_sub_left]
  linarith

lemma matrixOptimizer_unique {n : ℕ} (hn : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    {A X Y : Mat n} (hX : IsMatrixOptimizer lam A X) (hY : IsMatrixOptimizer lam A Y) : X = Y := by
  have he := matrixOptimizer_energy hn hX hY
  simp only [sub_self, matrixPairing, Matrix.zero_apply, zero_mul, Finset.sum_const_zero] at he
  have hs : covarianceDistance X Y ^ 2 ≤ 0 :=
    le_of_mul_le_mul_left (by simpa using he : lam * covarianceDistance X Y ^ 2 ≤ lam * 0) hlam
  apply (covarianceDistance_eq_zero_iff (feasible_posDef hn hX.1) (feasible_posDef hn hY.1)).mp
  nlinarith [sq_nonneg (covarianceDistance X Y)]

lemma optimizer_unique {n : ℕ} (hn : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    {D : Weights n} {X Y : Mat n} (hX : IsOptimizer lam D X) (hY : IsOptimizer lam D Y) : X = Y :=
  matrixOptimizer_unique hn hlam ((isOptimizer_iff_matrixOptimizer lam D X).mp hX)
    ((isOptimizer_iff_matrixOptimizer lam D Y).mp hY)

/-- The named choices `X_D` and `F(D)` are the unique optimizer and its attained value. -/
theorem optimizer_foundations : OptimizerStatement := by
  intro n hn lam hlam D
  have hx := optimizer_isOptimizer hn lam D
  exact ⟨⟨optimizer lam D, hx, fun Y hY => optimizer_unique hn hlam hY hx⟩,
    hx, optimum_eq_objective_optimizer hn lam D⟩

lemma matrixOptimizer_exists_unique {n : ℕ} (hn : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (A : Mat n) : ∃! X, IsMatrixOptimizer lam A X := by
  have hc : ContinuousOn (fun X : Mat n => matrixPairing A X + lam * Real.log X.det)
      (feasible n) := by
    apply ContinuousOn.add
    · exact (show Continuous (fun X : Mat n => matrixPairing A X) by
        unfold matrixPairing; fun_prop).continuousOn
    · exact continuousOn_const.mul (continuous_id.matrix_det.continuousOn.log
        (fun X hX => (feasible_posDef hn hX).det_pos.ne'))
  obtain ⟨X, hX, hm⟩ := (feasible_compact hn).exists_isMaxOn ⟨1, feasible_one hn⟩ hc
  exact ⟨X, ⟨hX, hm⟩, fun Y hY => matrixOptimizer_unique hn hlam hY ⟨hX, hm⟩⟩

end DPCut
