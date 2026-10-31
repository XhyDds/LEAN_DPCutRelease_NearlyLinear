import DPCut.ChiSquare
import Mathlib.Probability.Independence.Basic

/-! Gaussian projection and feasibility facts needed for Lemma 10. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal MatrixOrder

namespace DPCut

lemma measurable_gaussian_transform {n : ℕ} (X : Mat n) :
    Measurable (fun z => (CFC.sqrt X).mulVec z) := by
  unfold Matrix.mulVec dotProduct
  fun_prop

instance gaussian_isProbabilityMeasure {n : ℕ} (X : Mat n) :
    IsProbabilityMeasure (gaussian X) := by
  exact Measure.isProbabilityMeasure_map (measurable_gaussian_transform X).aemeasurable

instance gaussianBatch_isProbabilityMeasure {n : ℕ} (X : Mat n) (k : ℕ) :
    IsProbabilityMeasure (gaussianBatch X k) := by
  unfold gaussianBatch
  infer_instance

lemma feasible_posDef {n : ℕ} (hn : 2 ≤ n) {X : Mat n} (hX : X ∈ feasible n) :
    X.PosDef := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := (Matrix.PosDef.one : (1 : Mat n).PosDef).smul (show 0 < 1 / (n : ℝ) by positivity)
  convert Matrix.PosDef.posSemidef_add hX.2.2 h using 1
  simp

lemma feasible_fractionalQuery_bounds {n : ℕ} (hn : 2 ≤ n) {X : Mat n}
    (hX : X ∈ feasible n) (e : Edge n) :
    0 < fractionalQuery X e ∧ fractionalQuery X e ≤ 1 := by
  have hpos := feasible_posDef hn hX
  have hij : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  have hsym : X e.val.2 e.val.1 = X e.val.1 e.val.2 := by
    simpa using hX.1.apply e.val.1 e.val.2
  have hv : (Pi.single e.val.1 1 - Pi.single e.val.2 1 : Fin n → ℝ) ≠ 0 := by
    intro h
    have := congrFun h e.val.1
    simp [hij] at this
  have hlo := hpos.2 _ hv
  have hhi := hpos.posSemidef.2 (Pi.single e.val.1 1 + Pi.single e.val.2 1)
  simp [Matrix.mulVec_sub, Matrix.mulVec_add,
    dotProduct_sub, dotProduct_add, hX.2.1, hsym] at hlo hhi
  constructor <;> dsimp [fractionalQuery] <;> linarith

/-- A linear combination of independent standard Gaussians has its expected variance. -/
lemma standardGaussian_map_sum {n : ℕ} (a : Fin n → ℝ) :
    (standardGaussian n).map (fun z => ∑ i, a i * z i) =
      gaussianReal 0 (∑ i, (⟨a i ^ 2, sq_nonneg (a i)⟩ : ℝ≥0)) := by
  classical
  let f : Fin n → (Fin n → ℝ) → ℝ := fun i z => a i * z i
  have hm : ∀ i, Measurable (f i) := by intro i; dsimp [f]; fun_prop
  have hi : iIndepFun f (standardGaussian n) :=
    iIndepFun_pi (fun i => (measurable_const_mul (a i)).aemeasurable)
  have hd (i : Fin n) : (standardGaussian n).map (f i) =
      gaussianReal 0 (⟨a i ^ 2, sq_nonneg (a i)⟩ : ℝ≥0) := by
    have he := (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).map_eq
    calc
      _ = ((standardGaussian n).map (Function.eval i)).map (a i * ·) := by
        exact (Measure.map_map (measurable_const_mul (a i))
          (show Measurable (Function.eval i : (Fin n → ℝ) → ℝ) from measurable_pi_apply i)).symm
      _ = (gaussianReal 0 1).map (a i * ·) := by rw [show (standardGaussian n).map (Function.eval i) = _ from he]
      _ = _ := by simp [gaussianReal_map_const_mul]
  have hs (s : Finset (Fin n)) :
      (standardGaussian n).map (∑ i ∈ s, f i) =
        gaussianReal 0 (∑ i ∈ s, (⟨a i ^ 2, sq_nonneg (a i)⟩ : ℝ≥0)) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty, gaussianReal_zero_var]
      exact (Measure.map_const (μ := standardGaussian n) (0 : ℝ)).trans (by simp)
    | @insert i s his ih =>
      rw [Finset.sum_insert his, Finset.sum_insert his]
      convert gaussianReal_add_gaussianReal_of_indepFun
        (hi.indepFun_finset_sum_of_notMem hm his).symm (hd i) ih using 1
      simp
  have hf : (∑ i : Fin n, f i) = (fun z => ∑ i, a i * z i) := by
    ext z
    simp [f]
  rw [← hf]
  exact hs Finset.univ

/-- Normalize one edge difference by its standard deviation. -/
def normalizedEdge {n : ℕ} (X : Mat n) (e : Edge n) (z : Fin n → ℝ) : ℝ :=
  (z e.val.1 - z e.val.2) / (2 * Real.sqrt (fractionalQuery X e))

lemma measurable_normalizedEdge {n : ℕ} (X : Mat n) (e : Edge n) :
    Measurable (normalizedEdge X e) := by
  unfold normalizedEdge
  fun_prop

lemma sqrt_row_difference_sq {n : ℕ} {X : Mat n} (hX : X.PosSemidef)
    (hd : ∀ i, X i i = 1) (e : Edge n) :
    (∑ i, ((CFC.sqrt X) e.val.1 i - (CFC.sqrt X) e.val.2 i) ^ 2) =
      4 * fractionalQuery X e := by
  have hs : ∀ i j, (CFC.sqrt X) j i = (CFC.sqrt X) i j := by
    intro i j
    simpa using (CFC.sqrt_nonneg X).posSemidef.isHermitian.apply i j
  have hp (i j : Fin n) :
      (∑ l, (CFC.sqrt X) i l * (CFC.sqrt X) j l) = X i j := by
    have h := congrArg (fun A : Mat n => A i j) (CFC.sqrt_mul_sqrt_self X hX.nonneg)
    simpa only [Matrix.mul_apply, hs j] using h
  calc
    _ = (∑ i, (CFC.sqrt X) e.val.1 i * (CFC.sqrt X) e.val.1 i) +
        (∑ i, (CFC.sqrt X) e.val.2 i * (CFC.sqrt X) e.val.2 i) -
        2 * (∑ i, (CFC.sqrt X) e.val.1 i * (CFC.sqrt X) e.val.2 i) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _; ring
    _ = _ := by rw [hp, hp, hp, hd, hd]; unfold fractionalQuery; ring

/-- The exact standard-normal marginal used in Lemma 10, for the implemented covariance law. -/
lemma gaussian_map_normalizedEdge {n : ℕ} (hn : 2 ≤ n) {X : Mat n}
    (hX : X ∈ feasible n) (e : Edge n) :
    (gaussian X).map (normalizedEdge X e) = gaussianReal 0 1 := by
  let q := fractionalQuery X e
  let a : Fin n → ℝ := fun i =>
    ((CFC.sqrt X) e.val.1 i - (CFC.sqrt X) e.val.2 i) / (2 * Real.sqrt q)
  have hq : 0 < q := (feasible_fractionalQuery_bounds hn hX e).1
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hsq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq.le
  have ha : (∑ i, a i ^ 2) = 1 := by
    simp only [a, div_pow, mul_pow, hsq]
    rw [← Finset.sum_div, sqrt_row_difference_sq (feasible_posDef hn hX).posSemidef hX.2.1 e]
    change (4 * q) / (2 ^ 2 * q) = 1
    field_simp
    ring
  have haNN : (∑ i, (⟨a i ^ 2, sq_nonneg (a i)⟩ : ℝ≥0)) = 1 := by
    apply NNReal.coe_injective
    change (↑(∑ i, (⟨a i ^ 2, sq_nonneg (a i)⟩ : ℝ≥0)) : ℝ) = 1
    exact (NNReal.coe_sum Finset.univ (fun i : Fin n =>
      (⟨a i ^ 2, sq_nonneg (a i)⟩ : ℝ≥0))).trans ha
  unfold gaussian
  rw [Measure.map_map (measurable_normalizedEdge X e) (measurable_gaussian_transform X)]
  have he : normalizedEdge X e ∘ (fun z => (CFC.sqrt X).mulVec z) =
      (fun z => ∑ i, a i * z i) := by
    ext z
    simp only [Function.comp_apply, normalizedEdge, Matrix.mulVec, dotProduct, a, q,
      div_mul_eq_mul_div, sub_mul]
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
  rw [he, standardGaussian_map_sum, haNN]

lemma gaussianBatch_map_normalizedEdge {n : ℕ} (hn : 2 ≤ n) {X : Mat n}
    (hX : X ∈ feasible n) (e : Edge n) (k : ℕ) :
    (gaussianBatch X k).map (fun z j => normalizedEdge X e (z j)) = standardGaussian k := by
  unfold gaussianBatch standardGaussian
  rw [Measure.pi_map_pi (fun _ => (measurable_normalizedEdge X e).aemeasurable)]
  simp_rw [gaussian_map_normalizedEdge hn hX e]

end DPCut
