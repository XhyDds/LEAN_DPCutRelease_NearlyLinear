import DPCut.ChiSquare
import DPCut.GaussianMoments
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Exponential moments and the signed Laurent–Massart bound for Lemma 15. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace DPCut

private lemma log_one_add_lower {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 2 / 2 ≤ Real.log (1 + x) := by
  let f : ℝ → ℝ := fun y => Real.log (1 + y) - y + y ^ 2 / 2
  have hd (y : ℝ) (hy : y ∈ Set.Icc 0 x) :
      HasDerivWithinAt f (1 / (1 + y) - 1 + y) (Set.Icc 0 x) y := by
    have hp : 1 + y ≠ 0 := by linarith [hy.1]
    convert (((((hasDerivAt_id y).const_add 1).log hp).sub (hasDerivAt_id y)).add
      (((hasDerivAt_id y).pow 2).div_const 2)).hasDerivWithinAt using 1
    dsimp [f]
    ring
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) x)
    (fun y hy => (hd y hy).continuousWithinAt)
    (fun y hy => (hd y (interior_subset hy)).mono interior_subset)
    (fun y hy => by
      have hy := interior_subset hy
      have hp : 0 < 1 + y := by linarith [hy.1]
      have he : 1 / (1 + y) - 1 + y = y ^ 2 / (1 + y) := by field_simp; ring
      rw [he]
      positivity)
  have h := hm ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
  dsimp [f] at h
  norm_num at h
  linarith

private lemma log_one_sub_lower {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    -Real.log (1 - x) - x ≤ x ^ 2 / (2 * (1 - x)) := by
  let f : ℝ → ℝ := fun y => Real.log (1 - y) + y + y ^ 2 / (2 * (1 - x))
  have hd (y : ℝ) (hy : y ∈ Set.Icc 0 x) :
      HasDerivWithinAt f (-1 / (1 - y) + 1 + y / (1 - x)) (Set.Icc 0 x) y := by
    have hp : 1 - y ≠ 0 := by linarith [hy.2]
    convert (((((hasDerivAt_id y).const_sub 1).log hp).add (hasDerivAt_id y)).add
      (((hasDerivAt_id y).pow 2).div_const (2 * (1 - x)))).hasDerivWithinAt using 1
    dsimp [f]
    field_simp
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) x)
    (fun y hy => (hd y hy).continuousWithinAt)
    (fun y hy => (hd y (interior_subset hy)).mono interior_subset)
    (fun y hy => by
      have hy := interior_subset hy
      have hp : 0 < 1 - y := by linarith [hy.2]
      have hq : 0 < 1 - x := by linarith
      have he : -1 / (1 - y) + 1 + y / (1 - x) =
          y * (x - y) / ((1 - y) * (1 - x)) := by field_simp; ring
      rw [he]
      exact div_nonneg (mul_nonneg hy.1 (sub_nonneg.mpr hy.2)) (mul_pos hp hq).le)
  have h := hm ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
  dsimp [f] at h
  norm_num at h
  linarith

lemma centered_log_mgf_le {a b s : ℝ} (hab : |a| ≤ b) (hs : 0 ≤ s)
    (hsb : 2 * s * b < 1) :
    -s * a - Real.log (1 - 2 * s * a) / 2 ≤ s ^ 2 * a ^ 2 / (1 - 2 * s * b) := by
  have hb : 0 ≤ b := (abs_nonneg a).trans hab
  have hp : 0 < 1 - 2 * s * b := by linarith
  have ha : a ≤ b := (le_abs_self a).trans hab
  by_cases hsa : 0 ≤ 2 * s * a
  · have hsa1 : 2 * s * a < 1 := (mul_le_mul_of_nonneg_left ha (by positivity)).trans_lt hsb
    have hl := log_one_sub_lower hsa hsa1
    have hden : 1 - 2 * s * b ≤ 1 - 2 * s * a := by nlinarith
    have hdiv := div_le_div_of_nonneg_left (sq_nonneg (2 * s * a))
      (by positivity : 0 < 2 * (1 - 2 * s * b)) (by linarith :
        2 * (1 - 2 * s * b) ≤ 2 * (1 - 2 * s * a))
    have he : (2 * s * a) ^ 2 / (2 * (1 - 2 * s * b)) =
        2 * (s ^ 2 * a ^ 2 / (1 - 2 * s * b)) := by field_simp
    rw [he] at hdiv
    linarith
  · have hl := log_one_add_lower (show 0 ≤ -(2 * s * a) by linarith)
    have hdiv : s ^ 2 * a ^ 2 ≤ s ^ 2 * a ^ 2 / (1 - 2 * s * b) := by
      apply (le_div_iff₀ hp).mpr
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg s) (sq_nonneg a))
        (mul_nonneg (by positivity : 0 ≤ 2 * s) hb)]
    have he : 1 + -(2 * s * a) = 1 - 2 * s * a := by ring
    rw [he] at hl
    nlinarith

lemma integral_exp_centered_sq (u : ℝ) (hu : u < 1 / 2) :
    (∫ x : ℝ, Real.exp (u * (x ^ 2 - 1)) ∂gaussianReal 0 1) =
      Real.exp (-u - Real.log (1 - 2 * u) / 2) := by
  have hp : 0 < 1 - 2 * u := by linarith
  have he (x : ℝ) : Real.exp (u * (x ^ 2 - 1)) = Real.exp (-u) * Real.exp (u * x ^ 2) := by
    rw [← Real.exp_add]
    congr 1; ring
  simp_rw [he]
  rw [integral_const_mul, integral_exp_mul_sq_gaussian u hu]
  have hr : (Real.sqrt (1 - 2 * u))⁻¹ = Real.exp (-Real.log (1 - 2 * u) / 2) := by
    rw [neg_div, ← Real.log_sqrt hp.le, Real.exp_neg, Real.exp_log (Real.sqrt_pos.mpr hp)]
  rw [hr, ← Real.exp_add]
  congr 1; ring

lemma mgf_weighted_chiSquare {ι : Type*} [Fintype ι] (a : ι → ℝ) (s : ℝ)
    (hs : ∀ i, s * a i < 1 / 2) :
    mgf (fun z : ι → ℝ => ∑ i, a i * (z i ^ 2 - 1)) (gaussianProduct ι) s =
      Real.exp (∑ i, (-s * a i - Real.log (1 - 2 * s * a i) / 2)) := by
  simp only [mgf, Finset.mul_sum, ← mul_assoc, Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun (i : ι) (x : ℝ) => Real.exp (s * a i * (x ^ 2 - 1)))]
  simp_rw [integral_exp_centered_sq _ (hs _), neg_mul, mul_assoc]

lemma mgf_weighted_chiSquare_le {ι : Type*} [Fintype ι] (a : ι → ℝ) {s b : ℝ}
    (hs : 0 ≤ s) (hb : ∀ i, |a i| ≤ b) (hsb : 2 * s * b < 1) :
    mgf (fun z : ι → ℝ => ∑ i, a i * (z i ^ 2 - 1)) (gaussianProduct ι) s ≤
      Real.exp (s ^ 2 * (∑ i, a i ^ 2) / (1 - 2 * s * b)) := by
  have hsa (i : ι) : s * a i < 1 / 2 := by
    have := mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hb i)) (show 0 ≤ 2 * s by positivity)
    nlinarith
  rw [mgf_weighted_chiSquare a s hsa]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ∑ i, s ^ 2 * a i ^ 2 / (1 - 2 * s * b) :=
      Finset.sum_le_sum fun i _ => centered_log_mgf_le (hb i) hs hsb
    _ = _ := by simp only [← Finset.sum_div, ← Finset.mul_sum]

private lemma chernoff_choice {v b t : ℝ} (hv : 0 < v) (hb : 0 ≤ b) (ht : 0 < t) :
    let s := Real.sqrt t / (Real.sqrt v + 2 * b * Real.sqrt t)
    0 ≤ s ∧ 2 * s * b < 1 ∧
      -s * (2 * (Real.sqrt v * Real.sqrt t + b * t)) + s ^ 2 * v / (1 - 2 * s * b) = -t := by
  have hu : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hr : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hd : 0 < Real.sqrt v + 2 * b * Real.sqrt t := by positivity
  dsimp
  refine ⟨by positivity, ?_, ?_⟩
  · have he : 2 * (Real.sqrt t / (Real.sqrt v + 2 * b * Real.sqrt t)) * b =
        (2 * b * Real.sqrt t) / (Real.sqrt v + 2 * b * Real.sqrt t) := by ring
    rw [he, div_lt_one hd]
    linarith
  · have he : 1 - 2 * (Real.sqrt t / (Real.sqrt v + 2 * b * Real.sqrt t)) * b =
        Real.sqrt v / (Real.sqrt v + 2 * b * Real.sqrt t) := by field_simp; ring
    rw [he]
    have hv' := Real.sq_sqrt hv.le
    have ht' := Real.sq_sqrt ht.le
    rw [← hv', ← ht']
    simp only [Real.sqrt_sq (Real.sqrt_nonneg _)]
    field_simp
    ring

lemma weighted_chiSquare_upper {ι : Type*} [Fintype ι] (a : ι → ℝ) {b t : ℝ}
    (hb : 0 ≤ b) (hab : ∀ i, |a i| ≤ b) (ht : 0 < t) :
    (gaussianProduct ι).real {z | 2 * (Real.sqrt (∑ i, a i ^ 2) * Real.sqrt t + b * t) <
      ∑ i, a i * (z i ^ 2 - 1)} ≤ Real.exp (-t) := by
  have hv : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rcases eq_or_lt_of_le hv with hv | hv
  · have ha (i : ι) : a i = 0 := by
      have hi := Finset.single_le_sum (f := fun j => a j ^ 2)
        (fun j _ => sq_nonneg (a j)) (Finset.mem_univ i)
      nlinarith
    have he : {z : ι → ℝ | 2 * (Real.sqrt (∑ i, a i ^ 2) * Real.sqrt t + b * t) <
        ∑ i, a i * (z i ^ 2 - 1)} = ∅ := by
      ext z
      simp only [ha, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, Real.sqrt_zero,
        zero_mul, zero_add, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      positivity
    rw [he, measureReal_empty]
    positivity
  · let s := Real.sqrt t / (Real.sqrt (∑ i, a i ^ 2) + 2 * b * Real.sqrt t)
    obtain ⟨hs, hsb, he⟩ := chernoff_choice hv hb ht
    have hsa (i : ι) : s * a i < 1 / 2 := by
      have := mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hab i)) (show 0 ≤ 2 * s by positivity)
      change 2 * s * b < 1 at hsb
      nlinarith
    have hi : Integrable (fun z : ι → ℝ => Real.exp (s * ∑ i, a i * (z i ^ 2 - 1)))
        (gaussianProduct ι) := mgf_pos_iff.mp (by rw [mgf_weighted_chiSquare a s hsa]; positivity)
    have hm := measure_ge_le_exp_mul_mgf (μ := gaussianProduct ι)
      (X := fun z : ι → ℝ => ∑ i, a i * (z i ^ 2 - 1))
      (2 * (Real.sqrt (∑ i, a i ^ 2) * Real.sqrt t + b * t)) hs hi
    refine (measureReal_mono (μ := gaussianProduct ι)
      (s₁ := {z | 2 * (Real.sqrt (∑ i, a i ^ 2) * Real.sqrt t + b * t) <
        ∑ i, a i * (z i ^ 2 - 1)})
      (s₂ := {z | 2 * (Real.sqrt (∑ i, a i ^ 2) * Real.sqrt t + b * t) ≤
        ∑ i, a i * (z i ^ 2 - 1)}) (by
          intro z hz
          exact (show 2 * (Real.sqrt (∑ i, a i ^ 2) * Real.sqrt t + b * t) <
            ∑ i, a i * (z i ^ 2 - 1) from hz).le)).trans (hm.trans ?_)
    calc
      _ ≤ Real.exp (-s * (2 * (Real.sqrt (∑ i, a i ^ 2) * Real.sqrt t + b * t))) *
          Real.exp (s ^ 2 * (∑ i, a i ^ 2) / (1 - 2 * s * b)) :=
        mul_le_mul_of_nonneg_left (mgf_weighted_chiSquare_le a hs hab hsb) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, he]

lemma weighted_chiSquare_tail {ι : Type*} [Fintype ι] (a : ι → ℝ) {b t : ℝ}
    (hb : 0 ≤ b) (hab : ∀ i, |a i| ≤ b) (ht : 0 < t) :
    (gaussianProduct ι).real {z | |∑ i, a i * (z i ^ 2 - 1)| >
      2 * (Real.sqrt (∑ i, a i ^ 2) * Real.sqrt t + b * t)} ≤ 2 * Real.exp (-t) := by
  have hplus := weighted_chiSquare_upper a hb hab ht
  have hminus := weighted_chiSquare_upper (fun i => -a i) hb (fun i => by simpa using hab i) ht
  simp only [neg_sq, neg_mul, Finset.sum_neg_distrib] at hminus
  have hset : {z : ι → ℝ | |∑ i, a i * (z i ^ 2 - 1)| >
      2 * (Real.sqrt (∑ i, a i ^ 2) * Real.sqrt t + b * t)} ⊆
      {z | 2 * (Real.sqrt (∑ i, a i ^ 2) * Real.sqrt t + b * t) < ∑ i, a i * (z i ^ 2 - 1)} ∪
      {z | 2 * (Real.sqrt (∑ i, a i ^ 2) * Real.sqrt t + b * t) < -∑ i, a i * (z i ^ 2 - 1)} := by
    intro z hz
    simp only [Set.mem_setOf_eq, Set.mem_union] at hz ⊢
    exact lt_abs.mp hz
  exact (measureReal_mono hset).trans ((measureReal_union_le _ _).trans (by linarith))

end DPCut
