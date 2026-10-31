import DPCut.Privacy
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.Tactic

/-! The one-step exponential-moment estimate in the proof of Lemma 16. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DPCut
attribute [local instance] Classical.propDecidable

lemma exp_neg_le_one_sub_half {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (-x) ≤ 1 - x / 2 := by
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
  have h := Real.add_one_le_exp x
  have hmul := mul_le_mul_of_nonneg_left h (show 0 ≤ 1 - x / 2 by linarith)
  nlinarith [mul_nonneg hx (sub_nonneg.mpr hx1)]

lemma exp_seven_twentieths_le : Real.exp (7 / 20 : ℝ) ≤ 3 / 2 := by
  have h := Real.exp_bound' (x := (7 / 20 : ℝ)) (by norm_num) (by norm_num)
    (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

lemma success_moment_coefficient {a ell : ℝ} (ha : 0 ≤ a) (he : 0 ≤ ell)
    (he1 : ell ≤ 1 / 10) (hae : a * ell ≤ 1 / 4) :
    a * Real.exp (a * ell) * (Real.exp ell - 1) ≤ 3 * a * ell / 2 := by
  have hsmall : Real.exp (a * ell + ell) ≤ 3 / 2 :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_seven_twentieths_le
  have hsub : Real.exp ell - 1 ≤ ell * Real.exp ell := by
    have h := Real.add_one_le_exp (-ell)
    have hm := mul_le_mul_of_nonneg_right h (Real.exp_nonneg ell)
    rw [← Real.exp_add] at hm
    simp only [neg_add_cancel, Real.exp_zero] at hm
    nlinarith
  calc
    a * Real.exp (a * ell) * (Real.exp ell - 1)
        ≤ a * Real.exp (a * ell) * (ell * Real.exp ell) := by gcongr
    _ = (a * ell) * Real.exp (a * ell + ell) := by rw [Real.exp_add]; ring
    _ ≤ (a * ell) * (3 / 2) := mul_le_mul_of_nonneg_left hsmall (mul_nonneg ha he)
    _ = 3 * a * ell / 2 := by ring

/-- The successful-output contribution admits an affine upper bound in the inverse density. -/
lemma success_moment_affine {a ell z : ℝ} (ha : 0 ≤ a) (he : 0 ≤ ell)
    (he1 : ell ≤ 1 / 10) (hae : a * ell ≤ 1 / 4)
    (hz0 : -ell ≤ z) (hz1 : z ≤ ell) :
    Real.exp (a * (z - 4 * ell)) ≤
      1 + (a * Real.exp (a * ell)) * (1 - Real.exp (-z)) := by
  have hb := success_moment_coefficient ha he he1 hae
  have hz := Real.exp_le_exp.mpr (show -z ≤ ell by linarith)
  calc
    Real.exp (a * (z - 4 * ell)) ≤ Real.exp (-(3 * a * ell)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ ≤ 1 - 3 * a * ell / 2 := exp_neg_le_one_sub_half (by positivity) (by nlinarith)
    _ ≤ 1 - a * Real.exp (a * ell) * (Real.exp ell - 1) := by linarith
    _ ≤ 1 + (a * Real.exp (a * ell)) * (1 - Real.exp (-z)) := by
      nlinarith [mul_le_mul_of_nonneg_left hz
        (mul_nonneg ha (Real.exp_nonneg (a * ell)))]

/-- For a positive failure loss, Bernoulli's inequality gives the same affine bound. -/
lemma failure_moment_affine {a ell z : ℝ} (ha : 1 ≤ a)
    (hz0 : 0 ≤ z) (hz1 : z ≤ ell) :
    Real.exp (a * z) ≤
      1 + (a * Real.exp (a * ell)) * (1 - Real.exp (-z)) := by
  have hb := one_add_mul_self_le_rpow_one_add
    (s := Real.exp (-z) - 1) (by linarith [Real.exp_pos (-z)]) ha
  rw [add_sub_cancel, ← Real.exp_mul] at hb
  have hm := mul_le_mul_of_nonneg_left hb (Real.exp_nonneg (a * z))
  have heq : Real.exp (a * z) * Real.exp (-z * a) = 1 := by
    rw [← Real.exp_add, show a * z + -z * a = 0 by ring, Real.exp_zero]
  have he : Real.exp (a * z) ≤ Real.exp (a * ell) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hz1 (by linarith))
  have hn : 0 ≤ 1 - Real.exp (-z) := by
    have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hz0)
    linarith
  rw [heq] at hm
  have hm' := mul_le_mul_of_nonneg_right he (mul_nonneg (by linarith : 0 ≤ a) hn)
  nlinarith

/-- A single successful output is charged `ell`; the failure symbol is charged zero. -/
def stepCharge {Y : Type*} (bottom : Y) (ell : ℝ) (y : Y) : ℝ :=
  if y = bottom then 0 else ell

lemma measurable_stepCharge {Y : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (bottom : Y) (ell : ℝ) : Measurable (stepCharge bottom ell) :=
  Measurable.ite (measurableSet_singleton bottom) measurable_const measurable_const

/-- A form of the manuscript's one-step moment estimate that does not require a positive
mass at the failure atom. `z` is the log density and its inverse density integrates to one. -/
theorem success_charged_one_step {Y : Type*} [MeasurableSpace Y]
    [MeasurableSingletonClass Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    (bottom : Y) {z : Y → ℝ} (hz : Measurable z) {a ell : ℝ}
    (ha : 1 ≤ a) (he : 0 ≤ ell) (he1 : ell ≤ 1 / 10) (hae : a * ell ≤ 1 / 4)
    (hb : ∀ᵐ y ∂μ, -ell ≤ z y ∧ z y ≤ ell)
    (hinv : ∫ y, Real.exp (-z y) ∂μ = 1) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (a * (z y - 4 * stepCharge bottom ell y))) ∂μ ≤ 1 := by
  have ha0 : 0 ≤ a := by linarith
  have hm : Measurable (fun y => Real.exp (a * (z y - 4 * stepCharge bottom ell y))) :=
    (measurable_const.mul (hz.sub (measurable_const.mul (measurable_stepCharge bottom ell)))).exp
  have hf : Integrable (fun y => Real.exp (a * (z y - 4 * stepCharge bottom ell y))) μ := by
    apply (integrable_const (Real.exp (a * ell))).mono' hm.aestronglyMeasurable
    filter_upwards [hb] with y hy
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hc : 0 ≤ stepCharge bottom ell y := by unfold stepCharge; split <;> positivity
    nlinarith
  rw [← ofReal_integral_eq_lintegral_ofReal hf
    (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le), ENNReal.ofReal_le_one]
  by_cases hbottom : z bottom ≤ 0
  · calc
      _ ≤ ∫ _ : Y, (1 : ℝ) ∂μ := integral_mono_ae hf (integrable_const _) (by
        filter_upwards [hb] with y hy
        apply Real.exp_le_one_iff.mpr
        by_cases hyb : y = bottom
        · simp only [stepCharge, hyb, ite_true]
          nlinarith
        · simp only [stepCharge, hyb, if_false]
          nlinarith)
      _ = 1 := by simp
  · have hrec : Integrable (fun y => Real.exp (-z y)) μ := by
      apply (integrable_const (Real.exp ell)).mono' hz.neg.exp.aestronglyMeasurable
      filter_upwards [hb] with y hy
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (by linarith)
    have hg : Integrable (fun y => 1 + (a * Real.exp (a * ell)) *
        (1 - Real.exp (-z y))) μ :=
      (integrable_const _).add (((integrable_const _).sub hrec).const_mul _)
    calc
      _ ≤ ∫ y, (1 + (a * Real.exp (a * ell)) * (1 - Real.exp (-z y))) ∂μ :=
        integral_mono_ae hf hg (by
          filter_upwards [hb] with y hy
          by_cases hyb : y = bottom
          · simp only [stepCharge, hyb, ite_true, mul_zero, sub_zero]
            exact failure_moment_affine ha (by linarith) (hyb ▸ hy.2)
          · simp only [stepCharge, hyb, if_false]
            exact success_moment_affine ha0 he he1 hae hy.1 hy.2)
      _ = 1 := by
        rw [integral_add (integrable_const (1 : ℝ))
          (show Integrable (fun y => (a * Real.exp (a * ell)) *
            (1 - Real.exp (-z y))) μ from
            ((integrable_const (1 : ℝ)).sub hrec).const_mul _),
          integral_const_mul, integral_sub (integrable_const (1 : ℝ)) hrec, hinv]
        simp

end DPCut
