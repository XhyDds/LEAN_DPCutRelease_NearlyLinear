import DPCut.GaussianQuadratic

/-! A one-sided probability estimate from centered second and fourth moments. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace DPCut

private lemma sq_le_abs_fourth (x : ℝ) : x ^ 2 ≤ 8 * |x| + x ^ 4 / 64 := by
  by_cases h : |x| ≤ 8
  · nlinarith [mul_nonneg (abs_nonneg x) (sub_nonneg.2 h), sq_abs x, sq_nonneg (x ^ 2)]
  · have hx : 64 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
    nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.2 hx), abs_nonneg x]

private lemma oneSided_unitVariance {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {W : Ω → ℝ} (hm : Measurable W) (hW : AllLp μ W)
    (hmean : (∫ x, W x ∂μ) = 0) (h2 : (∫ x, W x ^ 2 ∂μ) = 1)
    (h4 : (∫ x, W x ^ 4 ∂μ) ≤ 15) :
    (1 / 1024 : ℝ) ≤ prob μ {x | 0 ≤ W x} := by
  classical
  let s : Set Ω := {x | 0 ≤ W x}
  have hs : MeasurableSet s := measurableSet_le measurable_const hm
  let g : Ω → ℝ := s.indicator (fun _ => 1)
  have hg : AllLp μ g := fun p hp => (AllLp.const (μ := μ) 1 p hp).indicator hs
  have hg2 : (fun x => g x ^ 2) = g := by ext x; by_cases h : x ∈ s <;> simp [g, h]
  have hgp : (∫ x, g x ∂μ) = prob μ s := by simp [g, integral_indicator hs, prob, measureReal_def]
  have habs : (∫ x, |W x| ∂μ) = 2 * (∫ x, W x * g x ∂μ) := by
    have he : (fun x => |W x|) = (fun x => 2 * (W x * g x) - W x) := by
      ext x
      by_cases h : 0 ≤ W x
      · simp [g, s, h, abs_of_nonneg h]; ring
      · simp [g, s, h, abs_of_neg (lt_of_not_ge h)]
    rw [he, integral_sub ((hW.mul hg).const_mul 2).integrable hW.integrable,
      integral_const_mul, hmean, sub_zero]
  have hmoment := integral_mono (hW.pow 2).integrable
    ((hW.abs.const_mul 8).add ((hW.pow 4).div_const 64)).integrable
    (fun x => sq_le_abs_fourth (W x))
  rw [integral_add (hW.abs.const_mul 8).integrable ((hW.pow 4).div_const 64).integrable,
    integral_const_mul, integral_div, h2] at hmoment
  have hp : (1 / 32 : ℝ) ≤ ∫ x, W x * g x ∂μ := by linarith
  have he : (fun x => (W x - 32 * g x) ^ 2) =
      (fun x => W x ^ 2 - 64 * (W x * g x) + 1024 * g x ^ 2) := by
    ext x; ring
  have hn : 0 ≤ ∫ x, (W x - 32 * g x) ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have hi : Integrable (fun x => W x ^ 2 - 64 * (W x * g x)) μ :=
    ((hW.pow 2).sub ((hW.mul hg).const_mul 64)).integrable
  rw [he, integral_add hi ((hg.pow 2).const_mul 1024).integrable,
    integral_sub (hW.pow 2).integrable ((hW.mul hg).const_mul 64).integrable,
    integral_const_mul, integral_const_mul, hg2, h2, hgp] at hn
  change (1 / 1024 : ℝ) ≤ prob μ s
  linarith

/-- Uniform mass on the nonnegative side; no nondegeneracy assumption is required. -/
theorem oneSided_of_fourth_moment {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {W : Ω → ℝ} (hm : Measurable W) (hW : AllLp μ W)
    (hmean : (∫ x, W x ∂μ) = 0)
    (h4 : (∫ x, W x ^ 4 ∂μ) ≤ 15 * (∫ x, W x ^ 2 ∂μ) ^ 2) :
    (1 / 1024 : ℝ) ≤ prob μ {x | 0 ≤ W x} := by
  let v := ∫ x, W x ^ 2 ∂μ
  have hv : 0 ≤ v := integral_nonneg (fun x => sq_nonneg _)
  rcases hv.eq_or_lt with hv | hv
  · have hz : ∀ᵐ x ∂μ, W x ^ 2 = 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) (hW.pow 2).integrable).1 hv.symm
    have he : {x | 0 ≤ W x} =ᵐ[μ] Set.univ := by
      filter_upwards [hz] with x hx
      have hx0 : W x = 0 := pow_eq_zero hx
      change (0 ≤ W x) = True
      simp [hx0]
    unfold prob
    rw [measure_congr he]
    norm_num
  · let σ := Real.sqrt v
    have hσ : 0 < σ := Real.sqrt_pos.2 hv
    have hσ2 : σ ^ 2 = v := Real.sq_sqrt hv.le
    have hσ4 : σ ^ 4 = v ^ 2 := by nlinarith [sq_nonneg (σ ^ 2 - v)]
    have hm0 : (∫ x, W x / σ ∂μ) = 0 := by rw [integral_div, hmean, zero_div]
    have hm2 : (∫ x, (W x / σ) ^ 2 ∂μ) = 1 := by
      simp only [div_pow, integral_div, hσ2]
      exact div_self hv.ne'
    have hm4 : (∫ x, (W x / σ) ^ 4 ∂μ) ≤ 15 := by
      simp only [div_pow, integral_div, hσ4]
      exact (div_le_iff₀ (sq_pos_of_pos hv)).2 h4
    have h := oneSided_unitVariance (hm.div_const σ) (hW.div_const σ) hm0 hm2 hm4
    simpa only [le_div_iff₀ hσ, zero_mul] using h

theorem gaussian_quadratic_above_mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (1 / 1024 : ℝ) ≤ prob (gaussianProduct ι)
      {z | (∫ y, quadratic A y ∂gaussianProduct ι) ≤ quadratic A z} := by
  obtain ⟨hmean, h4⟩ := gaussian_quadratic_moments hA
  have hc := (allLp_quadratic A).sub (AllLp.const A.trace)
  have hm0 : (∫ z, quadratic A z - A.trace ∂gaussianProduct ι) = 0 := by
    rw [integral_sub (allLp_quadratic A).integrable (integrable_const _), hmean]
    simp
  have h := oneSided_of_fourth_moment ((measurable_quadratic A).sub_const _) hc hm0 h4
  simpa only [sub_nonneg, hmean] using h

end DPCut
