import DPCut.EllipsoidAccuracy

/-! Polynomial bounds on the actual deterministic optimizer's oracle calls. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace DPCut.EllipsoidOptimization

open EllipsoidMethod

variable {m : ℕ} {Θ : Type} [MeasurableSpace Θ]

def scale (P : LSW.Problem (Fin m) Θ) (epsilon : ℝ) : ℝ :=
  1 + m + Real.log (P.outerRadius / P.innerRadius) + Real.log (P.rangeBound / epsilon)

theorem scale_bounds (P : LSW.Problem (Fin m) Θ) {epsilon : ℝ}
    (he : 0 < epsilon) (hehalf : epsilon ≤ 1 / 2) :
    1 ≤ scale P epsilon ∧ (m : ℝ) ≤ scale P epsilon ∧
      0 ≤ Real.log (P.outerRadius / P.innerRadius) ∧
      0 ≤ Real.log (P.rangeBound / epsilon) := by
  have hg := Real.log_nonneg ((one_le_div P.inner_pos).mpr P.radii_order)
  have hB : epsilon ≤ P.rangeBound := by linarith [P.range_one_le]
  have hp := Real.log_nonneg ((one_le_div he).mpr hB)
  unfold scale
  exact ⟨by have h := Nat.cast_nonneg (α := ℝ) m; linarith, by linarith, hg, hp⟩

def roundCoefficient : ℝ := (Real.log 2)⁻¹ + 3

theorem roundCoefficient_pos : 0 < roundCoefficient := by
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold roundCoefficient
  positivity

theorem rounds_le_scale (P : LSW.Problem (Fin m) Θ) {epsilon : ℝ}
    (he : 0 < epsilon) (hehalf : epsilon ≤ 1 / 2) :
    (rounds P epsilon : ℝ) ≤ roundCoefficient * scale P epsilon := by
  have hb := scale_bounds P he hehalf
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB : 0 < P.rangeBound := lt_of_lt_of_le zero_lt_one P.range_one_le
  have hlog : Real.log (2 * P.rangeBound / epsilon) =
      Real.log 2 + Real.log (P.rangeBound / epsilon) := by
    rw [mul_div_assoc, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (div_ne_zero hB.ne' he.ne')]
  have hx : 0 ≤ Real.log (2 * P.rangeBound / epsilon) / Real.log 2 := by
    rw [hlog]
    exact div_nonneg (add_nonneg hlog2.le hb.2.2.2) hlog2.le
  have hceil := (Nat.ceil_lt_add_one hx).le
  have hround : (rounds P epsilon : ℝ) ≤ Real.log (2 * P.rangeBound / epsilon) / Real.log 2 + 2 := by
    unfold rounds
    push_cast
    linarith
  have hp : Real.log (P.rangeBound / epsilon) ≤ scale P epsilon := by
    unfold scale
    linarith [hb.2.2.1, Nat.cast_nonneg (α := ℝ) m]
  have hratio : Real.log (2 * P.rangeBound / epsilon) / Real.log 2 + 2 =
      (Real.log 2)⁻¹ * Real.log (P.rangeBound / epsilon) + 3 := by
    rw [hlog]
    field_simp
    ring
  rw [hratio] at hround
  apply hround.trans
  have hmul := mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hlog2.le)
  unfold roundCoefficient
  nlinarith [hb.1]

theorem radius_log (P : LSW.Problem (Fin m) Θ) {epsilon : ℝ} (he : 0 < epsilon) :
    Real.log (P.outerRadius / radius P (epsilon / 4)) =
      Real.log (P.outerRadius / P.innerRadius) + Real.log 8 + Real.log (P.rangeBound / epsilon) := by
  have hR := P.inner_pos.trans_le P.radii_order
  have hB : 0 < P.rangeBound := lt_of_lt_of_le zero_lt_one P.range_one_le
  have hratio : P.outerRadius / radius P (epsilon / 4) =
      (P.outerRadius / P.innerRadius) * (8 * (P.rangeBound / epsilon)) := by
    unfold radius
    field_simp
    ring
  rw [hratio, Real.log_mul (div_ne_zero hR.ne' P.inner_pos.ne')
    (mul_ne_zero (by norm_num) (div_ne_zero hB.ne' he.ne')),
    Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (div_ne_zero hB.ne' he.ne')]
  ring

theorem feasibilityBudget_le_scale (P : LSW.Problem (Fin m) Θ) {epsilon : ℝ}
    (he : 0 < epsilon) (hehalf : epsilon ≤ 1 / 2) :
    (feasibilityBudget P epsilon : ℝ) ≤ 61 * scale P epsilon ^ 3 := by
  have hb := scale_bounds P he hehalf
  have hB : 0 < P.rangeBound := lt_of_lt_of_le zero_lt_one P.range_one_le
  have hcoef : epsilon / 4 / (2 * P.rangeBound) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith [P.range_one_le]
  have hrad : radius P (epsilon / 4) ≤ P.outerRadius :=
    (mul_le_of_le_one_right P.inner_pos.le hcoef).trans P.radii_order
  have hn := ballIterationBudget_le (m := m) (radius_pos P (by positivity : 0 < epsilon / 4)) hrad
  change (feasibilityBudget P epsilon : ℝ) ≤ _ at hn
  rw [radius_log P he] at hn
  let S := scale P epsilon
  have hS : 1 ≤ S := hb.1
  have hm : (m : ℝ) ≤ S := hb.2.1
  have hgeom : Real.log (P.outerRadius / P.innerRadius) ≤ S := by
    unfold S scale
    linarith [hb.2.2.2, Nat.cast_nonneg (α := ℝ) m]
  have hprec : Real.log (P.rangeBound / epsilon) ≤ S := by
    unfold S scale
    linarith [hb.2.2.1, Nat.cast_nonneg (α := ℝ) m]
  have h8 : Real.log 8 ≤ 8 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
    linarith
  have hsum : Real.log (P.outerRadius / P.innerRadius) + Real.log 8 +
      Real.log (P.rangeBound / epsilon) ≤ 10 * S := by linarith
  have hdim : (m : ℝ) + 2 ≤ 3 * S := by linarith
  have hnonnegative : 0 ≤ Real.log (P.outerRadius / P.innerRadius) + Real.log 8 +
      Real.log (P.rangeBound / epsilon) :=
    add_nonneg (add_nonneg hb.2.2.1 (Real.log_nonneg (by norm_num))) hb.2.2.2
  have hpower : 1 ≤ S ^ 3 := one_le_pow₀ hS
  calc
    _ ≤ 2 * ((m : ℝ) + 2) * m *
        (Real.log (P.outerRadius / P.innerRadius) + Real.log 8 + Real.log (P.rangeBound / epsilon)) + 1 := hn
    _ ≤ 2 * (3 * S) * S * (10 * S) + 1 := by gcongr
    _ ≤ 61 * S ^ 3 := by ring_nf; linarith

theorem solveCalls_polynomial (P : LSW.Problem (Fin m) Θ) (O : LSW.Oracle P) (hm : 1 ≤ m)
    (theta : Θ) {epsilon : ℝ} (he : 0 < epsilon) (hehalf : epsilon ≤ 1 / 2) :
    (solveCalls P O hm theta epsilon : ℝ) ≤
      (1 + 61 * roundCoefficient) * scale P epsilon ^ 4 := by
  have hc : (solveCalls P O hm theta epsilon : ℝ) ≤
      1 + (rounds P epsilon : ℝ) * (feasibilityBudget P epsilon : ℝ) := by
    exact_mod_cast solveCalls_le P O hm theta epsilon
  have hr := rounds_le_scale P he hehalf
  have hb := feasibilityBudget_le_scale P he hehalf
  have hs := (scale_bounds P he hehalf).1
  have hprod := mul_le_mul hr hb (Nat.cast_nonneg _)
    (mul_nonneg roundCoefficient_pos.le (le_trans zero_le_one hs))
  have hone : 1 ≤ scale P epsilon ^ 4 := one_le_pow₀ hs
  nlinarith

end DPCut.EllipsoidOptimization
