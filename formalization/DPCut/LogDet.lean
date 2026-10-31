import DPCut.Definitions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! Directional differentiation of the log determinant, used only for the SDP optimizer. -/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise

namespace DPCut

private def detContinuous (n : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin n → ℝ) ℝ :=
  ⟨Matrix.detRowAlternating.toMultilinearMap, continuous_id.matrix_det⟩

lemma hasDerivAt_det_one_add {n : ℕ} (H : Mat n) :
    HasDerivAt (fun t : ℝ => (1 + t • H).det) H.trace 0 := by
  classical
  have hd := (detContinuous n).hasFDerivAt (1 : Mat n)
  have hp : HasDerivAt (fun t : ℝ => (1 : Mat n) + t • H) H 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const H).const_add (1 : Mat n)
  have h := hd.comp_hasDerivAt_of_eq (0 : ℝ) hp (by simp)
  convert h using 1
  simp only [ContinuousMultilinearMap.linearDeriv_apply]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro i _
  change H i i = (Matrix.updateRow 1 i (H i)).det
  rw [← Matrix.cramer_transpose_apply, Matrix.transpose_one, Matrix.cramer_one]
  rfl

lemma hasDerivAt_logdet {n : ℕ} {X : Mat n} (hX : X.PosDef) (H : Mat n) :
    HasDerivAt (fun t : ℝ => Real.log (X + t • H).det)
      (X⁻¹ * H).trace 0 := by
  have hunit : IsUnit X.det := isUnit_iff_ne_zero.mpr hX.det_pos.ne'
  have hfactor (t : ℝ) : X + t • H = X * (1 + t • (X⁻¹ * H)) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv X hunit, Matrix.one_mul]
  have hd := (hasDerivAt_det_one_add (X⁻¹ * H)).const_mul X.det
  have heq : (fun t : ℝ => X.det * (1 + t • (X⁻¹ * H)).det) =
      (fun t => (X + t • H).det) := by
    funext t
    rw [hfactor, Matrix.det_mul]
  rw [heq] at hd
  have hl := hd.log (by simpa using hX.det_pos.ne')
  simpa [mul_div_cancel_left₀ _ hX.det_pos.ne'] using hl

end DPCut
