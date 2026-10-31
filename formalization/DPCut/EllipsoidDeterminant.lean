import DPCut.EllipsoidGeometry
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Determinant decrease of the explicit central-cut ellipsoid update. -/
set_option autoImplicit false
noncomputable section
open Matrix
open scoped RealInnerProductSpace
namespace DPCut.EllipsoidMethod

lemma det_one_add_outer {d : ℕ} (u v : Fin d → ℝ) :
    (1 + vecMulVec u v).det = 1 + v ⬝ᵥ u := by
  rw [Matrix.vecMulVec_eq Unit]
  exact Matrix.det_one_add_replicateCol_mul_replicateRow u v

lemma axialMap_matrix {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (a b : ℝ) :
    axialMap u a b = Matrix.toEuclideanLin
      (b • (1 : Matrix (Fin d) (Fin d) ℝ) + (a - b) • vecMulVec (WithLp.ofLp u) (WithLp.ofLp u)) := by
  ext x i
  simp [axialMap_apply, Matrix.toEuclideanLin_apply,
    Matrix.vecMulVec_mulVec, EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
    dotProduct_comm, mul_assoc]

theorem det_axialMap {d : ℕ} {u : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ = 1)
    (a b : ℝ) (hb : b ≠ 0) :
    LinearMap.det (axialMap u a b) = b ^ d * (a / b) := by
  have hu' : WithLp.ofLp u ⬝ᵥ WithLp.ofLp u = 1 := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct, hu] using real_inner_self_eq_norm_sq u
  rw [axialMap_matrix, Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]
  have hmat : b • (1 : Matrix (Fin d) (Fin d) ℝ) +
      (a - b) • vecMulVec (WithLp.ofLp u) (WithLp.ofLp u) =
      b • (1 + vecMulVec ((a / b - 1) • WithLp.ofLp u) (WithLp.ofLp u)) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
  rw [hmat, Matrix.det_smul, det_one_add_outer]
  simp only [Fintype.card_fin, dotProduct_smul, smul_eq_mul, hu']
  ring

lemma transverseRadius_sq {d : ℝ} (hd : 2 ≤ d) :
    transverseRadius d ^ 2 = d ^ 2 / (d ^ 2 - 1) := by
  rw [transverseRadius, div_pow, Real.sq_sqrt (by nlinarith : 0 ≤ d ^ 2 - 1)]

lemma transverseRadius_one_le {d : ℝ} (hd : 2 ≤ d) : 1 ≤ transverseRadius d := by
  have hp := transverseRadius_pos hd
  have hs := transverseRadius_sq hd
  have hfrac : 1 ≤ d ^ 2 / (d ^ 2 - 1) :=
    (le_div_iff₀ (by nlinarith)).mpr (by nlinarith)
  nlinarith

lemma log_axialRadius_le {d : ℝ} (hd : 2 ≤ d) :
    Real.log (axialRadius d) ≤ -(1 / (d + 1)) := by
  have h := Real.log_le_sub_one_of_pos (axialRadius_pos hd)
  have heq : axialRadius d - 1 = -(1 / (d + 1)) := by
    unfold axialRadius
    field_simp
    ring
  rwa [heq] at h

lemma log_transverseRadius_le {d : ℝ} (hd : 2 ≤ d) :
    Real.log (transverseRadius d) ≤ 1 / (2 * (d ^ 2 - 1)) := by
  have hp := transverseRadius_pos hd
  have h := Real.log_le_sub_one_of_pos (sq_pos_of_pos hp)
  rw [Real.log_pow, transverseRadius_sq hd] at h
  have heq : d ^ 2 / (d ^ 2 - 1) - 1 = 1 / (d ^ 2 - 1) := by
    have hs : d ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp
    ring
  rw [heq] at h
  norm_num at h
  convert (div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 2)) using 1 <;>
    simp [div_eq_mul_inv, _root_.mul_inv_rev, mul_comm]

/-- The update parameter may exceed the dimension. This permits a uniform
choice `dimension + 1`, including dimension one without a special formula. -/
theorem log_det_axial_update_le {m : ℕ} {d : ℝ} (hd : 2 ≤ d)
    (hmd : (m : ℝ) ≤ d) {u : EuclideanSpace ℝ (Fin m)} (hu : ‖u‖ = 1) :
    Real.log (LinearMap.det (axialMap u (axialRadius d) (transverseRadius d))) ≤
      -(1 / (2 * (d + 1))) := by
  have ha := axialRadius_pos hd
  have hb := transverseRadius_pos hd
  rw [det_axialMap hu _ _ hb.ne', Real.log_mul (pow_pos hb _).ne' (div_pos ha hb).ne',
    Real.log_pow, Real.log_div ha.ne' hb.ne']
  have hb0 : 0 ≤ Real.log (transverseRadius d) :=
    Real.log_nonneg (transverseRadius_one_le hd)
  have hdim := mul_le_mul_of_nonneg_right (show (m : ℝ) - 1 ≤ d - 1 by linarith) hb0
  have hlog := mul_le_mul_of_nonneg_left (log_transverseRadius_le hd)
    (show 0 ≤ d - 1 by linarith)
  have heq : -(1 / (d + 1)) + (d - 1) * (1 / (2 * (d ^ 2 - 1))) =
      -(1 / (2 * (d + 1))) := by
    have hs : d ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp
    ring
  have hax := log_axialRadius_le hd
  linarith

end DPCut.EllipsoidMethod
