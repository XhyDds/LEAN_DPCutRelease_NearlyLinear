import DPCut.EllipsoidDeterminant
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Volume certificates for the explicit ellipsoid method. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Metric
namespace DPCut.EllipsoidMethod

variable {m : ℕ}

def Ellipsoid.size (e : Ellipsoid (EuclideanSpace ℝ (Fin m))) : ℝ :=
  |LinearMap.det (e.axes : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))|

lemma Ellipsoid.size_pos (e : Ellipsoid (EuclideanSpace ℝ (Fin m))) : 0 < e.size :=
  abs_pos.mpr (LinearEquiv.isUnit_det' e.axes).ne_zero

theorem Ellipsoid.volume_region (e : Ellipsoid (EuclideanSpace ℝ (Fin m))) :
    volume e.region = ENNReal.ofReal e.size *
      volume (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) := by
  have heq : e.region = (fun x => x + -e.center) ⁻¹'
      (e.axes.symm ⁻¹' closedBall 0 1) := by
    ext x
    simp [region, mem_closedBall, dist_eq_norm, sub_eq_add_neg]
  rw [heq, measure_preimage_add_right, Measure.addHaar_preimage_linearEquiv]
  rfl

/-- Any contained ball provides a lower bound for the ellipsoid determinant. -/
theorem Ellipsoid.size_ge_of_ball_subset
    (e : Ellipsoid (EuclideanSpace ℝ (Fin m))) (p : EuclideanSpace ℝ (Fin m))
    {r : ℝ} (hr : 0 < r) (hsub : closedBall p r ⊆ e.region) :
    r ^ m ≤ e.size := by
  have h := measure_mono (μ := volume) hsub
  rw [e.volume_region, Measure.addHaar_closedBall' volume p hr.le,
    finrank_euclideanSpace, Fintype.card_fin] at h
  have hp : volume (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) ≠ 0 :=
    ne_of_gt (measure_closedBall_pos volume _ (by norm_num))
  have hf : volume (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) ≠ ⊤ :=
    measure_closedBall_lt_top.ne
  exact (ENNReal.ofReal_le_ofReal_iff e.size_pos.le).mp
    ((ENNReal.mul_le_mul_right hp hf).mp h)

theorem Ellipsoid.log_size_cut_le
    (e : Ellipsoid (EuclideanSpace ℝ (Fin m))) {d : ℝ} (hd : 2 ≤ d)
    (hmd : (m : ℝ) ≤ d) (u : EuclideanSpace ℝ (Fin m)) (hu : ‖u‖ = 1) :
    Real.log (e.cut d hd u hu).size ≤ Real.log e.size - 1 / (2 * (d + 1)) := by
  have hp : 0 < LinearMap.det (axialMap u (axialRadius d) (transverseRadius d)) := by
    rw [det_axialMap hu _ _ (transverseRadius_pos hd).ne']
    exact mul_pos (pow_pos (transverseRadius_pos hd) _) (div_pos (axialRadius_pos hd)
      (transverseRadius_pos hd))
  have heq : (e.cut d hd u hu).size = e.size *
      LinearMap.det (axialMap u (axialRadius d) (transverseRadius d)) := by
    change |LinearMap.det ((e.axes : _ →ₗ[ℝ] _).comp
      (axialMap u (axialRadius d) (transverseRadius d)))| = _
    rw [LinearMap.det_comp, abs_mul, abs_of_pos hp]
    rfl
  rw [heq, Real.log_mul e.size_pos.ne' hp.ne']
  linarith [log_det_axial_update_le hd hmd hu]

end DPCut.EllipsoidMethod
