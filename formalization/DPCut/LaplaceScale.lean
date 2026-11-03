import DPCut.LaplaceDensity
import DPCut.DensityTools

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace DPCut

def scaleReal (b : ℝ) (hb : 0 < b) : ℝ ≃ᵐ ℝ where
  toFun x := b*x
  invFun x := x/b
  left_inv x := by field_simp
  right_inv x := by field_simp
  measurable_toFun := measurable_const_mul _
  measurable_invFun := measurable_id.div_const _

theorem laplace_scale {b : ℝ} (hb : 0 < b) :
    (laplace 1).map (fun x => b*x) = laplace b := by
  let e := scaleReal b hb
  have hv : (volume : Measure ℝ).map e = ENNReal.ofReal |b⁻¹| • volume :=
    Real.map_volume_mul_left hb.ne'
  change (volume.withDensity (fun x => ENNReal.ofReal (laplaceDensity 1 x))).map e = _
  rw [map_withDensity_equiv _ e (by fun_prop), hv, withDensity_smul_measure,
    ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  apply withDensity_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change ENNReal.ofReal |b⁻¹| * ENNReal.ofReal (laplaceDensity 1 (x/b)) = ENNReal.ofReal (laplaceDensity b x)
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  simp only [laplaceDensity, abs_inv, abs_div, abs_of_pos hb, div_one, mul_one]
  norm_num
  ring

end DPCut
