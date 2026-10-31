import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-! The geometric central-cut update for the deterministic ellipsoid method.
An ellipsoid is an invertible affine image of the Euclidean unit ball. -/
set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace
namespace DPCut.EllipsoidMethod

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Scale the direction `u` by `a` and its orthogonal complement by `b`. -/
def axialMap (u : E) (a b : ℝ) : E →ₗ[ℝ] E where
  toFun x := b • x + ((a - b) * ⟪u, x⟫) • u
  map_add' x y := by simp [inner_add_right, mul_add, add_smul]; module
  map_smul' r x := by simp [real_inner_smul_right]; module

@[simp] lemma axialMap_apply (u : E) (a b : ℝ) (x : E) :
    axialMap u a b x = b • x + ((a - b) * ⟪u, x⟫) • u := rfl

lemma inner_axialMap {u : E} (hu : ‖u‖ = 1) (a b : ℝ) (x : E) :
    ⟪u, axialMap u a b x⟫ = a * ⟪u, x⟫ := by
  simp only [axialMap_apply, inner_add_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hu]
  ring

lemma axialMap_comp {u : E} (hu : ‖u‖ = 1) (a b c d : ℝ) (x : E) :
    axialMap u a b (axialMap u c d x) = axialMap u (a * c) (b * d) x := by
  rw [axialMap_apply, inner_axialMap hu]
  simp only [axialMap_apply]
  module

def axialEquiv (u : E) (hu : ‖u‖ = 1) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : E ≃ₗ[ℝ] E where
  toLinearMap := axialMap u a b
  invFun := axialMap u a⁻¹ b⁻¹
  left_inv x := by
    change axialMap u a⁻¹ b⁻¹ (axialMap u a b x) = x
    rw [axialMap_comp hu]
    simp [ha, hb]
  right_inv x := by
    change axialMap u a b (axialMap u a⁻¹ b⁻¹ x) = x
    rw [axialMap_comp hu]
    simp [ha, hb]

lemma norm_axialMap_sq {u : E} (hu : ‖u‖ = 1) (a b : ℝ) (x : E) :
    ‖axialMap u a b x‖ ^ 2 =
      b ^ 2 * ‖x‖ ^ 2 + (a ^ 2 - b ^ 2) * ⟪u, x⟫ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [axialMap_apply, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  simp only [real_inner_self_eq_norm_sq, real_inner_comm x u, hu]
  ring

/-- The major and minor radii of the ellipsoid enclosing a half unit ball. -/
def axialRadius (d : ℝ) : ℝ := d / (d + 1)
def transverseRadius (d : ℝ) : ℝ := d / Real.sqrt (d ^ 2 - 1)

lemma axialRadius_pos {d : ℝ} (hd : 2 ≤ d) : 0 < axialRadius d := by
  unfold axialRadius
  positivity

lemma transverseRadius_pos {d : ℝ} (hd : 2 ≤ d) : 0 < transverseRadius d := by
  unfold transverseRadius
  exact div_pos (by linarith) (Real.sqrt_pos.2 (by nlinarith))

/-- Pull a point of the retained half ball back into the new unit ball. -/
theorem centralCut_contains {d : ℝ} (hd : 2 ≤ d) {u x : E}
    (hu : ‖u‖ = 1) (hx : ‖x‖ ≤ 1) (hcut : ⟪u, x⟫ ≤ 0) :
    ‖axialMap u (axialRadius d)⁻¹ (transverseRadius d)⁻¹
      (x + (1 / (d + 1)) • u)‖ ≤ 1 := by
  have hd0 : d ≠ 0 := by linarith
  have hd1 : d + 1 ≠ 0 := by linarith
  have hs : 0 ≤ d ^ 2 - 1 := by nlinarith
  have ht : -1 ≤ ⟪u, x⟫ := by
    have hh := abs_real_inner_le_norm u x
    rw [hu, one_mul] at hh
    exact (abs_le.mp (hh.trans hx)).1
  have htprod : ⟪u, x⟫ * (⟪u, x⟫ + 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hcut (by linarith)
  have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  have hnorm : ‖x + (1 / (d + 1)) • u‖ ^ 2 =
      ‖x‖ ^ 2 + 2 / (d + 1) * ⟪u, x⟫ + 1 / (d + 1) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    simp only [real_inner_self_eq_norm_sq, real_inner_comm x u, hu]
    field_simp
    ring
  have hip : ⟪u, x + (1 / (d + 1)) • u⟫ = ⟪u, x⟫ + 1 / (d + 1) := by
    simp [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu]
  have hinv : (transverseRadius d)⁻¹ ^ 2 = (d ^ 2 - 1) / d ^ 2 := by
    simp only [transverseRadius, inv_div, div_pow, Real.sq_sqrt hs]
  have heq : ‖axialMap u (axialRadius d)⁻¹ (transverseRadius d)⁻¹
      (x + (1 / (d + 1)) • u)‖ ^ 2 =
      ((d ^ 2 - 1) * ‖x‖ ^ 2 + 2 * (d + 1) * (⟪u, x⟫ * (⟪u, x⟫ + 1)) + 1) / d ^ 2 := by
    rw [norm_axialMap_sq hu, hnorm, hip, hinv]
    simp only [axialRadius, inv_div]
    field_simp
    ring
  have hb : ‖axialMap u (axialRadius d)⁻¹ (transverseRadius d)⁻¹
      (x + (1 / (d + 1)) • u)‖ ^ 2 ≤ 1 := by
    rw [heq]
    apply (div_le_one (sq_pos_of_ne_zero hd0)).mpr
    have h1 := mul_le_mul_of_nonneg_left hx2 hs
    have h2 := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 2 * (d + 1)) htprod
    nlinarith
  nlinarith [norm_nonneg (axialMap u (axialRadius d)⁻¹ (transverseRadius d)⁻¹
    (x + (1 / (d + 1)) • u))]

structure Ellipsoid (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  center : E
  axes : E ≃ₗ[ℝ] E

def Ellipsoid.region (e : Ellipsoid E) : Set E := {x | ‖e.axes.symm (x - e.center)‖ ≤ 1}

def Ellipsoid.cut (e : Ellipsoid E) (d : ℝ) (hd : 2 ≤ d) (u : E) (hu : ‖u‖ = 1) : Ellipsoid E where
  center := e.center - e.axes ((1 / (d + 1)) • u)
  axes := (axialEquiv u hu (axialRadius d) (transverseRadius d)
    (axialRadius_pos hd).ne' (transverseRadius_pos hd).ne').trans e.axes

theorem Ellipsoid.cut_contains (e : Ellipsoid E) (d : ℝ) (hd : 2 ≤ d)
    (u : E) (hu : ‖u‖ = 1) {x : E} (hx : x ∈ e.region)
    (hcut : ⟪u, e.axes.symm (x - e.center)⟫ ≤ 0) :
    x ∈ (e.cut d hd u hu).region := by
  have heq : x - (e.center - e.axes ((1 / (d + 1)) • u)) =
      (x - e.center) + e.axes ((1 / (d + 1)) • u) := by abel
  change ‖axialMap u (axialRadius d)⁻¹ (transverseRadius d)⁻¹
    (e.axes.symm (x - (e.center - e.axes ((1 / (d + 1)) • u))))‖ ≤ 1
  rw [heq, map_add, LinearEquiv.symm_apply_apply]
  exact centralCut_contains hd hu hx hcut

end DPCut.EllipsoidMethod
