import DPCut.EllipsoidAlgorithm
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The usual point-separation interface, an initial enclosing ball, and the
explicit dimension/radius-ratio bound for ellipsoid feasibility. -/
set_option autoImplicit false
noncomputable section
open Metric
open scoped RealInnerProductSpace
namespace DPCut.EllipsoidMethod

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

/-- An ordinary separating normal in the original Euclidean coordinates. -/
inductive PointDecision (K : Set E) (p : E) where
  | accept (feasible : p ∈ K)
  | separate (normal : E) (nonzero : normal ≠ 0)
      (valid : ∀ x ∈ K, ⟪normal, x - p⟫ ≤ 0)

abbrev PointOracle (K : Set E) := (p : E) → PointDecision K p

def Ellipsoid.pullNormal (e : Ellipsoid E) (g : E) : E :=
  LinearMap.adjoint (e.axes : E →ₗ[ℝ] E) g

lemma Ellipsoid.pullNormal_ne_zero (e : Ellipsoid E) {g : E} (hg : g ≠ 0) :
    e.pullNormal g ≠ 0 := by
  intro h
  have hself : ⟪g, g⟫ = 0 := by
    calc
      ⟪g, g⟫ = ⟪e.pullNormal g, e.axes.symm g⟫ := by
        rw [pullNormal, LinearMap.adjoint_inner_left]
        simp
      _ = 0 := by rw [h]; simp
  apply hg
  simpa only [real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero] using hself

def Ellipsoid.unitNormal (e : Ellipsoid E) (g : E) : E :=
  ‖e.pullNormal g‖⁻¹ • e.pullNormal g

lemma Ellipsoid.unitNormal_norm (e : Ellipsoid E) {g : E} (hg : g ≠ 0) :
    ‖e.unitNormal g‖ = 1 := by
  simp [unitNormal, norm_smul, norm_ne_zero_iff.mpr (e.pullNormal_ne_zero hg)]

lemma Ellipsoid.unitNormal_valid (e : Ellipsoid E) (g x : E)
    (h : ⟪g, x - e.center⟫ ≤ 0) :
    ⟪e.unitNormal g, e.axes.symm (x - e.center)⟫ ≤ 0 := by
  rw [unitNormal, real_inner_smul_left, pullNormal, LinearMap.adjoint_inner_left]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _)) h

/-- Transform the supplied normal by the transpose of the ellipsoid axes and
normalize it; no new separation oracle is assumed in this conversion. -/
def PointOracle.toSeparationOracle {K : Set E} (oracle : PointOracle K) :
    SeparationOracle K := fun e => match oracle e.center with
  | .accept h => .accept h
  | .separate g hg h => .separate (e.unitNormal g) (e.unitNormal_norm hg)
      (fun x hx => e.unitNormal_valid g x (h x hx))

def Ellipsoid.ball (c : E) (R : ℝ) (hR : 0 < R) : Ellipsoid E where
  center := c
  axes := LinearEquiv.smulOfNeZero ℝ E R hR.ne'

@[simp] lemma Ellipsoid.ball_region (c : E) (R : ℝ) (hR : 0 < R) :
    (ball c R hR).region = closedBall c R := by
  ext x
  change ‖R⁻¹ • (x - c)‖ ≤ 1 ↔ dist x c ≤ R
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), dist_eq_norm]
  rw [inv_mul_le_iff₀ hR]
  simp

@[simp] lemma Ellipsoid.ball_size (c : E) (R : ℝ) (hR : 0 < R) :
    (ball c R hR).size = R ^ m := by
  change |LinearMap.det (R • (LinearMap.id : E →ₗ[ℝ] E))| = _
  rw [LinearMap.det_smul]
  simp [finrank_euclideanSpace, abs_of_pos hR]

/-- A dimension-uniform budget, including dimension one. -/
def ballIterationBudget (m : ℕ) (R r : ℝ) : ℕ :=
  ⌊2 * (m + 2) * m * Real.log (R / r)⌋₊ + 1

theorem ballIterationBudget_eq {R r : ℝ} (hR : 0 < R) (hr : 0 < r) :
    ballIterationBudget m R r = iterationBudget m (m + 1) (R ^ m) r := by
  unfold ballIterationBudget iterationBudget
  rw [Real.log_div hR.ne' hr.ne', Real.log_pow]
  congr 2
  ring

theorem feasible_of_balls {K : Set E} (oracle : PointOracle K) (hm : 1 ≤ m)
    (c p : E) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (houter : K ⊆ closedBall c R) (hinner : closedBall p r ⊆ K) :
    ∃ x, run oracle.toSeparationOracle (m + 1) (by exact_mod_cast Nat.succ_le_succ hm)
      (ballIterationBudget m R r) (Ellipsoid.ball c R hR) = .inl x := by
  rw [ballIterationBudget_eq hR hr, ← Ellipsoid.ball_size c R hR]
  apply run_iterationBudget_success _ _ _ (by linarith) _ _ p hr hinner
  simpa using houter

theorem ballIterationBudget_le {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    (ballIterationBudget m R r : ℝ) ≤ 2 * (m + 2) * m * Real.log (R / r) + 1 := by
  have hlog : 0 ≤ Real.log (R / r) :=
    Real.log_nonneg ((one_le_div hr).mpr hrR)
  have hnonneg : 0 ≤ 2 * (m + 2 : ℝ) * m * Real.log (R / r) := by positivity
  simpa [ballIterationBudget] using add_le_add_right (Nat.floor_le hnonneg) 1

end DPCut.EllipsoidMethod
