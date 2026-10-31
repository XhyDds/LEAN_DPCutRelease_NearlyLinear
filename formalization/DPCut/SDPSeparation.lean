import DPCut.SDPObjectiveBounds
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! A concrete separation and first-order oracle in the full-dimensional
coordinates. The only problem-specific external primitive finds a negative
quadratic form when a symmetric matrix is not positive semidefinite. -/
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Metric
open scoped RealInnerProductSpace BigOperators
namespace DPCut.SDPCoordinates

/-- Vectorization preserves the Frobenius pairing. -/
def flatten (n : ℕ) : Mat n →ₗ[ℝ] Space n where
  toFun X := WithLp.toLp 2 (fun ij => X ij.1 ij.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma flatten_inner {n : ℕ} (A X : Mat n) :
    ⟪flatten n A, flatten n X⟫ = matrixPairing A X := by
  simp [PiLp.inner_apply, flatten, matrixPairing, Fintype.sum_prod_type, mul_comm]

/-- The adjoint of the fixed coordinate projection. It is a fixed finite matrix
transpose/multiply, not an optimization primitive. -/
def normal (n : ℕ) : Mat n →ₗ[ℝ] Space n :=
  (LinearMap.adjoint ((flatten n).comp (offDiag n))).comp (flatten n)

lemma normal_inner {n : ℕ} (A : Mat n) (z : Space n) :
    ⟪normal n A, z⟫ = matrixPairing A (offDiag n z) := by
  rw [normal, LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearMap.comp_apply, flatten_inner]

lemma normal_inner_sub {n : ℕ} (A : Mat n) (y x : Space n) :
    ⟪normal n A, y-x⟫ = matrixPairing A (lift y - lift x) := by
  rw [normal_inner, map_sub]
  congr 1
  simp [lift]

lemma quadratic_pairing {n : ℕ} (v : Fin n → ℝ) (X : Mat n) :
    matrixPairing (Matrix.vecMulVec v v) X = v ⬝ᵥ (X *ᵥ v) := by
  simp only [matrixPairing, Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, Finset.mul_sum]
  congr 1
  ext i
  congr 1
  ext j
  ring

def slack {n : ℕ} (x : Space n) : Mat n := lift x - (1 / (n : ℝ)) • 1

@[fun_prop] lemma continuous_slack (n : ℕ) : Continuous (slack (n := n)) :=
  (continuous_lift n).sub continuous_const

lemma slack_hermitian {n : ℕ} (x : Space n) : (slack x).IsHermitian := by
  apply (lift_hermitian x).sub
  exact ((Matrix.PosSemidef.one : (1 : Mat n).PosSemidef).smul (by positivity : 0 ≤ 1 / (n : ℝ))).1

lemma slack_posSemidef_iff {n : ℕ} (x : Space n) :
    (slack x).PosSemidef ↔ lift x ∈ feasible n :=
  ⟨fun h => ⟨lift_hermitian x, lift_diag x, h⟩, fun h => h.2.2⟩

lemma quadratic_normal {n : ℕ} (v : Fin n → ℝ) (y x : Space n) :
    ⟪normal n (-(Matrix.vecMulVec v v)), y-x⟫ =
      v ⬝ᵥ (slack x *ᵥ v) - v ⬝ᵥ (slack y *ᵥ v) := by
  rw [map_neg, inner_neg_left, normal_inner_sub, matrixPairing_sub_right,
    quadratic_pairing, quadratic_pairing]
  simp only [slack, Matrix.sub_mulVec, dotProduct_sub]
  ring

lemma psd_cut {n : ℕ} (hn : 2 ≤ n) (x : Space n) (v : Fin n → ℝ)
    (hv : v ⬝ᵥ (slack x *ᵥ v) < 0) :
    x ∉ body n ∧ normal n (-(Matrix.vecMulVec v v)) ≠ 0 ∧
      ∀ y ∈ body n, ⟪normal n (-(Matrix.vecMulVec v v)), y-x⟫ ≤ 0 := by
  have hcut (y : Space n) (hy : lift y ∈ feasible n) :
      ⟪normal n (-(Matrix.vecMulVec v v)), y-x⟫ < 0 := by
    have hq := hy.2.2.2 v
    simp only [star_trivial] at hq
    rw [quadratic_normal]
    change 0 ≤ v ⬝ᵥ (slack y *ᵥ v) at hq
    linarith
  refine ⟨?_, ?_, fun y hy => (hcut y hy.2).le⟩
  · intro hx
    have := hcut x hx.2
    simp at this
  · intro hg
    have h0 : lift (0 : Space n) ∈ feasible n := by simpa using feasible_one hn
    have hh := hcut 0 h0
    simp [hg] at hh

lemma ball_cut {n : ℕ} (x : Space n) (hx : 2 * (n : ℝ) < ‖x‖) :
    x ∉ body n ∧ x ≠ 0 ∧ ∀ y ∈ body n, ⟪x, y-x⟫ ≤ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hh : ‖x‖ ≤ 2*n := by simpa using h.1
    linarith
  · intro h
    simp only [h, norm_zero] at hx
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  · intro y hy
    have hy' : ‖y‖ ≤ 2*n := by simpa using hy.1
    rw [inner_sub_right, real_inner_self_eq_norm_sq]
    have h := real_inner_le_norm x y
    have hm := mul_le_mul_of_nonneg_left (hy'.trans hx.le) (norm_nonneg x)
    nlinarith

lemma objective_supergradient {n : ℕ} (hn : 2 ≤ n) {lam : ℝ} (hlam : 0 ≤ lam)
    (D : Weights n) {x y : Space n} (hx : x ∈ body n) (hy : y ∈ body n) :
    objective lam D (lift y) ≤ objective lam D (lift x) +
      ⟪normal n (objectiveMatrix D + lam • (lift x)⁻¹), y-x⟫ := by
  rw [normal_inner_sub]
  exact objective_tangent_upper hn hlam D hx.2 hy.2

end DPCut.SDPCoordinates
