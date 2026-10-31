import DPCut.SDPLinearOracle

/-! Full-dimensional coordinates for LSW. The redundant `n²` coordinates avoid
identifying the unit-diagonal affine space with a lower-dimensional subspace.
The extra directions are bounded by a Euclidean ball; this does not remove any
feasible matrix. -/
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Metric
open scoped RealInnerProductSpace BigOperators
namespace DPCut
namespace SDPCoordinates

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n × Fin n)

def offDiag (n : ℕ) : Space n →ₗ[ℝ] Mat n where
  toFun z i j := if i = j then 0 else (z (i,j) + z (j,i)) / 2
  map_add' x y := by
    ext i j
    by_cases h : i = j
    · simp [h]
    · simp [h]; ring
  map_smul' a x := by
    ext i j
    by_cases h : i = j
    · simp [h]
    · simp [h]; ring

@[simp] lemma offDiag_apply {n : ℕ} (z : Space n) (i j : Fin n) :
    offDiag n z i j = if i = j then 0 else (z (i,j) + z (j,i)) / 2 := rfl

lemma offDiag_hermitian {n : ℕ} (z : Space n) : (offDiag n z).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, offDiag_apply]
  by_cases h : i = j
  · subst j; simp
  · simp [h, Ne.symm h, add_comm]

def lift {n : ℕ} (z : Space n) : Mat n := 1 + offDiag n z

@[fun_prop] lemma continuous_lift (n : ℕ) : Continuous (lift (n := n)) :=
  continuous_const.add (offDiag n).continuous_of_finiteDimensional

@[simp] lemma lift_zero (n : ℕ) : lift (0 : Space n) = 1 := by simp [lift]

lemma lift_hermitian {n : ℕ} (z : Space n) : (lift z).IsHermitian :=
  Matrix.isHermitian_one.add (offDiag_hermitian z)

@[simp] lemma lift_diag {n : ℕ} (z : Space n) (i : Fin n) : lift z i i = 1 := by
  simp [lift]

lemma lift_combo {n : ℕ} (x y : Space n) {a b : ℝ} (hab : a + b = 1) :
    lift (a • x + b • y) = a • lift x + b • lift y := by
  simp only [lift, map_add, map_smul, smul_add]
  have hb : b = 1 - a := by linarith
  rw [hb]
  module

lemma norm_sq {n : ℕ} (z : Space n) : ‖z‖ ^ 2 = ∑ i, ∑ j, z (i,j) ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, Fintype.sum_prod_type]

lemma offDiag_frobenius_le {n : ℕ} (z : Space n) : frobenius (offDiag n z) ≤ ‖z‖ := by
  have hpoint (i j : Fin n) : (offDiag n z i j) ^ 2 ≤
      (z (i,j) ^ 2 + z (j,i) ^ 2) / 2 := by
    by_cases h : i = j
    · simp [h]; positivity
    · simp only [offDiag_apply, if_neg h]; nlinarith [sq_nonneg (z (i,j) - z (j,i))]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hpoint i j))
  have ht : (∑ i : Fin n, ∑ j : Fin n, z (j,i) ^ 2) = ∑ i, ∑ j, z (i,j) ^ 2 :=
    Finset.sum_comm
  simp only [← Finset.sum_div, Finset.sum_add_distrib, ht] at hsum
  rw [← frobenius_sq, ← norm_sq] at hsum
  nlinarith [frobenius_nonneg (offDiag n z), norm_nonneg z]

lemma quadratic_lower {n : ℕ} (E : Mat n) (v : Fin n → ℝ) :
    -(frobenius E * (∑ i, v i ^ 2)) ≤ v ⬝ᵥ (E *ᵥ v) := by
  have hb := matrix_bilinear_sq_le E v v
  have hpos : 0 ≤ frobenius E * (∑ i, v i ^ 2) :=
    mul_nonneg (frobenius_nonneg _) (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  nlinarith [sq_nonneg (v ⬝ᵥ (E *ᵥ v) + frobenius E * (∑ i, v i ^ 2))]

lemma lift_feasible_of_norm {n : ℕ} (hn : 2 ≤ n) {z : Space n} (hz : ‖z‖ ≤ 1 / 4) :
    lift z ∈ feasible n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hinv : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hnR
  refine ⟨lift_hermitian z, lift_diag z, ?_⟩
  refine ⟨(lift_hermitian z).sub ((Matrix.PosSemidef.one : (1 : Mat n).PosSemidef).smul (by positivity : 0 ≤ 1 / (n : ℝ))).1, ?_⟩
  intro v
  have hlow := quadratic_lower (offDiag n z) v
  have hf := (offDiag_frobenius_le z).trans hz
  have hsum : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hprod := mul_le_mul_of_nonneg_right hf hsum
  have hi := mul_le_mul_of_nonneg_right hinv hsum
  have heq : star v ⬝ᵥ ((lift z - (1 / (n : ℝ)) • 1) *ᵥ v) =
      (1 - 1 / (n : ℝ)) * (∑ i, v i ^ 2) + v ⬝ᵥ (offDiag n z *ᵥ v) := by
    simp only [lift, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, star_trivial, dotProduct_sub, dotProduct_add, dotProduct_smul]
    simp only [dotProduct, pow_two, smul_eq_mul]
    ring
  rw [heq]
  nlinarith

def encode {n : ℕ} (X : Mat n) : Space n := WithLp.toLp 2 (fun ij => (X - 1) ij.1 ij.2)

lemma lift_encode {n : ℕ} {X : Mat n} (hX : X ∈ feasible n) : lift (encode X) = X := by
  ext i j
  have hs : X j i = X i j := by simpa using hX.1.apply i j
  by_cases h : i = j
  · subst j; simp [hX.2.1]
  · simp [lift, encode, h, Ne.symm h, hs]

lemma encode_norm_le {n : ℕ} (hn : 2 ≤ n) {X : Mat n} (hX : X ∈ feasible n) :
    ‖encode X‖ ≤ n := by
  have hb (i j : Fin n) : (encode X (i,j)) ^ 2 ≤ 1 := by
    by_cases h : i = j
    · subst j; simp [encode, hX.2.1]
    · have ha := abs_le.mp (feasible_entry_abs_le_one hn hX i j)
      simp only [encode, PiLp.toLp_apply, Matrix.sub_apply, Matrix.one_apply_ne h, sub_zero]
      nlinarith
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hb i j))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hh
  rw [← norm_sq] at hh
  nlinarith [norm_nonneg (encode X), Nat.cast_nonneg (α := ℝ) n]

def body (n : ℕ) : Set (Space n) := closedBall 0 (2 * n) ∩ lift ⁻¹' feasible n

lemma body_convex (n : ℕ) : Convex ℝ (body n) := by
  apply (convex_closedBall (0 : Space n) (2 * n)).inter
  intro x hx y hy a b ha hb hab
  change lift (a • x + b • y) ∈ feasible n
  rw [lift_combo x y hab]
  exact feasible_convex n hx hy ha hb hab

lemma body_compact (n : ℕ) : IsCompact (body n) :=
  (isCompact_closedBall (0 : Space n) (2 * n)).inter_right
    ((feasible_closed n).preimage (continuous_lift n))

lemma inner_ball {n : ℕ} (hn : 2 ≤ n) : closedBall (0 : Space n) (1/4) ⊆ body n := by
  intro z hz
  have hz' : ‖z‖ ≤ 1/4 := by simpa using hz
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact ⟨by simpa using (show ‖z‖ ≤ 2*n by linarith), lift_feasible_of_norm hn hz'⟩

lemma encode_mem {n : ℕ} (hn : 2 ≤ n) {X : Mat n} (hX : X ∈ feasible n) :
    encode X ∈ body n := by
  refine ⟨?_, ?_⟩
  · have := encode_norm_le hn hX
    simpa using (show ‖encode X‖ ≤ 2*n by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  · change lift (encode X) ∈ feasible n
    rwa [lift_encode hX]

end SDPCoordinates
end DPCut
