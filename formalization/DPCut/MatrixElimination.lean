import DPCut.SDPLinearOracle
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Scalar Schur elimination. All pivots, including zero pivots, are handled.
The negative branch returns a concrete quadratic-form witness. -/
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped BigOperators
namespace DPCut.MatrixElimination
attribute [local instance] Classical.propDecidable

def tail {n : ℕ} (M : Mat (n+1)) : Mat n := fun i j => M i.succ j.succ
def row {n : ℕ} (M : Mat (n+1)) : Fin n → ℝ := fun i => M 0 i.succ
def schur {n : ℕ} (M : Mat (n+1)) : Mat n :=
  fun i j => tail M i j - row M i * row M j / M 0 0
def prepend {n : ℕ} (t : ℝ) (v : Fin n → ℝ) : Fin (n+1) → ℝ := Fin.cons t v
def qform {n : ℕ} (M : Mat n) (v : Fin n → ℝ) : ℝ := v ⬝ᵥ (M *ᵥ v)

lemma symmetric {n : ℕ} {M : Mat n} (h : M.IsHermitian) (i j : Fin n) : M j i = M i j := by
  have hh := congrFun (congrFun h i) j
  simpa [Matrix.conjTranspose_apply] using hh

lemma tail_hermitian {n : ℕ} {M : Mat (n+1)} (h : M.IsHermitian) : (tail M).IsHermitian := by
  exact h.submatrix Fin.succ

lemma schur_hermitian {n : ℕ} {M : Mat (n+1)} (h : M.IsHermitian) : (schur M).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, schur, tail]
  rw [symmetric h i.succ j.succ, mul_comm (row M j)]

lemma qform_prepend {n : ℕ} {M : Mat (n+1)} (h : M.IsHermitian)
    (t : ℝ) (v : Fin n → ℝ) :
    qform M (prepend t v) = M 0 0*t^2 + 2*t*(row M ⬝ᵥ v) + qform (tail M) v := by
  simp only [qform, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, prepend,
    Fin.cons_zero, Fin.cons_succ]
  simp_rw [symmetric h (0 : Fin (n+1)), mul_add, Finset.sum_add_distrib]
  simp only [tail, row]
  have hs : (∑ x, v x * (M 0 x.succ * t)) = t * ∑ x, M 0 x.succ * v x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [hs]
  ring

lemma qform_schur {n : ℕ} (M : Mat (n+1)) (v : Fin n → ℝ) :
    qform (schur M) v = qform (tail M) v - (row M ⬝ᵥ v)^2 / M 0 0 := by
  simp only [qform, Matrix.mulVec, dotProduct, schur, sub_mul, Finset.sum_sub_distrib, mul_sub]
  congr 1
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma qform_eliminate {n : ℕ} {M : Mat (n+1)} (h : M.IsHermitian) (ha : M 0 0 ≠ 0)
    (t : ℝ) (v : Fin n → ℝ) :
    qform M (prepend t v) =
      M 0 0 * (t + (row M ⬝ᵥ v) / M 0 0)^2 + qform (schur M) v := by
  rw [qform_prepend h, qform_schur]
  field_simp
  ring

lemma qform_lift {n : ℕ} {M : Mat (n+1)} (h : M.IsHermitian) (ha : M 0 0 ≠ 0)
    (v : Fin n → ℝ) :
    qform M (prepend (-(row M ⬝ᵥ v) / M 0 0) v) = qform (schur M) v := by
  rw [qform_eliminate h ha]
  simp [neg_div]

lemma psd_schur {n : ℕ} {M : Mat (n+1)} (h : M.IsHermitian) (ha : 0 < M 0 0) :
    M.PosSemidef ↔ (schur M).PosSemidef := by
  constructor
  · intro hp
    refine ⟨schur_hermitian h, fun v => ?_⟩
    have hh := hp.2 (prepend (-(row M ⬝ᵥ v) / M 0 0) v)
    simp only [star_trivial] at hh ⊢
    change 0 ≤ qform M _ at hh
    rwa [qform_lift h ha.ne'] at hh
  · intro hp
    refine ⟨h, fun v => ?_⟩
    have hv : v = prepend (v 0) (fun i => v i.succ) := by ext i; exact (Fin.cases rfl (fun _ => rfl) i)
    simp only [star_trivial]
    change 0 ≤ qform M v
    rw [hv, qform_eliminate h ha.ne']
    exact add_nonneg (mul_nonneg ha.le (sq_nonneg _)) (hp.2 _)

lemma qform_single {n : ℕ} (M : Mat n) (i : Fin n) : qform M (Pi.single i 1) = M i i := by
  simp [qform]

lemma psd_zero_row {n : ℕ} {M : Mat (n+1)} (h : M.IsHermitian)
    (ha : M 0 0 = 0) (hr : ∀ i, row M i = 0) :
    M.PosSemidef ↔ (tail M).PosSemidef := by
  constructor
  · intro hp; exact hp.submatrix Fin.succ
  · intro hp
    refine ⟨h, fun v => ?_⟩
    have hv : v = prepend (v 0) (fun i => v i.succ) := by ext i; exact (Fin.cases rfl (fun _ => rfl) i)
    simp only [star_trivial]
    change 0 ≤ qform M v
    rw [hv, qform_prepend h]
    have hh : row M = 0 := funext hr
    simpa [ha, hh, qform] using hp.2 (fun i => v i.succ)

/-- First nonzero entry, using a bounded left-to-right scan. -/
def firstNonzero : {n : ℕ} → (Fin n → ℝ) → Option (Fin n)
  | 0, _ => none
  | n+1, r => if r 0 = 0 then (firstNonzero (fun i : Fin n => r i.succ)).map Fin.succ else some 0

lemma firstNonzero_none {n : ℕ} (r : Fin n → ℝ) :
    firstNonzero r = none ↔ ∀ i, r i = 0 := by
  induction n with
  | zero => simp [firstNonzero]
  | succ n ih =>
    rw [firstNonzero]
    split_ifs with h
    · simp only [Option.map_eq_none_iff, ih]
      exact ⟨fun hh i => Fin.cases h hh i, fun hh i => hh i.succ⟩
    · simp only [false_iff]
      exact fun hh => h (hh 0)

lemma firstNonzero_some {n : ℕ} (r : Fin n → ℝ) {j : Fin n}
    (hj : firstNonzero r = some j) : r j ≠ 0 := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    rw [firstNonzero] at hj
    split_ifs at hj with h
    · rcases Option.map_eq_some_iff.mp hj with ⟨i, hi, rfl⟩
      exact ih _ hi
    · cases Option.some.inj hj
      exact h

def psdWitness : {n : ℕ} → Mat n → Option (Fin n → ℝ)
  | 0, _ => none
  | _+1, M =>
    if M 0 0 < 0 then some (prepend 1 0) else
    if M 0 0 = 0 then
      match firstNonzero (row M) with
      | some j => some (prepend (-(tail M j j + 1) / (2 * row M j)) (Pi.single j 1))
      | none => (psdWitness (tail M)).map (prepend 0)
    else (psdWitness (schur M)).map (fun v => prepend (-(row M ⬝ᵥ v) / M 0 0) v)

lemma psdWitness_correct {n : ℕ} (M : Mat n) (hM : M.IsHermitian) :
    match psdWitness M with
    | none => M.PosSemidef
    | some v => qform M v < 0 := by
  induction n with
  | zero => exact ⟨hM, fun _ => by simp [dotProduct]⟩
  | succ n ih =>
    rw [psdWitness]
    split_ifs with ha hz
    · change qform M (prepend 1 0) < 0
      rw [qform_prepend hM]
      simpa [qform] using ha
    · cases hj : firstNonzero (row M) with
      | some j =>
        dsimp only
        rw [qform_prepend hM, hz, qform_single]
        simp only [dotProduct_single, mul_one, zero_mul, zero_add]
        have hb := firstNonzero_some (row M) hj
        have he : 2 * (-(tail M j j + 1) / (2 * row M j)) * row M j + tail M j j = -1 := by
          field_simp
          ring
        rw [he]; norm_num
      | none =>
        have hr := (firstNonzero_none _).mp hj
        have hh := ih (tail M) (tail_hermitian hM)
        cases hv : psdWitness (tail M) with
        | none => simpa [hv] using (psd_zero_row hM hz hr).mpr (by simpa [hv] using hh)
        | some v =>
          simp only [Option.map_some]
          simpa [qform_prepend hM] using (show qform (tail M) v < 0 by simpa [hv] using hh)
    · have hp : 0 < M 0 0 := lt_of_le_of_ne (le_of_not_gt ha) (Ne.symm hz)
      have hh := ih (schur M) (schur_hermitian hM)
      cases hv : psdWitness (schur M) with
      | none => simpa [hv] using (psd_schur hM hp).mpr (by simpa [hv] using hh)
      | some v =>
        simp only [Option.map_some]
        rw [qform_lift hM hp.ne']
        simpa [hv] using hh

end DPCut.MatrixElimination
