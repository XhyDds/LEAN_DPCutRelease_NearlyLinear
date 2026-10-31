import DPCut.Optimizer
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! The shrunken cut matrix used in Lemma 19 (`lem:sdp_error`). -/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder

namespace DPCut

@[simp] lemma cutSign_mul_self {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    cutSign S i * cutSign S i = 1 := by
  classical
  by_cases hi : i ∈ S <;> simp [cutSign, hi]

lemma cutSign_dot_self {n : ℕ} (S : Finset (Fin n)) :
    cutSign S ⬝ᵥ cutSign S = (n : ℝ) := by
  simp [dotProduct]

lemma shrunkenCut_feasible {n : ℕ} (hn : 2 ≤ n) (S : Finset (Fin n)) :
    shrunkenCut S ∈ feasible n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hc : 0 ≤ 1 - 1 / (n : ℝ) :=
    sub_nonneg.mpr (by simpa using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hnR)
  have hp : (Matrix.vecMulVec (cutSign S) (cutSign S)).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star (cutSign S)
  refine ⟨?_, ?_, ?_⟩
  · exact (hp.smul hc).isHermitian.add
      ((Matrix.PosSemidef.one : (1 : Mat n).PosSemidef).smul (by positivity)).isHermitian
  · intro i
    simp [shrunkenCut, Matrix.vecMulVec]
  · simpa only [shrunkenCut, add_sub_cancel_right] using hp.smul hc

lemma fractionalQuery_shrunkenCut {n : ℕ} (S : Finset (Fin n)) (e : Edge n) :
    fractionalQuery (shrunkenCut S) e =
      (1 - 1 / (n : ℝ)) * cutQuery S e + 1 / (2 * n) := by
  classical
  have he : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  simp only [fractionalQuery, shrunkenCut, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply, Matrix.one_apply_ne he, mul_zero, add_zero, cutSign, cutQuery]
  by_cases h1 : e.val.1 ∈ S <;> by_cases h2 : e.val.2 ∈ S <;> simp [h1, h2] <;> ring

/-- The rank-one determinant identity, using mathlib's matrix determinant lemma. -/
lemma det_one_add_smul_cutSign {n : ℕ} (S : Finset (Fin n)) (a : ℝ) :
    (1 + a • Matrix.vecMulVec (cutSign S) (cutSign S)).det = 1 + a * n := by
  rw [← Matrix.smul_vecMulVec, Matrix.vecMulVec_eq Unit,
    Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, cutSign_dot_self, smul_eq_mul]

lemma shrunkenCut_det {n : ℕ} (hn : 2 ≤ n) (S : Finset (Fin n)) :
    (shrunkenCut S).det = (n - 1 + 1 / (n : ℝ)) * (1 / (n : ℝ)) ^ (n - 1) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have he : shrunkenCut S = (1 / (n : ℝ)) •
      (1 + ((n : ℝ) - 1) • Matrix.vecMulVec (cutSign S) (cutSign S)) := by
    unfold shrunkenCut
    rw [smul_add, smul_smul]
    have hc : (1 / (n : ℝ)) * (n - 1) = 1 - 1 / n := by field_simp
    rw [hc, add_comm]
  rw [he, Matrix.det_smul, Fintype.card_fin, det_one_add_smul_cutSign]
  have hpow : (1 / (n : ℝ)) ^ n = (1 / (n : ℝ)) ^ (n - 1) * (1 / n) := by
    nth_rw 2 [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
  rw [hpow]
  field_simp
  ring

lemma shrunkenCut_logdet {n : ℕ} (hn : 2 ≤ n) (S : Finset (Fin n)) :
    Real.log (shrunkenCut S).det =
      Real.log (n - 1 + 1 / (n : ℝ)) - (n - 1 : ℝ) * Real.log n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have he : 0 < (n - 1 + 1 / (n : ℝ)) := by linarith [one_div_pos.mpr hn0]
  rw [shrunkenCut_det hn S, Real.log_mul he.ne' (pow_pos (by positivity) _).ne',
    Real.log_pow, one_div, Real.log_inv, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  ring

/-- The logarithmic penalty lies between zero and `n log n`. -/
lemma shrunkenCut_neg_logdet_bounds {n : ℕ} (hn : 2 ≤ n) (S : Finset (Fin n)) :
    0 ≤ -Real.log (shrunkenCut S).det ∧
      -Real.log (shrunkenCut S).det ≤ (n : ℝ) * Real.log n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hinv : 1 / (n : ℝ) ≤ 1 := (div_le_iff₀ hn0).mpr (by linarith)
  have he1 : (1 : ℝ) ≤ n - 1 + 1 / (n : ℝ) := by linarith [one_div_pos.mpr hn0]
  have he2 : n - 1 + 1 / (n : ℝ) ≤ n := by linarith
  have hlog0 := Real.log_nonneg he1
  have hlog1 := Real.log_le_log (lt_of_lt_of_le zero_lt_one he1) he2
  have hlogn := Real.log_natCast_nonneg n
  rw [shrunkenCut_logdet hn S]
  constructor
  · nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - 2 by linarith) hlogn]
  · nlinarith

lemma pairing_shrunkenCut {n : ℕ} (D : Weights n) (S : Finset (Fin n)) :
    pairing D (fractionalQuery (shrunkenCut S)) =
      (1 - 1 / (n : ℝ)) * cut D S + mass D / (2 * n) := by
  simp only [cut, pairing, fractionalQuery_shrunkenCut, mass,
    Finset.mul_sum, Finset.sum_div, mul_add, Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro e _ <;> ring

end DPCut
