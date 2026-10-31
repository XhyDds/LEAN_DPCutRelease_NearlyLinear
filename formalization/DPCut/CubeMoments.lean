import DPCut.Definitions
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Fin.Tuple.Basic

/-! Finite Rademacher averages, used by the lower-bound discrepancy argument. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DPCut

def boolSign (b : Bool) : ℝ := if b then 1 else -1

lemma expect_bool (f : Bool → ℝ) : (𝔼 b, f b) = (f false + f true) / 2 := by
  simp [Finset.expect_eq_sum_div_card, add_comm]

lemma expect_cube_succ {d : ℕ} (f : (Fin (d + 1) → Bool) → ℝ) :
    (𝔼 x, f x) = 𝔼 x : Fin d → Bool, (f (Fin.cons false x) + f (Fin.cons true x)) / 2 := by
  have h := Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (d + 1) => Bool))
    (fun bx => f (Fin.cons bx.1 bx.2)) f (fun _ => rfl)
  rw [← h, ← Finset.univ_product_univ, Finset.expect_product]
  rw [Finset.expect_comm]
  exact Finset.expect_congr rfl (fun _ _ => expect_bool _)

def signSum {d : ℕ} (a : Fin d → ℝ) (x : Fin d → Bool) : ℝ :=
  ∑ j, a j * boolSign (x j)

lemma signSum_cons {d : ℕ} (a : Fin (d + 1) → ℝ) (b : Bool) (x : Fin d → Bool) :
    signSum a (Fin.cons b x) = a 0 * boolSign b + signSum (fun j => a j.succ) x := by
  simp [signSum, Fin.sum_univ_succ]

lemma signSum_second {d : ℕ} (a : Fin d → ℝ) :
    (𝔼 x, signSum a x ^ 2) = ∑ j, a j ^ 2 := by
  induction d with
  | zero => simp [signSum]
  | succ d ih =>
    rw [expect_cube_succ]
    simp only [signSum_cons, boolSign, Bool.false_eq_true, ↓reduceIte, mul_neg_one,
      mul_one]
    have he (z : ℝ) : ((-a 0 + z) ^ 2 + (a 0 + z) ^ 2) / 2 = a 0 ^ 2 + z ^ 2 := by ring
    simp_rw [he]
    rw [Finset.expect_add_distrib, Fintype.expect_const, ih, Fin.sum_univ_succ]

lemma signSum_fourth {d : ℕ} (a : Fin d → ℝ) :
    (𝔼 x, signSum a x ^ 4) ≤ 3 * (∑ j, a j ^ 2) ^ 2 := by
  induction d with
  | zero => simp [signSum]
  | succ d ih =>
    rw [expect_cube_succ]
    simp only [signSum_cons, boolSign, Bool.false_eq_true, ↓reduceIte, mul_neg_one,
      mul_one]
    have he (z : ℝ) : ((-a 0 + z) ^ 4 + (a 0 + z) ^ 4) / 2 =
        a 0 ^ 4 + 6 * a 0 ^ 2 * z ^ 2 + z ^ 4 := by ring
    simp_rw [he]
    rw [Finset.expect_add_distrib, Finset.expect_add_distrib, Fintype.expect_const,
      ← Finset.mul_expect, signSum_second, Fin.sum_univ_succ]
    have hh := ih (fun j => a j.succ)
    nlinarith [sq_nonneg (a 0 ^ 2)]

/-- A deliberately coarse Khintchine lower bound, proved from moments two and four. -/
lemma signSum_abs_lower {d : ℕ} (a : Fin d → ℝ) {v : ℝ}
    (hv : 0 < v) (ha : ∑ j, a j ^ 2 ≤ v) :
    (∑ j, a j ^ 2) ≤ 16 * Real.sqrt v * (𝔼 x, |signSum a x|) := by
  let s := Real.sqrt v
  have hs : 0 < s := Real.sqrt_pos.2 hv
  have hs2 : s ^ 2 = v := Real.sq_sqrt hv.le
  have hp (z : ℝ) : z ^ 2 ≤ 8 * s * |z| + z ^ 4 / (64 * v) := by
    by_cases hz : |z| ≤ 8 * s
    · have hh := mul_nonneg (abs_nonneg z) (sub_nonneg.2 hz)
      have h4 : 0 ≤ z ^ 4 / (64 * v) := div_nonneg (by positivity) (by positivity)
      nlinarith [sq_abs z]
    · have hlarge : 64 * v ≤ z ^ 2 := by nlinarith [sq_abs z, abs_nonneg z]
      have hh := mul_nonneg (sq_nonneg z) (sub_nonneg.2 hlarge)
      have hd : z ^ 2 ≤ z ^ 4 / (64 * v) := by
        apply (le_div_iff₀ (by positivity)).2
        nlinarith
      nlinarith [mul_nonneg hs.le (abs_nonneg z)]
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun x _ => hp (signSum a x))
  rw [signSum_second, Finset.expect_add_distrib, ← Finset.mul_expect,
    ← Finset.expect_div] at hm
  have h4 := signSum_fourth a
  have hq : 0 ≤ ∑ j, a j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h4' : (𝔼 x, signSum a x ^ 4) / (64 * v) ≤ (∑ j, a j ^ 2) / 2 := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [mul_nonneg hq (sub_nonneg.2 ha)]
  dsimp [s] at hm
  linarith

end DPCut
