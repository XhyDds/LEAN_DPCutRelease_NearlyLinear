import DPCut.CappedProgress

/-! Coordinatewise telescoping enforces the output cap on every execution. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DPCut

theorem capped_retirement_sum_bound {n : ℕ} (a h r : ℕ → Weights n)
    (ha0 : Nonnegative (a 0)) (T : ℕ)
    (hh : ∀ t < T, ∀ e, 0 ≤ h t e ∧ h t e ≤ a t e)
    (hr : ∀ t < T, IsMask (r t))
    (ha : ∀ t < T, a (t + 1) = residualUpdate (a t) (r t)) :
    ∀ e, 0 ≤ a T e ∧ 0 ≤ ∑ t ∈ Finset.range T, h t e * r t e ∧
      (∑ t ∈ Finset.range T, h t e * r t e) ≤ a 0 e - a T e := by
  induction T with
  | zero => intro e; simpa using ha0 e
  | succ T ih =>
    have ih' := ih (fun t ht => hh t (by omega)) (fun t ht => hr t (by omega))
      (fun t ht => ha t (by omega))
    intro e
    obtain ⟨hpos, hlo, hhi⟩ := ih' e
    have hhT := hh T (by omega) e
    have hrT := hr T (by omega) e
    have haT := congrFun (ha T (by omega)) e
    change a (T + 1) e = a T e * (1 - r T e) at haT
    rw [Finset.sum_range_succ]
    refine ⟨?_, ?_, ?_⟩
    · rw [haT]
      exact mul_nonneg hpos (sub_nonneg.mpr hrT.2)
    · exact add_nonneg hlo (mul_nonneg hhT.1 hrT.1)
    · have hm := mul_le_mul_of_nonneg_right hhT.2 hrT.1
      nlinarith

theorem capped_retirement_output {n : ℕ} (D : Finset (Edge n)) (a h r : ℕ → Weights n)
    (ha0 : ∀ e, a 0 e = if e ∈ D then 1 else 0) (T : ℕ)
    (hh : ∀ t < T, ∀ e, 0 ≤ h t e ∧ h t e ≤ a t e)
    (hr : ∀ t < T, IsMask (r t))
    (ha : ∀ t < T, a (t + 1) = residualUpdate (a t) (r t)) :
    CappedOn D (fun e => ∑ t ∈ Finset.range T, h t e * r t e) := by
  have hz : Nonnegative (a 0) := by intro e; rw [ha0 e]; split <;> norm_num
  have hb := capped_retirement_sum_bound a h r hz T hh hr ha
  have hupper (e : Edge n) : (∑ t ∈ Finset.range T, h t e * r t e) ≤ a 0 e := by
    have he := hb e
    linarith [he.1, he.2.2]
  constructor
  · intro e
    refine ⟨(hb e).2.1, (hupper e).trans ?_⟩
    rw [ha0 e]
    split <;> norm_num
  · intro e he
    have hh' := hupper e
    rw [ha0 e, if_neg he] at hh'
    exact le_antisymm hh' (hb e).2.1

end DPCut
