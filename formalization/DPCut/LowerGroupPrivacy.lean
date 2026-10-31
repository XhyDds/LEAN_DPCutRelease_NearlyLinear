import DPCut.TotalVariation
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Group privacy on nonnegative weighted graphs, with explicit constants. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace DPCut

lemma EdgeDP.path {n : ℕ} {M : Kernel (Weights n) (Weights n)} [IsMarkovKernel M]
    {ε δ : ℝ} (hp : EdgeDP M ε δ) (hδ : 0 ≤ δ) (w : ℕ → Weights n)
    (k : ℕ) (hw : ∀ j ≤ k, Nonnegative (w j))
    (ha : ∀ j < k, Adjacent (w j) (w (j + 1)))
    (s : Set (Weights n)) (hs : MeasurableSet s) :
    prob (M (w 0)) s ≤ Real.exp (k * ε) * prob (M (w k)) s +
      δ * ∑ j ∈ Finset.range k, Real.exp (j * ε) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hprev := ih (fun j hj => hw j (by omega)) (fun j hj => ha j (by omega))
    have hstep := (privacy_event_iff_real _ _ s ε hδ).mp
      (hp _ _ ⟨hw k (by omega), hw (k + 1) le_rfl, ha k (by omega)⟩ s hs)
    have he : Real.exp ((k + 1 : ℕ) * ε) = Real.exp (k * ε) * Real.exp ε := by
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Real.exp_add]
    rw [he, Finset.sum_range_succ]
    nlinarith [mul_le_mul_of_nonneg_left hstep (Real.exp_nonneg (k * ε))]

/-- A segment of length at most k is a chain of k edge-adjacent graphs. -/
lemma EdgeDP.group {n : ℕ} {M : Kernel (Weights n) (Weights n)} [IsMarkovKernel M]
    {ε δ : ℝ} (hp : EdgeDP M ε δ) (hδ : 0 ≤ δ) {w w' : Weights n}
    (hw : Nonnegative w) (hw' : Nonnegative w') {k : ℕ} (hk : 0 < k)
    (hd : l1 (w - w') ≤ k) (s : Set (Weights n)) (hs : MeasurableSet s) :
    prob (M w) s ≤ Real.exp (k * ε) * prob (M w') s +
      δ * ∑ j ∈ Finset.range k, Real.exp (j * ε) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  let p : ℕ → Weights n := fun j e => (1 - (j : ℝ) / k) * w e + (j : ℝ) / k * w' e
  have hp0 : p 0 = w := by ext e; simp [p]
  have hpk : p k = w' := by ext e; simp [p, ne_of_gt hkr]
  have hn (j : ℕ) (hj : j ≤ k) : Nonnegative (p j) := by
    intro e
    apply add_nonneg (mul_nonneg ?_ (hw e)) (mul_nonneg (by positivity) (hw' e))
    exact sub_nonneg.2 ((div_le_one hkr).2 (by exact_mod_cast hj))
  have hadj (j : ℕ) (_hj : j < k) : Adjacent (p j) (p (j + 1)) := by
    have he (e : Edge n) : p j e - p (j + 1) e = (w e - w' e) / k := by
      dsimp [p]; push_cast; ring
    unfold Adjacent l1
    simp only [Pi.sub_apply, he, abs_div, abs_of_pos hkr, ← Finset.sum_div]
    exact (div_le_one hkr).2 hd
  simpa only [hp0, hpk] using hp.path hδ p k hn hadj s hs

/-- The manuscript's floor choice, including its endpoint and approximate-DP budgets. -/
lemma lower_group_parameters {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hδ : 0 ≤ δ) (hδε : δ ≤ ε / 100) :
    ∃ t : ℕ, 0 < t ∧ 1 / (2 * ε) ≤ (t : ℝ) ∧ (t : ℝ) * ε ≤ 1 ∧
      Real.exp (t * ε) ≤ 3 ∧ δ * (∑ j ∈ Finset.range t, Real.exp (j * ε)) ≤ 3 / 100 := by
  let t := ⌊1 / ε⌋₊
  have hinv : 1 ≤ 1 / ε := (le_div_iff₀ hε).2 (by linarith)
  have ht : 1 ≤ t := (Nat.le_floor_iff (by positivity)).2 (by exact_mod_cast hinv)
  have htf : (t : ℝ) ≤ 1 / ε := Nat.floor_le (by positivity)
  have htf' : 1 / ε < (t : ℝ) + 1 := Nat.lt_floor_add_one _
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hte : (t : ℝ) * ε ≤ 1 := (le_div_iff₀ hε).1 htf
  have hlo : 1 / (2 * ε) ≤ (t : ℝ) := by
    apply (div_le_iff₀ (by positivity)).2
    have hh := (div_lt_iff₀ hε).1 htf'
    nlinarith
  have hexp : Real.exp ((t : ℝ) * ε) ≤ 3 :=
    (Real.exp_le_exp.mpr hte).trans (by linarith [Real.exp_one_lt_d9])
  have hsum : (∑ j ∈ Finset.range t, Real.exp ((j : ℝ) * ε)) ≤ 3 * t := by
    calc
      _ ≤ ∑ _j ∈ Finset.range t, (3 : ℝ) := Finset.sum_le_sum fun j hj =>
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
          (by exact_mod_cast (Finset.mem_range.mp hj).le) hε.le)).trans hexp
      _ = _ := by simp; ring
  refine ⟨t, by omega, hlo, hte, hexp, ?_⟩
  have htd := mul_le_mul_of_nonneg_left hδε (by positivity : (0 : ℝ) ≤ t)
  nlinarith [mul_le_mul_of_nonneg_left hsum hδ]

end DPCut
