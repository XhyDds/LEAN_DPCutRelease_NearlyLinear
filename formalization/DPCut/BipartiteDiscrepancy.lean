import DPCut.CubeMoments

/-! The rectangular discrepancy estimate needed for Theorem 38's hard family. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DPCut

lemma sum_abs_le_of_subset_sum {ι : Type*} [Fintype ι] (u : ι → ℝ) {C : ℝ}
    (h : ∀ S : Finset ι, |∑ i ∈ S, u i| ≤ C) : (∑ i, |u i|) ≤ 2 * C := by
  classical
  have hp := (abs_le.mp (h (Finset.univ.filter (fun i => 0 ≤ u i)))).2
  have hn := (abs_le.mp (h (Finset.univ.filter (fun i => ¬0 ≤ u i)))).1
  have he : (∑ i, |u i|) = (∑ i ∈ Finset.univ.filter (fun i => 0 ≤ u i), u i) -
      (∑ i ∈ Finset.univ.filter (fun i => ¬0 ≤ u i), u i) := by
    simp only [Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 ≤ u i <;> simp [hi, abs_of_nonneg, abs_of_neg (lt_of_not_ge hi)]
  linarith

lemma abs_signSum_le {d : ℕ} (a : Fin d → ℝ) (x : Fin d → Bool) {C : ℝ}
    (h : ∀ T : Finset (Fin d), |∑ j ∈ T, a j| ≤ C) : |signSum a x| ≤ 2 * C := by
  classical
  have hp := h (Finset.univ.filter (fun j => x j = true))
  have hn := h (Finset.univ.filter (fun j => x j = false))
  have he : signSum a x = (∑ j ∈ Finset.univ.filter (fun j => x j = true), a j) -
      (∑ j ∈ Finset.univ.filter (fun j => x j = false), a j) := by
    simp only [signSum, Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _; cases x j <;> simp [boolSign]
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

/-- No minimum-degree assumption is needed: only bounded row energy and a bound
on every rectangle. This suffices for the complete bipartite bit family. -/
theorem bipartite_discrepancy {ι : Type*} [Fintype ι] {d : ℕ} (hd : 0 < d)
    (B : ι → Fin d → ℝ) (hB : ∀ i j, B i j ^ 2 ≤ 1) {R : ℝ}
    (hrect : ∀ (S : Finset ι) (T : Finset (Fin d)), |∑ i ∈ S, ∑ j ∈ T, B i j| ≤ R) :
    (∑ i, ∑ j, B i j ^ 2) ≤ 64 * Real.sqrt d * R := by
  classical
  have hs (x : Fin d → Bool) : (∑ i, |signSum (B i) x|) ≤ 4 * R := by
    have hsub (S : Finset ι) : |∑ i ∈ S, signSum (B i) x| ≤ 2 * R := by
      have he : (∑ i ∈ S, signSum (B i) x) = signSum (fun j => ∑ i ∈ S, B i j) x := by
        simp only [signSum, Finset.sum_mul]
        exact Finset.sum_comm
      rw [he]
      apply abs_signSum_le
      intro T
      rw [Finset.sum_comm]
      exact hrect S T
    have hh := sum_abs_le_of_subset_sum (fun i => signSum (B i) x) hsub
    linarith
  have hm (i : ι) : (∑ j, B i j ^ 2) ≤ 16 * Real.sqrt d * (𝔼 x, |signSum (B i) x|) := by
    apply signSum_abs_lower _ (by exact_mod_cast hd)
    calc
      _ ≤ ∑ _j : Fin d, (1 : ℝ) := Finset.sum_le_sum fun j _ => hB i j
      _ = _ := by simp
  have hl := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hm i)
  rw [← Finset.mul_sum, ← Finset.expect_sum_comm] at hl
  have hu := Finset.expect_le Finset.univ_nonempty (fun x _ => hs x)
  have hh := mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 16 * Real.sqrt (d : ℝ))
  nlinarith

end DPCut
