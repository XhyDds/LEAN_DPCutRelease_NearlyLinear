import DPCut.FiniteKL
import DPCut.Applications

/-! Finite KL in real coordinates, including the mixture identity. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory InformationTheory
open scoped BigOperators ENNReal
namespace DPCut

def klSum {m : ℕ} (p q : Fin m → ℝ) : ℝ :=
  ∑ i, p i * (Real.log (p i) - Real.log (q i))

lemma finiteKL_formula {m : ℕ} {p q : Fin m → ℝ}
    (hp : IsDistribution p) (hq : IsDistribution q)
    (hs : ∀ i, 0 < p i → 0 < q i) :
    finiteKL p q ≠ ∞ ∧ (finiteKL p q).toReal = klSum p q := by
  obtain ⟨hf, he⟩ := finite_kl_formula hp.1 hq.1 hp.2 hq.2 hs
  refine ⟨hf, he.trans ?_⟩
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : p i = 0
  · simp [hi]
  · rw [Real.log_div hi (hs i (lt_of_le_of_ne (hp.1 i) (Ne.symm hi))).ne']

lemma klSum_nonneg {m : ℕ} {p q : Fin m → ℝ}
    (hp : IsDistribution p) (hq : IsDistribution q)
    (hs : ∀ i, 0 < p i → 0 < q i) : 0 ≤ klSum p q := by
  rw [← (finiteKL_formula hp hq hs).2]
  exact ENNReal.toReal_nonneg

lemma klSum_mixture {m : ℕ} (p z q : Fin m → ℝ) (t : ℝ) :
    let r := fun i => (1 - t) * p i + t * z i
    klSum r q = (1 - t) * klSum p q + t * klSum z q -
      (1 - t) * klSum p r - t * klSum z r := by
  dsimp
  simp only [klSum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma IsDistribution.mixture {m : ℕ} {p z : Fin m → ℝ}
    (hp : IsDistribution p) (hz : IsDistribution z) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    IsDistribution (fun i => (1 - t) * p i + t * z i) := by
  constructor
  · intro i
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) (hp.1 i)) (mul_nonneg ht (hz.1 i))
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hp.2, hz.2]
    ring

lemma weighted_log_lower {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hs : 0 < x → 0 < y) : x - y ≤ x * (Real.log x - Real.log y) := by
  by_cases h : x = 0
  · simp [h, hy]
  · have hx' : 0 < x := lt_of_le_of_ne hx (Ne.symm h)
    have hy' := hs hx'
    have hh := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hy' hx')) hx
    rw [Real.log_div hy'.ne' h] at hh
    have he : x * (y / x - 1) = y - x := by field_simp
    rw [he] at hh
    nlinarith

lemma klSum_coordinate_bound {m : ℕ} {p q : Fin m → ℝ}
    (hp : IsDistribution p) (hq : IsDistribution q)
    (hs : ∀ i, 0 < p i → 0 < q i) (i : Fin m) :
    p i * (Real.log (p i) - Real.log (q i)) ≤ klSum p q + 1 := by
  have hnon (j : Fin m) : 0 ≤ p j * (Real.log (p j) - Real.log (q j)) + q j := by
    have hh := weighted_log_lower (hp.1 j) (hq.1 j) (hs j)
    linarith [hp.1 j]
  have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hnon j) (Finset.mem_univ i)
  simp only [Finset.sum_add_distrib, hq.2] at hh
  change p i * (Real.log (p i) - Real.log (q i)) + q i ≤ klSum p q + 1 at hh
  linarith [hq.1 i]

end DPCut
