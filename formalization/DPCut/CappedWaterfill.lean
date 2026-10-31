import DPCut.CappedSimplex
import Mathlib.Topology.Order.IntermediateValue

/-! The water-filling formula for the capped KL projection in Lemma 29. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators ENNReal
namespace DPCut

def cappedWaterfill {m : ℕ} (cap q : Fin m → ℝ) (c : ℝ) : Fin m → ℝ :=
  fun i => min (cap i) (c * q i)

lemma cappedWaterfill_scalar_exists {m : ℕ} {cap q : Fin m → ℝ}
    (hcap : ∀ i, 0 ≤ cap i) (hmass : 1 ≤ ∑ i, cap i) (hq : ∀ i, 0 < q i) :
    ∃ c : ℝ, 0 < c ∧ ∑ i, cappedWaterfill cap q c i = 1 := by
  let U := ∑ i, cap i / q i
  have hU : 0 ≤ U := Finset.sum_nonneg fun i _ => div_nonneg (hcap i) (hq i).le
  have hUi (i : Fin m) : cap i ≤ U * q i := by
    have hh : cap i / q i ≤ U := Finset.single_le_sum
      (fun j _ => div_nonneg (hcap j) (hq j).le) (Finset.mem_univ i)
    exact (div_le_iff₀ (hq i)).mp hh
  have hzero : ∑ i, cappedWaterfill cap q 0 i = 0 := by
    simp [cappedWaterfill, min_eq_right (hcap _)]
  have htop : ∑ i, cappedWaterfill cap q U i = ∑ i, cap i := by
    apply Finset.sum_congr rfl
    intro i _
    exact min_eq_left (hUi i)
  have hc : Continuous (fun c : ℝ => ∑ i, cappedWaterfill cap q c i) := by
    unfold cappedWaterfill
    fun_prop
  have hval : (1 : ℝ) ∈ Set.Icc (∑ i, cappedWaterfill cap q 0 i) (∑ i, cappedWaterfill cap q U i) := by
    rw [hzero, htop]
    exact ⟨by norm_num, hmass⟩
  obtain ⟨c, hcI, he⟩ := intermediate_value_Icc hU hc.continuousOn hval
  refine ⟨c, lt_of_le_of_ne hcI.1 ?_, he⟩
  intro hz
  simp only [← hz, hzero] at he
  norm_num at he

lemma klSum_three_point {m : ℕ} (z p q : Fin m → ℝ) :
    klSum z q = klSum z p + klSum p q +
      ∑ i, (z i - p i) * (Real.log (p i) - Real.log (q i)) := by
  simp only [klSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem cappedWaterfill_minimizes {m : ℕ} {cap q : Fin m → ℝ} {c : ℝ}
    (hcap : ∀ i, 0 ≤ cap i) (hq : IsDistribution q) (hqpos : ∀ i, 0 < q i)
    (hc : 0 < c) (hmass : ∑ i, cappedWaterfill cap q c i = 1) :
    cappedWaterfill cap q c ∈ cappedSimplex cap ∧
      ∀ z ∈ cappedSimplex cap, finiteKL (cappedWaterfill cap q c) q ≤ finiteKL z q := by
  let p := cappedWaterfill cap q c
  have hp : p ∈ cappedSimplex cap :=
    ⟨⟨fun i => le_min (hcap i) (mul_pos hc (hqpos i)).le, hmass⟩, fun i => min_le_left _ _⟩
  refine ⟨hp, fun z hz => ?_⟩
  have hs (i : Fin m) (hi : 0 < z i) : 0 < p i :=
    lt_min (hi.trans_le (hz.2 i)) (mul_pos hc (hqpos i))
  have hterms (i : Fin m) :
      0 ≤ (z i - p i) * (Real.log (p i) - Real.log (q i) - Real.log c) := by
    by_cases hsat : cap i ≤ c * q i
    · have he : p i = cap i := min_eq_left hsat
      rw [he]
      by_cases hzero : cap i = 0
      · have hz0 : z i = 0 := le_antisymm (by simpa [hzero] using hz.2 i) (hz.1.1 i)
        simp [hzero, hz0]
      · have hpos : 0 < cap i := lt_of_le_of_ne (hcap i) (Ne.symm hzero)
        have hl := Real.log_le_log hpos hsat
        rw [Real.log_mul hc.ne' (hqpos i).ne'] at hl
        exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hz.2 i)) (by linarith)
    · have he : p i = c * q i := min_eq_right (le_of_not_ge hsat)
      rw [he, Real.log_mul hc.ne' (hqpos i).ne']
      ring_nf
      exact le_refl _
  have ht := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hterms i)
  have hcancel : ∑ i, (z i - p i) = 0 := by rw [Finset.sum_sub_distrib, hz.1.2, hp.1.2]; ring
  have hfirst : 0 ≤ ∑ i, (z i - p i) * (Real.log (p i) - Real.log (q i)) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hcancel, zero_mul, sub_zero] at ht
    simpa only [mul_sub, Finset.sum_sub_distrib] using ht
  have hnon := klSum_nonneg hz.1 hp.1 hs
  have he := klSum_three_point z p q
  obtain ⟨hf₁, he₁⟩ := finiteKL_formula hp.1 hq (fun i _ => hqpos i)
  obtain ⟨hf₂, he₂⟩ := finiteKL_formula hz.1 hq (fun i _ => hqpos i)
  apply (ENNReal.toReal_le_toReal hf₁ hf₂).mp
  rw [he₁, he₂]
  linarith

theorem capped_projection_waterfill {m : ℕ} {cap q p : Fin m → ℝ}
    (hcap : ∀ i, 0 ≤ cap i) (hmass : 1 ≤ ∑ i, cap i)
    (hq : IsDistribution q) (hqpos : ∀ i, 0 < q i)
    (hp : p ∈ cappedSimplex cap)
    (hmin : ∀ z ∈ cappedSimplex cap, finiteKL p q ≤ finiteKL z q) :
    ∃ c : ℝ, 0 < c ∧ p = cappedWaterfill cap q c := by
  obtain ⟨c, hc, hm⟩ := cappedWaterfill_scalar_exists hcap hmass hqpos
  obtain ⟨hpc, hmc⟩ := cappedWaterfill_minimizes hcap hq hqpos hc hm
  exact ⟨c, hc, kl_projection_unique (cappedSimplex_closed cap) (cappedSimplex_convex cap)
    (fun _ h => h.1) hq hqpos hp hpc hmin hmc⟩

end DPCut
