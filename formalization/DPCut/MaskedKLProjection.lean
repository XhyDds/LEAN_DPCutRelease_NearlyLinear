import DPCut.CappedProjectionFormula

/-! Projection on a changing public support, without a dependent-type sampling
space. Zero-cap coordinates receive a positive reference filler; its normalization
constant cancels from the Pythagorean identity. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal
namespace DPCut
attribute [local instance] Classical.propDecidable

def filledReference {m : ℕ} (cap q : Fin m → ℝ) : Fin m → ℝ :=
  fun i => if cap i = 0 then 1 else q i

def normalizedReference {m : ℕ} (cap q : Fin m → ℝ) : Fin m → ℝ :=
  fun i => filledReference cap q i / ∑ j, filledReference cap q j

def maskedCappedProjection {m : ℕ} (cap q : Fin m → ℝ) : Fin m → ℝ :=
  finiteCappedProjection cap (normalizedReference cap q)

lemma filledReference_positive {m : ℕ} {cap q : Fin m → ℝ}
    (hcap : ∀ i, 0 ≤ cap i) (hq : ∀ i, 0 < cap i → 0 < q i) :
    ∀ i, 0 < filledReference cap q i := by
  intro i
  unfold filledReference
  split_ifs with hi
  · norm_num
  · exact hq i (lt_of_le_of_ne (hcap i) (Ne.symm hi))

lemma normalizedReference_distribution {m : ℕ} {cap q : Fin m → ℝ}
    (hcap : ∀ i, 0 ≤ cap i) (hmass : 1 ≤ ∑ i, cap i)
    (hq : ∀ i, 0 < cap i → 0 < q i) :
    IsDistribution (normalizedReference cap q) ∧ (∀ i, 0 < normalizedReference cap q i) ∧
      0 < ∑ i, filledReference cap q i := by
  have hf := filledReference_positive hcap hq
  have hsum : 0 < ∑ i, cap i := by linarith
  obtain ⟨i, hi, _⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hcap i)).mp hsum
  have hZ : 0 < ∑ i, filledReference cap q i :=
    Finset.sum_pos' (fun j _ => (hf j).le) ⟨i, hi, hf i⟩
  refine ⟨⟨fun j => (div_pos (hf j) hZ).le, ?_⟩, fun j => div_pos (hf j) hZ, hZ⟩
  simp only [normalizedReference, ← Finset.sum_div, div_self hZ.ne']

lemma klSum_filledReference {m : ℕ} {cap q z : Fin m → ℝ}
    (hcap : ∀ i, 0 ≤ cap i) (hmass : 1 ≤ ∑ i, cap i)
    (hq : ∀ i, 0 < cap i → 0 < q i) (hz : z ∈ cappedSimplex cap) :
    klSum z (normalizedReference cap q) = klSum z q + Real.log (∑ i, filledReference cap q i) := by
  have hZ := (normalizedReference_distribution hcap hmass hq).2.2
  have he (i : Fin m) : z i * (Real.log (z i) - Real.log (normalizedReference cap q i)) =
      z i * (Real.log (z i) - Real.log (q i)) + z i * Real.log (∑ j, filledReference cap q j) := by
    by_cases hi : cap i = 0
    · have hz0 : z i = 0 := le_antisymm (by simpa [hi] using hz.2 i) (hz.1.1 i)
      simp [hz0]
    · have hqi := hq i (lt_of_le_of_ne (hcap i) (Ne.symm hi))
      have hfi : filledReference cap q i = q i := by simp only [filledReference, if_neg hi]
      change z i * (Real.log (z i) - Real.log (filledReference cap q i / ∑ j, filledReference cap q j)) = _
      rw [hfi, Real.log_div hqi.ne' hZ.ne']
      ring
  unfold klSum
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hz.1.2, one_mul]

theorem maskedCappedProjection_valid {m : ℕ} {cap q : Fin m → ℝ}
    (hcap : ∀ i, 0 ≤ cap i) (hmass : 1 ≤ ∑ i, cap i)
    (hq : ∀ i, 0 < cap i → 0 < q i) :
    maskedCappedProjection cap q ∈ cappedSimplex cap ∧
      (∀ i, 0 < cap i → 0 < maskedCappedProjection cap q i) ∧
      ∀ z ∈ cappedSimplex cap, finiteKL (maskedCappedProjection cap q) (normalizedReference cap q) ≤
        finiteKL z (normalizedReference cap q) := by
  obtain ⟨hr, hrpos, _⟩ := normalizedReference_distribution hcap hmass hq
  obtain ⟨hp, hm⟩ := finiteCappedProjection_minimizes hcap hmass hr hrpos
  refine ⟨hp, ?_, hm⟩
  have hz : (fun i => cap i / ∑ j, cap j) ∈ cappedSimplex cap := by
    simpa only [div_one] using normalized_mask_mem_cappedSimplex hcap (by norm_num : (0 : ℝ) < 1) hmass
  have hs := kl_projection_support (cappedSimplex_convex cap) (fun _ h => h.1) hr hrpos hp hz hm
  intro i hi
  exact hs i (div_pos hi (by linarith : 0 < ∑ j, cap j))

theorem maskedCappedProjection_decreases {m : ℕ} {cap q z : Fin m → ℝ}
    (hcap : ∀ i, 0 ≤ cap i) (hmass : 1 ≤ ∑ i, cap i)
    (hq : IsDistribution q) (hqpos : ∀ i, 0 < cap i → 0 < q i)
    (hz : z ∈ cappedSimplex cap) :
    klSum z (maskedCappedProjection cap q) ≤ klSum z q := by
  let p := maskedCappedProjection cap q
  let r := normalizedReference cap q
  obtain ⟨hr, hrpos, _⟩ := normalizedReference_distribution hcap hmass hqpos
  obtain ⟨hp, hppos, hm⟩ := maskedCappedProjection_valid hcap hmass hqpos
  have hzp (i : Fin m) (hi : 0 < z i) : 0 < p i := hppos i (hi.trans_le (hz.2 i))
  have hpq (i : Fin m) (hi : 0 < p i) : 0 < q i := hqpos i (hi.trans_le (hp.2 i))
  have hpy := lemma28 m (cappedSimplex cap) (cappedSimplex_closed cap) (cappedSimplex_convex cap)
    (fun _ h => h.1) r p z hr hrpos hp hm hz
  obtain ⟨hf₁, he₁⟩ := finiteKL_formula hz.1 hp.1 hzp
  obtain ⟨hf₂, he₂⟩ := finiteKL_formula hp.1 hr (fun i _ => hrpos i)
  obtain ⟨hf₃, he₃⟩ := finiteKL_formula hz.1 hr (fun i _ => hrpos i)
  have hh := ENNReal.toReal_mono hf₃ hpy
  rw [ENNReal.toReal_add hf₁ hf₂, he₁, he₂, he₃] at hh
  have hc₁ := klSum_filledReference hcap hmass hqpos hp
  have hc₂ := klSum_filledReference hcap hmass hqpos hz
  have hnon := klSum_nonneg hp.1 hq hpq
  change klSum z p ≤ klSum z q
  change klSum p r = _ at hc₁
  change klSum z r = _ at hc₂
  linarith

theorem measurable_maskedCappedProjection {m : ℕ} :
    Measurable (fun x : (Fin m → ℝ) × (Fin m → ℝ) => maskedCappedProjection x.1 x.2) := by
  have hf : Measurable (fun x : (Fin m → ℝ) × (Fin m → ℝ) => filledReference x.1 x.2) := by
    apply measurable_pi_lambda
    intro i
    exact Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
      measurable_const ((measurable_pi_apply i).comp measurable_snd)
  have hr : Measurable (fun x : (Fin m → ℝ) × (Fin m → ℝ) => normalizedReference x.1 x.2) := by
    apply measurable_pi_lambda
    intro i
    exact ((measurable_pi_apply i).comp hf).div (by fun_prop)
  exact measurable_finiteCappedProjection.comp (measurable_fst.prodMk hr)

end DPCut
