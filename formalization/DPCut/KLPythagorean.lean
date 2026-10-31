import DPCut.KLSum

/-! Lemma 28, with support of the optimizer proved rather than assumed. -/
set_option autoImplicit false
noncomputable section
open Filter Set
open scoped BigOperators ENNReal Topology
namespace DPCut

lemma kl_projection_mixture_bound {m : ℕ} {K : Set (Fin m → ℝ)}
    (hK : Convex ℝ K) (hd : ∀ p ∈ K, IsDistribution p)
    {q p z : Fin m → ℝ} (hq : IsDistribution q) (hqpos : ∀ i, 0 < q i)
    (hp : p ∈ K) (hz : z ∈ K)
    (hmin : ∀ u ∈ K, finiteKL p q ≤ finiteKL u q)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    klSum z (fun i => (1 - t) * p i + t * z i) ≤ klSum z q - klSum p q := by
  let r := fun i => (1 - t) * p i + t * z i
  have hrK : r ∈ K := hK hp hz (sub_nonneg.mpr ht1.le) ht.le (by ring)
  have hr := hd r hrK
  have hpr (i : Fin m) (hi : 0 < p i) : 0 < r i :=
    add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr ht1) hi) (mul_nonneg ht.le ((hd z hz).1 i))
  have hmin' := ENNReal.toReal_mono (finiteKL_formula hr hq (fun i _ => hqpos i)).1 (hmin r hrK)
  rw [(finiteKL_formula (hd p hp) hq (fun i _ => hqpos i)).2,
    (finiteKL_formula hr hq (fun i _ => hqpos i)).2] at hmin'
  have hnon := klSum_nonneg (hd p hp) hr hpr
  have he := klSum_mixture p z q t
  change klSum r q = _ at he
  have hh : t * (klSum z r - (klSum z q - klSum p q)) ≤ 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1.le) hnon]
  nlinarith

lemma kl_projection_support {m : ℕ} {K : Set (Fin m → ℝ)}
    (hK : Convex ℝ K) (hd : ∀ p ∈ K, IsDistribution p)
    {q p z : Fin m → ℝ} (hq : IsDistribution q) (hqpos : ∀ i, 0 < q i)
    (hp : p ∈ K) (hz : z ∈ K)
    (hmin : ∀ u ∈ K, finiteKL p q ≤ finiteKL u q) :
    ∀ i, 0 < z i → 0 < p i := by
  intro i hi
  let B := klSum z q - klSum p q
  let c := Real.exp (Real.log (z i) - (B + 1) / z i)
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] 0, c ≤ (1 - t) * p i + t * z i := by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with t ht ht1
    have hr := (hd p hp).mixture (hd z hz) (le_of_lt ht) (le_of_lt ht1)
    have hzpos (j : Fin m) (hj : 0 < z j) : 0 < (1 - t) * p j + t * z j :=
      add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht1.le) ((hd p hp).1 j)) (mul_pos ht hj)
    have hcoord := (klSum_coordinate_bound (hd z hz) hr hzpos i).trans
      (add_le_add_right (kl_projection_mixture_bound hK hd hq hqpos hp hz hmin ht ht1) 1)
    have hlog : Real.log (z i) - (B + 1) / z i ≤
        Real.log ((1 - t) * p i + t * z i) := by
      have hh : Real.log (z i) - Real.log ((1 - t) * p i + t * z i) ≤ (B + 1) / z i :=
        (le_div_iff₀ hi).mpr (by rwa [mul_comm])
      linarith
    exact (Real.le_log_iff_exp_le (hzpos i hi)).mp hlog
  have hlim : Tendsto (fun t : ℝ => (1 - t) * p i + t * z i) (𝓝[>] 0) (𝓝 (p i)) := by
    have hc : ContinuousAt (fun t : ℝ => (1 - t) * p i + t * z i) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  exact lt_of_lt_of_le (Real.exp_pos _) (ge_of_tendsto hlim hbound)

lemma klSum_continuous_mixture {m : ℕ} {p z : Fin m → ℝ}
    (hs : ∀ i, 0 < z i → 0 < p i) (hz : ∀ i, 0 ≤ z i) :
    ContinuousAt (fun t : ℝ => klSum z (fun i => (1 - t) * p i + t * z i)) 0 := by
  unfold klSum
  apply tendsto_finset_sum
  intro i _
  by_cases hi : z i = 0
  · simp only [hi, zero_mul]
    exact continuousAt_const
  · have hp : p i ≠ 0 := (hs i (lt_of_le_of_ne (hz i) (Ne.symm hi))).ne'
    have harg : (1 - (0 : ℝ)) * p i + 0 * z i ≠ 0 := by simpa using hp
    exact continuousAt_const.mul (continuousAt_const.sub
      ((by fun_prop : ContinuousAt (fun t : ℝ => (1 - t) * p i + t * z i) 0).log harg))

theorem kl_pythagorean : KLPythagoreanStatement := by
  intro m K _hclosed hK hd q p z hq hqpos hp hmin hz
  have hs := kl_projection_support hK hd hq hqpos hp hz hmin
  have hlim : Tendsto (fun t : ℝ => klSum z (fun i => (1 - t) * p i + t * z i))
      (𝓝[>] 0) (𝓝 (klSum z p)) := by
    simpa using (klSum_continuous_mixture hs (hd z hz).1).tendsto.mono_left nhdsWithin_le_nhds
  have hb : klSum z p ≤ klSum z q - klSum p q := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with t ht ht1
    exact kl_projection_mixture_bound hK hd hq hqpos hp hz hmin ht ht1
  obtain ⟨h₁, he₁⟩ := finiteKL_formula (hd z hz) (hd p hp) hs
  obtain ⟨h₂, he₂⟩ := finiteKL_formula (hd p hp) hq (fun i _ => hqpos i)
  obtain ⟨h₃, he₃⟩ := finiteKL_formula (hd z hz) hq (fun i _ => hqpos i)
  apply (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨h₁, h₂⟩) h₃).mp
  rw [ENNReal.toReal_add h₁ h₂, he₁, he₂, he₃]
  linarith

theorem lemma28 : KLPythagoreanStatement := kl_pythagorean

lemma kl_projection_distance {m : ℕ} {K : Set (Fin m → ℝ)}
    (hc : IsClosed K) (hK : Convex ℝ K) (hd : ∀ p ∈ K, IsDistribution p)
    {q p z : Fin m → ℝ} (hq : IsDistribution q) (hqpos : ∀ i, 0 < q i)
    (hp : p ∈ K) (hmin : ∀ u ∈ K, finiteKL p q ≤ finiteKL u q) (hz : z ∈ K) :
    finiteKL z p ≤ finiteKL z q :=
  (le_add_right (le_refl _)).trans (lemma28 m K hc hK hd q p z hq hqpos hp hmin hz)

end DPCut
