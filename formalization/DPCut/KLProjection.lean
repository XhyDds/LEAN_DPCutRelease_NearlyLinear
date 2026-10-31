import DPCut.KLPythagorean

/-! Existence and uniqueness of finite KL projections onto closed convex subsets
of the simplex. No positivity of the optimizer is imposed. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set InformationTheory
open scoped BigOperators ENNReal
namespace DPCut

lemma continuous_klSum_right {m : ℕ} (q : Fin m → ℝ) : Continuous (fun p => klSum p q) := by
  have he : (fun p => klSum p q) =
      fun p : Fin m → ℝ => ∑ i, (p i * Real.log (p i) - p i * Real.log (q i)) := by
    ext p; apply Finset.sum_congr rfl; intro i _; ring
  rw [he]
  apply continuous_finset_sum
  intro i _
  exact (Real.continuous_mul_log.comp (continuous_apply i)).sub
    ((continuous_apply i).mul continuous_const)

lemma IsDistribution.le_one {m : ℕ} {p : Fin m → ℝ} (hp : IsDistribution p) (i : Fin m) :
    p i ≤ 1 := by
  rw [← hp.2]
  exact Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)

lemma distribution_set_compact {m : ℕ} {K : Set (Fin m → ℝ)}
    (hc : IsClosed K) (hd : ∀ p ∈ K, IsDistribution p) : IsCompact K := by
  apply (isCompact_Icc (a := (0 : Fin m → ℝ)) (b := 1)).of_isClosed_subset hc
  intro p hp
  exact ⟨(hd p hp).1, (hd p hp).le_one⟩

lemma finiteKL_eq_zero_iff {m : ℕ} {p q : Fin m → ℝ}
    (hp : IsDistribution p) (hq : IsDistribution q) : finiteKL p q = 0 ↔ p = q := by
  change klDiv (discreteMeasure p) (discreteMeasure q) = 0 ↔ _
  rw [klDiv_eq_zero_iff]
  constructor
  · intro h
    ext i
    have he := congrArg (fun μ : Measure (Fin m) => (μ {i}).toReal) h
    simpa only [discreteMeasure_singleton, ENNReal.toReal_ofReal (hp.1 i),
      ENNReal.toReal_ofReal (hq.1 i)] using he
  · rintro rfl; rfl

theorem kl_projection_exists {m : ℕ} {K : Set (Fin m → ℝ)}
    (hc : IsClosed K) (hne : K.Nonempty) (hd : ∀ p ∈ K, IsDistribution p)
    {q : Fin m → ℝ} (hq : IsDistribution q) (hqpos : ∀ i, 0 < q i) :
    ∃ p ∈ K, ∀ u ∈ K, finiteKL p q ≤ finiteKL u q := by
  obtain ⟨p, hp, hmin⟩ := (distribution_set_compact hc hd).exists_isMinOn hne
    (continuous_klSum_right q).continuousOn
  refine ⟨p, hp, fun u hu => ?_⟩
  obtain ⟨hf₁, he₁⟩ := finiteKL_formula (hd p hp) hq (fun i _ => hqpos i)
  obtain ⟨hf₂, he₂⟩ := finiteKL_formula (hd u hu) hq (fun i _ => hqpos i)
  apply (ENNReal.toReal_le_toReal hf₁ hf₂).mp
  rw [he₁, he₂]
  exact hmin hu

theorem kl_projection_unique {m : ℕ} {K : Set (Fin m → ℝ)}
    (hc : IsClosed K) (hK : Convex ℝ K) (hd : ∀ p ∈ K, IsDistribution p)
    {q p z : Fin m → ℝ} (hq : IsDistribution q) (hqpos : ∀ i, 0 < q i)
    (hp : p ∈ K) (hz : z ∈ K)
    (hminp : ∀ u ∈ K, finiteKL p q ≤ finiteKL u q)
    (hminz : ∀ u ∈ K, finiteKL z q ≤ finiteKL u q) : p = z := by
  have hh := lemma28 m K hc hK hd q p z hq hqpos hp hminp hz
  obtain ⟨hf₁, he₁⟩ := finiteKL_formula (hd z hz) (hd p hp)
    (kl_projection_support hK hd hq hqpos hp hz hminp)
  obtain ⟨hf₂, he₂⟩ := finiteKL_formula (hd p hp) hq (fun i _ => hqpos i)
  obtain ⟨hf₃, he₃⟩ := finiteKL_formula (hd z hz) hq (fun i _ => hqpos i)
  have hreal := ENNReal.toReal_mono hf₃ hh
  rw [ENNReal.toReal_add hf₁ hf₂] at hreal
  have hm := ENNReal.toReal_mono hf₂ (hminz p hp)
  have hzero : (finiteKL z p).toReal = 0 := by
    linarith [ENNReal.toReal_nonneg (a := finiteKL z p)]
  exact ((finiteKL_eq_zero_iff (hd z hz) (hd p hp)).mp
    ((ENNReal.toReal_eq_zero_iff _).mp hzero |>.resolve_right hf₁)).symm

theorem kl_projection_existsUnique {m : ℕ} {K : Set (Fin m → ℝ)}
    (hc : IsClosed K) (hK : Convex ℝ K) (hne : K.Nonempty) (hd : ∀ p ∈ K, IsDistribution p)
    {q : Fin m → ℝ} (hq : IsDistribution q) (hqpos : ∀ i, 0 < q i) :
    ∃! p, p ∈ K ∧ ∀ u ∈ K, finiteKL p q ≤ finiteKL u q := by
  obtain ⟨p, hp, hm⟩ := kl_projection_exists hc hne hd hq hqpos
  exact ⟨p, ⟨hp, hm⟩, fun z hz => kl_projection_unique hc hK hd hq hqpos hz.1 hp hz.2 hm⟩

end DPCut
