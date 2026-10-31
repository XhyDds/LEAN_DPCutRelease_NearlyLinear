import DPCut.SubpartComposition
import DPCut.PureAdaptiveComposition
import DPCut.Lemma17

/-! Adaptive composition for symmetric approximate privacy on standard Borel outputs. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DPCut
attribute [local instance] Classical.propDecidable

variable {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Inhabited Y]

theorem approximate_adaptive_composition (K H : Sequential Y)
    [∀ t, IsMarkovKernel (K t)] [∀ t, IsMarkovKernel (H t)]
    (k : ℕ) {ε₀ δ₀ ε δ a : ℝ} (hε₀ : 0 ≤ ε₀) (hδ₀ : 0 ≤ δ₀) (hδ₀1 : δ₀ < 1)
    (hδ : 0 < δ) (ha : 0 < a)
    (hbudget : Real.log (1 / δ) ≤ a * ε - (a + a ^ 2) * k * ε₀ ^ 2 / 2)
    (hp : ∀ t < k, ∀ h, Indistinguishable (K t h) (H t h) ε₀ δ₀) :
    Indistinguishable (sequentialLaw K k) (sequentialLaw H k) ε (k * δ₀ + δ) := by
  let P : Sequential Y := fun t => if t < k then purePartKernel (K t) (H t) ε₀ else K t
  let Q : Sequential Y := fun t => if t < k then purePartKernel (H t) (K t) ε₀ else H t
  have hparts (t : ℕ) (ht : t < k) :=
    purePartKernel_properties (K t) (H t) hε₀ hδ₀ hδ₀1 (hp t ht)
  letI : ∀ t, IsMarkovKernel (P t) := fun t => by
    dsimp [P]
    split_ifs with ht
    · exact (hparts t ht).1
    · infer_instance
  letI : ∀ t, IsMarkovKernel (Q t) := fun t => by
    dsimp [Q]
    split_ifs with ht
    · exact (hparts t ht).2.1
    · infer_instance
  have hpq := pure_adaptive_composition P Q k hε₀ hδ ha hbudget
    (fun t ht h => by simpa only [P, Q, if_pos ht] using ((hparts t ht).2.2 h).1)
  have hdP := sequential_subpart K P k (ENNReal.ofReal (1 - δ₀))
    (fun t ht h => by simpa only [P, if_pos ht] using ((hparts t ht).2.2 h).2.1)
  have hdQ := sequential_subpart H Q k (ENNReal.ofReal (1 - δ₀))
    (fun t ht h => by simpa only [Q, if_pos ht] using ((hparts t ht).2.2 h).2.2)
  have hc : 0 ≤ 1 - δ₀ := by linarith
  rw [← ENNReal.ofReal_pow hc] at hdP hdQ
  have hc1 : (1 - δ₀) ^ k ≤ 1 := pow_le_one₀ hc (by linarith)
  have herr : 1 - (1 - δ₀) ^ k ≤ k * δ₀ := by
    have hh := one_add_mul_le_pow (show (-2 : ℝ) ≤ -δ₀ by linarith) k
    simp only [sub_eq_add_neg] at *
    nlinarith only [hh]
  exact (hpq.subpart_transfer hδ.le (pow_nonneg hc _) hc1 hdP hdQ).mono le_rfl (by linarith)

/-- The usual advanced-composition bound, with adjacency made symmetric by using
`Indistinguishable` for each fixed neighboring pair and common history. -/
theorem advanced_composition (K H : Sequential Y)
    [∀ t, IsMarkovKernel (K t)] [∀ t, IsMarkovKernel (H t)]
    (k : ℕ) {ε₀ δ₀ δ : ℝ} (hε₀ : 0 < ε₀) (hδ₀ : 0 ≤ δ₀) (hδ₀1 : δ₀ < 1)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hp : ∀ t < k, ∀ h, Indistinguishable (K t h) (H t h) ε₀ δ₀) :
    Indistinguishable (sequentialLaw K k) (sequentialLaw H k)
      (advancedEpsilon k ε₀ δ) (k * δ₀ + δ) := by
  by_cases hk : k = 0
  · subst k
    apply Indistinguishable.of_eq rfl
    · simp [advancedEpsilon]
    · positivity
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (Nat.pos_of_ne_zero hk)
  let L := Real.log (1 / δ)
  have hL : 0 < L := Real.log_pos ((one_lt_div hδ).mpr hδ1)
  let s := Real.sqrt (2 * k * L)
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = 2 * k * L := Real.sq_sqrt (by positivity)
  let a := s / (k * ε₀)
  have ha : 0 < a := by dsimp [a]; positivity
  have haeq : a * (k * ε₀) = s := by dsimp [a]; field_simp
  have hquad : a ^ 2 * k * ε₀ ^ 2 / 2 = L := by
    dsimp [a]
    field_simp
    nlinarith only [hs2]
  have hlin : a * (ε₀ * s) = 2 * L := by
    dsimp [a]
    field_simp
    nlinarith only [hs2]
  have hmean : ε₀ ≤ Real.exp ε₀ - 1 := by linarith [Real.add_one_le_exp ε₀]
  apply approximate_adaptive_composition K H k hε₀.le hδ₀ hδ₀1 hδ ha _ hp
  change L ≤ a * (ε₀ * s + k * ε₀ * (Real.exp ε₀ - 1)) -
    (a + a ^ 2) * k * ε₀ ^ 2 / 2
  have hm := mul_le_mul_of_nonneg_left hmean (show 0 ≤ a * k * ε₀ by positivity)
  nlinarith only [hquad, hlin, hm, mul_nonneg (show 0 ≤ a * k by positivity) (sq_nonneg ε₀)]

/-- The full generic statement: symmetric adjacency supplies both directions,
and `δ₀ ≥ 1` is handled by the trivial privacy bound (or an empty transcript). -/
theorem advanced_composition_statement : AdvancedCompositionStatement := by
  classical
  intro X Y _ _ adj P k ε₀ δ₀ δ hsymm hmark hε hδ₀ hδ hδ1 hp
  letI : ∀ x t, IsMarkovKernel (P x t) := hmark
  intro x x' hxx'
  obtain ⟨y, _⟩ := nonempty_of_measure_ne_zero
    (show (P x 0 []) Set.univ ≠ 0 by simp)
  letI : Inhabited Y := ⟨y⟩
  by_cases hsmall : δ₀ < 1
  · exact (advanced_composition (P x) (P x') k hε hδ₀ hsmall hδ hδ1
      (fun t ht h => ⟨hp t ht h x x' hxx', hp t ht h x' x (hsymm hxx')⟩)).1
  by_cases hk : k = 0
  · subst k
    exact (Indistinguishable.of_eq (μ := sequentialLaw (P x) 0)
      (ν := sequentialLaw (P x') 0) rfl (by simp [advancedEpsilon])
      (by simpa using hδ.le)).1
  intro s hs
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have hbound : (1 : ℝ) ≤ k * δ₀ + δ := by nlinarith
  calc
    sequentialLaw (P x) k s ≤ sequentialLaw (P x) k Set.univ :=
      measure_mono (Set.subset_univ s)
    _ = 1 := measure_univ
    _ ≤ ENNReal.ofReal (k * δ₀ + δ) := ENNReal.one_le_ofReal.mpr hbound
    _ ≤ _ := le_add_of_nonneg_left bot_le

end DPCut
