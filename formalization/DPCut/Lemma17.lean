import DPCut.AggregateContinuation
import DPCut.PublicOracleCalibration
import DPCut.Statements

/-!
Lemma 17 (`lem:gradient_privacy`). The theorem concerns `aggregateLaw`, with
explicit universal constants in its public configuration. Auxiliary conditioning
and transcripts occur only in the proof.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace DPCut

lemma twice_card_edge_le_square (n : ℕ) : 2 * Fintype.card (Edge n) ≤ n ^ 2 := by
  let f : Bool × Edge n → Fin n × Fin n := fun p => if p.1 then p.2.val.swap else p.2.val
  have hf : Function.Injective f := by
    rintro ⟨b, e⟩ ⟨c, e'⟩ he
    cases b <;> cases c
    · exact Prod.ext rfl (Subtype.ext he)
    · have h0 := congrArg Prod.fst he
      have h1 := congrArg Prod.snd he
      dsimp [f] at h0 h1
      have hi := e.property
      have hj := e'.property
      omega
    · have h0 := congrArg Prod.fst he
      have h1 := congrArg Prod.snd he
      dsimp [f] at h0 h1
      have hi := e.property
      have hj := e'.property
      omega
    · exact congrArg (fun x : Edge n => (true, x)) (Subtype.ext (Prod.swap_injective he))
  simpa [Fintype.card_prod, pow_two] using Fintype.card_le_of_injective f hf

lemma Indistinguishable.mono {A : Type*} [MeasurableSpace A] {μ ν : Measure A}
    {ε δ ε' δ' : ℝ} (h : Indistinguishable μ ν ε δ) (he : ε ≤ ε') (hd : δ ≤ δ') :
    Indistinguishable μ ν ε' δ' := by
  have hε := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr he)
  have hδ := ENNReal.ofReal_le_ofReal hd
  exact ⟨fun s hs => (h.1 s hs).trans (add_le_add (mul_le_mul_right' hε _) hδ),
    fun s hs => (h.2 s hs).trans (add_le_add (mul_le_mul_right' hε _) hδ)⟩

/-- The analytic and adaptive parts of Lemma 17, before the final public calibration. -/
theorem aggregate_privacy_bound {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (ho : OraclePrivacyBounds n o) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1)
    (w w' h : Weights n) (hw : Adjacent w w') {δ : ℝ}
    (hsmall : 10 * o.K * o.eps1 < 1 / 10) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let ε := 320 * o.K * o.eps1 + 40 * o.K * o.eps1 * Real.log (1 / δ)
    Indistinguishable (aggregateLaw o γ w h) (aggregateLaw o γ w' h) ε
      (δ + (1 + Real.exp ε) * (2 * Fintype.card (Edge n)) * (2 * o.K * o.delta1)) := by
  have hp := adaptive_witness_privacy hn o ho (aggregateWitnessSchedule γ w w' h) (w - w') hw
    (aggregateWitnessSchedule_sensitive hγ hγ1 w w' h) (2 * Fintype.card (Edge n))
    hsmall hδ hδ1
  have hm := hp.map measurable_witnessAggregate
  rw [← aggregateLaw_eq_transcript hn o ho γ w w' h false,
    ← aggregateLaw_eq_transcript hn o ho γ w w' h true] at hm
  simpa using hm

theorem aggregate_privacy_calibrated {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (ho : OraclePrivacyBounds n o) {ε δ γ : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hγ : 0 < γ) (hγ1 : γ < 1) (hK : 0 < o.K)
    (heq : o.eps1 = ε / (320 * o.K * (1 + Real.log (2 / δ))))
    (hdq : o.delta1 = δ / (20 * (n : ℝ) ^ 2 * o.K))
    (w w' h : Weights n) (hw : Adjacent w w') :
    Indistinguishable (aggregateLaw o γ w h) (aggregateLaw o γ w' h) ε δ := by
  have hKR : (0 : ℝ) < o.K := by exact_mod_cast hK
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 0 ≤ Real.log (2 / δ) := Real.log_nonneg ((one_le_div hδ).mpr (by linarith))
  have he := ho.eps_pos
  have hd := ho.delta_pos
  have hrel : 320 * o.K * o.eps1 * (1 + Real.log (2 / δ)) = ε := by
    rw [heq]
    field_simp
  have hbase : 320 * o.K * o.eps1 ≤ ε := by
    nlinarith only [hrel, mul_nonneg (show 0 ≤ 320 * o.K * o.eps1 by positivity) hlog]
  have hsmall : 10 * o.K * o.eps1 < 1 / 10 := by nlinarith only [hbase, hε1]
  let E := 320 * o.K * o.eps1 + 40 * o.K * o.eps1 * Real.log (2 / δ)
  have hE : E ≤ ε := by
    dsimp [E]
    nlinarith only [hrel, mul_nonneg (show 0 ≤ o.K * o.eps1 by positivity) hlog]
  have hexp : Real.exp E ≤ 3 := by
    have hh := Real.exp_le_exp.mpr (hE.trans hε1.le)
    linarith [Real.exp_one_lt_d9]
  have hcap : ((2 * Fintype.card (Edge n) : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast twice_card_edge_le_square n
  have hdrel : 20 * (n : ℝ) ^ 2 * o.K * o.delta1 = δ := by
    rw [hdq]
    field_simp
  have herr : ((2 * Fintype.card (Edge n) : ℕ) : ℝ) * (2 * o.K * o.delta1) ≤ δ / 10 := by
    have hh := mul_le_mul_of_nonneg_right hcap (show 0 ≤ 2 * o.K * o.delta1 by positivity)
    nlinarith only [hh, hdrel]
  have hfinal : δ / 2 + (1 + Real.exp E) * (2 * Fintype.card (Edge n)) *
      (2 * o.K * o.delta1) ≤ δ := by
    have hmul := mul_le_mul_of_nonneg_left herr (show 0 ≤ 1 + Real.exp E by positivity)
    have hexp' := mul_le_mul_of_nonneg_right hexp (show 0 ≤ δ / 10 by positivity)
    push_cast at hmul
    nlinarith only [hmul, hexp', hδ]
  have hp := aggregate_privacy_bound hn o ho hγ hγ1 w w' h hw hsmall
    (show 0 < δ / 2 by positivity) (show δ / 2 < 1 by linarith)
  have hediv : 1 / (δ / 2) = 2 / δ := by ring
  dsimp only at hp
  rw [hediv] at hp
  exact hp.mono hE hfinal

/-- Lemma 17, for explicit universal constants. -/
theorem lemma17 : AggregatePrivacyStatement privacyConstants := by
  intro n hn ε δ β γ hε hε1 hδ hδ1 hβ hβ1 hγ hγ1 h _ w w' hw s hs
  have ho := public_oracle_privacy_bounds hn hε hε1 hδ hδ1 hβ hβ1
  have hK : 0 < (oracleConfig n privacyConstants ε δ β).K := by
    change 0 < ⌈8192 * Real.log (n / β)⌉₊
    apply Nat.ceil_pos.mpr
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hh : 0 < Real.log (n / β) := Real.log_pos ((one_lt_div hβ).mpr (by linarith))
    positivity
  exact (aggregate_privacy_calibrated hn _ ho hε hε1 hδ hδ1 hγ hγ1 hK rfl rfl
    w w' h hw.2.2).1 s hs

end DPCut
