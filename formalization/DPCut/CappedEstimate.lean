import DPCut.MaskedKLProjection
import DPCut.EdgeVector
import DPCut.MultiplicativeWeights

/-! Measurable capped candidate updates and their KL potential contraction. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DPCut

def cappedEstimate {n : ℕ} (a : Weights n) (H : ℝ) (h : Weights n) : Weights n :=
  fun e => H * vectorEdges (maskedCappedProjection (weightsVector (fun e => a e / H))
    (weightsVector (fun e => h e / H))) e

def CappedEstimateValid {n : ℕ} (a : Weights n) (H : ℝ) (h : Weights n) : Prop :=
  Nonnegative h ∧ mass h = H ∧ (∀ e, h e ≤ a e) ∧ (∀ e, 0 < a e → 0 < h e)

lemma cap_normalized_mass {n : ℕ} {a : Weights n} {H : ℝ} (hH : 0 < H) (ha : H ≤ mass a) :
    1 ≤ ∑ i, weightsVector (fun e => a e / H) i := by
  rw [sum_weightsVector]
  change 1 ≤ ∑ e, a e / H
  rw [← Finset.sum_div]
  exact (le_div_iff₀ hH).mpr (by simpa using ha)

theorem cappedEstimate_valid {n : ℕ} {a h : Weights n} {H : ℝ}
    (ha : Nonnegative a) (hH : 0 < H) (hcap : H ≤ mass a)
    (hs : ∀ e, 0 < a e → 0 < h e) : CappedEstimateValid a H (cappedEstimate a H h) := by
  let cap := weightsVector (fun e => a e / H)
  let q := weightsVector (fun e => h e / H)
  let p := maskedCappedProjection cap q
  have hc : ∀ i, 0 ≤ cap i := fun i => div_nonneg (ha _) hH.le
  have hm : 1 ≤ ∑ i, cap i := cap_normalized_mass hH hcap
  have hq (i : Fin (Fintype.card (Edge n))) (hi : 0 < cap i) : 0 < q i := by
    exact div_pos (hs _ ((div_pos_iff_of_pos_right hH).mp hi)) hH
  obtain ⟨hp, hppos, _⟩ := maskedCappedProjection_valid hc hm hq
  refine ⟨fun e => mul_nonneg hH.le (hp.1.1 _), ?_, ?_, ?_⟩
  · change (∑ e, H * vectorEdges p e) = H
    rw [← Finset.mul_sum]
    change H * mass (vectorEdges p) = H
    rw [mass_vectorEdges, hp.1.2, mul_one]
  · intro e
    have hb := hp.2 (Fintype.equivFin (Edge n) e)
    change p (Fintype.equivFin (Edge n) e) ≤ a ((Fintype.equivFin (Edge n)).symm
      (Fintype.equivFin (Edge n) e)) / H at hb
    rw [Equiv.symm_apply_apply] at hb
    have he := (le_div_iff₀ hH).mp hb
    change H * p (Fintype.equivFin (Edge n) e) ≤ a e
    nlinarith
  · intro e he
    apply mul_pos hH
    apply hppos
    simpa only [cap, weightsVector, Equiv.symm_apply_apply] using div_pos he hH

lemma cappedEstimate_normalized {n : ℕ} (a h : Weights n) {H : ℝ} (hH : H ≠ 0) :
    weightsVector (fun e => cappedEstimate a H h e / H) =
      maskedCappedProjection (weightsVector (fun e => a e / H)) (weightsVector (fun e => h e / H)) := by
  ext i
  simp [weightsVector, cappedEstimate, vectorEdges, hH]

theorem cappedEstimate_potential_le {n : ℕ} {w a h : Weights n} {M H : ℝ}
    (ha : Nonnegative a) (hw : Nonnegative w) (hh : Nonnegative h)
    (hM : 0 < M) (hH : 0 < H) (hmw : mass w = M) (hmh : mass h = H)
    (hcap : H ≤ mass a) (hs : ∀ e, 0 < a e → 0 < h e)
    (htarget : ∀ e, w e / M ≤ a e / H) :
    EstimateValid w H (cappedEstimate a H h) ∧
      potential w (cappedEstimate a H h) M H ≤ potential w h M H := by
  have ha_support (e : Edge n) (he : 0 < w e) : 0 < a e := by
    exact (div_pos_iff_of_pos_right hH).mp ((div_pos he hM).trans_le (htarget e))
  obtain ⟨hpn, hpm, hpc, hps⟩ := cappedEstimate_valid ha hH hcap hs
  have hsupport := fun e he => hps e (ha_support e he)
  refine ⟨⟨hpn, hpm, hsupport⟩, ?_⟩
  rw [potential_eq_vector_klSum hw hpn hM hH hmw hpm hsupport,
    potential_eq_vector_klSum hw hh hM hH hmw hmh (fun e he => hs e (ha_support e he)),
    cappedEstimate_normalized a h hH.ne']
  apply mul_le_mul_of_nonneg_left _ hM.le
  apply maskedCappedProjection_decreases
    (fun i => div_nonneg (ha _) hH.le) (cap_normalized_mass hH hcap)
    (weightsVector_distribution hh hH hmh)
  · intro i hi
    exact div_pos (hs _ ((div_pos_iff_of_pos_right hH).mp hi)) hH
  · exact ⟨weightsVector_distribution hw hM hmw, fun i => htarget _⟩

theorem measurable_cappedEstimate {n : ℕ} :
    Measurable (fun x : Weights n × ℝ × Weights n => cappedEstimate x.1 x.2.1 x.2.2) := by
  have hc : Measurable (fun x : Weights n × ℝ × Weights n => weightsVector (fun e => x.1 e / x.2.1)) := by
    apply measurable_weightsVector.comp
    fun_prop
  have hq : Measurable (fun x : Weights n × ℝ × Weights n => weightsVector (fun e => x.2.2 e / x.2.1)) := by
    apply measurable_weightsVector.comp
    fun_prop
  have hp := measurable_vectorEdges.comp (measurable_maskedCappedProjection.comp (hc.prodMk hq))
  apply measurable_pi_lambda
  intro e
  exact (measurable_fst.comp measurable_snd).mul ((measurable_pi_apply e).comp hp)

end DPCut
