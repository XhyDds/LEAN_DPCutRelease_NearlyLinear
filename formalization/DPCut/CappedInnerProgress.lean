import DPCut.CappedEstimate
import DPCut.CappedProgress

/-! Rejected inner iterations in the capped mechanism retain the original
potential decrement after projection. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DPCut

def cappedNext {n : ℕ} (c : RunConfig) (a : Weights n) (H : ℝ) (h : Weights n)
    (b : Aggregate n) : Weights n := cappedEstimate a H (innerNext c H h b)

lemma CappedEstimateValid.estimateValid {n : ℕ} {a h : Weights n} {H : ℝ}
    (hh : CappedEstimateValid a H h) : EstimateValid a H h := ⟨hh.1, hh.2.1, hh.2.2.2⟩

lemma innerNext_valid {n : ℕ} (c : RunConfig) {w h : Weights n} {H : ℝ}
    (hh : EstimateValid w H h) (hH : 0 < H) (b : Aggregate n) :
    EstimateValid w H (innerNext c H h b) := by
  unfold innerNext
  split <;> exact hh.update hH _ _

lemma cappedNext_valid {n : ℕ} (c : RunConfig) {a h : Weights n} {H : ℝ}
    (ha : Nonnegative a) (hH : 0 < H) (hcap : H ≤ mass a)
    (hh : CappedEstimateValid a H h) (b : Aggregate n) :
    CappedEstimateValid a H (cappedNext c a H h b) :=
  cappedEstimate_valid ha hH hcap (innerNext_valid c hh.estimateValid hH b).2.2

@[fun_prop] lemma measurable_cappedNext {X : Type*} [MeasurableSpace X] {n : ℕ} (c : RunConfig)
    {a h : X → Weights n} {H : X → ℝ} {b : X → Aggregate n}
    (ha : Measurable a) (hh : Measurable h) (hH : Measurable H) (hb : Measurable b) :
    Measurable (fun x => cappedNext c (a x) (H x) (h x) (b x)) :=
  measurable_cappedEstimate.comp (ha.prodMk (hH.prodMk (measurable_innerNext c hH hh hb)))

theorem cappedNext_progress {n : ℕ} (p : Parameters) (c : RunConfig) {w a h : Weights n}
    {M H B : ℝ} {b : Aggregate n} (hw : Nonnegative w) (ha : Nonnegative a)
    (hM : 0 < M) (hH : 0 < H) (hmw : mass w = M) (hcap : H ≤ mass a)
    (hh : CappedEstimateValid a H h) (hHM : H ≤ M) (hMH : (1 - p.gamma / 50) * M ≤ H)
    (htarget : ∀ e, w e / M ≤ a e / H)
    (hγ : 0 < p.gamma) (hγ1 : p.gamma ≤ 1 / 4) (hη : c.eta = stepSize p.gamma)
    (hb : b.Partition) (hacc : b.Accurate w h p.gamma B) (hreject : ¬b.Accepts h) :
    CappedEstimateValid a H (cappedNext c a H h b) ∧
      p.gamma ^ 2 * M / (64 * (1 + p.gamma) ^ 2) ≤
        potential w h M H - potential w (cappedNext c a H h b) M H := by
  have ha_support (e : Edge n) (he : 0 < w e) : 0 < a e :=
    (div_pos_iff_of_pos_right hH).mp ((div_pos he hM).trans_le (htarget e))
  have hv : EstimateValid w H h := ⟨hh.1, hh.2.1, fun e he => hh.2.2.2 e (ha_support e he)⟩
  have hu := innerNext_valid c hh.estimateValid hH b
  have hproj := (cappedEstimate_potential_le ha hw hu.1 hM hH hmw hu.2.1 hcap hu.2.2 htarget).2
  refine ⟨cappedNext_valid c ha hH hcap hh b, ?_⟩
  have hdec : p.gamma ^ 2 * M / (64 * (1 + p.gamma) ^ 2) ≤
      potential w h M H - potential w (innerNext c H h b) M H := by
    have hsum := hb.pairing_mass h
    rw [hh.2.1] at hsum
    change ¬max (pairing h b.plus) (pairing h b.minus) ≤ pairing h b.residual at hreject
    unfold innerNext
    split_ifs with hover
    · have hdom : H ≤ 3 * pairing h b.plus := by
        rw [max_eq_left hover] at hreject
        linarith
      have hgap := capped_plus_normalized_gap hγ hM hH hHM hdom hacc.1
      rw [← pairing_normalized_difference] at hgap
      rw [hη]
      exact mw_potential_progress n w h b.plus M H p.gamma 1 hw hh.1 hb.1 hM hH
        hmw hh.2.1 hv.2.2 hγ hγ1 (Or.inl rfl) (by simpa using hgap)
    · have hdom : H ≤ 3 * pairing h b.minus := by
        rw [max_eq_right (le_of_not_ge hover)] at hreject
        linarith
      have hgap := capped_minus_normalized_gap hγ hγ1 hM hH hMH hdom hacc.2.1
      have hgap' : p.gamma / (4 * (1 + p.gamma)) ≤
          (-1 : ℝ) * pairing (fun e => h e / H - w e / M) b.minus := by
        rw [pairing_normalized_difference]
        linarith
      rw [hη]
      exact mw_potential_progress n w h b.minus M H p.gamma (-1) hw hh.1 hb.2.1 hM hH
        hmw hh.2.1 hv.2.2 hγ hγ1 (Or.inr rfl) hgap'
  change potential w (cappedNext c a H h b) M H ≤ potential w (innerNext c H h b) M H at hproj
  linarith

lemma initialEstimate_capped_valid {n : ℕ} {a : Weights n} {H : ℝ}
    (ha : Nonnegative a) (hH : 0 < H) (hcap : H ≤ mass a) :
    CappedEstimateValid a H (initialEstimate H a) := by
  have hm : 0 < mass a := hH.trans_le hcap
  refine ⟨fun e => div_nonneg (mul_nonneg hH.le (ha e)) hm.le, ?_, ?_, ?_⟩
  · simp only [mass, initialEstimate, ← Finset.sum_div, ← Finset.mul_sum]
    exact mul_div_cancel_right₀ _ hm.ne'
  · intro e
    apply (div_le_iff₀ hm).mpr
    nlinarith [mul_le_mul_of_nonneg_right hcap (ha e)]
  · intro e he
    exact div_pos (mul_pos hH he) hm

end DPCut
