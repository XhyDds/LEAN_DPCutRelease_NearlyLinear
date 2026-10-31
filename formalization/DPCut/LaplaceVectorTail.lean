import DPCut.LaplaceVector
import DPCut.LaplaceTail
import DPCut.FailureProbability

/-! A simultaneous bound on every coordinate of a finite Laplace vector. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace DPCut

lemma laplace_abs_tail_le {b V : ℝ} (hb : 0 < b) (hV : 0 ≤ V) :
    laplace b {x | ¬ |x| ≤ V} ≤ ENNReal.ofReal (Real.exp (-V / b)) := by
  letI := laplace_isProbabilityMeasure hb
  apply (prob_le_iff_measure_le (Real.exp_pos _).le).mp
  have hs : {x : ℝ | ¬ |x| ≤ V} ⊆ Iic (-V) ∪ Ioi V := by
    intro x hx
    have := not_and_or.mp (mt abs_le.mpr hx)
    rcases this with h | h
    · exact Or.inl (le_of_lt (lt_of_not_ge h))
    · exact Or.inr (lt_of_not_ge h)
  have h := (measureReal_mono (μ := laplace b) hs).trans (measureReal_union_le _ _)
  change prob _ _ ≤ prob _ (Iic (-V)) + prob _ (Ioi V) at h
  rw [laplace_lower_tail hb hV, laplace_upper_tail hb hV] at h
  linarith

lemma laplace_pi_failure {ι : Type*} [Fintype ι] {b V : ℝ}
    (hb : 0 < b) (hV : 0 ≤ V) :
    (Measure.pi (fun _ : ι => laplace b)) {z | ¬ ∀ i, |z i| ≤ V} ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) * Real.exp (-V / b)) := by
  classical
  letI := laplace_isProbabilityMeasure hb
  have he : {z : ι → ℝ | ¬ ∀ i, |z i| ≤ V} = ⋃ i, {z | ¬ |z i| ≤ V} := by
    ext z; simp
  rw [he]
  calc
    _ ≤ ∑ i, (Measure.pi (fun _ : ι => laplace b)) {z | ¬ |z i| ≤ V} :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _ : ι, ENNReal.ofReal (Real.exp (-V / b)) := by
      apply Finset.sum_le_sum
      intro i _
      have hm := (measurePreserving_eval (fun _ : ι => laplace b) i).map_eq
      have hs : MeasurableSet {x : ℝ | ¬ |x| ≤ V} :=
        (measurableSet_le measurable_abs measurable_const).compl
      have ht := laplace_abs_tail_le hb hV
      rw [← hm, Measure.map_apply (measurable_pi_apply i) hs] at ht
      exact ht
    _ = _ := by rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => (Real.exp_pos _).le)]; simp

end DPCut
