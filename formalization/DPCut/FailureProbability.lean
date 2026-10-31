import DPCut.RepeatUntil

/-! Elementary failure accounting for finite adaptive sampling programs. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DPCut
attribute [local instance] Classical.propDecidable
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

lemma prob_le_iff_measure_le {μ : Measure α} [IsFiniteMeasure μ] {s : Set α}
    {d : ℝ} (hd : 0 ≤ d) : prob μ s ≤ d ↔ μ s ≤ ENNReal.ofReal d := by
  rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hd]
  rfl

lemma highProbability_of_failure {μ : Measure α} [IsProbabilityMeasure μ]
    {P : α → Prop} (hP : MeasurableSet {x | P x}) {d : ℝ} (hd : 0 ≤ d)
    (h : μ {x | ¬P x} ≤ ENNReal.ofReal d) : HighProbability μ d P := by
  have hb := (prob_le_iff_measure_le hd).mpr h
  have hc := measureReal_add_measureReal_compl (μ := μ) hP
  rw [measureReal_univ_eq_one] at hc
  exact ⟨hP, by change prob μ {x | P x} + prob μ {x | ¬P x} = 1 at hc; linarith⟩

/-- Adaptive union bound; the continuation estimate is needed only on good histories. -/
lemma measure_bind_le_of_good {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → Measure β} (hf : Measurable f) [∀ x, IsProbabilityMeasure (f x)]
    {G : Set α} (hG : MeasurableSet G) {s : Set β} (hs : MeasurableSet s)
    {d e : ℝ} (hd : 0 ≤ d) (he : 0 ≤ e)
    (hbad : μ Gᶜ ≤ ENNReal.ofReal d)
    (hgood : ∀ x ∈ G, f x s ≤ ENNReal.ofReal e) :
    μ.bind f s ≤ ENNReal.ofReal (d + e) := by
  rw [Measure.bind_apply hs hf.aemeasurable]
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal e + Gᶜ.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ G
      · simpa [hx] using hgood x hx
      · simpa [hx] using (prob_le_one (μ := f x) (s := s)).trans
          (le_add_self : (1 : ℝ≥0∞) ≤ ENNReal.ofReal e + 1)
    _ = ENNReal.ofReal e + μ Gᶜ := by
      rw [lintegral_add_left measurable_const, lintegral_indicator hG.compl]
      simp
    _ ≤ ENNReal.ofReal e + ENNReal.ofReal d := add_le_add_left hbad _
    _ = _ := by rw [← ENNReal.ofReal_add he hd, add_comm]

lemma repeatUntil_none {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → Option β} (hf : Measurable f) (t : ℕ) :
    repeatUntil μ f t {none} = (μ {x | f x = none}) ^ t := by
  induction t with
  | zero => simp [repeatUntil, Measure.dirac_apply' _ measurableSet_option_none]
  | succ t ih =>
    rw [repeatUntil, Measure.bind_apply measurableSet_option_none
      (measurable_repeat_continuation _ hf).aemeasurable]
    have he : (fun x => ((f x).elim (repeatUntil μ f t)
        (fun y => Measure.dirac (some y))) {none}) =
        {x | f x = none}.indicator (fun _ => (μ {x | f x = none}) ^ t) := by
      funext x
      cases hx : f x <;> simp [hx, ih, Measure.dirac_apply' _ measurableSet_option_none]
    rw [he, lintegral_indicator (show MeasurableSet {x | f x = none} from hf measurableSet_option_none)]
    simp [pow_succ]

/-- The first accepted output is bad only if some individual attempt was bad. -/
lemma repeatUntil_failure {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → Option β} (hf : Measurable f) {P : Option β → Prop}
    (hP : MeasurableSet {y | P y}) (h0 : P none) {d : ℝ} (hd : 0 ≤ d)
    (hbad : μ {x | ¬P (f x)} ≤ ENNReal.ofReal d) (t : ℕ) :
    repeatUntil μ f t {y | ¬P y} ≤ ENNReal.ofReal (t * d) := by
  have hB : MeasurableSet {y | ¬P y} := hP.compl
  induction t with
  | zero => simp [repeatUntil, Measure.dirac_apply' _ hB, h0]
  | succ t ih =>
    letI := repeatUntil_probability μ hf t
    letI (x : α) : IsProbabilityMeasure
        ((f x).elim (repeatUntil μ f t) (fun y => Measure.dirac (some y))) := by
      cases f x <;> dsimp <;> infer_instance
    have hb := measure_bind_le_of_good (measurable_repeat_continuation (repeatUntil μ f t) hf)
      (show MeasurableSet {x | P (f x)} from hf hP) hB hd (mul_nonneg (Nat.cast_nonneg t) hd) hbad
      (fun x hx => ?_)
    · convert hb using 1
      push_cast
      congr 1
      ring
    · cases hx' : f x with
      | none => exact ih
      | some y =>
        have hy : P (some y) := by simpa [hx'] using hx
        simp [Measure.dirac_apply' _ hB, hy]

end DPCut
