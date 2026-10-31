import DPCut.ProbabilityProgramming

/-! Repeated independent attempts, returning the first accepted output. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DPCut
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

def repeatUntil (μ : Measure α) (f : α → Option β) : ℕ → Measure (Option β)
  | 0 => Measure.dirac none
  | t + 1 => μ.bind fun z => (f z).elim (repeatUntil μ f t) (fun y => Measure.dirac (some y))

lemma measurable_repeat_continuation (R : Measure (Option β)) {f : α → Option β} (hf : Measurable f) :
    Measurable (fun z => (f z).elim R (fun y => Measure.dirac (some y))) :=
  (measurable_option_elim R (Measure.measurable_dirac.comp measurable_some)).comp hf

lemma repeatUntil_probability (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → Option β} (hf : Measurable f) (t : ℕ) : IsProbabilityMeasure (repeatUntil μ f t) := by
  induction t with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac none))
  | succ t ih =>
    letI := ih
    letI (z : α) : IsProbabilityMeasure
        ((f z).elim (repeatUntil μ f t) (fun y => Measure.dirac (some y))) := by
      cases f z <;> dsimp <;> infer_instance
    exact probability_bind _ _ (measurable_repeat_continuation _ hf)

lemma option_continuation_private {P Q : Measure (Option β)} {a : ℝ} (ha : 0 ≤ a)
    (h : Indistinguishable P Q a 0) (o : Option β) :
    Indistinguishable (o.elim P (fun y => Measure.dirac (some y)))
      (o.elim Q (fun y => Measure.dirac (some y))) a 0 := by
  cases o with
  | none => exact h
  | some y => exact Indistinguishable.of_eq rfl ha le_rfl

lemma option_continuation_tv {P Q : Measure (Option β)} {δ : ℝ}
    (h : TVClose P Q δ) (o : Option β) :
    TVClose (o.elim P (fun y => Measure.dirac (some y)))
      (o.elim Q (fun y => Measure.dirac (some y))) δ := by
  cases o with
  | none => exact h
  | some y => exact TVClose.refl _ h.nonneg

theorem repeatUntil_private {μ ν : Measure α} {a : ℝ} (ha : 0 ≤ a)
    (h : Indistinguishable μ ν a 0) {f : α → Option β} (hf : Measurable f) (t : ℕ) :
    Indistinguishable (repeatUntil μ f t) (repeatUntil ν f t) (t * a) 0 := by
  induction t with
  | zero => exact Indistinguishable.of_eq rfl (by simp) le_rfl
  | succ t ih =>
    rw [repeatUntil, repeatUntil]
    rw [show ((t + 1 : ℕ) : ℝ) * a = a + t * a by push_cast; ring]
    have hp := h.bind_pure (measurable_repeat_continuation (repeatUntil μ f t) hf)
      (measurable_repeat_continuation (repeatUntil ν f t) hf)
      (fun z => option_continuation_private (mul_nonneg (Nat.cast_nonneg t) ha) ih (f z))
    exact hp

theorem repeatUntil_tv {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {δ : ℝ} (h : TVClose μ ν δ) {f : α → Option β} (hf : Measurable f) (t : ℕ) :
    TVClose (repeatUntil μ f t) (repeatUntil ν f t) (t * δ) := by
  induction t with
  | zero => exact TVClose.refl _ (by simp)
  | succ t ih =>
    rw [repeatUntil, repeatUntil]
    rw [show ((t + 1 : ℕ) : ℝ) * δ = δ + t * δ by push_cast; ring]
    letI := repeatUntil_probability μ hf t
    letI := repeatUntil_probability ν hf t
    letI (z : α) : IsProbabilityMeasure
        ((f z).elim (repeatUntil μ f t) (fun y => Measure.dirac (some y))) := by
      cases f z <;> dsimp <;> infer_instance
    letI (z : α) : IsProbabilityMeasure
        ((f z).elim (repeatUntil ν f t) (fun y => Measure.dirac (some y))) := by
      cases f z <;> dsimp <;> infer_instance
    have hp := h.bind (mul_nonneg (Nat.cast_nonneg t) h.nonneg)
      (measurable_repeat_continuation (repeatUntil μ f t) hf)
      (measurable_repeat_continuation (repeatUntil ν f t) hf)
      (fun z => option_continuation_tv ih (f z))
    exact hp

lemma measurable_repeatUntil {A : Type*} [MeasurableSpace A] [Inhabited β]
    {μ : A → Measure α} (hμ : Measurable μ) [∀ a, IsProbabilityMeasure (μ a)]
    {f : A × α → Option β} (hf : Measurable f) (t : ℕ) :
    Measurable (fun a => repeatUntil (μ a) (fun z => f (a, z)) t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    exact measurable_bind_kernel hμ (measurable_option_continuation ih hf)

lemma option_continuation_ac {P Q : Measure (Option β)} (h : P ≪ Q) (o : Option β) :
    o.elim P (fun y => Measure.dirac (some y)) ≪
      o.elim Q (fun y => Measure.dirac (some y)) := by
  cases o with
  | none => exact h
  | some y => exact Measure.AbsolutelyContinuous.rfl

lemma measurable_repeatUntil_bounded {A : Type*} [MeasurableSpace A] [Inhabited β]
    {μ : A → Measure α} (hμ : Measurable μ) {C : ℝ≥0∞}
    (hC : C < ∞) (hbound : ∀ a, μ a Set.univ ≤ C)
    {f : A × α → Option β} (hf : Measurable f) (t : ℕ) :
    Measurable (fun a => repeatUntil (μ a) (fun z => f (a, z)) t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    exact measurable_bind_kernel_bounded hμ hC hbound (measurable_option_continuation ih hf)

theorem repeatUntil_ac {μ ν : Measure α} (h : μ ≪ ν)
    {f : α → Option β} (hf : Measurable f) (t : ℕ) :
    repeatUntil μ f t ≪ repeatUntil ν f t := by
  induction t with
  | zero => exact Measure.AbsolutelyContinuous.rfl
  | succ t ih =>
    exact bind_ac h (measurable_repeat_continuation _ hf)
      (measurable_repeat_continuation _ hf) (fun z => option_continuation_ac ih (f z))

lemma option_continuation_ae {P : Measure (Option β)} {Q : Option β → Prop}
    (hQ : MeasurableSet {y | Q y}) (h : ∀ᵐ y ∂P, Q y) (o : Option β) (ho : Q o) :
    ∀ᵐ y ∂o.elim P (fun y => Measure.dirac (some y)), Q y := by
  cases o with
  | none => exact h
  | some y => exact (ae_dirac_iff hQ).mpr ho

theorem repeatUntil_ae {μ : Measure α} {f : α → Option β} (hf : Measurable f)
    {Q : Option β → Prop} (hQ : MeasurableSet {y | Q y}) (h0 : Q none)
    (h : ∀ᵐ z ∂μ, Q (f z)) (t : ℕ) : ∀ᵐ y ∂repeatUntil μ f t, Q y := by
  induction t with
  | zero => exact (ae_dirac_iff hQ).mpr h0
  | succ t ih =>
    exact ae_bind_of_ae_ae (measurable_repeat_continuation _ hf) hQ
      (h.mono fun z hz => option_continuation_ae hQ ih (f z) hz)

end DPCut
