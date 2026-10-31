import DPCut.AdaptiveWitnessPrivacy

/-! Forward transcripts equal backward finite continuations. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut
variable {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z] [Inhabited Y]

def sequentialContinuation (P : Sequential Y) (f : List Y → Z) :
    ℕ → ℕ → List Y → Measure Z
  | _, 0, h => Measure.dirac (f h)
  | t, m + 1, h => (P t h).bind fun y => sequentialContinuation P f (t + 1) m (h ++ [y])

lemma measurable_sequentialContinuation (P : Sequential Y) [∀ t, IsMarkovKernel (P t)]
    {f : List Y → Z} (hf : Measurable f) (t m : ℕ) :
    Measurable (sequentialContinuation P f t m) := by
  induction m generalizing t with
  | zero => exact Measure.measurable_dirac.comp hf
  | succ m ih =>
    exact measurable_bind_kernel (P t).measurable
      (show Measurable (Function.uncurry (fun h y =>
        sequentialContinuation P f (t + 1) m (h ++ [y]))) from
        (ih (t + 1)).comp (measurable_list_append_one default))

lemma sequentialContinuation_probability (P : Sequential Y) [∀ t, IsMarkovKernel (P t)]
    {f : List Y → Z} (hf : Measurable f) (t m : ℕ) (h : List Y) :
    IsProbabilityMeasure (sequentialContinuation P f t m h) := by
  induction m generalizing t h with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (f h)))
  | succ m ih =>
    letI (y : Y) := ih (t + 1) (h ++ [y])
    exact probability_bind _ _ ((measurable_sequentialContinuation P hf (t + 1) m).comp
      ((measurable_list_append_one default).comp measurable_prodMk_left))

theorem sequentialLaw_bind_continuation (P : Sequential Y) [∀ t, IsMarkovKernel (P t)]
    {f : List Y → Z} (hf : Measurable f) (t m : ℕ) :
    (sequentialLaw P t).bind (sequentialContinuation P f t m) =
      (sequentialLaw P (t + m)).map f := by
  induction m generalizing t with
  | zero => simpa [sequentialContinuation] using Measure.bind_dirac_eq_map (sequentialLaw P t) hf
  | succ m ih =>
    have hnext := measurable_sequentialContinuation P hf (t + 1) m
    have hm : Measurable (fun h : List Y => (P t h).map (fun y => h ++ [y])) :=
      measurable_map_kernel (P t).measurable (measurable_list_append_one default)
    have he (h : List Y) :
        (P t h).bind (fun y => sequentialContinuation P f (t + 1) m (h ++ [y])) =
        ((P t h).map (fun y => h ++ [y])).bind (sequentialContinuation P f (t + 1) m) := by
      exact (bind_map_eq ((measurable_list_append_one default).comp measurable_prodMk_left) hnext).symm
    simp only [sequentialContinuation]
    simp_rw [he]
    rw [← Measure.bind_bind hm.aemeasurable hnext.aemeasurable]
    change (sequentialLaw P (t + 1)).bind (sequentialContinuation P f (t + 1) m) = _
    rw [ih]
    congr 2
    omega

theorem sequentialLaw_map_continuation (P : Sequential Y) [∀ t, IsMarkovKernel (P t)]
    {f : List Y → Z} (hf : Measurable f) (m : ℕ) :
    (sequentialLaw P m).map f = sequentialContinuation P f 0 m [] := by
  have h := sequentialLaw_bind_continuation P hf 0 m
  simpa only [sequentialLaw, zero_add,
    Measure.dirac_bind (measurable_sequentialContinuation P hf 0 m)] using h.symm

end DPCut
