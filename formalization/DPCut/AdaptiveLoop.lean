import DPCut.AdaptiveComposition
import DPCut.SequentialContinuation

/-! Finite stateful adaptive programs as postprocessing of their query transcripts. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut

variable {S Y Z : Type*} [MeasurableSpace S] [MeasurableSpace Y] [MeasurableSpace Z]

lemma measurable_foldl_state {u : S × Y → S} (hu : Measurable u) (s : S) :
    Measurable (fun h : List Y => h.foldl (fun s y => u (s, y)) s) := by
  have hn (n : ℕ) : Measurable (fun p : S × (Fin n → Y) =>
      (List.ofFn p.2).foldl (fun s y => u (s, y)) p.1) := by
    induction n with
    | zero => simpa using (measurable_fst : Measurable (Prod.fst : S × (Fin 0 → Y) → S))
    | succ n ih =>
      simp only [List.ofFn_succ, List.foldl_cons]
      exact ih.comp ((hu.comp (measurable_fst.prodMk
        ((measurable_pi_apply 0).comp measurable_snd))).prodMk
        (measurable_pi_lambda _ fun i => (measurable_pi_apply i.succ).comp measurable_snd))
  apply measurable_from_list
  intro n
  exact (hn n).comp (measurable_const.prodMk measurable_id)

def adaptiveLoop (K : Kernel S Y) (u : S × Y → S) (f : S → Z) : ℕ → S → Measure Z
  | 0, s => Measure.dirac (f s)
  | k + 1, s => (K s).bind (fun y => adaptiveLoop K u f k (u (s, y)))

lemma measurable_adaptiveLoop (K : Kernel S Y) [IsMarkovKernel K]
    {u : S × Y → S} (hu : Measurable u) {f : S → Z} (hf : Measurable f) (k : ℕ) :
    Measurable (adaptiveLoop K u f k) := by
  induction k with
  | zero => exact Measure.measurable_dirac.comp hf
  | succ k ih =>
    exact measurable_bind_kernel K.measurable
      (show Measurable (Function.uncurry (fun s y => adaptiveLoop K u f k (u (s, y)))) from ih.comp hu)

lemma adaptiveLoop_probability (K : Kernel S Y) [IsMarkovKernel K]
    {u : S × Y → S} (hu : Measurable u) {f : S → Z} (hf : Measurable f) (k : ℕ) (s : S) :
    IsProbabilityMeasure (adaptiveLoop K u f k s) := by
  induction k generalizing s with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (f s)))
  | succ k ih =>
    letI : ∀ y, IsProbabilityMeasure (adaptiveLoop K u f k (u (s, y))) := fun y => ih _
    exact probability_bind _ _ ((measurable_adaptiveLoop K hu hf k).comp
      (hu.comp measurable_prodMk_left))

def stateSchedule (K : Kernel S Y) (u : S × Y → S) (hu : Measurable u) (s : S) : Sequential Y :=
  fun _ => ⟨fun h => K (h.foldl (fun s y => u (s, y)) s),
    K.measurable.comp (measurable_foldl_state hu s)⟩

instance stateSchedule_markov (K : Kernel S Y) [IsMarkovKernel K]
    (u : S × Y → S) (hu : Measurable u) (s : S) (t : ℕ) :
    IsMarkovKernel (stateSchedule K u hu s t) :=
  ⟨fun h => inferInstanceAs (IsProbabilityMeasure (K (h.foldl (fun s y => u (s, y)) s)))⟩

theorem adaptiveLoop_eq_transcript [Inhabited Y] (K : Kernel S Y) [IsMarkovKernel K]
    {u : S × Y → S} (hu : Measurable u) {f : S → Z} (hf : Measurable f) (k : ℕ) (s : S) :
    adaptiveLoop K u f k s = (sequentialLaw (stateSchedule K u hu s) k).map
      (fun h => f (h.foldl (fun s y => u (s, y)) s)) := by
  have hm : Measurable (fun h : List Y => f (h.foldl (fun s y => u (s, y)) s)) :=
    hf.comp (measurable_foldl_state hu s)
  rw [sequentialLaw_map_continuation _ hm]
  have heq (m t : ℕ) (h : List Y) :
      sequentialContinuation (stateSchedule K u hu s)
        (fun h => f (h.foldl (fun s y => u (s, y)) s)) t m h =
      adaptiveLoop K u f m (h.foldl (fun s y => u (s, y)) s) := by
    induction m generalizing t h with
    | zero => rfl
    | succ m ih =>
      rw [sequentialContinuation, adaptiveLoop]
      apply congrArg ((K (h.foldl (fun s y => u (s, y)) s)).bind)
      funext y
      rw [ih]
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact (heq k 0 []).symm

theorem adaptiveLoop_private [Inhabited Y] [StandardBorelSpace Y]
    (K H : Kernel S Y) [IsMarkovKernel K] [IsMarkovKernel H]
    {u : S × Y → S} (hu : Measurable u) {f : S → Z} (hf : Measurable f)
    (k : ℕ) (s : S) {ε₀ δ₀ δ : ℝ} (hε : 0 < ε₀) (hδ₀ : 0 ≤ δ₀) (hδ₀1 : δ₀ < 1)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hp : ∀ s, Indistinguishable (K s) (H s) ε₀ δ₀) :
    Indistinguishable (adaptiveLoop K u f k s) (adaptiveLoop H u f k s)
      (advancedEpsilon k ε₀ δ) (k * δ₀ + δ) := by
  rw [adaptiveLoop_eq_transcript K hu hf, adaptiveLoop_eq_transcript H hu hf]
  exact (advanced_composition (stateSchedule K u hu s) (stateSchedule H u hu s) k
    hε hδ₀ hδ₀1 hδ hδ1 (fun _ _ h => hp _)).map
      (hf.comp (measurable_foldl_state hu s))

end DPCut
