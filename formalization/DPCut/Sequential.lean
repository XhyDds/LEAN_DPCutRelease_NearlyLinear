import DPCut.Privacy
import DPCut.SuccessChargedMoment
import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Tactic

/-! Measurable finite transcripts and their sequential laws, for Lemma 16. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace DPCut
attribute [local instance] Classical.propDecidable

variable {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]

private lemma measurable_sigma_mk {ι : Type*} {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] (i : ι) : Measurable (Sigma.mk i : β i → Sigma β) :=
  Measurable.of_le_map (iInf_le _ i)

private lemma measurable_sigma_iff {ι : Type*} {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] {f : Sigma β → Z} :
    Measurable f ↔ ∀ i, Measurable (fun x => f ⟨i, x⟩) := by
  constructor
  · intro h i
    exact h.comp (measurable_sigma_mk i)
  · intro h s hs
    exact MeasurableSpace.measurableSet_iInf.mpr fun i => h i hs

def listMeasurableEquiv : List Y ≃ᵐ (Σ n : ℕ, Fin n → Y) where
  toEquiv := List.equivSigmaTuple
  measurable_toFun := comap_measurable _
  measurable_invFun := by
    intro s hs
    rcases hs with ⟨s, hs, rfl⟩
    simpa only [Set.preimage_preimage, Function.comp_def, Equiv.apply_symm_apply,
      Set.preimage_id] using hs

lemma measurable_list_ofFn (n : ℕ) : Measurable (List.ofFn : (Fin n → Y) → List Y) :=
  listMeasurableEquiv.symm.measurable.comp (measurable_sigma_mk n)

lemma measurable_from_list {f : List Y → Z}
    (hf : ∀ n, Measurable (fun v : Fin n → Y => f (List.ofFn v))) : Measurable f := by
  have h : Measurable (f ∘ listMeasurableEquiv.symm) := measurable_sigma_iff.mpr hf
  simpa only [Function.comp_def, MeasurableEquiv.symm_apply_apply] using
    h.comp listMeasurableEquiv.measurable

@[fun_prop] lemma measurable_list_length : Measurable (List.length : List Y → ℕ) := by
  apply measurable_from_list
  intro n
  simp

@[fun_prop] lemma measurable_list_getD (bottom : Y) (i : ℕ) :
    Measurable (fun h : List Y => h[i]?.getD bottom) := by
  apply measurable_from_list
  intro n
  by_cases hi : i < n
  · simpa [List.getElem?_ofFn, hi] using (measurable_pi_apply (⟨i, hi⟩ : Fin n))
  · simp [hi]

lemma measurable_to_list (bottom : Y) {f : Z → List Y}
    (hl : Measurable (fun x => (f x).length))
    (he : ∀ i : ℕ, Measurable (fun x => (f x)[i]?.getD bottom)) : Measurable f := by
  have hm : Measurable (fun p : Z × ℕ =>
      List.ofFn (fun i : Fin p.2 => (f p.1)[i]?.getD bottom)) :=
    measurable_from_prod_countable_left fun n =>
      (measurable_list_ofFn n).comp (measurable_pi_lambda _ fun i => he i)
  convert hm.comp (measurable_id.prodMk hl) using 1
  funext x
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

@[fun_prop] lemma measurable_list_append_one (bottom : Y) :
    Measurable (fun p : List Y × Y => p.1 ++ [p.2]) := by
  have hlen : Measurable (fun p : List Y × Y => p.1.length) :=
    measurable_list_length.comp measurable_fst
  apply measurable_to_list bottom
  · simpa using hlen.add_const 1
  · intro i
    have hm : Measurable (fun p : List Y × Y =>
        if i < p.1.length then p.1[i]?.getD bottom
        else if i = p.1.length then p.2 else bottom) :=
      Measurable.ite (measurableSet_lt measurable_const (measurable_list_length.comp measurable_fst))
        ((measurable_list_getD bottom i).comp measurable_fst)
        (Measurable.ite (by simpa only [Set.preimage, Set.mem_singleton_iff, eq_comm] using hlen (measurableSet_singleton i))
          measurable_snd measurable_const)
    convert hm using 1
    funext p
    by_cases hi : i < p.1.length
    · simp [List.getElem?_append, hi]
    · by_cases he : i = p.1.length
      · simp [he]
      · have hn : i - p.1.length ≠ 0 := by omega
        simp [List.getElem?_append, hi, he, hn]

@[fun_prop] lemma measurable_list_take (bottom : Y) (n : ℕ) :
    Measurable (List.take n : List Y → List Y) := by
  apply measurable_to_list bottom
  · simpa using measurable_const.min measurable_list_length
  · intro i
    by_cases hi : i < n
    · simpa [List.getElem?_take, hi] using measurable_list_getD bottom i
    · simp [hi]

/-- The kernel that records the next output at the end of the history. -/
def appendKernel (_bottom : Y) (K : Kernel (List Y) Y) : Kernel (List Y) (List Y) :=
  (Kernel.id ×ₖ K).map (fun p => p.1 ++ [p.2])

lemma appendKernel_apply (bottom : Y) (K : Kernel (List Y) Y) [IsMarkovKernel K]
    (h : List Y) : appendKernel bottom K h = (K h).map (fun y => h ++ [y]) := by
  ext s hs
  rw [appendKernel, Kernel.map_apply _ (measurable_list_append_one bottom),
    Measure.map_apply (measurable_list_append_one bottom) hs,
    Kernel.id_prod_apply' _ _ ((measurable_list_append_one bottom) hs),
    Measure.map_apply (show Measurable (fun y : Y => h ++ [y]) from
      (measurable_list_append_one bottom).comp (measurable_const.prodMk measurable_id)) hs]
  rfl

instance (bottom : Y) (K : Kernel (List Y) Y) [IsMarkovKernel K] :
    IsMarkovKernel (appendKernel bottom K) :=
  Kernel.IsMarkovKernel.map _ (measurable_list_append_one bottom)

lemma sequentialLaw_succ (bottom : Y) (P : Sequential Y) (t : ℕ)
    [IsMarkovKernel (P t)] [SFinite (sequentialLaw P t)] :
    sequentialLaw P (t + 1) = (sequentialLaw P t ⊗ₘ P t).map (fun p => p.1 ++ [p.2]) := by
  ext s hs
  have hm : Measurable (fun h => (P t h).map (fun y => h ++ [y])) := by
    simpa only [← appendKernel_apply bottom] using (appendKernel bottom (P t)).measurable
  rw [sequentialLaw, Measure.bind_apply hs hm.aemeasurable,
    Measure.map_apply (measurable_list_append_one bottom) hs, Measure.compProd_apply]
  · apply lintegral_congr
    intro h
    rw [Measure.map_apply (show Measurable (fun y : Y => h ++ [y]) from
      (measurable_list_append_one bottom).comp (measurable_const.prodMk measurable_id)) hs]
    rfl
  · exact (measurable_list_append_one bottom) hs

instance sequentialLaw_probability [Inhabited Y] (P : Sequential Y)
    [∀ t, IsMarkovKernel (P t)] (t : ℕ) : IsProbabilityMeasure (sequentialLaw P t) := by
  induction t with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac []))
  | succ t ih =>
    letI := ih
    rw [sequentialLaw_succ (default : Y)]
    exact Measure.isProbabilityMeasure_map (measurable_list_append_one default).aemeasurable

lemma lintegral_sequentialLaw_succ [Inhabited Y] (P : Sequential Y)
    [∀ t, IsMarkovKernel (P t)] (t : ℕ) {f : List Y → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ h, f h ∂sequentialLaw P (t + 1) =
      ∫⁻ h, ∫⁻ y, f (h ++ [y]) ∂P t h ∂sequentialLaw P t := by
  rw [sequentialLaw_succ (default : Y),
    lintegral_map hf (measurable_list_append_one default)]
  exact Measure.lintegral_compProd (hf.comp (measurable_list_append_one default))

lemma sequentialLaw_length [Inhabited Y] (P : Sequential Y)
    [∀ t, IsMarkovKernel (P t)] (t : ℕ) :
    ∀ᵐ h ∂sequentialLaw P t, h.length = t := by
  induction t with
  | zero =>
    exact (ae_dirac_iff (measurable_list_length (measurableSet_singleton 0))).mpr rfl
  | succ t ih =>
    rw [sequentialLaw_succ (default : Y)]
    apply (ae_map_iff (measurable_list_append_one default).aemeasurable
      (measurable_list_length (measurableSet_singleton (t + 1)))).mpr
    apply Measure.ae_compProd_of_ae_ae
    · exact (measurable_list_length.comp (measurable_list_append_one default))
        (measurableSet_singleton (t + 1))
    · filter_upwards [ih] with h hh
      exact Filter.Eventually.of_forall fun y => by simp [hh]

lemma sequentialLaw_ac_succ [Inhabited Y] (P N : Sequential Y)
    [∀ t, IsMarkovKernel (P t)] [∀ t, IsMarkovKernel (N t)] (t : ℕ)
    (hh : sequentialLaw N t ≪ sequentialLaw P t)
    (hk : ∀ᵐ h ∂sequentialLaw N t, N t h ≪ P t h) :
    sequentialLaw N (t + 1) ≪ sequentialLaw P (t + 1) := by
  rw [sequentialLaw_succ (default : Y), sequentialLaw_succ (default : Y)]
  exact (hh.compProd hk).map (measurable_list_append_one default)

lemma ae_commonPrefix [Inhabited Y] (P₀ P₁ : Sequential Y)
    [∀ t, IsMarkovKernel (P₀ t)] [∀ t, IsMarkovKernel (P₁ t)]
    (t : ℕ) (μ : Measure (List Y))
    (h₀ : μ ≪ sequentialLaw P₀ t) (h₁ : μ ≪ sequentialLaw P₁ t) :
    ∀ᵐ h ∂μ, CommonPrefix P₀ P₁ t h := by
  have hsum₀ : sequentialLaw P₀ t ≪ sequentialLaw P₀ t + sequentialLaw P₁ t :=
    Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hsum₁ : sequentialLaw P₁ t ≪ sequentialLaw P₀ t + sequentialLaw P₁ t :=
    Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  filter_upwards [h₀.ae_le (Measure.rnDeriv_pos hsum₀),
    h₁.ae_le (Measure.rnDeriv_pos hsum₁)] with h h0 h1 using ⟨h0, h1⟩

/-- Sum of a history-dependent contribution along a finite transcript. -/
def transcriptSum (bottom : Y) (f : ℕ → List Y → Y → ℝ) (h : List Y) : ℝ :=
  ∑ i ∈ Finset.range h.length, f i (h.take i) (h[i]?.getD bottom)

@[fun_prop] lemma measurable_transcriptSum (bottom : Y) {f : ℕ → List Y → Y → ℝ}
    (hf : ∀ i, Measurable (Function.uncurry (f i))) :
    Measurable (transcriptSum bottom f) := by
  have hm : Measurable (fun p : List Y × ℕ =>
      ∑ i ∈ Finset.range p.2, f i (p.1.take i) (p.1[i]?.getD bottom)) := by
    apply measurable_from_prod_countable_left
    intro n
    dsimp only
    apply Finset.measurable_sum
    intro i _
    exact (hf i).comp ((measurable_list_take bottom i).prodMk (measurable_list_getD bottom i))
  exact hm.comp (measurable_id.prodMk measurable_list_length)

omit [MeasurableSpace Y] in
lemma transcriptSum_append (bottom : Y) (f : ℕ → List Y → Y → ℝ)
    (h : List Y) (y : Y) :
    transcriptSum bottom f (h ++ [y]) = transcriptSum bottom f h + f h.length h y := by
  simp only [transcriptSum, List.length_append, List.length_singleton, Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < h.length := Finset.mem_range.mp hi
    rw [List.take_append_of_le_length hi'.le, List.getElem?_append_left hi']
  · simp

omit [MeasurableSpace Y] in
lemma successCharge_eq_transcriptSum (bottom : Y) (ell : ℕ → List Y → ℝ) :
    successCharge bottom ell = transcriptSum bottom (fun t h y => stepCharge bottom (ell t h) y) :=
  rfl

@[fun_prop] lemma measurable_successCharge [MeasurableSingletonClass Y]
    (bottom : Y) {ell : ℕ → List Y → ℝ} (hell : ∀ t, Measurable (ell t)) :
    Measurable (successCharge bottom ell) := by
  rw [successCharge_eq_transcriptSum]
  apply measurable_transcriptSum
  intro t
  exact Measurable.ite (measurable_snd (measurableSet_singleton bottom))
    measurable_const ((hell t).comp measurable_fst)

omit [MeasurableSpace Y] in
lemma successCharge_append (bottom : Y) (ell : ℕ → List Y → ℝ) (h : List Y) (y : Y) :
    successCharge bottom ell (h ++ [y]) =
      successCharge bottom ell h + stepCharge bottom (ell h.length h) y :=
  transcriptSum_append bottom (fun t h y => stepCharge bottom (ell t h) y) h y

end DPCut
