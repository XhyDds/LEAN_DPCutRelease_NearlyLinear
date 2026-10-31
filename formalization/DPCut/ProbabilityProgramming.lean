import DPCut.ConditioningPrivacy

/-! Measurable finite sampling programs for the concrete oracle in Lemma 17. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DPCut
attribute [local instance] Classical.propDecidable
variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

def optionMeasurableEquiv : Option α ≃ᵐ α ⊕ Unit where
  toEquiv := Equiv.optionEquivSumPUnit α
  measurable_toFun := comap_measurable _
  measurable_invFun := by
    intro s hs
    obtain ⟨s, hs, rfl⟩ := hs
    simpa only [Set.preimage_preimage, Function.comp_def, Equiv.apply_symm_apply,
      Set.preimage_id] using hs

lemma measurable_some : Measurable (some : α → Option α) :=
  optionMeasurableEquiv.symm.measurable.comp measurable_inl

lemma measurable_option_elim (b : β) {f : α → β} (hf : Measurable f) :
    Measurable (fun o : Option α => o.elim b f) := by
  convert (hf.sumElim (measurable_const (a := b))).comp optionMeasurableEquiv.measurable using 1
  funext o
  cases o <;> rfl

lemma measurable_from_option {f : Option α → β}
    (hf : Measurable (fun a => f (some a))) : Measurable f := by
  convert measurable_option_elim (f none) hf using 1
  funext o
  cases o <;> rfl

lemma measurableSet_option_none : MeasurableSet ({none} : Set (Option α)) := by
  have h := optionMeasurableEquiv.measurable (measurableSet_range_inr (α := α) (β := Unit))
  convert h using 1
  ext o
  cases o <;> simp [optionMeasurableEquiv]

lemma measurable_option_getD (a : α) : Measurable (fun o : Option α => o.getD a) := by
  convert measurable_option_elim a measurable_id using 1
  funext o
  cases o <;> rfl

lemma measurableSet_option_elim {P : α → Prop} (hP : MeasurableSet {x | P x}) :
    MeasurableSet {o : Option α | o.elim True P} := by
  have hm : Measurable (fun o : Option α => o.elim (1 : ℝ) (fun x => if P x then 1 else 0)) :=
    measurable_option_elim 1 (Measurable.ite hP measurable_const measurable_const)
  convert hm (measurableSet_singleton (1 : ℝ)) using 1
  ext o
  cases o <;> simp

lemma measurable_option_continuation [Inhabited γ] {R : α → Measure (Option γ)}
    (hR : Measurable R) {f : α × β → Option γ} (hf : Measurable f) :
    Measurable (fun p : α × β => (f p).elim (R p.1) (fun y => Measure.dirac (some y))) := by
  have h : Measurable (fun p : α × β => if f p = none then R p.1
      else Measure.dirac (some ((f p).getD default))) :=
    Measurable.ite (hf measurableSet_option_none) (hR.comp measurable_fst)
      (Measure.measurable_dirac.comp (measurable_some.comp ((measurable_option_getD default).comp hf)))
  convert h using 1
  funext p
  cases ho : f p <;> simp

lemma probability_bind (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → Measure β) (hf : Measurable f) [∀ a, IsProbabilityMeasure (f a)] :
    IsProbabilityMeasure (μ.bind f) := by
  constructor
  rw [Measure.bind_apply MeasurableSet.univ hf.aemeasurable]
  simp only [measure_univ, lintegral_one]

lemma measurable_bind_kernel {μ : α → Measure β} (hμ : Measurable μ)
    [∀ a, IsProbabilityMeasure (μ a)] {f : α → β → Measure γ}
    (hf : Measurable (Function.uncurry f)) : Measurable (fun a => (μ a).bind (f a)) := by
  let K : Kernel α β := ⟨μ, hμ⟩
  letI : IsMarkovKernel K := ⟨fun a => inferInstanceAs (IsProbabilityMeasure (μ a))⟩
  have hfa (a : α) : Measurable (f a) := hf.comp measurable_prodMk_left
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.bind_apply hs (hfa _).aemeasurable]
  exact Measurable.lintegral_kernel_prod_right (κ := K)
    (show Measurable (Function.uncurry (fun a b => f a b s)) from
      (Measure.measurable_coe hs).comp hf)

lemma measurable_bind_kernel_bounded {μ : α → Measure β} (hμ : Measurable μ)
    {C : ℝ≥0∞} (hC : C < ∞) (hbound : ∀ a, μ a Set.univ ≤ C)
    {f : α → β → Measure γ} (hf : Measurable (Function.uncurry f)) :
    Measurable (fun a => (μ a).bind (f a)) := by
  let K : Kernel α β := ⟨μ, hμ⟩
  letI : IsFiniteKernel K := ⟨⟨C, hC, hbound⟩⟩
  have hfa (a : α) : Measurable (f a) := hf.comp measurable_prodMk_left
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.bind_apply hs (hfa _).aemeasurable]
  exact Measurable.lintegral_kernel_prod_right (κ := K)
    (show Measurable (Function.uncurry (fun a b => f a b s)) from
      (Measure.measurable_coe hs).comp hf)

lemma measurable_conditional {μ : α → Measure β} (hμ : Measurable μ)
    [∀ a, IsProbabilityMeasure (μ a)] {G : α → Set β}
    (hG : MeasurableSet {p : α × β | p.2 ∈ G p.1}) :
    Measurable (fun a => (μ a)[|G a]) := by
  let K : Kernel α β := ⟨μ, hμ⟩
  letI : IsMarkovKernel K := ⟨fun a => inferInstanceAs (IsProbabilityMeasure (μ a))⟩
  have hm (s : Set β) (hs : MeasurableSet s) :
      Measurable (fun a => μ a (G a ∩ s)) := by
    have hh : Measurable (fun p : α × β =>
        ({p : α × β | p.2 ∈ G p.1 ∧ p.2 ∈ s}).indicator (fun _ => (1 : ℝ≥0∞)) p) :=
      measurable_const.indicator (hG.inter (measurable_snd hs))
    have hi := Measurable.lintegral_kernel_prod_right (κ := K)
      (show Measurable (Function.uncurry (fun a b =>
        (G a ∩ s).indicator (fun _ => (1 : ℝ≥0∞)) b)) from hh)
    convert hi using 1
    funext a
    have hGa : MeasurableSet (G a) := hG.preimage measurable_prodMk_left
    change μ a (G a ∩ s) = ∫⁻ b, (G a ∩ s).indicator (fun _ => (1 : ℝ≥0∞)) b ∂μ a
    simp [lintegral_indicator (hGa.inter hs)]
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp_rw [cond_apply' hs]
  have hmass : Measurable (fun a => μ a (G a)) := by
    simpa only [Set.inter_univ] using hm Set.univ MeasurableSet.univ
  exact hmass.inv.mul (hm s hs)

lemma measurable_map_kernel {μ : α → Measure β} (hμ : Measurable μ)
    [∀ a, IsProbabilityMeasure (μ a)] {f : α → β → γ}
    (hf : Measurable (Function.uncurry f)) : Measurable (fun a => (μ a).map (f a)) := by
  have hfa (a : α) : Measurable (f a) := hf.comp measurable_prodMk_left
  have he : (fun a => (μ a).map (f a)) =
      (fun a => (μ a).bind (fun b => Measure.dirac (f a b))) :=
    funext fun a => (Measure.bind_dirac_eq_map _ (hfa a)).symm
  rw [he]
  exact measurable_bind_kernel hμ (show Measurable (Function.uncurry
    (fun a b => Measure.dirac (f a b))) from Measure.measurable_dirac.comp hf)

lemma bind_map_eq {μ : Measure α} {f : α → β} (hf : Measurable f)
    {g : β → Measure γ} (hg : Measurable g) :
    (μ.map f).bind g = μ.bind (fun a => g (f a)) := by
  ext s hs
  rw [Measure.bind_apply hs hg.aemeasurable,
    lintegral_map (show Measurable (fun b => g b s) from (Measure.measurable_coe hs).comp hg) hf,
    Measure.bind_apply hs (show Measurable (fun a => g (f a)) from hg.comp hf).aemeasurable]

lemma map_bind_eq {μ : Measure α} {f : α → Measure β} (hf : Measurable f)
    {g : β → γ} (hg : Measurable g) :
    (μ.bind f).map g = μ.bind (fun a => (f a).map g) := by
  ext s hs
  rw [Measure.map_apply hg hs, Measure.bind_apply (hg hs) hf.aemeasurable,
    Measure.bind_apply hs (show Measurable (fun a => (f a).map g) from
      (Measure.measurable_map _ hg).comp hf).aemeasurable]
  simp only [Measure.map_apply hg hs]

lemma bind_prod_eq (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {f : α × β → Measure γ} (hf : Measurable f) :
    (μ.prod ν).bind f = μ.bind (fun a => ν.bind (fun b => f (a, b))) := by
  have hm : Measurable (fun a => ν.bind (fun b => f (a, b))) :=
    measurable_bind_kernel measurable_const (show Measurable (Function.uncurry
      (fun a b => f (a, b))) from hf)
  ext s hs
  rw [Measure.bind_apply hs hf.aemeasurable,
    lintegral_prod _ (show Measurable (fun p => f p s) from
      (Measure.measurable_coe hs).comp hf).aemeasurable,
    Measure.bind_apply hs hm.aemeasurable]
  apply lintegral_congr
  intro a
  rw [Measure.bind_apply hs (show Measurable (fun b => f (a, b)) from
    hf.comp measurable_prodMk_left).aemeasurable]

lemma bind_ac {μ ν : Measure α} (h : μ ≪ ν) {f g : α → Measure β}
    (hf : Measurable f) (hg : Measurable g) (hfg : ∀ x, f x ≪ g x) : μ.bind f ≪ ν.bind g := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hz
  rw [Measure.bind_apply hs hg.aemeasurable] at hz
  rw [Measure.bind_apply hs hf.aemeasurable]
  apply (lintegral_eq_zero_iff (show Measurable (fun x => f x s) from
    (Measure.measurable_coe hs).comp hf)).mpr
  have ha := (lintegral_eq_zero_iff (show Measurable (fun x => g x s) from
    (Measure.measurable_coe hs).comp hg)).mp hz
  have ha' : ∀ᵐ x ∂μ, g x s = 0 := h.ae_le ha
  exact ha'.mono fun x hx => hfg x hx

lemma ae_bind_of_ae_ae {μ : Measure α} {f : α → Measure β} (hf : Measurable f)
    {P : β → Prop} (hP : MeasurableSet {y | P y})
    (h : ∀ᵐ x ∂μ, ∀ᵐ y ∂f x, P y) : ∀ᵐ y ∂μ.bind f, P y := by
  rw [ae_iff]
  change μ.bind f {y | P y}ᶜ = 0
  rw [Measure.bind_apply hP.compl hf.aemeasurable]
  exact (lintegral_eq_zero_iff (show Measurable (fun x => f x {y | P y}ᶜ) from
    (Measure.measurable_coe hP.compl).comp hf)).mpr (h.mono fun _ hx => ae_iff.mp hx)

lemma Indistinguishable.bind_pure {μ ν : Measure α} {a b : ℝ}
    (h : Indistinguishable μ ν a 0) {f g : α → Measure β}
    (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ x, Indistinguishable (f x) (g x) b 0) :
    Indistinguishable (μ.bind f) (ν.bind g) (a + b) 0 := by
  have bound (P Q : Measure α) (F G : α → Measure β)
      (hPQ : P ≤ ENNReal.ofReal (Real.exp a) • Q) (hF : Measurable F) (hG : Measurable G)
      (hFG : ∀ x, F x ≤ ENNReal.ofReal (Real.exp b) • G x)
      (s : Set β) (hs : MeasurableSet s) :
      P.bind F s ≤ ENNReal.ofReal (Real.exp (a + b)) * Q.bind G s := by
    rw [Measure.bind_apply hs hF.aemeasurable, Measure.bind_apply hs hG.aemeasurable]
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp b) * G x s ∂P :=
        lintegral_mono fun x => hFG x s
      _ = ENNReal.ofReal (Real.exp b) * ∫⁻ x, G x s ∂P :=
        lintegral_const_mul _ ((Measure.measurable_coe hs).comp hG)
      _ ≤ ENNReal.ofReal (Real.exp b) * ∫⁻ x, G x s ∂(ENNReal.ofReal (Real.exp a) • Q) :=
        mul_le_mul_left' (lintegral_mono' hPQ le_rfl) _
      _ = _ := by
        rw [lintegral_smul_measure, smul_eq_mul, Real.exp_add,
          ENNReal.ofReal_mul (Real.exp_nonneg _)]
        ring
  exact ⟨fun s hs => by simpa using bound μ ν f g h.le hf hg (fun x => (hfg x).le) s hs,
    fun s hs => by simpa using bound ν μ g f h.symm.le hg hf (fun x => (hfg x).symm.le) s hs⟩

lemma TVClose.bind {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {δ η : ℝ} (h : TVClose μ ν δ) (hη : 0 ≤ η) {f g : α → Measure β}
    (hf : Measurable f) (hg : Measurable g)
    [∀ x, IsProbabilityMeasure (f x)] [∀ x, IsProbabilityMeasure (g x)]
    (hfg : ∀ x, TVClose (f x) (g x) η) : TVClose (μ.bind f) (ν.bind g) (δ + η) := by
  letI := probability_bind μ f hf
  letI := probability_bind ν g hg
  have bound (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
      (F G : α → Measure β) [∀ x, IsProbabilityMeasure (F x)] [∀ x, IsProbabilityMeasure (G x)]
      (hPQ : TVClose P Q δ) (hF : Measurable F) (hG : Measurable G)
      (hFG : ∀ x, TVClose (F x) (G x) η) (s : Set β) (hs : MeasurableSet s) :
      P.bind F s ≤ Q.bind G s + ENNReal.ofReal (δ + η) := by
    rw [Measure.bind_apply hs hF.aemeasurable, Measure.bind_apply hs hG.aemeasurable]
    calc
      _ ≤ ∫⁻ x, G x s + ENNReal.ofReal η ∂P := lintegral_mono fun x => (hFG x).le_apply s hs
      _ = (∫⁻ x, G x s ∂P) + ENNReal.ofReal η := by
        rw [lintegral_add_left (show Measurable (fun x => G x s) from
          (Measure.measurable_coe hs).comp hG)]
        simp
      _ ≤ (∫⁻ x, G x s ∂Q) + ENNReal.ofReal δ + ENNReal.ofReal η :=
        add_le_add_right (hPQ.lintegral_le (fun _ => prob_le_one)) _
      _ = _ := by rw [ENNReal.ofReal_add hPQ.nonneg hη, add_assoc]
  exact TVClose.of_event_bounds (add_nonneg h.nonneg hη)
    (bound μ ν f g h hf hg hfg)
    (bound ν μ g f h.symm hg hf (fun x => (hfg x).symm))

end DPCut
