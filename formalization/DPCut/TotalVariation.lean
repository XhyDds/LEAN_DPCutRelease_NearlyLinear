import DPCut.Sequential
import DPCut.KernelLikelihood
import Mathlib.MeasureTheory.Measure.Sub

/-! Eventwise total variation: bounded tests, adaptive accumulation, and privacy transfer. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DPCut

variable {α Y : Type*} [MeasurableSpace α] [MeasurableSpace Y]

lemma TVClose.nonneg {μ ν : Measure α} {δ : ℝ} (h : TVClose μ ν δ) : 0 ≤ δ := by
  simpa [prob] using h ∅ MeasurableSet.empty

lemma TVClose.symm {μ ν : Measure α} {δ : ℝ} (h : TVClose μ ν δ) : TVClose ν μ δ := by
  intro s hs
  simpa only [abs_sub_comm] using h s hs

lemma TVClose.refl (μ : Measure α) {δ : ℝ} (hδ : 0 ≤ δ) : TVClose μ μ δ := by
  intro s _
  simpa using hδ

lemma TVClose.le_apply {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {δ : ℝ} (h : TVClose μ ν δ) (s : Set α) (hs : MeasurableSet s) :
    μ s ≤ ν s + ENNReal.ofReal δ := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩)).mp
  rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal h.nonneg]
  exact (sub_le_iff_le_add.mp ((abs_le.mp (h s hs)).2)).trans_eq (add_comm _ _)

lemma TVClose.of_event_bounds {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {δ : ℝ} (hδ : 0 ≤ δ)
    (h₀ : ∀ s, MeasurableSet s → μ s ≤ ν s + ENNReal.ofReal δ)
    (h₁ : ∀ s, MeasurableSet s → ν s ≤ μ s + ENNReal.ofReal δ) : TVClose μ ν δ := by
  intro s hs
  have h0 := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩) (h₀ s hs)
  have h1 := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩) (h₁ s hs)
  simp only [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hδ] at h0 h1
  unfold prob
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma TVClose.triangle {μ ν ρ : Measure α} {δ η : ℝ}
    (h : TVClose μ ν δ) (h' : TVClose ν ρ η) : TVClose μ ρ (δ + η) := by
  intro s hs
  exact (abs_sub_le (prob μ s) (prob ν s) (prob ρ s)).trans (add_le_add (h s hs) (h' s hs))

lemma TVClose.map {μ ν : Measure α} {δ : ℝ} (h : TVClose μ ν δ)
    {f : α → Y} (hf : Measurable f) : TVClose (μ.map f) (ν.map f) δ := by
  intro s hs
  simpa only [prob, Measure.map_apply hf hs] using h (f ⁻¹' s) (hf hs)

/-- Hahn decomposition turns an eventwise bound into a small residual measure. -/
lemma TVClose.exists_residual {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {δ : ℝ} (h : TVClose μ ν δ) :
    ∃ ρ : Measure α, μ ≤ ν + ρ ∧ ρ Set.univ ≤ ENNReal.ofReal δ := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition ν μ
  let ρ := μ.restrict s - ν.restrict s
  have hcancel : ρ + ν.restrict s = μ.restrict s := Measure.sub_add_cancel_of_le hs.le_on
  refine ⟨ρ, ?_, ?_⟩
  · calc
      μ = μ.restrict s + μ.restrict sᶜ := (Measure.restrict_add_restrict_compl hs.measurableSet).symm
      _ ≤ μ.restrict s + ν.restrict sᶜ := add_le_add_left hs.ge_on_compl _
      _ = ν + ρ := by
        rw [← hcancel, add_assoc, Measure.restrict_add_restrict_compl hs.measurableSet, add_comm]
  · change (μ.restrict s - ν.restrict s) Set.univ ≤ _
    rw [Measure.sub_apply MeasurableSet.univ hs.le_on]
    simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact tsub_le_iff_right.mpr (by simpa only [add_comm] using h.le_apply s hs.measurableSet)

lemma TVClose.lintegral_le {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {δ : ℝ} (h : TVClose μ ν δ) {f : α → ℝ≥0∞} (hf : ∀ x, f x ≤ 1) :
    ∫⁻ x, f x ∂μ ≤ (∫⁻ x, f x ∂ν) + ENNReal.ofReal δ := by
  obtain ⟨ρ, hρ, hm⟩ := h.exists_residual
  calc
    _ ≤ ∫⁻ x, f x ∂(ν + ρ) := lintegral_mono' hρ le_rfl
    _ = (∫⁻ x, f x ∂ν) + ∫⁻ x, f x ∂ρ := lintegral_add_measure _ _ _
    _ ≤ _ := add_le_add_left ((lintegral_mono hf).trans (by simpa using hm)) _

lemma TVClose.compProd_same_kernel {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {δ : ℝ} (h : TVClose μ ν δ)
    (K : Kernel α Y) [IsMarkovKernel K] : TVClose (μ ⊗ₘ K) (ν ⊗ₘ K) δ := by
  apply TVClose.of_event_bounds h.nonneg
  · intro s hs
    simp only [Measure.compProd_apply hs]
    exact h.lintegral_le (fun _ => prob_le_one)
  · intro s hs
    simp only [Measure.compProd_apply hs]
    exact h.symm.lintegral_le (fun _ => prob_le_one)

lemma TVClose.compProd_same_measure (μ : Measure α) [IsProbabilityMeasure μ]
    (K H : Kernel α Y) [IsMarkovKernel K] [IsMarkovKernel H] {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ᵐ x ∂μ, TVClose (K x) (H x) δ) : TVClose (μ ⊗ₘ K) (μ ⊗ₘ H) δ := by
  have hbound (A B : Kernel α Y) [IsMarkovKernel A] [IsMarkovKernel B]
      (hab : ∀ᵐ x ∂μ, TVClose (A x) (B x) δ) (s : Set (α × Y)) (hs : MeasurableSet s) :
      (μ ⊗ₘ A) s ≤ (μ ⊗ₘ B) s + ENNReal.ofReal δ := by
    rw [Measure.compProd_apply hs, Measure.compProd_apply hs]
    calc
      _ ≤ ∫⁻ x, (B x (Prod.mk x ⁻¹' s) + ENNReal.ofReal δ) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hab] with x hx
        exact hx.le_apply _ (measurable_prodMk_left hs)
      _ = _ := by
        rw [lintegral_add_left (Kernel.measurable_kernel_prodMk_left hs)]
        simp
  apply TVClose.of_event_bounds hδ (hbound K H h)
  exact hbound H K (h.mono fun _ hx => hx.symm)

lemma TVClose.compProd {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {δ η : ℝ} (h : TVClose μ ν δ) (hη : 0 ≤ η)
    (K H : Kernel α Y) [IsMarkovKernel K] [IsMarkovKernel H]
    (hk : ∀ᵐ x ∂ν, TVClose (K x) (H x) η) :
    TVClose (μ ⊗ₘ K) (ν ⊗ₘ H) (δ + η) :=
  (h.compProd_same_kernel K).triangle (TVClose.compProd_same_measure ν K H hη hk)

lemma sequential_tv [Inhabited Y] (P N : Sequential Y)
    [∀ t, IsMarkovKernel (P t)] [∀ t, IsMarkovKernel (N t)] (k : ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hs : ∀ t < k, ∀ᵐ h ∂sequentialLaw N t, TVClose (P t h) (N t h) δ) :
    TVClose (sequentialLaw P k) (sequentialLaw N k) (k * δ) := by
  induction k with
  | zero => simpa [sequentialLaw] using TVClose.refl (Measure.dirac ([] : List Y)) (le_refl (0 : ℝ))
  | succ k ih =>
    rw [sequentialLaw_succ (default : Y), sequentialLaw_succ (default : Y)]
    convert ((ih (fun t ht => hs t (by omega))).compProd hδ (P k) (N k)
      (hs k (by omega))).map (measurable_list_append_one default) using 1
    push_cast
    ring

lemma privacy_event_iff_real (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (s : Set α) (ε : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (μ s ≤ ENNReal.ofReal (Real.exp ε) * ν s + ENNReal.ofReal δ) ↔
      prob μ s ≤ Real.exp ε * prob ν s + δ := by
  rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_ne_top _ _), ENNReal.ofReal_ne_top⟩),
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_nonneg _), ENNReal.toReal_ofReal hδ]
  rfl

lemma Indistinguishable.of_eq {μ ν : Measure α} (h : μ = ν) {ε δ : ℝ}
    (hε : 0 ≤ ε) (_hδ : 0 ≤ δ) : Indistinguishable μ ν ε δ := by
  subst ν
  have he : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp ε) :=
    ENNReal.one_le_ofReal.mpr (Real.one_le_exp hε)
  have hb (s : Set α) : μ s ≤ ENNReal.ofReal (Real.exp ε) * μ s + ENNReal.ofReal δ := by
    calc
      μ s = 1 * μ s := (one_mul _).symm
      _ ≤ ENNReal.ofReal (Real.exp ε) * μ s := mul_le_mul_right' he _
      _ ≤ _ := le_add_right le_rfl
  exact ⟨fun s _ => hb s, fun s _ => hb s⟩

/-- The two TV errors have costs `rho` and `exp epsilon * rho`. -/
lemma Indistinguishable.tv_transfer {P₀ P₁ N₀ N₁ : Measure α}
    [IsFiniteMeasure P₀] [IsFiniteMeasure P₁] [IsFiniteMeasure N₀] [IsFiniteMeasure N₁]
    {ε δ ρ : ℝ} (hδ : 0 ≤ δ) (hp : Indistinguishable N₀ N₁ ε δ)
    (h₀ : TVClose P₀ N₀ ρ) (h₁ : TVClose P₁ N₁ ρ) :
    Indistinguishable P₀ P₁ ε (δ + (1 + Real.exp ε) * ρ) := by
  have hρ := h₀.nonneg
  have hd : 0 ≤ δ + (1 + Real.exp ε) * ρ := by positivity
  have hb (P Q N M : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q]
      [IsFiniteMeasure N] [IsFiniteMeasure M]
      (hPN : TVClose P N ρ) (hQM : TVClose Q M ρ)
      (hNM : ∀ s, MeasurableSet s → N s ≤ ENNReal.ofReal (Real.exp ε) * M s + ENNReal.ofReal δ)
      (s : Set α) (hs : MeasurableSet s) :
      P s ≤ ENNReal.ofReal (Real.exp ε) * Q s + ENNReal.ofReal (δ + (1 + Real.exp ε) * ρ) := by
    apply (privacy_event_iff_real P Q s ε hd).mpr
    have hpn := (abs_le.mp (hPN s hs)).2
    have hqm := (abs_le.mp (hQM s hs)).1
    have hnm := (privacy_event_iff_real N M s ε hδ).mp (hNM s hs)
    have hm := mul_le_mul_of_nonneg_left
      (show prob M s ≤ prob Q s + ρ by linarith) (Real.exp_nonneg ε)
    nlinarith
  exact ⟨hb P₀ P₁ N₀ N₁ h₀ h₁ hp.1, hb P₁ P₀ N₁ N₀ h₁ h₀ hp.2⟩

end DPCut
