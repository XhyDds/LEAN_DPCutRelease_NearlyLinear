import DPCut.SubpartComposition
import DPCut.Lemma17

/-! Basic adaptive composition for probability-valued measurable programs. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DPCut

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma bind_subpart {μ ν : Measure X} {f g : X → Measure Y} {a b : ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hμ : a • μ ≤ ν)
    (hfsub : ∀ x, b • f x ≤ g x) : (a * b) • μ.bind f ≤ ν.bind g := by
  apply Measure.le_iff.mpr
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul, Measure.bind_apply hs hf.aemeasurable,
    Measure.bind_apply hs hg.aemeasurable]
  calc
    _ = ∫⁻ x, b * f x s ∂a • μ := by
      rw [lintegral_smul_measure, lintegral_const_mul b
        (show Measurable (fun x => f x s) from (Measure.measurable_coe hs).comp hf)]
      simp [smul_eq_mul, mul_assoc]
    _ ≤ _ := lintegral_mono' hμ (fun x => hfsub x s)

lemma Indistinguishable.of_delta_ge_one {μ ν : Measure Y}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {ε δ : ℝ} (hδ : 1 ≤ δ) :
    Indistinguishable μ ν ε δ := by
  have hd : (1 : ℝ≥0∞) ≤ ENNReal.ofReal δ := ENNReal.one_le_ofReal.mpr hδ
  exact ⟨fun s _ => prob_le_one.trans (hd.trans (le_add_left le_rfl)),
    fun s _ => prob_le_one.trans (hd.trans (le_add_left le_rfl))⟩

lemma Indistinguishable.bind_approx [StandardBorelSpace X] [StandardBorelSpace Y]
    {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f g : X → Measure Y} [∀ x, IsProbabilityMeasure (f x)] [∀ x, IsProbabilityMeasure (g x)]
    {a b δ η : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hp : Indistinguishable μ ν a δ) (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ x, Indistinguishable (f x) (g x) b η) :
    Indistinguishable (μ.bind f) (ν.bind g) (a + b) (δ + η) := by
  letI := probability_bind μ f hf
  letI := probability_bind ν g hg
  by_cases hδ1 : δ < 1
  swap
  · exact Indistinguishable.of_delta_ge_one (by linarith)
  by_cases hη1 : η < 1
  swap
  · exact Indistinguishable.of_delta_ge_one (by linarith)
  let A := Kernel.const Unit μ
  let B := Kernel.const Unit ν
  let F : Kernel X Y := ⟨f, hf⟩
  let G : Kernel X Y := ⟨g, hg⟩
  letI : IsMarkovKernel F := ⟨fun x => inferInstanceAs (IsProbabilityMeasure (f x))⟩
  letI : IsMarkovKernel G := ⟨fun x => inferInstanceAs (IsProbabilityMeasure (g x))⟩
  obtain ⟨hA, hB, hpAB⟩ := purePartKernel_properties A B ha hδ hδ1 (fun _ => hp)
  obtain ⟨hF, hG, hpFG⟩ := purePartKernel_properties F G hb hη hη1 hfg
  letI := hA
  letI := hB
  letI := hF
  letI := hG
  let P := purePartKernel A B a ()
  let Q := purePartKernel B A a ()
  let J := purePartKernel F G b
  let L := purePartKernel G F b
  have hPQ : Indistinguishable P Q a 0 := (hpAB ()).1
  have hJL : ∀ x, Indistinguishable (J x) (L x) b 0 := fun x => (hpFG x).1
  have hresult := hPQ.bind_pure J.measurable L.measurable hJL
  have hP := bind_subpart J.measurable hf (hpAB ()).2.1 (fun x => (hpFG x).2.1)
  have hQ := bind_subpart L.measurable hg (hpAB ()).2.2 (fun x => (hpFG x).2.2)
  have hc : 0 ≤ (1 - δ) * (1 - η) := mul_nonneg (by linarith) (by linarith)
  have hc1 : (1 - δ) * (1 - η) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (show 1 - η ≤ 1 by linarith) (by linarith)).trans (by linarith)
  rw [← ENNReal.ofReal_mul (show 0 ≤ 1 - δ by linarith)] at hP hQ
  change ENNReal.ofReal ((1 - δ) * (1 - η)) • P.bind J ≤ μ.bind f at hP
  change ENNReal.ofReal ((1 - δ) * (1 - η)) • Q.bind L ≤ ν.bind g at hQ
  letI := probability_bind P J J.measurable
  letI := probability_bind Q L L.measurable
  have htransfer := hresult.subpart_transfer (le_refl 0) hc hc1 hP hQ
  exact htransfer.mono le_rfl (by nlinarith only [mul_nonneg hδ hη])

/-- The continuation guarantee only needs to hold on a common measurable support. -/
lemma Indistinguishable.bind_approx_on [StandardBorelSpace X] [StandardBorelSpace Y] [Inhabited Y]
    {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f g : X → Measure Y} [∀ x, IsProbabilityMeasure (f x)] [∀ x, IsProbabilityMeasure (g x)]
    {a b δ η : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hp : Indistinguishable μ ν a δ) (hf : Measurable f) (hg : Measurable g)
    {G : Set X} (hG : MeasurableSet G) (hμ : ∀ᵐ x ∂μ, x ∈ G) (hν : ∀ᵐ x ∂ν, x ∈ G)
    (hfg : ∀ x ∈ G, Indistinguishable (f x) (g x) b η) :
    Indistinguishable (μ.bind f) (ν.bind g) (a + b) (δ + η) := by
  classical
  let F := fun x => if x ∈ G then f x else Measure.dirac (default : Y)
  let H := fun x => if x ∈ G then g x else Measure.dirac (default : Y)
  have hF : Measurable F := Measurable.ite hG hf measurable_const
  have hH : Measurable H := Measurable.ite hG hg measurable_const
  letI : ∀ x, IsProbabilityMeasure (F x) := fun x => by dsimp [F]; split_ifs <;> infer_instance
  letI : ∀ x, IsProbabilityMeasure (H x) := fun x => by dsimp [H]; split_ifs <;> infer_instance
  have hres := hp.bind_approx ha hb hδ hη hF hH (fun x => by
    dsimp [F, H]
    split_ifs with hx
    · exact hfg x hx
    · exact Indistinguishable.of_eq rfl hb hη)
  have heF : μ.bind F = μ.bind f := Measure.bind_congr_right (hμ.mono fun x hx => if_pos hx)
  have heH : ν.bind H = ν.bind g := Measure.bind_congr_right (hν.mono fun x hx => if_pos hx)
  rwa [heF, heH] at hres

end DPCut
