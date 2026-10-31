import DPCut.CappedLSWRelease
import DPCut.ApplicationLSWBounds

/-! Uniform polynomial cost of the approximate capped release, with logarithmic
dependence on inverse privacy delta and failure probability. Correlation
clustering is a specialization of the general certificate. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DPCut

lemma PolynomialRuntimeBound.application {f : ℕ → Parameters → ℝ≥0∞}
    (hf : PolynomialRuntimeBound f) {η ε : ℝ}
    (hη : 0 < η) (hη₁ : η ≤ 1/4) (hε : 0 < ε) :
    PolynomialVertexBound (fun n => f n (applicationParameters n η ε)) := by
  obtain ⟨B, hB, hb⟩ := application_runtimeScale_bound hη hε
  exact hf.specialize _ (fun _ hn => applicationParameters_valid hn hη hη₁ hε) hB hb

lemma edge_count_polynomial : PolynomialVertexBound (fun n => (Fintype.card (Edge n):ℝ≥0∞)) := by
  apply (real_vertex_polynomial.real_pow 2 (fun n _ => Nat.cast_nonneg n)).mono
  intro n hn
  simpa using ENNReal.ofReal_le_ofReal (edge_card_le_square n)

namespace CappedLSW

lemma errorBudget_polynomial :
    PolynomialRuntimeBound (fun n p => (errorBudget n p:ℝ≥0∞)) := by
  have h1 : PolynomialRuntimeBound (fun _ _ => (1:ℝ≥0∞)) := by
    simpa using PolynomialRuntimeBound.constant 1 (by norm_num)
  have h4 : PolynomialRuntimeBound (fun _ _ => (4:ℝ≥0∞)) := by
    simpa using PolynomialRuntimeBound.constant 4 (by norm_num)
  obtain ⟨hT1,hT2,hK,hk⟩ := polynomial_capped_parameters
  simpa [errorBudget, config] using
    ((((h4.mul polynomial_edges).mul hT1.precision).mul hT2.precision).mul
      (hK.precision.add h1)).mul (hk.precision.add h1)

lemma precisionIndex_log_bound {n : ℕ} {p : Parameters} (hp : p.Valid) :
    Real.log (precisionIndex n p) ≤
      19 + errorBudget n p + Real.log (1/p.beta) + Real.log (1/p.delta) := by
  have hb := hp.2.2.2.2.2.2.1
  have hd := hp.2.2.2.2.1
  have hprod : 0 < p.beta*p.delta := mul_pos hb hd
  have hprod1 : p.beta*p.delta ≤ 1 := mul_le_one₀
    (by linarith [hp.2.2.2.2.2.2.2]) hd.le (by linarith [hp.2.2.2.2.2.1])
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ 16/(p.beta*p.delta) by positivity)).le
  have hN : (precisionIndex n p:ℝ) ≤ 19*(1+(errorBudget n p:ℝ))/(p.beta*p.delta) := by
    rw [le_div_iff₀ hprod]
    have hh := mul_le_mul_of_nonneg_right hc (show (0:ℝ) ≤ 1+errorBudget n p by positivity)
    have hh' := mul_le_mul_of_nonneg_right hh hprod.le
    have heq : (16/(p.beta*p.delta)+1)*(1+(errorBudget n p:ℝ))*(p.beta*p.delta) =
        (16+p.beta*p.delta)*(1+(errorBudget n p:ℝ)) := by field_simp
    rw [heq] at hh'
    simp only [precisionIndex, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
    nlinarith [Nat.cast_nonneg (α:=ℝ) (errorBudget n p)]
  have hpos : (0:ℝ) < precisionIndex n p := by
    exact_mod_cast (show 0 < precisionIndex n p by have := precisionIndex_two_le n p; omega)
  have hlog := Real.log_le_log hpos hN
  rw [Real.log_div (by positivity) hprod.ne', Real.log_mul (by norm_num) (by positivity),
    Real.log_mul hb.ne' hd.ne'] at hlog
  have h19 := Real.log_le_self (by norm_num : (0:ℝ)≤19)
  have hE := Real.log_le_sub_one_of_pos (show (0:ℝ)<1+errorBudget n p by positivity)
  simp only [one_div, Real.log_inv]
  linarith

lemma precisionIndex_log_polynomial :
    PolynomialRuntimeBound (fun n p => ENNReal.ofReal (Real.log (precisionIndex n p))) := by
  have hE : PolynomialRuntimeBound (fun n p => ENNReal.ofReal (errorBudget n p:ℝ)) := by
    simpa using errorBudget_polynomial
  have hR : PolynomialRuntimeBound (fun n p => ENNReal.ofReal (runtimeScale n p)) :=
    ⟨1, by norm_num, 1, fun _ _ _ _ => by simp⟩
  apply (((PolynomialRuntimeBound.constant 19 (by norm_num)).real_add hE).real_add hR).of_le
  intro n hn p hp
  apply ENNReal.ofReal_le_ofReal
  have h := precisionIndex_log_bound (n:=n) hp
  have hg := (one_div_pos.mpr hp.1).le
  have he := (one_div_pos.mpr hp.2.2.1).le
  unfold runtimeScale
  linarith [Nat.cast_nonneg (α:=ℝ) n]

/-- Uniform in all valid public parameters, including logarithmic dependence on
inverse privacy delta and failure probability. -/
lemma cost_polynomial (F : CuttingPlaneFamily) : PolynomialRuntimeBound (costBound F) := by
  have hc (a : ℝ) (ha : 0<a) := PolynomialRuntimeBound.constant a ha
  have h1 : PolynomialRuntimeBound (fun _ _ => (1:ℝ≥0∞)) := by simpa using hc 1 (by norm_num)
  have h2 : PolynomialRuntimeBound (fun _ _ => (2:ℝ≥0∞)) := by simpa using hc 2 (by norm_num)
  have h100 : PolynomialRuntimeBound (fun _ _ => (100:ℝ≥0∞)) := by simpa using hc 100 (by norm_num)
  have hB : PolynomialRuntimeBound (fun n _ => vectorBlockCost n) := h100.mul (polynomial_vertices.pow 2)
  have hcap : PolynomialRuntimeBound (fun n _ => cappedBlockCost n) := hB.mul hB
  obtain ⟨hT1,hT2,hK,hk⟩ := polynomial_capped_parameters
  have hBr : PolynomialRuntimeBound (fun n _ => ENNReal.ofReal (objectiveBound n)) := by
    simpa [objectiveBound, ENNReal.ofReal_mul] using (hc 3 (by norm_num)).mul polynomial_edges
  have hsolve := configuredLSW_cost_polynomial F precisionIndex
    (fun n p => (config n p).oracle.lam) (fun n _ => objectiveBound n)
    precisionIndex_log_polynomial polynomial_capped_lam.precision hBr
    (fun n _ p _ => precisionIndex_two_le n p)
    (fun n hn p hp => by linarith [(oracle_bounds hn hp).lam_lower])
    (fun n _ _ _ => by unfold objectiveBound; positivity)
  have hG : PolynomialRuntimeBound (fun n p => gaussianBatchCost n (config n p).oracle.k) :=
    (hB.mul polynomial_vertices).mul (hk.precision.add h1)
  have hTrial : PolynomialRuntimeBound (fun n p => trialCostBound n (config n p).oracle) :=
    (hG.add h1).add hB
  have hW : PolynomialRuntimeBound (witnessCost F) :=
    (hB.add hsolve).add (hK.precision.mul hTrial)
  have hAgg := polynomial_edges.mul (hB.add (h2.mul hW))
  exact (hT1.precision.mul ((h1.add hcap).add
    (hT2.precision.mul (hAgg.add hcap)))).add hB

lemma cc_cost_polynomial (F : CuttingPlaneFamily) {γ ε : ℝ}
    (hγ : 0 < γ) (hγ₁ : γ ≤ 1/4) (hε : 0 < ε) :
    PolynomialVertexBound (fun n => costBound F n (ccParameters n γ ε)) :=
  (cost_polynomial F).cc hγ hγ₁ hε

/-- Lemma 29 with privacy, utility, support, and general runtime for one program. -/
theorem capped_release_of_lsw (hLSW : LSWStatement) :
    ∃ Ctime : ℝ, 0 < Ctime ∧ ∃ degree : ℕ,
    ∀ n (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) (D : Finset (Edge n)),
      let F := cuttingPlaneFamily hLSW verifiedLinearAlgebra.primitives
      DP (fun w w' => CappedOn D w ∧ CappedOn D w' ∧ Adjacent w w')
        (kernel F hn p hp D) p.epsilon p.delta ∧
      ∀ w : Weights n,
        (run F hn p hp D w).cost ≤ ENNReal.ofReal (Ctime * runtimeScale n p ^ degree) ∧
        (∀ᵐ h ∂(run F hn p hp D w).law, CappedOn D h) ∧
        (CappedOn D w → HighProbability (run F hn p hp D w).law p.beta
          (fun h => AllCuts w h p.gamma ((2:ℝ)^138 * mainError n p))) := by
  let F := cuttingPlaneFamily hLSW verifiedLinearAlgebra.primitives
  obtain ⟨C, hC, d, hcost⟩ := cost_polynomial F
  refine ⟨C, hC, d, fun n hn p hp D => ⟨run_private F hn p hp D, fun w => ?_⟩⟩
  exact ⟨(run_cost F hn p hp D w).trans (hcost n hn p hp), run_capped F hn p hp D w,
    fun hw => run_utility F hn p hp D w hw⟩

end CappedLSW
end DPCut
