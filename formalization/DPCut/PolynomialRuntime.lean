import DPCut.RuntimeParameters

/-! Uniform polynomial closure for the public worst-case cost expression. -/
set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace DPCut

def PolynomialRuntimeBound (f : ℕ → Parameters → ℝ≥0∞) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ n, 2 ≤ n → ∀ p : Parameters, p.Valid →
    f n p ≤ ENNReal.ofReal (C * runtimeScale n p ^ d)

lemma PolynomialRuntimeBound.constant (C : ℝ) (hC : 0 < C) :
    PolynomialRuntimeBound (fun _ _ => ENNReal.ofReal C) := by
  exact ⟨C, hC, 0, fun _ _ _ _ => by simp⟩

lemma PolynomialRuntimeBound.add {f g : ℕ → Parameters → ℝ≥0∞}
    (hf : PolynomialRuntimeBound f) (hg : PolynomialRuntimeBound g) :
    PolynomialRuntimeBound (fun n p => f n p + g n p) := by
  obtain ⟨C, hC, d, hf⟩ := hf
  obtain ⟨D, hD, e, hg⟩ := hg
  refine ⟨C + D, add_pos hC hD, max d e, ?_⟩
  intro n hn p hp
  have hR := (runtimeScale_bounds (n := n) hp).2.2
  calc
    _ ≤ ENNReal.ofReal (C * runtimeScale n p ^ d) + ENNReal.ofReal (D * runtimeScale n p ^ e) :=
      add_le_add (hf n hn p hp) (hg n hn p hp)
    _ = ENNReal.ofReal (C * runtimeScale n p ^ d + D * runtimeScale n p ^ e) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      have h₁ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR (Nat.le_max_left d e)) hC.le
      have h₂ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR (Nat.le_max_right d e)) hD.le
      nlinarith)

lemma PolynomialRuntimeBound.mul {f g : ℕ → Parameters → ℝ≥0∞}
    (hf : PolynomialRuntimeBound f) (hg : PolynomialRuntimeBound g) :
    PolynomialRuntimeBound (fun n p => f n p * g n p) := by
  obtain ⟨C, hC, d, hf⟩ := hf
  obtain ⟨D, hD, e, hg⟩ := hg
  refine ⟨C * D, mul_pos hC hD, d + e, ?_⟩
  intro n hn p hp
  have hR := (runtimeScale_bounds (n := n) hp).2.2
  calc
    _ ≤ ENNReal.ofReal (C * runtimeScale n p ^ d) * ENNReal.ofReal (D * runtimeScale n p ^ e) :=
      mul_le_mul' (hf n hn p hp) (hg n hn p hp)
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity), pow_add]; congr 1; ring

lemma polynomial_vertices : PolynomialRuntimeBound (fun n _ => (n : ℝ≥0∞) + 1) := by
  refine ⟨1, by norm_num, 1, ?_⟩
  intro n hn p hp
  have h := ENNReal.ofReal_le_ofReal (runtimeScale_bounds (n := n) hp).1
  simpa [ENNReal.ofReal_add, add_comm] using h

lemma polynomial_edges : PolynomialRuntimeBound (fun n _ => (Fintype.card (Edge n) : ℝ≥0∞)) := by
  refine ⟨1, by norm_num, 2, ?_⟩
  intro n hn p hp
  have hnR : (n : ℝ) ≤ runtimeScale n p := by linarith [(runtimeScale_bounds (n := n) hp).1]
  have h := (edge_card_le_square n).trans (pow_le_pow_left₀ (Nat.cast_nonneg n) hnR 2)
  simpa using ENNReal.ofReal_le_ofReal h

lemma polynomial_sdp (sdp : ExactSDPOracleCost) : PolynomialRuntimeBound (fun n _ => sdp.charge n) := by
  refine ⟨sdp.coefficient, sdp.coefficient_pos, sdp.degree, ?_⟩
  intro n hn p hp
  apply (sdp.charge_le n).trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (runtimeScale_bounds hp).1 sdp.degree) sdp.coefficient_pos.le

lemma polynomial_full_parameters :
    PolynomialRuntimeBound (fun n p => (fullRunConfig n p).T1) ∧
    PolynomialRuntimeBound (fun n p => (fullRunConfig n p).T2) ∧
    PolynomialRuntimeBound (fun n p => (fullRunConfig n p).oracle.K) ∧
    PolynomialRuntimeBound (fun n p => (fullRunConfig n p).oracle.k) := by
  refine ⟨⟨5184, by norm_num, 1, ?_⟩, ⟨26112, by norm_num, 3, ?_⟩,
    ⟨128000000, by norm_num, 1, ?_⟩, ⟨640000000000, by norm_num, 1, ?_⟩⟩ <;>
    intro n hn p hp
  · simpa using ENNReal.ofReal_le_ofReal (full_runtime_parameter_bounds hn hp).1
  · simpa using ENNReal.ofReal_le_ofReal (full_runtime_parameter_bounds hn hp).2.1
  · simpa using ENNReal.ofReal_le_ofReal (full_runtime_parameter_bounds hn hp).2.2.1
  · simpa using ENNReal.ofReal_le_ofReal (full_runtime_parameter_bounds hn hp).2.2.2

/-- All coefficients and degrees are chosen before the graph size and public parameters. -/
theorem fullCostBound_polynomial (sdp : ExactSDPOracleCost) : PolynomialRuntimeBound (fullCostBound sdp) := by
  have h1 : PolynomialRuntimeBound (fun _ _ => (1 : ℝ≥0∞)) := by
    simpa using PolynomialRuntimeBound.constant 1 (by norm_num)
  have h2 : PolynomialRuntimeBound (fun _ _ => (2 : ℝ≥0∞)) := by
    simpa using PolynomialRuntimeBound.constant 2 (by norm_num)
  have h3 : PolynomialRuntimeBound (fun _ _ => (3 : ℝ≥0∞)) := by
    simpa using PolynomialRuntimeBound.constant 3 (by norm_num)
  have h100 : PolynomialRuntimeBound (fun _ _ => (100 : ℝ≥0∞)) := by
    simpa using PolynomialRuntimeBound.constant 100 (by norm_num)
  obtain ⟨hT1, hT2, hK, hk⟩ := polynomial_full_parameters
  have hB : PolynomialRuntimeBound (fun n _ => vectorBlockCost n) := by
    simpa only [vectorBlockCost, pow_two] using h100.mul (polynomial_vertices.mul polynomial_vertices)
  have hG : PolynomialRuntimeBound (fun n p => gaussianBatchCost n (fullRunConfig n p).oracle.k) :=
    (hB.mul polynomial_vertices).mul (hk.add h1)
  have hTrial : PolynomialRuntimeBound (fun n p => trialCostBound n (fullRunConfig n p).oracle) :=
    (hG.add h1).add hB
  have hWitness : PolynomialRuntimeBound (fun n p => witnessCostBound sdp n (fullRunConfig n p).oracle) :=
    (hB.add (polynomial_sdp sdp)).add (hK.mul hTrial)
  have hAggregate : PolynomialRuntimeBound (fun n p => aggregateCostBound sdp n (fullRunConfig n p).oracle) :=
    polynomial_edges.mul (hB.add (h2.mul hWitness))
  have hInner : PolynomialRuntimeBound (fun n p => innerCostBound sdp n (fullRunConfig n p)) :=
    hT2.mul (hAggregate.add hB)
  have hOuter : PolynomialRuntimeBound (fun n p => outerCostBound sdp n (fullRunConfig n p)) :=
    hT1.mul ((h1.add hB).add hInner)
  exact ((h3.mul hB).add polynomial_edges).add hOuter

end DPCut
