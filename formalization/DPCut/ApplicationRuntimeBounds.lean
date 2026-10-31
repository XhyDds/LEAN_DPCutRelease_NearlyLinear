import DPCut.CappedCosted
import DPCut.CCCalibration

/-! Polynomial closure in the vertex count for fixed application parameters. -/
set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace DPCut

def PolynomialVertexBound (f : ℕ → ℝ≥0∞) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ n, 2 ≤ n → f n ≤ ENNReal.ofReal (C * (1 + (n : ℝ)) ^ d)

lemma PolynomialVertexBound.constant (C : ℝ) (hC : 0 < C) :
    PolynomialVertexBound (fun _ => ENNReal.ofReal C) := ⟨C, hC, 0, fun _ _ => by simp⟩

lemma PolynomialVertexBound.add {f g : ℕ → ℝ≥0∞}
    (hf : PolynomialVertexBound f) (hg : PolynomialVertexBound g) :
    PolynomialVertexBound (fun n => f n + g n) := by
  obtain ⟨C, hC, d, hf⟩ := hf
  obtain ⟨D, hD, e, hg⟩ := hg
  refine ⟨C + D, add_pos hC hD, max d e, ?_⟩
  intro n hn
  calc
    _ ≤ ENNReal.ofReal (C * (1 + (n : ℝ)) ^ d) + ENNReal.ofReal (D * (1 + (n : ℝ)) ^ e) := add_le_add (hf n hn) (hg n hn)
    _ = ENNReal.ofReal (C * (1 + (n : ℝ)) ^ d + D * (1 + (n : ℝ)) ^ e) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      have hbase : (1 : ℝ) ≤ 1 + n := le_add_of_nonneg_right (Nat.cast_nonneg n)
      have h₁ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (Nat.le_max_left d e)) hC.le
      have h₂ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (Nat.le_max_right d e)) hD.le
      nlinarith)

lemma PolynomialVertexBound.mul {f g : ℕ → ℝ≥0∞}
    (hf : PolynomialVertexBound f) (hg : PolynomialVertexBound g) :
    PolynomialVertexBound (fun n => f n * g n) := by
  obtain ⟨C, hC, d, hf⟩ := hf
  obtain ⟨D, hD, e, hg⟩ := hg
  refine ⟨C * D, mul_pos hC hD, d + e, ?_⟩
  intro n hn
  calc
    _ ≤ ENNReal.ofReal (C * (1 + (n : ℝ)) ^ d) * ENNReal.ofReal (D * (1 + (n : ℝ)) ^ e) := mul_le_mul' (hf n hn) (hg n hn)
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity), pow_add]; congr 1; ring

lemma PolynomialVertexBound.mono {f g : ℕ → ℝ≥0∞} (hg : PolynomialVertexBound g)
    (hfg : ∀ n, 2 ≤ n → f n ≤ g n) : PolynomialVertexBound f := by
  obtain ⟨C, hC, d, hg⟩ := hg
  exact ⟨C, hC, d, fun n hn => (hfg n hn).trans (hg n hn)⟩

lemma vertex_count_polynomial : PolynomialVertexBound (fun n => (n : ℝ≥0∞) + 1) := by
  refine ⟨1, by norm_num, 1, fun n hn => ?_⟩
  simp [ENNReal.ofReal_add, add_comm]

lemma vector_block_polynomial : PolynomialVertexBound vectorBlockCost := by
  have h100 : PolynomialVertexBound (fun _ => (100 : ℝ≥0∞)) := by
    simpa using PolynomialVertexBound.constant 100 (by norm_num)
  change PolynomialVertexBound (fun n => 100 * ((n : ℝ≥0∞) + 1) ^ 2)
  simpa only [pow_two] using h100.mul (vertex_count_polynomial.mul vertex_count_polynomial)

lemma capped_block_polynomial : PolynomialVertexBound cappedBlockCost :=
  vector_block_polynomial.mul vector_block_polynomial

lemma PolynomialRuntimeBound.specialize {f : ℕ → Parameters → ℝ≥0∞}
    (hf : PolynomialRuntimeBound f) (p : ℕ → Parameters)
    (hp : ∀ n, 2 ≤ n → (p n).Valid)
    {B : ℝ} (hB : 0 < B) (hscale : ∀ n, 2 ≤ n → runtimeScale n (p n) ≤ B * (1 + n)) :
    PolynomialVertexBound (fun n => f n (p n)) := by
  obtain ⟨C, hC, d, hf⟩ := hf
  refine ⟨C * B ^ d, mul_pos hC (pow_pos hB d), d, ?_⟩
  intro n hn
  apply (hf n hn (p n) (hp n hn)).trans
  apply ENNReal.ofReal_le_ofReal
  have hR : 0 ≤ runtimeScale n (p n) := (by norm_num : (0 : ℝ) ≤ 1).trans (runtimeScale_bounds (hp n hn)).2.2
  have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR (hscale n hn) d) hC.le
  simpa only [mul_pow, mul_assoc] using hh

lemma application_runtimeScale_bound {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ n, 2 ≤ n → runtimeScale n (applicationParameters n η ε) ≤ B * (1 + n) := by
  let B : ℝ := 22 + 1 / η + 1 / min ε 1
  have he : 0 < min ε 1 := lt_min hε (by norm_num)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hl := Real.log_le_self hn0
  simp only [runtimeScale, applicationParameters, one_div, Real.log_inv, Real.log_pow]
  dsimp [B]
  have hηi : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  have hei : 0 ≤ (min ε 1)⁻¹ := inv_nonneg.mpr he.le
  simp only [one_div]
  nlinarith

lemma cc_runtimeScale_bound {γ ε : ℝ} (hγ : 0 < γ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ n, 2 ≤ n → runtimeScale n (ccParameters n γ ε) ≤ B * (1 + n) := by
  obtain ⟨B, hB, hb⟩ := application_runtimeScale_bound hγ (half_pos hε)
  refine ⟨B + 2, by linarith, ?_⟩
  intro n hn
  have he : runtimeScale n (ccParameters n γ ε) = runtimeScale n (applicationParameters n γ (ε / 2)) + Real.log 2 := by
    simp only [runtimeScale, ccParameters, applicationParameters]
    rw [one_div ((n : ℝ)⁻¹ ^ 10 / 2), inv_div, Real.log_div (by norm_num) (by positivity), Real.log_pow, Real.log_inv]
    simp only [one_div, Real.log_inv, Real.log_pow]
    ring
  rw [he]
  have hl : Real.log 2 ≤ 2 := Real.log_le_self (by norm_num)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  nlinarith [hb n hn]

end DPCut
