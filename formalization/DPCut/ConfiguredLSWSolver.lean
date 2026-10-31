import DPCut.Theorem1LSW

/-! LSW at a caller-specified oracle configuration. Public timeouts and
independent restarts retain logarithmic dependence on inverse precision. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DPCut.ConfiguredLSW

def accuracy (n N : ℕ) : ℝ := (N:ℝ)⁻¹ ^ 2 / (8*(n:ℝ)^4)
def scale (n N : ℕ) (lam B : ℝ) : ℝ :=
  20 + (n:ℝ)^2 + SDPCoordinates.oracleCharge n + 12*n +
    2*B + lam*(n:ℝ)^2 + 2*Real.log N
def fuel (F : CuttingPlaneFamily) (n N : ℕ) (lam B : ℝ) : ℕ :=
  ⌈2*F.coefficient * scale n N lam B ^ F.degree⌉₊ + 1
def repeats (N : ℕ) : ℕ := ⌈2*Real.log (2*N)⌉₊ + 1
def cost (F : CuttingPlaneFamily) (n N : ℕ) (lam B : ℝ) : ℝ≥0∞ :=
  repeats N * ((fuel F n N lam B : ℝ≥0∞)+1) + SDPCoordinates.oracleCharge n

lemma radius_bounds {N : ℕ} (hN : 2 ≤ N) : 0 < (N:ℝ)⁻¹ ∧ (N:ℝ)⁻¹ ≤ 1/2 := by
  have h : (2:ℝ) ≤ N := by exact_mod_cast hN
  exact ⟨by positivity, by simpa using inv_anti₀ (by norm_num : (0:ℝ)<2) h⟩

lemma accuracy_bounds {n N : ℕ} (hn : 2 ≤ n) (hN : 2 ≤ N) :
    0 < accuracy n N ∧ accuracy n N ≤ 1/2 := by
  obtain ⟨hr, hrh⟩ := radius_bounds hN
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn4 : (1:ℝ) ≤ (n:ℝ)^4 := one_le_pow₀ (by linarith)
  unfold accuracy
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : (0:ℝ)<8*(n:ℝ)^4)).mpr
    nlinarith

lemma scale_bound {n N : ℕ} (hn : 2 ≤ n) (hN : 2 ≤ N) {lam B : ℝ}
    (hl : 0 ≤ lam) (hB : 0 ≤ B) :
    0 ≤ sdpLSWScale n lam B (accuracy n N) ∧
      sdpLSWScale n lam B (accuracy n N) ≤ scale n N lam B := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have he := accuracy_bounds hn hN
  have hT : 1 ≤ 1+2*B+lam*(n:ℝ)^2 := by nlinarith [mul_nonneg hl (sq_nonneg (n:ℝ))]
  have hratio : 0 ≤ (1+2*B+lam*(n:ℝ)^2) / accuracy n N := div_nonneg (by linarith) he.1.le
  have hlog : 0 ≤ Real.log ((1+2*B+lam*(n:ℝ)^2) / accuracy n N) :=
    Real.log_nonneg ((one_le_div he.1).mpr (he.2.trans (by linarith)))
  have hg := Real.log_nonneg (show (1:ℝ)≤8*n by
    have h : (2:ℝ)≤n := by exact_mod_cast hn
    linarith)
  constructor
  · unfold sdpLSWScale; positivity
  · have hTpos : 0 < 1+2*B+lam*(n:ℝ)^2 := by linarith
    have heq : Real.log ((1+2*B+lam*(n:ℝ)^2) / accuracy n N) =
        Real.log (1+2*B+lam*(n:ℝ)^2) + 2*Real.log N + Real.log 8 + 4*Real.log n := by
      rw [Real.log_div hTpos.ne' he.1.ne']
      unfold accuracy
      rw [Real.log_div (by positivity) (by positivity),
        Real.log_mul (by norm_num) (pow_ne_zero _ hn0.ne'), Real.log_pow,
        Real.log_pow, Real.log_inv]
      ring
    have h1 := Real.log_le_self (show (0:ℝ)≤8*n by positivity)
    have h2 := Real.log_le_self hTpos.le
    have h3 := Real.log_le_self hn0.le
    have h4 := Real.log_le_self (by norm_num : (0:ℝ)≤8)
    unfold sdpLSWScale scale
    rw [heq]
    nlinarith

lemma scale_nonneg {n N : ℕ} (hn : 2 ≤ n) (hN : 2 ≤ N) {lam B : ℝ}
    (hl : 0 ≤ lam) (hB : 0 ≤ B) : 0 ≤ scale n N lam B :=
  (scale_bound hn hN hl hB).1.trans (scale_bound hn hN hl hB).2

lemma fuel_mean (F : CuttingPlaneFamily) {n N : ℕ} (hn : 2 ≤ n) (hN : 2 ≤ N)
    {lam B : ℝ} (hl : 0 ≤ lam) (hB : 0 ≤ B) :
    ENNReal.ofReal (F.coefficient*sdpLSWScale n lam B (accuracy n N)^F.degree) ≤
      (fuel F n N lam B : ℝ≥0∞)/2 := by
  obtain ⟨h0, hscale⟩ := scale_bound hn hN hl hB
  have hpow := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hscale F.degree) F.coefficient_pos.le
  have hf : 2*F.coefficient*scale n N lam B^F.degree ≤ (fuel F n N lam B : ℝ) :=
    (Nat.le_ceil _).trans (by simp [fuel])
  have h := ENNReal.ofReal_le_ofReal (show
    F.coefficient*sdpLSWScale n lam B (accuracy n N)^F.degree ≤ (fuel F n N lam B:ℝ)/2 by linarith)
  simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2), ENNReal.ofReal_natCast,
    ENNReal.ofReal_ofNat] using h

lemma repeats_failure {N : ℕ} (hN : 2 ≤ N) :
    (1/2:ℝ≥0∞)^repeats N ≤ ENNReal.ofReal ((N:ℝ)⁻¹/2) := by
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have h := repetition_failure_bound (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)≤1)
    (by positivity : 0 < (N:ℝ)⁻¹/2) (repeats N) (by
      have heq : 1 / ((N:ℝ)⁻¹/2) = 2*N := by field_simp
      rw [heq]
      have hc := Nat.le_ceil (2*Real.log (2*(N:ℝ)))
      dsimp [repeats]
      push_cast
      linarith)
  simpa only [show (1-(1/2:ℝ))=1/2 by norm_num, ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤1/2),
    ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2), ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal h

variable (F : CuttingPlaneFamily) {n N : ℕ} (hn : 2 ≤ n) (hN : 2 ≤ N)
  {lam B : ℝ} (hl : 0 ≤ lam) (hB : 0 ≤ B)

def algorithm : TimedAlgorithm (Weights n) (SDPCoordinates.Space n) :=
  F.algorithm n hn lam B (accuracy n N) hl hB (accuracy_bounds hn hN).1 (accuracy_bounds hn hN).2

def solve (D : Weights n) : CostedLaw (FeasibleMatrix n) :=
  SDPCoordinates.solve hn (algorithm F hn hN hl hB) (fuel F n N lam B) (repeats N) D

lemma measurable_solve : Measurable (fun D => (solve F hn hN hl hB D).law) :=
  SDPCoordinates.measurable_solve hn _ _ _

instance solve_probability (D : Weights n) : IsProbabilityMeasure (solve F hn hN hl hB D).law :=
  SDPCoordinates.solve_probability hn _ _ _ _

lemma solve_cost (D : Weights n) : (solve F hn hN hl hB D).cost ≤ cost F n N lam B :=
  SDPCoordinates.solve_cost hn _ _ _ _

lemma solve_failure (hl1 : 1 ≤ lam) (D : Weights n) :
    (solve F hn hN hl hB D).law {X | lam*((N:ℝ)⁻¹/2)^2/(2*(n:ℝ)^4) <
      optimum lam (boundedObjective B D) - objective lam (boundedObjective B D) X.val} ≤
        ENNReal.ofReal ((N:ℝ)⁻¹/2) := by
  have hm := (F.expected n hn lam B (accuracy n N) hl hB
    (accuracy_bounds hn hN).1 (accuracy_bounds hn hN).2 D).trans (fuel_mean F hn hN hl hB)
  have hf := SDPCoordinates.solve_failure hn hl hB (algorithm F hn hN hl hB)
    (F.accurate n hn lam B (accuracy n N) hl hB (accuracy_bounds hn hN).1 (accuracy_bounds hn hN).2)
    (show 0 < fuel F n N lam B by unfold fuel; omega) (repeats N) D hm
  have hg : accuracy n N ≤ lam*((N:ℝ)⁻¹/2)^2/(2*(n:ℝ)^4) := by
    have h := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hl1 (sq_nonneg ((N:ℝ)⁻¹)))
      (show 0 ≤ 8*(n:ℝ)^4 by positivity)
    dsimp [accuracy]
    convert h using 1 <;> ring
  exact (measure_mono (fun X hX => lt_of_le_of_lt hg hX)).trans (hf.trans (repeats_failure hN))

end DPCut.ConfiguredLSW
