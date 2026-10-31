import DPCut.SDPLSWAlgorithm
import DPCut.ApproxSDPPrecision
import DPCut.ExpectedApproximation

/-! Public numerical bounds for every optimization call. Clipping the noisy
mass bounds objective data even off the utility good event. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DPCut

def publicObjectiveBound (n : ℕ) (p : Parameters) : ℝ :=
  (fullRunConfig n p).massCap + (1+(boundedParameters p).gamma) * Fintype.card (Edge n) * preprocessingThreshold n p

lemma runtimeScale_epsilon {n : ℕ} {p : Parameters} (hp : p.Valid) :
    1/p.epsilon ≤ runtimeScale n p := by
  have hg := one_div_pos.mpr hp.1
  have hd : 0 ≤ Real.log (1/p.delta) := Real.log_nonneg ((one_le_div hp.2.2.2.2.1).mpr (by linarith [hp.2.2.2.2.2.1]))
  have hb : 0 ≤ Real.log (1/p.beta) := Real.log_nonneg ((one_le_div hp.2.2.2.2.2.2.1).mpr (by linarith [hp.2.2.2.2.2.2.2]))
  unfold runtimeScale
  linarith [Nat.cast_nonneg (α := ℝ) n]

lemma full_massCap_nonneg {n : ℕ} (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid) :
    0 ≤ (fullRunConfig n p).massCap := by
  have hc := outerConfig_inner_utility_bounds hn (preprocessingThreshold_one_le hn hp)
    (boundedParameters p) (boundedParameters_valid hp)
  have hτ : 0 ≤ (fullRunConfig n p).tau2 := by
    change 0 ≤ (runConfig n (preprocessingThreshold n p) (boundedParameters p) outerUtilityConstants).tau2
    rw [hc.tau2_eq]
    exact div_nonneg (Real.log_nonneg ((one_le_div hc.beta2_pos).mpr hc.beta2_lt_one.le)) hc.eps2_pos.le
  change 0 ≤ Fintype.card (Edge n) * preprocessingThreshold n p + 2 * (fullRunConfig n p).tau2
  have hU : 0 ≤ preprocessingThreshold n p := le_trans (by norm_num) (preprocessingThreshold_one_le hn hp)
  positivity

lemma publicObjectiveBound_nonneg {n : ℕ} (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid) :
    0 ≤ publicObjectiveBound n p := by
  have hc := full_massCap_nonneg hn hp
  have hγ := (boundedParameters_valid hp).1.le
  have hU := (show (0 : ℝ) ≤ 1 by norm_num).trans (preprocessingThreshold_one_le hn hp)
  unfold publicObjectiveBound
  positivity

/-- Coarse polynomial majorants; the LSW invocation uses their logarithms. -/
theorem full_sdp_magnitude_bounds {n : ℕ} (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid) :
    (fullRunConfig n p).oracle.lam ≤ (10:ℝ)^40 * runtimeScale n p ^ 7 ∧
    publicObjectiveBound n p ≤ (10:ℝ)^10 * runtimeScale n p ^ 5 := by
  let R := runtimeScale n p
  let U := preprocessingThreshold n p
  let q := boundedParameters p
  let L := logFactor n U q
  let c := fullRunConfig n p
  have hR : 1 ≤ R := (runtimeScale_bounds hp).2.2
  have hR0 : 0 ≤ R := by linarith
  have hU : 1 ≤ U := preprocessingThreshold_one_le hn hp
  have hq : q.Valid := boundedParameters_valid hp
  have hL := core_log_bounds hn hU q hq
  have hLR : L ≤ 64*R := (full_release_log_bound hn hp).trans
    (mul_le_mul_of_nonneg_left (main_log_le_runtimeScale hn hp) (by norm_num))
  have hnR : (n : ℝ) ≤ R := by linarith [(runtimeScale_bounds (n:=n) hp).1]
  have hgi : 0 ≤ 1/p.gamma := (one_div_pos.mpr hp.1).le
  have hei : 0 ≤ 1/p.epsilon := (one_div_pos.mpr hp.2.2.1).le
  have hgR : 1/p.gamma ≤ R := (runtimeScale_bounds hp).2.1
  have heR : 1/p.epsilon ≤ R := runtimeScale_epsilon hp
  have hUupper : U ≤ 48 * R^3 := by
    calc
      _ ≤ 48 * logFactor n 1 p / (p.gamma*p.epsilon) := preprocessingThreshold_upper hn hp
      _ = 48 * logFactor n 1 p * (1/p.gamma) * (1/p.epsilon) := by ring
      _ ≤ 48 * R * R * R := mul_le_mul
        (mul_le_mul (mul_le_mul_of_nonneg_left (main_log_le_runtimeScale hn hp) (by norm_num)) hgR hgi (by positivity))
        heR hei (by positivity)
      _ = _ := by ring
  have hLam := (outer_oracle_size_bounds hn hU q hq hL).2
  have hLamUpper : c.oracle.lam ≤ (10:ℝ)^40 * R^7 := by
    calc
      _ ≤ (10:ℝ)^28 * L^5 / (q.gamma*q.epsilon) := hLam
      _ = 4 * (10:ℝ)^28 * L^5 * (1/p.gamma) * (1/p.epsilon) := by dsimp [q, boundedParameters]; ring
      _ ≤ 4 * (10:ℝ)^28 * (64*R)^5 * R * R := mul_le_mul
        (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [hL.one_le]) hLR 5) (by norm_num)) hgR hgi (by positivity))
        heR hei (by positivity)
      _ ≤ _ := by ring_nf; nlinarith [pow_nonneg hR0 7]
  have hτ := (outer_budget_bounds hn hU q hq hL).tau2_le
  have hτupper : c.tau2 ≤ (10:ℝ)^9 * R^3 := by
    calc
      _ ≤ 14000 * L^2 / q.epsilon := hτ
      _ = 28000 * L^2 * (1/p.epsilon) := by dsimp [q, boundedParameters]; ring
      _ ≤ 28000 * (64*R)^2 * R := mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [hL.one_le]) hLR 2) (by norm_num)) heR hei (by positivity)
      _ ≤ _ := by ring_nf; nlinarith [pow_nonneg hR0 3]
  have hmR : (Fintype.card (Edge n) : ℝ) ≤ R^2 :=
    (edge_card_le_square n).trans (pow_le_pow_left₀ (Nat.cast_nonneg n) hnR 2)
  have hmU : (Fintype.card (Edge n) : ℝ) * U ≤ 48*R^5 := by
    calc
      _ ≤ R^2 * (48*R^3) := mul_le_mul hmR hUupper (by linarith) (sq_nonneg R)
      _ = _ := by ring
  have hqg : 0 ≤ q.gamma ∧ q.gamma ≤ 1 := ⟨hq.1.le, by linarith [hq.2.1]⟩
  have hcap : c.massCap = Fintype.card (Edge n) * U + 2*c.tau2 := rfl
  have hB : publicObjectiveBound n p = c.massCap + (1+q.gamma) * (Fintype.card (Edge n) * U) := by
    unfold publicObjectiveBound; dsimp [c, q, U]; ring
  have hgprod : (1+q.gamma) * ((Fintype.card (Edge n) : ℝ) * U) ≤ 2*(48*R^5) :=
    mul_le_mul (by linarith [hqg.2]) hmU (by positivity) (by norm_num)
  have hpow := pow_le_pow_right₀ hR (show 3 ≤ 5 by omega)
  refine ⟨hLamUpper, ?_⟩
  rw [hB, hcap]
  nlinarith [pow_nonneg hR0 5]

def solverAccuracy (n : ℕ) (p : Parameters) : ℝ := approximationRadius n p ^ 2 / (8 * (n:ℝ)^4)
def solverRestarts (n : ℕ) (p : Parameters) : ℕ := ⌈2 * Real.log (2 / approximationRadius n p)⌉₊ + 1

lemma solverAccuracy_bounds {n : ℕ} (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid) :
    0 < solverAccuracy n p ∧ solverAccuracy n p ≤ 1/2 := by
  obtain ⟨hr, hrh⟩ := approximationRadius_bounds (n:=n) hp
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn4 : (1:ℝ) ≤ (n:ℝ)^4 := one_le_pow₀ (by linarith)
  unfold solverAccuracy
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : (0:ℝ) < 8*(n:ℝ)^4)).mpr
    nlinarith

lemma solverAccuracy_le_gap {n : ℕ} {p : Parameters} {lam : ℝ} (hlam : 1 ≤ lam) :
    solverAccuracy n p ≤ lam * (approximationRadius n p / 2)^2 / (2*(n:ℝ)^4) := by
  have h := mul_le_mul_of_nonneg_right hlam (sq_nonneg (approximationRadius n p))
  have hd : 0 ≤ (8:ℝ)*(n:ℝ)^4 := by positivity
  have hh := div_le_div_of_nonneg_right h hd
  simpa only [solverAccuracy, one_mul] using (show approximationRadius n p^2 / (8*(n:ℝ)^4) ≤ lam * (approximationRadius n p/2)^2 / (2*(n:ℝ)^4) by convert hh using 1 <;> ring)

lemma solverRestarts_failure {n : ℕ} {p : Parameters} (hp : p.Valid) :
    (1/2 : ℝ≥0∞) ^ solverRestarts n p ≤ ENNReal.ofReal (approximationRadius n p/2) := by
  have hr := (approximationRadius_bounds (n:=n) hp).1
  have h := repetition_failure_bound (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)≤1)
    (by positivity : 0 < approximationRadius n p/2) (solverRestarts n p) (by
      have hh : 2 * Real.log (2 / approximationRadius n p) ≤ (solverRestarts n p : ℝ) :=
        (Nat.le_ceil _).trans (by simp [solverRestarts])
      rw [show 1 / (approximationRadius n p / 2) = 2 / approximationRadius n p by ring]
      convert hh using 1 <;> ring)
  simpa only [show (1-(1/2:ℝ))=1/2 by norm_num, ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤1/2),
    ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2), ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal h

end DPCut
