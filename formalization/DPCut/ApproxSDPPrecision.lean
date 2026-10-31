import DPCut.PolynomialRuntime
import DPCut.ApproximationTransfer
import DPCut.ApproxSDPOracle

/-! A public accuracy request and a uniform polynomial bound on its logarithmic cost. -/
set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace DPCut

def approximationBudget (n : ℕ) (p : Parameters) : ℝ :=
  let c := fullRunConfig n (precisionParameters p)
  4 * Fintype.card (Edge n) * c.T1 * c.T2 * c.oracle.K * (c.oracle.k + 1)

def approximationRadius (n : ℕ) (p : Parameters) : ℝ :=
  p.beta * p.delta / (16 * (1 + approximationBudget n p))

lemma approximationBudget_nonneg (n : ℕ) (p : Parameters) : 0 ≤ approximationBudget n p := by
  unfold approximationBudget
  positivity

lemma approximationRadius_bounds {n : ℕ} {p : Parameters} (hp : p.Valid) :
    0 < approximationRadius n p ∧ approximationRadius n p ≤ 1 / 2 := by
  have hb := hp.2.2.2.2.2.2.1
  have hd := hp.2.2.2.2.1
  have hb1 : p.beta ≤ 1 := by linarith [hp.2.2.2.2.2.2.2]
  have hd1 : p.delta ≤ 1 := by linarith [hp.2.2.2.2.2.1]
  have hprod : p.beta * p.delta ≤ 1 := mul_le_one₀ hb1 hd.le hd1
  have hB := approximationBudget_nonneg n p
  unfold approximationRadius
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : 0 < 16 * (1 + approximationBudget n p))).mpr
    nlinarith

lemma approximationBudget_error {n : ℕ} {p : Parameters} (hp : p.Valid) :
    approximationBudget n p * approximationRadius n p ≤ implementationTV p := by
  have hb := hp.2.2.2.2.2.2.1
  have hd := hp.2.2.2.2.1
  have hb1 : p.beta ≤ 1 := by linarith [hp.2.2.2.2.2.2.2]
  have hd1 : p.delta ≤ 1 := by linarith [hp.2.2.2.2.2.1]
  have hB := approximationBudget_nonneg n p
  have he : Real.exp p.epsilon ≤ 3 :=
    (Real.exp_le_exp.mpr hp.2.2.2.1).trans (by linarith [Real.exp_one_lt_d9])
  have hbnd : approximationBudget n p * approximationRadius n p ≤ p.beta * p.delta / 16 := by
    unfold approximationRadius
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 16 * (1 + approximationBudget n p))).mpr
    nlinarith [mul_pos hb hd]
  apply hbnd.trans
  unfold implementationTV
  apply le_min
  · nlinarith [mul_le_mul_of_nonneg_left hd1 hb.le]
  · apply (le_div_iff₀ (by positivity : 0 < 2 * (1 + Real.exp p.epsilon))).mpr
    have hprod : p.beta * p.delta ≤ p.delta := mul_le_of_le_one_left hd.le hb1
    nlinarith [mul_le_mul_of_nonneg_left he (mul_nonneg hb.le hd.le)]

lemma runtimeScale_precision_le {n : ℕ} {p : Parameters} (hp : p.Valid) :
    runtimeScale n (precisionParameters p) ≤ 3 * runtimeScale n p := by
  have hR := (runtimeScale_bounds (n := n) hp).2.2
  have h2 : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
    norm_num
  have heq : runtimeScale n (precisionParameters p) = runtimeScale n p + 2 * Real.log 2 := by
    simp only [runtimeScale, precisionParameters, one_div, Real.log_inv]
    rw [Real.log_div hp.2.2.2.2.1.ne' (by norm_num),
      Real.log_div hp.2.2.2.2.2.2.1.ne' (by norm_num)]
    ring
  linarith

lemma PolynomialRuntimeBound.precision {f : ℕ → Parameters → ℝ≥0∞}
    (hf : PolynomialRuntimeBound f) :
    PolynomialRuntimeBound (fun n p => f n (precisionParameters p)) := by
  obtain ⟨C, hC, d, hf⟩ := hf
  refine ⟨C * 3 ^ d, by positivity, d, ?_⟩
  intro n hn p hp
  apply (hf n hn _ (precisionParameters_valid hp)).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    C * runtimeScale n (precisionParameters p) ^ d ≤ C * (3 * runtimeScale n p) ^ d :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (le_trans (by norm_num) (runtimeScale_bounds (precisionParameters_valid hp)).2.2)
        (runtimeScale_precision_le hp) d) hC.le
    _ = _ := by rw [mul_pow]; ring

lemma PolynomialRuntimeBound.pow {f : ℕ → Parameters → ℝ≥0∞}
    (hf : PolynomialRuntimeBound f) (k : ℕ) : PolynomialRuntimeBound (fun n p => f n p ^ k) := by
  induction k with
  | zero => simpa using PolynomialRuntimeBound.constant 1 (by norm_num)
  | succ k ih => simpa only [pow_succ] using ih.mul hf

lemma PolynomialRuntimeBound.of_le {f g : ℕ → Parameters → ℝ≥0∞}
    (hg : PolynomialRuntimeBound g)
    (hfg : ∀ n, 2 ≤ n → ∀ p : Parameters, p.Valid → f n p ≤ g n p) :
    PolynomialRuntimeBound f := by
  obtain ⟨C, hC, d, hg⟩ := hg
  exact ⟨C, hC, d, fun n hn p hp => (hfg n hn p hp).trans (hg n hn p hp)⟩

lemma polynomial_approximationBudget :
    PolynomialRuntimeBound (fun n p => ENNReal.ofReal (approximationBudget n p)) := by
  have h1 : PolynomialRuntimeBound (fun _ _ => (1 : ℝ≥0∞)) := by
    simpa using PolynomialRuntimeBound.constant 1 (by norm_num)
  have h4 : PolynomialRuntimeBound (fun _ _ => (4 : ℝ≥0∞)) := by
    simpa using PolynomialRuntimeBound.constant 4 (by norm_num)
  obtain ⟨hT1, hT2, hK, hk⟩ := polynomial_full_parameters
  have h := ((((h4.mul polynomial_edges).mul hT1.precision).mul hT2.precision).mul hK.precision).mul
    (hk.precision.add h1)
  convert h using 1
  funext n p
  have heq : approximationBudget n p =
      ((4 * Fintype.card (Edge n) * (fullRunConfig n (precisionParameters p)).T1 *
        (fullRunConfig n (precisionParameters p)).T2 * (fullRunConfig n (precisionParameters p)).oracle.K *
        ((fullRunConfig n (precisionParameters p)).oracle.k + 1) : ℕ) : ℝ) := by
    simp only [approximationBudget, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  rw [heq, ENNReal.ofReal_natCast]
  push_cast
  rfl

lemma approximationRadius_log_le {n : ℕ} {p : Parameters} (hp : p.Valid) :
    |Real.log (approximationRadius n p)| ≤
      16 + approximationBudget n p + Real.log (1 / p.beta) + Real.log (1 / p.delta) := by
  obtain ⟨hμ, hμhalf⟩ := approximationRadius_bounds (n := n) hp
  rw [abs_of_nonpos (Real.log_nonpos hμ.le (by linarith))]
  have hB := approximationBudget_nonneg n p
  have h16 : Real.log 16 ≤ 16 := Real.log_le_self (by norm_num)
  have hlogB := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + approximationBudget n p)
  simp only [approximationRadius, Real.log_div (mul_pos hp.2.2.2.2.2.2.1 hp.2.2.2.2.1).ne'
    (by positivity : (16 * (1 + approximationBudget n p) : ℝ) ≠ 0),
    Real.log_mul hp.2.2.2.2.2.2.1.ne' hp.2.2.2.2.1.ne',
    Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) (by positivity : (1 + approximationBudget n p) ≠ 0),
    one_div, Real.log_inv]
  linarith

lemma polynomial_approximationScale : PolynomialRuntimeBound
    (fun n p => ENNReal.ofReal (1 + n + |Real.log (approximationRadius n p)|)) := by
  have h16 := PolynomialRuntimeBound.constant 16 (by norm_num)
  have hR : PolynomialRuntimeBound (fun n p => ENNReal.ofReal (runtimeScale n p)) :=
    ⟨1, by norm_num, 1, fun _ _ _ _ => by simp⟩
  apply ((h16.add polynomial_approximationBudget).add hR).of_le
  intro n hn p hp
  have hB := approximationBudget_nonneg n p
  rw [← ENNReal.ofReal_add (by positivity) (approximationBudget_nonneg n p),
    ← ENNReal.ofReal_add (by positivity) (le_trans (by norm_num) (runtimeScale_bounds hp).2.2)]
  apply ENNReal.ofReal_le_ofReal
  have ht := approximationRadius_log_le (n := n) hp
  have hg := (one_div_pos.mpr hp.1).le
  have he := (one_div_pos.mpr hp.2.2.1).le
  unfold runtimeScale
  linarith

theorem polynomial_approximateSolve (sdp : ApproxSDPOracle) :
    PolynomialRuntimeBound (fun n p => sdp.charge n (approximationRadius n p)) := by
  have h := (PolynomialRuntimeBound.constant sdp.coefficient sdp.coefficient_pos).mul
    (polynomial_approximationScale.pow sdp.degree)
  apply h.of_le
  intro n hn p hp
  have hh := sdp.charge_le n (approximationRadius n p)
    (approximationRadius_bounds (n := n) hp).1 (approximationRadius_bounds (n := n) hp).2
  simpa only [← ENNReal.ofReal_pow (by positivity : 0 ≤ 1 + (n : ℝ) + |Real.log (approximationRadius n p)|),
    ← ENNReal.ofReal_mul sdp.coefficient_pos.le] using hh

end DPCut
