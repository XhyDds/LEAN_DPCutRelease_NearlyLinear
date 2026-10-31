import DPCut.InnerLoopUtility
import DPCut.MainPrivacyCalibration

/-! The public parameter obligations used by Lemma 21, with Lemma 20's constants. -/
set_option autoImplicit false
noncomputable section
namespace DPCut

structure InnerUtilityBounds (n : ℕ) (U : ℝ) (p : Parameters) (c : RunConfig) : Prop where
  oracle_privacy : OraclePrivacyBounds n c.oracle
  aggregate_utility : ∀ w h : Weights n, Bounded U w → Nonnegative h →
    HighProbability (aggregateLaw c.oracle p.gamma w h) c.betaGE
      (fun a => a.Partition ∧ a.Accurate w h p.gamma c.B)
  eps2_pos : 0 < c.eps2
  beta2_pos : 0 < c.beta2
  beta2_lt_one : c.beta2 < 1
  tau2_eq : c.tau2 = Real.log (1 / c.beta2) / c.eps2
  betaGE_nonneg : 0 ≤ c.betaGE
  eta_eq : c.eta = stepSize p.gamma
  horizon_eq : c.T2 = innerHorizon n p.gamma
  certificate_lower : n * U ≤ c.B
  massCap_lower : Fintype.card (Edge n) * U + 2 * c.tau2 ≤ c.massCap

theorem runConfig_inner_utility_bounds_general {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U)
    (p : Parameters) (hp : p.IterationValid) :
    InnerUtilityBounds n U p (runConfig n U p utilityConstants) := by
  obtain ⟨hγ, hγ1, hε, hε1, hδ, hδ1, hβ, hβ1⟩ := hp
  let c := runConfig n U p utilityConstants
  have hT1 : 0 < c.T1 := main_outer_horizon_pos hn hU
  have hT2 : 0 < c.T2 := by change 0 < 1 + ⌈64 * (1 + p.gamma) ^ 2 * Real.log n / p.gamma ^ 2⌉₊; omega
  have hT1R : (0 : ℝ) < c.T1 := by exact_mod_cast hT1
  have hT2R : (0 : ℝ) < c.T2 := by exact_mod_cast hT2
  have hT11 : (1 : ℝ) ≤ c.T1 := by exact_mod_cast hT1
  have hT21 : (1 : ℝ) ≤ c.T2 := by exact_mod_cast hT2
  have hnum := main_composition_budget hT1 hT2 hε hε1 hδ (by linarith)
  have heG : 0 < c.epsGE := hnum.1
  have heG1 : c.epsGE < 1 := hnum.2.1
  have he2 : 0 < c.eps2 := by change 0 < p.epsilon / (2 * c.T1); positivity
  have hb2 : 0 < c.beta2 := by change 0 < p.beta / (2 * c.T1); positivity
  have hb21 : c.beta2 < 1 := by
    change p.beta / (2 * c.T1) < 1
    apply (div_lt_one (by positivity)).mpr
    linarith
  have hden : (2 : ℝ) ≤ 2 * c.T1 * c.T2 := by
    have h := mul_le_mul hT11 hT21 (by norm_num) hT1R.le
    nlinarith
  have hdG : 0 < c.deltaGE := by change 0 < p.delta / (2 * c.T1 * c.T2); positivity
  have hdG1 : c.deltaGE < 1 := by
    change p.delta / (2 * c.T1 * c.T2) < 1
    exact (div_lt_one (by positivity)).mpr (by linarith)
  have hbG : 0 < c.betaGE := by change 0 < p.beta / (2 * c.T1 * c.T2); positivity
  have hbG1 : c.betaGE < 1 := by
    change p.beta / (2 * c.T1 * c.T2) < 1
    exact (div_lt_one (by positivity)).mpr (by linarith)
  have ho : OraclePrivacyBounds n c.oracle :=
    public_oracle_privacy_bounds hn heG heG1 hdG hdG1 hbG hbG1
  have hu : OracleUtilityBounds n c.oracle :=
    public_oracle_utility_bounds hn heG heG1 hdG hdG1 hbG hbG1
  have hB : n * U ≤ c.B := by
    have ht := hu.tau_pos
    have hl : 0 < c.oracle.lam := by linarith [ho.lam_lower]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hU0 : 0 ≤ U := by linarith
    have hterm : 0 ≤ c.oracle.lam * n * Real.log n := by positivity
    change n * U ≤ 16 * (c.oracle.tau1 + c.oracle.lam * n * Real.log n + n * U)
    nlinarith [mul_nonneg hn0 hU0]
  refine ⟨ho, ?_, he2, hb2, hb21, rfl, hbG.le, rfl, rfl, hB, le_refl _⟩
  intro w h hw hh
  exact lemma20 n hn U c.epsGE c.deltaGE c.betaGE p.gamma (by linarith) heG heG1 hdG hdG1
    hbG hbG1 hγ (by linarith) w h hw hh

/-- Specializations retained for callers using the main theorem's parameter range. -/
theorem runConfig_inner_utility_bounds {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U)
    (p : Parameters) (hp : p.Valid) :
    InnerUtilityBounds n U p (runConfig n U p utilityConstants) := by
  exact runConfig_inner_utility_bounds_general hn hU p hp.iterationValid

end DPCut
