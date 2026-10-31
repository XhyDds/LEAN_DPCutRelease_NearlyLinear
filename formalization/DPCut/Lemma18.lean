import DPCut.InnerLoopPrivacy
import DPCut.OuterLoopPrivacy
import DPCut.MainPrivacyCalibration

/-!
Lemma 18 (`lem:main-privacy`) of the root manuscript: the original CutRelease
law is `(epsilon, delta)`-differentially private. All composition, sampling,
measurability, support, and calibration obligations are discharged below.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut

theorem cutRelease_private {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U)
    (p : Parameters) (hp : p.PrivacyValid) (w w' : Weights n) (hw : Adjacent w w') :
    Indistinguishable (cutReleaseLaw U p privacyConstants w)
      (cutReleaseLaw U p privacyConstants w') p.epsilon p.delta := by
  obtain ⟨hγ, hγ1, hε, hε1, hδ, hδ1, hβ, hβ1⟩ := hp
  let c := runConfig n U p privacyConstants
  have hT1 : 0 < c.T1 := main_outer_horizon_pos hn hU
  have hT2 : 0 < c.T2 := by change 0 < 1 + ⌈64 * (1 + p.gamma) ^ 2 * Real.log n / p.gamma ^ 2⌉₊; omega
  have hT1R : (0 : ℝ) < c.T1 := by exact_mod_cast hT1
  have hT2R : (0 : ℝ) < c.T2 := by exact_mod_cast hT2
  have hT11 : (1 : ℝ) ≤ c.T1 := by exact_mod_cast hT1
  have hT21 : (1 : ℝ) ≤ c.T2 := by exact_mod_cast hT2
  have hnum := main_composition_budget hT1 hT2 hε hε1 hδ hδ1
  change 0 < c.epsGE ∧ c.epsGE < 1 ∧ 0 < p.delta / (2 * c.T1) ∧
    p.delta / (2 * c.T1) < 1 ∧
    advancedEpsilon c.T2 c.epsGE (p.delta / (2 * c.T1)) ≤ c.eps2 at hnum
  obtain ⟨heG, heG1, hdslack, hdslack1, hbudget⟩ := hnum
  have he2 : 0 < c.eps2 := by change 0 < p.epsilon / (2 * c.T1); positivity
  have hden : (2 : ℝ) ≤ 2 * c.T1 * c.T2 := by
    have hh := mul_le_mul hT11 hT21 (by norm_num) hT1R.le
    nlinarith only [hh]
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
  have hK : 0 < c.oracle.K := by
    change 0 < ⌈8192 * Real.log (n / c.betaGE)⌉₊
    apply Nat.ceil_pos.mpr
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hh : 0 < Real.log (n / c.betaGE) :=
      Real.log_pos ((one_lt_div hbG).mpr (by linarith))
    positivity
  have hdelta : c.T2 * c.deltaGE + p.delta / (2 * c.T1) = p.delta / c.T1 := by
    change c.T2 * (p.delta / (2 * c.T1 * c.T2)) + p.delta / (2 * c.T1) = p.delta / c.T1
    field_simp; ring
  have hinner (v v' : Weights n) (hv : Adjacent v v') (M : ℝ) (h : Weights n) :
      Indistinguishable (innerLoop p c v M c.T2 h) (innerLoop p c v' M c.T2 h)
        c.eps2 (p.delta / c.T1) := by
    apply (innerLoop_privacy hn p c ho v v' M c.T2 h heG hdG.le hdG1 hdslack hdslack1
      (fun h => aggregate_privacy_calibrated hn c.oracle ho heG heG1 hdG hdG1 hγ hγ1 hK
        rfl rfl v v' h hv)).mono hbudget hdelta.le
  have hres := outerLoop_privacy hn p c ho he2 he2.le (by positivity : 0 ≤ p.delta / c.T1)
    hinner w w' hw c.T1 1 0 (by simp [IsMask, Bounded])
  have he_total : (c.T1 : ℝ) * (c.eps2 + c.eps2) = p.epsilon := by
    change (c.T1 : ℝ) * (p.epsilon / (2 * c.T1) + p.epsilon / (2 * c.T1)) = p.epsilon
    field_simp; ring
  have hd_total : (c.T1 : ℝ) * (p.delta / c.T1) = p.delta := by field_simp
  rw [he_total, hd_total] at hres
  exact hres

/-- Lemma 18, proving the pre-existing main privacy statement with the same constants
used for Lemma 17. No composition theorem is assumed. -/
theorem lemma18 : MainPrivacyStatement privacyConstants := by
  intro n hn U hU p hp w w' hw s hs
  exact (cutRelease_private hn hU p hp w w' hw.2.2).1 s hs

end DPCut
