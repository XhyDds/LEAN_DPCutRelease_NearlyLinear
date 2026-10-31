import DPCut.Theorem1
import DPCut.ApplicationPostprocessing

/-! Explicit inverse-polynomial failure and soft-O calibration for Appendix C. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut

def applicationParameters (n : ℕ) (η ε : ℝ) : Parameters :=
  ⟨η, min ε 1, (n : ℝ)⁻¹ ^ 10, (n : ℝ)⁻¹ ^ 10⟩

lemma inverse_tenth_small {n : ℕ} (hn : 2 ≤ n) :
    0 < (n : ℝ)⁻¹ ^ 10 ∧ (n : ℝ)⁻¹ ^ 10 < 1 / 10 := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  refine ⟨by positivity, ?_⟩
  have hh : (n : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hn2
  have hp := pow_le_pow_left₀ (inv_nonneg.mpr hn0.le) hh 10
  norm_num at hp ⊢
  linarith

lemma applicationParameters_valid {n : ℕ} (hn : 2 ≤ n) {η ε : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1 / 4) (hε : 0 < ε) : (applicationParameters n η ε).Valid := by
  have hi := inverse_tenth_small hn
  exact ⟨hη, hη1, lt_min hε (by norm_num), min_le_right _ _, hi.1, hi.2, hi.1, hi.2⟩

def applicationLogCoefficient (η ε : ℝ) : ℝ :=
  21 + |Real.log (η * min ε 1)| / Real.log 2

lemma applicationLogCoefficient_pos (η ε : ℝ) : 0 < applicationLogCoefficient η ε := by
  have hh : 0 ≤ |Real.log (η * min ε 1)| / Real.log 2 :=
    div_nonneg (abs_nonneg _) (Real.log_nonneg (by norm_num))
  dsimp [applicationLogCoefficient]
  linarith

lemma application_log_bound {n : ℕ} (hn : 2 ≤ n) {η ε : ℝ}
    (hη : 0 < η) (hε : 0 < ε) :
    logFactor n 1 (applicationParameters n η ε) ≤ applicationLogCoefficient η ε * Real.log n := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have he : 0 < min ε 1 := lt_min hε (by norm_num)
  have hnz := hn0.ne'
  have hez := he.ne'
  have hηz := hη.ne'
  have heq : logFactor n 1 (applicationParameters n η ε) =
      21 * Real.log n - Real.log (η * min ε 1) := by
    simp only [logFactor, applicationParameters, mul_one]
    rw [Real.log_div hnz (by positivity)]
    rw [Real.log_mul (by positivity) hez, Real.log_mul (by positivity) hηz,
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_inv,
      Real.log_mul hηz hez]
    ring
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh := mul_le_mul_of_nonneg_left hlog
    (div_nonneg (abs_nonneg (Real.log (η * min ε 1))) hlog2.le)
  rw [div_mul_cancel₀ _ hlog2.ne'] at hh
  rw [heq]
  dsimp [applicationLogCoefficient]
  nlinarith [neg_le_abs (Real.log (η * min ε 1))]

lemma application_error_bound {n : ℕ} (hn : 2 ≤ n) {η ε : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1 / 4) (hε : 0 < ε) :
    mainError n (applicationParameters n η ε) ≤
      (applicationLogCoefficient η ε ^ 7 / (η * min ε 1)) * n * Real.log n ^ 7 := by
  have hp := applicationParameters_valid hn hη hη1 hε
  have he : 0 < min ε 1 := hp.2.2.1
  have hlog0 : 0 ≤ logFactor n 1 (applicationParameters n η ε) := by
    have hh := (core_log_bounds hn (le_refl (1 : ℝ)) _ hp).one_le
    linarith
  have hpow := pow_le_pow_left₀ hlog0 (application_log_bound hn hη hε) 7
  have hh := mul_le_mul_of_nonneg_left hpow
    (by positivity : 0 ≤ (n : ℝ) / (η * min ε 1))
  change (n : ℝ) / (η * min ε 1) * logFactor n 1 (applicationParameters n η ε) ^ 7 ≤ _
  convert hh using 1
  ring

theorem application_release {η ε : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 4) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, 2 ≤ n →
      ∃ M : Kernel (Weights n) (Weights n), IsMarkovKernel M ∧ GraphValued M ∧
        EdgeDP M ε ((n : ℝ)⁻¹ ^ 10) ∧ ∀ w, Nonnegative w →
          HighProbability (M w) ((n : ℝ)⁻¹ ^ 10)
            (fun h => AllCuts w h η (C * n * Real.log n ^ 7)) := by
  obtain ⟨CA, hCA, hmain⟩ := theorem1_statistical
  let C := CA * (applicationLogCoefficient η ε ^ 7 / (η * min ε 1))
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos hCA (div_pos (pow_pos (applicationLogCoefficient_pos η ε) _)
      (mul_pos hη (lt_min hε (by norm_num))))
  refine ⟨C, hC, fun n hn => ?_⟩
  obtain ⟨M, hM, hg, hDP, hutility⟩ := hmain n hn _ (applicationParameters_valid hn hη hη1 hε)
  letI := hM
  refine ⟨M, hM, hg, DP.mono hDP (min_le_left _ _) (le_refl _), fun w hw => ?_⟩
  apply (hutility w hw).mono (M w) (measurableSet_allCuts measurable_const measurable_id _ _)
  intro h hh S
  have he := mul_le_mul_of_nonneg_left (application_error_bound hn hη hη1 hε) hCA.le
  change CA * mainError n (applicationParameters n η ε) ≤ _ at he
  have he' : CA * mainError n (applicationParameters n η ε) ≤ C * n * Real.log n ^ 7 := by
    convert he using 1
    dsimp [C]; ring
  exact (hh S).trans (add_le_add_left he' _)

end DPCut
