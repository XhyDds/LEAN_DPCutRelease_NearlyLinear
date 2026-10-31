import DPCut.CCErrorBound
import DPCut.ExternalApplicationContracts
import DPCut.MaxKApplication

/-! The statistical CC reduction with explicit external private-baseline and
nonprivate approximation contracts. Internal release and rounding are proved. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut

abbrev CCBaselineFamily := ∀ ε : ℝ, 0 < ε →
  PrivateCCBaselineContract (ε / 2) (fun n => (n : ℝ)⁻¹ ^ 10 / 2)

/-- A single error bound for all cluster bounds, source algorithms and success
probabilities, once the cited baseline and accuracy/privacy parameters are fixed. -/
theorem private_cc_reduction {ε ξ ρ : ℝ} (hε : 0 < ε) (hξ : 0 < ξ) (hρ : 1 ≤ ρ)
    (base : PrivateCCBaselineContract (ε / 2) (fun n => (n : ℝ)⁻¹ ^ 10 / 2)) :
    ∃ C Cfail : ℝ, ∃ exponent : ℕ, 0 < C ∧ 0 < Cfail ∧
    ∀ s : ℝ, 0 < s → s ≤ 1 →
    ∀ clusters : ℕ → ℕ, (∀ n, 2 ≤ n → 1 ≤ clusters n) →
    ∀ algorithm : (n : ℕ) → Kernel (Weights n) (Partition n),
    (∀ n, IsMarkovKernel (algorithm n)) →
    (∀ n, 2 ≤ n → ∀ w, IsUnweighted w →
      HighProbability (algorithm n w) (1 - s) (fun π => clusterCount π ≤ clusters n ∧
        ccCost w π ≤ ρ * ccOptimumK w (clusters n))) →
    PrivateCCGuarantee C Cfail ε (ρ + ξ) exponent clusters := by
  obtain ⟨γ, η, hγ, hγ4, hη, hη1, hθ, hratio⟩ := cc_slack_choice base.ratio_ge_one hρ hξ
  obtain ⟨C, d, hC, herror⟩ := cc_total_error_bound base.logDegree hγ hγ4 hη hε
    (by linarith : 0 ≤ ρ) hθ base.additiveCoefficient_pos
  refine ⟨C, 4, d, hC, by norm_num, ?_⟩
  intro s hs hs1 clusters hk algorithm hmarkov happrox n hn
  let p := ccParameters n γ ε
  have hp : p.Valid := ccParameters_valid hn hγ hγ4 hε
  let τ := (n : ℝ)⁻¹ ^ 10
  have hτ : 0 < τ := (inverse_tenth_small hn).1
  have hτ1 : τ < 1 := by linarith [(inverse_tenth_small hn).2]
  obtain ⟨seed, hseed⟩ := partitions_le_nonempty (by omega : 0 < n) (hk n hn)
  let t := ⌈Real.log (1 / τ) / s⌉₊
  letI := hmarkov n
  letI := base.markov n
  let K := amplifiedCC (algorithm n) (clusters n) t seed
  have hK : ∀ w, IsUnweighted w → HighProbability (K w) τ (fun π => clusterCount π ≤ clusters n ∧
      ccCost w π ≤ ρ * ccOptimumK w (clusters n)) := by
    intro w hw
    exact amplifiedCC_success (algorithm n) seed hseed w hs hs1 hτ (happrox n hn w hw) t
      (Nat.le_ceil _)
  refine ⟨ccPrivateKernel hn p hp (base.kernel n) K, inferInstance, ?_, fun w hw => ?_⟩
  · apply DP.mono (ccPrivateKernel_private hn p hp (base.kernel n) K
      (half_pos hε).le (by positivity : 0 ≤ (n : ℝ)⁻¹ ^ 10 / 2) (base.privacy n))
    · change ε / 2 + min (ε / 2) 1 ≤ ε
      linarith [min_le_left (ε / 2) 1]
    · change (n : ℝ)⁻¹ ^ 10 / 2 + (n : ℝ)⁻¹ ^ 10 / 2 ≤ (n : ℝ)⁻¹ ^ 10
      linarith
  · have hbase := base.approximation n hn w hw
    have hu := ccPrivateKernel_utility hn (hk n hn) p hp (base.kernel n) K hw.bounded
      (by linarith [base.ratio_ge_one] : 0 ≤ base.ratio) hη hη1 hτ hτ1 hτ.le
      (by linarith : 0 ≤ ρ) (by positivity : 0 ≤ (n : ℝ)⁻¹ ^ 2) hθ hbase hK
    have hfail : (n : ℝ)⁻¹ ^ 2 + (p.beta + (τ + τ)) ≤ 4 / (n : ℝ) ^ 2 := by
      have hh := inverse_tenth_le_inverse_square hn
      change (n : ℝ)⁻¹ ^ 2 + ((n : ℝ)⁻¹ ^ 10 + ((n : ℝ)⁻¹ ^ 10 + (n : ℝ)⁻¹ ^ 10)) ≤ _
      rw [inv_pow, inv_eq_one_div]
      simp only [div_eq_mul_inv, one_mul] at hh ⊢
      linarith
    apply (hu.weaken hfail).mono _ (Set.toFinite _ |>.measurableSet)
    intro π hπ
    refine ⟨hπ.1, ?_⟩
    have hopt : 0 ≤ ccOptimumK w (clusters n) := ccOptimumK_nonneg (by omega) (hk n hn) hw.bounded
    have hr := mul_le_mul_of_nonneg_right hratio hopt
    have he := herror n hn
    have hcost := hπ.2
    change ccCost w π ≤
      ρ * (1 + ccTransferTheta base.ratio γ η) / (1 - ccTransferTheta base.ratio γ η) * ccOptimumK w (clusters n) +
      (ρ + 1) / (1 - ccTransferTheta base.ratio γ η) *
        ccTransferError n γ η (base.additiveCoefficient * n * Real.log n ^ base.logDegree)
          ((2 : ℝ) ^ 126 * mainError n (ccParameters n γ ε)) ((n : ℝ)⁻¹ ^ 10) at hcost
    linarith

/-- Theorem 30, relative only to the explicitly cited private baseline. The
nonprivate approximation is already an argument of the original target. -/
theorem theorem30 (baseline : CCBaselineFamily) : CCBlackBoxStatement := by
  intro ρ ξ ε hρ hξ hε
  obtain ⟨C, Cfail, d, hC, hCfail, hreduce⟩ :=
    private_cc_reduction hε hξ hρ (baseline ε hε)
  refine ⟨C, Cfail, d, hC, hCfail, ?_⟩
  intro p₀ hp₀ algorithm hmarkov happrox
  let s := min p₀ (1 / 2 : ℝ)
  have hs : 0 < s := lt_min hp₀ (by norm_num)
  have hs1 : s ≤ 1 := (min_le_right _ _).trans (by norm_num)
  apply hreduce s hs hs1 id (fun n hn => by dsimp; omega)
    algorithm hmarkov
  intro n hn w hw
  letI := hmarkov n
  have hh := (happrox n hn w hw).weaken (show 1 - p₀ ≤ 1 - s by
    exact sub_le_sub_left (min_le_left _ _) 1)
  apply hh.mono _ (Set.toFinite _ |>.measurableSet)
  intro π hπ
  exact ⟨clusterCount_le_n π, by simpa only [id_eq, ccOptimumK_n] using hπ⟩

end DPCut
