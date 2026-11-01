import DPCut.AppendixRuntime
import DPCut.CCErrorBound
import DPCut.Theorem30

/-! Combined application guarantees. Each realization explicitly identifies the
law of its costed program with the private kernel. Assigned-cost coefficients are
uniform in n and the input graph; approximation constants retain the stronger
uniformity specified in the corresponding statistical statements. These are
bounds in the permissive cost model, not operational running-time certificates. -/
set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DPCut

/-- The specified costed program realizes this kernel within the bound on every input. -/
def RealizedWithin {n : ℕ} {Y : Type} [MeasurableSpace Y]
    (M : Kernel (Weights n) Y) (bound : ℝ≥0∞) (run : Weights n → CostedLaw Y) : Prop :=
  ∀ w, (run w).law = M w ∧ (run w).cost ≤ bound

/-- `PrivateCCGuarantee` together with a polynomial realization of the same law. -/
def ImplementedCCGuarantee (hLSW : LSWStatement) (base alg : PolynomialGraphAlgorithm Partition)
    (C Cfail ε ratio : ℝ) (exponent : ℕ) (clusters : ℕ → ℕ) : Prop :=
  ∃ Ctime : ℝ, 0 < Ctime ∧ ∃ degree : ℕ,
  ∀ n (hn : 2 ≤ n), ∃ (p : Parameters) (hp : p.Valid) (t : ℕ) (seed : Partition n)
    (M : Kernel (Weights n) (Partition n)), IsMarkovKernel M ∧
    RealizedWithin M (ENNReal.ofReal (Ctime * (1+(n:ℝ))^degree))
      (LSWApplications.costedCC (LSWApplications.family hLSW) hn p hp (base.run n)
        (costedCCSolver (alg.run n) (clusters n) t seed)) ∧
    DP (fun w w' => IsUnweighted w ∧ IsUnweighted w' ∧ Adjacent w w') M ε ((n:ℝ)⁻¹^10) ∧
    ∀ w, IsUnweighted w → HighProbability (M w) (Cfail/(n:ℝ)^2)
      (fun π => clusterCount π ≤ clusters n ∧
        ccCost w π ≤ ratio * ccOptimumK w (clusters n) + C*n*Real.log n^exponent)

/-- `PrivateMaxKGuarantee` with a polynomial realization of the same law. -/
def ImplementedMaxKGuarantee (hLSW : LSWStatement) (alg : PolynomialGraphAlgorithm Partition)
    (C Cfail ε ratio : ℝ) (exponent k : ℕ) : Prop :=
  ∃ Ctime : ℝ, 0 < Ctime ∧ ∃ degree : ℕ,
  ∀ n (hn : 2 ≤ n), ∃ (p : Parameters) (hp : p.Valid) (t : ℕ) (seed : Partition n)
    (M : Kernel (Weights n) (Partition n)), IsMarkovKernel M ∧
    RealizedWithin M (ENNReal.ofReal (Ctime * (1+(n:ℝ))^degree))
      (LSWApplications.costedPostprocess (LSWApplications.family hLSW) hn p hp
        (costedMaxKSolver (alg.run n) t seed)) ∧
    EdgeDP M ε ((n:ℝ)⁻¹^10) ∧
    ∀ w, Nonnegative w → HighProbability (M w) (Cfail/(n:ℝ)^2)
      (fun π => clusterCount π ≤ k ∧
        ratio * maxKOptimum w k - C*n*Real.log n^exponent ≤ partitionCut w π)

namespace LSWApplications

/-- The near-linear error constant is uniform in the cluster bound, source
algorithm, and its success probability. The runtime may depend on that algorithm. -/
theorem private_cc_reduction (hLSW : LSWStatement) {ε ξ ρ : ℝ}
    (hε : 0 < ε) (hξ : 0 < ξ) (hρ : 1 ≤ ρ)
    (base : PrivateCCBaselineContract (ε/2) (fun n => (n:ℝ)⁻¹^10/2)) :
    ∃ C Cfail : ℝ, ∃ exponent : ℕ, 0 < C ∧ 0 < Cfail ∧
    ∀ s : ℝ, 0 < s → s ≤ 1 →
    ∀ clusters : ℕ → ℕ, (∀ n, 2 ≤ n → 1 ≤ clusters n) →
    ∀ alg : PolynomialGraphAlgorithm Partition,
    (∀ n, 2 ≤ n → ∀ w, IsUnweighted w →
      HighProbability (alg.kernel n w) (1-s) (fun π => clusterCount π ≤ clusters n ∧
        ccCost w π ≤ ρ * ccOptimumK w (clusters n))) →
    ImplementedCCGuarantee hLSW base.toPolynomialGraphAlgorithm alg C Cfail ε (ρ+ξ) exponent clusters := by
  obtain ⟨γ, η, hγ, hγ4, hη, hη1, hθ, hratio⟩ := cc_slack_choice base.ratio_ge_one hρ hξ
  obtain ⟨C, d, hC, herror⟩ := cc_total_error_bound_of_constant ((2:ℝ)^138) (by positivity)
    base.logDegree hγ hγ4 hη hε (by linarith : 0 ≤ ρ) hθ base.additiveCoefficient_pos
  refine ⟨C, 4, d, hC, by norm_num, ?_⟩
  intro s hs hs1 clusters hk alg happrox
  let seed : ∀ n, Partition n := fun n =>
    if hn : 2 ≤ n then Classical.choose (partitions_le_nonempty (by omega : 0<n) (hk n hn)) else id
  have hseed (n : ℕ) (hn : 2 ≤ n) : clusterCount (seed n) ≤ clusters n := by
    simpa only [seed, dif_pos hn] using
      Classical.choose_spec (partitions_le_nonempty (by omega : 0<n) (hk n hn))
  obtain ⟨Ct, hCt, dt, htime⟩ := cc_reduction_runtime hLSW base.toPolynomialGraphAlgorithm alg
    hγ hγ4 hε hs clusters seed
  refine ⟨Ct, hCt, dt, fun n hn => ?_⟩
  let p := ccParameters n γ ε
  have hp : p.Valid := ccParameters_valid hn hγ hγ4 hε
  let τ := (n:ℝ)⁻¹^10
  have hτ : 0 < τ := (inverse_tenth_small hn).1
  have hτ1 : τ < 1 := by linarith [(inverse_tenth_small hn).2]
  let t := ⌈Real.log (1/τ)/s⌉₊
  letI := alg.markov n
  letI := base.markov n
  let K := amplifiedCC (alg.kernel n) (clusters n) t (seed n)
  have hK : ∀ w, IsUnweighted w → HighProbability (K w) τ
      (fun π => clusterCount π ≤ clusters n ∧ ccCost w π ≤ ρ * ccOptimumK w (clusters n)) := by
    intro w hw
    exact amplifiedCC_success (alg.kernel n) (seed n) (hseed n hn) w hs hs1 hτ
      (happrox n hn w hw) t (Nat.le_ceil _)
  refine ⟨p, hp, t, seed n, ccPrivateKernel (family hLSW) hn p hp (base.kernel n) K,
    inferInstance, (fun w => htime n hn w), ?_, fun w hw => ?_⟩
  · apply DP.mono (ccPrivateKernel_private (family hLSW) hn p hp (base.kernel n) K
      (half_pos hε).le (by positivity : 0 ≤ (n:ℝ)⁻¹^10/2) (base.privacy n))
    · change ε/2 + min (ε/2) 1 ≤ ε
      linarith [min_le_left (ε/2) 1]
    · change (n:ℝ)⁻¹^10/2 + (n:ℝ)⁻¹^10/2 ≤ (n:ℝ)⁻¹^10
      linarith
  · have hu := ccPrivateKernel_utility (family hLSW) hn (hk n hn) p hp (base.kernel n) K hw.bounded
      (by linarith [base.ratio_ge_one] : 0 ≤ base.ratio) hη hη1 hτ hτ1 hτ.le
      (by linarith : 0 ≤ ρ) (by positivity : 0 ≤ (n:ℝ)⁻¹^2) hθ (base.approximation n hn w hw) hK
    have hfail : (n:ℝ)⁻¹^2 + (p.beta + (τ+τ)) ≤ 4/(n:ℝ)^2 := by
      have hh := inverse_tenth_le_inverse_square hn
      change (n:ℝ)⁻¹^2 + ((n:ℝ)⁻¹^10 + ((n:ℝ)⁻¹^10 + (n:ℝ)⁻¹^10)) ≤ _
      rw [inv_pow, inv_eq_one_div]
      simp only [div_eq_mul_inv, one_mul] at hh ⊢
      linarith
    apply (hu.weaken hfail).mono _ (Set.toFinite _ |>.measurableSet)
    intro π hπ
    refine ⟨hπ.1, ?_⟩
    have hr := mul_le_mul_of_nonneg_right hratio (ccOptimumK_nonneg (by omega) (hk n hn) hw.bounded)
    have he := herror n hn
    have hcost := hπ.2
    change ccCost w π ≤
      ρ*(1+ccTransferTheta base.ratio γ η)/(1-ccTransferTheta base.ratio γ η)*ccOptimumK w (clusters n) +
      (ρ+1)/(1-ccTransferTheta base.ratio γ η)*ccTransferError n γ η
        (base.additiveCoefficient*n*Real.log n^base.logDegree)
        ((2:ℝ)^138*mainError n (ccParameters n γ ε)) ((n:ℝ)⁻¹^10) at hcost
    linarith

/-- Theorem 30, now including assigned-cost bounds for the specified approximate program. -/
theorem theorem30 (hLSW : LSWStatement) (baseline : CCBaselineFamily)
    {ρ ξ ε : ℝ} (hρ : 1 ≤ ρ) (hξ : 0 < ξ) (hε : 0 < ε) :
    ∃ C Cfail : ℝ, ∃ exponent : ℕ, 0 < C ∧ 0 < Cfail ∧
    ∀ s : ℝ, 0 < s → ∀ alg : CCApproximationContract ρ s,
      ImplementedCCGuarantee hLSW (baseline ε hε).toPolynomialGraphAlgorithm
        alg.toPolynomialGraphAlgorithm C Cfail ε (ρ+ξ) exponent id := by
  obtain ⟨C, Cf, d, hC, hCf, h⟩ := private_cc_reduction hLSW hε hξ hρ (baseline ε hε)
  refine ⟨C, Cf, d, hC, hCf, fun s hs alg => ?_⟩
  apply h (min s (1/2)) (lt_min hs (by norm_num))
    ((min_le_right _ _).trans (by norm_num)) id (fun n hn => by dsimp; omega) alg.toPolynomialGraphAlgorithm
  intro n hn w hw
  letI := alg.markov n
  apply ((alg.approximation n hn w hw).weaken (show 1-s ≤ 1-min s (1/2) by
    linarith [min_le_left s (1/2)])).mono _ (Set.toFinite _ |>.measurableSet)
  intro π hπ
  exact ⟨clusterCount_le_n π, by simpa only [id_eq, ccOptimumK_n] using hπ⟩

/-- Corollary 2 with the cited approximation and a polynomial realization. -/
theorem private_correlation_clustering (hLSW : LSWStatement) (baseline : CCBaselineFamily)
    (alg : CCApproximationContract (5547/4000) 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ C Cfail : ℝ, ∃ exponent : ℕ, 0 < C ∧ 0 < Cfail ∧
      ImplementedCCGuarantee hLSW (baseline ε hε).toPolynomialGraphAlgorithm
        alg.toPolynomialGraphAlgorithm C Cfail ε (1387/1000) exponent id := by
  obtain ⟨C, Cf, d, hC, hCf, h⟩ := theorem30 hLSW baseline
    (ρ:=5547/4000) (ξ:=1/4000) (by norm_num) (by norm_num) hε
  refine ⟨C, Cf, d, hC, hCf, ?_⟩
  convert h 1 (by norm_num) alg using 1
  norm_num

/-- Corollary 31: error constants precede k, while cost coefficients may depend on k. -/
theorem corollary31 (hLSW : LSWStatement) (baseline : CCBaselineFamily)
    (ptas : ∀ k : ℕ, 2 ≤ k → ∀ slack : ℝ, 0 < slack → FixedKCCContract k slack (1/2))
    {ξ ε : ℝ} (hξ : 0 < ξ) (hε : 0 < ε) :
    ∃ C Cfail : ℝ, ∃ exponent : ℕ, 0 < C ∧ 0 < Cfail ∧
      ∀ k : ℕ, ∀ hk : 2 ≤ k, ImplementedCCGuarantee hLSW (baseline ε hε).toPolynomialGraphAlgorithm
        (ptas k hk (ξ/2) (half_pos hξ)).toPolynomialGraphAlgorithm C Cfail ε (1+ξ) exponent (fun _ => k) := by
  obtain ⟨C, Cf, d, hC, hCf, h⟩ := private_cc_reduction hLSW hε (half_pos hξ)
    (show 1 ≤ 1+ξ/2 by linarith) (baseline ε hε)
  refine ⟨C, Cf, d, hC, hCf, fun k hk => ?_⟩
  let alg := ptas k hk (ξ/2) (half_pos hξ)
  have hu := h (1/2) (by norm_num) (by norm_num) (fun _ => k) (fun _ _ => by dsimp; omega)
    alg.toPolynomialGraphAlgorithm (fun n hn w hw => alg.approximation n hn w hw)
  convert hu using 1
  ring

/-- Theorem 32 with a costed realization. The additive constants are uniform in
k and in the expected approximation ratio supplied by the external algorithm. -/
theorem theorem32 (hLSW : LSWStatement) {ξ ε : ℝ} (hξ : 0 < ξ) (hε : 0 < ε) :
    ∃ C Cfail : ℝ, ∃ exponent : ℕ, 0 < C ∧ 0 < Cfail ∧
    ∀ k : ℕ, 2 ≤ k → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
    ∀ alg : MaxKCutContract k ρ,
      ImplementedMaxKGuarantee hLSW alg.toPolynomialGraphAlgorithm C Cfail ε (ρ-ξ) exponent k := by
  let s := min (ξ/3) (1/4)
  have hs : 0 < s := lt_min (by positivity) (by norm_num)
  have hs4 : s ≤ 1/4 := min_le_right _ _
  have hsξ : 3*s ≤ ξ := by have := min_le_left (ξ/3) (1/4:ℝ); dsimp [s]; linarith
  let C := (2:ℝ)^178 * (applicationLogCoefficient s ε^7/(s*min ε 1))
  have hC : 0 < C := by
    have := applicationLogCoefficient_pos s ε
    have := lt_min hε (by norm_num : (0:ℝ)<1)
    dsimp [C]; positivity
  refine ⟨4*C, 2, 7, by positivity, by norm_num, ?_⟩
  intro k hk ρ hρ hρ1 alg
  let seed : ∀ n, Partition n := fun n =>
    if hn : 2 ≤ n then Classical.choose (partitions_le_nonempty (by omega : 0<n) (show 1≤k by omega)) else id
  have hseed (n : ℕ) (hn : 2 ≤ n) : clusterCount (seed n) ≤ k := by
    simpa only [seed, dif_pos hn] using
      Classical.choose_spec (partitions_le_nonempty (by omega : 0<n) (show 1≤k by omega))
  obtain ⟨Ct, hCt, dt, htime⟩ := max_k_reduction_runtime hLSW alg.toPolynomialGraphAlgorithm
    hs hs4 hε hs seed
  refine ⟨Ct, hCt, dt, fun n hn => ?_⟩
  let p := applicationParameters n s ε
  have hp : p.Valid := applicationParameters_valid hn hs hs4 hε
  let τ := (n:ℝ)⁻¹^10
  have hτ : 0 < τ := (inverse_tenth_small hn).1
  let t := ⌈Real.log (1/τ)/s⌉₊
  letI := alg.markov n
  let K := amplifiedMaxK (alg.kernel n) t (seed n)
  let ρ' := max (ρ-s) 0
  have hρ' : 0 ≤ ρ' := le_max_right _ _
  have hρ'1 : ρ' ≤ 1 := max_le (by linarith) (by norm_num)
  have hK : ∀ h, Nonnegative h → HighProbability (K h) τ
      (fun π => clusterCount π ≤ k ∧ ρ'*maxKOptimum h k ≤ partitionCut h π) := by
    intro h hh
    have hu := amplifiedMaxK_success (by omega) (by omega) (alg.kernel n) hh hs
      (by linarith : s ≤ 1) hτ (alg.feasible n hn h hh) (alg.approximation n hn h hh)
      t (Nat.le_ceil _) (seed n) (hseed n hn)
    apply hu.mono _ (Set.toFinite _ |>.measurableSet)
    intro π hπ
    refine ⟨hπ.1, ?_⟩
    by_cases hnon : 0 ≤ ρ-s
    · simpa only [ρ', max_eq_left hnon] using hπ.2
    · simp only [ρ', max_eq_right (le_of_not_ge hnon), zero_mul]
      exact labelCut_nonneg hh π
  let M : Kernel (Weights n) (Partition n) :=
    ⟨fun w => (LSWRelease.kernel (family hLSW) hn p hp w).bind K,
      measurable_bind_kernel (LSWRelease.kernel (family hLSW) hn p hp).measurable
        (K.measurable.comp measurable_snd)⟩
  letI : IsMarkovKernel M := ⟨fun _ => probability_bind _ _ K.measurable⟩
  refine ⟨p, hp, t, seed n, M, inferInstance, (fun w => htime n hn w), ?_, fun w hw => ?_⟩
  · exact DP.mono (postprocess_private (family hLSW) hn p hp K) (min_le_left ε 1) (le_refl _)
  · have hu := max_k_utility (family hLSW) hn p hp K hk hρ' hρ'1 hτ.le hK w hw
    have hfail : p.beta+τ ≤ 2/(n:ℝ)^2 := by
      have hi := inverse_tenth_le_inverse_square hn
      change (n:ℝ)⁻¹^10+(n:ℝ)⁻¹^10 ≤ _
      convert add_le_add hi hi using 1
      ring
    apply (hu.weaken hfail).mono _ (Set.toFinite _ |>.measurableSet)
    intro π hπ
    refine ⟨hπ.1, ?_⟩
    have hslack : ρ-ξ ≤ ρ'*(1-s)/(1+s) :=
      (maxK_ratio_slack hs.le hρ1 hsξ).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left (ρ-s) 0)
          (by linarith : 0 ≤ 1-s)) (by positivity : 0 ≤ 1+s))
    have hr := mul_le_mul_of_nonneg_right hslack (maxKOptimum_nonneg (by omega) (by omega) hw (k:=k))
    have hcoef : 2*(ρ'+1)/(1+s) ≤ 4 := by
      apply (div_le_iff₀ (by positivity : 0 < 1+s)).mpr
      linarith
    have hE : (2:ℝ)^178 * mainError n p ≤ C*n*Real.log n^7 := by
      have he := mul_le_mul_of_nonneg_left (application_error_bound hn hs hs4 hε)
        (by positivity : (0:ℝ)≤2^178)
      convert he using 1
      dsimp [C, p]
      ring
    have hE0 : 0 ≤ (2:ℝ)^178 * mainError n p := by have := mainError_one_le hn hp; positivity
    have he := mul_le_mul hcoef hE hE0 (by norm_num : (0:ℝ)≤4)
    have hc := hπ.2
    change ρ'*(1-s)/(1+s)*maxKOptimum w k -
      (2*(ρ'+1)/(1+s))*((2:ℝ)^178*mainError n p) ≤ partitionCut w π at hc
    nlinarith

/-- Corollary 3, with the Goemans--Williamson contract and assigned-cost bound. -/
theorem private_max_cut (hLSW : LSWStatement) (gw : MaxKCutContract 2 (878/1000))
    {ξ ε : ℝ} (hξ : 0 < ξ) (hε : 0 < ε) :
    ∃ C Cfail : ℝ, ∃ exponent : ℕ, 0 < C ∧ 0 < Cfail ∧
      ImplementedMaxKGuarantee hLSW gw.toPolynomialGraphAlgorithm C Cfail ε (878/1000-ξ) exponent 2 := by
  obtain ⟨C, Cf, d, hC, hCf, h⟩ := theorem32 hLSW hξ hε
  exact ⟨C, Cf, d, hC, hCf, h 2 (by norm_num) (878/1000) (by norm_num) (by norm_num) gw⟩

/-- A measurable postprocessing kernel for the actual approximate release. -/
def postprocessKernel {n : ℕ} {Y : Type} [MeasurableSpace Y]
    (F : CuttingPlaneFamily) (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (K : Kernel (Weights n) Y) : Kernel (Weights n) Y :=
  ⟨fun w => (LSWRelease.kernel F hn p hp w).bind K,
    measurable_bind_kernel (LSWRelease.kernel F hn p hp).measurable
      (K.measurable.comp measurable_snd)⟩

instance postprocessKernel_markov {n : ℕ} {Y : Type} [MeasurableSpace Y]
    (F : CuttingPlaneFamily) (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (K : Kernel (Weights n) Y) [IsMarkovKernel K] :
    IsMarkovKernel (postprocessKernel F hn p hp K) :=
  ⟨fun _ => probability_bind _ _ K.measurable⟩

/-- The general constrained-cut transfer, including assigned-cost bounds uniformly over
all valid privacy and accuracy parameters. -/
theorem constrained_cut_general (hLSW : LSWStatement)
    (alg : PolynomialGraphAlgorithm (fun n => Finset (Fin n))) :
    ∃ Ctime : ℝ, 0 < Ctime ∧ ∃ degree : ℕ,
    ∀ n (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
      (S S' : Set (Finset (Fin n))), S.Nonempty →
    ∀ ρ τ : ℝ, 0 ≤ ρ → 0 ≤ τ →
    (∀ h, Nonnegative h → HighProbability (alg.kernel n h) τ
      (fun T => T ∈ S' ∧ cut h T ≤ ρ*constrainedOptimum h S)) →
    let M := postprocessKernel (family hLSW) hn p hp (alg.kernel n)
    EdgeDP M p.epsilon p.delta ∧
    RealizedWithin M (ENNReal.ofReal (Ctime*runtimeScale n p^degree))
      (costedPostprocess (family hLSW) hn p hp (alg.run n)) ∧
    ∀ w, Nonnegative w → HighProbability (M w) (p.beta+τ)
      (fun T => T ∈ S' ∧ cut w T ≤ ρ*(1+p.gamma)/(1-p.gamma)*constrainedOptimum w S +
        (ρ+1)/(1-p.gamma)*((2:ℝ)^178*mainError n p)) := by
  have hs : PolynomialRuntimeBound (fun n _ => ENNReal.ofReal
      (alg.coefficient*(1+(n:ℝ))^alg.degree)) := by
    convert (PolynomialRuntimeBound.constant alg.coefficient alg.coefficient_pos).mul
      (polynomial_vertices.pow alg.degree) using 1
    ext n p
    rw [ENNReal.ofReal_mul alg.coefficient_pos.le, ENNReal.ofReal_pow (by positivity)]
    simp [ENNReal.ofReal_add, add_comm]
  obtain ⟨Ct, hCt, d, htime⟩ := (LSWRelease.costBound_polynomial (family hLSW)).add hs
  refine ⟨Ct, hCt, d, fun n hn p hp S S' hS ρ τ hρ hτ hK => ?_⟩
  letI := alg.markov n
  refine ⟨postprocess_private (family hLSW) hn p hp (alg.kernel n),
    (fun w => ⟨?_, ?_⟩),
    fun w hw => constrained_utility (family hLSW) hn p hp (alg.kernel n) hS hρ hτ hK w hw⟩
  · exact costedPostprocess_law (family hLSW) hn p hp (alg.run n) (alg.kernel n) (alg.realizes n) w
  · exact (costedPostprocess_cost (family hLSW) hn p hp (alg.run n) (alg.cost_le n) w).trans
      (htime n hn p hp)

/-- Theorem 34 at the application privacy budgets, with its exact transfer
factors, calibrated near-linear additive error, and a polynomial realization. -/
theorem theorem34 (hLSW : LSWStatement)
    (alg : PolynomialGraphAlgorithm (fun n => Finset (Fin n)))
    {η ε : ℝ} (hη : 0 < η) (hη4 : η ≤ 1/4) (hε : 0 < ε) :
    ∃ CA Ctime : ℝ, 0 < CA ∧ 0 < Ctime ∧ ∃ degree : ℕ,
    ∀ n (hn : 2 ≤ n) (S S' : Set (Finset (Fin n))), S.Nonempty →
    ∀ ρ τ : ℝ, 0 ≤ ρ → 0 ≤ τ →
    (∀ h, Nonnegative h → HighProbability (alg.kernel n h) τ
      (fun T => T ∈ S' ∧ cut h T ≤ ρ*constrainedOptimum h S)) →
    let p := applicationParameters n η ε
    let M := postprocessKernel (family hLSW) hn p (applicationParameters_valid hn hη hη4 hε) (alg.kernel n)
    EdgeDP M ε ((n:ℝ)⁻¹^10) ∧
    RealizedWithin M (ENNReal.ofReal (Ctime*(1+(n:ℝ))^degree))
      (costedPostprocess (family hLSW) hn p (applicationParameters_valid hn hη hη4 hε) (alg.run n)) ∧
    ∀ w, Nonnegative w → HighProbability (M w) ((n:ℝ)⁻¹^10+τ)
      (fun T => T ∈ S' ∧ cut w T ≤ ρ*(1+η)/(1-η)*constrainedOptimum w S +
        (ρ+1)/(1-η)*(CA*n*Real.log n^7)) := by
  let CA := (2:ℝ)^178*(applicationLogCoefficient η ε^7/(η*min ε 1))
  have hCA : 0 < CA := by
    have := applicationLogCoefficient_pos η ε
    have := lt_min hε (by norm_num : (0:ℝ)<1)
    dsimp [CA]; positivity
  obtain ⟨Ct, hCt, d, htime⟩ := constrained_reduction_runtime hLSW alg hη hη4 hε
  refine ⟨CA, Ct, hCA, hCt, d, fun n hn S S' hS ρ τ hρ hτ hK => ?_⟩
  let p := applicationParameters n η ε
  have hp := applicationParameters_valid hn hη hη4 hε
  letI := alg.markov n
  refine ⟨DP.mono (postprocess_private (family hLSW) hn p hp (alg.kernel n))
    (min_le_left ε 1) (le_refl _),
    (fun w => htime n hn w), fun w hw => ?_⟩
  have hu := constrained_utility (family hLSW) hn p hp (alg.kernel n) hS hρ hτ hK w hw
  apply hu.mono _ (Set.toFinite _ |>.measurableSet)
  intro T hT
  refine ⟨hT.1, hT.2.trans ?_⟩
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by linarith) (by linarith : 0 ≤ 1-η))
  have he := mul_le_mul_of_nonneg_left (application_error_bound hn hη hη4 hε)
    (by positivity : (0:ℝ)≤2^178)
  convert he using 1
  dsimp [CA, p]
  ring

/-- Theorem 36, with one private approximate program carrying both the hierarchy
guarantee and a polynomial bound in the assigned-cost model. -/
theorem theorem36 (hLSW : LSWStatement) (o : InducedARVContract) :
    ∃ b' Cratio CA Cfail : ℝ, 0 < b' ∧ b' ≤ 1/3 ∧ 0 < Cratio ∧ 0 < CA ∧ 0 < Cfail ∧
    ∀ η : ℝ, ∀ (hη : 0 < η) (hη4 : η ≤ 1/4), ∃ Cadd : ℝ, 0 < Cadd ∧
    ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ 1 → ∃ Ctime : ℝ, 0 < Ctime ∧ ∃ degree : ℕ,
    ∀ n (hn : 2 ≤ n), ∃ M : Kernel (Weights n) (Hierarchy n), IsMarkovKernel M ∧
      RealizedWithin M (ENNReal.ofReal (Ctime*(1+(n:ℝ))^degree))
        (costedPrivateHierarchy hLSW o hn (applicationParameters n η ε)
          (applicationParameters_valid hn hη hη4 hε)) ∧
      EdgeDP M ε ((n:ℝ)⁻¹^10) ∧
      ∀ w, Nonnegative w → HighProbability (M w) (Cfail/(n:ℝ)^2)
        (fun T => BalancedHierarchy b' T ∧ hcCost w T ≤
          Cratio*Real.sqrt (Real.log n)*hcOptimum w +
          Cadd*(CA*mainError n ⟨η, ε, (n:ℝ)⁻¹^10, (n:ℝ)⁻¹^10⟩)*n*(Real.log n)^(3/2:ℝ)) := by
  refine ⟨o.balance, 512*hierarchyRatioCoefficient o, (2:ℝ)^178, 2,
    o.balance_pos, o.balance_le, mul_pos (by norm_num) (hierarchyRatioCoefficient_pos o),
    by positivity, by norm_num, fun η hη hη4 =>
      ⟨hierarchyAddCoefficient o, hierarchyAddCoefficient_pos o, fun ε hε hε1 => ?_⟩⟩
  obtain ⟨Ct, hCt, d, htime⟩ := hierarchy_reduction_runtime hLSW o hη hη4 hε
  refine ⟨Ct, hCt, d, fun n hn => ?_⟩
  let p := applicationParameters n η ε
  have hp := applicationParameters_valid hn hη hη4 hε
  let M := postprocessKernel (family hLSW) hn p hp (nonprivateHierarchyKernel o n)
  refine ⟨M, inferInstance, (fun w => htime n hn w),
    DP.mono (postprocess_private (family hLSW) hn p hp (nonprivateHierarchyKernel o n))
      (min_le_left ε 1) (le_refl _), fun w hw => ?_⟩
  have hu := hierarchy_utility (family hLSW) hn p hp o w hw
  have hfail : p.beta+(n:ℝ)⁻¹^10 ≤ 2/(n:ℝ)^2 := by
    have hi := inverse_tenth_le_inverse_square hn
    change (n:ℝ)⁻¹^10+(n:ℝ)⁻¹^10 ≤ _
    convert add_le_add hi hi using 1
    ring
  have heq : mainError n p = mainError n ⟨η, ε, (n:ℝ)⁻¹^10, (n:ℝ)⁻¹^10⟩ := by
    simp only [p, applicationParameters, min_eq_left hε1]
  have hgood := hu.weaken hfail
  rw [heq] at hgood
  exact hgood

end LSWApplications
end DPCut
