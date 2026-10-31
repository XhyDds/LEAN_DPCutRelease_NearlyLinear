import DPCut.KLTotalVariation
import DPCut.CovarianceApproximation
import DPCut.FindWitnessPrivacy

/-! Total-variation error caused by replacing the exact SDP optimizer by a
feasible point with a certified objective gap. The covariance is an argument;
no optimizer implementation or running-time contract is assumed. -/
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder
namespace DPCut

lemma TVClose.mono {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {a b : ℝ}
    (h : TVClose μ ν a) (hab : a ≤ b) : TVClose μ ν b :=
  fun s hs => (h s hs).trans hab

lemma TVClose.prod_same_right {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : ℝ} (h : TVClose μ ν η) (ρ : Measure β) [IsProbabilityMeasure ρ] :
    TVClose (μ.prod ρ) (ν.prod ρ) η := by
  simpa only [Measure.compProd_const] using h.compProd_same_kernel (Kernel.const α ρ)

lemma frobenius_neg {n : ℕ} (X : Mat n) : frobenius (-X) = frobenius X := by
  letI : NormedAddCommGroup (Mat n) := Matrix.frobeniusNormedAddCommGroup
  exact norm_neg X

theorem gaussian_covariance_tv {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    {X Y : Mat n} (hX : X.PosDef) (hY : Y.PosDef) {μ : ℝ}
    (hμ : 0 < μ) (hμhalf : μ ≤ 1 / 2)
    (hclose : frobenius ((CFC.sqrt Y)⁻¹ * (X - Y) * (CFC.sqrt Y)⁻¹) ≤ μ) :
    TVClose (gaussianBatch X k) (gaussianBatch Y k) (2 * Real.sqrt k * μ) := by
  have h := tvClose_of_klDiv_bound (by positivity : (0 : ℝ) ≤ k * μ ^ 2 / 2)
    (approximate_gaussian n k hn hk X Y hX hY μ hμ hμhalf hclose)
  apply h.mono
  have hs : Real.sqrt ((k : ℝ) * μ ^ 2 / 2) ≤ Real.sqrt k * μ := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (Nat.cast_nonneg k)]
    nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) (sq_nonneg μ)]
  nlinarith

theorem optimizer_gaussian_tv {n k : ℕ} (hn : 2 ≤ n) (hk : 0 < k)
    {lam μ : ℝ} (hlam : 0 < lam) (hμ : 0 < μ) (hμhalf : μ ≤ 1 / 2)
    (D : Weights n) {X : Mat n} (hX : X ∈ feasible n)
    (hgap : optimum lam D - objective lam D X ≤ lam * μ ^ 2 / (2 * (n : ℝ) ^ 4)) :
    TVClose (gaussianBatch X k) (gaussianBatch (optimizer lam D) k)
      (2 * Real.sqrt k * μ) := by
  have hclose := objective_gap n hn lam μ hlam hμ hμhalf D X hX hgap
  have he : (CFC.sqrt (optimizer lam D))⁻¹ * (X - optimizer lam D) *
      (CFC.sqrt (optimizer lam D))⁻¹ =
      -((CFC.sqrt (optimizer lam D))⁻¹ * (optimizer lam D - X) *
        (CFC.sqrt (optimizer lam D))⁻¹) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul]
    abel
  apply gaussian_covariance_tv (by omega) hk (feasible_posDef hn hX)
    (feasible_posDef hn (optimizer_isOptimizer hn lam D).1) hμ hμhalf
  rwa [he, frobenius_neg]

def approximateTrialLaw {n : ℕ} (o : OracleConfig) (D : Weights n) (X : Mat n) :
    Measure (TrialSample n o.k) :=
  ((gaussianBatch X o.k).prod (laplace (1 / o.eps1))).map (scoreShear D)

lemma approximateTrialLaw_probability {n : ℕ} (o : OracleConfig) (he : 0 < o.eps1)
    (D : Weights n) (X : Mat n) : IsProbabilityMeasure (approximateTrialLaw o D X) := by
  letI := laplace_isProbabilityMeasure (one_div_pos.mpr he)
  exact Measure.isProbabilityMeasure_map (scoreShear D).measurable.aemeasurable

def approximateFindWitness {n : ℕ} (o : OracleConfig) (D r : Weights n) (X : Mat n) :
    Measure (Option (Weights n)) :=
  if r = 0 then Measure.dirac none else
    repeatUntil (approximateTrialLaw o D X) (acceptTrial o r) o.K

theorem approximateFindWitness_tv {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (he : 0 < o.eps1) (hl : 0 < o.lam) (hk : 0 < o.k)
    (D r : Weights n) {X : Mat n} (hX : X ∈ feasible n) {μ : ℝ}
    (hμ : 0 < μ) (hμhalf : μ ≤ 1 / 2)
    (hgap : optimum o.lam D - objective o.lam D X ≤ o.lam * μ ^ 2 / (2 * (n : ℝ) ^ 4)) :
    TVClose (approximateFindWitness o D r X) (findWitness o D r)
      (o.K * (2 * Real.sqrt o.k * μ)) := by
  letI := laplace_isProbabilityMeasure (one_div_pos.mpr he)
  letI := approximateTrialLaw_probability o he D X
  letI := trialLaw_probability o he D
  have hg := optimizer_gaussian_tv hn hk hl hμ hμhalf D hX hgap
  have ht : TVClose (approximateTrialLaw o D X) (trialLaw o D) (2 * Real.sqrt o.k * μ) :=
    (hg.prod_same_right (laplace (1 / o.eps1))).map (scoreShear D).measurable
  unfold approximateFindWitness findWitness
  split_ifs
  · exact TVClose.refl _ (by positivity)
  · rw [findTrials_eq_repeatUntil o he]
    exact repeatUntil_tv ht (measurable_acceptTrial_fixed o r) o.K

end DPCut
