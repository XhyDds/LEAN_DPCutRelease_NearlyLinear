import DPCut.OracleReplacementMeasurable

/-! Full release kernels and identification with the original exact mechanism. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut.OracleReplacement

lemma config_eps2_pos {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U)
    {p : Parameters} (hp : p.Valid) :
    0 < (runConfig n U p outerUtilityConstants).eps2 :=
  (outerConfig_inner_utility_bounds hn hU p hp).eps2_pos

def boundedRelease {n : ℕ} (K : WitnessKernel n) (U : ℝ) (p : Parameters) (w : Weights n) :=
  let c := runConfig n U p outerUtilityConstants
  outerLoop K p c w c.T1 1 0

lemma boundedRelease_probability {n : ℕ} (K : WitnessKernel n) [IsMarkovKernel K]
    (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U) (p : Parameters) (hp : p.Valid) (w : Weights n) :
    IsProbabilityMeasure (boundedRelease K U p w) :=
  outerLoop_probability K p _ (config_eps2_pos hn hU hp) w _ 1 0

lemma measurable_boundedRelease {n : ℕ} (K : WitnessKernel n) [IsMarkovKernel K]
    (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U) (p : Parameters) (hp : p.Valid) :
    Measurable (boundedRelease K U p) :=
  measurable_outerLoop K p _ (config_eps2_pos hn hU hp) _
    measurable_id measurable_const measurable_const

def continuation {n : ℕ} (K : WitnessKernel n) (p : Parameters) (w y : Weights n) : Measure (Weights n) :=
  (boundedRelease K (preprocessingThreshold n p) (boundedParameters p)
    (clipWeights (preprocessingThreshold n p) w)).map (fun h => h + y)

lemma fullRelease_eq {n : ℕ} (K : WitnessKernel n) (p : Parameters) (w : Weights n) :
    fullRelease K p w =
      (preprocessLaw (p.epsilon / 2) (p.beta / 2) p.gamma w).bind (continuation K p w) := rfl

lemma continuation_probability {n : ℕ} (K : WitnessKernel n) [IsMarkovKernel K] (hn : 2 ≤ n) {p : Parameters}
    (hp : p.Valid) (w y : Weights n) : IsProbabilityMeasure (continuation K p w y) := by
  letI := boundedRelease_probability K hn (preprocessingThreshold_one_le hn hp)
    (boundedParameters p) (boundedParameters_valid hp) (clipWeights (preprocessingThreshold n p) w)
  exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma measurable_continuation {n : ℕ} (K : WitnessKernel n) [IsMarkovKernel K] (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid) :
    Measurable (Function.uncurry (continuation (n := n) K p)) := by
  let U := preprocessingThreshold n p
  let q := boundedParameters p
  letI (wy : Weights n × Weights n) :
      IsProbabilityMeasure (boundedRelease K U q (clipWeights U wy.1)) :=
    boundedRelease_probability K hn (preprocessingThreshold_one_le hn hp) q
      (boundedParameters_valid hp) _
  exact measurable_map_kernel
    (μ := fun wy : Weights n × Weights n => boundedRelease K U q (clipWeights U wy.1))
    (f := fun wy h => h + wy.2)
    ((measurable_boundedRelease K hn (preprocessingThreshold_one_le hn hp) q
      (boundedParameters_valid hp)).comp ((measurable_clipWeights U).comp measurable_fst))
    (by fun_prop)

lemma fullRelease_probability {n : ℕ} (K : WitnessKernel n) [IsMarkovKernel K] (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid)
    (w : Weights n) : IsProbabilityMeasure (fullRelease K p w) := by
  letI := preprocessLaw_probability (show 0 < p.epsilon / 2 by linarith [hp.2.2.1])
    (p.beta / 2) p.gamma w
  letI (y : Weights n) : IsProbabilityMeasure (continuation K p w y) :=
    continuation_probability K hn hp w y
  rw [fullRelease_eq]
  exact probability_bind _ _ ((measurable_continuation K hn hp).comp measurable_prodMk_left)

lemma measurable_fullRelease {n : ℕ} (K : WitnessKernel n) [IsMarkovKernel K] (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid) :
    Measurable (fullRelease (n := n) K p) := by
  letI := preprocessLaw_probability (n := n) (show 0 < p.epsilon / 2 by linarith [hp.2.2.1])
    (p.beta / 2) p.gamma
  exact measurable_bind_kernel
    (measurable_preprocessLaw (by linarith [hp.2.2.1]) _ _) (measurable_continuation K hn hp)

def fullKernel {n : ℕ} (K : WitnessKernel n) [IsMarkovKernel K] (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) :
    Kernel (Weights n) (Weights n) :=
  ⟨fullRelease K p, measurable_fullRelease K hn hp⟩

instance fullKernel_markov {n : ℕ} (K : WitnessKernel n) [IsMarkovKernel K] (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) :
    IsMarkovKernel (fullKernel K hn p hp) := ⟨fullRelease_probability K hn hp⟩


def exactKernel {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig) (hl : 0 < o.lam)
    (he : 0 < o.eps1) : WitnessKernel n :=
  ⟨fun q => findWitness o q.1 q.2, measurable_findWitness hn o hl he⟩

instance exactKernel_markov {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig) (hl : 0 < o.lam)
    (he : 0 < o.eps1) : IsMarkovKernel (exactKernel hn o hl he) :=
  ⟨fun q => findWitness_probability o he q.1 q.2⟩

variable {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig) (hl : 0 < o.lam) (he : 0 < o.eps1)

lemma aggregateLoop_exact (γ : ℝ) (w h : Weights n) (t : ℕ) (a : Aggregate n) :
    aggregateLoop (exactKernel hn o hl he) γ w h t a = DPCut.aggregateLoop o γ w h t a := by
  induction t generalizing a with
  | zero => rfl
  | succ t ih =>
    rw [aggregateLoop, DPCut.aggregateLoop_succ_eq]
    simp only [ih]
    rfl

lemma innerLoop_exact (p : Parameters) (c : RunConfig) (hc : c.oracle = o)
    (w : Weights n) (M : ℝ) (t : ℕ) (h : Weights n) :
    innerLoop (exactKernel hn o hl he) p c w M t h = DPCut.innerLoop p c w M t h := by
  induction t generalizing h with
  | zero => rfl
  | succ t ih =>
    rw [innerLoop, DPCut.innerLoop_succ_eq]
    simp only [aggregateLaw, aggregateLoop_exact, hc, DPCut.aggregateLaw, ih]

lemma outerLoop_exact (p : Parameters) (c : RunConfig) (hc : c.oracle = o)
    (w : Weights n) (t : ℕ) (a out : Weights n) :
    outerLoop (exactKernel hn o hl he) p c w t a out = DPCut.outerLoop p c w t a out := by
  induction t generalizing a out with
  | zero => rfl
  | succ t ih =>
    rw [outerLoop, DPCut.outerLoop_succ_raw]
    congr 1
    funext noise
    simp only [DPCut.outerAfterMass, innerLoop_exact hn o hl he p c hc]
    split_ifs
    · rfl
    · congr 1
      funext r
      cases r <;> simp [DPCut.outerResult, ih]

lemma fullRelease_exact (p : Parameters)
    (hc : (runConfig n (preprocessingThreshold n p) (boundedParameters p) outerUtilityConstants).oracle = o)
    (w : Weights n) :
    fullRelease (exactKernel hn o hl he) p w = fullReleaseLaw p outerUtilityConstants w := by
  unfold fullRelease fullReleaseLaw cutReleaseLaw
  dsimp only
  congr 1
  funext y
  congr 1
  exact outerLoop_exact hn o hl he _ _ hc _ _ _ _

end DPCut.OracleReplacement
