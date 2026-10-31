import DPCut.Definitions

/-! Ideal real-valued probability semantics of Algorithms 1--4. These are definitions,
not executable finite-bit implementations. Measurability and normalization are proof targets. -/
set_option autoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace DPCut
attribute [local instance] Classical.propDecidable

instance {n : ℕ} : MeasurableSpace (Aggregate n) :=
  MeasurableSpace.comap (fun a => (a.plus, a.minus, a.residual)) inferInstance

structure Constants where
  outer : ℝ
  trials : ℝ
  batch : ℝ
  regularization : ℝ
  certificate : ℝ
  stopping : ℝ

def Constants.Positive (c : Constants) : Prop :=
  0 < c.outer ∧ 0 < c.trials ∧ 0 < c.batch ∧ 0 < c.regularization ∧
  0 < c.certificate ∧ 0 < c.stopping

structure OracleConfig where
  k : ℕ
  K : ℕ
  lam : ℝ
  eps1 : ℝ
  delta1 : ℝ
  beta1 : ℝ
  betaChi : ℝ
  tau1 : ℝ

def oracleConfig (n : ℕ) (c : Constants) (ε δ β : ℝ) : OracleConfig :=
  let K := ⌈c.trials * Real.log (n / β)⌉₊
  let ε₁ := ε / (320 * K * (1 + Real.log (2 / δ)))
  let δ₁ := δ / (20 * (n : ℝ) ^ 2 * K)
  let β₁ := β / (4 * (n : ℝ) ^ 2 * K)
  { k := ⌈c.batch * Real.log (n / (β₁ * δ₁))⌉₊, K := K,
    lam := c.regularization / ε₁ * Real.log (n / (β * δ)),
    eps1 := ε₁, delta1 := δ₁, beta1 := β₁, betaChi := β₁,
    tau1 := Real.log (1 / β₁) / ε₁ }

structure RunConfig where
  T1 : ℕ
  T2 : ℕ
  eps2 : ℝ
  beta2 : ℝ
  tau2 : ℝ
  massCap : ℝ
  epsGE : ℝ
  deltaGE : ℝ
  betaGE : ℝ
  oracle : OracleConfig
  B : ℝ
  stop : ℝ
  eta : ℝ

def runConfig (n : ℕ) (U : ℝ) (p : Parameters) (c : Constants) : RunConfig :=
  let T₁ := outerHorizon n U c.outer
  let T₂ := innerHorizon n p.gamma
  let ε₂ := p.epsilon / (2 * T₁)
  let β₂ := p.beta / (2 * T₁)
  let εG := p.epsilon / (4 * T₁ * Real.sqrt (2 * T₂ * Real.log (2 * T₁ / p.delta)))
  let δG := p.delta / (2 * T₁ * T₂)
  let βG := p.beta / (2 * T₁ * T₂)
  let o := oracleConfig n c εG δG βG
  { T1 := T₁, T2 := T₂, eps2 := ε₂, beta2 := β₂, tau2 := Real.log (1 / β₂) / ε₂,
    massCap := Fintype.card (Edge n) * U + 2 * (Real.log (1 / β₂) / ε₂),
    epsGE := εG, deltaGE := δG, betaGE := βG, oracle := o,
    B := c.certificate * (o.tau1 + o.lam * n * Real.log n + n * U),
    stop := stoppingThreshold n U c.stopping p, eta := stepSize p.gamma }

/-- Public upper clipping of the shifted nonnegative noisy mass. The `max` on
an invalid negative cap makes the definition total; calibrated caps are positive. -/
def clipNoisyMass (cap M z τ : ℝ) : ℝ :=
  min (max 0 cap) (max 0 (M + z + τ))

def activeMaximum {n : ℕ} (r g : Weights n) : ℝ :=
  sSup (insert 0 (g '' {e | 0 < r e}))
def normalizeWitness {n : ℕ} (r g : Weights n) : Weights n :=
  fun e => r e * g e / activeMaximum r g

/-- Trials use fresh product Gaussian samples and an independent Laplace sample. -/
def findTrials {n : ℕ} (o : OracleConfig) (D r : Weights n) : ℕ → Measure (Option (Weights n))
  | 0 => Measure.dirac none
  | t + 1 => (gaussianBatch (optimizer o.lam D) o.k).bind fun z =>
      (laplace (1 / o.eps1)).bind fun noise =>
        let g := clippedWitness z
        if o.tau1 ≤ pairing D g + noise ∧ 0 < activeMaximum r g
        then Measure.dirac (some (normalizeWitness r g))
        else findTrials o D r t

def findWitness {n : ℕ} (o : OracleConfig) (D r : Weights n) : Measure (Option (Weights n)) :=
  if r = 0 then Measure.dirac none else findTrials o D r o.K

def plusDiscrepancy {n : ℕ} (γ : ℝ) (w h r : Weights n) : Weights n :=
  fun e => r e * (h e - (1 + γ) * w e)
def minusDiscrepancy {n : ℕ} (γ : ℝ) (w h r : Weights n) : Weights n :=
  fun e => r e * ((1 - γ) * w e - h e)

/-- Fuel counts successful retirements. At most `card (Edge n)` can occur.
The unreachable-fallback assertion is a separate obligation, not assumed by this definition. -/
def aggregateLoop {n : ℕ} (o : OracleConfig) (γ : ℝ) (w h : Weights n) :
    ℕ → Aggregate n → Measure (Aggregate n)
  | 0, a => Measure.dirac a
  | t + 1, a =>
      if a.residual = 0 then Measure.dirac a else
      (findWitness o (plusDiscrepancy γ w h a.residual) a.residual).bind fun gp =>
      match gp with
      | some g => aggregateLoop o γ w h t
          { a with plus := a.plus + g, residual := a.residual - g }
      | none =>
        (findWitness o (minusDiscrepancy γ w h a.residual) a.residual).bind fun gm =>
        match gm with
        | some g => aggregateLoop o γ w h t
            { a with minus := a.minus + g, residual := a.residual - g }
        | none => Measure.dirac a

def aggregateLaw {n : ℕ} (o : OracleConfig) (γ : ℝ) (w h : Weights n) : Measure (Aggregate n) :=
  aggregateLoop o γ w h (Fintype.card (Edge n)) { plus := 0, minus := 0, residual := 1 }

/-- None means the public inner horizon was exhausted. -/
def innerLoop {n : ℕ} (p : Parameters) (c : RunConfig) (w : Weights n) (M : ℝ) :
    ℕ → Weights n → Measure (Option (Weights n × Weights n))
  | 0, _ => Measure.dirac none
  | t + 1, h => (aggregateLaw c.oracle p.gamma w h).bind fun a =>
      if a.Accepts h then Measure.dirac (some (h, a.residual)) else
      let over := pairing h a.minus ≤ pairing h a.plus
      let θ : ℝ := if over then 1 else -1
      let g := if over then a.plus else a.minus
      innerLoop p c w M t (mwUpdate M θ c.eta h g)

/-- CutRelease with the public noisy-mass cap from the implementation proof. -/
def outerLoop {n : ℕ} (p : Parameters) (c : RunConfig) (w : Weights n) :
    ℕ → Weights n → Weights n → Measure (Weights n)
  | 0, _, output => Measure.dirac output
  | t + 1, a, output =>
      let wi := hadamard a w
      (laplace (1 / c.eps2)).bind fun noise =>
      let M := clipNoisyMass c.massCap (mass wi) noise c.tau2
      if a = 0 ∨ M ≤ c.stop then Measure.dirac output else
      (innerLoop p c wi M c.T2 (initialEstimate M a)).bind fun result =>
      match result with
      | none => outerLoop p c w t a output
      | some (h, r) => outerLoop p c w t (residualUpdate a r) (output + hadamard h r)

def cutReleaseLaw {n : ℕ} (U : ℝ) (p : Parameters) (c : Constants)
    (w : Weights n) : Measure (Weights n) :=
  let cfg := runConfig n U p c
  outerLoop p cfg w cfg.T1 1 0

def fullReleaseLaw {n : ℕ} (p : Parameters) (c : Constants) (w : Weights n) : Measure (Weights n) :=
  let U := clipThreshold n (p.epsilon / 2) (p.beta / 2) p.gamma
  let inner := { p with gamma := p.gamma / 2, epsilon := p.epsilon / 2, beta := p.beta / 2 }
  (preprocessLaw (p.epsilon / 2) (p.beta / 2) p.gamma w).bind fun y =>
    (cutReleaseLaw U inner c (clipWeights U w)).map (fun h => h + y)

end DPCut
