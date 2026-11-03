import DPCut.TypedPublicExpressions
import DPCut.TypedFullLaw
import DPCut.VerifiedEllipsoidRelease

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace DPCut.TypedMachine

@[simp] theorem eval_parameterPrecision {Γ : List ValueType} (p : ParameterTerms Γ) (s : Environment Γ) :
    p.precision.eval s = precisionParameters (p.eval s) := by
  cases p
  norm_num [ParameterTerms.precision,ParameterTerms.eval,precisionParameters,Term.eval,RealBinary.eval]

@[simp] theorem eval_parameterBounded {Γ : List ValueType} (p : ParameterTerms Γ) (s : Environment Γ) :
    p.bounded.eval s = boundedParameters (p.eval s) := by
  cases p
  norm_num [ParameterTerms.bounded,ParameterTerms.eval,boundedParameters,Term.eval,RealBinary.eval]

@[simp] theorem eval_clipThresholdExpr {Γ : List ValueType} (n : ℕ) (epsilon beta gamma : Term Γ .real)
    (s : Environment Γ) :
    (clipThresholdExpr n epsilon beta gamma).eval s = clipThreshold n (epsilon.eval s) (beta.eval s) (gamma.eval s) := by
  norm_num [clipThresholdExpr,Term.eval,RealBinary.eval,RealUnary.eval,clipThreshold]

@[simp] theorem eval_noiseShiftExpr {Γ : List ValueType} (n : ℕ) (epsilon beta : Term Γ .real)
    (s : Environment Γ) :
    (noiseShiftExpr n epsilon beta).eval s = noiseShift n (epsilon.eval s) (beta.eval s) := by
  norm_num [noiseShiftExpr,Term.eval,RealBinary.eval,RealUnary.eval,noiseShift]

@[simp] theorem eval_logFactorExpr {Γ : List ValueType} (n : ℕ) (U : Term Γ .real)
    (p : ParameterTerms Γ) (s : Environment Γ) :
    (logFactorExpr n U p).eval s = logFactor n (U.eval s) (p.eval s) := by
  simp [logFactorExpr,ParameterTerms.eval,Term.eval,RealBinary.eval,RealUnary.eval,logFactor]

structure OracleExpressions.Matches {Γ : List ValueType} (e : OracleExpressions Γ) (o : OracleConfig)
    (s : Environment Γ) : Prop where
  k : e.k.eval s = o.k
  K : e.K.eval s = o.K
  lambda : e.lambda.eval s = o.lam
  epsilon : e.epsilon.eval s = o.eps1
  tau : e.tau.eval s = o.tau1

theorem oracleExpressions_matches {Γ : List ValueType} (n : ℕ) (epsilon delta beta : Term Γ .real) (s : Environment Γ) :
    (oracleExpressions n epsilon delta beta).Matches
      (oracleConfig n outerUtilityConstants (epsilon.eval s) (delta.eval s) (beta.eval s)) s := by
  constructor <;>
    norm_num [oracleExpressions,oracleConfig,outerUtilityConstants,utilityConstants,privacyConstants,
      Term.eval,RealBinary.eval,RealUnary.eval,Term.eval_pow]

structure RunExpressions.Matches {Γ : List ValueType} (e : RunExpressions Γ) (p : Parameters) (c : RunConfig)
    (B : ℝ) (s : Environment Γ) : Prop where
  T1 : e.T1.eval s = c.T1
  T2 : e.T2.eval s = c.T2
  oracle : e.oracle.Matches c.oracle s
  terms : e.terms.Matches p c B s

theorem runExpressions_matches {Γ : List ValueType} (n : ℕ) (U : Term Γ .real) (p : ParameterTerms Γ)
    (s : Environment Γ) :
    let c := runConfig n (U.eval s) (p.eval s) outerUtilityConstants
    (runExpressions n U p).Matches (p.eval s) c
      (c.massCap+(1+(p.eval s).gamma)*Fintype.card (Edge n)*U.eval s) s := by
  dsimp only
  constructor
  · norm_num [runExpressions,runConfig,outerHorizon,outerUtilityConstants,Term.eval,RealBinary.eval,RealUnary.eval,ParameterTerms.eval]
  · norm_num [runExpressions,runConfig,innerHorizon,Term.eval,RealBinary.eval,RealUnary.eval,NaturalBinary.eval,ParameterTerms.eval]
  · constructor <;>
      norm_num [runExpressions,runConfig,oracleExpressions,oracleConfig,outerHorizon,innerHorizon,outerUtilityConstants,
        utilityConstants,privacyConstants,Term.eval,RealBinary.eval,RealUnary.eval,NaturalBinary.eval,Term.eval_pow,ParameterTerms.eval]
  · refine ⟨⟨?_,?_,?_⟩,?_,?_,?_,?_,?_,?_⟩ <;>
      norm_num [runExpressions,runConfig,OracleTerms.Matches,ParameterTerms.eval,Term.eval,RealBinary.eval,RealUnary.eval,NaturalBinary.eval,
        outerHorizon,innerHorizon,outerUtilityConstants,utilityConstants,privacyConstants,
        oracleExpressions,oracleConfig,stepSize,stoppingThreshold,logFactorExpr,logFactor]

structure PublicExpressions.Matches {Γ : List ValueType} (e : PublicExpressions Γ) (n : ℕ)
    (p : Parameters) (s : Environment Γ) : Prop where
  run : e.run.Matches (boundedParameters (precisionParameters p)) (fullRunConfig n (precisionParameters p))
    (publicObjectiveBound n (precisionParameters p)) s
  threshold : e.threshold.eval s = preprocessingThreshold n (precisionParameters p)
  shift : e.shift.eval s = noiseShift n (p.epsilon/2) (p.beta/4)
  epsilon : e.epsilon.eval s = p.epsilon/2
  accuracy : e.accuracy.eval s = solverAccuracy n p

theorem eval_accuracyExpr {Γ : List ValueType} (n : ℕ) (p : ParameterTerms Γ)
    (T1 T2 k K : Term Γ .natural) (s : Environment Γ) :
    (accuracyExpr n p T1 T2 k K).eval s =
      (p.beta.eval s*p.delta.eval s /
        (16*(1+4*Fintype.card (Edge n)*(T1.eval s)*(T2.eval s)*(K.eval s)*(k.eval s+1))))^2 /
          (8*(n:ℝ)^4) := by
  norm_num [accuracyExpr,Term.eval,RealBinary.eval]

theorem publicExpressions_matches {Γ : List ValueType} (n : ℕ) (p : ParameterTerms Γ) (s : Environment Γ) :
    (publicExpressions n p).Matches n (p.eval s) s := by
  let q := p.precision
  let U := clipThresholdExpr n (q.epsilon/2) (q.beta/2) q.gamma
  have hU : U.eval s = preprocessingThreshold n (precisionParameters (p.eval s)) := by
    norm_num [U,q,eval_clipThresholdExpr,preprocessingThreshold,ParameterTerms.precision,
      ParameterTerms.eval,precisionParameters,Term.eval,RealBinary.eval]
  have hr := runExpressions_matches n U q.bounded s
  have hr' : (publicExpressions n p).run.Matches (boundedParameters (precisionParameters (p.eval s)))
      (fullRunConfig n (precisionParameters (p.eval s)))
      (publicObjectiveBound n (precisionParameters (p.eval s))) s := by
    simpa only [publicExpressions,hU,q,eval_parameterBounded,eval_parameterPrecision,
      fullRunConfig,publicObjectiveBound] using hr
  refine ⟨hr',hU,?_,?_,?_⟩
  · norm_num [publicExpressions,eval_noiseShiftExpr,ParameterTerms.precision,ParameterTerms.eval,
      Term.eval,RealBinary.eval]
    congr 1
    ring
  · norm_num [publicExpressions,ParameterTerms.precision,ParameterTerms.eval,Term.eval,RealBinary.eval]
  · change (accuracyExpr n p _ _ _ _).eval s = _
    have hT1 := hr'.T1
    have hT2 := hr'.T2
    have hk := hr'.oracle.k
    have hK := hr'.oracle.K
    simp only [publicExpressions] at hT1 hT2 hk hK
    rw [eval_accuracyExpr,hT1,hT2,hk,hK]
    rfl

theorem parameterTerms_input (p : Parameters) : parameterTerms.eval (parameterInput p) = p := by
  cases p
  rfl

end DPCut.TypedMachine
