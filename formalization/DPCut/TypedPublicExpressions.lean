import DPCut.TypedReleaseProgram

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace DPCut.TypedMachine

def Term.pow {Γ : List ValueType} (x : Term Γ .real) : ℕ → Term Γ .real
  | 0 => 1
  | k+1 => x.pow k*x

@[simp] theorem Term.eval_pow {Γ : List ValueType} (x : Term Γ .real) (k : ℕ) (s : Environment Γ) :
    (x.pow k).eval s = (x.eval s)^k := by
  induction k with
  | zero => norm_num [Term.pow,Term.eval]
  | succ k ih => simpa only [Term.pow,Term.eval,RealBinary.eval,pow_succ] using congrArg (fun y => y*x.eval s) ih

structure ParameterTerms (Γ : List ValueType) where
  gamma : Term Γ .real
  epsilon : Term Γ .real
  delta : Term Γ .real
  beta : Term Γ .real

def ParameterTerms.eval {Γ : List ValueType} (p : ParameterTerms Γ) (s : Environment Γ) : Parameters :=
  ⟨p.gamma.eval s,p.epsilon.eval s,p.delta.eval s,p.beta.eval s⟩

def ParameterTerms.precision {Γ : List ValueType} (p : ParameterTerms Γ) : ParameterTerms Γ :=
  ⟨p.gamma,p.epsilon,p.delta/2,p.beta/2⟩

def ParameterTerms.bounded {Γ : List ValueType} (p : ParameterTerms Γ) : ParameterTerms Γ :=
  ⟨p.gamma/2,p.epsilon/2,p.delta,p.beta/2⟩

def clipThresholdExpr {Γ : List ValueType} (n : ℕ) (epsilon beta gamma : Term Γ .real) : Term Γ .real :=
  8/(epsilon*gamma)*.realUnary .log ((.cast (.natural n))/beta)

def noiseShiftExpr {Γ : List ValueType} (n : ℕ) (epsilon beta : Term Γ .real) : Term Γ .real :=
  2/epsilon*.realUnary .log ((.cast (.natural n))/beta)

def logFactorExpr {Γ : List ValueType} (n : ℕ) (U : Term Γ .real) (p : ParameterTerms Γ) : Term Γ .real :=
  .realUnary .log ((.cast (.natural n))*U/(p.delta*p.beta*p.gamma*p.epsilon))

structure OracleExpressions (Γ : List ValueType) where
  k : Term Γ .natural
  K : Term Γ .natural
  lambda : Term Γ .real
  epsilon : Term Γ .real
  tau : Term Γ .real

def oracleExpressions {Γ : List ValueType} (n : ℕ) (epsilon delta beta : Term Γ .real) : OracleExpressions Γ :=
  let nr : Term Γ .real := .cast (.natural n)
  let K : Term Γ .natural := .ceil (8192*.realUnary .log (nr/beta))
  let Kr := Term.cast K
  let eps1 := epsilon/(320*Kr*(1+.realUnary .log (2/delta)))
  let delta1 := delta/(20*nr.pow 2*Kr)
  let beta1 := beta/(4*nr.pow 2*Kr)
  ⟨.ceil (512*.realUnary .log (nr/(beta1*delta1))),K,
    1073741824/eps1*.realUnary .log (nr/(beta*delta)),eps1,.realUnary .log (1/beta1)/eps1⟩

structure RunExpressions (Γ : List ValueType) where
  T1 : Term Γ .natural
  T2 : Term Γ .natural
  oracle : OracleExpressions Γ
  terms : RunTerms Γ

def runExpressions {Γ : List ValueType} (n : ℕ) (U : Term Γ .real) (p : ParameterTerms Γ) : RunExpressions Γ :=
  let nr : Term Γ .real := .cast (.natural n)
  let m : Term Γ .real := .cast (.natural (Fintype.card (Edge n)))
  let T1 : Term Γ .natural := .ceil (80*.realUnary .log (nr*U))
  let T2 : Term Γ .natural := .naturalBinary .add (.natural 1)
    (.ceil (64*(1+p.gamma).pow 2*.realUnary .log nr/p.gamma.pow 2))
  let t1 := Term.cast T1
  let t2 := Term.cast T2
  let eps2 := p.epsilon/(2*t1)
  let beta2 := p.beta/(2*t1)
  let tau2 := (.realUnary .log (1/beta2))/eps2
  let cap := m*U+2*tau2
  let epsG := p.epsilon/(4*t1*.realUnary .sqrt (2*t2*.realUnary .log (2*t1/p.delta)))
  let deltaG := p.delta/(2*t1*t2)
  let betaG := p.beta/(2*t1*t2)
  let o := oracleExpressions n epsG deltaG betaG
  let B := cap+(1+p.gamma)*m*U
  let L := logFactorExpr n U p
  let stop := (.rational ((2:ℚ)^120))*(nr*U*L+nr/(p.gamma*p.epsilon)*L.pow 6)
  ⟨T1,T2,o,⟨⟨o.epsilon,o.tau,B⟩,p.gamma,p.gamma/(8*(1+p.gamma)),eps2,tau2,cap,stop⟩⟩

structure PublicExpressions (Γ : List ValueType) where
  dimension : ℕ
  run : RunExpressions Γ
  threshold : Term Γ .real
  shift : Term Γ .real
  epsilon : Term Γ .real
  accuracy : Term Γ .real

def accuracyExpr {Γ : List ValueType} (n : ℕ) (p : ParameterTerms Γ)
    (T1 T2 k K : Term Γ .natural) : Term Γ .real :=
  let budget := (4 : Term Γ .real)*(.cast (.natural (Fintype.card (Edge n))))*
    (.cast T1)*(.cast T2)*(.cast K)*((.cast k)+1)
  let radius := p.beta*p.delta/(16*(1+budget))
  radius.pow 2/(8*(Term.cast (.natural n)).pow 4)

def publicExpressions {Γ : List ValueType} (n : ℕ) (p : ParameterTerms Γ) : PublicExpressions Γ :=
  let q := p.precision
  let epsilon := q.epsilon/2
  let beta := q.beta/2
  let U := clipThresholdExpr n epsilon beta q.gamma
  let run := runExpressions n U q.bounded
  ⟨n,run,U,noiseShiftExpr n epsilon beta,epsilon,accuracyExpr n p run.T1 run.T2 run.oracle.k run.oracle.K⟩

abbrev parameterContext : List ValueType := [.real,.real,.real,.real]

def parameterTerms : ParameterTerms parameterContext :=
  ⟨.read .head,.read (.tail .head),.read (.tail (.tail .head)),.read (.tail (.tail (.tail .head)))⟩

def parameterInput (p : Parameters) : Environment parameterContext :=
  (p.gamma,p.epsilon,p.delta,p.beta,())

end DPCut.TypedMachine
