import DPCut.TypedPublicRefinement

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace DPCut.TypedMachine

abbrev publicType : ValueType := .pair (.array 6 .natural) (.array 14 .real)

def scheduleFuel {Γ : List ValueType} (e : PublicExpressions Γ) : Term Γ .natural :=
  let m : Term Γ .real := .cast (.natural (e.dimension*e.dimension))
  let range := 1+2*e.run.terms.oracle.bound+e.run.oracle.lambda*(Term.cast (.natural e.dimension)).pow 2
  let radius := (1/4 : Term Γ .real)*(e.accuracy/4/(2*range))
  .naturalBinary .add (.floor (2*(m+2)*m*.realUnary .log ((2*(.cast (.natural e.dimension)))/radius))) (.natural 1)

def scheduleRounds {Γ : List ValueType} (e : PublicExpressions Γ) : Term Γ .natural :=
  let range := 1+2*e.run.terms.oracle.bound+e.run.oracle.lambda*(Term.cast (.natural e.dimension)).pow 2
  .naturalBinary .add (.ceil (.realUnary .log (2*range/e.accuracy)/(.realUnary .log 2))) (.natural 1)

def publicTerm {Γ : List ValueType} (e : PublicExpressions Γ) : Term Γ publicType :=
  .pair (.array ![e.run.T1,e.run.T2,e.run.oracle.k,e.run.oracle.K,scheduleFuel e,scheduleRounds e])
    (.array ![e.run.terms.gamma,e.run.terms.eta,e.run.terms.oracle.epsilon,e.run.terms.oracle.tau,
      e.run.terms.oracle.bound,e.run.terms.epsilon,e.run.terms.tau,e.run.terms.massCap,e.run.terms.stop,
      e.threshold,e.shift,e.epsilon,e.run.oracle.lambda,e.accuracy])

def realPublic {Γ : List ValueType} (data : Term Γ publicType) (i : Fin 14) : Term Γ .real := (Term.snd data).at i
def naturalPublic {Γ : List ValueType} (data : Term Γ publicType) (i : Fin 6) : Term Γ .natural := (Term.fst data).at i

def runTermsOf {Γ : List ValueType} (data : Term Γ publicType) : RunTerms Γ :=
  ⟨⟨realPublic data 2,realPublic data 3,realPublic data 4⟩,realPublic data 0,realPublic data 1,
    realPublic data 5,realPublic data 6,realPublic data 7,realPublic data 8⟩

def publicData (n : ℕ) (p : Parameters) : publicType.Value :=
  (publicTerm (publicExpressions n parameterTerms)).eval (parameterInput p)

def calibrationCommand (n : ℕ) : BoundedCommand parameterContext publicType :=
  .pure (publicTerm (publicExpressions n parameterTerms))

abbrev releaseContext (n : ℕ) : List ValueType := [weightType n,publicType]

def releaseInput (n : ℕ) (p : Parameters) (w : Weights n) : Environment (releaseContext n) :=
  (encodeWeights w,publicData n p,())

def dataInput (n : ℕ) : Term (releaseContext n) publicType := .read (.tail .head)

def releaseProgram {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) :
    BoundedCommand (releaseContext n) (weightType n) :=
  let c := fullRunConfig n (precisionParameters p)
  let data := dataInput n
  fullCommand (releaseSolver hn p hp) c.oracle.k c.oracle.K c.T1 c.T2 (runTermsOf data)
    (realPublic data 9) (realPublic data 10) (realPublic data 11) newest

@[simp] theorem eval_realPublic {Γ : List ValueType} (data : Term Γ publicType) (i : Fin 14) (s : Environment Γ) :
    (realPublic data i).eval s = (data.eval s).2 i := by
  simp [realPublic,Term.eval]

@[simp] theorem eval_naturalPublic {Γ : List ValueType} (data : Term Γ publicType) (i : Fin 6) (s : Environment Γ) :
    (naturalPublic data i).eval s = (data.eval s).1 i := by
  simp [naturalPublic,Term.eval]

theorem runTermsOf_matches {Γ Δ : List ValueType} (n : ℕ) (e : PublicExpressions Γ) (p : Parameters)
    (s : Environment Γ) (hs : e.Matches n p s) (data : Term Δ publicType) (t : Environment Δ)
    (hdata : data.eval t = (publicTerm e).eval s) :
    (runTermsOf data).Matches (boundedParameters (precisionParameters p)) (fullRunConfig n (precisionParameters p))
      (publicObjectiveBound n (precisionParameters p)) t := by
  have hr := hs.run.terms
  simpa only [RunTerms.Matches,OracleTerms.Matches,runTermsOf,eval_realPublic,hdata,
    publicTerm,Term.eval,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail]
      using hr

theorem releaseInput_matches {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) (w : Weights n) :
    (runTermsOf (dataInput n)).Matches (boundedParameters (precisionParameters p)) (fullRunConfig n (precisionParameters p))
      (publicObjectiveBound n (precisionParameters p)) (releaseInput n p w) := by
  have hs := publicExpressions_matches n parameterTerms (parameterInput p)
  rw [parameterTerms_input] at hs
  exact runTermsOf_matches n _ p _ hs _ _ rfl

theorem releaseInput_threshold (n : ℕ) (p : Parameters) (w : Weights n) :
    (realPublic (dataInput n) 9).eval (releaseInput n p w) = preprocessingThreshold n (precisionParameters p) := by
  have h := (publicExpressions_matches n parameterTerms (parameterInput p)).threshold
  simpa only [eval_realPublic,dataInput,releaseInput,publicData,publicTerm,Term.eval,Local.read,
    Matrix.cons_val_zero,Matrix.cons_val_succ,parameterTerms_input] using h

theorem releaseInput_shift (n : ℕ) (p : Parameters) (w : Weights n) :
    (realPublic (dataInput n) 10).eval (releaseInput n p w) = noiseShift n (p.epsilon/2) (p.beta/4) := by
  have h := (publicExpressions_matches n parameterTerms (parameterInput p)).shift
  simpa only [eval_realPublic,dataInput,releaseInput,publicData,publicTerm,Term.eval,Local.read,
    Matrix.cons_val_zero,Matrix.cons_val_succ,parameterTerms_input] using h

theorem releaseInput_epsilon (n : ℕ) (p : Parameters) (w : Weights n) :
    (realPublic (dataInput n) 11).eval (releaseInput n p w) = p.epsilon/2 := by
  have h := (publicExpressions_matches n parameterTerms (parameterInput p)).epsilon
  simpa only [eval_realPublic,dataInput,releaseInput,publicData,publicTerm,Term.eval,Local.read,
    Matrix.cons_val_zero,Matrix.cons_val_succ,parameterTerms_input] using h

end DPCut.TypedMachine
