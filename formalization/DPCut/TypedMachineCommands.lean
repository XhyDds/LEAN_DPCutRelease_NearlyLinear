import DPCut.TypedMachineNumerical
import DPCut.LaplaceScale
import DPCut.ProbabilityProgramming

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

open MeasureTheory ProbabilityTheory

namespace DPCut.TypedMachine

abbrev Outcome (a : ValueType) := a.Value × ℕ × ℕ

def addOperations {a : ValueType} (amount : ℕ) (r : Outcome a) : Outcome a :=
  (r.1,amount+r.2.1,r.2.2)

def appendOutcome {a b : ValueType} (overhead : ℕ) (first : Outcome a) (next : Outcome b) : Outcome b :=
  (next.1,first.2.1+next.2.1+overhead,first.2.2+next.2.2)

@[fun_prop] theorem measurable_addOperations (a : ValueType) (amount : ℕ) :
    Measurable (addOperations (a := a) amount) := by
  unfold addOperations
  fun_prop

@[fun_prop] theorem measurable_appendOutcome (a b : ValueType) (overhead : ℕ) :
    Measurable (fun p : Outcome a × Outcome b => appendOutcome overhead p.1 p.2) := by
  unfold appendOutcome
  fun_prop

def iterateMeasure {a : ValueType} (body : a.Value → Measure (Outcome a))
    (initial : a.Value) : ℕ → Measure (Outcome a)
  | 0 => Measure.dirac (initial,0,0)
  | n+1 => (body initial).bind fun r =>
      (iterateMeasure body r.1 n).map (appendOutcome 2 r)

inductive Command : List ValueType → ValueType → Type where
  | pure {Γ a} (value : Term Γ a) : Command Γ a
  | bind {Γ a b} (first : Command Γ a) (next : Command (a :: Γ) b) : Command Γ b
  | branch {Γ a} (condition : Term Γ .boolean) (yes no : Command Γ a) : Command Γ a
  | normal {Γ} : Command Γ .real
  | laplace {Γ} : Command Γ .real
  | factor {Γ} (n : ℕ) (matrix : Term Γ (matrixType n)) : Command Γ (matrixType n)
  | solver {Γ n} (parameters : SolverData n) (input : Term Γ (weightType n)) : Command Γ (matrixType n)
  | iterate {Γ a} (count : Term Γ .natural) (initial : Term Γ a)
      (body : Command (a :: Γ) a) : Command Γ a

/-- Counts are produced by the operational interpreter. Solver and factor
commands execute the scalar register programs; no command accepts a price. -/
def Command.run {Γ : List ValueType} : {a : ValueType} → Command Γ a → Environment Γ → Measure (Outcome a)
  | _, .pure value, s => Measure.dirac (value.eval s,value.operations+1,0)
  | _, .bind first next, s =>
      (first.run s).bind fun r => (next.run (r.1,s)).map (appendOutcome 1 r)
  | _, .branch condition yes no, s =>
      (if condition.eval s then yes.run s else no.run s).map (addOperations (condition.operations+1))
  | _, .normal, _ => (gaussianReal 0 1).map (fun z => (z,4,0))
  | _, .laplace, _ => (DPCut.laplace 1).map (fun z => (z,4,0))
  | _, .factor n matrix, s =>
      Measure.dirac (RealMachine.factorValue n (matrix.eval s),
        matrix.operations+RealMachine.factorOperations n (matrix.eval s)+1,0)
  | _, .solver S input, s =>
      let D := decodeWeights (input.eval s)
      Measure.dirac (S.result D,input.operations+S.operations D+1,1)
  | _, .iterate count initial body, s =>
      (iterateMeasure (fun x => body.run (x,s)) (initial.eval s) (count.eval s)).map
        (addOperations (count.operations+initial.operations+1))

def Command.law {Γ : List ValueType} {a : ValueType} (code : Command Γ a) (s : Environment Γ) :
    Measure a.Value := (code.run s).map Prod.fst

def newest {Γ : List ValueType} {a : ValueType} : Term (a :: Γ) a := .read .head

end DPCut.TypedMachine
