import DPCut.TypedWitnessProgram

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section

namespace DPCut.TypedMachine

structure OracleTerms (Γ : List ValueType) where
  epsilon : Term Γ .real
  tau : Term Γ .real
  bound : Term Γ .real

def OracleTerms.weaken {Γ : List ValueType} {a : ValueType} (p : OracleTerms Γ) : OracleTerms (a :: Γ) :=
  ⟨p.epsilon.weaken,p.tau.weaken,p.bound.weaken⟩

abbrev aggregateType (n : ℕ) : ValueType := .pair (weightType n) (.pair (weightType n) (weightType n))
abbrev aggregateStateType (n : ℕ) : ValueType := .pair .boolean (aggregateType n)
abbrev innerResultType (n : ℕ) : ValueType := .pair .boolean (.pair (weightType n) (weightType n))
abbrev innerStateType (n : ℕ) : ValueType := .pair .boolean (innerResultType n)
abbrev outerStateType (n : ℕ) : ValueType := .pair .boolean (.pair (weightType n) (weightType n))

def plusTerm {Γ : List ValueType} {n : ℕ} (a : Term Γ (aggregateType n)) : Term Γ (weightType n) := .fst a
def minusTerm {Γ : List ValueType} {n : ℕ} (a : Term Γ (aggregateType n)) : Term Γ (weightType n) := .fst (.snd a)
def residualTerm {Γ : List ValueType} {n : ℕ} (a : Term Γ (aggregateType n)) : Term Γ (weightType n) := .snd (.snd a)

def initialAggregate {Γ : List ValueType} (n : ℕ) : Term Γ (aggregateType n) :=
  .pair (zeroWeights n) (.pair (zeroWeights n) (oneWeights n))

def plusDiscrepancyTerm {Γ : List ValueType} {n : ℕ} (gamma : Term Γ .real)
    (w h r : Term Γ (weightType n)) : Term Γ (weightType n) :=
  weightTerms (fun e => edgeTerm r e*(edgeTerm h e-(1+gamma)*edgeTerm w e))

def minusDiscrepancyTerm {Γ : List ValueType} {n : ℕ} (gamma : Term Γ .real)
    (w h r : Term Γ (weightType n)) : Term Γ (weightType n) :=
  weightTerms (fun e => edgeTerm r e*((1-gamma)*edgeTerm w e-edgeTerm h e))

def aggregateAddTerm {Γ : List ValueType} {n : ℕ} (positive : Bool)
    (a : Term Γ (aggregateType n)) (g : Term Γ (weightType n)) : Term Γ (aggregateType n) :=
  .pair (if positive then addWeights (plusTerm a) g else plusTerm a)
    (.pair (if positive then minusTerm a else addWeights (minusTerm a) g)
      (subWeights (residualTerm a) g))

def acceptsTerm {Γ : List ValueType} {n : ℕ} (a : Term Γ (aggregateType n)) (h : Term Γ (weightType n)) :
    Term Γ .boolean :=
  .realCompare .le (.realBinary .max (pairingTerm h (plusTerm a)) (pairingTerm h (minusTerm a)))
    (pairingTerm h (residualTerm a))

def mwUpdateTerm {Γ : List ValueType} {n : ℕ} (M theta eta : Term Γ .real)
    (h g : Term Γ (weightType n)) : Term Γ (weightType n) :=
  let updated := weightTerms (fun e => edgeTerm h e*.realUnary .exp (-theta*eta*edgeTerm g e))
  weightTerms (fun e => M*edgeTerm updated e/(massTerm updated))

def innerNextTerm {Γ : List ValueType} {n : ℕ} (M eta : Term Γ .real)
    (h : Term Γ (weightType n)) (a : Term Γ (aggregateType n)) : Term Γ (weightType n) :=
  let choosePlus := Term.realCompare .le (pairingTerm h (minusTerm a)) (pairingTerm h (plusTerm a))
  mwUpdateTerm M (.select choosePlus 1 (-1)) eta h (.select choosePlus (plusTerm a) (minusTerm a))

def initialEstimateTerm {Γ : List ValueType} {n : ℕ} (M : Term Γ .real) (a : Term Γ (weightType n)) :
    Term Γ (weightType n) :=
  weightTerms (fun e => M*edgeTerm a e/(massTerm a))

def residualUpdateTerm {Γ : List ValueType} {n : ℕ} (a r : Term Γ (weightType n)) : Term Γ (weightType n) :=
  weightTerms (fun e => edgeTerm a e*(1-edgeTerm r e))

def noisyMassTerm {Γ : List ValueType} (cap mass noise tau : Term Γ .real) : Term Γ .real :=
  .realBinary .min (.realBinary .max 0 cap) (.realBinary .max 0 (mass+noise+tau))

def clipWeightsTerm {Γ : List ValueType} {n : ℕ} (U : Term Γ .real) (w : Term Γ (weightType n)) : Term Γ (weightType n) :=
  weightTerms (fun e => .realBinary .min (edgeTerm w e) U)

def noisyExcessTerm {Γ : List ValueType} {n : ℕ} (U V epsilon : Term Γ .real)
    (w noise : Term Γ (weightType n)) : Term Γ (weightType n) :=
  weightTerms (fun e => .realBinary .max 0
    (.realBinary .max (edgeTerm w e-U) 0+edgeTerm noise e/epsilon-V))

def positiveTerm {Γ : List ValueType} {n : ℕ} (w : Term Γ (weightType n)) : Term Γ (weightType n) :=
  weightTerms (fun e => .realBinary .max 0 (edgeTerm w e))

def decodeAggregate {n : ℕ} (a : (aggregateType n).Value) : Aggregate n :=
  ⟨decodeWeights a.1,decodeWeights a.2.1,decodeWeights a.2.2⟩

def decodeInner {n : ℕ} (a : (innerResultType n).Value) : Option (Weights n × Weights n) :=
  if a.1 then some (decodeWeights a.2.1,decodeWeights a.2.2) else none

end DPCut.TypedMachine
