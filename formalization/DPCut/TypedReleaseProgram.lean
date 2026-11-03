import DPCut.TypedReleaseTerms

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section

namespace DPCut.TypedMachine

def aggregateFinish {Γ : List ValueType} {n : ℕ} (positive : Bool)
    (a : Term Γ (aggregateType n)) (result : Term Γ (witnessType n)) :
    BoundedCommand Γ (aggregateStateType n) :=
  .branch (.fst result)
    (.pure (.pair (.boolean false) (aggregateAddTerm positive a (.snd result))))
    (.pure (.pair (.boolean true) a))

def aggregateAfterPlus {Γ : List ValueType} {n : ℕ} (S : SolverData n) (k K : ℕ)
    (o : OracleTerms Γ) (gamma : Term Γ .real) (w h : Term Γ (weightType n))
    (a : Term Γ (aggregateType n)) (result : Term Γ (witnessType n)) :
    BoundedCommand Γ (aggregateStateType n) :=
  .branch (.fst result)
    (.pure (.pair (.boolean false) (aggregateAddTerm true a (.snd result))))
    ((witnessCommand S k K o.epsilon o.tau o.bound
        (minusDiscrepancyTerm gamma w h (residualTerm a)) (residualTerm a)).bind
      (aggregateFinish false a.weaken newest))

def aggregateStep {Γ : List ValueType} {n : ℕ} (S : SolverData n) (k K : ℕ)
    (o : OracleTerms Γ) (gamma : Term Γ .real) (w h : Term Γ (weightType n)) :
    BoundedCommand (aggregateStateType n :: Γ) (aggregateStateType n) :=
  let a : Term (aggregateStateType n :: Γ) (aggregateType n) := .snd newest
  let r := residualTerm a
  .branch (.fst newest) (.pure newest)
    (.branch (allZero r) (.pure (.pair (.boolean true) a))
      ((witnessCommand S k K o.epsilon.weaken o.tau.weaken o.bound.weaken
          (plusDiscrepancyTerm gamma.weaken w.weaken h.weaken r) r).bind
        (aggregateAfterPlus S k K o.weaken.weaken gamma.weaken.weaken w.weaken.weaken h.weaken.weaken
          a.weaken newest)))

def aggregateCommand {Γ : List ValueType} {n : ℕ} (S : SolverData n) (k K : ℕ)
    (o : OracleTerms Γ) (gamma : Term Γ .real) (w h : Term Γ (weightType n)) :
    BoundedCommand Γ (aggregateType n) :=
  (BoundedCommand.iterate (Fintype.card (Edge n)) (.pair (.boolean false) (initialAggregate n))
    (aggregateStep S k K o gamma w h)).bind (.pure (.snd newest))

def innerStep {Γ : List ValueType} {n : ℕ} (S : SolverData n) (k K : ℕ)
    (o : OracleTerms Γ) (gamma eta M : Term Γ .real) (w : Term Γ (weightType n)) :
    BoundedCommand (innerStateType n :: Γ) (innerStateType n) :=
  let h : Term (innerStateType n :: Γ) (weightType n) := .fst (.snd (.snd newest))
  .branch (.fst newest) (.pure newest)
    ((aggregateCommand S k K o.weaken gamma.weaken w.weaken h).bind
      (.branch (acceptsTerm newest h.weaken)
        (.pure (.pair (.boolean true) (.pair (.boolean true) (.pair h.weaken (residualTerm newest)))))
        (.pure (.pair (.boolean false) (.pair (.boolean false)
          (.pair (innerNextTerm M.weaken.weaken eta.weaken.weaken h.weaken newest) (zeroWeights n)))))))

def innerCommand {Γ : List ValueType} {n : ℕ} (S : SolverData n) (k K T : ℕ)
    (o : OracleTerms Γ) (gamma eta M : Term Γ .real) (w initial : Term Γ (weightType n)) :
    BoundedCommand Γ (innerResultType n) :=
  (BoundedCommand.iterate T (.pair (.boolean false) (.pair (.boolean false) (.pair initial (zeroWeights n))))
    (innerStep S k K o gamma eta M w)).bind (.pure (.snd newest))

structure RunTerms (Γ : List ValueType) where
  oracle : OracleTerms Γ
  gamma : Term Γ .real
  eta : Term Γ .real
  epsilon : Term Γ .real
  tau : Term Γ .real
  massCap : Term Γ .real
  stop : Term Γ .real

def RunTerms.weaken {Γ : List ValueType} {a : ValueType} (p : RunTerms Γ) : RunTerms (a :: Γ) :=
  ⟨p.oracle.weaken,p.gamma.weaken,p.eta.weaken,p.epsilon.weaken,p.tau.weaken,p.massCap.weaken,p.stop.weaken⟩

def outerAfterInner {Γ : List ValueType} {n : ℕ} (a output : Term Γ (weightType n))
    (result : Term Γ (innerResultType n)) : BoundedCommand Γ (outerStateType n) :=
  .branch (.fst result)
    (.pure (.pair (.boolean false)
      (.pair (residualUpdateTerm a (.snd (.snd result)))
        (addWeights output (productWeights (.fst (.snd result)) (.snd (.snd result)))))))
    (.pure (.pair (.boolean false) (.pair a output)))

def outerAfterMass {Γ : List ValueType} {n : ℕ} (S : SolverData n) (k K T2 : ℕ)
    (p : RunTerms Γ) (w a output : Term Γ (weightType n)) (M : Term Γ .real) :
    BoundedCommand Γ (outerStateType n) :=
  .branch (.or (allZero a) (.realCompare .le M p.stop))
    (.pure (.pair (.boolean true) (.pair a output)))
    ((innerCommand S k K T2 p.oracle p.gamma p.eta M (productWeights a w) (initialEstimateTerm M a)).bind
      (outerAfterInner a.weaken output.weaken newest))

def outerAfterNoise {Γ : List ValueType} {n : ℕ} (S : SolverData n) (k K T2 : ℕ)
    (p : RunTerms Γ) (w a output : Term Γ (weightType n)) (noise : Term Γ .real) :
    BoundedCommand Γ (outerStateType n) :=
  (BoundedCommand.pure (noisyMassTerm p.massCap (massTerm (productWeights a w))
    (noise/p.epsilon) p.tau)).bind
    (outerAfterMass S k K T2 p.weaken w.weaken a.weaken output.weaken newest)

def outerStep {Γ : List ValueType} {n : ℕ} (S : SolverData n) (k K T2 : ℕ)
    (p : RunTerms Γ) (w : Term Γ (weightType n)) :
    BoundedCommand (outerStateType n :: Γ) (outerStateType n) :=
  let a : Term (outerStateType n :: Γ) (weightType n) := .fst (.snd newest)
  let output : Term (outerStateType n :: Γ) (weightType n) := .snd (.snd newest)
  .branch (.fst newest) (.pure newest)
    ((BoundedCommand.laplace _).bind
      (outerAfterNoise S k K T2 p.weaken.weaken w.weaken.weaken a.weaken output.weaken newest))

def outerCommand {Γ : List ValueType} {n : ℕ} (S : SolverData n) (k K T1 T2 : ℕ)
    (p : RunTerms Γ) (w : Term Γ (weightType n)) : BoundedCommand Γ (weightType n) :=
  (BoundedCommand.iterate T1 (.pair (.boolean false) (.pair (oneWeights n) (zeroWeights n)))
    (outerStep S k K T2 p w)).bind (.pure (.snd (.snd newest)))

def preprocessCommand {Γ : List ValueType} (n : ℕ) (U V epsilon : Term Γ .real) (w : Term Γ (weightType n)) :
    BoundedCommand Γ (weightType n) :=
  (scalarArray false (Fintype.card (Edge n)) Γ).bind
    (.pure (noisyExcessTerm U.weaken V.weaken epsilon.weaken w.weaken newest))

def fullCommand {Γ : List ValueType} {n : ℕ} (S : SolverData n) (k K T1 T2 : ℕ)
    (p : RunTerms Γ) (U V epsilon : Term Γ .real) (w : Term Γ (weightType n)) : BoundedCommand Γ (weightType n) :=
  (preprocessCommand n U V epsilon w).bind
    ((outerCommand S k K T1 T2 p.weaken (clipWeightsTerm U w).weaken).bind
      (.pure (positiveTerm (addWeights newest (.read (.tail .head))))))

end DPCut.TypedMachine
