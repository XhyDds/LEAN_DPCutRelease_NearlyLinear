import DPCut.TypedGaussianSampling
import DPCut.FindWitnessPrivacy

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section

namespace DPCut.TypedMachine

abbrev trialType (n k : ℕ) : ValueType := .pair (batchType n k) .real

def boundedObjectiveTerm {Γ : List ValueType} {n : ℕ}
    (B : Term Γ .real) (D : Term Γ (weightType n)) : Term Γ (weightType n) :=
  .select (.realCompare .le (l1Term D) B) D (zeroWeights n)

def trialSampleCommand {Γ : List ValueType} (n k : ℕ) (epsilon : Term Γ .real)
    (D : Term Γ (weightType n)) (X : Term Γ (matrixType n)) : BoundedCommand Γ (trialType n k) :=
  (gaussianCommand n k X).bind
    ((BoundedCommand.laplace _).bind
      (.pure (.pair (.read (.tail .head))
        (pairingTerm D.weaken.weaken (clippedWitnessTerm n k (.read (.tail .head))) +
          newest/epsilon.weaken.weaken))))

def acceptTrialTerm {Γ : List ValueType} (n k : ℕ) (tau : Term Γ .real)
    (r : Term Γ (weightType n)) (sample : Term Γ (trialType n k)) : Term Γ (witnessType n) :=
  let g := clippedWitnessTerm n k (.fst sample)
  let maximum := activeMaximumTerm r g
  .select (.and (.realCompare .le tau (.snd sample)) (.realCompare .lt 0 maximum))
    (.pair (.boolean true) (normalizeTerm r g maximum)) (noWitness n)

def trialStep {Γ : List ValueType} (n k : ℕ) (epsilon tau : Term Γ .real)
    (D r : Term Γ (weightType n)) (X : Term Γ (matrixType n)) :
    BoundedCommand (witnessType n :: Γ) (witnessType n) :=
  .branch (.fst newest) (.pure newest)
    ((trialSampleCommand n k epsilon.weaken D.weaken X.weaken).bind
      (.pure (acceptTrialTerm n k tau.weaken.weaken r.weaken.weaken newest)))

def trialsCommand {Γ : List ValueType} (n k K : ℕ) (epsilon tau : Term Γ .real)
    (D r : Term Γ (weightType n)) (X : Term Γ (matrixType n)) : BoundedCommand Γ (witnessType n) :=
  .iterate K (noWitness n) (trialStep n k epsilon tau D r X)

def witnessCommand {Γ : List ValueType} {n : ℕ} (S : SolverData n) (k K : ℕ)
    (epsilon tau B : Term Γ .real) (D r : Term Γ (weightType n)) : BoundedCommand Γ (witnessType n) :=
  .branch (allZero r) (.pure (noWitness n))
    ((BoundedCommand.solver S D).bind
      (trialsCommand n k K epsilon.weaken tau.weaken
        (boundedObjectiveTerm B D).weaken r.weaken newest))

@[simp] theorem eval_boundedObjectiveTerm {Γ : List ValueType} {n : ℕ}
    (B : Term Γ .real) (D : Term Γ (weightType n)) (s : Environment Γ) :
    decodeWeights ((boundedObjectiveTerm B D).eval s) = boundedObjective (B.eval s) (decodeWeights (D.eval s)) := by
  simp only [boundedObjectiveTerm, Term.eval, Comparison.real, eval_l1Term, decide_eq_true_eq]
  split <;> simp_all [boundedObjective]

@[simp] theorem eval_acceptTrialTerm {Γ : List ValueType} (n k : ℕ) (tau : Term Γ .real)
    (r : Term Γ (weightType n)) (sample : Term Γ (trialType n k)) (s : Environment Γ)
    (o : OracleConfig) (hk : o.k = k) (htau : tau.eval s = o.tau1) :
    decodeWitness ((acceptTrialTerm n k tau r sample).eval s) =
      acceptTrial {o with k := k} (decodeWeights (r.eval s)) (sample.eval s) := by
  subst k
  simp only [acceptTrialTerm, Term.eval, Comparison.real, RealBinary.eval,
    Bool.and_eq_true, decide_eq_true_eq]
  have hg := eval_clippedWitnessTerm n o.k (.fst sample) s
  have hm := eval_activeMaximumTerm r (clippedWitnessTerm n o.k (.fst sample)) s
  have hn := eval_normalizeTerm r (clippedWitnessTerm n o.k (.fst sample)) s
  simp only [Term.eval] at hg hm hn
  rw [hg] at hm hn
  rw [hm,htau]
  unfold acceptTrial
  norm_num only
  split_ifs with h
  · simp only [decodeWitness, Term.eval, Bool.true_eq, ite_true]
    exact congrArg some hn
  · simp [decodeWitness,noWitness,Term.eval]

end DPCut.TypedMachine
