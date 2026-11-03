import DPCut.TypedReleaseProgram
import DPCut.OracleReplacementLaw

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut.TypedMachine
attribute [local instance] Classical.propDecidable

theorem aggregate_ext {n : ℕ} {a b : Aggregate n} (hp : a.plus = b.plus)
    (hm : a.minus = b.minus) (hr : a.residual = b.residual) : a = b := by
  cases a
  cases b
  simp_all

@[fun_prop] theorem measurable_decodeAggregate (n : ℕ) : Measurable (decodeAggregate (n:=n)) :=
  measurable_aggregate_mk ((measurable_decodeWeights n).comp measurable_fst)
    ((measurable_decodeWeights n).comp (measurable_fst.comp measurable_snd))
    ((measurable_decodeWeights n).comp (measurable_snd.comp measurable_snd))

@[fun_prop] theorem measurable_decodeInner (n : ℕ) : Measurable (decodeInner (n:=n)) :=
  Measurable.ite (measurable_fst (measurableSet_singleton true))
    (measurable_some.comp
      (((measurable_decodeWeights n).comp (measurable_fst.comp measurable_snd)).prodMk
        ((measurable_decodeWeights n).comp (measurable_snd.comp measurable_snd)))) measurable_const

@[simp] theorem eval_plusTerm {Γ : List ValueType} {n : ℕ} (a : Term Γ (aggregateType n)) (s : Environment Γ) :
    decodeWeights ((plusTerm a).eval s) = (decodeAggregate (a.eval s)).plus := rfl

@[simp] theorem eval_minusTerm {Γ : List ValueType} {n : ℕ} (a : Term Γ (aggregateType n)) (s : Environment Γ) :
    decodeWeights ((minusTerm a).eval s) = (decodeAggregate (a.eval s)).minus := rfl

@[simp] theorem eval_residualTerm {Γ : List ValueType} {n : ℕ} (a : Term Γ (aggregateType n)) (s : Environment Γ) :
    decodeWeights ((residualTerm a).eval s) = (decodeAggregate (a.eval s)).residual := rfl

@[simp] theorem eval_plusDiscrepancy {Γ : List ValueType} {n : ℕ} (gamma : Term Γ .real)
    (w h r : Term Γ (weightType n)) (s : Environment Γ) :
    decodeWeights ((plusDiscrepancyTerm gamma w h r).eval s) =
      plusDiscrepancy (gamma.eval s) (decodeWeights (w.eval s)) (decodeWeights (h.eval s)) (decodeWeights (r.eval s)) := by
  rw [plusDiscrepancyTerm,eval_weightTerms]
  funext e
  norm_num [Term.eval,RealBinary.eval,plusDiscrepancy]

@[simp] theorem eval_minusDiscrepancy {Γ : List ValueType} {n : ℕ} (gamma : Term Γ .real)
    (w h r : Term Γ (weightType n)) (s : Environment Γ) :
    decodeWeights ((minusDiscrepancyTerm gamma w h r).eval s) =
      minusDiscrepancy (gamma.eval s) (decodeWeights (w.eval s)) (decodeWeights (h.eval s)) (decodeWeights (r.eval s)) := by
  rw [minusDiscrepancyTerm,eval_weightTerms]
  funext e
  norm_num [Term.eval,RealBinary.eval,minusDiscrepancy]

@[simp] theorem eval_aggregateAddTrue {Γ : List ValueType} {n : ℕ}
    (a : Term Γ (aggregateType n)) (g : Term Γ (weightType n)) (s : Environment Γ) :
    decodeAggregate ((aggregateAddTerm true a g).eval s) =
      aggregatePlusStep (decodeAggregate (a.eval s)) (decodeWeights (g.eval s)) := by
  unfold aggregateAddTerm
  simp only [ite_true,Term.eval]
  apply aggregate_ext <;>
    simp [decodeAggregate,plusTerm,minusTerm,residualTerm,aggregatePlusStep,eval_addWeights,eval_subWeights,Term.eval]

@[simp] theorem eval_aggregateAddFalse {Γ : List ValueType} {n : ℕ}
    (a : Term Γ (aggregateType n)) (g : Term Γ (weightType n)) (s : Environment Γ) :
    decodeAggregate ((aggregateAddTerm false a g).eval s) =
      aggregateMinusStep (decodeAggregate (a.eval s)) (decodeWeights (g.eval s)) := by
  unfold aggregateAddTerm
  simp only [Bool.false_eq_true,ite_false,Term.eval]
  apply aggregate_ext <;>
    simp [decodeAggregate,plusTerm,minusTerm,residualTerm,aggregateMinusStep,eval_addWeights,eval_subWeights,Term.eval]

@[simp] theorem eval_acceptsTerm {Γ : List ValueType} {n : ℕ}
    (a : Term Γ (aggregateType n)) (h : Term Γ (weightType n)) (s : Environment Γ) :
    (acceptsTerm a h).eval s = decide ((decodeAggregate (a.eval s)).Accepts (decodeWeights (h.eval s))) := by
  simp [acceptsTerm,Term.eval,Comparison.real,RealBinary.eval,Aggregate.Accepts]

@[simp] theorem eval_mwUpdateTerm {Γ : List ValueType} {n : ℕ} (M theta eta : Term Γ .real)
    (h g : Term Γ (weightType n)) (s : Environment Γ) :
    decodeWeights ((mwUpdateTerm M theta eta h g).eval s) =
      mwUpdate (M.eval s) (theta.eval s) (eta.eval s) (decodeWeights (h.eval s)) (decodeWeights (g.eval s)) := by
  unfold mwUpdateTerm
  rw [eval_weightTerms]
  funext e
  simp [Term.eval,RealBinary.eval,RealUnary.eval,eval_massTerm,mwUpdate,mass]

@[simp] theorem eval_innerNextTerm {Γ : List ValueType} {n : ℕ} (M eta : Term Γ .real)
    (h : Term Γ (weightType n)) (a : Term Γ (aggregateType n)) (s : Environment Γ)
    (c : RunConfig) (heta : eta.eval s = c.eta) :
    decodeWeights ((innerNextTerm M eta h a).eval s) =
      innerNext c (M.eval s) (decodeWeights (h.eval s)) (decodeAggregate (a.eval s)) := by
  rw [innerNextTerm,eval_mwUpdateTerm]
  simp only [Term.eval,Comparison.real,RealUnary.eval,Rat.cast_ofNat,decide_eq_true_eq,
    eval_pairingTerm,eval_minusTerm,eval_plusTerm,heta]
  unfold innerNext
  split_ifs <;> norm_num [eval_plusTerm,eval_minusTerm]

@[simp] theorem eval_initialEstimateTerm {Γ : List ValueType} {n : ℕ} (M : Term Γ .real)
    (a : Term Γ (weightType n)) (s : Environment Γ) :
    decodeWeights ((initialEstimateTerm M a).eval s) =
      initialEstimate (M.eval s) (decodeWeights (a.eval s)) := by
  rw [initialEstimateTerm,eval_weightTerms]
  funext e
  simp [Term.eval,RealBinary.eval,initialEstimate]

@[simp] theorem eval_residualUpdateTerm {Γ : List ValueType} {n : ℕ}
    (a r : Term Γ (weightType n)) (s : Environment Γ) :
    decodeWeights ((residualUpdateTerm a r).eval s) =
      residualUpdate (decodeWeights (a.eval s)) (decodeWeights (r.eval s)) := by
  rw [residualUpdateTerm,eval_weightTerms]
  funext e
  norm_num [Term.eval,RealBinary.eval,residualUpdate]

@[simp] theorem eval_noisyMassTerm {Γ : List ValueType} (cap mass noise tau : Term Γ .real) (s : Environment Γ) :
    (noisyMassTerm cap mass noise tau).eval s =
      clipNoisyMass (cap.eval s) (mass.eval s) (noise.eval s) (tau.eval s) := by
  norm_num [noisyMassTerm,Term.eval,RealBinary.eval,clipNoisyMass]

@[simp] theorem eval_clipWeightsTerm {Γ : List ValueType} {n : ℕ} (U : Term Γ .real)
    (w : Term Γ (weightType n)) (s : Environment Γ) :
    decodeWeights ((clipWeightsTerm U w).eval s) = clipWeights (U.eval s) (decodeWeights (w.eval s)) := by
  rw [clipWeightsTerm,eval_weightTerms]
  funext e
  simp [Term.eval,RealBinary.eval,clipWeights]

@[simp] theorem eval_noisyExcessTerm {Γ : List ValueType} {n : ℕ} (U V epsilon : Term Γ .real)
    (w noise : Term Γ (weightType n)) (s : Environment Γ) :
    decodeWeights ((noisyExcessTerm U V epsilon w noise).eval s) =
      noisyExcess (U.eval s) (V.eval s) (decodeWeights (w.eval s))
        (fun e => decodeWeights (noise.eval s) e/epsilon.eval s) := by
  rw [noisyExcessTerm,eval_weightTerms]
  funext e
  norm_num [Term.eval,RealBinary.eval,noisyExcess,excess]

@[simp] theorem eval_positiveTerm {Γ : List ValueType} {n : ℕ}
    (w : Term Γ (weightType n)) (s : Environment Γ) :
    decodeWeights ((positiveTerm w).eval s) = positiveWeights (decodeWeights (w.eval s)) := by
  rw [positiveTerm,eval_weightTerms]
  funext e
  norm_num [Term.eval,RealBinary.eval,positiveWeights]

end DPCut.TypedMachine
