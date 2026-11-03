import DPCut.TypedAggregateLaw

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut.TypedMachine
attribute [local instance] Classical.propDecidable

theorem innerStep_halted {Γ : List ValueType} {n : ℕ} (S : SolverData n) (k K : ℕ)
    (terms : OracleTerms Γ) (gamma eta M : Term Γ .real) (w : Term Γ (weightType n))
    (s : Environment Γ) (state : (innerResultType n).Value) :
    (innerStep S k K terms gamma eta M w).code.law ((true,state),s) = Measure.dirac (true,state) := by
  simp only [innerStep,BoundedCommand.branch,Command.law_branch,Term.eval,newest,Local.read,ite_true,
    BoundedCommand.pure,Command.law_pure]

theorem innerStopLoop_eq {Γ : List ValueType} {n : ℕ} (S : SolverData n) (p : Parameters) (c : RunConfig)
    (he : 0 < c.oracle.eps1) (B : ℝ) (terms : OracleTerms Γ) (gamma eta M : Term Γ .real)
    (w : Term Γ (weightType n)) (s : Environment Γ) (hs : terms.Matches c.oracle B s)
    (hgamma : gamma.eval s = p.gamma) (heta : eta.eval s = c.eta)
    (rounds : ℕ) (h r : (weightType n).Value) :
    stopLoop (guardedKernel (innerStep S c.oracle.k c.oracle.K terms gamma eta M w).code s)
      decodeInner (false,(h,r)) rounds =
      OracleReplacement.innerLoop (numericalWitnessKernel S c.oracle he B) p c
        (decodeWeights (w.eval s)) (M.eval s) rounds (decodeWeights h) := by
  let K := numericalWitnessKernel S c.oracle he B
  let body := (innerStep S c.oracle.k c.oracle.K terms gamma eta M w).code
  let loop := guardedKernel body s
  letI : IsMarkovKernel loop := guardedKernel_markov body s
  induction rounds generalizing h r with
  | zero => rfl
  | succ rounds ih =>
      let R : (innerStateType n).Value → Measure (Option (Weights n × Weights n)) :=
        fun result => if result.1 then Measure.dirac (decodeInner result.2)
          else stopLoop loop decodeInner result.2 rounds
      have hR : Measurable R := Measurable.ite (measurable_fst (measurableSet_singleton true))
        (Measure.measurable_dirac.comp ((measurable_decodeInner n).comp measurable_snd))
        ((stopLoop_measurable loop decodeInner (measurable_decodeInner n) rounds).comp measurable_snd)
      change (body.law ((false,(false,(h,r))),s)).bind R = _
      simp only [body,innerStep,BoundedCommand.branch,BoundedCommand.bind,BoundedCommand.pure,
        Command.law_branch,Term.eval,newest,Local.read,Bool.false_eq_true,ite_false]
      rw [law_bind_continue _ _ _ _ hR]
      let hTerm : Term (innerStateType n :: Γ) (weightType n) := .fst (.snd (.snd newest))
      let next : Command (aggregateType n :: innerStateType n :: Γ) (innerStateType n) :=
        Command.branch (acceptsTerm newest hTerm.weaken)
          (.pure (.pair (.boolean true) (.pair (.boolean true) (.pair hTerm.weaken (residualTerm newest)))))
          (.pure (.pair (.boolean false) (.pair (.boolean false)
            (.pair (innerNextTerm M.weaken.weaken eta.weaken.weaken hTerm.weaken newest) (zeroWeights n)))))
      let F : Aggregate n → Measure (Option (Weights n × Weights n)) := fun a =>
        if a.Accepts (decodeWeights h) then Measure.dirac (some (decodeWeights h,a.residual)) else
          OracleReplacement.innerLoop K p c (decodeWeights (w.eval s)) (M.eval s) rounds
            (innerNext c (M.eval s) (decodeWeights h) a)
      have hF : Measurable F :=
        OracleReplacement.measurable_inner_continuation K p c (decodeWeights (w.eval s))
          (decodeWeights h) (M.eval s) rounds
      have hnext (a : (aggregateType n).Value) :
          (next.law (a,(false,(false,(h,r))),s)).bind R = F (decodeAggregate a) := by
        dsimp only [next]
        rw [Command.law_branch,eval_acceptsTerm]
        simp only [Term.eval_weaken_env,Term.eval,newest,Local.read,hTerm]
        by_cases ha : (decodeAggregate a).Accepts (decodeWeights h)
        · simp only [ha,decide_true,ite_true]
          rw [law_pure_continue _ _ _ hR]
          dsimp only [F]
          rw [if_pos ha]
          simp only [R,decodeInner,Term.eval,newest,Local.read,hTerm,Term.eval_weaken_env,ite_true]
          rfl
        · simp only [ha,decide_false,Bool.false_eq_true,ite_false]
          rw [law_pure_continue _ _ _ hR]
          let updated : Term (aggregateType n :: innerStateType n :: Γ) (weightType n) :=
            innerNextTerm M.weaken.weaken eta.weaken.weaken hTerm.weaken newest
          let zeros : Term (aggregateType n :: innerStateType n :: Γ) (weightType n) := zeroWeights n
          change stopLoop loop decodeInner
            (false,(updated.eval (a,(false,(false,(h,r))),s),zeros.eval (a,(false,(false,(h,r))),s))) rounds = _
          rw [ih]
          dsimp only [F]
          rw [if_neg ha]
          congr 1
          simpa only [Term.eval_weaken_env,Term.eval,newest,Local.read,hTerm] using
            eval_innerNextTerm (Γ := aggregateType n :: innerStateType n :: Γ)
              M.weaken.weaken eta.weaken.weaken hTerm.weaken newest
              (a,(false,(false,(h,r))),s) c (by simpa using heta)
      change ((aggregateCommand S c.oracle.k c.oracle.K terms.weaken gamma.weaken w.weaken hTerm).code.law
        ((false,(false,(h,r))),s)).bind (fun a => (next.law (a,(false,(false,(h,r))),s)).bind R) = _
      simp_rw [hnext]
      rw [← bind_map_eq (measurable_decodeAggregate n) hF]
      have hs0 : (terms.weaken : OracleTerms (innerStateType n :: Γ)).Matches c.oracle B ((false,(false,(h,r))),s) :=
        OracleTerms.Matches.weaken (a := innerStateType n) terms c.oracle B s hs (false,(false,(h,r)))
      rw [aggregateCommand_law S c.oracle he B terms.weaken gamma.weaken w.weaken hTerm
        ((false,(false,(h,r))),s) hs0]
      simp only [Term.eval_weaken_env,Term.eval,newest,Local.read,hTerm,hgamma]
      rfl

theorem innerCommand_law {Γ : List ValueType} {n : ℕ} (S : SolverData n) (p : Parameters) (c : RunConfig)
    (he : 0 < c.oracle.eps1) (B : ℝ) (terms : OracleTerms Γ) (gamma eta M : Term Γ .real)
    (w initial : Term Γ (weightType n)) (s : Environment Γ) (hs : terms.Matches c.oracle B s)
    (hgamma : gamma.eval s = p.gamma) (heta : eta.eval s = c.eta) :
    ((innerCommand S c.oracle.k c.oracle.K c.T2 terms gamma eta M w initial).code.law s).map decodeInner =
      OracleReplacement.innerLoop (numericalWitnessKernel S c.oracle he B) p c
        (decodeWeights (w.eval s)) (M.eval s) c.T2 (decodeWeights (initial.eval s)) := by
  let body := (innerStep S c.oracle.k c.oracle.K terms gamma eta M w).code
  simp only [innerCommand,BoundedCommand.bind,BoundedCommand.pure]
  rw [law_bind_pure,BoundedCommand.iterate,Command.law_iterate]
  simp only [Term.eval,newest,Local.read]
  have hproj : Measurable (fun x : (innerStateType n).Value => x.2) := measurable_snd
  rw [Measure.map_map (measurable_decodeInner n) hproj]
  have hi := guardedIteration_finish body s (innerStep_halted S c.oracle.k c.oracle.K terms gamma eta M w s)
    decodeInner (measurable_decodeInner n) (false,(initial.eval s,(zeroWeights n).eval s)) c.T2
  change (iterateLaw (fun state => body.law (state,s)) (false,(false,(initial.eval s,(zeroWeights n).eval s)))
    c.T2).map (fun state => decodeInner state.2) = _
  rw [hi]
  exact innerStopLoop_eq S p c he B terms gamma eta M w s hs hgamma heta _ _ _

end DPCut.TypedMachine
