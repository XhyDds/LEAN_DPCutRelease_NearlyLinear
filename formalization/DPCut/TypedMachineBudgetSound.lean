import DPCut.TypedMachineBudget

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

open MeasureTheory ProbabilityTheory

namespace DPCut.TypedMachine

def Within {a : ValueType} (operations calls : ℕ) (r : Outcome a) : Prop :=
  r.2.1 ≤ operations ∧ r.2.2 ≤ calls

theorem measurableSet_within (a : ValueType) (operations calls : ℕ) :
    MeasurableSet {r : Outcome a | Within operations calls r} :=
  (measurableSet_le (measurable_fst.comp measurable_snd) measurable_const).inter
    (measurableSet_le (measurable_snd.comp measurable_snd) measurable_const)

theorem iterateMeasure_bound {a : ValueType} (body : a.Value → Measure (Outcome a))
    (hm : Measurable body) (hp : ∀ x, IsProbabilityMeasure (body x)) (k c : ℕ)
    (hb : ∀ x, ∀ᵐ r ∂body x, Within k c r) (rounds : ℕ) (initial : a.Value) :
    ∀ᵐ r ∂iterateMeasure body initial rounds, Within (rounds*(k+2)) (rounds*c) r := by
  have hloop (rounds : ℕ) := iterateMeasure_properties
    (fun p : Unit × a.Value => body p.2) (hm.comp measurable_snd) (fun p => hp p.2) rounds
  have hM (rounds : ℕ) : Measurable (fun x => iterateMeasure body x rounds) :=
    (hloop rounds).1.comp ((measurable_const (a := ())).prodMk measurable_id)
  induction rounds generalizing initial with
  | zero =>
      apply (ae_dirac_iff (measurableSet_within _ _ _)).mpr
      simp [Within]
  | succ rounds ih =>
      letI (r : Outcome a) : IsProbabilityMeasure (iterateMeasure body r.1 rounds) :=
        (hloop rounds).2 ((),r.1)
      letI : ∀ r : Outcome a,
          IsProbabilityMeasure (((fun x => iterateMeasure body x rounds) ∘ Prod.fst) r) :=
        fun r => (hloop rounds).2 ((),r.1)
      have hc : Measurable (fun r : Outcome a =>
          (iterateMeasure body r.1 rounds).map (appendOutcome 2 r)) :=
        measurable_map_kernel ((hM rounds).comp measurable_fst) (measurable_appendOutcome a a 2)
      apply ae_bind_of_ae_ae hc (measurableSet_within _ _ _)
      refine (hb initial).mono ?_
      intro r hr
      have ha : Measurable (appendOutcome 2 r : Outcome a → Outcome a) :=
        (measurable_appendOutcome a a 2).comp measurable_prodMk_left
      apply (ae_map_iff ha.aemeasurable (measurableSet_within _ _ _)).mpr
      refine (ih r.1).mono ?_
      intro q hq
      unfold Within appendOutcome at *
      constructor <;> simp only [Nat.succ_mul] <;> omega

theorem Budget.sound {Γ : List ValueType} {a : ValueType} {code : Command Γ a} {k c : ℕ}
    (budget : Budget code k c) (s : Environment Γ) :
    ∀ᵐ r ∂code.run s, Within k c r := by
  induction budget with
  | pure value =>
      apply (ae_dirac_iff (measurableSet_within _ _ _)).mpr
      exact ⟨le_refl _,le_refl _⟩
  | normal =>
      have hm : Measurable (fun z : ℝ => ((z,4,0) : Outcome .real)) := by fun_prop
      apply (ae_map_iff hm.aemeasurable (measurableSet_within _ _ _)).mpr
      exact Filter.Eventually.of_forall (fun _ => ⟨le_refl _,le_refl _⟩)
  | laplace =>
      have hm : Measurable (fun z : ℝ => ((z,4,0) : Outcome .real)) := by fun_prop
      apply (ae_map_iff hm.aemeasurable (measurableSet_within _ _ _)).mpr
      exact Filter.Eventually.of_forall (fun _ => ⟨le_refl _,le_refl _⟩)
  | factor n matrix =>
      apply (ae_dirac_iff (measurableSet_within _ _ _)).mpr
      exact ⟨by have h := RealMachine.factorOperations_le n (matrix.eval s); dsimp; omega,le_refl _⟩
  | solver S input =>
      apply (ae_dirac_iff (measurableSet_within _ _ _)).mpr
      exact ⟨by have h := S.operations_le (decodeWeights (input.eval s)); dsimp; omega,le_refl _⟩
  | @bind Γ a b first next k l c d hf hn ihf ihn =>
      letI (r : Outcome a) : IsProbabilityMeasure (next.run (r.1,s)) := inferInstance
      letI : ∀ r : Outcome a, IsProbabilityMeasure ((next.run ∘ fun q : Outcome a => (q.1,s)) r) :=
        fun r => Command.run_probability next (r.1,s)
      have hc : Measurable (fun r : Outcome a => (next.run (r.1,s)).map (appendOutcome 1 r)) :=
        measurable_map_kernel
          (next.measurable_run.comp (measurable_fst.prodMk measurable_const)) (measurable_appendOutcome a b 1)
      apply ae_bind_of_ae_ae hc (measurableSet_within _ _ _)
      refine (ihf s).mono ?_
      intro r hr
      have ha : Measurable (appendOutcome 1 r : Outcome b → Outcome b) :=
        (measurable_appendOutcome a b 1).comp measurable_prodMk_left
      apply (ae_map_iff ha.aemeasurable (measurableSet_within _ _ _)).mpr
      refine (ihn (r.1,s)).mono ?_
      intro q hq
      unfold Within appendOutcome at *
      constructor <;> dsimp at * <;> omega
  | @branch Γ a condition yes no k l c d hy hn ihy ihn =>
      have hm := measurable_addOperations a (condition.operations+1)
      apply (ae_map_iff hm.aemeasurable (measurableSet_within _ _ _)).mpr
      by_cases h : condition.eval s = true
      · simp only [h, ite_true]
        refine (ihy s).mono ?_
        intro r hr
        unfold Within addOperations at *
        constructor <;> dsimp at * <;> omega
      · have hfalse := Bool.eq_false_of_not_eq_true h
        simp only [hfalse, Bool.false_eq_true, ite_false]
        refine (ihn s).mono ?_
        intro r hr
        unfold Within addOperations at *
        constructor <;> dsimp at * <;> omega
  | @iterate Γ a rounds initial body k c hb ih =>
      have hm := measurable_addOperations a (initial.operations+2)
      simp only [Command.run, Term.eval, Term.operations]
      rw [show 1+initial.operations+1 = initial.operations+2 by omega]
      change ∀ᵐ r ∂(iterateMeasure (fun x => body.run (x,s)) (initial.eval s) rounds).map
        (addOperations (initial.operations+2)), Within _ _ r
      apply (ae_map_iff hm.aemeasurable (measurableSet_within _ _ _)).mpr
      have hi := iterateMeasure_bound (fun x => body.run (x,s))
        (body.measurable_run.comp (measurable_id.prodMk measurable_const))
        (fun _ => inferInstance) k c (fun x => ih (x,s)) rounds (initial.eval s)
      refine hi.mono ?_
      intro r hr
      unfold Within addOperations at *
      constructor <;> dsimp at * <;> omega
  | mono hb hk hc ih =>
      refine (ih s).mono ?_
      intro r hr
      exact ⟨hr.1.trans hk,hr.2.trans hc⟩

theorem BoundedCommand.bound {Γ : List ValueType} {a : ValueType} (code : BoundedCommand Γ a) (s : Environment Γ) :
    ∀ᵐ r ∂code.code.run s, r.2.1 ≤ code.operations ∧ r.2.2 ≤ code.solverCalls :=
  code.budget.sound s

end DPCut.TypedMachine
