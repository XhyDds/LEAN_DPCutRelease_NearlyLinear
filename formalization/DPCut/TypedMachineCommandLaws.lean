import DPCut.TypedMachineCommands

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

open MeasureTheory ProbabilityTheory

namespace DPCut.TypedMachine
attribute [local instance] Classical.propDecidable

theorem iterateMeasure_properties {Θ : Type*} [MeasurableSpace Θ] {a : ValueType}
    (body : Θ × a.Value → Measure (Outcome a)) (hb : Measurable body)
    (hp : ∀ p, IsProbabilityMeasure (body p)) (rounds : ℕ) :
    Measurable (fun p : Θ × a.Value => iterateMeasure (fun x => body (p.1,x)) p.2 rounds) ∧
      ∀ p : Θ × a.Value, IsProbabilityMeasure (iterateMeasure (fun x => body (p.1,x)) p.2 rounds) := by
  induction rounds with
  | zero =>
      refine ⟨Measure.measurable_dirac.comp (measurable_snd.prodMk (measurable_const.prodMk measurable_const)),?_⟩
      intro p
      simp only [iterateMeasure]
      infer_instance
  | succ rounds ih =>
      let continuation : (Θ × a.Value) × Outcome a → Measure (Outcome a) := fun p =>
        (iterateMeasure (fun x => body (p.1.1,x)) p.2.1 rounds).map (appendOutcome 2 p.2)
      have hbase : Measurable (fun p : (Θ × a.Value) × Outcome a =>
          iterateMeasure (fun x => body (p.1.1,x)) p.2.1 rounds) :=
        ih.1.comp ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))
      letI (p : (Θ × a.Value) × Outcome a) :
          IsProbabilityMeasure (iterateMeasure (fun x => body (p.1.1,x)) p.2.1 rounds) :=
        ih.2 (p.1.1,p.2.1)
      have hc : Measurable continuation := measurable_map_kernel hbase
        ((measurable_appendOutcome a a 2).comp
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
      letI (p : Θ × a.Value) : IsProbabilityMeasure (body p) := hp p
      refine ⟨measurable_bind_kernel hb hc,?_⟩
      intro p
      letI (r : Outcome a) : IsProbabilityMeasure (continuation (p,r)) :=
        Measure.isProbabilityMeasure_map
          ((measurable_appendOutcome a a 2).comp measurable_prodMk_left).aemeasurable
      exact probability_bind _ _ (hc.comp measurable_prodMk_left)

theorem Command.run_properties {Γ : List ValueType} {a : ValueType} (code : Command Γ a) :
    Measurable code.run ∧ ∀ s, IsProbabilityMeasure (code.run s) := by
  induction code with
  | pure value =>
      refine ⟨Measure.measurable_dirac.comp
        (value.measurable_eval.prodMk (measurable_const.prodMk measurable_const)),?_⟩
      intro s
      simp only [Command.run]
      infer_instance
  | normal =>
      refine ⟨measurable_const,?_⟩
      intro s
      exact Measure.isProbabilityMeasure_map (by fun_prop)
  | laplace =>
      letI := laplace_isProbabilityMeasure (by norm_num : (0:ℝ)<1)
      refine ⟨measurable_const,?_⟩
      intro s
      exact Measure.isProbabilityMeasure_map (by fun_prop)
  | factor n matrix =>
      refine ⟨Measure.measurable_dirac.comp
        (((RealMachine.measurable_factorValue n).comp matrix.measurable_eval).prodMk
          ((((RealMachine.measurable_factorOperations n).comp matrix.measurable_eval).const_add _ |>.add_const _).prodMk
            measurable_const)),?_⟩
      intro s
      simp only [Command.run]
      infer_instance
  | solver S input =>
      have hD := (measurable_decodeWeights _).comp input.measurable_eval
      refine ⟨Measure.measurable_dirac.comp ((S.measurable_result.comp hD).prodMk
        (((S.measurable_operations.comp hD).const_add _ |>.add_const _).prodMk measurable_const)),?_⟩
      intro s
      simp only [Command.run]
      infer_instance
  | @bind Γ a b first next hf hn =>
      let continuation : Environment Γ × Outcome a → Measure (Outcome b) :=
        fun p => (next.run (p.2.1,p.1)).map (appendOutcome 1 p.2)
      have hbase : Measurable (fun p : Environment Γ × Outcome a => next.run (p.2.1,p.1)) :=
        hn.1.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)
      letI (p : Environment Γ × Outcome a) : IsProbabilityMeasure (next.run (p.2.1,p.1)) := hn.2 _
      have hc : Measurable continuation := measurable_map_kernel hbase
        ((measurable_appendOutcome _ _ 1).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
      letI (s : Environment Γ) : IsProbabilityMeasure (first.run s) := hf.2 s
      refine ⟨measurable_bind_kernel hf.1 hc,?_⟩
      intro s
      letI (r : Outcome a) : IsProbabilityMeasure (continuation (s,r)) :=
        Measure.isProbabilityMeasure_map
          ((measurable_appendOutcome _ _ 1).comp measurable_prodMk_left).aemeasurable
      exact probability_bind _ _ (hc.comp measurable_prodMk_left)
  | branch condition yes no hy hn =>
      have hbase : Measurable (fun s => if condition.eval s then yes.run s else no.run s) :=
        Measurable.ite (condition.measurable_eval (measurableSet_singleton true)) hy.1 hn.1
      refine ⟨(Measure.measurable_map _ (measurable_addOperations _ _)).comp hbase,?_⟩
      intro s
      have hp : IsProbabilityMeasure (if condition.eval s then yes.run s else no.run s) := by
        split
        · exact hy.2 s
        · exact hn.2 s
      letI := hp
      exact Measure.isProbabilityMeasure_map (measurable_addOperations _ _).aemeasurable
  | @iterate Γ a count initial body ih =>
      have hb := ih.1.comp measurable_swap
      have hp (p : Environment Γ × a.Value) : IsProbabilityMeasure (body.run (p.2,p.1)) := ih.2 _
      have hloop (n) := iterateMeasure_properties (fun p => body.run (p.2,p.1)) hb hp n
      have hc : Measurable (fun p : Environment Γ × ℕ =>
          iterateMeasure (fun x => body.run (x,p.1)) (initial.eval p.1) p.2) :=
        measurable_from_prod_countable_left (fun n => (hloop n).1.comp
          (measurable_id.prodMk initial.measurable_eval))
      have hbase := hc.comp (measurable_id.prodMk count.measurable_eval)
      refine ⟨(Measure.measurable_map _ (measurable_addOperations _ _)).comp hbase,?_⟩
      intro s
      letI : IsProbabilityMeasure (iterateMeasure (fun x => body.run (x,s)) (initial.eval s) (count.eval s)) :=
        (hloop (count.eval s)).2 (s,initial.eval s)
      exact Measure.isProbabilityMeasure_map (measurable_addOperations _ _).aemeasurable

@[fun_prop] theorem Command.measurable_run {Γ : List ValueType} {a : ValueType} (code : Command Γ a) :
    Measurable code.run := code.run_properties.1

instance Command.run_probability {Γ : List ValueType} {a : ValueType} (code : Command Γ a) (s : Environment Γ) :
    IsProbabilityMeasure (code.run s) := code.run_properties.2 s

@[fun_prop] theorem Command.measurable_law {Γ : List ValueType} {a : ValueType} (code : Command Γ a) :
    Measurable code.law := (Measure.measurable_map _ measurable_fst).comp code.measurable_run

instance Command.law_probability {Γ : List ValueType} {a : ValueType} (code : Command Γ a) (s : Environment Γ) :
    IsProbabilityMeasure (code.law s) := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable

@[simp] theorem Command.law_pure {Γ : List ValueType} {a : ValueType} (value : Term Γ a) (s : Environment Γ) :
    (Command.pure value).law s = Measure.dirac (value.eval s) := by
  simp only [Command.law, Command.run]
  rw [Measure.map_dirac measurable_fst]

theorem Command.law_bind {Γ : List ValueType} {a b : ValueType}
    (first : Command Γ a) (next : Command (a :: Γ) b) (s : Environment Γ) :
    (Command.bind first next).law s = (first.law s).bind (fun x => next.law (x,s)) := by
  simp only [Command.law, Command.run]
  have hbase : Measurable (fun r : Outcome a => next.run (r.1,s)) :=
    next.measurable_run.comp (measurable_fst.prodMk measurable_const)
  have hc : Measurable (fun r : Outcome a => (next.run (r.1,s)).map (appendOutcome 1 r)) :=
    measurable_map_kernel hbase (measurable_appendOutcome a b 1)
  have hn : Measurable (fun x : a.Value => (next.run (x,s)).map Prod.fst) :=
    next.measurable_law.comp (measurable_id.prodMk measurable_const)
  rw [map_bind_eq hc measurable_fst, bind_map_eq measurable_fst hn]
  congr 1
  funext r
  have ha : Measurable (appendOutcome 1 r : Outcome b → Outcome b) :=
    (measurable_appendOutcome a b 1).comp measurable_prodMk_left
  rw [Measure.map_map measurable_fst ha]
  rfl

end DPCut.TypedMachine
