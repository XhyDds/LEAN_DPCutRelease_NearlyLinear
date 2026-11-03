import DPCut.TypedMachineBudgetSound

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut.TypedMachine
attribute [local instance] Classical.propDecidable

@[simp] theorem Command.law_branch {Γ : List ValueType} {a : ValueType}
    (condition : Term Γ .boolean) (yes no : Command Γ a) (s : Environment Γ) :
    (Command.branch condition yes no).law s =
      if condition.eval s then yes.law s else no.law s := by
  have hm := measurable_addOperations a (condition.operations+1)
  simp only [Command.law, Command.run]
  rw [Measure.map_map measurable_fst hm]
  by_cases h : condition.eval s = true <;> simp only [h, Bool.false_eq_true, ite_true, ite_false]
  · rfl
  · rfl

@[simp] theorem Command.law_normal {Γ : List ValueType} (s : Environment Γ) :
    (Command.normal (Γ := Γ)).law s = gaussianReal 0 1 := by
  unfold Command.law
  rw [Command.run, Measure.map_map measurable_fst (by fun_prop)]
  exact Measure.map_id

@[simp] theorem Command.law_laplace {Γ : List ValueType} (s : Environment Γ) :
    (Command.laplace (Γ := Γ)).law s = DPCut.laplace 1 := by
  unfold Command.law
  rw [Command.run, Measure.map_map measurable_fst (by fun_prop)]
  exact Measure.map_id

@[simp] theorem Command.law_factor {Γ : List ValueType} (n : ℕ) (matrix : Term Γ (matrixType n)) (s : Environment Γ) :
    (Command.factor n matrix).law s = Measure.dirac (MatrixElimination.factor (matrix.eval s)) := by
  simp only [Command.law, Command.run, Measure.map_dirac measurable_fst, RealMachine.factorValue_eq]

@[simp] theorem Command.law_solver {Γ : List ValueType} {n : ℕ} (S : SolverData n)
    (input : Term Γ (weightType n)) (s : Environment Γ) :
    (Command.solver S input).law s = Measure.dirac (S.result (decodeWeights (input.eval s))) := by
  simp only [Command.law, Command.run, Measure.map_dirac measurable_fst]

def iterateLaw {a : ValueType} (body : a.Value → Measure a.Value) (initial : a.Value) : ℕ → Measure a.Value
  | 0 => Measure.dirac initial
  | n+1 => (body initial).bind fun x => iterateLaw body x n

theorem iterateLaw_properties {a : ValueType} (body : a.Value → Measure a.Value)
    (hm : Measurable body) (hp : ∀ x, IsProbabilityMeasure (body x)) (rounds : ℕ) :
    Measurable (fun x => iterateLaw body x rounds) ∧ ∀ x, IsProbabilityMeasure (iterateLaw body x rounds) := by
  induction rounds with
  | zero =>
      refine ⟨Measure.measurable_dirac,?_⟩
      intro x
      change IsProbabilityMeasure (Measure.dirac x)
      infer_instance
  | succ n ih =>
      letI (x : a.Value) := hp x
      letI (x : a.Value) := ih.2 x
      have hcont : Measurable (fun p : a.Value × a.Value => iterateLaw body p.2 n) := ih.1.comp measurable_snd
      exact ⟨measurable_bind_kernel hm hcont,fun x => probability_bind _ _ ih.1⟩

theorem iterateMeasure_law {a : ValueType} (body : a.Value → Measure (Outcome a))
    (hm : Measurable body) (hp : ∀ x, IsProbabilityMeasure (body x)) (initial : a.Value) (rounds : ℕ) :
    (iterateMeasure body initial rounds).map Prod.fst =
      iterateLaw (fun x => (body x).map Prod.fst) initial rounds := by
  have hloop (n) := iterateMeasure_properties (fun p : Unit × a.Value => body p.2)
    (hm.comp measurable_snd) (fun p => hp p.2) n
  have hiter (n) : Measurable (fun x => iterateMeasure body x n) :=
    (hloop n).1.comp ((measurable_const (a:=())).prodMk measurable_id)
  let law := fun x => (body x).map Prod.fst
  have hlaw : Measurable law := (Measure.measurable_map _ measurable_fst).comp hm
  have hplaw (x) : IsProbabilityMeasure (law x) := by
    letI := hp x
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  induction rounds generalizing initial with
  | zero => rw [iterateMeasure, Measure.map_dirac measurable_fst]; rfl
  | succ n ih =>
      letI (r : Outcome a) : IsProbabilityMeasure (iterateMeasure body r.1 n) := (hloop n).2 ((),r.1)
      letI : ∀ r : Outcome a,
          IsProbabilityMeasure (((fun x => iterateMeasure body x n) ∘ Prod.fst) r) :=
        fun r => (hloop n).2 ((),r.1)
      have hc : Measurable (fun r : Outcome a => (iterateMeasure body r.1 n).map (appendOutcome 2 r)) :=
        measurable_map_kernel ((hiter n).comp measurable_fst) (measurable_appendOutcome a a 2)
      rw [iterateMeasure, map_bind_eq hc measurable_fst, iterateLaw,
        bind_map_eq measurable_fst (iterateLaw_properties law hlaw hplaw n).1]
      congr 1
      funext r
      have ha : Measurable (appendOutcome 2 r : Outcome a → Outcome a) :=
        (measurable_appendOutcome a a 2).comp measurable_prodMk_left
      rw [Measure.map_map measurable_fst ha]
      exact ih r.1

theorem Command.law_iterate {Γ : List ValueType} {a : ValueType}
    (count : Term Γ .natural) (initial : Term Γ a) (body : Command (a :: Γ) a) (s : Environment Γ) :
    (Command.iterate count initial body).law s =
      iterateLaw (fun x => body.law (x,s)) (initial.eval s) (count.eval s) := by
  unfold Command.law
  rw [Command.run, Measure.map_map measurable_fst (measurable_addOperations _ _)]
  exact iterateMeasure_law (fun x => body.run (x,s))
    (body.measurable_run.comp (measurable_id.prodMk measurable_const)) (fun _ => inferInstance) _ _

end DPCut.TypedMachine
