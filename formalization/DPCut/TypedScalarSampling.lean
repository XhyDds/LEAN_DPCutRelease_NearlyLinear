import DPCut.TypedWitnessNormalization
import DPCut.ScalarGaussianSampling

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut.TypedMachine

def scalarLaw : Bool → Measure ℝ
  | false => DPCut.laplace 1
  | true => gaussianReal 0 1

instance scalarLaw_probability (normal : Bool) : IsProbabilityMeasure (scalarLaw normal) := by
  cases normal
  · change IsProbabilityMeasure (DPCut.laplace 1)
    exact laplace_isProbabilityMeasure (by norm_num : (0:ℝ)<1)
  · change IsProbabilityMeasure (gaussianReal 0 1)
    exact instIsProbabilityMeasureGaussianReal 0 1

def scalarDraw : Bool → (Γ : List ValueType) → BoundedCommand Γ .real
  | false, Γ => BoundedCommand.laplace Γ
  | true, Γ => BoundedCommand.normal Γ

def prependTerm {Γ : List ValueType} (n : ℕ) :
    Term (.array n .real :: .real :: Γ) (.array (n+1) .real) :=
  .array (fun i => Fin.cases (.read (.tail .head)) (fun j => (newest : Term _ (.array n .real)).at j) i)

def scalarArray (normal : Bool) : (n : ℕ) → (Γ : List ValueType) → BoundedCommand Γ (.array n .real)
  | 0, Γ => .pure (.array (fun i : Fin 0 => Fin.elim0 i))
  | n+1, Γ => (scalarDraw normal Γ).bind
      ((scalarArray normal n (.real :: Γ)).bind (.pure (prependTerm n)))

@[simp] theorem eval_prependTerm {Γ : List ValueType} (n : ℕ) (z : Fin n → ℝ) (x : ℝ) (s : Environment Γ) :
    (prependTerm n).eval (z,x,s) = MatrixElimination.prepend x z := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [prependTerm, Term.eval, newest, Local.read, MatrixElimination.prepend]

theorem scalarDraw_law (normal : Bool) (Γ : List ValueType) (s : Environment Γ) :
    (scalarDraw normal Γ).code.law s = scalarLaw normal := by
  cases normal <;>
    simp only [scalarDraw, scalarLaw, BoundedCommand.normal, BoundedCommand.laplace, Bool.true_eq, Bool.false_eq_true,
      ite_true, ite_false, Command.law, Command.run]
  all_goals
    rw [Measure.map_map measurable_fst (by fun_prop)]
    change Measure.map id _ = _
    rw [Measure.map_id]

theorem scalarArray_law (normal : Bool) (n : ℕ) (Γ : List ValueType) (s : Environment Γ) :
    (scalarArray normal n Γ).code.law s = Measure.pi (fun _ : Fin n => scalarLaw normal) := by
  rw [← scalarProduct_law (scalarLaw normal)]
  induction n generalizing Γ with
  | zero =>
      rw [scalarArray, BoundedCommand.pure, Command.law_pure]
      change Measure.dirac _ = Measure.dirac (Fin.elim0 : Fin 0 → ℝ)
      congr 1
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      change (Command.bind (scalarDraw normal Γ).code
        (Command.bind (scalarArray normal n (.real :: Γ)).code (Command.pure (prependTerm n)))).law s = _
      rw [Command.law_bind, scalarDraw_law]
      simp only [scalarProduct, CostedLaw.bind_law, CostedLaw.sample, CostedLaw.map_law]
      congr 1
      funext x
      rw [Command.law_bind, ih (.real :: Γ) (x,s)]
      simp only [Command.law_pure, eval_prependTerm]
      have hm : Measurable (MatrixElimination.prepend x : (Fin n → ℝ) → Fin (n+1) → ℝ) :=
        (MatrixElimination.measurable_prepend n).comp measurable_prodMk_left
      exact Measure.bind_dirac_eq_map _ hm

theorem scalarArray_operations (normal : Bool) (n : ℕ) (Γ : List ValueType) :
    (scalarArray normal n Γ).operations ≤ 30*(n+1)^2 := by
  induction n generalizing Γ with
  | zero => norm_num [scalarArray, BoundedCommand.pure, Term.operations]
  | succ n ih =>
      have hdraw : (scalarDraw normal Γ).operations = 4 := by
        cases normal <;> rfl
      have hprepend : (prependTerm (Γ := Γ) n).operations ≤ 8*(n+1)+1 := by
        let items : Fin (n+1) → Term (.array n .real :: .real :: Γ) .real :=
          fun i => Fin.cases (.read (.tail .head)) (fun j => (newest : Term _ (.array n .real)).at j) i
        change (∑ i, (items i).operations)+(n+1)+1 ≤ _
        have hitems (i : Fin (n+1)) : (items i).operations ≤ 7 := by
          refine Fin.cases ?_ (fun j => ?_) i <;>
            norm_num [items, Term.at, newest, Term.operations, Local.operations]
        have hsum : (∑ i : Fin (n+1), (items i).operations) ≤ 7*(n+1) := by
          calc
            _ ≤ ∑ _ : Fin (n+1), 7 := Finset.sum_le_sum (fun i _ => hitems i)
            _ = _ := by simp [Nat.mul_comm]
        omega
      simp only [scalarArray, BoundedCommand.bind, BoundedCommand.pure, hdraw]
      nlinarith [ih (.real :: Γ)]

theorem scalarArray_calls (normal : Bool) (n : ℕ) (Γ : List ValueType) :
    (scalarArray normal n Γ).solverCalls = 0 := by
  induction n generalizing Γ with
  | zero => rfl
  | succ n ih =>
      have hdraw : (scalarDraw normal Γ).solverCalls = 0 := by cases normal <;> rfl
      simp only [scalarArray, BoundedCommand.bind, BoundedCommand.pure, hdraw, ih, Nat.zero_add]

end DPCut.TypedMachine
