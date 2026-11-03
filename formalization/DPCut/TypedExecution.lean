import DPCut.TypedTermExecution
import DPCut.TypedMachineBudget

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace DPCut.TypedMachine

mutual
  inductive Executes : {Γ : List ValueType} → {a : ValueType} →
      Command Γ a → Environment Γ → Outcome a → Prop where
    | pure {Γ a} (value : Term Γ a) (s : Environment Γ) :
        Executes (.pure value) s (value.eval s,value.operations+1,0)
    | normal {Γ} (s : Environment Γ) (z : ℝ) : Executes .normal s (z,4,0)
    | laplace {Γ} (s : Environment Γ) (z : ℝ) : Executes .laplace s (z,4,0)
    | factor {Γ} (n : ℕ) (matrix : Term Γ (matrixType n)) (s : Environment Γ) :
        Executes (.factor n matrix) s (RealMachine.factorValue n (matrix.eval s),
          matrix.operations+RealMachine.factorOperations n (matrix.eval s)+1,0)
    | solver {Γ n} (S : SolverData n) (input : Term Γ (weightType n)) (s : Environment Γ) :
        Executes (.solver S input) s (S.result (decodeWeights (input.eval s)),
          input.operations+S.operations (decodeWeights (input.eval s))+1,1)
    | bind {Γ a b} {first : Command Γ a} {next : Command (a :: Γ) b} {s : Environment Γ}
        {r : Outcome a} {q : Outcome b} (hf : Executes first s r) (hn : Executes next (r.1,s) q) :
        Executes (.bind first next) s (appendOutcome 1 r q)
    | yes {Γ a} {condition : Term Γ .boolean} {yes no : Command Γ a} {s : Environment Γ} {r : Outcome a}
        (hc : condition.eval s = true) (h : Executes yes s r) :
        Executes (.branch condition yes no) s (addOperations (condition.operations+1) r)
    | no {Γ a} {condition : Term Γ .boolean} {yes no : Command Γ a} {s : Environment Γ} {r : Outcome a}
        (hc : condition.eval s = false) (h : Executes no s r) :
        Executes (.branch condition yes no) s (addOperations (condition.operations+1) r)
    | iterate {Γ a} {count : Term Γ .natural} {initial : Term Γ a} {body : Command (a :: Γ) a}
        {s : Environment Γ} {r : Outcome a} (h : Iterations body s (count.eval s) (initial.eval s) r) :
        Executes (.iterate count initial body) s (addOperations (count.operations+initial.operations+1) r)

  inductive Iterations : {Γ : List ValueType} → {a : ValueType} →
      Command (a :: Γ) a → Environment Γ → ℕ → a.Value → Outcome a → Prop where
    | zero {Γ a} (body : Command (a :: Γ) a) (s : Environment Γ) (initial : a.Value) :
        Iterations body s 0 initial (initial,0,0)
    | succ {Γ a} {body : Command (a :: Γ) a} {s : Environment Γ} {rounds : ℕ} {initial : a.Value}
        {first next : Outcome a} (hf : Executes body (initial,s) first)
        (hn : Iterations body s rounds first.1 next) :
        Iterations body s (rounds+1) initial (appendOutcome 2 first next)
end

theorem iterations_bound {Γ : List ValueType} {a : ValueType} {body : Command (a :: Γ) a}
    (k c : ℕ) (hb : ∀ s r, Executes body s r → r.2.1 ≤ k ∧ r.2.2 ≤ c)
    {s : Environment Γ} {rounds : ℕ} {initial : a.Value} {r : Outcome a}
    (trace : Iterations body s rounds initial r) :
    r.2.1 ≤ rounds*(k+2) ∧ r.2.2 ≤ rounds*c := by
  induction rounds generalizing initial r with
  | zero => cases trace; simp
  | succ rounds ih =>
      cases trace with
      | succ hf hn =>
          have h := hb _ _ hf
          have hi := ih hn
          simp only [appendOutcome,Nat.succ_mul]
          constructor <;> omega

theorem Budget.execution_bound {Γ : List ValueType} {a : ValueType} {code : Command Γ a} {k c : ℕ}
    (budget : Budget code k c) :
    ∀ s r, Executes code s r → r.2.1 ≤ k ∧ r.2.2 ≤ c := by
  induction budget with
  | pure value =>
      intro s r trace
      cases trace
      exact ⟨le_refl _,le_refl _⟩
  | normal | laplace =>
      intro s r trace
      cases trace
      exact ⟨le_refl _,le_refl _⟩
  | factor n matrix =>
      intro s r trace
      cases trace
      have h := RealMachine.factorOperations_le n (matrix.eval s)
      constructor <;> dsimp <;> omega
  | solver S input =>
      intro s r trace
      cases trace
      have h := S.operations_le (decodeWeights (input.eval s))
      constructor <;> dsimp <;> omega
  | bind hf hn ihf ihn =>
      intro s r trace
      cases trace with
      | bind ht₁ ht₂ =>
          have h₁ := ihf _ _ ht₁
          have h₂ := ihn _ _ ht₂
          unfold appendOutcome
          constructor <;> dsimp <;> omega
  | branch condition hy hn ihy ihn =>
      intro s r trace
      cases trace with
      | yes _ h =>
          have ht := ihy _ _ h
          unfold addOperations
          constructor <;> dsimp <;> omega
      | no _ h =>
          have ht := ihn _ _ h
          unfold addOperations
          constructor <;> dsimp <;> omega
  | iterate rounds initial hb ih =>
      intro s r trace
      cases trace with
      | iterate h =>
          have ht := iterations_bound _ _ ih h
          simp only [Term.eval,Term.operations] at ht ⊢
          unfold addOperations
          constructor <;> dsimp <;> omega
  | mono hb hk hc ih =>
      intro s r trace
      exact ⟨(ih s r trace).1.trans hk,(ih s r trace).2.trans hc⟩

theorem BoundedCommand.execution_bound {Γ : List ValueType} {a : ValueType}
    (code : BoundedCommand Γ a) (s : Environment Γ) (r : Outcome a) (trace : Executes code.code s r) :
    r.2.1 ≤ code.operations ∧ r.2.2 ≤ code.solverCalls :=
  code.budget.execution_bound s r trace

theorem Command.execution_exists {Γ : List ValueType} {a : ValueType} (code : Command Γ a) :
    ∀ s, ∃ r, Executes code s r := by
  induction code with
  | pure value => intro s; exact ⟨_,Executes.pure value s⟩
  | normal => intro s; exact ⟨_,Executes.normal s 0⟩
  | laplace => intro s; exact ⟨_,Executes.laplace s 0⟩
  | factor n matrix => intro s; exact ⟨_,Executes.factor n matrix s⟩
  | solver S input => intro s; exact ⟨_,Executes.solver S input s⟩
  | bind first next hf hn =>
      intro s
      obtain ⟨r,hr⟩ := hf s
      obtain ⟨q,hq⟩ := hn (r.1,s)
      exact ⟨_,Executes.bind hr hq⟩
  | branch condition yes no hy hn =>
      intro s
      cases hc : condition.eval s
      · obtain ⟨r,hr⟩ := hn s
        exact ⟨_,Executes.no hc hr⟩
      · obtain ⟨r,hr⟩ := hy s
        exact ⟨_,Executes.yes hc hr⟩
  | @iterate Γ a count initial body ih =>
      intro s
      have hloop (rounds : ℕ) (x : a.Value) : ∃ r, Iterations body s rounds x r := by
        induction rounds generalizing x with
        | zero => exact ⟨_,Iterations.zero body s x⟩
        | succ rounds hn =>
            obtain ⟨r,hr⟩ := ih (x,s)
            obtain ⟨q,hq⟩ := hn r.1
            exact ⟨_,Iterations.succ hr hq⟩
      obtain ⟨r,hr⟩ := hloop (count.eval s) (initial.eval s)
      exact ⟨_,Executes.iterate hr⟩

end DPCut.TypedMachine
