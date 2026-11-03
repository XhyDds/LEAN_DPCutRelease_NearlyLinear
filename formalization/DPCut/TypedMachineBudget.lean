import DPCut.TypedMachineCommandLaws

set_option autoImplicit false
noncomputable section

namespace DPCut.TypedMachine

inductive Budget : {Γ : List ValueType} → {a : ValueType} → Command Γ a → ℕ → ℕ → Prop where
  | pure {Γ a} (value : Term Γ a) : Budget (.pure value) (value.operations+1) 0
  | normal {Γ} : Budget (Command.normal (Γ := Γ)) 4 0
  | laplace {Γ} : Budget (Command.laplace (Γ := Γ)) 4 0
  | factor {Γ} (n : ℕ) (matrix : Term Γ (matrixType n)) :
      Budget (.factor n matrix) (matrix.operations+100*(n+1)^3+1) 0
  | solver {Γ n} (S : SolverData n) (input : Term Γ (weightType n)) :
      Budget (.solver S input) (input.operations+S.operationBound+1) 1
  | bind {Γ a b} {first : Command Γ a} {next : Command (a :: Γ) b} {k l c d}
      (hf : Budget first k c) (hn : Budget next l d) : Budget (.bind first next) (k+l+1) (c+d)
  | branch {Γ a} (condition : Term Γ .boolean) {yes no : Command Γ a} {k l c d}
      (hy : Budget yes k c) (hn : Budget no l d) :
      Budget (.branch condition yes no) (condition.operations+1+max k l) (max c d)
  | iterate {Γ a} (rounds : ℕ) (initial : Term Γ a) {body : Command (a :: Γ) a} {k c}
      (hb : Budget body k c) :
      Budget (.iterate (.natural rounds) initial body) (initial.operations+2+rounds*(k+2)) (rounds*c)
  | mono {Γ a} {code : Command Γ a} {k l c d} (hb : Budget code k c) (hk : k ≤ l) (hc : c ≤ d) :
      Budget code l d

/-- An assembly-time certificate generated from the restricted instruction
syntax. Unlike a law paired with a number, the numbers require a derivation. -/
structure BoundedCommand (Γ : List ValueType) (a : ValueType) where
  code : Command Γ a
  operations : ℕ
  solverCalls : ℕ
  budget : Budget code operations solverCalls

def BoundedCommand.pure {Γ : List ValueType} {a : ValueType} (value : Term Γ a) : BoundedCommand Γ a :=
  ⟨.pure value,value.operations+1,0,Budget.pure value⟩

def BoundedCommand.normal (Γ : List ValueType) : BoundedCommand Γ .real :=
  ⟨.normal,4,0,Budget.normal⟩

def BoundedCommand.laplace (Γ : List ValueType) : BoundedCommand Γ .real :=
  ⟨.laplace,4,0,Budget.laplace⟩

def BoundedCommand.factor {Γ : List ValueType} (n : ℕ) (matrix : Term Γ (matrixType n)) :
    BoundedCommand Γ (matrixType n) :=
  ⟨.factor n matrix,matrix.operations+100*(n+1)^3+1,0,Budget.factor n matrix⟩

def BoundedCommand.solver {Γ : List ValueType} {n : ℕ} (S : SolverData n) (input : Term Γ (weightType n)) :
    BoundedCommand Γ (matrixType n) :=
  ⟨.solver S input,input.operations+S.operationBound+1,1,Budget.solver S input⟩

def BoundedCommand.bind {Γ : List ValueType} {a b : ValueType}
    (first : BoundedCommand Γ a) (next : BoundedCommand (a :: Γ) b) : BoundedCommand Γ b :=
  ⟨.bind first.code next.code,first.operations+next.operations+1,first.solverCalls+next.solverCalls,
    Budget.bind first.budget next.budget⟩

def BoundedCommand.branch {Γ : List ValueType} {a : ValueType} (condition : Term Γ .boolean)
    (yes no : BoundedCommand Γ a) : BoundedCommand Γ a :=
  ⟨.branch condition yes.code no.code,condition.operations+1+max yes.operations no.operations,
    max yes.solverCalls no.solverCalls,Budget.branch condition yes.budget no.budget⟩

def BoundedCommand.iterate {Γ : List ValueType} {a : ValueType} (rounds : ℕ)
    (initial : Term Γ a) (body : BoundedCommand (a :: Γ) a) : BoundedCommand Γ a :=
  ⟨.iterate (.natural rounds) initial body.code,initial.operations+2+rounds*(body.operations+2),
    rounds*body.solverCalls,Budget.iterate rounds initial body.budget⟩

end DPCut.TypedMachine
