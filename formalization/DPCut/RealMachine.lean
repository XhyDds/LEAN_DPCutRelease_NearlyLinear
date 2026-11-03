import Mathlib

/-!
An operational real-arithmetic register machine. Programs cannot insert a
semantic function, an optimization result, or a claimed cost as an instruction.
Every expression is built from registers, rational literals, and the explicitly
listed elementary operations. Gaussian and Laplace instructions consume one
scalar from their respective random tapes.
-/
set_option autoImplicit false
noncomputable section

namespace DPCut.RealMachine

inductive RegisterType where
  | real
  | natural
  | boolean
  deriving DecidableEq

abbrev RegisterType.Value : RegisterType → Type
  | .real => ℝ
  | .natural => ℕ
  | .boolean => Bool

structure Memory where
  real : ℕ → ℝ
  natural : ℕ → ℕ
  boolean : ℕ → Bool

def Memory.zero : Memory := ⟨fun _ => 0, fun _ => 0, fun _ => false⟩

def Memory.writeReal (s : Memory) (address : ℕ) (value : ℝ) : Memory :=
  { s with real := Function.update s.real address value }

def Memory.writeNatural (s : Memory) (address value : ℕ) : Memory :=
  { s with natural := Function.update s.natural address value }

def Memory.writeBoolean (s : Memory) (address : ℕ) (value : Bool) : Memory :=
  { s with boolean := Function.update s.boolean address value }

inductive Expr : RegisterType → Type where
  | rational (value : ℚ) : Expr .real
  | natural (value : ℕ) : Expr .natural
  | boolean (value : Bool) : Expr .boolean
  | readReal (address : Expr .natural) : Expr .real
  | readNatural (address : Expr .natural) : Expr .natural
  | readBoolean (address : Expr .natural) : Expr .boolean
  | cast (value : Expr .natural) : Expr .real
  | ceil (value : Expr .real) : Expr .natural
  | floor (value : Expr .real) : Expr .natural
  | natAdd (left right : Expr .natural) : Expr .natural
  | natSub (left right : Expr .natural) : Expr .natural
  | natMul (left right : Expr .natural) : Expr .natural
  | natDiv (left right : Expr .natural) : Expr .natural
  | add (left right : Expr .real) : Expr .real
  | sub (left right : Expr .real) : Expr .real
  | mul (left right : Expr .real) : Expr .real
  | div (left right : Expr .real) : Expr .real
  | neg (value : Expr .real) : Expr .real
  | sqrt (value : Expr .real) : Expr .real
  | log (value : Expr .real) : Expr .real
  | exp (value : Expr .real) : Expr .real
  | select (condition : Expr .boolean) (yes no : Expr .real) : Expr .real
  | le (left right : Expr .real) : Expr .boolean
  | lt (left right : Expr .real) : Expr .boolean
  | eq (left right : Expr .real) : Expr .boolean
  | natLe (left right : Expr .natural) : Expr .boolean
  | natLt (left right : Expr .natural) : Expr .boolean
  | natEq (left right : Expr .natural) : Expr .boolean
  | and (left right : Expr .boolean) : Expr .boolean
  | or (left right : Expr .boolean) : Expr .boolean
  | not (value : Expr .boolean) : Expr .boolean

def Expr.eval (s : Memory) : {sort : RegisterType} → Expr sort → sort.Value
  | _, .rational value => (value : ℝ)
  | _, .natural value => value
  | _, .boolean value => value
  | _, .readReal address => s.real (address.eval s)
  | _, .readNatural address => s.natural (address.eval s)
  | _, .readBoolean address => s.boolean (address.eval s)
  | _, .cast value => ((value.eval s : ℕ) : ℝ)
  | _, .ceil value => ⌈value.eval s⌉₊
  | _, .floor value => ⌊value.eval s⌋₊
  | _, .natAdd a b => a.eval s + b.eval s
  | _, .natSub a b => a.eval s - b.eval s
  | _, .natMul a b => a.eval s * b.eval s
  | _, .natDiv a b => a.eval s / b.eval s
  | _, .add a b => a.eval s + b.eval s
  | _, .sub a b => a.eval s - b.eval s
  | _, .mul a b => a.eval s * b.eval s
  | _, .div a b => a.eval s / b.eval s
  | _, .neg value => -value.eval s
  | _, .sqrt value => Real.sqrt (value.eval s)
  | _, .log value => Real.log (value.eval s)
  | _, .exp value => Real.exp (value.eval s)
  | _, .select condition yes no => if condition.eval s then yes.eval s else no.eval s
  | _, .le a b => decide (a.eval s ≤ b.eval s)
  | _, .lt a b => decide (a.eval s < b.eval s)
  | _, .eq a b => decide (a.eval s = b.eval s)
  | _, .natLe a b => decide (a.eval s ≤ b.eval s)
  | _, .natLt a b => decide (a.eval s < b.eval s)
  | _, .natEq a b => decide (a.eval s = b.eval s)
  | _, .and a b => a.eval s && b.eval s
  | _, .or a b => a.eval s || b.eval s
  | _, .not value => !(value.eval s)

def Expr.operations : {sort : RegisterType} → Expr sort → ℕ
  | _, .rational _ | _, .natural _ | _, .boolean _ => 1
  | _, .readReal e | _, .readNatural e | _, .readBoolean e => e.operations + 1
  | _, .cast e | _, .ceil e | _, .floor e => e.operations + 1
  | _, .neg e | _, .sqrt e | _, .log e | _, .exp e | _, .not e => e.operations + 1
  | _, .natAdd a b | _, .natSub a b | _, .natMul a b | _, .natDiv a b => a.operations + b.operations + 1
  | _, .add a b | _, .sub a b | _, .mul a b | _, .div a b => a.operations + b.operations + 1
  | _, .le a b | _, .lt a b | _, .eq a b => a.operations + b.operations + 1
  | _, .natLe a b | _, .natLt a b | _, .natEq a b => a.operations + b.operations + 1
  | _, .and a b | _, .or a b => a.operations + b.operations + 1
  | _, .select c a b => c.operations + a.operations + b.operations + 1

theorem Expr.operations_pos {sort : RegisterType} (e : Expr sort) : 0 < e.operations := by
  cases e <;> simp only [operations] <;> omega

structure Tapes where
  normal : ℕ → ℝ
  laplace : ℕ → ℝ

structure State where
  memory : Memory
  normalIndex : ℕ := 0
  laplaceIndex : ℕ := 0
  operations : ℕ := 0

def State.tick (s : State) (operations : ℕ) : State :=
  { s with operations := s.operations + operations }

inductive Code where
  | skip
  | real (address : Expr .natural) (value : Expr .real)
  | natural (address value : Expr .natural)
  | boolean (address : Expr .natural) (value : Expr .boolean)
  | normal (address : Expr .natural)
  | laplace (address : Expr .natural)
  | seq (first next : Code)
  | branch (condition : Expr .boolean) (yes no : Code)
  | loop (count : Expr .natural) (indexRegister : ℕ) (body : Code)

def Code.execute (tapes : Tapes) : Code → State → State
  | .skip, s => s
  | .real address value, s =>
      { s with
        memory := s.memory.writeReal (address.eval s.memory) (value.eval s.memory)
        operations := s.operations + address.operations + value.operations + 1 }
  | .natural address value, s =>
      { s with
        memory := s.memory.writeNatural (address.eval s.memory) (value.eval s.memory)
        operations := s.operations + address.operations + value.operations + 1 }
  | .boolean address value, s =>
      { s with
        memory := s.memory.writeBoolean (address.eval s.memory) (value.eval s.memory)
        operations := s.operations + address.operations + value.operations + 1 }
  | .normal address, s =>
      { s with
        memory := s.memory.writeReal (address.eval s.memory) (tapes.normal s.normalIndex)
        normalIndex := s.normalIndex + 1
        operations := s.operations + address.operations + 3 }
  | .laplace address, s =>
      { s with
        memory := s.memory.writeReal (address.eval s.memory) (tapes.laplace s.laplaceIndex)
        laplaceIndex := s.laplaceIndex + 1
        operations := s.operations + address.operations + 3 }
  | .seq first next, s => next.execute tapes (first.execute tapes s)
  | .branch condition yes no, s =>
      let next := s.tick (condition.operations + 1)
      if condition.eval s.memory then yes.execute tapes next else no.execute tapes next
  | .loop count indexRegister body, s =>
      (List.range (count.eval s.memory)).foldl
        (fun old index => body.execute tapes
          { old with
            memory := old.memory.writeNatural indexRegister index
            operations := old.operations + 2 })
        (s.tick (count.operations + 1))

theorem Code.operations_mono (tapes : Tapes) (code : Code) (s : State) :
    s.operations ≤ (code.execute tapes s).operations := by
  induction code generalizing s with
  | skip => rfl
  | real address value => simp [execute] <;> omega
  | natural address value => simp [execute] <;> omega
  | boolean address value => simp [execute] <;> omega
  | normal address => simp [execute] <;> omega
  | laplace address => simp [execute] <;> omega
  | seq first next ih₁ ih₂ =>
      change s.operations ≤ (next.execute tapes (first.execute tapes s)).operations
      exact (ih₁ s).trans (ih₂ (first.execute tapes s))
  | branch condition yes no ih₁ ih₂ =>
      simp only [execute]
      split
      · exact (Nat.le_add_right s.operations (condition.operations + 1)).trans
          (ih₁ (s.tick (condition.operations + 1)))
      · exact (Nat.le_add_right s.operations (condition.operations + 1)).trans
          (ih₂ (s.tick (condition.operations + 1)))
  | loop count indexRegister body ih =>
      have hfold (indices : List ℕ) (initial : State) :
          initial.operations ≤
            (indices.foldl (fun old index => body.execute tapes
              { old with
                memory := old.memory.writeNatural indexRegister index
                operations := old.operations + 2 }) initial).operations := by
        induction indices generalizing initial with
        | nil => rfl
        | cons index indices h =>
            have hstep : initial.operations ≤
                (body.execute tapes { initial with
                  memory := initial.memory.writeNatural indexRegister index
                  operations := initial.operations + 2 }).operations :=
              (Nat.le_add_right initial.operations 2).trans (ih { initial with
                memory := initial.memory.writeNatural indexRegister index
                operations := initial.operations + 2 })
            exact hstep.trans (h _)
      change s.operations ≤
        ((List.range (count.eval s.memory)).foldl
          (fun old index => body.execute tapes { old with
            memory := old.memory.writeNatural indexRegister index
            operations := old.operations + 2 }) (s.tick (count.operations + 1))).operations
      exact (Nat.le_add_right s.operations (count.operations + 1)).trans
        (hfold (List.range (count.eval s.memory)) (s.tick (count.operations + 1)))

def Code.cost (code : Code) (tapes : Tapes) (memory : Memory) : ℕ :=
  (code.execute tapes ⟨memory, 0, 0, 0⟩).operations

theorem Code.real_cost (tapes : Tapes) (memory : Memory)
    (address : Expr .natural) (value : Expr .real) :
    (Code.real address value).cost tapes memory = address.operations + value.operations + 1 := by
  simp [cost, execute]

theorem Code.normal_cost (tapes : Tapes) (memory : Memory) (address : Expr .natural) :
    (Code.normal address).cost tapes memory = address.operations + 3 := by
  simp [cost, execute]

def writeReal (address : ℕ) (value : Expr .real) : Code := .real (.natural address) value
def readReal (address : ℕ) : Expr .real := .readReal (.natural address)
def readNatural (address : ℕ) : Expr .natural := .readNatural (.natural address)
def readBoolean (address : ℕ) : Expr .boolean := .readBoolean (.natural address)

theorem writeReal_value (tapes : Tapes) (s : State) (address : ℕ) (value : Expr .real) :
    ((writeReal address value).execute tapes s).memory.real address = value.eval s.memory := by
  simp [writeReal, Code.execute, Expr.eval, Memory.writeReal]

theorem writeReal_frame (tapes : Tapes) (s : State) (address other : ℕ)
    (value : Expr .real) (h : other ≠ address) :
    ((writeReal address value).execute tapes s).memory.real other = s.memory.real other := by
  simp [writeReal, Code.execute, Expr.eval, Memory.writeReal, h]

end DPCut.RealMachine
