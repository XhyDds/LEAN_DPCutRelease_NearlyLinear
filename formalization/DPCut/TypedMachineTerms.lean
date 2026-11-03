import Mathlib

/-! A typed, immutable-register layer for the release controller. There is no
constructor for an arbitrary semantic function or an entered operation price. -/
set_option autoImplicit false
noncomputable section

namespace DPCut.TypedMachine

inductive ValueType where
  | real
  | natural
  | boolean
  | unit
  | pair (left right : ValueType)
  | array (length : ℕ) (element : ValueType)

abbrev ValueType.Value : ValueType → Type
  | .real => ℝ
  | .natural => ℕ
  | .boolean => Bool
  | .unit => Unit
  | .pair a b => a.Value × b.Value
  | .array n a => Fin n → a.Value

def ValueType.zero : (a : ValueType) → a.Value
  | .real => 0
  | .natural => 0
  | .boolean => false
  | .unit => ()
  | .pair a b => (a.zero,b.zero)
  | .array _ a => fun _ => a.zero

abbrev Environment : List ValueType → Type
  | [] => Unit
  | a :: Γ => a.Value × Environment Γ

inductive Local : List ValueType → ValueType → Type where
  | head {Γ a} : Local (a :: Γ) a
  | tail {Γ a b} (old : Local Γ a) : Local (b :: Γ) a

def Local.read : {Γ : List ValueType} → {a : ValueType} → Local Γ a → Environment Γ → a.Value
  | _, _, .head, s => s.1
  | _, _, .tail old, s => old.read s.2

def Local.operations : {Γ : List ValueType} → {a : ValueType} → Local Γ a → ℕ
  | _, _, .head => 1
  | _, _, .tail old => old.operations+1

inductive RealBinary where
  | add | sub | mul | div | min | max

def RealBinary.eval : RealBinary → ℝ → ℝ → ℝ
  | .add, a, b => a+b
  | .sub, a, b => a-b
  | .mul, a, b => a*b
  | .div, a, b => a/b
  | .min, a, b => Min.min a b
  | .max, a, b => Max.max a b

def RealBinary.operations : RealBinary → ℕ
  | .min | .max => 2
  | _ => 1

inductive RealUnary where
  | neg | abs | sqrt | log | exp

def RealUnary.eval : RealUnary → ℝ → ℝ
  | .neg, a => -a
  | .abs, a => |a|
  | .sqrt, a => Real.sqrt a
  | .log, a => Real.log a
  | .exp, a => Real.exp a

def RealUnary.operations : RealUnary → ℕ
  | .abs => 2
  | _ => 1

inductive NaturalBinary where
  | add | sub | mul | div

def NaturalBinary.eval : NaturalBinary → ℕ → ℕ → ℕ
  | .add, a, b => a+b
  | .sub, a, b => a-b
  | .mul, a, b => a*b
  | .div, a, b => a/b

inductive Comparison where
  | le | lt | eq

def Comparison.real : Comparison → ℝ → ℝ → Bool
  | .le, a, b => decide (a ≤ b)
  | .lt, a, b => decide (a < b)
  | .eq, a, b => decide (a = b)

def Comparison.natural : Comparison → ℕ → ℕ → Bool
  | .le, a, b => decide (a ≤ b)
  | .lt, a, b => decide (a < b)
  | .eq, a, b => decide (a = b)

inductive Term (Γ : List ValueType) : ValueType → Type where
  | rational (q : ℚ) : Term Γ .real
  | natural (n : ℕ) : Term Γ .natural
  | boolean (b : Bool) : Term Γ .boolean
  | unit : Term Γ .unit
  | read {a} (v : Local Γ a) : Term Γ a
  | pair {a b} (left : Term Γ a) (right : Term Γ b) : Term Γ (.pair a b)
  | fst {a b} (value : Term Γ (.pair a b)) : Term Γ a
  | snd {a b} (value : Term Γ (.pair a b)) : Term Γ b
  | array {n a} (items : Fin n → Term Γ a) : Term Γ (.array n a)
  | get {n a} (items : Term Γ (.array n a)) (index : Term Γ .natural) : Term Γ a
  | realBinary (op : RealBinary) (left right : Term Γ .real) : Term Γ .real
  | realUnary (op : RealUnary) (value : Term Γ .real) : Term Γ .real
  | naturalBinary (op : NaturalBinary) (left right : Term Γ .natural) : Term Γ .natural
  | cast (value : Term Γ .natural) : Term Γ .real
  | ceil (value : Term Γ .real) : Term Γ .natural
  | floor (value : Term Γ .real) : Term Γ .natural
  | realCompare (op : Comparison) (left right : Term Γ .real) : Term Γ .boolean
  | naturalCompare (op : Comparison) (left right : Term Γ .natural) : Term Γ .boolean
  | and (left right : Term Γ .boolean) : Term Γ .boolean
  | or (left right : Term Γ .boolean) : Term Γ .boolean
  | not (value : Term Γ .boolean) : Term Γ .boolean
  | select {a} (condition : Term Γ .boolean) (yes no : Term Γ a) : Term Γ a
  | sum {n} (values : Term Γ (.array n .real)) : Term Γ .real
  | maximum {n} (values : Term Γ (.array n .real)) : Term Γ .real

def Term.eval {Γ : List ValueType} (s : Environment Γ) : {a : ValueType} → Term Γ a → a.Value
  | _, .rational q => (q:ℝ)
  | _, .natural n => n
  | _, .boolean b => b
  | _, .unit => ()
  | _, .read v => v.read s
  | _, .pair a b => (a.eval s,b.eval s)
  | _, .fst p => (p.eval s).1
  | _, .snd p => (p.eval s).2
  | _, .array items => fun i => (items i).eval s
  | _, .get (n := n) (a := a) items index =>
      if h : index.eval s < n then items.eval s ⟨index.eval s,h⟩ else a.zero
  | _, .realBinary op a b => op.eval (a.eval s) (b.eval s)
  | _, .realUnary op a => op.eval (a.eval s)
  | _, .naturalBinary op a b => op.eval (a.eval s) (b.eval s)
  | _, .cast a => ((a.eval s:ℕ):ℝ)
  | _, .ceil a => ⌈a.eval s⌉₊
  | _, .floor a => ⌊a.eval s⌋₊
  | _, .realCompare op a b => op.real (a.eval s) (b.eval s)
  | _, .naturalCompare op a b => op.natural (a.eval s) (b.eval s)
  | _, .and a b => a.eval s && b.eval s
  | _, .or a b => a.eval s || b.eval s
  | _, .not a => !(a.eval s)
  | _, .select c a b => if c.eval s then a.eval s else b.eval s
  | _, .sum a => ∑ i, a.eval s i
  | _, .maximum a => (List.finRange _).foldl (fun old i => max old (a.eval s i)) 0

def Term.operations {Γ : List ValueType} : {a : ValueType} → Term Γ a → ℕ
  | _, .rational _ | _, .natural _ | _, .boolean _ | _, .unit => 1
  | _, .read v => v.operations
  | _, .pair a b => a.operations+b.operations+1
  | _, .fst a | _, .snd a => a.operations+1
  | _, .array (n := n) items => (∑ i, (items i).operations)+n+1
  | _, .get items index => items.operations+index.operations+2
  | _, .realBinary op a b => a.operations+b.operations+op.operations
  | _, .realUnary op a => a.operations+op.operations
  | _, .naturalBinary _ a b => a.operations+b.operations+1
  | _, .cast a | _, .ceil a | _, .floor a => a.operations+1
  | _, .realCompare _ a b | _, .naturalCompare _ a b | _, .and a b | _, .or a b =>
      a.operations+b.operations+1
  | _, .not a => a.operations+1
  | _, .select c a b => c.operations+a.operations+b.operations+1
  | _, .sum (n := n) a => a.operations+n+1
  | _, .maximum (n := n) a => a.operations+2*n+1

instance {Γ : List ValueType} : Add (Term Γ .real) := ⟨.realBinary .add⟩
instance {Γ : List ValueType} : Sub (Term Γ .real) := ⟨.realBinary .sub⟩
instance {Γ : List ValueType} : Mul (Term Γ .real) := ⟨.realBinary .mul⟩
instance {Γ : List ValueType} : Div (Term Γ .real) := ⟨.realBinary .div⟩
instance {Γ : List ValueType} : Neg (Term Γ .real) := ⟨.realUnary .neg⟩
instance {Γ : List ValueType} (n : ℕ) : OfNat (Term Γ .real) n := ⟨.rational n⟩

def Term.at {Γ : List ValueType} {n : ℕ} {a : ValueType}
    (values : Term Γ (.array n a)) (i : Fin n) : Term Γ a := .get values (.natural i.val)

@[simp] theorem Term.eval_at {Γ : List ValueType} {n : ℕ} {a : ValueType}
    (values : Term Γ (.array n a)) (i : Fin n) (s : Environment Γ) :
    (values.at i).eval s = values.eval s i := by
  simp [Term.at, Term.eval, i.isLt]

def Term.weaken {Γ : List ValueType} {a b : ValueType} : Term Γ a → Term (b :: Γ) a
  | .rational q => .rational q
  | .natural n => .natural n
  | .boolean b => .boolean b
  | .unit => .unit
  | .read v => .read (.tail v)
  | .pair a b => .pair a.weaken b.weaken
  | .fst a => .fst a.weaken
  | .snd a => .snd a.weaken
  | .array items => .array (fun i => (items i).weaken)
  | .get items index => .get items.weaken index.weaken
  | .realBinary op a b => .realBinary op a.weaken b.weaken
  | .realUnary op a => .realUnary op a.weaken
  | .naturalBinary op a b => .naturalBinary op a.weaken b.weaken
  | .cast a => .cast a.weaken
  | .ceil a => .ceil a.weaken
  | .floor a => .floor a.weaken
  | .realCompare op a b => .realCompare op a.weaken b.weaken
  | .naturalCompare op a b => .naturalCompare op a.weaken b.weaken
  | .and a b => .and a.weaken b.weaken
  | .or a b => .or a.weaken b.weaken
  | .not a => .not a.weaken
  | .select c a b => .select c.weaken a.weaken b.weaken
  | .sum a => .sum a.weaken
  | .maximum a => .maximum a.weaken

end DPCut.TypedMachine
