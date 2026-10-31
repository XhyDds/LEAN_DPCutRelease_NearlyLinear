import DPCut.MatrixPSDAlgorithm
import DPCut.MatrixFactorAlgorithm

/-! Deterministic operation-count semantics for scalar real arithmetic.
Indexing, constants and structural rearrangement of data are free. Scalar
operations/comparisons and each stored vector entry cost one operation. The
algorithms below compose these operations, rather than assigning a price to
an arbitrary matrix function. This is real-operation semantics, not bit cost. -/
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators
namespace DPCut

structure Arithmetic (α : Type) where
  value : α
  steps : ℕ

namespace Arithmetic
variable {α β : Type}
def pure (x : α) : Arithmetic α := ⟨x,0⟩
def bind (x : Arithmetic α) (f : α → Arithmetic β) : Arithmetic β :=
  ⟨(f x.value).value, x.steps + (f x.value).steps⟩
instance : Monad Arithmetic where
  pure := pure
  bind := bind

def add (a b : ℝ) : Arithmetic ℝ := ⟨a+b,1⟩
def sub (a b : ℝ) : Arithmetic ℝ := ⟨a-b,1⟩
def mul (a b : ℝ) : Arithmetic ℝ := ⟨a*b,1⟩
def div (a b : ℝ) : Arithmetic ℝ := ⟨a/b,1⟩
def neg (a : ℝ) : Arithmetic ℝ := ⟨-a,1⟩
def sqrt (a : ℝ) : Arithmetic ℝ := ⟨Real.sqrt a,1⟩
def log (a : ℝ) : Arithmetic ℝ := ⟨Real.log a,1⟩
def lt (a b : ℝ) : Arithmetic Bool := ⟨decide (a<b),1⟩
def eq (a b : ℝ) : Arithmetic Bool := ⟨decide (a=b),1⟩
def store (a : α) : Arithmetic α := ⟨a,1⟩

@[simp] lemma pure_value (a : α) : (pure a).value = a := rfl
@[simp] lemma pure_steps (a : α) : (pure a).steps = 0 := rfl
@[simp] lemma bind_value (a : Arithmetic α) (f : α → Arithmetic β) :
    (a.bind f).value = (f a.value).value := rfl
@[simp] lemma bind_steps (a : Arithmetic α) (f : α → Arithmetic β) :
    (a.bind f).steps = a.steps + (f a.value).steps := rfl
@[simp] lemma monad_bind_value (a : Arithmetic α) (f : α → Arithmetic β) :
    (a >>= f).value = (f a.value).value := rfl
@[simp] lemma monad_bind_steps (a : Arithmetic α) (f : α → Arithmetic β) :
    (a >>= f).steps = a.steps + (f a.value).steps := rfl
@[simp] lemma monad_pure_value (a : α) : (Pure.pure a : Arithmetic α).value = a := rfl
@[simp] lemma monad_pure_steps (a : α) : (Pure.pure a : Arithmetic α).steps = 0 := rfl
@[simp] lemma ite_value (p : Prop) [Decidable p] (a b : Arithmetic α) :
    (if p then a else b).value = if p then a.value else b.value := by split <;> rfl
@[simp] lemma ite_steps (p : Prop) [Decidable p] (a b : Arithmetic α) :
    (if p then a else b).steps = if p then a.steps else b.steps := by split <;> rfl

/-- A small reusable refinement lemma keeps large implementations opaque
while their semantic outputs are substituted. -/
lemma bind3_value {γ δ : Type} (p : Arithmetic α) (f : α → Arithmetic β)
    (g : β → Arithmetic γ) (h : α → γ → Arithmetic δ) (a : α) (b : β) (c : γ)
    (hp : p.value = a) (hf : (f a).value = b) (hg : (g b).value = c) :
    (p >>= fun x => f x >>= fun y => g y >>= fun z => h x z).value = (h a c).value := by
  rw [monad_bind_value, hp, monad_bind_value, hf, monad_bind_value, hg]

/-- Materialize a vector, counting both the entry computation and its store. -/
def collect {α : Type} : {n : ℕ} → (Fin n → Arithmetic α) → Arithmetic (Fin n → α)
  | 0, _ => pure Fin.elim0
  | _+1, f => do
    let a ← f 0
    let a ← store a
    let t ← collect (fun i => f i.succ)
    pure (Fin.cons a t)

@[simp] lemma collect_value {n : ℕ} (f : Fin n → Arithmetic α) :
    (collect f).value = fun i => (f i).value := by
  induction n with
  | zero => ext i; exact Fin.elim0 i
  | succ n ih =>
    simp only [collect, bind, Bind.bind, pure, store, ih]
    ext i; exact Fin.cases rfl (fun _ => rfl) i

lemma collect_steps {n : ℕ} (f : Fin n → Arithmetic α) :
    (collect f).steps = ∑ i, ((f i).steps + 1) := by
  induction n with
  | zero => simp [collect]
  | succ n ih => simp [collect, pure, store, ih, Fin.sum_univ_succ, Nat.add_assoc]

lemma collect_steps_le {n c : ℕ} (f : Fin n → Arithmetic α) (hf : ∀ i, (f i).steps ≤ c) :
    (collect f).steps ≤ n*(c+1) := by
  rw [collect_steps]
  calc
    _ ≤ ∑ _ : Fin n, (c+1) := Finset.sum_le_sum (fun i _ => Nat.add_le_add_right (hf i) 1)
    _ = _ := by simp

def dot : {n : ℕ} → (Fin n → ℝ) → (Fin n → ℝ) → Arithmetic ℝ
  | 0, _, _ => pure 0
  | _+1, a, b => do
    let p ← mul (a 0) (b 0)
    let t ← dot (fun i => a i.succ) (fun i => b i.succ)
    add p t

@[simp] lemma dot_value {n : ℕ} (a b : Fin n → ℝ) : (dot a b).value = a ⬝ᵥ b := by
  induction n with
  | zero => simp [dot, dotProduct]
  | succ n ih => simp [dot, mul, add, ih, dotProduct, Fin.sum_univ_succ]

@[simp] lemma dot_steps {n : ℕ} (a b : Fin n → ℝ) : (dot a b).steps = 2*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [dot, mul, add, ih]; omega

end Arithmetic
end DPCut
