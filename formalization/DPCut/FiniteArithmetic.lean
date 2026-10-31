import DPCut.ScalarArithmetic

/-! Bounded loops over finite public index sets. Reindexing is structural;
each scalar sum step and vector store is counted. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DPCut.Arithmetic

def sumFin : {n : ℕ} → (Fin n → Arithmetic ℝ) → Arithmetic ℝ
  | 0, _ => Arithmetic.pure 0
  | _+1, f => do
    let a ← f 0
    let b ← sumFin (fun i => f i.succ)
    add a b

@[simp] lemma sumFin_value {n : ℕ} (f : Fin n → Arithmetic ℝ) :
    (sumFin f).value = ∑ i, (f i).value := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih => simp [sumFin, add, ih, Fin.sum_univ_succ]

lemma sumFin_steps {n : ℕ} (f : Fin n → Arithmetic ℝ) :
    (sumFin f).steps = ∑ i, ((f i).steps+1) := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih => simp [sumFin, add, ih, Fin.sum_univ_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def sum {ι : Type} [Fintype ι] (f : ι → Arithmetic ℝ) : Arithmetic ℝ :=
  sumFin (fun i => f ((Fintype.equivFin ι).symm i))

@[simp] lemma sum_value {ι : Type} [Fintype ι] (f : ι → Arithmetic ℝ) :
    (sum f).value = ∑ i, (f i).value := by
  rw [sum, sumFin_value]
  exact (Fintype.equivFin ι).symm.sum_comp (fun i => (f i).value)

lemma sum_steps {ι : Type} [Fintype ι] (f : ι → Arithmetic ℝ) :
    (sum f).steps = ∑ i, ((f i).steps+1) := by
  rw [sum, sumFin_steps]
  exact (Fintype.equivFin ι).symm.sum_comp (fun i => (f i).steps+1)

lemma sum_steps_le {ι : Type} [Fintype ι] {c : ℕ} (f : ι → Arithmetic ℝ)
    (hf : ∀ i, (f i).steps ≤ c) : (sum f).steps ≤ Fintype.card ι*(c+1) := by
  rw [sum_steps]
  calc
    _ ≤ ∑ _ : ι, (c+1) := Finset.sum_le_sum (fun i _ => Nat.add_le_add_right (hf i) 1)
    _ = _ := by simp

def abs (a : ℝ) : Arithmetic ℝ := do
  let n ← lt a 0
  if n then neg a else Arithmetic.pure a

@[simp] lemma abs_value (a : ℝ) : (abs a).value = |a| := by
  by_cases h : a<0
  · simp [abs, lt, neg, h, abs_of_neg h]
  · simp [abs, lt, h, abs_of_nonneg (le_of_not_gt h)]

lemma abs_steps (a : ℝ) : (abs a).steps ≤ 2 := by
  by_cases h : a<0 <;> simp [abs, lt, neg, h]

end DPCut.Arithmetic
