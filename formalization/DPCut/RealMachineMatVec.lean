import DPCut.RealMachineSDPComplete

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace DPCut.RealMachine

def matVecLoop {n : ℕ} (matrix : Fin n → Fin n → ℕ) (vector output : Fin n → ℕ) : List (Fin n) → Code
  | [] => .skip
  | i :: indices => .seq (dotProgram (matrix i) vector (output i)) (matVecLoop matrix vector output indices)

def matVecProgram {n : ℕ} (matrix : Fin n → Fin n → ℕ) (vector output : Fin n → ℕ) : Code :=
  matVecLoop matrix vector output (List.finRange n)

theorem matVecLoop_steps {n : ℕ} (matrix : Fin n → Fin n → ℕ) (vector output : Fin n → ℕ)
    (indices : List (Fin n)) : Steps (matVecLoop matrix vector output indices) (indices.length * (3 + 10 * n)) := by
  induction indices with
  | nil => simpa only [matVecLoop, List.length_nil, Nat.zero_mul] using Steps.skip
  | cons i indices ih =>
      simpa only [matVecLoop, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using
        (dotProgram_steps (matrix i) vector (output i)).seq ih

theorem matVecProgram_steps {n : ℕ} (matrix : Fin n → Fin n → ℕ) (vector output : Fin n → ℕ) :
    Steps (matVecProgram matrix vector output) (n * (3 + 10 * n)) := by
  simpa only [matVecProgram, List.length_finRange] using matVecLoop_steps matrix vector output (List.finRange n)

theorem matVecLoop_frame {n : ℕ} (tapes : Tapes) (s : State) (matrix : Fin n → Fin n → ℕ)
    (vector output : Fin n → ℕ) (indices : List (Fin n)) (address : ℕ) (h : ∀ i ∈ indices, address ≠ output i) :
    ((matVecLoop matrix vector output indices).execute tapes s).memory.real address = s.memory.real address := by
  induction indices generalizing s with
  | nil => rfl
  | cons i indices ih =>
      change ((matVecLoop matrix vector output indices).execute tapes
        ((dotProgram (matrix i) vector (output i)).execute tapes s)).memory.real address = _
      rw [ih _ (fun j hj => h j (List.mem_cons_of_mem _ hj))]
      exact dotProgram_frame _ _ _ _ _ _ (h i (by simp))

theorem matVecProgram_frame {n : ℕ} (tapes : Tapes) (s : State) (matrix : Fin n → Fin n → ℕ)
    (vector output : Fin n → ℕ) (address : ℕ) (h : ∀ i, address ≠ output i) :
    ((matVecProgram matrix vector output).execute tapes s).memory.real address = s.memory.real address :=
  matVecLoop_frame _ _ _ _ _ _ _ (fun i _ => h i)

theorem matVecLoop_value {n : ℕ} (tapes : Tapes) (s : State) (matrix : Fin n → Fin n → ℕ)
    (vector output : Fin n → ℕ) (indices : List (Fin n)) (hnodup : indices.Nodup)
    (hinj : Function.Injective output) (hM : ∀ i j k, matrix i j ≠ output k)
    (hV : ∀ i j, vector i ≠ output j) :
    ∀ i ∈ indices, ((matVecLoop matrix vector output indices).execute tapes s).memory.real (output i) =
      ∑ j, s.memory.real (matrix i j) * s.memory.real (vector j) := by
  induction indices generalizing s with
  | nil => simp
  | cons head indices ih =>
      have hn := List.nodup_cons.mp hnodup
      let next := (dotProgram (matrix head) vector (output head)).execute tapes s
      have hmatrix (i j : Fin n) : next.memory.real (matrix i j) = s.memory.real (matrix i j) :=
        dotProgram_frame _ _ _ _ _ _ (hM i j head)
      have hvector (i : Fin n) : next.memory.real (vector i) = s.memory.real (vector i) :=
        dotProgram_frame _ _ _ _ _ _ (hV i head)
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · change ((matVecLoop matrix vector output indices).execute tapes next).memory.real (output i) = _
        rw [matVecLoop_frame _ _ _ _ _ _ _ (by intro j hj he; exact hn.1 ((hinj he).symm ▸ hj))]
        exact dotProgram_value _ _ _ _ _ (fun j => hM i j i) (fun j => hV j i)
      · have h := ih next hn.2 i hi
        simpa only [hmatrix, hvector] using h

theorem matVecProgram_value {n : ℕ} (tapes : Tapes) (s : State) (matrix : Fin n → Fin n → ℕ)
    (vector output : Fin n → ℕ) (hinj : Function.Injective output)
    (hM : ∀ i j k, matrix i j ≠ output k) (hV : ∀ i j, vector i ≠ output j) (i : Fin n) :
    ((matVecProgram matrix vector output).execute tapes s).memory.real (output i) =
      ∑ j, s.memory.real (matrix i j) * s.memory.real (vector j) :=
  matVecLoop_value _ _ _ _ _ _ (List.nodup_finRange n) hinj hM hV i (List.mem_finRange i)

theorem floor_matVec {n : ℕ} (floor : ℕ) (matrix : Fin n → Fin n → ℕ) (vector output : Fin n → ℕ)
    (h : ∀ i, floor ≤ output i) : (matVecProgram matrix vector output).RealWriteFloor floor := by
  have hf (indices : List (Fin n)) : (matVecLoop matrix vector output indices).RealWriteFloor floor := by
    induction indices with
    | nil => trivial
    | cons i indices ih => exact ⟨floor_dot _ _ _ _ (h i), ih⟩
  exact hf _

end DPCut.RealMachine
