import DPCut.RealMachineFrames

set_option autoImplicit false
noncomputable section

namespace DPCut.RealMachine

def sumLoop {n : ℕ} (values : Fin n → Expr .real) (output : ℕ) : List (Fin n) → Code
  | [] => .skip
  | i :: indices =>
      .seq (writeReal output (.add (readReal output) (values i))) (sumLoop values output indices)

def sumProgram {n : ℕ} (values : Fin n → Expr .real) (output : ℕ) : Code :=
  .seq (writeReal output (.rational 0)) (sumLoop values output (List.finRange n))

theorem sumLoop_steps {n : ℕ} (values : Fin n → Expr .real) (output c : ℕ)
    (h : ∀ i, (values i).operations ≤ c) (indices : List (Fin n)) :
    Steps (sumLoop values output indices) (indices.length * (c + 5)) := by
  induction indices with
  | nil => simpa only [sumLoop, List.length_nil, Nat.zero_mul] using Steps.skip
  | cons i indices ih =>
      have hw := (Steps.real (.natural output) (.add (readReal output) (values i))).mono
        (show _ ≤ c + 5 by simp only [Expr.operations, readReal]; have hi := h i; omega)
      simpa only [sumLoop, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using hw.seq ih

theorem sumProgram_steps {n : ℕ} (values : Fin n → Expr .real) (output c : ℕ)
    (h : ∀ i, (values i).operations ≤ c) : Steps (sumProgram values output) (3 + n * (c + 5)) := by
  simpa only [sumProgram, writeReal, Expr.operations, List.length_finRange] using
    (Steps.real (.natural output) (.rational 0)).seq (sumLoop_steps values output c h (List.finRange n))

theorem sumLoop_frame {n : ℕ} (tapes : Tapes) (s : State) (values : Fin n → Expr .real)
    (output address : ℕ) (indices : List (Fin n)) (h : address ≠ output) :
    ((sumLoop values output indices).execute tapes s).memory.real address = s.memory.real address := by
  induction indices generalizing s with
  | nil => rfl
  | cons i indices ih =>
      change ((sumLoop values output indices).execute tapes
        ((writeReal output (.add (readReal output) (values i))).execute tapes s)).memory.real address = _
      rw [ih]
      exact writeReal_frame _ _ _ _ _ h

theorem sumProgram_frame {n : ℕ} (tapes : Tapes) (s : State) (values : Fin n → Expr .real)
    (output address : ℕ) (h : address ≠ output) :
    ((sumProgram values output).execute tapes s).memory.real address = s.memory.real address := by
  change ((sumLoop values output (List.finRange n)).execute tapes
    ((writeReal output (.rational 0)).execute tapes s)).memory.real address = _
  rw [sumLoop_frame _ _ _ _ _ _ h]
  exact writeReal_frame _ _ _ _ _ h

theorem sumLoop_realOnly {n : ℕ} (values : Fin n → Expr .real) (output : ℕ) (indices : List (Fin n)) :
    (sumLoop values output indices).RealOnly := by
  induction indices with
  | nil => trivial
  | cons i indices ih => exact ⟨trivial, ih⟩

theorem sumProgram_realOnly {n : ℕ} (values : Fin n → Expr .real) (output : ℕ) :
    (sumProgram values output).RealOnly := ⟨trivial, sumLoop_realOnly _ _ _⟩

theorem sumLoop_value {n : ℕ} (tapes : Tapes) (s : State) (values : Fin n → Expr .real)
    (output : ℕ) (indices : List (Fin n)) (hframe : ∀ i, (values i).RealFrame output) :
    ((sumLoop values output indices).execute tapes s).memory.real output =
      s.memory.real output + (indices.map (fun i => (values i).eval s.memory)).sum := by
  induction indices generalizing s with
  | nil => simp [sumLoop, Code.execute]
  | cons i indices ih =>
      let next := (writeReal output (.add (readReal output) (values i))).execute tapes s
      have hv : next.memory.real output = s.memory.real output + (values i).eval s.memory :=
        writeReal_value tapes s output _
      have he (j : Fin n) : (values j).eval next.memory = (values j).eval s.memory :=
        hframe j s.memory _
      change ((sumLoop values output indices).execute tapes next).memory.real output = _
      rw [ih, hv]
      simp only [he, List.map_cons, List.sum_cons]
      ring

theorem sumProgram_value {n : ℕ} (tapes : Tapes) (s : State) (values : Fin n → Expr .real)
    (output : ℕ) (hframe : ∀ i, (values i).RealFrame output) :
    ((sumProgram values output).execute tapes s).memory.real output = ∑ i, (values i).eval s.memory := by
  let initial := (writeReal output (.rational 0)).execute tapes s
  have hzero : initial.memory.real output = 0 := by
    rw [writeReal_value]
    norm_num [Expr.eval]
  have he (i : Fin n) : (values i).eval initial.memory = (values i).eval s.memory :=
    hframe i s.memory _
  change ((sumLoop values output (List.finRange n)).execute tapes initial).memory.real output = _
  rw [sumLoop_value _ _ _ _ _ hframe]
  simp only [hzero, he, zero_add, ← List.ofFn_eq_map, List.sum_ofFn]

end DPCut.RealMachine
