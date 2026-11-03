import DPCut.RealMachineBounds

/-! Actual scalar-instruction programs for vector inner products. -/
set_option autoImplicit false
noncomputable section

namespace DPCut.RealMachine

variable {n : ℕ}

def dotLoop (left right : Fin n → ℕ) (output : ℕ) : List (Fin n) → Code
  | [] => .skip
  | i :: rest => .seq
      (writeReal output (.add (readReal output) (.mul (readReal (left i)) (readReal (right i)))))
      (dotLoop left right output rest)

def dotProgram (left right : Fin n → ℕ) (output : ℕ) : Code :=
  .seq (writeReal output (.rational 0)) (dotLoop left right output (List.finRange n))

theorem dotLoop_steps (left right : Fin n → ℕ) (output : ℕ) (indices : List (Fin n)) :
    Steps (dotLoop left right output indices) (10 * indices.length) := by
  induction indices with
  | nil => exact Steps.skip
  | cons i indices ih =>
      have hw : Steps (writeReal output (.add (readReal output)
          (.mul (readReal (left i)) (readReal (right i))))) 10 :=
        Steps.real _ _
      have h := hw.seq ih
      simpa only [dotLoop, List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_comm] using h

theorem dotProgram_steps (left right : Fin n → ℕ) (output : ℕ) :
    Steps (dotProgram left right output) (3 + 10 * n) := by
  have h := (Steps.real (.natural output) (.rational 0)).seq
    (dotLoop_steps left right output (List.finRange n))
  simpa only [dotProgram, writeReal, Expr.operations, List.length_finRange] using h

theorem dotLoop_frame (tapes : Tapes) (s : State) (left right : Fin n → ℕ)
    (output other : ℕ) (indices : List (Fin n)) (h : other ≠ output) :
    ((dotLoop left right output indices).execute tapes s).memory.real other = s.memory.real other := by
  induction indices generalizing s with
  | nil => rfl
  | cons i indices ih =>
      change ((dotLoop left right output indices).execute tapes
        ((writeReal output (.add (readReal output) (.mul (readReal (left i)) (readReal (right i))))).execute tapes s)).memory.real other = _
      rw [ih]
      exact writeReal_frame _ _ _ _ _ h

theorem dotLoop_value (tapes : Tapes) (s : State) (left right : Fin n → ℕ)
    (output : ℕ) (indices : List (Fin n))
    (hleft : ∀ i, left i ≠ output) (hright : ∀ i, right i ≠ output) :
    ((dotLoop left right output indices).execute tapes s).memory.real output =
      s.memory.real output + (indices.map (fun i => s.memory.real (left i) * s.memory.real (right i))).sum := by
  induction indices generalizing s with
  | nil => simp [dotLoop, Code.execute]
  | cons i indices ih =>
      let next := (writeReal output (.add (readReal output)
        (.mul (readReal (left i)) (readReal (right i))))).execute tapes s
      have ha (j : Fin n) : next.memory.real (left j) = s.memory.real (left j) :=
        writeReal_frame _ _ _ _ _ (hleft j)
      have hb (j : Fin n) : next.memory.real (right j) = s.memory.real (right j) :=
        writeReal_frame _ _ _ _ _ (hright j)
      have hnext : next.memory.real output = s.memory.real output +
          s.memory.real (left i) * s.memory.real (right i) := by
        rw [writeReal_value]
        rfl
      change ((dotLoop left right output indices).execute tapes next).memory.real output = _
      rw [ih, hnext]
      simp only [ha, hb, List.map_cons, List.sum_cons]
      ring

theorem dotProgram_value (tapes : Tapes) (s : State) (left right : Fin n → ℕ)
    (output : ℕ) (hleft : ∀ i, left i ≠ output) (hright : ∀ i, right i ≠ output) :
    ((dotProgram left right output).execute tapes s).memory.real output =
      ∑ i, s.memory.real (left i) * s.memory.real (right i) := by
  let initial := (writeReal output (.rational 0)).execute tapes s
  have hl (i : Fin n) : initial.memory.real (left i) = s.memory.real (left i) :=
    writeReal_frame _ _ _ _ _ (hleft i)
  have hr (i : Fin n) : initial.memory.real (right i) = s.memory.real (right i) :=
    writeReal_frame _ _ _ _ _ (hright i)
  have hzero : initial.memory.real output = 0 := by
    change ((writeReal output (.rational 0)).execute tapes s).memory.real output = 0
    rw [writeReal_value]
    norm_num [Expr.eval]
  change ((dotLoop left right output (List.finRange n)).execute tapes initial).memory.real output = _
  rw [dotLoop_value _ _ _ _ _ _ hleft hright]
  simp only [hzero, hl, hr, zero_add, List.sum_ofFn, ← List.ofFn_eq_map]

theorem dotProgram_frame (tapes : Tapes) (s : State) (left right : Fin n → ℕ)
    (output other : ℕ) (h : other ≠ output) :
    ((dotProgram left right output).execute tapes s).memory.real other = s.memory.real other := by
  change ((dotLoop left right output (List.finRange n)).execute tapes
    ((writeReal output (.rational 0)).execute tapes s)).memory.real other = _
  rw [dotLoop_frame _ _ _ _ _ _ _ h]
  exact writeReal_frame _ _ _ _ _ h

end DPCut.RealMachine
