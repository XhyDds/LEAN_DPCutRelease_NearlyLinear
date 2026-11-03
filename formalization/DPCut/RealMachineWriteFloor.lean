import DPCut.RealMachineSDPFields

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace DPCut.RealMachine

def Code.RealWriteFloor (floor : ℕ) : Code → Prop
  | .skip | .natural .. | .boolean .. => True
  | .real address _ | .normal address | .laplace address => ∀ memory, floor ≤ address.eval memory
  | .seq first next => first.RealWriteFloor floor ∧ next.RealWriteFloor floor
  | .branch _ yes no => yes.RealWriteFloor floor ∧ no.RealWriteFloor floor
  | .loop _ _ body => body.RealWriteFloor floor

theorem Code.realWriteFloor_frame (code : Code) (floor : ℕ) (h : code.RealWriteFloor floor)
    (tapes : Tapes) (s : State) (address : ℕ) (ha : address < floor) :
    (code.execute tapes s).memory.real address = s.memory.real address := by
  induction code generalizing s with
  | skip | natural | boolean => rfl
  | real destination value =>
      have hd : address ≠ destination.eval s.memory := (ha.trans_le (h s.memory)).ne
      simp [Code.execute, Memory.writeReal, hd]
  | normal destination =>
      have hd : address ≠ destination.eval s.memory := (ha.trans_le (h s.memory)).ne
      simp [Code.execute, Memory.writeReal, hd]
  | laplace destination =>
      have hd : address ≠ destination.eval s.memory := (ha.trans_le (h s.memory)).ne
      simp [Code.execute, Memory.writeReal, hd]
  | seq first next ih₁ ih₂ =>
      change (next.execute tapes (first.execute tapes s)).memory.real address = _
      rw [ih₂ h.2, ih₁ h.1]
  | branch condition yes no ih₁ ih₂ =>
      simp only [Code.execute]
      split
      · exact ih₁ h.1 _
      · exact ih₂ h.2 _
  | loop count index body ih =>
      have hf (indices : List ℕ) (initial : State) :
          (indices.foldl (fun old i => body.execute tapes
            { old with
              memory := old.memory.writeNatural index i
              operations := old.operations + 2 }) initial).memory.real address = initial.memory.real address := by
        induction indices generalizing initial with
        | nil => rfl
        | cons i indices ih' => rw [List.foldl_cons, ih']; exact ih h _
      exact hf _ _

theorem floor_writeReal (floor address : ℕ) (value : Expr .real) (h : floor ≤ address) :
    (writeReal address value).RealWriteFloor floor := fun _ => h

theorem floor_array {n : ℕ} (floor : ℕ) (addresses : Fin n → ℕ) (values : Fin n → Expr .real)
    (h : ∀ i, floor ≤ addresses i) : (arrayProgram addresses values).RealWriteFloor floor := by
  have hf (indices : List (Fin n)) : (arrayLoop addresses values indices).RealWriteFloor floor := by
    induction indices with
    | nil => trivial
    | cons i indices ih => exact ⟨floor_writeReal _ _ _ (h i), ih⟩
  exact hf _

theorem floor_matrixMap (floor n output : ℕ) (values : Fin n × Fin n → Expr .real)
    (h : floor ≤ output) : (matrixMapProgram n output values).RealWriteFloor floor := by
  exact floor_array _ _ _ (fun i => h.trans (by unfold matrixAddress; omega))

theorem floor_sum {n : ℕ} (floor output : ℕ) (values : Fin n → Expr .real) (h : floor ≤ output) :
    (sumProgram values output).RealWriteFloor floor := by
  have hf (indices : List (Fin n)) : (sumLoop values output indices).RealWriteFloor floor := by
    induction indices with
    | nil => trivial
    | cons i indices ih => exact ⟨floor_writeReal _ _ _ h, ih⟩
  exact ⟨floor_writeReal _ _ _ h, hf _⟩

theorem floor_dot {n : ℕ} (floor output : ℕ) (left right : Fin n → ℕ) (h : floor ≤ output) :
    (dotProgram left right output).RealWriteFloor floor := by
  have hf (indices : List (Fin n)) : (dotLoop left right output indices).RealWriteFloor floor := by
    induction indices with
    | nil => trivial
    | cons i indices ih => exact ⟨floor_writeReal _ _ _ h, ih⟩
  exact ⟨floor_writeReal _ _ _ h, hf _⟩

theorem floor_matrixSum (floor n d output : ℕ) (values : Fin n × Fin n → Fin d → Expr .real)
    (h : floor ≤ output) : (matrixSumProgram n d output values).RealWriteFloor floor := by
  have hf (entries : List (Fin n × Fin n)) : (matrixSumLoop n d output values entries).RealWriteFloor floor := by
    induction entries with
    | nil => trivial
    | cons ij entries ih => exact ⟨floor_sum _ _ _ (h.trans (by unfold matrixAddress; omega)), ih⟩
  exact hf _

theorem floor_control (code : Code) (h : code.ControlOnly) (floor : ℕ) : code.RealWriteFloor floor := by
  induction code with
  | skip | natural | boolean => trivial
  | real | normal | laplace => cases h
  | seq first next ih₁ ih₂ | branch condition first next ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | loop count index body ih => exact ih h

theorem floor_solve (floor n input rhs output scratch : ℕ) (ho : floor ≤ output) (hs : floor ≤ scratch) :
    (solveProgram n input rhs output scratch).RealWriteFloor floor := by
  induction n generalizing input rhs output scratch with
  | zero => trivial
  | succ n ih =>
      exact ⟨floor_matrixMap _ _ _ _ hs,
        floor_array _ _ _ (fun i => by unfold vectorAddress; omega),
        ih _ _ _ _ (by omega) (by omega),
        floor_dot _ _ _ _ hs,
        floor_array _ _ _ (fun i => by unfold vectorAddress; omega)⟩

theorem floor_inverse (floor n input output scratch : ℕ) (ho : floor ≤ output) (hs : floor ≤ scratch) :
    (inverseProgram n input output scratch).RealWriteFloor floor := by
  have hc (j : Fin n) : (inverseColumn n input output scratch j).RealWriteFloor floor :=
    ⟨floor_array _ _ _ (fun i => by unfold vectorAddress; omega),
      floor_solve _ _ _ _ _ _ (by omega) (by omega),
      floor_array _ _ _ (fun i => by unfold matrixAddress; omega)⟩
  have hf (columns : List (Fin n)) : (inverseLoop n input output scratch columns).RealWriteFloor floor := by
    induction columns with
    | nil => trivial
    | cons j columns ih => exact ⟨hc j, ih⟩
  exact hf _

theorem floor_determinant (floor n input output scratch : ℕ) (ho : floor ≤ output) (hs : floor ≤ scratch) :
    (determinantProgram n input output scratch).RealWriteFloor floor := by
  induction n generalizing input scratch with
  | zero => exact floor_writeReal _ _ _ ho
  | succ n ih =>
      exact ⟨floor_matrixMap _ _ _ _ hs, ih _ _ (by omega), floor_writeReal _ _ _ ho⟩

theorem floor_psd (floor n input output flag scratch : ℕ) (ho : floor ≤ output) (hs : floor ≤ scratch) :
    (psdProgram n input output flag scratch).RealWriteFloor floor := by
  induction n generalizing input output scratch with
  | zero => trivial
  | succ n ih =>
      exact ⟨⟨trivial, floor_array _ _ _ (fun i => by unfold vectorAddress; omega)⟩,
        floor_control _ (firstNonzero_control _ _ _) _,
        ⟨floor_writeReal _ _ _ (by omega), trivial, floor_array _ _ _ (fun i => by unfold vectorAddress; omega)⟩,
        ⟨floor_matrixMap _ _ _ _ (by omega), floor_matrixMap _ _ _ _ (by omega)⟩,
        ih _ _ _ (by omega) (by omega),
        ⟨⟨⟨floor_writeReal _ _ _ (by omega),
          floor_dot _ _ _ _ (by omega), floor_writeReal _ _ _ (by omega)⟩,
          floor_array _ _ _ (fun i => by unfold vectorAddress; omega)⟩, trivial⟩⟩

end DPCut.RealMachine
