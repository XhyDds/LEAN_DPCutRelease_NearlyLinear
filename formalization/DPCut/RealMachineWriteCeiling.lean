import DPCut.RealMachineEllipsoidStep

set_option autoImplicit false
noncomputable section

namespace DPCut.RealMachine

def Code.RealWriteCeiling (ceiling : ℕ) : Code → Prop
  | .skip | .natural .. | .boolean .. => True
  | .real address _ | .normal address | .laplace address => ∀ memory, address.eval memory < ceiling
  | .seq first next => first.RealWriteCeiling ceiling ∧ next.RealWriteCeiling ceiling
  | .branch _ yes no => yes.RealWriteCeiling ceiling ∧ no.RealWriteCeiling ceiling
  | .loop _ _ body => body.RealWriteCeiling ceiling

theorem Code.realWriteCeiling_frame (code : Code) (ceiling : ℕ) (h : code.RealWriteCeiling ceiling)
    (tapes : Tapes) (s : State) (address : ℕ) (ha : ceiling ≤ address) :
    (code.execute tapes s).memory.real address = s.memory.real address := by
  induction code generalizing s with
  | skip | natural | boolean => rfl
  | real destination value =>
      have hd : address ≠ destination.eval s.memory := (lt_of_lt_of_le (h s.memory) ha).ne'
      simp [Code.execute, Memory.writeReal, hd]
  | normal destination =>
      have hd : address ≠ destination.eval s.memory := (lt_of_lt_of_le (h s.memory) ha).ne'
      simp [Code.execute, Memory.writeReal, hd]
  | laplace destination =>
      have hd : address ≠ destination.eval s.memory := (lt_of_lt_of_le (h s.memory) ha).ne'
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

theorem ceiling_writeReal (ceiling address : ℕ) (value : Expr .real) (h : address < ceiling) :
    (writeReal address value).RealWriteCeiling ceiling := fun _ => h

theorem ceiling_array {n : ℕ} (ceiling : ℕ) (addresses : Fin n → ℕ) (values : Fin n → Expr .real)
    (h : ∀ i, addresses i < ceiling) : (arrayProgram addresses values).RealWriteCeiling ceiling := by
  have hf (indices : List (Fin n)) : (arrayLoop addresses values indices).RealWriteCeiling ceiling := by
    induction indices with
    | nil => trivial
    | cons i indices ih => exact ⟨ceiling_writeReal _ _ _ (h i), ih⟩
  exact hf _

theorem ceiling_matrixMap (ceiling n output : ℕ) (values : Fin n × Fin n → Expr .real)
    (h : ∀ ij : Fin n × Fin n, matrixAddress output ij < ceiling) :
    (matrixMapProgram n output values).RealWriteCeiling ceiling :=
  ceiling_array _ _ _ (fun i => h _)

theorem ceiling_dot {n : ℕ} (ceiling output : ℕ) (left right : Fin n → ℕ) (h : output < ceiling) :
    (dotProgram left right output).RealWriteCeiling ceiling := by
  have hf (indices : List (Fin n)) : (dotLoop left right output indices).RealWriteCeiling ceiling := by
    induction indices with
    | nil => trivial
    | cons i indices ih => exact ⟨ceiling_writeReal _ _ _ h, ih⟩
  exact ⟨ceiling_writeReal _ _ _ h, hf _⟩

theorem ceiling_matVec {n : ℕ} (ceiling : ℕ) (matrix : Fin n → Fin n → ℕ) (vector output : Fin n → ℕ)
    (h : ∀ i, output i < ceiling) : (matVecProgram matrix vector output).RealWriteCeiling ceiling := by
  have hf (indices : List (Fin n)) : (matVecLoop matrix vector output indices).RealWriteCeiling ceiling := by
    induction indices with
    | nil => trivial
    | cons i indices ih => exact ⟨ceiling_dot _ _ _ _ (h i), ih⟩
  exact hf _

theorem ceiling_mul (ceiling n left right output : ℕ)
    (h : ∀ ij : Fin n × Fin n, matrixAddress output ij < ceiling) :
    (mulProgram n left right output).RealWriteCeiling ceiling := by
  have hf (entries : List (Fin n × Fin n)) : (mulLoop left right output entries).RealWriteCeiling ceiling := by
    induction entries with
    | nil => trivial
    | cons ij entries ih =>
        rcases ij with ⟨i,j⟩
        exact ⟨ceiling_dot _ _ _ _ (h (i,j)), ih⟩
  exact hf _

namespace EllipsoidCode

open SDP

theorem cutProgram_ceiling (m base : ℕ) : (cutProgram m base).RealWriteCeiling (slot m base 12) := by
  have hv (k : ℕ) (hk : k < 12) (i : Fin m) := vector_before_slot m base k 12 hk i
  have hm (k : ℕ) (hk : k < 12) (ij : Fin m × Fin m) := matrix_before_slot m base k 12 hk ij
  have hs (k : ℕ) (hk : k < 12) := slot_lt_slot m base k 12 hk
  exact ⟨ceiling_matVec _ _ _ _ (hv _ (by decide)), ceiling_dot _ _ _ _ (hs _ (by decide)),
    ceiling_writeReal _ _ _ (hs _ (by decide)), ceiling_array _ _ _ (hv _ (by decide)), ceiling_matVec _ _ _ _ (hv _ (by decide)),
    ceiling_writeReal _ _ _ (hs _ (by decide)), ceiling_writeReal _ _ _ (hs _ (by decide)),
    ceiling_matrixMap _ _ _ _ (hm _ (by decide)), ceiling_mul _ _ _ _ _ (hm _ (by decide)),
    ceiling_array _ _ _ (hv _ (by decide)), ceiling_matrixMap _ _ _ _ (hm _ (by decide)), ceiling_array _ _ _ (hv _ (by decide))⟩

theorem cutProgram_realOnly (m base : ℕ) : (cutProgram m base).RealOnly := by
  have hmv (matrix : Fin m → Fin m → ℕ) (vector output : Fin m → ℕ) :
      (matVecProgram matrix vector output).RealOnly := by
    have hf (indices : List (Fin m)) : (matVecLoop matrix vector output indices).RealOnly := by
      induction indices with
      | nil => trivial
      | cons i indices ih => exact ⟨dotProgram_realOnly _ _ _, ih⟩
    exact hf _
  have hmul (left right output : ℕ) : (mulProgram m left right output).RealOnly := by
    have hf (entries : List (Fin m × Fin m)) : (mulLoop left right output entries).RealOnly := by
      induction entries with
      | nil => trivial
      | cons ij entries ih => exact ⟨dotProgram_realOnly _ _ _, ih⟩
    exact hf _
  exact ⟨hmv _ _ _, dotProgram_realOnly _ _ _, trivial, arrayProgram_realOnly _ _, hmv _ _ _,
    trivial, trivial, matrixMap_realOnly _ _ _, hmul _ _ _, arrayProgram_realOnly _ _,
    matrixMap_realOnly _ _ _, arrayProgram_realOnly _ _⟩

end EllipsoidCode

end DPCut.RealMachine
