import DPCut.RealMachineVectors

/-! Dense matrix multiplication lowered to real-register dot-product code. -/
set_option autoImplicit false
noncomputable section

namespace DPCut.RealMachine

variable {n : ℕ}

def matrixAddress (base : ℕ) (index : Fin n × Fin n) : ℕ :=
  base + (finProdFinEquiv index).val

theorem matrixAddress_injective (base : ℕ) : Function.Injective (matrixAddress (n := n) base) := by
  intro i j h
  have he : (finProdFinEquiv i).val = (finProdFinEquiv j).val := by
    unfold matrixAddress at h
    omega
  exact finProdFinEquiv.injective (Fin.ext he)

def readMatrix (n base : ℕ) (memory : Memory) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => memory.real (matrixAddress base (i, j))

def mulLoop (left right output : ℕ) : List (Fin n × Fin n) → Code
  | [] => .skip
  | (i, j) :: rest =>
      .seq (dotProgram (fun k => matrixAddress left (i, k))
        (fun k => matrixAddress right (k, j)) (matrixAddress output (i, j)))
        (mulLoop left right output rest)

def matrixIndices (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange (n * n)).map finProdFinEquiv.symm

def mulProgram (n left right output : ℕ) : Code :=
  mulLoop (n := n) left right output (matrixIndices n)

theorem mulLoop_steps (left right output : ℕ) (indices : List (Fin n × Fin n)) :
    Steps (mulLoop left right output indices) (indices.length * (3 + 10 * n)) := by
  induction indices with
  | nil => simpa only [mulLoop, List.length_nil, Nat.zero_mul] using Steps.skip
  | cons index indices ih =>
      rcases index with ⟨i, j⟩
      have h := (dotProgram_steps (fun k => matrixAddress left (i, k))
        (fun k => matrixAddress right (k, j)) (matrixAddress output (i, j))).seq ih
      simpa only [mulLoop, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using h

theorem mulProgram_steps (n left right output : ℕ) :
    Steps (mulProgram n left right output) (n * n * (3 + 10 * n)) := by
  simpa only [mulProgram, matrixIndices, List.length_map, List.length_finRange] using
    mulLoop_steps (n := n) left right output (matrixIndices n)

theorem mulLoop_frame (tapes : Tapes) (s : State) (left right output address : ℕ)
    (indices : List (Fin n × Fin n))
    (h : ∀ index ∈ indices, address ≠ matrixAddress output index) :
    ((mulLoop left right output indices).execute tapes s).memory.real address = s.memory.real address := by
  induction indices generalizing s with
  | nil => rfl
  | cons index indices ih =>
      rcases index with ⟨i, j⟩
      change ((mulLoop left right output indices).execute tapes
        ((dotProgram (fun k => matrixAddress left (i, k)) (fun k => matrixAddress right (k, j))
          (matrixAddress output (i, j))).execute tapes s)).memory.real address = _
      rw [ih _ (by intro index hi; exact h index (List.mem_cons_of_mem _ hi))]
      exact dotProgram_frame _ _ _ _ _ _ (h (i, j) (by simp))

theorem mulLoop_value (tapes : Tapes) (s : State) (left right output : ℕ)
    (indices : List (Fin n × Fin n)) (hnodup : indices.Nodup)
    (hleft : ∀ i j : Fin n × Fin n, matrixAddress left i ≠ matrixAddress output j)
    (hright : ∀ i j : Fin n × Fin n, matrixAddress right i ≠ matrixAddress output j) :
    ∀ index ∈ indices,
      ((mulLoop left right output indices).execute tapes s).memory.real (matrixAddress output index) =
        (readMatrix n left s.memory * readMatrix n right s.memory) index.1 index.2 := by
  induction indices generalizing s with
  | nil => simp
  | cons head indices ih =>
      rcases head with ⟨i, j⟩
      have hn := List.nodup_cons.mp hnodup
      let next := (dotProgram (fun k => matrixAddress left (i, k)) (fun k => matrixAddress right (k, j))
        (matrixAddress output (i, j))).execute tapes s
      have hL : readMatrix n left next.memory = readMatrix n left s.memory := by
        funext a b
        exact dotProgram_frame _ _ _ _ _ _ (hleft (a, b) (i, j))
      have hR : readMatrix n right next.memory = readMatrix n right s.memory := by
        funext a b
        exact dotProgram_frame _ _ _ _ _ _ (hright (a, b) (i, j))
      intro index hindex
      rcases List.mem_cons.mp hindex with rfl | hindex
      · change ((mulLoop left right output indices).execute tapes next).memory.real (matrixAddress output (i, j)) = _
        rw [mulLoop_frame _ _ _ _ _ _ _ (by
          intro other ho he
          have hsame := matrixAddress_injective output he
          exact hn.1 (hsame.symm ▸ ho))]
        exact dotProgram_value tapes s _ _ _ (fun k => hleft (i, k) (i, j))
          (fun k => hright (k, j) (i, j))
      · have h := ih next hn.2 index hindex
        rw [hL, hR] at h
        exact h

theorem mulProgram_value (tapes : Tapes) (s : State) (n left right output : ℕ)
    (hleft : ∀ i j : Fin n × Fin n, matrixAddress left i ≠ matrixAddress output j)
    (hright : ∀ i j : Fin n × Fin n, matrixAddress right i ≠ matrixAddress output j) :
    readMatrix n output ((mulProgram n left right output).execute tapes s).memory =
      readMatrix n left s.memory * readMatrix n right s.memory := by
  have hn : (matrixIndices n).Nodup :=
    (List.nodup_finRange _).map (fun a b h => finProdFinEquiv.symm.injective h)
  funext i j
  apply mulLoop_value tapes s _ _ _ _ hn hleft hright (i, j)
  apply List.mem_map.mpr
  exact ⟨finProdFinEquiv (i, j), List.mem_finRange _, finProdFinEquiv.symm_apply_apply _⟩

end DPCut.RealMachine
