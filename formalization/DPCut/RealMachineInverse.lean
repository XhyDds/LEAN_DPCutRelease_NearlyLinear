import DPCut.RealMachineSolve

/-! Matrix inversion is implemented by the proved register linear solves,
not by a unit-cost inverse instruction. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace DPCut.RealMachine

def inverseColumn (n input output scratch : ℕ) (j : Fin n) : Code :=
  .seq (arrayProgram (fun i : Fin n => vectorAddress scratch i)
      (fun i => .rational (if i = j then 1 else 0)))
    (.seq (solveProgram n input scratch (scratch + n) (scratch + 2 * n))
      (arrayProgram (fun i : Fin n => matrixAddress output (i, j))
        (fun i => readReal (vectorAddress (scratch + n) i))))

def inverseLoop (n input output scratch : ℕ) : List (Fin n) → Code
  | [] => .skip
  | j :: columns => .seq (inverseColumn n input output scratch j) (inverseLoop n input output scratch columns)

def inverseProgram (n input output scratch : ℕ) : Code :=
  inverseLoop n input output scratch (List.finRange n)

theorem inverseColumn_steps (n input output scratch : ℕ) (j : Fin n) :
    Steps (inverseColumn n input output scratch j) (107 * (n + 1) ^ 3) := by
  have hb := arrayProgram_steps (fun i : Fin n => vectorAddress scratch i)
    (fun i => Expr.rational (if i = j then 1 else 0)) 1 (by intro i; rfl)
  have hs := solveProgram_steps n input scratch (scratch + n) (scratch + 2 * n)
  have ho := arrayProgram_steps (fun i : Fin n => matrixAddress output (i, j))
    (fun i => readReal (vectorAddress (scratch + n) i)) 2 (by intro i; rfl)
  have hp : n ≤ (n + 1) ^ 3 := (Nat.le_succ n).trans (Nat.le_self_pow (by decide : 3 ≠ 0) (n + 1))
  exact (hb.seq (hs.seq ho)).mono (by nlinarith)

theorem inverseLoop_steps (n input output scratch : ℕ) (columns : List (Fin n)) :
    Steps (inverseLoop n input output scratch columns) (columns.length * (107 * (n + 1) ^ 3)) := by
  induction columns with
  | nil => simpa only [inverseLoop, List.length_nil, Nat.zero_mul] using Steps.skip
  | cons j columns ih =>
      have h := (inverseColumn_steps n input output scratch j).seq ih
      simpa only [inverseLoop, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using h

theorem inverseProgram_steps (n input output scratch : ℕ) :
    Steps (inverseProgram n input output scratch) (107 * (n + 1) ^ 4) := by
  have h := inverseLoop_steps n input output scratch (List.finRange n)
  simp only [List.length_finRange] at h
  simpa only [inverseProgram, List.length_finRange] using h.mono (by
    exact (Nat.mul_le_mul_right (107 * (n + 1) ^ 3) (Nat.le_succ n)).trans_eq (by
      simp only [Nat.succ_eq_add_one]
      ring))

theorem inverseColumn_below (tapes : Tapes) (s : State) (n input output scratch address : ℕ) (j : Fin n)
    (hout : address < output) (hscratch : address < scratch) :
    ((inverseColumn n input output scratch j).execute tapes s).memory.real address = s.memory.real address := by
  simp only [inverseColumn, Code.execute]
  unfold arrayProgram
  rw [arrayLoop_frame _ _ _ _ _ _ (by
    intro i _
    unfold matrixAddress
    omega)]
  rw [solveProgram_below _ _ _ _ _ _ _ _ (by omega) (by omega)]
  exact arrayLoop_frame _ _ _ _ _ _ (by intro i _; unfold vectorAddress; omega)

theorem inverseLoop_below (tapes : Tapes) (s : State) (n input output scratch address : ℕ)
    (columns : List (Fin n)) (hout : address < output) (hscratch : address < scratch) :
    ((inverseLoop n input output scratch columns).execute tapes s).memory.real address = s.memory.real address := by
  induction columns generalizing s with
  | nil => rfl
  | cons j columns ih =>
      change ((inverseLoop n input output scratch columns).execute tapes
        ((inverseColumn n input output scratch j).execute tapes s)).memory.real address = _
      rw [ih]
      exact inverseColumn_below _ _ _ _ _ _ _ _ hout hscratch

theorem inverseColumn_other (tapes : Tapes) (s : State) (n input output scratch : ℕ)
    (j : Fin n) (address : ℕ) (ha : address < scratch)
    (h : ∀ i : Fin n, address ≠ matrixAddress output (i, j)) :
    ((inverseColumn n input output scratch j).execute tapes s).memory.real address = s.memory.real address := by
  simp only [inverseColumn, Code.execute]
  unfold arrayProgram
  rw [arrayLoop_frame _ _ _ _ _ _ (by intro i _; exact h i)]
  rw [solveProgram_below _ _ _ _ _ _ _ _ (by omega) (by omega)]
  exact arrayLoop_frame _ _ _ _ _ _ (by intro i _; unfold vectorAddress; omega)

theorem inverseColumn_value (tapes : Tapes) (s : State) (n input output scratch : ℕ) (j : Fin n)
    (hM : ∀ ij : Fin n × Fin n, matrixAddress input ij < scratch)
    (ho : ∀ ij : Fin n × Fin n, matrixAddress output ij < scratch) :
    ∀ i : Fin n, ((inverseColumn n input output scratch j).execute tapes s).memory.real (matrixAddress output (i, j)) =
      MatrixElimination.solve (readMatrix n input s.memory) (Pi.single j 1) i := by
  let first := (arrayProgram (fun i : Fin n => vectorAddress scratch i)
    (fun i => Expr.rational (if i = j then 1 else 0))).execute tapes s
  let second := (solveProgram n input scratch (scratch + n) (scratch + 2 * n)).execute tapes first
  have hmatrix : readMatrix n input first.memory = readMatrix n input s.memory := by
    funext a b
    unfold first arrayProgram
    apply arrayLoop_frame
    intro i _
    have h := hM (a, b)
    unfold vectorAddress
    omega
  have hrhs : readVector n scratch first.memory = (Pi.single j 1 : Fin n → ℝ) := by
    funext i
    have h := arrayProgram_value tapes s (fun i : Fin n => vectorAddress scratch i)
      (fun i => Expr.rational (if i = j then 1 else 0)) (vectorAddress_injective scratch)
      (by intro a b; exact realFrame_rational _ _) i
    by_cases he : i = j <;> simpa [readVector, first, Expr.eval, Pi.single_apply, he] using h
  have hsolve : readVector n (scratch + n) second.memory =
      MatrixElimination.solve (readMatrix n input s.memory) (Pi.single j 1) := by
    have h := solveProgram_value tapes first n input scratch (scratch + n) (scratch + 2 * n) (by
      intro ij
      have h := hM ij
      omega) (by intro i; unfold vectorAddress; have h := i.isLt; omega)
      (by intro i; unfold vectorAddress; have h := i.isLt; omega)
      (by intro ij i; have h := hM ij; unfold vectorAddress; omega)
      (by intro i k; unfold vectorAddress; have h := i.isLt; omega)
    rw [hmatrix, hrhs] at h
    exact h
  intro i
  have hi : Function.Injective (fun a : Fin n => matrixAddress output (a, j)) := by
    intro a b h
    exact (Prod.mk.inj (matrixAddress_injective output h)).1
  have hf : ∀ a b : Fin n, (readReal (vectorAddress (scratch + n) a)).RealFrame (matrixAddress output (b, j)) := by
    intro a b
    apply realFrame_read
    have h := ho (b, j)
    unfold vectorAddress
    omega
  have hv := arrayProgram_value tapes second (fun a : Fin n => matrixAddress output (a, j))
    (fun a => readReal (vectorAddress (scratch + n) a)) hi hf i
  change ((arrayProgram (fun a : Fin n => matrixAddress output (a, j))
    (fun a => readReal (vectorAddress (scratch + n) a))).execute tapes second).memory.real (matrixAddress output (i, j)) = _
  rw [hv]
  exact congrFun hsolve i

theorem inverseLoop_other (tapes : Tapes) (s : State) (n input output scratch address : ℕ)
    (columns : List (Fin n)) (ha : address < scratch)
    (h : ∀ j ∈ columns, ∀ i : Fin n, address ≠ matrixAddress output (i, j)) :
    ((inverseLoop n input output scratch columns).execute tapes s).memory.real address = s.memory.real address := by
  induction columns generalizing s with
  | nil => rfl
  | cons j columns ih =>
      change ((inverseLoop n input output scratch columns).execute tapes
        ((inverseColumn n input output scratch j).execute tapes s)).memory.real address = _
      rw [ih _ (by intro j hj; exact h j (List.mem_cons_of_mem _ hj))]
      exact inverseColumn_other tapes s n input output scratch j address ha (h j (by simp))

theorem inverseLoop_value (tapes : Tapes) (s : State) (n input output scratch : ℕ)
    (columns : List (Fin n)) (hnodup : columns.Nodup)
    (hM : ∀ ij : Fin n × Fin n, matrixAddress input ij < scratch)
    (ho : ∀ ij : Fin n × Fin n, matrixAddress output ij < scratch)
    (hdisjoint : ∀ ij kl : Fin n × Fin n, matrixAddress input ij ≠ matrixAddress output kl) :
    ∀ j ∈ columns, ∀ i : Fin n, ((inverseLoop n input output scratch columns).execute tapes s).memory.real
      (matrixAddress output (i, j)) = MatrixElimination.solve (readMatrix n input s.memory) (Pi.single j 1) i := by
  induction columns generalizing s with
  | nil => simp
  | cons head columns ih =>
      have hn := List.nodup_cons.mp hnodup
      let next := (inverseColumn n input output scratch head).execute tapes s
      have hm : readMatrix n input next.memory = readMatrix n input s.memory := by
        funext a b
        exact inverseColumn_other tapes s n input output scratch head (matrixAddress input (a, b))
          (hM (a, b)) (fun i => hdisjoint (a, b) (i, head))
      intro j hj i
      rcases List.mem_cons.mp hj with rfl | hj
      · change ((inverseLoop n input output scratch columns).execute tapes next).memory.real (matrixAddress output (i, j)) = _
        rw [inverseLoop_other tapes next n input output scratch (matrixAddress output (i, j)) columns (ho (i, j)) (by
          intro k hk a he
          have hsame := (Prod.mk.inj (matrixAddress_injective output he)).2
          exact hn.1 (hsame.symm ▸ hk))]
        exact inverseColumn_value tapes s n input output scratch j hM ho i
      · have h := ih next hn.2 j hj i
        rw [hm] at h
        exact h

theorem inverseProgram_value (tapes : Tapes) (s : State) (n input output scratch : ℕ)
    (hM : ∀ ij : Fin n × Fin n, matrixAddress input ij < scratch)
    (ho : ∀ ij : Fin n × Fin n, matrixAddress output ij < scratch)
    (hdisjoint : ∀ ij kl : Fin n × Fin n, matrixAddress input ij ≠ matrixAddress output kl) :
    readMatrix n output ((inverseProgram n input output scratch).execute tapes s).memory =
      MatrixElimination.inverse (readMatrix n input s.memory) := by
  funext i j
  exact inverseLoop_value _ _ _ _ _ _ _ (List.nodup_finRange n) hM ho hdisjoint j (List.mem_finRange j) i

end DPCut.RealMachine
