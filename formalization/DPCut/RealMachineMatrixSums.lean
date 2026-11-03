import DPCut.RealMachineSums

set_option autoImplicit false
noncomputable section

namespace DPCut.RealMachine

def matrixSumLoop (n d output : ℕ) (values : Fin n × Fin n → Fin d → Expr .real) :
    List (Fin n × Fin n) → Code
  | [] => .skip
  | ij :: entries => .seq (sumProgram (values ij) (matrixAddress output ij))
      (matrixSumLoop n d output values entries)

def matrixSumProgram (n d output : ℕ) (values : Fin n × Fin n → Fin d → Expr .real) : Code :=
  matrixSumLoop n d output values (matrixIndices n)

theorem matrixSumLoop_steps (n d output c : ℕ) (values : Fin n × Fin n → Fin d → Expr .real)
    (h : ∀ ij i, (values ij i).operations ≤ c) (entries : List (Fin n × Fin n)) :
    Steps (matrixSumLoop n d output values entries) (entries.length * (3 + d * (c + 5))) := by
  induction entries with
  | nil => simpa only [matrixSumLoop, List.length_nil, Nat.zero_mul] using Steps.skip
  | cons ij entries ih =>
      simpa only [matrixSumLoop, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using
        (sumProgram_steps (values ij) (matrixAddress output ij) c (h ij)).seq ih

theorem matrixSumProgram_steps (n d output c : ℕ) (values : Fin n × Fin n → Fin d → Expr .real)
    (h : ∀ ij i, (values ij i).operations ≤ c) :
    Steps (matrixSumProgram n d output values) (n * n * (3 + d * (c + 5))) := by
  simpa only [matrixSumProgram, matrixIndices, List.length_map, List.length_finRange] using
    matrixSumLoop_steps n d output c values h (matrixIndices n)

theorem matrixSumLoop_frame (tapes : Tapes) (s : State) (n d output address : ℕ)
    (values : Fin n × Fin n → Fin d → Expr .real) (entries : List (Fin n × Fin n))
    (h : ∀ ij ∈ entries, address ≠ matrixAddress output ij) :
    ((matrixSumLoop n d output values entries).execute tapes s).memory.real address = s.memory.real address := by
  induction entries generalizing s with
  | nil => rfl
  | cons ij entries ih =>
      change ((matrixSumLoop n d output values entries).execute tapes
        ((sumProgram (values ij) (matrixAddress output ij)).execute tapes s)).memory.real address = _
      rw [ih _ (fun kl hk => h kl (List.mem_cons_of_mem _ hk))]
      exact sumProgram_frame _ _ _ _ _ (h ij (by simp))

theorem matrixSumLoop_value (tapes : Tapes) (s : State) (n d output : ℕ)
    (values : Fin n × Fin n → Fin d → Expr .real) (entries : List (Fin n × Fin n))
    (hnodup : entries.Nodup)
    (hframe : ∀ ij : Fin n × Fin n, ∀ i : Fin d, ∀ kl : Fin n × Fin n,
      (values ij i).RealFrame (matrixAddress output kl)) :
    ∀ ij ∈ entries, ((matrixSumLoop n d output values entries).execute tapes s).memory.real (matrixAddress output ij) =
      ∑ i, (values ij i).eval s.memory := by
  induction entries generalizing s with
  | nil => simp
  | cons head entries ih =>
      have hn := List.nodup_cons.mp hnodup
      let next := (sumProgram (values head) (matrixAddress output head)).execute tapes s
      have hvals (ij : Fin n × Fin n) (i : Fin d) : (values ij i).eval next.memory = (values ij i).eval s.memory := by
        have hf (indices : List (Fin d)) (old : State) :
            (values ij i).eval ((sumLoop (values head) (matrixAddress output head) indices).execute tapes old).memory =
              (values ij i).eval old.memory := by
          induction indices generalizing old with
          | nil => rfl
          | cons j indices ih =>
              change (values ij i).eval ((sumLoop (values head) (matrixAddress output head) indices).execute tapes
                ((writeReal (matrixAddress output head) (.add (readReal (matrixAddress output head)) (values head j))).execute tapes old)).memory = _
              rw [ih]
              exact hframe ij i head old.memory _
        exact (hf _ _).trans (by
          simpa only [writeReal, Code.execute, Expr.eval, Rat.cast_zero] using hframe ij i head s.memory 0)
      intro ij hi
      rcases List.mem_cons.mp hi with rfl | hi
      · change ((matrixSumLoop n d output values entries).execute tapes next).memory.real (matrixAddress output ij) = _
        rw [matrixSumLoop_frame _ _ _ _ _ _ _ _ (by
          intro kl hk he
          exact hn.1 ((matrixAddress_injective output he).symm ▸ hk))]
        exact sumProgram_value _ _ _ _ (fun i => hframe ij i ij)
      · have h := ih next hn.2 ij hi
        simpa only [hvals] using h

theorem matrixSumProgram_value (tapes : Tapes) (s : State) (n d output : ℕ)
    (values : Fin n × Fin n → Fin d → Expr .real)
    (hframe : ∀ ij : Fin n × Fin n, ∀ i : Fin d, ∀ kl : Fin n × Fin n,
      (values ij i).RealFrame (matrixAddress output kl)) :
    readMatrix n output ((matrixSumProgram n d output values).execute tapes s).memory =
      (fun a b => ∑ i, (values (a, b) i).eval s.memory) := by
  have hn : (matrixIndices n).Nodup := (List.nodup_finRange _).map
    (fun i j h => finProdFinEquiv.symm.injective h)
  funext a b
  apply matrixSumLoop_value _ _ _ _ _ _ _ hn hframe (a, b)
  exact List.mem_map.mpr ⟨finProdFinEquiv (a, b), List.mem_finRange _, finProdFinEquiv.symm_apply_apply _⟩

theorem matrixSumProgram_frame (tapes : Tapes) (s : State) (n d output address : ℕ)
    (values : Fin n × Fin n → Fin d → Expr .real)
    (h : ∀ ij : Fin n × Fin n, address ≠ matrixAddress output ij) :
    ((matrixSumProgram n d output values).execute tapes s).memory.real address = s.memory.real address :=
  matrixSumLoop_frame _ _ _ _ _ _ _ _ (fun ij _ => h ij)

end DPCut.RealMachine
