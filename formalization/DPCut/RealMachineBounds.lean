import DPCut.RealMachine

/-! Derived execution bounds and a non-vacuity property of the machine. -/
set_option autoImplicit false
noncomputable section

namespace DPCut.RealMachine

def Steps (code : Code) (bound : ℕ) : Prop :=
  ∀ tapes s, (code.execute tapes s).operations ≤ s.operations + bound

theorem Steps.skip : Steps .skip 0 := by intro tapes s; rfl

theorem Steps.real (address : Expr .natural) (value : Expr .real) :
    Steps (.real address value) (address.operations + value.operations + 1) := by
  intro tapes s
  simp only [Code.execute]
  omega

theorem Steps.natural (address value : Expr .natural) :
    Steps (.natural address value) (address.operations + value.operations + 1) := by
  intro tapes s
  simp only [Code.execute]
  omega

theorem Steps.boolean (address : Expr .natural) (value : Expr .boolean) :
    Steps (.boolean address value) (address.operations + value.operations + 1) := by
  intro tapes s
  simp only [Code.execute]
  omega

theorem Steps.normal (address : Expr .natural) : Steps (.normal address) (address.operations + 3) := by
  intro tapes s
  simp only [Code.execute]
  omega

theorem Steps.laplace (address : Expr .natural) : Steps (.laplace address) (address.operations + 3) := by
  intro tapes s
  simp only [Code.execute]
  omega

theorem Steps.mono {code : Code} {a b : ℕ} (h : Steps code a) (hab : a ≤ b) : Steps code b := by
  intro tapes s
  exact (h tapes s).trans (Nat.add_le_add_left hab _)

theorem Steps.seq {first next : Code} {a b : ℕ} (hfirst : Steps first a) (hnext : Steps next b) :
    Steps (.seq first next) (a + b) := by
  intro tapes s
  have h := hnext tapes (first.execute tapes s)
  have hf := hfirst tapes s
  change (next.execute tapes (first.execute tapes s)).operations ≤ _
  omega

theorem Steps.branch (condition : Expr .boolean) {yes no : Code} {a b : ℕ}
    (hyes : Steps yes a) (hno : Steps no b) :
    Steps (.branch condition yes no) (condition.operations + 1 + max a b) := by
  intro tapes s
  simp only [Code.execute]
  split
  · have h := hyes tapes (s.tick (condition.operations + 1))
    change (yes.execute tapes (s.tick (condition.operations + 1))).operations ≤
      s.operations + (condition.operations + 1) + a at h
    omega
  · have h := hno tapes (s.tick (condition.operations + 1))
    change (no.execute tapes (s.tick (condition.operations + 1))).operations ≤
      s.operations + (condition.operations + 1) + b at h
    omega

theorem loop_execution_bound (count : Expr .natural) (index : ℕ) {body : Code} {c : ℕ}
    (hbody : Steps body c) (tapes : Tapes) (s : State) :
    ((Code.loop count index body).execute tapes s).operations ≤
      s.operations + count.operations + 1 + count.eval s.memory * (c + 2) := by
  have hfold (indices : List ℕ) (initial : State) :
      (indices.foldl (fun old i => body.execute tapes
        { old with
          memory := old.memory.writeNatural index i
          operations := old.operations + 2 }) initial).operations ≤
        initial.operations + indices.length * (c + 2) := by
    induction indices generalizing initial with
    | nil => simp
    | cons i indices ih =>
        let next := body.execute tapes { initial with
          memory := initial.memory.writeNatural index i
          operations := initial.operations + 2 }
        have hs : next.operations ≤ initial.operations + 2 + c := hbody tapes _
        have ht := ih next
        simp only [List.foldl_cons, List.length_cons]
        dsimp only [next] at ht hs
        nlinarith
  simpa only [Code.execute, State.tick, List.length_range] using
    hfold (List.range (count.eval s.memory)) (s.tick (count.operations + 1))

theorem Steps.loop (iterations index : ℕ) {body : Code} {c : ℕ} (hbody : Steps body c) :
    Steps (.loop (.natural iterations) index body) (2 + iterations * (c + 2)) := by
  intro tapes s
  have h := loop_execution_bound (.natural iterations) index hbody tapes s
  simp only [Expr.operations, Expr.eval] at h
  omega

/-- No computation is free: an execution spending no operations cannot change
even one register or tape index. -/
theorem Code.unchanged_of_no_operations (code : Code) (tapes : Tapes) (s : State)
    (h : (code.execute tapes s).operations = s.operations) : code.execute tapes s = s := by
  induction code generalizing s with
  | skip => rfl
  | real address value => simp only [Code.execute] at h; have hp := address.operations_pos; omega
  | natural address value => simp only [Code.execute] at h; have hp := address.operations_pos; omega
  | boolean address value => simp only [Code.execute] at h; have hp := address.operations_pos; omega
  | normal address => simp only [Code.execute] at h; have hp := address.operations_pos; omega
  | laplace address => simp only [Code.execute] at h; have hp := address.operations_pos; omega
  | seq first next ih₁ ih₂ =>
      have hm := first.operations_mono tapes s
      have hn := next.operations_mono tapes (first.execute tapes s)
      change (next.execute tapes (first.execute tapes s)).operations = s.operations at h
      have hf : (first.execute tapes s).operations = s.operations := by omega
      have he := ih₁ s hf
      change next.execute tapes (first.execute tapes s) = s
      rw [he] at h ⊢
      exact ih₂ s h
  | branch condition yes no ih₁ ih₂ =>
      simp only [Code.execute] at h ⊢
      split at h
      · have hm := yes.operations_mono tapes (s.tick (condition.operations + 1))
        change s.operations + (condition.operations + 1) ≤
          (yes.execute tapes (s.tick (condition.operations + 1))).operations at hm
        omega
      · have hm := no.operations_mono tapes (s.tick (condition.operations + 1))
        change s.operations + (condition.operations + 1) ≤
          (no.execute tapes (s.tick (condition.operations + 1))).operations at hm
        omega
  | loop count index body ih =>
      have hprefix : (s.tick (count.operations + 1)).operations ≤
          ((Code.loop count index body).execute tapes s).operations := by
        have hm (indices : List ℕ) (initial : State) :
            initial.operations ≤
              (indices.foldl (fun old i => body.execute tapes
                { old with
                  memory := old.memory.writeNatural index i
                  operations := old.operations + 2 }) initial).operations := by
          induction indices generalizing initial with
          | nil => rfl
          | cons i indices ih =>
              have hs := body.operations_mono tapes
                { initial with
                  memory := initial.memory.writeNatural index i
                  operations := initial.operations + 2 }
              have ht := ih (body.execute tapes
                { initial with
                  memory := initial.memory.writeNatural index i
                  operations := initial.operations + 2 })
              simpa only [List.foldl_cons] using
                (show initial.operations ≤ initial.operations + 2 by omega).trans (hs.trans ht)
        exact hm _ _
      change s.operations + (count.operations + 1) ≤
        ((Code.loop count index body).execute tapes s).operations at hprefix
      omega

end DPCut.RealMachine
