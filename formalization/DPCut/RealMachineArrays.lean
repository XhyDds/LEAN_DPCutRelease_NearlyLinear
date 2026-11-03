import DPCut.RealMachineBounds

/-! Register-array maps built only from expression syntax. The frame hypotheses
below describe read/write disjointness; they do not assign a runtime price. -/
set_option autoImplicit false
noncomputable section

namespace DPCut.RealMachine

variable {n : ℕ}

def Expr.RealFrame {kind : RegisterType} (expression : Expr kind) (address : ℕ) : Prop :=
  ∀ memory value, expression.eval (memory.writeReal address value) = expression.eval memory

theorem realFrame_read (address other : ℕ) (h : address ≠ other) :
    (readReal address).RealFrame other := by
  intro memory value
  simp [readReal, Expr.eval, Memory.writeReal, h]

theorem realFrame_rational (value : ℚ) (address : ℕ) :
    (Expr.rational value).RealFrame address := by intro memory v; rfl

theorem realFrame_natural (value address : ℕ) :
    (Expr.natural value).RealFrame address := by intro memory v; rfl

theorem realFrame_binary {kind : RegisterType} (op : Expr .real → Expr .real → Expr kind)
    (semantics : ℝ → ℝ → kind.Value)
    (hsem : ∀ a b memory, (op a b).eval memory = semantics (a.eval memory) (b.eval memory))
    {left right : Expr .real} {address : ℕ} (hl : left.RealFrame address) (hr : right.RealFrame address) :
    (op left right).RealFrame address := by
  intro memory value
  rw [hsem, hsem, hl, hr]

theorem realFrame_add {left right : Expr .real} {address : ℕ}
    (hl : left.RealFrame address) (hr : right.RealFrame address) : (Expr.add left right).RealFrame address :=
  realFrame_binary Expr.add (· + ·) (by intros; rfl) hl hr

theorem realFrame_sub {left right : Expr .real} {address : ℕ}
    (hl : left.RealFrame address) (hr : right.RealFrame address) : (Expr.sub left right).RealFrame address :=
  realFrame_binary Expr.sub (· - ·) (by intros; rfl) hl hr

theorem realFrame_mul {left right : Expr .real} {address : ℕ}
    (hl : left.RealFrame address) (hr : right.RealFrame address) : (Expr.mul left right).RealFrame address :=
  realFrame_binary Expr.mul (· * ·) (by intros; rfl) hl hr

theorem realFrame_div {left right : Expr .real} {address : ℕ}
    (hl : left.RealFrame address) (hr : right.RealFrame address) : (Expr.div left right).RealFrame address :=
  realFrame_binary Expr.div (· / ·) (by intros; rfl) hl hr

theorem realFrame_sqrt {value : Expr .real} {address : ℕ}
    (h : value.RealFrame address) : (Expr.sqrt value).RealFrame address := by
  intro memory v
  simp only [Expr.eval]
  rw [h]

theorem realFrame_readNatural (address other : ℕ) : (readNatural address).RealFrame other := by
  intro memory value
  rfl

theorem realFrame_natEq {left right : Expr .natural} {address : ℕ}
    (hl : left.RealFrame address) (hr : right.RealFrame address) : (Expr.natEq left right).RealFrame address := by
  intro memory value
  simp only [Expr.eval]
  rw [hl, hr]

theorem realFrame_select {condition : Expr .boolean} {yes no : Expr .real} {address : ℕ}
    (hc : condition.RealFrame address) (hy : yes.RealFrame address) (hn : no.RealFrame address) :
    (Expr.select condition yes no).RealFrame address := by
  intro memory value
  simp only [Expr.eval]
  rw [hc, hy, hn]

theorem realFrame_neg {value : Expr .real} {address : ℕ}
    (h : value.RealFrame address) : (Expr.neg value).RealFrame address := by
  intro memory v
  simp only [Expr.eval]
  rw [h]

theorem realFrame_log {value : Expr .real} {address : ℕ}
    (h : value.RealFrame address) : (Expr.log value).RealFrame address := by
  intro memory v
  simp only [Expr.eval]
  rw [h]

theorem realFrame_exp {value : Expr .real} {address : ℕ}
    (h : value.RealFrame address) : (Expr.exp value).RealFrame address := by
  intro memory v
  simp only [Expr.eval]
  rw [h]

theorem realFrame_lt {left right : Expr .real} {address : ℕ}
    (hl : left.RealFrame address) (hr : right.RealFrame address) : (Expr.lt left right).RealFrame address :=
  realFrame_binary Expr.lt (fun a b => decide (a < b)) (by intros; rfl) hl hr

theorem realFrame_le {left right : Expr .real} {address : ℕ}
    (hl : left.RealFrame address) (hr : right.RealFrame address) : (Expr.le left right).RealFrame address :=
  realFrame_binary Expr.le (fun a b => decide (a ≤ b)) (by intros; rfl) hl hr

def absExpr (value : Expr .real) : Expr .real :=
  .select (.lt value (.rational 0)) (.neg value) value

theorem absExpr_value (value : Expr .real) (memory : Memory) : (absExpr value).eval memory = |value.eval memory| := by
  by_cases h : value.eval memory < 0
  · simp [absExpr, Expr.eval, h, abs_of_neg h]
  · simp [absExpr, Expr.eval, h, abs_of_nonneg (le_of_not_gt h)]

theorem realFrame_abs {value : Expr .real} {address : ℕ}
    (h : value.RealFrame address) : (absExpr value).RealFrame address :=
  realFrame_select (realFrame_lt h (realFrame_rational _ _)) (realFrame_neg h) h

def arrayLoop (addresses : Fin n → ℕ) (values : Fin n → Expr .real) : List (Fin n) → Code
  | [] => .skip
  | i :: indices => .seq (writeReal (addresses i) (values i)) (arrayLoop addresses values indices)

def arrayProgram (addresses : Fin n → ℕ) (values : Fin n → Expr .real) : Code :=
  arrayLoop addresses values (List.finRange n)

theorem arrayLoop_steps (addresses : Fin n → ℕ) (values : Fin n → Expr .real) (c : ℕ)
    (hc : ∀ i, (values i).operations ≤ c) (indices : List (Fin n)) :
    Steps (arrayLoop addresses values indices) (indices.length * (c + 2)) := by
  induction indices with
  | nil => simpa only [arrayLoop, List.length_nil, Nat.zero_mul] using Steps.skip
  | cons i indices ih =>
      have hw := (Steps.real (.natural (addresses i)) (values i)).mono
        (show (Expr.natural (addresses i)).operations + (values i).operations + 1 ≤ c + 2 by
          simp only [Expr.operations]
          have h := hc i
          omega)
      simpa only [arrayLoop, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using hw.seq ih

theorem arrayProgram_steps (addresses : Fin n → ℕ) (values : Fin n → Expr .real) (c : ℕ)
    (hc : ∀ i, (values i).operations ≤ c) : Steps (arrayProgram addresses values) (n * (c + 2)) := by
  simpa only [arrayProgram, List.length_finRange] using arrayLoop_steps addresses values c hc (List.finRange n)

theorem arrayLoop_frame (tapes : Tapes) (s : State) (addresses : Fin n → ℕ) (values : Fin n → Expr .real)
    (indices : List (Fin n)) (address : ℕ) (h : ∀ i ∈ indices, address ≠ addresses i) :
    ((arrayLoop addresses values indices).execute tapes s).memory.real address = s.memory.real address := by
  induction indices generalizing s with
  | nil => rfl
  | cons i indices ih =>
      change ((arrayLoop addresses values indices).execute tapes ((writeReal (addresses i) (values i)).execute tapes s)).memory.real address = _
      rw [ih _ (by intro j hj; exact h j (List.mem_cons_of_mem _ hj))]
      exact writeReal_frame _ _ _ _ _ (h i (by simp))

theorem arrayLoop_value (tapes : Tapes) (s : State) (addresses : Fin n → ℕ) (values : Fin n → Expr .real)
    (hinj : Function.Injective addresses)
    (hframe : ∀ i j, (values i).RealFrame (addresses j))
    (indices : List (Fin n)) (hnodup : indices.Nodup) :
    ∀ i ∈ indices, ((arrayLoop addresses values indices).execute tapes s).memory.real (addresses i) =
      (values i).eval s.memory := by
  induction indices generalizing s with
  | nil => simp
  | cons head indices ih =>
      have hn := List.nodup_cons.mp hnodup
      let next := (writeReal (addresses head) (values head)).execute tapes s
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · change ((arrayLoop addresses values indices).execute tapes next).memory.real (addresses i) = _
        rw [arrayLoop_frame _ _ _ _ _ _ (by intro j hj he; exact hn.1 ((hinj he).symm ▸ hj))]
        exact writeReal_value _ _ _ _
      · have h := ih next hn.2 i hi
        change ((arrayLoop addresses values indices).execute tapes next).memory.real (addresses i) = _
        rw [h]
        exact hframe i head s.memory ((values head).eval s.memory)

theorem arrayProgram_value (tapes : Tapes) (s : State) (addresses : Fin n → ℕ) (values : Fin n → Expr .real)
    (hinj : Function.Injective addresses) (hframe : ∀ i j, (values i).RealFrame (addresses j)) (i : Fin n) :
    ((arrayProgram addresses values).execute tapes s).memory.real (addresses i) = (values i).eval s.memory :=
  arrayLoop_value _ _ _ _ hinj hframe _ (List.nodup_finRange n) i (List.mem_finRange i)

theorem arrayProgram_frame (tapes : Tapes) (s : State) (addresses : Fin n → ℕ)
    (values : Fin n → Expr .real) (address : ℕ) (h : ∀ i, address ≠ addresses i) :
    ((arrayProgram addresses values).execute tapes s).memory.real address = s.memory.real address :=
  arrayLoop_frame _ _ _ _ _ _ (fun i _ => h i)

end DPCut.RealMachine
