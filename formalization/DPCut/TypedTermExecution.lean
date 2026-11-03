import DPCut.TypedMachineCommands

/-! Call-by-value execution of pure expressions. Both branches of a pure
selection are evaluated, as reflected by the conservative expression counter. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace DPCut.TypedMachine

def Term.execute {Γ : List ValueType} (s : Environment Γ) :
    {a : ValueType} → Term Γ a → a.Value × ℕ
  | _, .rational q => ((q:ℝ),1)
  | _, .natural n => (n,1)
  | _, .boolean b => (b,1)
  | _, .unit => ((),1)
  | _, .read v => (v.read s,v.operations)
  | _, .pair a b =>
      let x := a.execute s
      let y := b.execute s
      ((x.1,y.1),x.2+y.2+1)
  | _, .fst a =>
      let x := a.execute s
      (x.1.1,x.2+1)
  | _, .snd a =>
      let x := a.execute s
      (x.1.2,x.2+1)
  | _, .array (n:=n) values =>
      let x := fun i => (values i).execute s
      (fun i => (x i).1,(∑ i, (x i).2)+n+1)
  | _, .get (n:=n) (a:=a) values index =>
      let x := values.execute s
      let i := index.execute s
      ((if hi : i.1 < n then x.1 ⟨i.1,hi⟩ else a.zero),x.2+i.2+2)
  | _, .realBinary op a b =>
      let x := a.execute s
      let y := b.execute s
      (op.eval x.1 y.1,x.2+y.2+op.operations)
  | _, .realUnary op a =>
      let x := a.execute s
      (op.eval x.1,x.2+op.operations)
  | _, .naturalBinary op a b =>
      let x := a.execute s
      let y := b.execute s
      (op.eval x.1 y.1,x.2+y.2+1)
  | _, .cast a =>
      let x := a.execute s
      ((x.1:ℝ),x.2+1)
  | _, .ceil a =>
      let x := a.execute s
      (⌈x.1⌉₊,x.2+1)
  | _, .floor a =>
      let x := a.execute s
      (⌊x.1⌋₊,x.2+1)
  | _, .realCompare op a b =>
      let x := a.execute s
      let y := b.execute s
      (op.real x.1 y.1,x.2+y.2+1)
  | _, .naturalCompare op a b =>
      let x := a.execute s
      let y := b.execute s
      (op.natural x.1 y.1,x.2+y.2+1)
  | _, .and a b =>
      let x := a.execute s
      let y := b.execute s
      (x.1 && y.1,x.2+y.2+1)
  | _, .or a b =>
      let x := a.execute s
      let y := b.execute s
      (x.1 || y.1,x.2+y.2+1)
  | _, .not a =>
      let x := a.execute s
      (!x.1,x.2+1)
  | _, .select c a b =>
      let condition := c.execute s
      let x := a.execute s
      let y := b.execute s
      ((if condition.1 then x.1 else y.1),condition.2+x.2+y.2+1)
  | _, .sum (n:=n) a =>
      let x := a.execute s
      (∑ i, x.1 i,x.2+n+1)
  | _, .maximum (n:=n) a =>
      let x := a.execute s
      ((List.finRange n).foldl (fun old i => max old (x.1 i)) 0,x.2+2*n+1)

theorem Term.execute_eq {Γ : List ValueType} {a : ValueType} (term : Term Γ a) (s : Environment Γ) :
    term.execute s = (term.eval s,term.operations) := by
  induction term <;> simp_all only [Term.execute,Term.eval,Term.operations]

theorem Command.pure_operational {Γ : List ValueType} {a : ValueType} (term : Term Γ a) (s : Environment Γ) :
    (Command.pure term).run s = MeasureTheory.Measure.dirac ((term.execute s).1,(term.execute s).2+1,0) := by
  rw [Term.execute_eq]
  rfl

end DPCut.TypedMachine
