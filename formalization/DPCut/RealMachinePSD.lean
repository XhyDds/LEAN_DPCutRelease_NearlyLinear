import DPCut.RealMachineNonzero
import DPCut.RealMachineFrames
import DPCut.RealMachineSolve

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace DPCut.RealMachine

def tailProgram (n input output : ℕ) : Code :=
  matrixMapProgram n output (fun ij =>
    readReal (matrixAddress (n := n + 1) input (ij.1.succ, ij.2.succ)))

theorem tailProgram_steps (n input output : ℕ) : Steps (tailProgram n input output) (4 * n * n) := by
  exact (matrixMap_steps n output 2 _ (by intro i; rfl)).mono (by ring_nf; rfl)

def specialPivotExpr (n input index : ℕ) : Expr .real :=
  let j := Expr.natAdd (readNatural index) (.natural 1)
  let diagonal := Expr.natAdd (.natural input) (.natMul (.natural (n + 2)) j)
  let row := Expr.natAdd (.natural input) j
  .div (.neg (.add (.readReal diagonal) (.rational 1)))
    (.mul (.rational 2) (.readReal row))

def specialOutputExpr (n pivot index : ℕ) (i : Fin (n + 1)) : Expr .real :=
  Fin.cases (readReal pivot) (fun j =>
    .select (.natEq (.natural j.val) (readNatural index)) (.rational 1) (.rational 0)) i

def liftOutputExpr (n pivot child : ℕ) (i : Fin (n + 1)) : Expr .real :=
  Fin.cases (readReal pivot) (fun j => readReal (vectorAddress child j)) i

def liftPivotProgram (n input pivot child : ℕ) : Code :=
  .branch (.eq (readReal (matrixAddress (n := n + 1) input (0, 0))) (.rational 0))
    (writeReal pivot (.rational 0))
    (.seq (dotProgram (fun i : Fin n => matrixAddress (n := n + 1) input (0, i.succ))
        (fun i => vectorAddress child i) pivot)
      (writeReal pivot (.div (.neg (readReal pivot))
        (readReal (matrixAddress (n := n + 1) input (0, 0))))))

def liftPSDProgram (n input output flag pivot child : ℕ) : Code :=
  .branch (readBoolean flag)
    (.seq (liftPivotProgram n input pivot child)
      (arrayProgram (fun i : Fin (n + 1) => vectorAddress output i) (liftOutputExpr n pivot child)))
    .skip

def negativePSDProgram (n output flag : ℕ) : Code :=
  .seq (writeBoolean flag (.boolean true))
    (arrayProgram (fun i : Fin (n + 1) => vectorAddress output i)
      (fun i => .rational (if i = 0 then 1 else 0)))

def specialPSDProgram (n input output flag scratch : ℕ) : Code :=
  .seq (writeReal (scratch + 1) (specialPivotExpr n input scratch))
    (.seq (writeBoolean flag (.boolean true))
      (arrayProgram (fun i : Fin (n + 1) => vectorAddress output i)
        (specialOutputExpr n (scratch + 1) scratch)))

def preparePSDProgram (n input matrix : ℕ) : Code :=
  .branch (.eq (readReal (matrixAddress (n := n + 1) input (0, 0))) (.rational 0))
    (tailProgram n input matrix) (schurProgram n input matrix)

def psdProgram : ℕ → ℕ → ℕ → ℕ → ℕ → Code
  | 0, _, _, flag, _ => writeBoolean flag (.boolean false)
  | n + 1, input, output, flag, scratch =>
      let matrix := scratch + 2
      let child := matrix + n * n
      let next := child + n
      let recurse := .seq (preparePSDProgram n input matrix) (.seq (psdProgram n matrix child flag next)
        (liftPSDProgram n input output flag (scratch + 1) child))
      .branch (.lt (readReal (matrixAddress (n := n + 1) input (0, 0))) (.rational 0)) (negativePSDProgram n output flag)
        (.seq (firstNonzeroProgram (fun i : Fin n => matrixAddress (n := n + 1) input (0, i.succ)) scratch scratch)
          (.branch (.and (.eq (readReal (matrixAddress (n := n + 1) input (0, 0))) (.rational 0))
              (readBoolean scratch)) (specialPSDProgram n input output flag scratch) recurse))

def psdResult (n output flag : ℕ) (s : State) : Option (Fin n → ℝ) :=
  if s.memory.boolean flag then some (readVector n output s.memory) else none

theorem liftPSD_steps (n input output flag pivot child : ℕ) :
    Steps (liftPSDProgram n input output flag pivot child) (40 * (n + 1)) := by
  have hd := (dotProgram_steps (fun i : Fin n => matrixAddress (n := n + 1) input (0, i.succ))
    (fun i => vectorAddress child i) pivot).seq
      (Steps.real (.natural pivot) (.div (.neg (readReal pivot))
        (readReal (matrixAddress (n := n + 1) input (0, 0)))))
  have hp := Steps.branch (.eq (readReal (matrixAddress (n := n + 1) input (0, 0))) (.rational 0))
    (Steps.real (.natural pivot) (.rational 0)) hd
  have ho := arrayProgram_steps (fun i : Fin (n + 1) => vectorAddress output i) (liftOutputExpr n pivot child)
    2 (by intro i; refine Fin.cases ?_ (fun i => ?_) i <;> rfl)
  have h := Steps.branch (readBoolean flag) (hp.seq ho) Steps.skip
  exact h.mono (by simp only [Expr.operations, readReal, readBoolean]; omega)

theorem psdProgram_steps (n input output flag scratch : ℕ) :
    Steps (psdProgram n input output flag scratch) (500 * (n + 1) ^ 3) := by
  induction n generalizing input output scratch with
  | zero => exact (Steps.boolean (.natural flag) (.boolean false)).mono (by norm_num [Expr.operations])
  | succ n ih =>
      have hnegative := (Steps.boolean (.natural flag) (.boolean true)).seq
        (arrayProgram_steps (fun i : Fin (n + 1) => vectorAddress output i)
          (fun i => Expr.rational (if i = 0 then 1 else 0)) 1 (by intro i; rfl))
      have hspecial := (Steps.real (.natural (scratch + 1)) (specialPivotExpr n input scratch)).seq
        ((Steps.boolean (.natural flag) (.boolean true)).seq
          (arrayProgram_steps (fun i : Fin (n + 1) => vectorAddress output i) (specialOutputExpr n (scratch + 1) scratch)
            8 (by intro i; refine Fin.cases ?_ (fun i => ?_) i <;> norm_num [specialOutputExpr, Expr.operations, readReal, readNatural])))
      have hprepare := Steps.branch (.eq (readReal (matrixAddress (n := n + 1) input (0, 0))) (.rational 0))
        (tailProgram_steps n input (scratch + 2)) (schurProgram_steps n input (scratch + 2))
      have hrecursive := hprepare.seq
        ((ih (scratch + 2) (scratch + 2 + n * n) (scratch + 2 + n * n + n)).seq
          (liftPSD_steps n input output flag (scratch + 1) (scratch + 2 + n * n)))
      have hscan := firstNonzeroProgram_steps (fun i : Fin n => matrixAddress (n := n + 1) input (0, i.succ)) scratch scratch
      have h := Steps.branch (.lt (readReal (matrixAddress (n := n + 1) input (0, 0))) (.rational 0))
        hnegative (hscan.seq (Steps.branch (.and (.eq (readReal (matrixAddress (n := n + 1) input (0, 0))) (.rational 0))
          (readBoolean scratch)) hspecial hrecursive))
      exact h.mono (by
        simp only [Expr.operations, readReal, readBoolean, readNatural, specialPivotExpr]
        have hn : n ≤ (n + 1) ^ 3 := (Nat.le_succ n).trans (Nat.le_self_pow (by decide : 3 ≠ 0) (n + 1))
        simp only [Nat.max_def]
        split_ifs <;> nlinarith)

end DPCut.RealMachine
