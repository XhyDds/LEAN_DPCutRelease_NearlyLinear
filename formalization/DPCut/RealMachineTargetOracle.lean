import DPCut.SDPFlatCoordinates
import DPCut.RealMachineEllipsoidLoop

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace DPCut.RealMachine.TargetCode

open SDP EllipsoidCode

def workspace (n base : ℕ) : ℕ := slot (n*n) base 16

def copyPoint (n base : ℕ) : Code :=
  matrixMapProgram n (slot n (workspace n base) 1) (fun ij =>
    readReal (vectorAddress (slot (n*n) base 0) (finProdFinEquiv ij)))

def copyNormalExpr (n base : ℕ) (negative : Bool) (i : Fin (n*n)) : Expr .real :=
  let value := readReal (matrixAddress (slot n (workspace n base) 3) (finProdFinEquiv.symm i))
  if negative then .neg value else value

def copyNormal (n base : ℕ) (negative : Bool) : Code :=
  arrayProgram (vectorAddress (slot (n*n) base 2)) (copyNormalExpr n base negative)

def fixedNormalProgram (n base : ℕ) : Code :=
  arrayProgram (vectorAddress (slot (n*n) base 2)) (fun i : Fin (n*n) => .rational (if i.val = 0 then 1 else 0))

def accept (n base : ℕ) : Code := writeBoolean (slot (n*n) base 14) (.boolean true)
def reject (n base : ℕ) : Code := writeBoolean (slot (n*n) base 14) (.boolean false)

def gradientReject (n base : ℕ) : Code :=
  .seq (coordinateNormProgram n (slot n (workspace n base) 3) (slot n (workspace n base) 11 + 1))
    (.seq (.branch (.eq (readReal (slot n (workspace n base) 11 + 1)) (.rational 0))
      (fixedNormalProgram n base) (copyNormal n base true)) (reject n base))

def decideReply (n base : ℕ) : Code :=
  .branch (readBoolean (slot n (workspace n base) 4))
    (.branch (.le (readReal (slot (n*n) base 13)) (readReal (slot n (workspace n base) 4)))
      (accept n base) (gradientReject n base))
    (.seq (copyNormal n base false) (reject n base))

def ask (n base : ℕ) : Code :=
  .seq (copyPoint n base) (.seq (SDP.oracleProgram n (workspace n base)) (decideReply n base))

def Context (n base : ℕ) (lam B threshold : ℝ) (D : Weights n) (s : State) : Prop :=
  SDP.inputWeights n (workspace n base) s = D ∧ SDP.inputLambda n (workspace n base) s = lam ∧
    SDP.inputBound n (workspace n base) s = B ∧ s.memory.real (slot (n*n) base 13) = threshold

theorem context_real (n base : ℕ) (lam B threshold : ℝ) (D : Weights n)
    (s t : State) (h : s.memory.real = t.memory.real) (hs : Context n base lam B threshold D s) :
    Context n base lam B threshold D t := by
  have hweights : SDP.inputWeights n (workspace n base) t = SDP.inputWeights n (workspace n base) s := by
    funext edge
    exact congrFun h.symm _
  exact ⟨hweights.trans hs.1, (congrFun h.symm _).trans hs.2.1,
    (congrFun h.symm _).trans hs.2.2.1, (congrFun h.symm _).trans hs.2.2.2⟩

theorem copyPoint_steps (n base : ℕ) : Steps (copyPoint n base) (4 * n * n) := by
  simpa only [copyPoint, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    matrixMap_steps n (slot n (workspace n base) 1) 2
      (fun ij => readReal (vectorAddress (slot (n*n) base 0) (finProdFinEquiv ij))) (by intro ij; rfl)

theorem copyNormal_steps (n base : ℕ) (negative : Bool) : Steps (copyNormal n base negative) (5 * n * n) := by
  have h := arrayProgram_steps (vectorAddress (slot (n*n) base 2)) (copyNormalExpr n base negative) 3 (by
    intro i
    unfold copyNormalExpr
    cases negative <;> norm_num [readReal, Expr.operations])
  simpa only [copyNormal, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

theorem fixedNormal_steps (n base : ℕ) : Steps (fixedNormalProgram n base) (3 * n * n) := by
  simpa only [fixedNormalProgram, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    arrayProgram_steps (vectorAddress (slot (n*n) base 2)) (fun i : Fin (n*n) => Expr.rational (if i.val = 0 then 1 else 0))
      1 (by intro i; rfl)

theorem ask_steps (n base : ℕ) : Steps (ask n base) (50000 * (n + 1) ^ 6) := by
  have hc := copyPoint_steps n base
  have ho := SDP.oracleProgram_steps n (workspace n base)
  have hy := Steps.boolean (.natural (slot (n*n) base 14)) (.boolean true)
  have hn := Steps.boolean (.natural (slot (n*n) base 14)) (.boolean false)
  have hg := (coordinateNorm_steps n (slot n (workspace n base) 3) (slot n (workspace n base) 11 + 1)).seq
    ((Steps.branch (.eq (readReal (slot n (workspace n base) 11 + 1)) (.rational 0))
      (fixedNormal_steps n base) (copyNormal_steps n base true)).seq hn)
  have hd := Steps.branch (readBoolean (slot n (workspace n base) 4))
    (Steps.branch (.le (readReal (slot (n*n) base 13)) (readReal (slot n (workspace n base) 4))) hy hg)
    ((copyNormal_steps n base false).seq hn)
  exact (hc.seq (ho.seq hd)).mono (by
    simp only [Expr.operations, readReal, readBoolean, Nat.max_def]
    split_ifs <;> ring_nf <;> omega)

theorem workspace_after (n base index : ℕ) (h : index < 16) :
    slot (n*n) base index < workspace n base := slot_lt_slot _ _ _ _ h

theorem cut_context (n base : ℕ) (lam B threshold : ℝ) (D : Weights n) (tapes : Tapes) (s : State)
    (hs : Context n base lam B threshold D s) :
    Context n base lam B threshold D ((cutProgram (n*n) base).execute tapes s) := by
  have hc (address : ℕ) (ha : slot (n*n) base 12 ≤ address) :
      ((cutProgram (n*n) base).execute tapes s).memory.real address = s.memory.real address :=
    Code.realWriteCeiling_frame _ _ (cutProgram_ceiling (n*n) base) tapes s address ha
  have hbefore : slot (n*n) base 12 ≤ workspace n base := (workspace_after n base 12 (by decide)).le
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hs.1]
    funext edge
    exact hc _ (hbefore.trans (by
      have h := (weight_range (slot n (workspace n base) 0) edge).1
      simpa only [slot, Nat.mul_zero, Nat.add_zero] using h))
  · exact (hc _ (hbefore.trans (by unfold slot; omega))).trans hs.2.1
  · exact (hc _ (hbefore.trans (by unfold slot; omega))).trans hs.2.2.1
  · exact (hc _ (slot_lt_slot _ _ _ _ (by decide)).le).trans hs.2.2.2

end DPCut.RealMachine.TargetCode
