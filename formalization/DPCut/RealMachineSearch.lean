import DPCut.RealMachineSearchFrames

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace DPCut.RealMachine.EllipsoidCode

open SDP

def lowerAddress (n base : ℕ) := slot (n*n) base 12
def upperAddress (n base : ℕ) := lowerAddress n base + 1
def epsilonAddress (n base : ℕ) := lowerAddress n base + 2
def thresholdAddress (n base : ℕ) := slot (n*n) base 13
def bestAddress (n base : ℕ) := slot (n*n) base 15

def searchState (n base : ℕ) (s : State) : EllipsoidOptimization.State (n*n) :=
  ⟨WithLp.toLp 2 (readVector (n*n) (bestAddress n base) s.memory),
    s.memory.real (lowerAddress n base),s.memory.real (upperAddress n base)⟩

def midpointExpr (n base : ℕ) : Expr .real :=
  .div (.add (readReal (lowerAddress n base)) (readReal (upperAddress n base))) (.rational 2)

def failureUpperExpr (n base : ℕ) : Expr .real :=
  let bound := Expr.add (readReal (thresholdAddress n base)) (.div (readReal (epsilonAddress n base)) (.rational 4))
  .select (.le (readReal (upperAddress n base)) bound) (readReal (upperAddress n base)) bound

def successProgram (n base : ℕ) : Code :=
  .seq (arrayProgram (vectorAddress (bestAddress n base))
      (fun i : Fin (n*n) => readReal (vectorAddress (slot (n*n) base 0) i)))
    (writeReal (lowerAddress n base) (readReal (thresholdAddress n base)))

def failureProgram (n base : ℕ) : Code :=
  writeReal (upperAddress n base) (failureUpperExpr n base)

def searchStep (n base fuel : ℕ) : Code :=
  .seq (writeReal (thresholdAddress n base) (midpointExpr n base))
    (.seq (checkCode n base fuel)
      (.branch (readBoolean (slot (n*n) base 14)) (successProgram n base) (failureProgram n base)))

def searchLoop (n base fuel : ℕ) : ℕ → Code
  | 0 => .skip
  | rounds + 1 => .seq (searchStep n base fuel) (searchLoop n base fuel rounds)

theorem searchStep_steps (n base fuel : ℕ) :
    Steps (searchStep n base fuel)
      (100 * (n + 1) ^ 4 + fuel * (50000 * (n + 1) ^ 6 + 1000 * (n*n + 1) ^ 3 + 3)) := by
  have hm := Steps.real (.natural (thresholdAddress n base)) (midpointExpr n base)
  have hc := checkCode_steps n base fuel
  have hy := (arrayProgram_steps (vectorAddress (bestAddress n base))
    (fun i : Fin (n*n) => readReal (vectorAddress (slot (n*n) base 0) i)) 2 (by intro i; rfl)).seq
    (Steps.real (.natural (lowerAddress n base)) (readReal (thresholdAddress n base)))
  have hn := Steps.real (.natural (upperAddress n base)) (failureUpperExpr n base)
  exact (hm.seq (hc.seq (Steps.branch (readBoolean (slot (n*n) base 14)) hy hn))).mono (by
    simp only [Expr.operations, readReal, readBoolean, midpointExpr, failureUpperExpr, Nat.max_def]
    split_ifs <;> ring_nf <;> omega)

theorem searchLoop_steps (n base fuel rounds : ℕ) :
    Steps (searchLoop n base fuel rounds)
      (rounds * (100 * (n + 1) ^ 4 + fuel * (50000 * (n + 1) ^ 6 + 1000 * (n*n + 1) ^ 3 + 3))) := by
  induction rounds with
  | zero => simpa only [searchLoop, Nat.zero_mul] using Steps.skip
  | succ rounds ih =>
      exact ((searchStep_steps _ _ _).seq ih).mono (by ring_nf; omega)

end DPCut.RealMachine.EllipsoidCode
