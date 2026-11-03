import DPCut.RealMachineMatVec
import DPCut.EllipsoidFeasibility
import DPCut.EllipsoidDeterminant

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Matrix
open scoped RealInnerProductSpace

namespace DPCut.RealMachine.EllipsoidCode

open SDP

def center (m base : ℕ) (s : State) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (readVector m (slot m base 0) s.memory)

def normal (m base : ℕ) (s : State) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (readVector m (slot m base 2) s.memory)

def axes (m base : ℕ) (s : State) := readMatrix m (slot m base 1) s.memory

def Matches (m base : ℕ) (s : State) (e : EllipsoidMethod.Ellipsoid (EuclideanSpace ℝ (Fin m))) : Prop :=
  center m base s = e.center ∧ Matrix.toEuclideanLin (axes m base s) = (e.axes : _ →ₗ[ℝ] _)

def axialExpression (m : ℕ) : Expr .real :=
  .div (.cast (.natural (m + 1))) (.cast (.natural (m + 2)))

def transverseExpression (m : ℕ) : Expr .real :=
  .div (.cast (.natural (m + 1)))
    (.sqrt (.sub (.mul (.cast (.natural (m + 1))) (.cast (.natural (m + 1)))) (.rational 1)))

def updateExpr (m base : ℕ) (ij : Fin m × Fin m) : Expr .real :=
  .add (if ij.1 = ij.2 then readReal (slot m base 11) else .rational 0)
    (.mul (.mul (.sub (readReal (slot m base 10)) (readReal (slot m base 11)))
        (readReal (vectorAddress (slot m base 5) ij.1)))
      (readReal (vectorAddress (slot m base 5) ij.2)))

def cutProgram (m base : ℕ) : Code :=
  .seq (matVecProgram (fun i j : Fin m => matrixAddress (slot m base 1) (j,i))
      (vectorAddress (slot m base 2)) (vectorAddress (slot m base 3)))
    (.seq (dotProgram (n := m) (vectorAddress (slot m base 3)) (vectorAddress (slot m base 3)) (slot m base 4))
      (.seq (writeReal (slot m base 4) (.sqrt (readReal (slot m base 4))))
        (.seq (arrayProgram (vectorAddress (slot m base 5))
            (fun i : Fin m => .div (readReal (vectorAddress (slot m base 3) i)) (readReal (slot m base 4))))
          (.seq (matVecProgram (fun i j : Fin m => matrixAddress (slot m base 1) (i,j))
              (vectorAddress (slot m base 5)) (vectorAddress (slot m base 6)))
            (.seq (writeReal (slot m base 10) (axialExpression m))
              (.seq (writeReal (slot m base 11) (transverseExpression m))
                (.seq (matrixMapProgram m (slot m base 7) (updateExpr m base))
                  (.seq (mulProgram m (slot m base 1) (slot m base 7) (slot m base 9))
                    (.seq (arrayProgram (vectorAddress (slot m base 8)) (fun i : Fin m =>
                        .sub (readReal (vectorAddress (slot m base 0) i))
                          (.div (readReal (vectorAddress (slot m base 6) i)) (.cast (.natural (m + 2))))))
                      (.seq (matrixMapProgram m (slot m base 1) (fun ij => readReal (matrixAddress (slot m base 9) ij)))
                        (arrayProgram (vectorAddress (slot m base 0))
                          (fun i : Fin m => readReal (vectorAddress (slot m base 8) i)))))))))))))

theorem updateExpr_steps (m base : ℕ) (ij : Fin m × Fin m) : (updateExpr m base ij).operations ≤ 17 := by
  unfold updateExpr
  split <;> norm_num [Expr.operations, readReal]

theorem cutProgram_steps (m base : ℕ) : Steps (cutProgram m base) (1000 * (m + 1) ^ 3) := by
  have hp := matVecProgram_steps (fun i j : Fin m => matrixAddress (slot m base 1) (j,i))
    (vectorAddress (slot m base 2)) (vectorAddress (slot m base 3))
  have hn := dotProgram_steps (n := m) (vectorAddress (slot m base 3)) (vectorAddress (slot m base 3)) (slot m base 4)
  have hs := Steps.real (.natural (slot m base 4)) (.sqrt (readReal (slot m base 4)))
  have hu := arrayProgram_steps (vectorAddress (slot m base 5))
    (fun i : Fin m => Expr.div (readReal (vectorAddress (slot m base 3) i)) (readReal (slot m base 4)))
    5 (by intro i; rfl)
  have hi := matVecProgram_steps (fun i j : Fin m => matrixAddress (slot m base 1) (i,j))
    (vectorAddress (slot m base 5)) (vectorAddress (slot m base 6))
  have ha := Steps.real (.natural (slot m base 10)) (axialExpression m)
  have hb := Steps.real (.natural (slot m base 11)) (transverseExpression m)
  have ht := matrixMap_steps m (slot m base 7) 17 (updateExpr m base) (updateExpr_steps m base)
  have hm := mulProgram_steps m (slot m base 1) (slot m base 7) (slot m base 9)
  have hc := arrayProgram_steps (vectorAddress (slot m base 8)) (fun i : Fin m =>
    Expr.sub (readReal (vectorAddress (slot m base 0) i))
      (.div (readReal (vectorAddress (slot m base 6) i)) (.cast (.natural (m + 2)))))
    8 (by intro i; rfl)
  have hcA := matrixMap_steps m (slot m base 1) 2 (fun ij => readReal (matrixAddress (slot m base 9) ij)) (by intro ij; rfl)
  have hcC := arrayProgram_steps (vectorAddress (slot m base 0))
    (fun i : Fin m => readReal (vectorAddress (slot m base 8) i)) 2 (by intro i; rfl)
  exact (hp.seq (hn.seq (hs.seq (hu.seq (hi.seq (ha.seq (hb.seq (ht.seq (hm.seq (hc.seq (hcA.seq hcC))))))))))).mono (by
    simp only [Expr.operations, readReal, axialExpression, transverseExpression]
    ring_nf
    omega)

theorem cutProgram_floor (m base floor : ℕ) (h : floor ≤ base) : (cutProgram m base).RealWriteFloor floor := by
  have hslot (k : ℕ) : floor ≤ slot m base k := by unfold slot; omega
  have hvec (k : ℕ) (i : Fin m) : floor ≤ vectorAddress (slot m base k) i := by
    unfold vectorAddress
    have hk := hslot k
    omega
  have hm (n left right output : ℕ) (ho : floor ≤ output) : (mulProgram n left right output).RealWriteFloor floor := by
    have hf (entries : List (Fin n × Fin n)) : (mulLoop left right output entries).RealWriteFloor floor := by
      induction entries with
      | nil => trivial
      | cons ij entries ih =>
          rcases ij with ⟨i,j⟩
          exact ⟨floor_dot _ _ _ _ (by unfold matrixAddress; omega), ih⟩
    exact hf _
  exact ⟨floor_matVec _ _ _ _ (hvec 3), floor_dot _ _ _ _ (hslot 4),
    floor_writeReal _ _ _ (hslot 4), floor_array _ _ _ (hvec 5), floor_matVec _ _ _ _ (hvec 6),
    floor_writeReal _ _ _ (hslot 10), floor_writeReal _ _ _ (hslot 11), floor_matrixMap _ _ _ _ (hslot 7),
    hm _ _ _ _ (hslot 9), floor_array _ _ _ (hvec 8), floor_matrixMap _ _ _ _ (hslot 1),
    floor_array _ _ _ (hvec 0)⟩

theorem axialExpression_value (m : ℕ) (s : State) :
    (axialExpression m).eval s.memory = EllipsoidMethod.axialRadius ((m + 1 : ℕ) : ℝ) := by
  simp only [axialExpression, Expr.eval, EllipsoidMethod.axialRadius, Nat.cast_add, Nat.cast_one]
  ring

theorem transverseExpression_value (m : ℕ) (s : State) :
    (transverseExpression m).eval s.memory = EllipsoidMethod.transverseRadius ((m + 1 : ℕ) : ℝ) := by
  simp only [transverseExpression, Expr.eval, EllipsoidMethod.transverseRadius, Rat.cast_one, pow_two]

end DPCut.RealMachine.EllipsoidCode
