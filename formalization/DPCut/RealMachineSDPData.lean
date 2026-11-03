import DPCut.RealMachineMatrixSums
import DPCut.RealMachineInverse
import DPCut.RealMachineDeterminant
import DPCut.RealMachinePSDComplete
import DPCut.SDPArithmeticCoordinates

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Matrix
open scoped BigOperators RealInnerProductSpace

namespace DPCut.RealMachine

def weightAddress {n : ℕ} (base : ℕ) (e : Edge n) : ℕ := base + ((Fintype.equivFin (Edge n)) e).val
def readWeights (n base : ℕ) (memory : Memory) : Weights n := fun e => memory.real (weightAddress base e)
def readCoordinates (n base : ℕ) (memory : Memory) : SDPCoordinates.Space n :=
  WithLp.toLp 2 (fun ij => (readMatrix n base memory) ij.1 ij.2)

def rationalEdgeVector {n : ℕ} (e : Edge n) (i : Fin n) : ℚ :=
  (if i = e.val.1 then 1 else 0) - (if i = e.val.2 then 1 else 0)

theorem rationalEdgeVector_cast {n : ℕ} (e : Edge n) (i : Fin n) :
    (rationalEdgeVector e i : ℝ) = edgeVector e i := by
  unfold rationalEdgeVector edgeVector
  split_ifs <;> norm_num

def matrixObjectiveExpr (n input : ℕ) (ij : Fin n × Fin n) (k : Fin (Fintype.card (Edge n))) : Expr .real :=
  let e := (Fintype.equivFin (Edge n)).symm k
  .mul (readReal (weightAddress input e)) (.rational (rationalEdgeVector e ij.1 * rationalEdgeVector e ij.2 / 4))

def matrixObjectiveProgram (n input output : ℕ) : Code :=
  matrixSumProgram n (Fintype.card (Edge n)) output (matrixObjectiveExpr n input)

theorem matrixObjective_steps (n input output : ℕ) :
    Steps (matrixObjectiveProgram n input output) (20 * (n + 1) ^ 4) := by
  have h := matrixSumProgram_steps n (Fintype.card (Edge n)) output 4 (matrixObjectiveExpr n input) (by intro ij k; rfl)
  have hm : Fintype.card (Edge n) ≤ n ^ 2 := by have h := twice_card_edge_le_square n; omega
  have hp := Nat.mul_le_mul_left (n * n) (Nat.add_le_add_left (Nat.mul_le_mul_right 9 hm) 3)
  exact h.mono (by nlinarith)

theorem matrixObjective_value (tapes : Tapes) (s : State) (n input output : ℕ)
    (h : ∀ e : Edge n, ∀ ij : Fin n × Fin n, weightAddress input e ≠ matrixAddress output ij) :
    readMatrix n output ((matrixObjectiveProgram n input output).execute tapes s).memory =
      objectiveMatrix (readWeights n input s.memory) := by
  unfold matrixObjectiveProgram
  rw [matrixSumProgram_value _ _ _ _ _ _ (by
    intro ij k kl
    exact realFrame_mul (realFrame_read _ _ (h _ kl)) (realFrame_rational _ _))]
  funext i j
  simp only [matrixObjectiveExpr, Expr.eval, readReal, Rat.cast_div, Rat.cast_mul, rationalEdgeVector_cast,
    Rat.cast_ofNat, objectiveMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply, readWeights]
  have hsum := (Fintype.equivFin (Edge n)).symm.sum_comp (fun e => s.memory.real (weightAddress input e) / 4 *
    (edgeVector e i * edgeVector e j))
  exact (Finset.sum_congr rfl (fun k _ => by ring)).trans hsum

def l1Program (n input output : ℕ) : Code :=
  sumProgram (fun k : Fin (Fintype.card (Edge n)) =>
    absExpr (readReal (weightAddress input ((Fintype.equivFin (Edge n)).symm k)))) output

theorem l1Program_steps (n input output : ℕ) : Steps (l1Program n input output) (20 * (n + 1) ^ 2) := by
  have h := sumProgram_steps (fun k : Fin (Fintype.card (Edge n)) =>
    absExpr (readReal (weightAddress input ((Fintype.equivFin (Edge n)).symm k)))) output 10 (by intro k; rfl)
  have hm : Fintype.card (Edge n) ≤ n ^ 2 := by have h := twice_card_edge_le_square n; omega
  exact h.mono ((Nat.add_le_add_left (Nat.mul_le_mul_right 15 hm) 3).trans (by ring_nf; omega))

theorem l1Program_value (tapes : Tapes) (s : State) (n input output : ℕ)
    (h : ∀ e : Edge n, weightAddress input e ≠ output) :
    ((l1Program n input output).execute tapes s).memory.real output = l1 (readWeights n input s.memory) := by
  unfold l1Program
  rw [sumProgram_value _ _ _ _ (fun k => realFrame_abs (realFrame_read _ _ (h _)))]
  simp only [absExpr_value, readReal, Expr.eval, l1, readWeights]
  exact (Fintype.equivFin (Edge n)).symm.sum_comp (fun e : Edge n => |s.memory.real (weightAddress input e)|)

def liftCoordinatesExpr (n input : ℕ) (ij : Fin n × Fin n) : Expr .real :=
  if ij.1 = ij.2 then .rational 1 else
    .div (.add (readReal (matrixAddress input ij)) (readReal (matrixAddress input (ij.2, ij.1)))) (.rational 2)

def liftCoordinatesProgram (n input output : ℕ) : Code :=
  matrixMapProgram n output (liftCoordinatesExpr n input)

theorem liftCoordinates_steps (n input output : ℕ) : Steps (liftCoordinatesProgram n input output) (10 * n * n) := by
  have h := matrixMap_steps n output 7 (liftCoordinatesExpr n input) (by
    intro ij; unfold liftCoordinatesExpr; split <;> simp [Expr.operations, readReal])
  exact h.mono (by nlinarith)

theorem liftCoordinates_value (tapes : Tapes) (s : State) (n input output : ℕ)
    (h : ∀ ij kl : Fin n × Fin n, matrixAddress input ij ≠ matrixAddress output kl) :
    readMatrix n output ((liftCoordinatesProgram n input output).execute tapes s).memory =
      SDPCoordinates.lift (readCoordinates n input s.memory) := by
  have hvalue := matrixMap_value tapes s n output (liftCoordinatesExpr n input) (by
    intro ij kl
    unfold liftCoordinatesExpr
    split
    · exact realFrame_rational _ _
    · exact realFrame_div (realFrame_add (realFrame_read _ _ (h ij kl)) (realFrame_read _ _ (h (ij.2, ij.1) kl)))
        (realFrame_rational _ _))
  funext i j
  unfold liftCoordinatesProgram
  rw [hvalue]
  by_cases hij : i = j <;>
    simp [liftCoordinatesExpr, Expr.eval, readReal, hij, SDPCoordinates.lift, readCoordinates, readMatrix]

def slackExpr (n input : ℕ) (ij : Fin n × Fin n) : Expr .real :=
  .sub (readReal (matrixAddress input ij)) (.rational (if ij.1 = ij.2 then (1 / (n : ℚ)) else 0))

def slackProgram (n input output : ℕ) : Code :=
  matrixMapProgram n output (slackExpr n input)

theorem slackProgram_steps (n input output : ℕ) : Steps (slackProgram n input output) (6 * n * n) := by
  simpa only [slackProgram, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    matrixMap_steps n output 4 (slackExpr n input) (by intro ij; rfl)

theorem slackProgram_value (tapes : Tapes) (s : State) (n input output : ℕ)
    (h : ∀ ij kl : Fin n × Fin n, matrixAddress input ij ≠ matrixAddress output kl) :
    readMatrix n output ((slackProgram n input output).execute tapes s).memory =
      readMatrix n input s.memory - (1 / (n : ℝ)) • 1 := by
  have hvalue := matrixMap_value tapes s n output (slackExpr n input)
    (fun ij kl => realFrame_sub (realFrame_read _ _ (h ij kl)) (realFrame_rational _ _))
  funext i j
  unfold slackProgram
  rw [hvalue]
  by_cases hij : i = j <;>
    simp [slackExpr, Expr.eval, readReal, readMatrix, hij, Matrix.one_apply, Rat.cast_div]

def coordinateNormProgram (n input output : ℕ) : Code :=
  .seq (sumProgram (fun k : Fin (n * n) =>
      let ij := finProdFinEquiv.symm k
      Expr.mul (readReal (matrixAddress input ij)) (readReal (matrixAddress input ij))) output)
    (writeReal output (.sqrt (readReal output)))

theorem coordinateNorm_steps (n input output : ℕ) : Steps (coordinateNormProgram n input output) (20 * (n + 1) ^ 2) := by
  have h := (sumProgram_steps (fun k : Fin (n * n) =>
      let ij := finProdFinEquiv.symm k
      Expr.mul (readReal (matrixAddress input ij)) (readReal (matrixAddress input ij))) output 5 (by intro k; rfl)).seq
    (Steps.real (.natural output) (.sqrt (readReal output)))
  exact h.mono (by simp only [Expr.operations, readReal]; nlinarith)

theorem coordinateNorm_value (tapes : Tapes) (s : State) (n input output : ℕ)
    (h : ∀ ij : Fin n × Fin n, matrixAddress input ij ≠ output) :
    ((coordinateNormProgram n input output).execute tapes s).memory.real output = ‖readCoordinates n input s.memory‖ := by
  let first := (sumProgram (fun k : Fin (n * n) =>
      let ij := finProdFinEquiv.symm k
      Expr.mul (readReal (matrixAddress input ij)) (readReal (matrixAddress input ij))) output).execute tapes s
  have hs : first.memory.real output = ∑ ij : Fin n × Fin n,
      s.memory.real (matrixAddress input ij) * s.memory.real (matrixAddress input ij) := by
    rw [sumProgram_value _ _ _ _ (fun k => realFrame_mul (realFrame_read _ _ (h _)) (realFrame_read _ _ (h _)))]
    exact finProdFinEquiv.symm.sum_comp (fun ij : Fin n × Fin n =>
      s.memory.real (matrixAddress input ij) * s.memory.real (matrixAddress input ij))
  change ((writeReal output (.sqrt (readReal output))).execute tapes first).memory.real output = _
  rw [writeReal_value]
  simp only [Expr.eval, readReal, hs]
  have he : (∑ ij : Fin n × Fin n, s.memory.real (matrixAddress input ij) * s.memory.real (matrixAddress input ij)) =
      ‖readCoordinates n input s.memory‖ ^ 2 := by
    rw [SDPCoordinates.norm_sq]
    simp [readCoordinates, readMatrix, Fintype.sum_prod_type, pow_two]
  rw [he, Real.sqrt_sq (norm_nonneg _)]

end DPCut.RealMachine
