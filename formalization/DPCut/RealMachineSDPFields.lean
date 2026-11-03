import DPCut.RealMachineSDPData

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Matrix
open scoped BigOperators

namespace DPCut.RealMachine

theorem weightAddress_injective {n : ℕ} (base : ℕ) : Function.Injective (weightAddress (n := n) base) := by
  intro e f he
  apply (Fintype.equivFin (Edge n)).injective
  apply Fin.ext
  unfold weightAddress at he
  omega

def boundedWeightExpr (n input bound l1 : ℕ) (k : Fin (Fintype.card (Edge n))) : Expr .real :=
  .select (.le (readReal l1) (readReal bound))
    (readReal (weightAddress input ((Fintype.equivFin (Edge n)).symm k))) (.rational 0)

def boundedWeightsProgram (n input output bound l1 : ℕ) : Code :=
  arrayProgram (fun k : Fin (Fintype.card (Edge n)) => output + k.val) (boundedWeightExpr n input bound l1)

theorem boundedWeights_steps (n input output bound l1 : ℕ) :
    Steps (boundedWeightsProgram n input output bound l1) (20 * (n + 1) ^ 2) := by
  have h := arrayProgram_steps (fun k : Fin (Fintype.card (Edge n)) => output + k.val)
    (boundedWeightExpr n input bound l1) 9 (by intro k; rfl)
  have hm : Fintype.card (Edge n) ≤ n ^ 2 := by have h := twice_card_edge_le_square n; omega
  exact h.mono ((Nat.mul_le_mul_right 11 hm).trans (by ring_nf; omega))

theorem boundedWeights_value (tapes : Tapes) (s : State) (n input output bound l1 : ℕ)
    (hD : ∀ e f : Edge n, weightAddress input e ≠ weightAddress output f)
    (hb : ∀ e : Edge n, bound ≠ weightAddress output e)
    (hl : ∀ e : Edge n, l1 ≠ weightAddress output e)
    (hs : s.memory.real l1 = DPCut.l1 (readWeights n input s.memory)) :
    readWeights n output ((boundedWeightsProgram n input output bound l1).execute tapes s).memory =
      boundedObjective (s.memory.real bound) (readWeights n input s.memory) := by
  funext e
  have hinj : Function.Injective (fun k : Fin (Fintype.card (Edge n)) => output + k.val) := by
    intro i j h
    apply Fin.ext
    change output + i.val = output + j.val at h
    exact Nat.add_left_cancel h
  have haddr (k : Fin (Fintype.card (Edge n))) :
      weightAddress output ((Fintype.equivFin (Edge n)).symm k) = output + k.val := by
    simp [weightAddress]
  have hv := arrayProgram_value tapes s (fun k : Fin (Fintype.card (Edge n)) => output + k.val)
    (boundedWeightExpr n input bound l1) hinj (by
      intro i j
      exact realFrame_select (realFrame_le
        (realFrame_read _ _ (by simpa only [haddr] using hl ((Fintype.equivFin (Edge n)).symm j)))
        (realFrame_read _ _ (by simpa only [haddr] using hb ((Fintype.equivFin (Edge n)).symm j))))
        (realFrame_read _ _ (by simpa only [haddr] using
          (hD ((Fintype.equivFin (Edge n)).symm i) ((Fintype.equivFin (Edge n)).symm j)))) (realFrame_rational _ _))
    ((Fintype.equivFin (Edge n)) e)
  unfold boundedWeightsProgram
  change ((arrayProgram (fun k : Fin (Fintype.card (Edge n)) => output + k.val)
    (boundedWeightExpr n input bound l1)).execute tapes s).memory.real (output + ((Fintype.equivFin (Edge n)) e).val) = _
  rw [hv]
  simp only [boundedWeightExpr, Expr.eval, readReal, Equiv.symm_apply_apply, hs,
    readWeights, boundedObjective, Rat.cast_zero]
  by_cases hp : DPCut.l1 (readWeights n input s.memory) ≤ s.memory.real bound <;>
    simp [hp, readWeights]

def gradientNormalExpr (n matrix inverse lam : ℕ) (ij : Fin n × Fin n) : Expr .real :=
  if ij.1 = ij.2 then .rational 0 else
    .div
      (.add (.add (readReal (matrixAddress matrix ij)) (.mul (readReal lam) (readReal (matrixAddress inverse ij))))
        (.add (readReal (matrixAddress matrix (ij.2, ij.1))) (.mul (readReal lam) (readReal (matrixAddress inverse (ij.2, ij.1))))))
      (.rational 2)

def gradientNormalProgram (n matrix inverse lam output : ℕ) : Code :=
  matrixMapProgram n output (gradientNormalExpr n matrix inverse lam)

theorem gradientNormal_steps (n matrix inverse lam output : ℕ) :
    Steps (gradientNormalProgram n matrix inverse lam output) (30 * (n + 1) ^ 2) := by
  have h := matrixMap_steps n output 19 (gradientNormalExpr n matrix inverse lam)
    (by intro ij; unfold gradientNormalExpr; split <;> norm_num [Expr.operations, readReal])
  exact h.mono (by ring_nf; omega)

theorem gradientNormal_value (tapes : Tapes) (s : State) (n matrix inverse lam output : ℕ)
    (hA : ∀ ij kl : Fin n × Fin n, matrixAddress matrix ij ≠ matrixAddress output kl)
    (hI : ∀ ij kl : Fin n × Fin n, matrixAddress inverse ij ≠ matrixAddress output kl)
    (hL : ∀ ij : Fin n × Fin n, lam ≠ matrixAddress output ij) :
    readCoordinates n output ((gradientNormalProgram n matrix inverse lam output).execute tapes s).memory =
      SDPCoordinates.normal n (readMatrix n matrix s.memory + (s.memory.real lam) • readMatrix n inverse s.memory) := by
  have hv := matrixMap_value tapes s n output (gradientNormalExpr n matrix inverse lam) (by
    intro ij kl
    unfold gradientNormalExpr
    split
    · exact realFrame_rational _ _
    · exact realFrame_div
        (realFrame_add
          (realFrame_add (realFrame_read _ _ (hA ij kl)) (realFrame_mul (realFrame_read _ _ (hL kl)) (realFrame_read _ _ (hI ij kl))))
          (realFrame_add (realFrame_read _ _ (hA (ij.2, ij.1) kl)) (realFrame_mul (realFrame_read _ _ (hL kl)) (realFrame_read _ _ (hI (ij.2, ij.1) kl)))))
        (realFrame_rational _ _))
  rw [SDPCoordinates.normal_formula]
  ext ij
  change readMatrix n output ((gradientNormalProgram n matrix inverse lam output).execute tapes s).memory ij.1 ij.2 = _
  unfold gradientNormalProgram
  rw [hv]
  by_cases h : ij.1 = ij.2 <;>
    simp [gradientNormalExpr, Expr.eval, readReal, readCoordinates, readMatrix, SDPCoordinates.flatten,
      SDPCoordinates.project, h]

def negativeNormalExpr (n vector : ℕ) (ij : Fin n × Fin n) : Expr .real :=
  if ij.1 = ij.2 then .rational 0 else
    .neg (.mul (readReal (vectorAddress vector ij.1)) (readReal (vectorAddress vector ij.2)))

def negativeNormalProgram (n vector output : ℕ) : Code :=
  matrixMapProgram n output (negativeNormalExpr n vector)

theorem negativeNormal_steps (n vector output : ℕ) :
    Steps (negativeNormalProgram n vector output) (10 * (n + 1) ^ 2) := by
  have h := matrixMap_steps n output 6 (negativeNormalExpr n vector)
    (by intro ij; unfold negativeNormalExpr; split <;> norm_num [Expr.operations, readReal])
  exact h.mono (by ring_nf; omega)

theorem negativeNormal_value (tapes : Tapes) (s : State) (n vector output : ℕ)
    (h : ∀ i : Fin n, ∀ ij : Fin n × Fin n, vectorAddress vector i ≠ matrixAddress output ij) :
    readCoordinates n output ((negativeNormalProgram n vector output).execute tapes s).memory =
      SDPCoordinates.normal n (-(Matrix.vecMulVec (readVector n vector s.memory) (readVector n vector s.memory))) := by
  have hv := matrixMap_value tapes s n output (negativeNormalExpr n vector) (by
    intro ij kl
    unfold negativeNormalExpr
    split
    · exact realFrame_rational _ _
    · exact realFrame_neg (realFrame_mul (realFrame_read _ _ (h ij.1 kl)) (realFrame_read _ _ (h ij.2 kl))))
  rw [SDPCoordinates.normal_formula]
  ext ij
  change readMatrix n output ((negativeNormalProgram n vector output).execute tapes s).memory ij.1 ij.2 = _
  unfold negativeNormalProgram
  rw [hv]
  by_cases he : ij.1 = ij.2 <;>
    simp [negativeNormalExpr, Expr.eval, readReal, readCoordinates, readVector, readMatrix,
      SDPCoordinates.flatten, SDPCoordinates.project, he, Matrix.vecMulVec, mul_comm]

def queryPairExpr (n weights matrix : ℕ) (k : Fin (Fintype.card (Edge n))) : Expr .real :=
  let e := (Fintype.equivFin (Edge n)).symm k
  .mul (readReal (weightAddress weights e))
    (.div (.sub (.rational 1) (readReal (matrixAddress matrix (e.val.1, e.val.2)))) (.rational 2))

def queryPairProgram (n weights matrix output : ℕ) : Code :=
  sumProgram (queryPairExpr n weights matrix) output

theorem queryPair_steps (n weights matrix output : ℕ) :
    Steps (queryPairProgram n weights matrix output) (30 * (n + 1) ^ 2) := by
  have h := sumProgram_steps (queryPairExpr n weights matrix) output 9 (by intro k; rfl)
  have hm : Fintype.card (Edge n) ≤ n ^ 2 := by have h := twice_card_edge_le_square n; omega
  exact h.mono ((Nat.add_le_add_left (Nat.mul_le_mul_right 14 hm) 3).trans (by ring_nf; omega))

theorem queryPair_value (tapes : Tapes) (s : State) (n weights matrix output : ℕ)
    (hW : ∀ e : Edge n, weightAddress weights e ≠ output)
    (hM : ∀ ij : Fin n × Fin n, matrixAddress matrix ij ≠ output) :
    ((queryPairProgram n weights matrix output).execute tapes s).memory.real output =
      pairing (readWeights n weights s.memory) (fractionalQuery (readMatrix n matrix s.memory)) := by
  unfold queryPairProgram
  have hf (k : Fin (Fintype.card (Edge n))) : (queryPairExpr n weights matrix k).RealFrame output := by
    unfold queryPairExpr
    exact realFrame_mul (realFrame_read _ _ (hW _))
      (realFrame_div (realFrame_sub (realFrame_rational _ _) (realFrame_read _ _ (hM _))) (realFrame_rational _ _))
  rw [sumProgram_value tapes s (queryPairExpr n weights matrix) output hf]
  simp only [queryPairExpr, Expr.eval, readReal, Rat.cast_one, Rat.cast_ofNat, pairing, fractionalQuery, readWeights, readMatrix]
  exact (Fintype.equivFin (Edge n)).symm.sum_comp (fun e : Edge n =>
    s.memory.real (weightAddress weights e) * ((1 - s.memory.real (matrixAddress matrix (e.val.1, e.val.2))) / 2))

end DPCut.RealMachine
