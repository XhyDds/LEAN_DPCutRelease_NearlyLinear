import DPCut.GaussianWitness
import DPCut.LogDet
import DPCut.Statements

/-! The feasible spectrahedron and the paper's edge and matrix objectives. -/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise

namespace DPCut

lemma matrixPairing_eq_trace {n : ℕ} (A X : Mat n) :
    matrixPairing A X = (Aᵀ * X).trace := by
  simp only [matrixPairing, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

lemma matrixPairing_add_left {n : ℕ} (A B X : Mat n) :
    matrixPairing (A + B) X = matrixPairing A X + matrixPairing B X := by
  simp [matrixPairing, add_mul, Finset.sum_add_distrib]

lemma matrixPairing_sub_left {n : ℕ} (A B X : Mat n) :
    matrixPairing (A - B) X = matrixPairing A X - matrixPairing B X := by
  simp [matrixPairing, sub_mul, Finset.sum_sub_distrib]

lemma matrixPairing_sub_right {n : ℕ} (A X Y : Mat n) :
    matrixPairing A (X - Y) = matrixPairing A X - matrixPairing A Y := by
  simp [matrixPairing, mul_sub, Finset.sum_sub_distrib]

lemma edgeVector_eq {n : ℕ} (e : Edge n) :
    edgeVector e = Pi.single e.val.1 1 - Pi.single e.val.2 1 := by
  ext i
  simp [edgeVector, Pi.single_apply]

lemma edgeVector_quadratic {n : ℕ} {X : Mat n} (hX : X ∈ feasible n) (e : Edge n) :
    edgeVector e ⬝ᵥ (X *ᵥ edgeVector e) = 4 * fractionalQuery X e := by
  have hs : X e.val.2 e.val.1 = X e.val.1 e.val.2 := by
    simpa using hX.1.apply e.val.1 e.val.2
  simp [edgeVector_eq, Matrix.mulVec_sub, dotProduct_sub, hX.2.1, hs, fractionalQuery]
  ring

lemma fractionalQuery_eq_quadratic {n : ℕ} {X : Mat n} (hX : X ∈ feasible n) (e : Edge n) :
    fractionalQuery X e = (edgeVector e ⬝ᵥ (X *ᵥ edgeVector e)) / 4 := by
  rw [edgeVector_quadratic hX]
  ring

lemma objectiveMatrix_add {n : ℕ} (D ξ : Weights n) :
    objectiveMatrix (D + ξ) = objectiveMatrix D + objectiveMatrix ξ := by
  simp [objectiveMatrix, add_div, add_smul, Finset.sum_add_distrib]

lemma objectiveMatrix_transpose {n : ℕ} (D : Weights n) :
    (objectiveMatrix D)ᵀ = objectiveMatrix D := by
  simp [objectiveMatrix, Matrix.transpose_sum, Matrix.transpose_smul, Matrix.transpose_vecMulVec]

lemma matrixPairing_objectiveMatrix {n : ℕ} (D : Weights n) {X : Mat n}
    (hX : X ∈ feasible n) : matrixPairing (objectiveMatrix D) X = pairing D (fractionalQuery X) := by
  classical
  simp only [matrixPairing, objectiveMatrix, pairing, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  change (∑ i, ∑ j, (D e / 4 * (edgeVector e i * edgeVector e j)) * X i j) = _
  have he := edgeVector_quadratic hX e
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum] at he
  calc
    _ = D e / 4 * (∑ i, ∑ j, edgeVector e i * (X i j * edgeVector e j)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = D e * fractionalQuery X e := by rw [he]; ring

lemma feasible_one {n : ℕ} (hn : 2 ≤ n) : (1 : Mat n) ∈ feasible n := by
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  refine ⟨Matrix.isHermitian_one, by simp, ?_⟩
  have h : 0 ≤ 1 - 1 / (n : ℝ) := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hnR
    exact sub_nonneg.mpr (by simpa using this)
  convert (Matrix.PosSemidef.one : (1 : Mat n).PosSemidef).smul h using 1
  module

lemma feasible_convex (n : ℕ) : Convex ℝ (feasible n) := by
  intro X hX Y hY a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · change (a • X + b • Y).conjTranspose = a • X + b • Y
    have hx : X.conjTranspose = X := hX.1
    have hy : Y.conjTranspose = Y := hY.1
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, star_trivial, hx, hy]
  · intro i
    simpa [hX.2.1, hY.2.1] using hab
  · convert (hX.2.2.smul ha).add (hY.2.2.smul hb) using 1
    have hb' : b = 1 - a := by linarith
    rw [hb']
    module

lemma feasible_closed (n : ℕ) : IsClosed (feasible n) := by
  have hsym : IsClosed {X : Mat n | X.IsHermitian} := by
    change IsClosed {X : Mat n | X.conjTranspose = X}
    exact isClosed_eq (by fun_prop) continuous_id
  have hd : IsClosed {X : Mat n | ∀ i, X i i = 1} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun i => ?_
    exact isClosed_eq (by fun_prop) continuous_const
  have hp : IsClosed {X : Mat n | (X - (1 / (n : ℝ)) • 1).PosSemidef} := by
    change IsClosed {X : Mat n | (X - (1 / (n : ℝ)) • 1).IsHermitian ∧
      ∀ v, 0 ≤ star v ⬝ᵥ ((X - (1 / (n : ℝ)) • 1) *ᵥ v)}
    apply IsClosed.inter
    · exact hsym.preimage (by fun_prop)
    · have hq (v : Fin n → ℝ) : IsClosed {X : Mat n |
          0 ≤ star v ⬝ᵥ ((X - (1 / (n : ℝ)) • 1) *ᵥ v)} := by
        apply isClosed_le continuous_const
        unfold dotProduct Matrix.mulVec
        fun_prop
      simpa only [Set.iInter_setOf] using isClosed_iInter hq
  exact hsym.inter (hd.inter hp)

lemma feasible_entry_abs_le_one {n : ℕ} (hn : 2 ≤ n) {X : Mat n}
    (hX : X ∈ feasible n) (i j : Fin n) : |X i j| ≤ 1 := by
  have hps := (feasible_posDef hn hX).posSemidef
  have hs : X j i = X i j := by simpa using hX.1.apply i j
  have hl := hps.2 (Pi.single i 1 + Pi.single j 1)
  have hu := hps.2 (Pi.single i 1 - Pi.single j 1)
  simp [Matrix.mulVec_add, Matrix.mulVec_sub, dotProduct_add, dotProduct_sub,
    hX.2.1, hs] at hl hu
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma feasible_compact {n : ℕ} (hn : 2 ≤ n) : IsCompact (feasible n) := by
  have hc : IsCompact (Set.pi Set.univ (fun _ : Fin n =>
      Set.pi Set.univ (fun _ : Fin n => Set.Icc (-1 : ℝ) 1))) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
  apply hc.of_isClosed_subset (feasible_closed n)
  intro X hX i _ j _
  exact abs_le.mp (feasible_entry_abs_le_one hn hX i j)

lemma objective_continuousOn {n : ℕ} (hn : 2 ≤ n) (lam : ℝ) (D : Weights n) :
    ContinuousOn (objective lam D) (feasible n) := by
  have hp : Continuous (fun X : Mat n => pairing D (fractionalQuery X)) := by
    unfold pairing fractionalQuery
    fun_prop
  apply hp.continuousOn.add
  apply continuousOn_const.mul
  exact continuous_id.matrix_det.continuousOn.log (fun X hX => (feasible_posDef hn hX).det_pos.ne')

lemma optimizer_exists {n : ℕ} (hn : 2 ≤ n) (lam : ℝ) (D : Weights n) :
    ∃ X, IsOptimizer lam D X := by
  obtain ⟨X, hX, hm⟩ := (feasible_compact hn).exists_isMaxOn
    ⟨1, feasible_one hn⟩ (objective_continuousOn hn lam D)
  exact ⟨X, hX, hm⟩

end DPCut
