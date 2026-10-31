import DPCut.SDPLSWProblem
import DPCut.MatrixSPDArithmetic

/-! Explicit scalar formulas for the coordinate projection and its adjoint. -/
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped BigOperators RealInnerProductSpace
namespace DPCut.SDPCoordinates
attribute [local instance] Classical.propDecidable

def project {n : ℕ} (A : Mat n) : Mat n :=
  fun i j => if i=j then 0 else (A i j + A j i)/2

lemma project_pairing {n : ℕ} (A : Mat n) (z : Space n) :
    matrixPairing (project A) (fun i j => z (i,j)) = matrixPairing A (offDiag n z) := by
  have hswap : (∑ i, ∑ j, (if i=j then 0 else A j i * z (i,j))) =
      ∑ i, ∑ j, (if i=j then 0 else A i j * z (j,i)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [eq_comm]
  have h1 : matrixPairing (project A) (fun i j => z (i,j)) =
      ((∑ i, ∑ j, (if i=j then 0 else A i j*z (i,j))) +
        (∑ i, ∑ j, (if i=j then 0 else A j i*z (i,j))))/2 := by
    simp only [matrixPairing, project, ← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [h1, hswap]
  simp only [matrixPairing, offDiag_apply, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

lemma normal_formula {n : ℕ} (A : Mat n) : normal n A = flatten n (project A) := by
  apply ext_inner_right ℝ
  intro z
  rw [normal_inner]
  have hz : flatten n (fun i j => z (i,j)) = z := rfl
  conv_rhs => rw [← hz]
  rw [flatten_inner, project_pairing]

namespace Counted
open Arithmetic

def lift {n : ℕ} (z : Space n) : Arithmetic (Mat n) :=
  collect fun i => collect fun j =>
    if i=j then Arithmetic.pure 1 else do
      let a ← Arithmetic.add (z (i,j)) (z (j,i))
      Arithmetic.div a 2

lemma lift_value {n : ℕ} (z : Space n) : (lift z).value = SDPCoordinates.lift z := by
  simp only [lift, collect_value]
  ext i j
  by_cases h : i=j <;> simp [h, SDPCoordinates.lift, Arithmetic.add, Arithmetic.div]

lemma lift_steps {n : ℕ} (z : Space n) : (lift z).steps ≤ 3*n^2+n := by
  apply (collect_steps_le (c := n*(2+1)) _ (fun i => collect_steps_le (c := 2) _ (fun j => ?_))).trans ?_
  · dsimp; nlinarith
  · split <;> simp [Arithmetic.add, Arithmetic.div]

def project {n : ℕ} (A : Mat n) : Arithmetic (Mat n) :=
  collect fun i => collect fun j =>
    if i=j then Arithmetic.pure 0 else do
      let a ← Arithmetic.add (A i j) (A j i)
      Arithmetic.div a 2

lemma project_value {n : ℕ} (A : Mat n) : (project A).value = SDPCoordinates.project A := by
  simp only [project, collect_value]
  ext i j
  by_cases h : i=j <;> simp [h, SDPCoordinates.project, Arithmetic.add, Arithmetic.div]

lemma project_steps {n : ℕ} (A : Mat n) : (project A).steps ≤ 3*n^2+n := by
  apply (collect_steps_le (c := n*(2+1)) _ (fun i => collect_steps_le (c := 2) _ (fun j => ?_))).trans ?_
  · dsimp; nlinarith
  · split <;> simp [Arithmetic.add, Arithmetic.div]

def normal {n : ℕ} (A : Mat n) : Arithmetic (Space n) := do
  let P ← project A
  Arithmetic.pure (flatten n P)

lemma normal_value {n : ℕ} (A : Mat n) : (normal A).value = SDPCoordinates.normal n A := by
  simp only [normal, monad_bind_value, pure_value, project_value, normal_formula]

lemma normal_steps {n : ℕ} (A : Mat n) : (normal A).steps ≤ 3*n^2+n := by
  simpa [normal] using project_steps A

end Counted
end DPCut.SDPCoordinates
