import DPCut.KLSum

/-! Reindexing finite edge vectors for the finite-simplex KL lemmas. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DPCut

def weightsVector {n : ℕ} (w : Weights n) : Fin (Fintype.card (Edge n)) → ℝ :=
  fun i => w ((Fintype.equivFin (Edge n)).symm i)

def vectorEdges {n : ℕ} (p : Fin (Fintype.card (Edge n)) → ℝ) : Weights n :=
  fun e => p (Fintype.equivFin (Edge n) e)

@[simp] lemma weightsVector_vectorEdges {n : ℕ} (p : Fin (Fintype.card (Edge n)) → ℝ) :
    weightsVector (vectorEdges p) = p := by ext i; simp [weightsVector, vectorEdges]

@[simp] lemma vectorEdges_weightsVector {n : ℕ} (w : Weights n) : vectorEdges (weightsVector w) = w := by
  ext e; simp [weightsVector, vectorEdges]

lemma sum_weightsVector {n : ℕ} (w : Weights n) : ∑ i, weightsVector w i = mass w := by
  exact Fintype.sum_bijective (Fintype.equivFin (Edge n)).symm
    (Fintype.equivFin (Edge n)).symm.bijective (weightsVector w) w (fun _ => rfl)

lemma mass_vectorEdges {n : ℕ} (p : Fin (Fintype.card (Edge n)) → ℝ) :
    mass (vectorEdges p) = ∑ i, p i := by
  rw [← sum_weightsVector, weightsVector_vectorEdges]

lemma weightsVector_distribution {n : ℕ} {w : Weights n} {M : ℝ}
    (hw : Nonnegative w) (hM : 0 < M) (hm : mass w = M) :
    IsDistribution (weightsVector (fun e => w e / M)) := by
  refine ⟨fun i => div_nonneg (hw _) hM.le, ?_⟩
  rw [sum_weightsVector]
  change (∑ e, w e / M) = 1
  rw [← Finset.sum_div]
  change mass w / M = 1
  rw [hm, div_self hM.ne']

lemma potential_eq_vector_klSum {n : ℕ} {w h : Weights n} {M H : ℝ}
    (hw : Nonnegative w) (hh : Nonnegative h) (hM : 0 < M) (hH : 0 < H)
    (hmw : mass w = M) (hmh : mass h = H) (hs : ∀ e, 0 < w e → 0 < h e) :
    potential w h M H = M * klSum (weightsVector (fun e => w e / M)) (weightsVector (fun e => h e / H)) := by
  rw [(normalizedKL_finite_formula hw hh hM hH hmw hmh hs).2]
  have he : klSum (weightsVector (fun e => w e / M)) (weightsVector (fun e => h e / H)) =
      mass (fun e => (w e / M) * (Real.log (w e / M) - Real.log (h e / H))) := by
    simpa only [klSum, weightsVector] using sum_weightsVector
      (fun e => (w e / M) * (Real.log (w e / M) - Real.log (h e / H)))
  rw [he, mass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hz : w e = 0
  · simp [hz]
  · have hp : 0 < w e := lt_of_le_of_ne (hw e) (Ne.symm hz)
    rw [Real.log_div (div_pos hp hM).ne' (div_pos (hs e hp) hH).ne']
    field_simp

lemma measurable_weightsVector {n : ℕ} : Measurable (weightsVector (n := n)) := by
  unfold weightsVector; fun_prop

lemma measurable_vectorEdges {n : ℕ} : Measurable (vectorEdges (n := n)) := by
  unfold vectorEdges; fun_prop

end DPCut
