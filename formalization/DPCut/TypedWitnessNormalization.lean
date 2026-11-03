import DPCut.TypedWitnessTerms

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace DPCut.TypedMachine

theorem maximumFold_le {ι : Type*} (values : ι → ℝ) (indices : List ι) (initial bound : ℝ)
    (hi : initial ≤ bound) (hv : ∀ i ∈ indices, values i ≤ bound) :
    indices.foldl (fun old i => max old (values i)) initial ≤ bound := by
  induction indices generalizing initial with
  | nil => exact hi
  | cons i indices ih =>
      exact ih _ (max_le hi (hv i (by simp))) (fun j hj => hv j (by simp [hj]))

theorem initial_le_maximumFold {ι : Type*} (values : ι → ℝ) (indices : List ι) (initial : ℝ) :
    initial ≤ indices.foldl (fun old i => max old (values i)) initial := by
  induction indices generalizing initial with
  | nil => exact le_refl _
  | cons i indices ih => exact (le_max_left _ _).trans (ih _)

theorem member_le_maximumFold {ι : Type*} (values : ι → ℝ) (indices : List ι) (initial : ℝ)
    (i : ι) (hi : i ∈ indices) :
    values i ≤ indices.foldl (fun old j => max old (values j)) initial := by
  induction indices generalizing initial with
  | nil => cases hi
  | cons j indices ih =>
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact (le_max_right _ _).trans (initial_le_maximumFold values indices _)
      · exact ih _ hi

@[simp] theorem eval_activeMaximumTerm {Γ : List ValueType} {n : ℕ}
    (r g : Term Γ (weightType n)) (s : Environment Γ) :
    (activeMaximumTerm r g).eval s =
      activeMaximum (decodeWeights (r.eval s)) (decodeWeights (g.eval s)) := by
  let R := decodeWeights (r.eval s)
  let G := decodeWeights (g.eval s)
  let values : Fin (Fintype.card (Edge n)) → ℝ := fun i =>
    if 0 < R ((Fintype.equivFin (Edge n)).symm i) then G ((Fintype.equivFin (Edge n)).symm i) else 0
  have heval : (activeMaximumTerm r g).eval s =
      (List.finRange (Fintype.card (Edge n))).foldl (fun old i => max old (values i)) 0 := by
    simp [activeMaximumTerm, Term.eval, Comparison.real, weightTerms, R, G, values,
      decodeWeights, RealBinary.eval]
  rw [heval]
  apply le_antisymm
  · apply maximumFold_le
    · exact activeMaximum_nonneg R G
    · intro i _
      unfold values
      split
      · exact le_activeMaximum R G _ ‹_›
      · exact activeMaximum_nonneg R G
  · apply activeMaximum_le R G
    · exact initial_le_maximumFold values _ 0
    · intro e he
      have h := member_le_maximumFold values (List.finRange _) 0 (Fintype.equivFin (Edge n) e) (by simp)
      simpa [values, he] using h

@[simp] theorem eval_normalizeTerm {Γ : List ValueType} {n : ℕ}
    (r g : Term Γ (weightType n)) (s : Environment Γ) :
    decodeWeights ((normalizeTerm r g (activeMaximumTerm r g)).eval s) =
      normalizeWitness (decodeWeights (r.eval s)) (decodeWeights (g.eval s)) := by
  rw [normalizeTerm, eval_weightTerms]
  funext e
  simp [Term.eval, RealBinary.eval, normalizeWitness]

theorem l1_zero_iff {n : ℕ} (r : Weights n) : l1 r = 0 ↔ r = 0 := by
  constructor
  · intro h
    funext e
    apply abs_eq_zero.mp
    apply le_antisymm
    · have hterm : |r e| ≤ l1 r :=
        Finset.single_le_sum (fun e _ => abs_nonneg (r e)) (Finset.mem_univ e)
      simpa only [h] using hterm
    · exact abs_nonneg _
  · intro h
    simp [h, l1]

@[simp] theorem eval_allZero {Γ : List ValueType} {n : ℕ}
    (r : Term Γ (weightType n)) (s : Environment Γ) :
    (allZero r).eval s = decide (decodeWeights (r.eval s) = 0) := by
  norm_num only [allZero, Term.eval, Comparison.real]
  simp only [eval_l1Term, l1_zero_iff]

end DPCut.TypedMachine
