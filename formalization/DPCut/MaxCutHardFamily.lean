import DPCut.EmbeddedGraphs
import DPCut.CCOptimization
import DPCut.CutReconstruction

/-! The eight-vertex block family for Remark 33. Finite enumeration below is
checked by Lean's kernel (`decide`), not a native evaluation axiom. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace DPCut

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma eight_cut_card_bound : ∀ x : Fin 8 → Bool,
    (Finset.univ.filter (fun e : Edge 8 => x e.val.1 ≠ x e.val.2)).card ≤ 16 := by
  decide

lemma eight_edge_card : Fintype.card (Edge 8) = 28 := by decide

def blockVertex {n : ℕ} (i : Fin (n / 8)) (v : Fin 8) : Fin n :=
  ⟨(i : ℕ) * 8 + v, by have := Nat.div_mul_le_self n 8; omega⟩

def blockEdge {n : ℕ} (i : Fin (n / 8)) (e : Edge 8) : Edge n :=
  ⟨(blockVertex i e.val.1, blockVertex i e.val.2), by
    change (i : ℕ) * 8 + e.val.1 < (i : ℕ) * 8 + e.val.2
    have := e.property
    omega⟩

lemma blockVertex_injective {n : ℕ} :
    Function.Injective (fun iv : Fin (n / 8) × Fin 8 => blockVertex iv.1 iv.2) := by
  intro x y h
  have hh := congrArg Fin.val h
  change (x.1 : ℕ) * 8 + x.2 = (y.1 : ℕ) * 8 + y.2 at hh
  have hi : x.1 = y.1 := Fin.ext (by omega)
  have hv : x.2 = y.2 := Fin.ext (by omega)
  exact Prod.ext hi hv

lemma blockEdge_injective {n : ℕ} :
    Function.Injective (fun ie : Fin (n / 8) × Edge 8 => blockEdge ie.1 ie.2) := by
  intro x y h
  have hv := congrArg Subtype.val h
  have h₁ := @blockVertex_injective n (x.1, x.2.val.1) (y.1, y.2.val.1) (congrArg Prod.fst hv)
  have h₂ := @blockVertex_injective n (x.1, x.2.val.2) (y.1, y.2.val.2) (congrArg Prod.snd hv)
  have hi := congrArg Prod.fst h₁
  have ha : x.2.val.1 = y.2.val.1 := congrArg (fun v : Fin (n / 8) × Fin 8 => v.2) h₁
  have hb : x.2.val.2 = y.2.val.2 := congrArg (fun v : Fin (n / 8) × Fin 8 => v.2) h₂
  have he : x.2 = y.2 := Subtype.ext (Prod.ext ha hb)
  exact Prod.ext hi he

lemma selectedBlockEdge_injective {n : ℕ} (x : Fin (n / 8) → Edge 8) :
    Function.Injective (fun i => blockEdge i (x i)) := by
  intro i j h
  exact congrArg Prod.fst (@blockEdge_injective n (i, x i) (j, x j) h)

lemma embedWeights_unweighted {n : ℕ} {ι : Type*} [Fintype ι]
    (e : ι → Edge n) (he : Function.Injective e) (a : ι → ℝ)
    (ha : ∀ i, a i = 0 ∨ a i = 1) : IsUnweighted (embedWeights e a) := by
  classical
  intro f
  by_cases hex : ∃ i, e i = f
  · obtain ⟨i, rfl⟩ := hex
    have hv : embedWeights e a (e i) = a i := by
      unfold embedWeights
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        exact if_neg (fun h => hj (he h))
      · simp
    simpa only [hv] using ha i
  · left
    apply Finset.sum_eq_zero
    intro i _
    exact if_neg (fun h => hex ⟨i, h⟩)

def blockGraph {n : ℕ} (x : Fin (n / 8) → Edge 8) : Weights n :=
  embedWeights (fun i => blockEdge i (x i)) (fun _ => 1)

def deletedBlockGraph {n : ℕ} (x : Fin (n / 8) → Edge 8) (i : Fin (n / 8)) : Weights n :=
  embedWeights (fun j => blockEdge j (x j)) (fun j => if j = i then 0 else 1)

lemma blockGraph_unweighted {n : ℕ} (x : Fin (n / 8) → Edge 8) : IsUnweighted (blockGraph x) :=
  embedWeights_unweighted _ (selectedBlockEdge_injective x) _ (fun _ => Or.inr rfl)

lemma deletedBlockGraph_unweighted {n : ℕ} (x : Fin (n / 8) → Edge 8) (i : Fin (n / 8)) :
    IsUnweighted (deletedBlockGraph x i) :=
  embedWeights_unweighted _ (selectedBlockEdge_injective x) _ (fun j => by split <;> simp)

lemma deletedBlockGraph_update {n : ℕ} (x : Fin (n / 8) → Edge 8) (i : Fin (n / 8)) (e : Edge 8) :
    deletedBlockGraph (Function.update x i e) i = deletedBlockGraph x i := by
  classical
  funext f
  unfold deletedBlockGraph embedWeights
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = i
  · subst j
    simp [Function.update_self]
  · simp [hj]

lemma blockGraph_adjacent_deleted {n : ℕ} (x : Fin (n / 8) → Edge 8) (i : Fin (n / 8)) :
    Adjacent (deletedBlockGraph x i) (blockGraph x) := by
  unfold Adjacent deletedBlockGraph blockGraph
  rw [embedWeights_sub]
  apply (l1_embedWeights_le _ _).trans
  have heq : (∑ j : Fin (n / 8), |(if j = i then (0 : ℝ) else 1) - 1|) = 1 := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  simpa only [Pi.sub_apply] using heq.le

lemma cut_blockGraph {n : ℕ} (x : Fin (n / 8) → Edge 8) (S : Finset (Fin n)) :
    cut (blockGraph x) S = ∑ i, cutQuery S (blockEdge i (x i)) := by
  simpa only [one_mul] using pairing_embedWeights (fun i => blockEdge i (x i)) (fun _ => 1) (cutQuery S)

lemma mass_blockGraph {n : ℕ} (x : Fin (n / 8) → Edge 8) : mass (blockGraph x) = (n / 8 : ℕ) := by
  have h := pairing_embedWeights (fun i => blockEdge i (x i)) (fun _ : Fin (n / 8) => (1 : ℝ)) (fun _ => 1)
  simpa [pairing, mass, blockGraph] using h

lemma blockGraph_optimum {n : ℕ} (x : Fin (n / 8) → Edge 8) :
    sSup (Set.range (cut (blockGraph x))) = (n / 8 : ℕ) := by
  let S := Finset.univ.image (fun i => blockVertex i (x i).val.1)
  have hcut : cut (blockGraph x) S = (n / 8 : ℕ) := by
    rw [cut_blockGraph]
    have hcross (i : Fin (n / 8)) : cutQuery S (blockEdge i (x i)) = 1 := by
      have hleft : blockVertex i (x i).val.1 ∈ S := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      have hright : blockVertex i (x i).val.2 ∉ S := by
        intro h
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
        have hv := @blockVertex_injective n (j, (x j).val.1) (i, (x i).val.2) hj
        have hi : j = i := congrArg Prod.fst hv
        have he : (x j).val.1 = (x i).val.2 := congrArg Prod.snd hv
        subst j
        exact (ne_of_lt (x i).property) he
      simp [cutQuery, blockEdge, hleft, hright]
    simp [hcross]
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨T, rfl⟩
    exact (cut_le_mass (fun e => ((blockGraph_unweighted x).bounded e).1) T).trans_eq (mass_blockGraph x)
  · rw [← hcut]
    exact le_csSup (Set.finite_range (cut (blockGraph x))).bddAbove ⟨S, rfl⟩

lemma sum_block_cutQuery_le {n : ℕ} (i : Fin (n / 8)) (S : Finset (Fin n)) :
    (∑ e : Edge 8, cutQuery S (blockEdge i e)) ≤ 16 := by
  let x : Fin 8 → Bool := fun v => decide (blockVertex i v ∈ S)
  have h := eight_cut_card_bound x
  have heq : (∑ e : Edge 8, cutQuery S (blockEdge i e)) =
      ((Finset.univ.filter (fun e : Edge 8 => x e.val.1 ≠ x e.val.2)).card : ℝ) := by
    rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro e _
    by_cases ha : blockVertex i e.val.1 ∈ S <;> by_cases hb : blockVertex i e.val.2 ∈ S <;>
      simp [cutQuery, blockEdge, x, ha, hb]
  rw [heq]
  exact_mod_cast h

end DPCut
