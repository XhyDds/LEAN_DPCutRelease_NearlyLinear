import DPCut.EmbeddedGraphs
import DPCut.CutDiscrepancy
import DPCut.BipartiteDiscrepancy

/-! Cuts and rectangle discrepancy of the embedded bipartite hard family. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DPCut

lemma between_embedWeights {n : ℕ} {ι : Type*} [Fintype ι]
    (e : ι → Edge n) (a : ι → ℝ) (S T : Finset (Fin n)) :
    between (embedWeights e a) S T = ∑ i,
      if ((e i).val.1 ∈ S ∧ (e i).val.2 ∈ T) ∨ ((e i).val.2 ∈ S ∧ (e i).val.1 ∈ T)
      then a i else 0 := by
  classical
  have hh := pairing_embedWeights e a (fun f =>
    if (f.val.1 ∈ S ∧ f.val.2 ∈ T) ∨ (f.val.2 ∈ S ∧ f.val.1 ∈ T) then 1 else 0)
  simpa only [pairing, mul_ite, mul_one, mul_zero] using hh

@[simp] lemma left_mem_left {n r d : ℕ} (h : r + d ≤ n) (i : Fin r) (S : Finset (Fin r)) :
    bipartiteLeft h i ∈ S.image (bipartiteLeft h) ↔ i ∈ S := by
  simp [(bipartiteLeft_injective h).mem_finset_image]

@[simp] lemma right_mem_right {n r d : ℕ} (h : r + d ≤ n) (j : Fin d) (T : Finset (Fin d)) :
    bipartiteRight h j ∈ T.image (bipartiteRight h) ↔ j ∈ T := by
  simp [(bipartiteRight_injective h).mem_finset_image]

@[simp] lemma left_not_mem_right {n r d : ℕ} (h : r + d ≤ n) (i : Fin r) (T : Finset (Fin d)) :
    bipartiteLeft h i ∉ T.image (bipartiteRight h) := by
  rintro hx
  obtain ⟨j, _, he⟩ := Finset.mem_image.mp hx
  exact bipartiteLeft_ne_right h i j he.symm

@[simp] lemma right_not_mem_left {n r d : ℕ} (h : r + d ≤ n) (j : Fin d) (S : Finset (Fin r)) :
    bipartiteRight h j ∉ S.image (bipartiteLeft h) := by
  rintro hx
  obtain ⟨i, _, he⟩ := Finset.mem_image.mp hx
  exact bipartiteLeft_ne_right h i j he

lemma bipartite_disjoint {n r d : ℕ} (h : r + d ≤ n) (S : Finset (Fin r)) (T : Finset (Fin d)) :
    Disjoint (S.image (bipartiteLeft h)) (T.image (bipartiteRight h)) := by
  apply Finset.disjoint_left.mpr
  intro v hv hv'
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
  exact left_not_mem_right h i T hv'

lemma between_bipartite {n r d : ℕ} (h : r + d ≤ n) (a : (Fin r × Fin d) → ℝ)
    (S : Finset (Fin r)) (T : Finset (Fin d)) :
    between (embedWeights (bipartiteEdge h) a)
      (S.image (bipartiteLeft h)) (T.image (bipartiteRight h)) = ∑ i ∈ S, ∑ j ∈ T, a (i,j) := by
  classical
  rw [between_embedWeights]
  simp only [bipartiteEdge, left_mem_left, right_mem_right, right_not_mem_left,
    left_not_mem_right, false_and, or_false, Fintype.sum_prod_type]
  simp only [ite_and]
  change (∑ i : Fin r, ∑ j : Fin d, if i ∈ S then if j ∈ T then a (i,j) else 0 else 0) = _
  simp_rw [Finset.sum_ite_irrel]
  simp [Finset.sum_ite_mem]

lemma cut_bipartite_left {n r d : ℕ} (h : r + d ≤ n) (a : (Fin r × Fin d) → ℝ)
    (S : Finset (Fin r)) :
    cut (embedWeights (bipartiteEdge h) a) (S.image (bipartiteLeft h)) =
      ∑ i ∈ S, ∑ j, a (i,j) := by
  classical
  rw [cut, pairing_embedWeights]
  simp only [cutQuery, bipartiteEdge, left_mem_left, right_not_mem_left,
    iff_false, ite_not, mul_ite, mul_one, mul_zero, Fintype.sum_prod_type]
  change (∑ i : Fin r, ∑ j : Fin d, if i ∈ S then a (i,j) else 0) = _
  simp_rw [Finset.sum_ite_irrel]
  simp [Finset.sum_ite_mem]

/-- Compatibility converts the moment estimate into a Hamming-distance bound. -/
lemma bipartite_compatible_distance {n r d : ℕ} (h : r + d ≤ n) (hd : 0 < d)
    {t γ A : ℝ} (ht : 0 < t) (hγ : 0 ≤ γ)
    (x y : (Fin r × Fin d) → Bool) {H : Weights n}
    (hx : AllCuts (bitGraph (bipartiteEdge h) t x) H γ A)
    (hy : AllCuts (bitGraph (bipartiteEdge h) t y) H γ A) :
    t * hamming x y ≤ 192 * Real.sqrt d * (γ * t * (r * d) + A) := by
  classical
  let B : Fin r → Fin d → ℝ := fun i j => (if x (i,j) then 1 else 0) - (if y (i,j) then 1 else 0)
  have hB (i : Fin r) (j : Fin d) : B i j ^ 2 ≤ 1 := by
    dsimp [B]; cases x (i,j) <;> cases y (i,j) <;> norm_num
  have hdist : (∑ i, ∑ j, B i j ^ 2) = hamming x y := by
    simp only [hamming, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _; apply Finset.sum_congr rfl
    intro j _; dsimp [B]; cases x (i,j) <;> cases y (i,j) <;> norm_num
  have hrect (S : Finset (Fin r)) (T : Finset (Fin d)) :
      |∑ i ∈ S, ∑ j ∈ T, B i j| ≤ 3 * (γ * t * (r * d) + A) / t := by
    have heq : bitGraph (bipartiteEdge h) t x - bitGraph (bipartiteEdge h) t y =
        embedWeights (bipartiteEdge h) (fun ij => t * B ij.1 ij.2) := by
      rw [bitGraph, bitGraph, embedWeights_sub]
      congr 1; ext ij
      dsimp [B]; cases x ij <;> cases y ij <;> simp
    have hh := compatible_between_bound (bitGraph_nonnegative _ ht.le x)
      (bitGraph_nonnegative _ ht.le y) hγ hx hy (bipartite_disjoint h S T)
    rw [← between_sub, heq, between_bipartite] at hh
    simp_rw [← Finset.mul_sum] at hh
    rw [abs_mul, abs_of_pos ht] at hh
    have hxM := mass_bitGraph_le (bipartiteEdge h) ht.le x
    have hyM := mass_bitGraph_le (bipartiteEdge h) ht.le y
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] at hxM hyM
    apply (le_div_iff₀ ht).2
    have hu := mul_le_mul_of_nonneg_left (add_le_add hxM hyM) (by positivity : 0 ≤ 3 / 2 * γ)
    nlinarith
  have hh := bipartite_discrepancy hd B hB hrect
  rw [hdist] at hh
  have hm := mul_le_mul_of_nonneg_left hh ht.le
  have he : t * (64 * Real.sqrt (d : ℝ) * (3 * (γ * t * (r * d) + A) / t)) =
      192 * Real.sqrt d * (γ * t * (r * d) + A) := by field_simp; ring
  rwa [he] at hm

end DPCut
