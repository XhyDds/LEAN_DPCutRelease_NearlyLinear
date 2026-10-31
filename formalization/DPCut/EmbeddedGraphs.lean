import DPCut.FiniteReconstruction

/-! Weighted bit families embedded in the project's unordered-edge representation. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DPCut

def embedWeights {n : ℕ} {ι : Type*} [Fintype ι] (e : ι → Edge n) (a : ι → ℝ) : Weights n :=
  fun f => ∑ i, if e i = f then a i else 0

lemma pairing_embedWeights {n : ℕ} {ι : Type*} [Fintype ι]
    (e : ι → Edge n) (a : ι → ℝ) (q : Weights n) :
    pairing (embedWeights e a) q = ∑ i, a i * q (e i) := by
  classical
  simp only [pairing, embedWeights, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [ite_mul]

lemma embedWeights_sub {n : ℕ} {ι : Type*} [Fintype ι]
    (e : ι → Edge n) (a b : ι → ℝ) :
    embedWeights e a - embedWeights e b = embedWeights e (a - b) := by
  ext f
  simp only [embedWeights, Pi.sub_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _; split <;> simp

lemma l1_embedWeights_le {n : ℕ} {ι : Type*} [Fintype ι]
    (e : ι → Edge n) (a : ι → ℝ) : l1 (embedWeights e a) ≤ ∑ i, |a i| := by
  classical
  unfold l1 embedWeights
  calc
    _ ≤ ∑ f, ∑ i, |if e i = f then a i else 0| :=
      Finset.sum_le_sum fun f _ => Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      simp only [apply_ite abs, abs_zero]
      rw [Finset.sum_comm]
      simp

def bitGraph {n : ℕ} {ι : Type*} [Fintype ι] (e : ι → Edge n) (t : ℝ)
    (x : ι → Bool) : Weights n := embedWeights e (fun i => if x i then t else 0)

lemma bitGraph_nonnegative {n : ℕ} {ι : Type*} [Fintype ι] (e : ι → Edge n)
    {t : ℝ} (ht : 0 ≤ t) (x : ι → Bool) : Nonnegative (bitGraph e t x) := by
  intro f
  apply Finset.sum_nonneg
  intro i _; dsimp [bitGraph, embedWeights]; split <;> positivity

lemma mass_bitGraph_le {n : ℕ} {ι : Type*} [Fintype ι] (e : ι → Edge n)
    {t : ℝ} (ht : 0 ≤ t) (x : ι → Bool) : mass (bitGraph e t x) ≤ t * Fintype.card ι := by
  have he : mass (bitGraph e t x) = ∑ i, if x i then t else 0 := by
    simpa [mass, pairing, bitGraph] using pairing_embedWeights e (fun i => if x i then t else 0) (fun _ => 1)
  rw [he]
  calc
    _ ≤ ∑ _i : ι, t := Finset.sum_le_sum fun i _ => by split <;> simp [ht]
    _ = _ := by simp [mul_comm]

lemma bitGraph_flip_distance {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → Edge n) {t : ℝ} (ht : 0 ≤ t) (x : ι → Bool) (i : ι) :
    l1 (bitGraph e t x - bitGraph e t (bitFlip i x)) ≤ t := by
  unfold bitGraph
  rw [embedWeights_sub]
  apply (l1_embedWeights_le _ _).trans
  have he : (∑ j : ι, |((fun j => if x j then t else 0) -
      (fun j => if bitFlip i x j then t else 0)) j|) = t := by
    rw [Finset.sum_eq_single i]
    · cases h : x i <;> simp [bitFlip, h, abs_of_nonneg ht]
    · intro j _ hj
      simp [bitFlip, Function.update_of_ne hj]
    · simp
  exact he.le

/-- Vertex labels 0,...,r-1 on the left and r,...,r+d-1 on the right. -/
def bipartiteLeft {n r d : ℕ} (h : r + d ≤ n) (i : Fin r) : Fin n :=
  ⟨i, by omega⟩
def bipartiteRight {n r d : ℕ} (h : r + d ≤ n) (j : Fin d) : Fin n :=
  ⟨r + j, by omega⟩
def bipartiteEdge {n r d : ℕ} (h : r + d ≤ n) (ij : Fin r × Fin d) : Edge n :=
  ⟨(bipartiteLeft h ij.1, bipartiteRight h ij.2), by
    change (ij.1 : ℕ) < r + ij.2
    omega⟩

lemma bipartiteLeft_injective {n r d : ℕ} (h : r + d ≤ n) :
    Function.Injective (bipartiteLeft h) := fun _ _ he => Fin.ext (congrArg (Fin.val (n := n)) he)
lemma bipartiteRight_injective {n r d : ℕ} (h : r + d ≤ n) :
    Function.Injective (bipartiteRight h) := by
  intro i j he
  apply Fin.ext
  have hh := congrArg Fin.val he
  simp only [bipartiteRight] at hh
  omega
lemma bipartiteLeft_ne_right {n r d : ℕ} (h : r + d ≤ n) (i : Fin r) (j : Fin d) :
    bipartiteLeft h i ≠ bipartiteRight h j := by
  intro he
  have hh := congrArg Fin.val he
  simp only [bipartiteLeft, bipartiteRight] at hh
  omega

end DPCut
