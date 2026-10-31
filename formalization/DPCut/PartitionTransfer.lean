import DPCut.Applications
import DPCut.CubeMoments
import DPCut.FiniteReconstruction

/-! Appendix C: random block coloring transfers all cuts to all partitions. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DPCut

def labelQuery {n : ℕ} {ι : Type*} [DecidableEq ι] (π : Fin n → ι) : Weights n :=
  fun e => if π e.val.1 = π e.val.2 then 0 else 1
def labelCut {n : ℕ} {ι : Type*} [DecidableEq ι] (w : Weights n) (π : Fin n → ι) : ℝ :=
  pairing w (labelQuery π)
def blockCut {n : ℕ} {ι : Type*} (π : Fin n → ι) (x : ι → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun v => x (π v) = true)

lemma expect_blockCut_query {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (π : Fin n → ι) (e : Edge n) :
    (𝔼 x, cutQuery (blockCut π x) e) = labelQuery π e / 2 := by
  classical
  by_cases he : π e.val.1 = π e.val.2
  · simp [cutQuery, blockCut, labelQuery, he]
  · have hflip (x : ι → Bool) : cutQuery (blockCut π (bitFlip (π e.val.1) x)) e =
        1 - cutQuery (blockCut π x) e := by
      simp only [cutQuery, blockCut, Finset.mem_filter, Finset.mem_univ, true_and,
        bitFlip, Function.update_self, Function.update_of_ne (Ne.symm he)]
      cases x (π e.val.1) <;> cases x (π e.val.2) <;> norm_num
    have hh := Fintype.expect_bijective (bitFlip (π e.val.1))
      (bitFlip_involutive _).bijective
      (fun x => 1 - cutQuery (blockCut π x) e) (fun x => cutQuery (blockCut π x) e)
      (fun x => (hflip x).symm)
    rw [Finset.expect_sub_distrib, Fintype.expect_const] at hh
    simp only [labelQuery, he, ↓reduceIte]
    linarith

lemma expect_blockCut {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : Weights n) (π : Fin n → ι) :
    (𝔼 x, cut w (blockCut π x)) = labelCut w π / 2 := by
  simp only [cut, pairing, labelCut]
  rw [Finset.expect_sum_comm]
  simp only [← Finset.mul_expect, expect_blockCut_query]
  change (∑ e, w e * (labelQuery π e / 2)) = _
  simp only [← mul_div_assoc, ← Finset.sum_div]

theorem label_cut_transfer {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {w h : Weights n} {γ A : ℝ} (hc : AllCuts w h γ A) (π : Fin n → ι) :
    |labelCut h π - labelCut w π| ≤ γ * labelCut w π + 2 * A := by
  have hu := Finset.expect_le_expect (s := Finset.univ)
    (fun x _ => (abs_le.mp (hc (blockCut π x))).2)
  have hl := Finset.expect_le_expect (s := Finset.univ)
    (fun x _ => (abs_le.mp (hc (blockCut π x))).1)
  simp only [Finset.expect_sub_distrib, Finset.expect_add_distrib,
    Finset.expect_neg_distrib, ← Finset.mul_expect, Fintype.expect_const,
    expect_blockCut] at hu hl
  rw [abs_le]
  constructor <;> linarith

theorem partition_transfer : PartitionTransferStatement := by
  intro n w h γ A _ _ _ _ hc π
  exact label_cut_transfer hc π

lemma labelCut_nonneg {n : ℕ} {ι : Type*} [DecidableEq ι] {w : Weights n}
    (hw : Nonnegative w) (π : Fin n → ι) : 0 ≤ labelCut w π := by
  apply Finset.sum_nonneg
  intro e _
  exact mul_nonneg (hw e) (by unfold labelQuery; split <;> norm_num)

lemma labelCut_le_mass {n : ℕ} {ι : Type*} [DecidableEq ι] {w : Weights n}
    (hw : Nonnegative w) (π : Fin n → ι) : labelCut w π ≤ mass w := by
  apply Finset.sum_le_sum
  intro e _
  exact mul_le_of_le_one_right (hw e) (by unfold labelQuery; split <;> norm_num)

end DPCut
