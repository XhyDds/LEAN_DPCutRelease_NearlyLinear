import DPCut.CubeMoments
import DPCut.CutBasics
import DPCut.LowerGroupPrivacy

/-! Measurable finite decoding and the elementary DP reconstruction lower bound. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace DPCut

lemma exists_measurable_finite_decoder {Ω ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace ι] [Fintype ι] [Nonempty ι]
    (P : ι → Ω → Prop) (hP : ∀ i, MeasurableSet {x | P i x}) :
    ∃ f : Ω → ι, Measurable f ∧ ∀ x, (∃ i, P i x) → P (f x) x := by
  classical
  have aux (s : Finset ι) : ∃ f : Ω → ι, Measurable f ∧
      ∀ x, (∃ i ∈ s, P i x) → P (f x) x := by
    induction s using Finset.induction_on with
    | empty => exact ⟨fun _ => Classical.arbitrary ι, measurable_const, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨f, hf, hp⟩ := ih
      refine ⟨fun x => if P i x then i else f x, Measurable.ite (hP i) measurable_const hf, ?_⟩
      intro x hx
      dsimp only
      split_ifs with h
      · exact h
      · apply hp x
        simpa [h] using hx
  simpa using aux Finset.univ

def bitFlip {ι : Type*} [DecidableEq ι] (i : ι) (x : ι → Bool) : ι → Bool :=
  Function.update x i (!(x i))

lemma bitFlip_involutive {ι : Type*} [DecidableEq ι] (i : ι) :
    Function.Involutive (bitFlip i) := by
  intro x
  ext j
  by_cases h : j = i <;> simp [bitFlip, h]

def hamming {ι : Type*} [Fintype ι] (x y : ι → Bool) : ℝ :=
  ∑ i, if x i = y i then 0 else 1

lemma hamming_nonneg {ι : Type*} [Fintype ι] (x y : ι → Bool) : 0 ≤ hamming x y := by
  apply Finset.sum_nonneg; intro i _; split <;> norm_num

lemma hamming_le_card {ι : Type*} [Fintype ι] (x y : ι → Bool) :
    hamming x y ≤ Fintype.card ι := by
  calc
    _ ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun _ _ => by split <;> norm_num
    _ = _ := by simp

/-- A finite, purely algebraic reconstruction bound. The 3 and 3/100 budgets
come from group privacy, not an assumption about pure privacy. -/
lemma finite_reconstruction {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (p : (ι → Bool) → (ι → Bool) → ℝ)
    (hp : ∀ x y, 0 ≤ p x y) (hsum : ∀ x, ∑ y, p x y = 1)
    (hdp : ∀ x i, (∑ y, if y i = x i then p x y else 0) ≤
      3 * (∑ y, if y i = x i then p (bitFlip i x) y else 0) + 3 / 100)
    (R : (ι → Bool) → (ι → Bool) → Prop) [DecidableRel R]
    (hgood : ∀ x, (∑ y, if R x y then 0 else p x y) ≤ 1 / 40) :
    ∃ x y, R x y ∧ (Fintype.card ι : ℝ) / 5 ≤ hamming x y := by
  classical
  let err : (ι → Bool) → ι → ℝ := fun x i => ∑ y, if y i = x i then 0 else p x y
  have hsplit (x : ι → Bool) (i : ι) :
      (∑ y, if y i = x i then p x y else 0) = 1 - err x i := by
    have h := hsum x
    have he : (∑ y, if y i = x i then p x y else 0) + err x i = ∑ y, p x y := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro y _; dsimp; split <;> simp
    linarith
  have hflip (x : ι → Bool) (i : ι) :
      (∑ y, if y i = x i then p (bitFlip i x) y else 0) = err (bitFlip i x) i := by
    apply Finset.sum_congr rfl
    intro y _
    simp only [bitFlip, Function.update_self]
    cases x i <;> cases y i <;> simp
  have hpair (x : ι → Bool) (i : ι) : 97 / 100 ≤ err x i + 3 * err (bitFlip i x) i := by
    have h := hdp x i
    rw [hsplit, hflip] at h
    linarith
  have hcoord (i : ι) : 97 / 400 ≤ 𝔼 x, err x i := by
    have h := Finset.le_expect Finset.univ_nonempty (fun x _ => hpair x i)
    rw [Finset.expect_add_distrib, ← Finset.mul_expect] at h
    have he := Fintype.expect_bijective (bitFlip i) (bitFlip_involutive i).bijective
      (fun x => err (bitFlip i x) i) (fun x => err x i) (fun _ => rfl)
    rw [he] at h
    linarith
  have hm (x : ι → Bool) : (∑ y, p x y * hamming x y) = ∑ i, err x i := by
    simp only [hamming, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro y _
    dsimp only [err]
    by_cases h : x i = y i <;> simp [h, eq_comm]
  have hlower : 97 / 400 * (Fintype.card ι : ℝ) ≤ 𝔼 x, ∑ y, p x y * hamming x y := by
    simp_rw [hm]
    rw [Finset.expect_sum_comm]
    simpa [mul_comm] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcoord i)
  by_contra! hn
  have hu (x : ι → Bool) : (∑ y, p x y * hamming x y) ≤
      (Fintype.card ι : ℝ) / 5 + (Fintype.card ι : ℝ) / 40 := by
    have hpoint (y : ι → Bool) : p x y * hamming x y ≤
        p x y * ((Fintype.card ι : ℝ) / 5) +
          (Fintype.card ι : ℝ) * (if R x y then 0 else p x y) := by
      by_cases h : R x y
      · simp only [h, ↓reduceIte, mul_zero, add_zero]
        exact mul_le_mul_of_nonneg_left (hn x y h).le (hp x y)
      · simp only [h, ↓reduceIte]
        have hh := mul_le_mul_of_nonneg_left (hamming_le_card x y) (hp x y)
        nlinarith [hp x y, (show (0 : ℝ) ≤ Fintype.card ι by positivity)]
    have h := Finset.sum_le_sum (s := Finset.univ) (fun y _ => hpoint y)
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul, ← Finset.mul_sum] at h
    have hg := mul_le_mul_of_nonneg_left (hgood x)
      (show (0 : ℝ) ≤ Fintype.card ι by positivity)
    linarith
  have hupper := Finset.expect_le Finset.univ_nonempty (fun x _ => hu x)
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  linarith

end DPCut
