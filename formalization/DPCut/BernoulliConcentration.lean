import DPCut.FiniteKL
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Finite Bernoulli product weights and a two-sided relative concentration bound.
All estimates are proved directly for finite sums; no concentration contract is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DPCut
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def bernoulliWeight (p : ι → ℝ) (x : ι → Bool) : ℝ :=
  ∏ i, if x i then p i else 1 - p i

def bernoulliCount (b x : ι → Bool) : ℝ := ∑ i, if x i = b i then 1 else 0

def bernoulliMean (p : ι → ℝ) (b : ι → Bool) : ℝ :=
  ∑ i, if b i then p i else 1 - p i

omit [DecidableEq ι] in
lemma bernoulliWeight_nonneg {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (x : ι → Bool) :
    0 ≤ bernoulliWeight p x :=
  Finset.prod_nonneg fun i _ => by split <;> linarith [(hp i).1, (hp i).2]

omit [DecidableEq ι] in
lemma bernoulliMean_nonneg {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (b : ι → Bool) :
    0 ≤ bernoulliMean p b :=
  Finset.sum_nonneg fun i _ => by split <;> linarith [(hp i).1, (hp i).2]

lemma bernoulliWeight_sum (p : ι → ℝ) : ∑ x, bernoulliWeight p x = 1 := by
  unfold bernoulliWeight
  rw [← Fintype.prod_sum (fun i (v : Bool) => if v then p i else 1 - p i)]
  simp

lemma bernoulli_mgf_formula (p : ι → ℝ) (b : ι → Bool) (s : ℝ) :
    (∑ x, bernoulliWeight p x * Real.exp (s * bernoulliCount b x)) =
      ∏ i, (1 + (if b i then p i else 1 - p i) * (Real.exp s - 1)) := by
  simp only [bernoulliWeight, bernoulliCount, Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (v : Bool) =>
    (if v then p i else 1 - p i) * Real.exp (s * if v = b i then 1 else 0))]
  apply Finset.prod_congr rfl
  intro i _
  cases b i <;> simp <;> ring

lemma bernoulli_mgf_bound {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (b : ι → Bool) {s : ℝ} (hs : |s| ≤ 1) :
    (∑ x, bernoulliWeight p x * Real.exp (s * (bernoulliCount b x - bernoulliMean p b))) ≤
      Real.exp (bernoulliMean p b * s ^ 2) := by
  have hExp : Real.exp s - 1 ≤ s + s ^ 2 := by
    have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hs)).2
    linarith
  have hu (i : ι) : 0 ≤ (if b i then p i else 1 - p i) := by
    split <;> linarith [(hp i).1, (hp i).2]
  have hmgf : (∑ x, bernoulliWeight p x * Real.exp (s * bernoulliCount b x)) ≤
      Real.exp (bernoulliMean p b * (s + s ^ 2)) := by
    rw [bernoulli_mgf_formula]
    calc
      _ ≤ ∏ i, Real.exp ((if b i then p i else 1 - p i) * (s + s ^ 2)) := by
        apply Finset.prod_le_prod
        · intro i _
          cases b i <;> simp
          · nlinarith [mul_nonneg (sub_nonneg.mpr (hp i).2) (Real.exp_pos s).le, (hp i).1]
          · nlinarith [mul_nonneg (hp i).1 (Real.exp_pos s).le, (hp i).2]
        · intro i _
          have h := mul_le_mul_of_nonneg_left hExp (hu i)
          exact (by linarith : 1 + (if b i then p i else 1 - p i) * (Real.exp s - 1) ≤
            1 + (if b i then p i else 1 - p i) * (s + s ^ 2)).trans
              (by linarith [Real.add_one_le_exp ((if b i then p i else 1 - p i) * (s + s ^ 2))])
      _ = _ := by rw [← Real.exp_sum, ← Finset.sum_mul]; rfl
  have heq : (∑ x, bernoulliWeight p x * Real.exp (s * (bernoulliCount b x - bernoulliMean p b))) =
      Real.exp (-s * bernoulliMean p b) *
        (∑ x, bernoulliWeight p x * Real.exp (s * bernoulliCount b x)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [mul_sub, Real.exp_sub]
    rw [neg_mul, Real.exp_neg]
    ring
  rw [heq]
  calc
    _ ≤ Real.exp (-s * bernoulliMean p b) * Real.exp (bernoulliMean p b * (s + s ^ 2)) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma bernoulli_relative_tail {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (b : ι → Bool) {η t : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (ht : 0 ≤ t) :
    (∑ x, if η * bernoulliMean p b + 3 / η * t < |bernoulliCount b x - bernoulliMean p b|
      then bernoulliWeight p x else 0) ≤ 2 * Real.exp (-t) := by
  let μ := bernoulliMean p b
  let R := η * μ + 3 / η * t
  have hm : 0 ≤ μ := bernoulliMean_nonneg hp b
  have hpoint (x : ι → Bool) :
      (if R < |bernoulliCount b x - μ| then bernoulliWeight p x else 0) ≤
        Real.exp (-η * R) * (bernoulliWeight p x * Real.exp (η * (bernoulliCount b x - μ)) +
          bernoulliWeight p x * Real.exp (-η * (bernoulliCount b x - μ))) := by
    have hw := bernoulliWeight_nonneg hp x
    by_cases hx : R < |bernoulliCount b x - μ|
    · rw [if_pos hx]
      rcases lt_abs.mp hx with hl | hr
      · have hE : 1 ≤ Real.exp (-η * R) * Real.exp (η * (bernoulliCount b x - μ)) := by
          rw [← Real.exp_add, ← Real.exp_zero]
          apply Real.exp_le_exp.mpr
          nlinarith
        have h := mul_le_mul_of_nonneg_left hE hw
        nlinarith [mul_nonneg hw (Real.exp_pos (-η * (bernoulliCount b x - μ))).le,
          Real.exp_pos (-η * R)]
      · have hE : 1 ≤ Real.exp (-η * R) * Real.exp (-η * (bernoulliCount b x - μ)) := by
          rw [← Real.exp_add, ← Real.exp_zero]
          apply Real.exp_le_exp.mpr
          nlinarith
        have h := mul_le_mul_of_nonneg_left hE hw
        nlinarith [mul_nonneg hw (Real.exp_pos (η * (bernoulliCount b x - μ))).le,
          Real.exp_pos (-η * R)]
    · rw [if_neg hx]
      positivity
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hpoint x)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hh
  have hplus := bernoulli_mgf_bound hp b (show |η| ≤ 1 by rwa [abs_of_pos hη])
  have hminus := bernoulli_mgf_bound hp b (show |-η| ≤ 1 by simpa [abs_of_pos hη] using hη1)
  simp only [neg_sq] at hminus
  have hsum := add_le_add hplus hminus
  have hu := mul_le_mul_of_nonneg_left hsum (Real.exp_pos (-η * R)).le
  change _ ≤ 2 * Real.exp (-(t : ℝ))
  apply le_trans hh
  apply hu.trans
  have heq : Real.exp (-η * R) * (Real.exp (μ * η ^ 2) + Real.exp (μ * η ^ 2)) =
      2 * Real.exp (-3 * t) := by
    rw [← two_mul, ← mul_assoc, mul_comm (Real.exp (-η * R)) 2, mul_assoc, ← Real.exp_add]
    congr 2
    dsimp [R]
    field_simp
    ring
  change Real.exp (-η * R) * (Real.exp (μ * η ^ 2) + Real.exp (μ * η ^ 2)) ≤ _
  rw [heq]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)

end DPCut
