import DPCut.Definitions

/-! Measurability, linearity, and positivity of finite graph cuts. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace DPCut

@[fun_prop] lemma measurable_cut {A : Type*} [MeasurableSpace A] {n : ℕ}
    {w : A → Weights n} (hw : Measurable w) (S : Finset (Fin n)) :
    Measurable (fun x => cut (w x) S) := by unfold cut pairing; fun_prop

lemma measurableSet_nonnegative {A : Type*} [MeasurableSpace A] {n : ℕ}
    {w : A → Weights n} (hw : Measurable w) : MeasurableSet {x | Nonnegative (w x)} := by
  unfold Nonnegative
  simp only [setOf_forall]
  exact MeasurableSet.iInter fun e => measurableSet_le measurable_const ((measurable_pi_apply e).comp hw)

lemma measurableSet_allCuts {A : Type*} [MeasurableSpace A] {n : ℕ}
    {w h : A → Weights n} (hw : Measurable w) (hh : Measurable h) (γ B : ℝ) :
    MeasurableSet {x | AllCuts (w x) (h x) γ B} := by
  unfold AllCuts
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro S
  exact measurableSet_le (((measurable_cut hw S).sub (measurable_cut hh S)).abs)
    (((measurable_cut hw S).const_mul γ).add_const B)

lemma cut_add {n : ℕ} (w h : Weights n) (S : Finset (Fin n)) :
    cut (w + h) S = cut w S + cut h S := by
  simp [cut, pairing, add_mul, Finset.sum_add_distrib]

lemma cut_sub {n : ℕ} (w h : Weights n) (S : Finset (Fin n)) :
    cut (w - h) S = cut w S - cut h S := by
  simp [cut, pairing, sub_mul, Finset.sum_sub_distrib]

lemma cut_nonneg {n : ℕ} {w : Weights n} (hw : Nonnegative w) (S : Finset (Fin n)) :
    0 ≤ cut w S := Finset.sum_nonneg fun e _ => mul_nonneg (hw e) (by unfold cutQuery; split <;> norm_num)

lemma cut_le_mass {n : ℕ} {w : Weights n} (hw : Nonnegative w) (S : Finset (Fin n)) :
    cut w S ≤ mass w := by
  apply Finset.sum_le_sum
  intro e _
  exact mul_le_of_le_one_right (hw e) (by unfold cutQuery; split <;> norm_num)

end DPCut
