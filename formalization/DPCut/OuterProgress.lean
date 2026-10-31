import DPCut.InnerProgress
import Mathlib.Data.Finset.SymmDiff

/-! Averaging the simultaneous cut guarantee and the exact outer mass contraction. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators symmDiff
namespace DPCut

lemma sum_cutQuery (n : ℕ) (e : Edge n) :
    ∑ S : Finset (Fin n), cutQuery S e = (Fintype.card (Finset (Fin n)) : ℝ) / 2 := by
  let f : Finset (Fin n) → Finset (Fin n) := fun S => S ∆ {e.val.1}
  have hf : Function.Involutive f := fun S => by simp [f]
  have hflip (S : Finset (Fin n)) : cutQuery (f S) e = 1 - cutQuery S e := by
    have hne := ne_of_lt e.property
    simp only [cutQuery, f, Finset.mem_symmDiff, Finset.mem_singleton]
    by_cases h1 : e.val.1 ∈ S <;> by_cases h2 : e.val.2 ∈ S <;> simp [h1, h2, Ne.symm hne]
  have heq := Fintype.sum_bijective f hf.bijective (fun S => cutQuery S e)
    (fun S => 1 - cutQuery S e) (fun S => by dsimp only; rw [hflip]; ring)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at heq
  linarith

lemma sum_cuts {n : ℕ} (w : Weights n) :
    ∑ S : Finset (Fin n), cut w S = (Fintype.card (Finset (Fin n)) : ℝ) / 2 * mass w := by
  simp only [cut, pairing]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, sum_cutQuery]
  rw [← Finset.sum_mul, mul_comm]
  rfl

theorem mass_from_cuts : MassFromCutsStatement := by
  intro n w h γ B _ _ _ _ hc
  have hu := Finset.sum_le_sum (s := Finset.univ) (fun S _ => (abs_le.mp (hc S)).2)
  have hl := Finset.sum_le_sum (s := Finset.univ) (fun S _ => (abs_le.mp (hc S)).1)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum, sum_cuts, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hu hl
  have hcard : (0 : ℝ) < Fintype.card (Finset (Fin n)) := by exact_mod_cast Fintype.card_pos
  rw [abs_le]
  constructor <;> nlinarith

lemma mass_residualUpdate {n : ℕ} (w r : Weights n) :
    mass (residualUpdate w r) = mass w - pairing w r := by
  simp only [mass, pairing, residualUpdate, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem residual_contraction : ResidualContractionStatement := by
  intro n w h a γ B hw hh ha hacc haccept hγ hγ1 hB hlarge hMH
  have hsum := ha.pairing_mass h
  have hdom := max_le_iff.mp haccept
  have hwR : Nonnegative (hadamard w a.residual) := fun e => mul_nonneg (hw e) (ha.2.2.1 e).1
  have hhR : Nonnegative (hadamard h a.residual) := fun e => mul_nonneg (hh e) (ha.2.2.1 e).1
  have hm := mass_from_cuts n _ _ γ B hwR hhR hγ.le hB hacc.2.2
  change |pairing w a.residual - pairing h a.residual| ≤ γ * pairing w a.residual + 2 * B at hm
  have hr : 0 ≤ pairing w a.residual := Finset.sum_nonneg fun e _ => hwR e
  have hu := (abs_le.mp hm).1
  rw [mass_residualUpdate]
  nlinarith [mul_le_mul_of_nonneg_right hγ1 hr]

end DPCut
