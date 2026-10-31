import DPCut.Lemma12
import DPCut.OuterLogBounds

/-! The exact budget split and clipping prerequisites in Theorem 1. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace DPCut

def boundedParameters (p : Parameters) : Parameters :=
  { p with gamma := p.gamma / 2, epsilon := p.epsilon / 2, beta := p.beta / 2 }

def preprocessingThreshold (n : ℕ) (p : Parameters) : ℝ :=
  clipThreshold n (p.epsilon / 2) (p.beta / 2) p.gamma

lemma Parameters.Valid.privacyValid {p : Parameters} (hp : p.Valid) : p.PrivacyValid := by
  obtain ⟨hg, hg1, he, he1, hd, hd1, hb, hb1⟩ := hp
  exact ⟨hg, by linarith, he, he1, hd, by linarith, hb, by linarith⟩

lemma boundedParameters_valid {p : Parameters} (hp : p.Valid) : (boundedParameters p).Valid := by
  obtain ⟨hg, hg1, he, he1, hd, hd1, hb, hb1⟩ := hp
  dsimp [Parameters.Valid, boundedParameters]
  exact ⟨by linarith, by linarith, by linarith, by linarith, hd, hd1,
    by linarith, by linarith⟩

lemma preprocessingThreshold_eq (n : ℕ) (p : Parameters) :
    preprocessingThreshold n p = 16 / (p.gamma * p.epsilon) * Real.log (n / (p.beta / 2)) := by
  unfold preprocessingThreshold clipThreshold
  ring

lemma preprocessingThreshold_one_le {n : ℕ} (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid) :
    1 ≤ preprocessingThreshold n p := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨hg, hg1, he, he1, hd, hd1, hb, hb1⟩ := hp
  have hprod : 0 < p.gamma * p.epsilon := mul_pos hg he
  have hprod1 : p.gamma * p.epsilon ≤ 1 := by nlinarith
  have hl : 1 / 2 ≤ Real.log (n / (p.beta / 2)) := by
    have hratio : (2 : ℝ) ≤ n / (p.beta / 2) := (le_div_iff₀ (by linarith)).mpr (by linarith)
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hratio
    linarith [Real.log_two_gt_d9]
  rw [preprocessingThreshold_eq]
  have hcoeff : 16 ≤ 16 / (p.gamma * p.epsilon) := (le_div_iff₀ hprod).mpr (by linarith)
  nlinarith

lemma Adjacent.clipWeights {n : ℕ} {w w' : Weights n} (h : Adjacent w w') (U : ℝ) :
    Adjacent (clipWeights U w) (clipWeights U w') := by
  apply le_trans _ h
  apply Finset.sum_le_sum
  intro e _
  have hm := abs_min_sub_min_le_max (w e) U (w' e) U
  simpa [clipWeights, max_eq_left (abs_nonneg (w e - w' e))] using hm

@[fun_prop] lemma measurable_clipWeights {n : ℕ} (U : ℝ) :
    Measurable (clipWeights (n := n) U) := by unfold clipWeights; fun_prop

lemma cut_clipWeights_le {n : ℕ} (U : ℝ) (w : Weights n) (S : Finset (Fin n)) :
    cut (clipWeights U w) S ≤ cut w S := by
  apply Finset.sum_le_sum
  intro e _
  exact mul_le_mul_of_nonneg_right (min_le_left _ _) (by unfold cutQuery; split <;> norm_num)

end DPCut
