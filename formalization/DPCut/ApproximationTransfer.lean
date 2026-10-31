import DPCut.Theorem1
import DPCut.TotalVariation

/-! Budget allocation and statistical transfer for approximate release laws.
These lemmas are shared by the real-arithmetic approximate-SDP proof. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DPCut

def precisionParameters (p : Parameters) : Parameters :=
  { p with delta := p.delta / 2, beta := p.beta / 2 }

lemma precisionParameters_valid {p : Parameters} (hp : p.Valid) :
    (precisionParameters p).Valid := by
  rcases hp with ⟨hg, hg', he, he', hd, hd', hb, hb'⟩
  dsimp [Parameters.Valid, precisionParameters]
  exact ⟨hg, hg', he, he', by linarith, by linarith, by linarith, by linarith⟩

def implementationTV (p : Parameters) : ℝ :=
  min (p.beta / 2) (p.delta / (2 * (1 + Real.exp p.epsilon)))

lemma implementationTV_pos {p : Parameters} (hp : p.Valid) : 0 < implementationTV p := by
  unfold implementationTV
  apply lt_min
  · linarith [hp.2.2.2.2.2.2.1]
  · exact div_pos hp.2.2.2.2.1 (by positivity)

lemma implementationTV_privacy {p : Parameters} :
    p.delta / 2 + (1 + Real.exp p.epsilon) * implementationTV p ≤ p.delta := by
  have he : 0 < 1 + Real.exp p.epsilon := by positivity
  have hm := mul_le_mul_of_nonneg_left
    (min_le_right (p.beta / 2) (p.delta / (2 * (1 + Real.exp p.epsilon)))) he.le
  have hid : (1 + Real.exp p.epsilon) * (p.delta / (2 * (1 + Real.exp p.epsilon))) =
      p.delta / 2 := by field_simp
  rw [hid] at hm
  unfold implementationTV
  linarith

lemma mainError_one_le {n : ℕ} (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid) :
    1 ≤ mainError n p := by
  have hge : 0 < p.gamma * p.epsilon := mul_pos hp.1 hp.2.2.1
  have hge1 : p.gamma * p.epsilon ≤ 1 :=
    (mul_le_mul_of_nonneg_left hp.2.2.2.1 hp.1.le).trans (by linarith [hp.2.1])
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hratio : 1 ≤ (n : ℝ) / (p.gamma * p.epsilon) :=
    (le_div_iff₀ hge).mpr (by linarith)
  exact one_le_mul_of_one_le_of_one_le hratio
    (one_le_pow₀ (core_log_bounds hn (le_refl (1 : ℝ)) p hp).one_le)

lemma precision_mainError_le {n : ℕ} (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid) :
    mainError n (precisionParameters p) ≤ (3 : ℝ) ^ 7 * mainError n p := by
  have hL := (core_log_bounds hn (le_refl (1 : ℝ)) p hp).one_le
  have heq : logFactor n 1 (precisionParameters p) = logFactor n 1 p + 2 * Real.log 2 := by
    rw [main_log_expansion hn (precisionParameters_valid hp), main_log_expansion hn hp]
    simp only [precisionParameters]
    rw [Real.log_div hp.2.2.2.2.1.ne' (by norm_num),
      Real.log_div hp.2.2.2.2.2.2.1.ne' (by norm_num)]
    ring
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hpow := pow_le_pow_left₀
    (show 0 ≤ logFactor n 1 (precisionParameters p) from
      le_trans (by norm_num) (core_log_bounds hn (le_refl (1 : ℝ)) _ (precisionParameters_valid hp)).one_le)
    (show logFactor n 1 (precisionParameters p) ≤ 3 * logFactor n 1 p by linarith) 7
  have hm := mul_le_mul_of_nonneg_left hpow
    (div_nonneg (Nat.cast_nonneg n) (mul_pos hp.1 hp.2.2.1).le)
  simpa only [mainError, precisionParameters, mul_pow, mul_left_comm] using hm

lemma precision_error_le {n : ℕ} (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid) :
    (2 : ℝ) ^ 166 * mainError n (precisionParameters p) ≤
      (2 : ℝ) ^ 178 * mainError n p := by
  have h := mul_le_mul_of_nonneg_left (precision_mainError_le hn hp)
    (show (0 : ℝ) ≤ 2 ^ 166 by positivity)
  have h1 := mainError_one_le hn hp
  nlinarith

lemma HighProbability.tv_transfer {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} {β ρ : ℝ} {P : α → Prop}
    (h : HighProbability ν β P) (ht : TVClose μ ν ρ) :
    HighProbability μ (β + ρ) P := by
  refine ⟨h.1, ?_⟩
  have ht' := (abs_le.mp (ht {x | P x} h.1)).1
  linarith [h.2]

end DPCut
