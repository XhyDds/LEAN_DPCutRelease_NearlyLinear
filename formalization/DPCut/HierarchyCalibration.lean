import DPCut.HierarchyOracle
import DPCut.HierarchyTransferBound
import DPCut.MaxKApplication

/-! Uniform constants and failure budgets for Theorem 36. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut

def hierarchyRatioCoefficient (o : InducedARVContract) : ℝ :=
  1 / Real.sqrt (Real.log 2) + o.factor

def hierarchyAddCoefficient (o : InducedARVContract) : ℝ :=
  32 * hierarchyRatioCoefficient o * treeErrorCoefficient (1 / 4) +
  2 * treeErrorCoefficient o.balance / Real.sqrt (Real.log 2)

lemma hierarchyRatioCoefficient_pos (o : InducedARVContract) : 0 < hierarchyRatioCoefficient o := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hf := o.factor_pos
  unfold hierarchyRatioCoefficient
  positivity

lemma hierarchyAddCoefficient_pos (o : InducedARVContract) : 0 < hierarchyAddCoefficient o := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr := hierarchyRatioCoefficient_pos o
  have h₁ := treeErrorCoefficient_pos (by norm_num : (0 : ℝ) < 1 / 4)
  have h₂ := treeErrorCoefficient_pos o.balance_pos
  unfold hierarchyAddCoefficient
  positivity

lemma sqrt_log_lower {n : ℕ} (hn : 2 ≤ n) :
    0 < Real.sqrt (Real.log 2) ∧ Real.sqrt (Real.log 2) ≤ Real.sqrt (Real.log n) := by
  refine ⟨Real.sqrt_pos.mpr (Real.log_pos (by norm_num)), Real.sqrt_le_sqrt ?_⟩
  exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)

lemma hierarchyFactor_bound (o : InducedARVContract) {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ hierarchyFactor o n ∧ hierarchyFactor o n ≤ hierarchyRatioCoefficient o * Real.sqrt (Real.log n) := by
  have hs := sqrt_log_lower hn
  have hratio : 1 ≤ Real.sqrt (Real.log n) / Real.sqrt (Real.log 2) := (le_div_iff₀ hs.1).mpr (by simpa using hs.2)
  unfold hierarchyFactor hierarchyRatioCoefficient
  constructor
  · nlinarith [mul_nonneg o.factor_pos.le (Real.sqrt_nonneg (Real.log n))]
  · simp only [div_eq_mul_inv, one_mul] at hratio ⊢
    nlinarith

lemma log_three_halves {n : ℕ} (hn : 2 ≤ n) :
    (Real.log n) ^ (3 / 2 : ℝ) = Real.sqrt (Real.log n) * Real.log n := by
  have hp : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hp, Real.rpow_one, ← Real.sqrt_eq_rpow]

lemma hierarchy_calibrated_transfer (o : InducedARVContract) {n : ℕ} (hn : 2 ≤ n)
    {w h : Weights n} (hw : Nonnegative w) {T : Hierarchy n} {η E : ℝ}
    (hη : 0 ≤ η) (hη₁ : η ≤ 1 / 4) (hE : 0 ≤ E) (hcuts : AllCuts w h η E)
    (hT : BalancedHierarchy o.balance T)
    (happrox : hcCost h T ≤ 16 * hierarchyFactor o n * hcOptimum h) :
    hcCost w T ≤ (512 * hierarchyRatioCoefficient o) * Real.sqrt (Real.log n) * hcOptimum w +
      hierarchyAddCoefficient o * E * n * (Real.log n) ^ (3 / 2 : ℝ) := by
  have hf := hierarchyFactor_bound o hn
  have hb := hierarchy_private_transfer hn hw o.balance_pos (by linarith [hf.1]) hη hη₁ hE hcuts hT happrox
  have ho := hcOptimum_nonneg hw hT.1
  have hmain := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf.2 (by norm_num : (0 : ℝ) ≤ 512)) ho
  have hs := sqrt_log_lower hn
  have hratio : 1 ≤ Real.sqrt (Real.log n) / Real.sqrt (Real.log 2) := (le_div_iff₀ hs.1).mpr (by simpa using hs.2)
  have h₁ := treeErrorCoefficient_pos (by norm_num : (0 : ℝ) < 1 / 4)
  have h₂ := treeErrorCoefficient_pos o.balance_pos
  have hcoeff : 32 * hierarchyFactor o n * treeErrorCoefficient (1 / 4) + 2 * treeErrorCoefficient o.balance ≤
      hierarchyAddCoefficient o * Real.sqrt (Real.log n) := by
    unfold hierarchyAddCoefficient
    have hh₁ := mul_le_mul_of_nonneg_right hf.2 (by positivity : 0 ≤ 32 * treeErrorCoefficient (1 / 4))
    have hh₂ := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 2 * treeErrorCoefficient o.balance)
    simp only [div_eq_mul_inv] at hh₂ ⊢
    nlinarith
  have hp : 0 ≤ E * n * Real.log n := by
    have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    positivity
  have hadd := mul_le_mul_of_nonneg_right hcoeff hp
  rw [log_three_halves hn]
  nlinarith

lemma hierarchy_failure_bound {n : ℕ} (hn : 2 ≤ n) :
    ((n : ℝ) - 1) * (n : ℝ)⁻¹ ^ 12 ≤ (n : ℝ)⁻¹ ^ 10 := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hi : (n : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hp).mpr h1
  have hpow := pow_le_pow_of_le_one (inv_nonneg.mpr hp.le) hi (by norm_num : 10 ≤ 11)
  calc
    _ ≤ (n : ℝ) * (n : ℝ)⁻¹ ^ 12 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (n : ℝ)⁻¹ ^ 11 := by field_simp
    _ ≤ _ := hpow

def nonprivateHierarchyKernel (o : InducedARVContract) (n : ℕ) : Kernel (Weights n) (Hierarchy n) :=
  hierarchyKernel (hierarchySplitKernel o n) o.balance n Finset.univ

instance nonprivateHierarchyKernel_markov (o : InducedARVContract) (n : ℕ) :
    IsMarkovKernel (nonprivateHierarchyKernel o n) := hierarchyKernel_markov _ _ _ _

lemma nonprivateHierarchy_quality (o : InducedARVContract) {n : ℕ} (hn : 2 ≤ n)
    {w : Weights n} (hw : Nonnegative w) :
    HighProbability (nonprivateHierarchyKernel o n w) ((n : ℝ)⁻¹ ^ 10)
      (fun T => BalancedHierarchy o.balance T ∧ hcCost w T ≤ 16 * hierarchyFactor o n * hcOptimum w) := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hh := hierarchyLaw_quality (hierarchySplitKernel o n) w o.balance_pos o.balance_le
    (by positivity : 0 ≤ (n : ℝ)⁻¹ ^ 12) (hierarchySplitKernel_quality o hn hw) n hne
    (by simp : (Finset.univ : Finset (Fin n)).card ≤ n + 1)
  have hf : (((Finset.univ : Finset (Fin n)).card : ℕ) : ℝ) = (n : ℝ) := by simp
  rw [hf] at hh
  apply (hh.weaken (hierarchy_failure_bound hn)).mono _ (Set.toFinite _ |>.measurableSet)
  intro T hT
  obtain ⟨hbal, hrec⟩ := hT.to_global
  refine ⟨hbal, ?_⟩
  obtain ⟨Tstar, hstar, heq⟩ := hcOptimum_exists w hbal.1
  have hc := hierarchy_charging_bound hw hbal.1 hstar (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (1 / 4 : ℝ) ≤ 1 / 3) (hierarchyFactor_bound o hn).1 hrec
  norm_num [heq] at hc
  exact hc

end DPCut
