import DPCut.HierarchyComparator

/-! Deterministic final transfer for hierarchical clustering. -/
set_option autoImplicit false
noncomputable section
namespace DPCut

def treeErrorCoefficient (c : ℝ) : ℝ := 1 / Real.log 2 + 1 / c

lemma treeErrorCoefficient_pos {c : ℝ} (hc : 0 < c) : 0 < treeErrorCoefficient c := by
  unfold treeErrorCoefficient
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

lemma hierarchy_error_log_bound {n : ℕ} (hn : 2 ≤ n) {c E : ℝ} (hc : 0 < c) (hE : 0 ≤ E) :
    E / 2 * (n + n * Real.log n / c) ≤ treeErrorCoefficient c * E * n * Real.log n := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn2
  have hlogpos : 0 < Real.log n := lt_of_lt_of_le hl2 hlog
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hbase : (n : ℝ) ≤ n * Real.log n / Real.log 2 := (le_div_iff₀ hl2).mpr
    (mul_le_mul_of_nonneg_left hlog hn0)
  have he := mul_le_mul_of_nonneg_left hbase hE
  have hp : 0 ≤ E * (n * Real.log n / c) := by positivity
  unfold treeErrorCoefficient
  have heq : (1 / Real.log 2 + 1 / c) * E * n * Real.log n =
      E * (n * Real.log n / Real.log 2) + E * (n * Real.log n / c) := by ring
  rw [heq]
  nlinarith

lemma hcOptimum_nonneg {n : ℕ} {w : Weights n} (hw : Nonnegative w)
    {T : Hierarchy n} (hT : IsHierarchy T) : 0 ≤ hcOptimum w := by
  obtain ⟨Tstar, hstar, he⟩ := hcOptimum_exists w hT
  rw [← he]
  exact Finset.sum_nonneg fun e he => mul_nonneg (hw e) (Nat.cast_nonneg _)

lemma hcOptimum_le {n : ℕ} (w : Weights n) {T : Hierarchy n} (hT : IsHierarchy T) :
    hcOptimum w ≤ hcCost w T := csInf_le ((Set.toFinite _).image _).bddBelow ⟨T, hT, rfl⟩

lemma hierarchy_private_transfer {n : ℕ} (hn : 2 ≤ n) {w h : Weights n}
    (hw : Nonnegative w) {T : Hierarchy n} {c η E a : ℝ}
    (hc : 0 < c) (ha : 0 ≤ a) (hη : 0 ≤ η) (hη₁ : η ≤ 1 / 4) (hE : 0 ≤ E)
    (hcuts : AllCuts w h η E) (hT : BalancedHierarchy c T)
    (happrox : hcCost h T ≤ 16 * a * hcOptimum h) :
    hcCost w T ≤ 512 * a * hcOptimum w +
      (32 * a * treeErrorCoefficient (1 / 4) + 2 * treeErrorCoefficient c) * E * n * Real.log n := by
  obtain ⟨Tstar, hstar, hcost⟩ := balanced_comparator hn hw
  have h₁ := (hc_balanced_transfer hT hc hE hcuts).trans
    (add_le_add_left (hierarchy_error_log_bound hn hc hE) _)
  have h₂ := (hc_balanced_transfer hstar (by norm_num) hE hcuts).trans
    (add_le_add_left (hierarchy_error_log_bound hn (by norm_num) hE) _)
  have hlow := (abs_le.mp h₁).1
  have hhigh := (abs_le.mp h₂).2
  have hop := mul_le_mul_of_nonneg_left (hcOptimum_le h hstar.1) (by positivity : 0 ≤ 16 * a)
  have hcomp := mul_le_mul_of_nonneg_left hcost (by positivity : 0 ≤ 16 * a * (1 + η))
  have hnon := hcOptimum_nonneg hw hT.1
  have hcost0 : 0 ≤ hcCost w T := Finset.sum_nonneg fun e he => mul_nonneg (hw e) (Nat.cast_nonneg _)
  have hE₁ : 0 ≤ treeErrorCoefficient (1 / 4) * E * n * Real.log n := by
    have := (treeErrorCoefficient_pos (by norm_num : (0 : ℝ) < 1 / 4)).le
    have : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    positivity
  have hE₂ : 0 ≤ treeErrorCoefficient c * E * n * Real.log n := by
    have := (treeErrorCoefficient_pos hc).le
    have : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    positivity
  have hpre : (1 - η) * hcCost w T ≤ 256 * a * (1 + η) * hcOptimum w +
      16 * a * (treeErrorCoefficient (1 / 4) * E * n * Real.log n) +
      treeErrorCoefficient c * E * n * Real.log n := by
    nlinarith [mul_le_mul_of_nonneg_left hhigh (by positivity : 0 ≤ 16 * a)]
  have hupper : (1 / 2 : ℝ) * hcCost w T ≤ 256 * a * hcOptimum w +
      16 * a * (treeErrorCoefficient (1 / 4) * E * n * Real.log n) +
      treeErrorCoefficient c * E * n * Real.log n := by
    -- Keep 3/4 on the left and 5/4 on the optimum, then use the slack in 512.
    nlinarith [mul_nonneg ha hnon, mul_nonneg (sub_nonneg.mpr hη₁) hcost0]
  nlinarith

end DPCut
