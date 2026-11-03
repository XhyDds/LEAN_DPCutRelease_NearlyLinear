import DPCut.EllipsoidOptimization

/-! Approximation and actual oracle-call bounds for the deterministic solver. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Metric
open scoped RealInnerProductSpace

namespace DPCut.EllipsoidOptimization

open EllipsoidMethod

variable {m : ℕ} {Θ : Type} [MeasurableSpace Θ]

def iterate (P : LSW.Problem (Fin m) Θ) (O : LSW.Oracle P) (hm : 1 ≤ m)
    (θ : Θ) (tolerance : ℝ) : ℕ → State m → State m
  | 0, s => s
  | k + 1, s => step P O hm θ tolerance (iterate P O hm θ tolerance k s)

theorem iterate_valid_width (P : LSW.Problem (Fin m) Θ) (O : LSW.Oracle P) (hm : 1 ≤ m)
    (θ : Θ) (tolerance : ℝ) (ht : 0 < tolerance) (ht1 : tolerance ≤ 1)
    (k : ℕ) (s : State m) (hs : s.Valid P θ) :
    (iterate P O hm θ tolerance k s).Valid P θ ∧
      (iterate P O hm θ tolerance k s).width ≤ s.width / (2 : ℝ) ^ k + 2 * tolerance := by
  induction k with
  | zero =>
      exact ⟨hs, by simp only [iterate, pow_zero, div_one]; linarith⟩
  | succ k ih =>
      have h := step_valid_width P O hm θ tolerance ht ht1 _ ih.1
      refine ⟨h.1, ?_⟩
      change (step P O hm θ tolerance (iterate P O hm θ tolerance k s)).width ≤ _
      calc
        _ ≤ (iterate P O hm θ tolerance k s).width / 2 + tolerance := h.2
        _ ≤ (s.width / (2 : ℝ) ^ k + 2 * tolerance) / 2 + tolerance := by linarith [ih.2]
        _ = _ := by rw [pow_succ]; field_simp; ring

def rounds (P : LSW.Problem (Fin m) Θ) (epsilon : ℝ) : ℕ :=
  ⌈Real.log (2 * P.rangeBound / epsilon) / Real.log 2⌉₊ + 1

theorem rounds_precision (P : LSW.Problem (Fin m) Θ) {epsilon : ℝ}
    (he : 0 < epsilon) :
    P.rangeBound / (2 : ℝ) ^ rounds P epsilon ≤ epsilon / 2 := by
  have hB : 0 < P.rangeBound := lt_of_lt_of_le zero_lt_one P.range_one_le
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil : Real.log (2 * P.rangeBound / epsilon) / Real.log 2 ≤ (rounds P epsilon : ℝ) := by
    exact (Nat.le_ceil _).trans (by simp [rounds])
  have hlog : Real.log (2 * P.rangeBound / epsilon) ≤
      Real.log ((2 : ℝ) ^ rounds P epsilon) := by
    rw [Real.log_pow]
    exact (div_le_iff₀ htwo).mp hceil
  have hratio : 2 * P.rangeBound / epsilon ≤ (2 : ℝ) ^ rounds P epsilon :=
    (Real.log_le_log_iff (by positivity) (by positivity)).mp hlog
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ rounds P epsilon)).mpr
  have h := (div_le_iff₀ he).mp hratio
  nlinarith

def solve (P : LSW.Problem (Fin m) Θ) (O : LSW.Oracle P) (hm : 1 ≤ m)
    (theta : Θ) (epsilon : ℝ) : LSW.Space (Fin m) :=
  (iterate P O hm theta (epsilon / 4) (rounds P epsilon) (initial P O theta)).best

/-- This names the solver's returned iterate, rather than merely asserting the
existence of an approximate maximizer. Its only data-dependent access is `O`. -/
theorem solve_accurate (P : LSW.Problem (Fin m) Θ) (O : LSW.Oracle P) (hm : 1 ≤ m)
    (theta : Θ) {epsilon : ℝ} (he : 0 < epsilon) (hehalf : epsilon ≤ 1 / 2) :
    LSW.Accurate P epsilon theta (solve P O hm theta epsilon) := by
  have hi := initial_valid P O theta
  have h := iterate_valid_width P O hm theta (epsilon / 4) (by positivity) (by linarith)
    (rounds P epsilon) _ hi.1
  have hw : (iterate P O hm theta (epsilon / 4) (rounds P epsilon) (initial P O theta)).width ≤ epsilon := by
    have hr := rounds_precision P he
    rw [hi.2] at h
    linarith [h.2]
  refine ⟨h.1.1, ?_⟩
  intro y hy
  have hu := h.1.2.2 y hy
  have hl := h.1.2.1
  unfold solve
  change _ ≤ epsilon
  unfold State.width at hw
  linarith

def feasibilityBudget (P : LSW.Problem (Fin m) Θ) (epsilon : ℝ) : ℕ :=
  ballIterationBudget m P.outerRadius (radius P (epsilon / 4))

def checkCalls (P : LSW.Problem (Fin m) Θ) (O : LSW.Oracle P) (hm : 1 ≤ m)
    (theta : Θ) (epsilon threshold : ℝ) : ℕ :=
  oracleCalls (targetOracle P O hm theta threshold).toSeparationOracle
    (m + 1) (by exact_mod_cast Nat.succ_le_succ hm)
    (feasibilityBudget P epsilon)
    (Ellipsoid.ball 0 P.outerRadius (P.inner_pos.trans_le P.radii_order))

theorem checkCalls_le (P : LSW.Problem (Fin m) Θ) (O : LSW.Oracle P) (hm : 1 ≤ m)
    (theta : Θ) (epsilon threshold : ℝ) :
    checkCalls P O hm theta epsilon threshold ≤ feasibilityBudget P epsilon :=
  oracleCalls_le _ _ _ _ _

def iterateCalls (P : LSW.Problem (Fin m) Θ) (O : LSW.Oracle P) (hm : 1 ≤ m)
    (theta : Θ) (epsilon : ℝ) : ℕ → State m → ℕ
  | 0, _ => 0
  | k + 1, s =>
      iterateCalls P O hm theta epsilon k s +
        checkCalls P O hm theta epsilon
          (((iterate P O hm theta (epsilon / 4) k s).lower +
            (iterate P O hm theta (epsilon / 4) k s).upper) / 2)

theorem iterateCalls_le (P : LSW.Problem (Fin m) Θ) (O : LSW.Oracle P) (hm : 1 ≤ m)
    (theta : Θ) (epsilon : ℝ) (k : ℕ) (s : State m) :
    iterateCalls P O hm theta epsilon k s ≤ k * feasibilityBudget P epsilon := by
  induction k with
  | zero => simp [iterateCalls]
  | succ k ih =>
      exact (Nat.add_le_add ih (checkCalls_le P O hm theta epsilon _)).trans_eq (by ring)

def solveCalls (P : LSW.Problem (Fin m) Θ) (O : LSW.Oracle P) (hm : 1 ≤ m)
    (theta : Θ) (epsilon : ℝ) : ℕ :=
  1 + iterateCalls P O hm theta epsilon (rounds P epsilon) (initial P O theta)

theorem solveCalls_le (P : LSW.Problem (Fin m) Θ) (O : LSW.Oracle P) (hm : 1 ≤ m)
    (theta : Θ) (epsilon : ℝ) :
    solveCalls P O hm theta epsilon ≤ 1 + rounds P epsilon * feasibilityBudget P epsilon :=
  Nat.add_le_add_left (iterateCalls_le _ _ _ _ _ _ _) 1

end DPCut.EllipsoidOptimization
