import DPCut.EllipsoidVolume

/-! A finite, deterministic ellipsoid feasibility algorithm. Its input oracle
either accepts the current center or supplies a separating central cut in
unit-ball coordinates. Correctness and the iteration bound are proved here;
construction and arithmetic cost of a problem-specific oracle are separate. -/
set_option autoImplicit false
noncomputable section
open Metric
open scoped RealInnerProductSpace
namespace DPCut.EllipsoidMethod

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

inductive Decision (K : Set E) (e : Ellipsoid E) where
  | accept (feasible : e.center ∈ K)
  | separate (normal : E) (unit : ‖normal‖ = 1)
      (valid : ∀ x ∈ K, ⟪normal, e.axes.symm (x - e.center)⟫ ≤ 0)

abbrev SeparationOracle (K : Set E) := (e : Ellipsoid E) → Decision K e

/-- Exhausting the fuel returns the remaining enclosing ellipsoid. Success
returns the actual center inspected by the oracle, with a feasibility proof. -/
def run {K : Set E} (oracle : SeparationOracle K) (d : ℝ) (hd : 2 ≤ d) :
    ℕ → Ellipsoid E → {x // x ∈ K} ⊕ Ellipsoid E
  | 0, e => .inr e
  | k + 1, e => match oracle e with
    | .accept h => .inl ⟨e.center, h⟩
    | .separate u hu _ => run oracle d hd k (e.cut d hd u hu)

/-- Number of oracle invocations in this particular execution. -/
def oracleCalls {K : Set E} (oracle : SeparationOracle K) (d : ℝ) (hd : 2 ≤ d) :
    ℕ → Ellipsoid E → ℕ
  | 0, _ => 0
  | k + 1, e => match oracle e with
    | .accept _ => 1
    | .separate u hu _ => 1 + oracleCalls oracle d hd k (e.cut d hd u hu)

theorem oracleCalls_le {K : Set E} (oracle : SeparationOracle K) (d : ℝ) (hd : 2 ≤ d)
    (k : ℕ) (e : Ellipsoid E) : oracleCalls oracle d hd k e ≤ k := by
  induction k generalizing e with
  | zero => simp [oracleCalls]
  | succ k ih =>
    simp only [oracleCalls]
    cases oracle e with
    | accept h => simp
    | separate u hu h => simpa [Nat.add_comm] using Nat.add_le_add_left (ih _) 1

theorem run_failure_invariant {K : Set E} (oracle : SeparationOracle K)
    (d : ℝ) (hd : 2 ≤ d) (hmd : (m : ℝ) ≤ d) (k : ℕ)
    (e : Ellipsoid E) (hK : K ⊆ e.region) {e' : Ellipsoid E}
    (hfail : run oracle d hd k e = .inr e') :
    K ⊆ e'.region ∧ Real.log e'.size ≤ Real.log e.size - k / (2 * (d + 1)) := by
  induction k generalizing e with
  | zero =>
    simp only [run, Sum.inr.injEq] at hfail
    subst e'
    simpa using hK
  | succ k ih =>
    simp only [run] at hfail
    cases ho : oracle e with
    | accept h => simp [ho] at hfail
    | separate u hu hcut =>
      simp only [ho] at hfail
      have hnew : K ⊆ (e.cut d hd u hu).region :=
        fun x hx => e.cut_contains d hd u hu (hK hx) (hcut x hx)
      obtain ⟨hsub, hlog⟩ := ih _ hnew hfail
      refine ⟨hsub, ?_⟩
      have hstep := e.log_size_cut_le hd hmd u hu
      push_cast
      rw [add_div]
      linarith

/-- A body containing a ball cannot survive more than the explicit logarithmic
volume budget. No exact optimizer is assumed by this theorem. -/
theorem run_success {K : Set E} (oracle : SeparationOracle K)
    (d : ℝ) (hd : 2 ≤ d) (hmd : (m : ℝ) ≤ d)
    (e : Ellipsoid E) (hK : K ⊆ e.region)
    (p : E) {r : ℝ} (hr : 0 < r) (hball : closedBall p r ⊆ K)
    (k : ℕ)
    (hk : 2 * (d + 1) * (Real.log e.size - m * Real.log r) < k) :
    ∃ x, run oracle d hd k e = .inl x := by
  cases hrun : run oracle d hd k e with
  | inl x => exact ⟨x, rfl⟩
  | inr e' =>
    obtain ⟨hsub, hlog⟩ := run_failure_invariant oracle d hd hmd k e hK hrun
    have hlower := e'.size_ge_of_ball_subset p hr (hball.trans hsub)
    have hl := Real.log_le_log (pow_pos hr _) hlower
    rw [Real.log_pow] at hl
    have hden : 0 < 2 * (d + 1) := by linarith
    have hk' : Real.log e.size - m * Real.log r < k / (2 * (d + 1)) :=
      (lt_div_iff₀ hden).mpr (by nlinarith [hk])
    linarith

/-- An explicit natural-number fuel bound; its dependence on the inner radius
is logarithmic. The extra one makes the volume inequality strict. -/
def iterationBudget (m : ℕ) (d initialSize r : ℝ) : ℕ :=
  ⌊2 * (d + 1) * (Real.log initialSize - m * Real.log r)⌋₊ + 1

theorem run_iterationBudget_success {K : Set E} (oracle : SeparationOracle K)
    (d : ℝ) (hd : 2 ≤ d) (hmd : (m : ℝ) ≤ d)
    (e : Ellipsoid E) (hK : K ⊆ e.region)
    (p : E) {r : ℝ} (hr : 0 < r) (hball : closedBall p r ⊆ K) :
    ∃ x, run oracle d hd (iterationBudget m d e.size r) e = .inl x := by
  apply run_success oracle d hd hmd e hK p hr hball
  simpa [iterationBudget] using Nat.lt_floor_add_one
    (2 * (d + 1) * (Real.log e.size - m * Real.log r))

end DPCut.EllipsoidMethod
