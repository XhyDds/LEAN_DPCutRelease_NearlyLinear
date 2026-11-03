import DPCut.EllipsoidFeasibility
import DPCut.LSWStatement

/-!
Deterministic concave optimization by the proved central-cut ellipsoid method.
The only queried information is the supplied separation/first-order reply.
In particular, neither the program nor its stopping rule computes an optimum.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Metric
open scoped RealInnerProductSpace

namespace DPCut.EllipsoidOptimization

open EllipsoidMethod

variable {m : ℕ} {Θ : Type} [MeasurableSpace Θ]
local notation "E" => EuclideanSpace ℝ (Fin m)

def target (P : LSW.Problem (Fin m) Θ) (θ : Θ) (threshold : ℝ) : Set E :=
  P.body ∩ {x | threshold ≤ P.value θ x}

def fixedNormal (hm : 1 ≤ m) : E := EuclideanSpace.single ⟨0, by omega⟩ 1

theorem fixedNormal_ne_zero (hm : 1 ≤ m) : fixedNormal hm ≠ 0 := by
  intro h
  have he := congrArg (fun x : E => x ⟨0, by omega⟩) h
  simp [fixedNormal] at he

def targetOracle (P : LSW.Problem (Fin m) Θ) (O : LSW.Oracle P)
    (hm : 1 ≤ m) (θ : Θ) (threshold : ℝ) : PointOracle (target P θ threshold) :=
  fun x =>
    match h : (O.answer (θ, x)).value with
    | .inl g =>
        .separate g (by
          have hc := O.correct θ x
          simp only [h, LSW.CorrectReply] at hc
          exact hc.2.1) (by
          have hc := O.correct θ x
          simp only [h, LSW.CorrectReply] at hc
          exact fun y hy => hc.2.2 y hy.1)
    | .inr (value, g) =>
        have hc : x ∈ P.body ∧ value = P.value θ x ∧
            ∀ y ∈ P.body, P.value θ y ≤ value + ⟪g, y - x⟫ := by
          simpa only [h, LSW.CorrectReply] using O.correct θ x
        if accepted : threshold ≤ value then
          .accept ⟨hc.1, by change threshold ≤ P.value θ x; rw [← hc.2.1]; exact accepted⟩
        else if zero : g = 0 then
          .separate (fixedNormal hm) (fixedNormal_ne_zero hm) (by
            intro y hy
            have hv := hc.2.2 y hy.1
            simp only [zero, inner_zero_left, add_zero] at hv
            exact False.elim (by
              have ht : threshold ≤ P.value θ y := hy.2
              have hlt : value < threshold := lt_of_not_ge accepted
              linarith))
        else
          .separate (-g) (neg_ne_zero.mpr zero) (by
            intro y hy
            have hv := hc.2.2 y hy.1
            have ht : threshold ≤ P.value θ y := hy.2
            have hlt : value < threshold := lt_of_not_ge accepted
            have hinner : 0 ≤ ⟪g, y - x⟫ := by linarith
            simpa only [inner_neg_left] using neg_nonpos.mpr hinner)

def radius (P : LSW.Problem (Fin m) Θ) (tolerance : ℝ) : ℝ :=
  P.innerRadius * (tolerance / (2 * P.rangeBound))

theorem radius_pos (P : LSW.Problem (Fin m) Θ) {tolerance : ℝ} (ht : 0 < tolerance) :
    0 < radius P tolerance := by
  have hB : 0 < P.rangeBound := lt_of_lt_of_le zero_lt_one P.range_one_le
  unfold radius
  exact mul_pos P.inner_pos (div_pos ht (by positivity))

theorem target_contains_ball (P : LSW.Problem (Fin m) Θ) (θ : Θ) (threshold tolerance : ℝ)
    (ht : 0 < tolerance) (ht1 : tolerance ≤ 1) (y : E) (hy : y ∈ P.body)
    (hvalue : threshold + tolerance ≤ P.value θ y) :
    closedBall ((1 - tolerance / (2 * P.rangeBound)) • y) (radius P tolerance) ⊆ target P θ threshold := by
  let a := tolerance / (2 * P.rangeBound)
  have hB : 0 < P.rangeBound := lt_of_lt_of_le zero_lt_one P.range_one_le
  have ha : 0 < a := by dsimp only [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp only [a]
    apply (div_le_one (by positivity)).mpr
    linarith [P.range_one_le]
  intro z hz
  let u := a⁻¹ • (z - (1 - a) • y)
  have hzu : ‖z - (1 - a) • y‖ ≤ a * P.innerRadius := by
    simpa only [mem_closedBall, dist_eq_norm, radius, a, mul_comm] using hz
  have huNorm : ‖u‖ ≤ P.innerRadius := by
    calc
      _ = a⁻¹ * ‖z - (1 - a) • y‖ := by
        simp only [u, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
      _ ≤ a⁻¹ * (a * P.innerRadius) := mul_le_mul_of_nonneg_left hzu (by positivity)
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
  have hu : u ∈ P.body := P.inner_ball (by simpa using huNorm)
  have he : (1 - a) • y + a • u = z := by
    dsimp only [u]
    rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    abel
  have hbody : z ∈ P.body := he ▸ P.convex hy hu (by linarith) ha.le (by ring)
  have hc := (P.concave θ).2 hy hu (show 0 ≤ 1 - a by linarith) ha.le (by ring : (1 - a) + a = 1)
  rw [he] at hc
  have hrange := P.range_le θ y hy u hu
  have hscale : a * P.rangeBound = tolerance / 2 := by
    dsimp only [a]
    field_simp
  change (1 - a) * P.value θ y + a * P.value θ u ≤ P.value θ z at hc
  have hm := mul_le_mul_of_nonneg_left hrange ha.le
  refine ⟨hbody, ?_⟩
  change threshold ≤ P.value θ z
  nlinarith

def check (P : LSW.Problem (Fin m) Θ) (O : LSW.Oracle P) (hm : 1 ≤ m)
    (θ : Θ) (threshold tolerance : ℝ) :
    {x // x ∈ target P θ threshold} ⊕ Ellipsoid E :=
  EllipsoidMethod.run (targetOracle P O hm θ threshold).toSeparationOracle
    (m + 1) (by exact_mod_cast Nat.succ_le_succ hm)
    (ballIterationBudget m P.outerRadius (radius P tolerance))
    (Ellipsoid.ball 0 P.outerRadius (P.inner_pos.trans_le P.radii_order))

theorem failed_threshold (P : LSW.Problem (Fin m) Θ) (O : LSW.Oracle P) (hm : 1 ≤ m)
    (θ : Θ) (threshold tolerance : ℝ) (ht : 0 < tolerance) (ht1 : tolerance ≤ 1)
    (remaining : Ellipsoid E) (hfail : check P O hm θ threshold tolerance = .inr remaining) :
    ∀ y ∈ P.body, P.value θ y < threshold + tolerance := by
  intro y hy
  by_contra hvalue
  have hv : threshold + tolerance ≤ P.value θ y := le_of_not_gt hvalue
  have hball := target_contains_ball P θ threshold tolerance ht ht1 y hy hv
  have hsuccess := feasible_of_balls (targetOracle P O hm θ threshold) hm
    (0 : E) ((1 - tolerance / (2 * P.rangeBound)) • y)
    (P.inner_pos.trans_le P.radii_order) (radius_pos P ht)
    (fun x hx => P.outer_ball hx.1) hball
  obtain ⟨x, hx⟩ := hsuccess
  change check P O hm θ threshold tolerance = .inl x at hx
  rw [hfail] at hx
  cases hx

structure State (m : ℕ) where
  best : EuclideanSpace ℝ (Fin m)
  lower : ℝ
  upper : ℝ

def State.Valid (P : LSW.Problem (Fin m) Θ) (θ : Θ) (s : State m) : Prop :=
  s.best ∈ P.body ∧ s.lower ≤ P.value θ s.best ∧ ∀ y ∈ P.body, P.value θ y ≤ s.upper

def State.width (s : State m) : ℝ := s.upper - s.lower

def initial (P : LSW.Problem (Fin m) Θ) (O : LSW.Oracle P) (θ : Θ) : State m :=
  match (O.answer (θ, 0)).value with
  | .inl _ => ⟨0, 0, P.rangeBound⟩
  | .inr (value, _) => ⟨0, value, value + P.rangeBound⟩

theorem initial_valid (P : LSW.Problem (Fin m) Θ) (O : LSW.Oracle P) (θ : Θ) :
    (initial P O θ).Valid P θ ∧ (initial P O θ).width = P.rangeBound := by
  have hzero : (0 : E) ∈ P.body := P.inner_ball (by simp [P.inner_pos.le])
  have hc := O.correct θ 0
  cases h : (O.answer (θ, 0)).value with
  | inl g => simp only [h, LSW.CorrectReply] at hc; exact False.elim (hc.1 hzero)
  | inr pair =>
      rcases pair with ⟨value, g⟩
      simp only [h, LSW.CorrectReply] at hc
      simp only [initial, h, State.Valid, State.width]
      refine ⟨⟨hzero, by rw [hc.2.1], ?_⟩, ?_⟩
      · intro y hy
        have hr := P.range_le θ y hy 0 hzero
        rw [hc.2.1]
        linarith
      · ring

def step (P : LSW.Problem (Fin m) Θ) (O : LSW.Oracle P) (hm : 1 ≤ m)
    (θ : Θ) (tolerance : ℝ) (s : State m) : State m :=
  let threshold := (s.lower + s.upper) / 2
  match check P O hm θ threshold tolerance with
  | .inl x => ⟨x.val, threshold, s.upper⟩
  | .inr _ => ⟨s.best, s.lower, min s.upper (threshold + tolerance)⟩

theorem step_valid_width (P : LSW.Problem (Fin m) Θ) (O : LSW.Oracle P) (hm : 1 ≤ m)
    (θ : Θ) (tolerance : ℝ) (ht : 0 < tolerance) (ht1 : tolerance ≤ 1)
    (s : State m) (hs : s.Valid P θ) :
    (step P O hm θ tolerance s).Valid P θ ∧
      (step P O hm θ tolerance s).width ≤ s.width / 2 + tolerance := by
  have horder : s.lower ≤ s.upper := hs.2.1.trans (hs.2.2 s.best hs.1)
  cases h : check P O hm θ ((s.lower + s.upper) / 2) tolerance with
  | inl x =>
      simp only [step, h, State.Valid, State.width]
      refine ⟨⟨x.property.1, x.property.2, hs.2.2⟩, ?_⟩
      linarith
  | inr remaining =>
      have hf := failed_threshold P O hm θ _ tolerance ht ht1 remaining h
      simp only [step, h, State.Valid, State.width]
      refine ⟨⟨hs.1, hs.2.1, ?_⟩, ?_⟩
      · intro y hy
        exact le_min (hs.2.2 y hy) (hf y hy).le
      · have hb := min_le_right s.upper ((s.lower + s.upper) / 2 + tolerance)
        linarith

end DPCut.EllipsoidOptimization
