import DPCut.SDPLSWProblem
import DPCut.EllipsoidCallBounds
import DPCut.MatrixPSDAlgorithm
import DPCut.VerifiedLinearAlgebra

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open MeasureTheory Metric
open scoped RealInnerProductSpace

namespace DPCut.SDPFlat

def equiv (n : ℕ) : SDPCoordinates.Space n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n * n)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finProdFinEquiv

def reindex {ι κ Θ : Type} [Fintype ι] [Fintype κ] [MeasurableSpace Θ]
    (P : LSW.Problem ι Θ) (φ : LSW.Space ι ≃ₗᵢ[ℝ] LSW.Space κ) : LSW.Problem κ Θ where
  body := φ '' P.body
  value D x := P.value D (φ.symm x)
  measurable_value := by
    exact P.measurable_value.comp (measurable_fst.prodMk (φ.symm.continuous.measurable.comp measurable_snd))
  convex := P.convex.linear_image φ.toLinearEquiv.toLinearMap
  compact := P.compact.image φ.continuous
  concave D := by
    refine ⟨P.convex.linear_image φ.toLinearEquiv.toLinearMap, ?_⟩
    intro x hx y hy a b ha hb hab
    have hxm : φ.symm x ∈ P.body := by
      obtain ⟨z, hz, rfl⟩ := hx
      simpa using hz
    have hym : φ.symm y ∈ P.body := by
      obtain ⟨z, hz, rfl⟩ := hy
      simpa using hz
    simpa only [map_add, map_smul] using (P.concave D).2 hxm hym ha hb hab
  innerRadius := P.innerRadius
  outerRadius := P.outerRadius
  inner_pos := P.inner_pos
  radii_order := P.radii_order
  inner_ball := by
    intro x hx
    refine ⟨φ.symm x, ?_, by simp⟩
    apply P.inner_ball
    simpa only [mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using hx
  outer_ball := by
    rintro x ⟨y, hy, rfl⟩
    have h := P.outer_ball hy
    simpa only [mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using h
  rangeBound := P.rangeBound
  range_one_le := P.range_one_le
  range_le D x hx y hy := by
    have hx' : φ.symm x ∈ P.body := by obtain ⟨z,hz,rfl⟩ := hx; simpa using hz
    have hy' : φ.symm y ∈ P.body := by obtain ⟨z,hz,rfl⟩ := hy; simpa using hz
    exact P.range_le D _ hx' _ hy'

def problem {n : ℕ} (hn : 2 ≤ n) {lam B : ℝ} (hlam : 0 ≤ lam) (hB : 0 ≤ B) :
    LSW.Problem (Fin (n * n)) (Weights n) :=
  reindex (SDPCoordinates.problem hn hlam hB) (equiv n)

def mapReply (n : ℕ) : LSW.Reply (Fin n × Fin n) → LSW.Reply (Fin (n * n))
  | .inl g => .inl (equiv n g)
  | .inr (value,g) => .inr (value,equiv n g)

def answer {n : ℕ} (lam B : ℝ) (q : Weights n × EuclideanSpace ℝ (Fin (n * n))) :
    LSW.Reply (Fin (n * n)) :=
  mapReply n (SDPCoordinates.answer MatrixElimination.primitives lam B (q.1, (equiv n).symm q.2))

theorem answer_correct {n : ℕ} (hn : 2 ≤ n) {lam B : ℝ} (hlam : 0 ≤ lam) (hB : 0 ≤ B)
    (D : Weights n) (x : EuclideanSpace ℝ (Fin (n*n))) :
    LSW.CorrectReply (problem hn hlam hB) D x (answer lam B (D,x)) := by
  have hc := SDPCoordinates.answer_correct hn hlam hB MatrixElimination.primitives D ((equiv n).symm x)
  cases hr : SDPCoordinates.answer MatrixElimination.primitives lam B (D, (equiv n).symm x) with
  | inl g =>
      simp only [hr, LSW.CorrectReply] at hc
      simp only [answer, hr, mapReply, LSW.CorrectReply]
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨y,hy,he⟩
        have hxy : (equiv n).symm x = y := by rw [← he]; simp
        exact hc.1 (hxy ▸ hy)
      · exact fun h => hc.2.1 ((equiv n).injective (by simpa using h))
      · rintro y ⟨z,hz,rfl⟩
        have h := hc.2.2 z hz
        have he : x = equiv n ((equiv n).symm x) := by simp
        change ⟪equiv n g, equiv n z - x⟫ ≤ 0
        rw [he, ← map_sub, LinearIsometryEquiv.inner_map_map]
        exact h
  | inr pair =>
      rcases pair with ⟨value,g⟩
      simp only [hr, LSW.CorrectReply] at hc
      simp only [answer, hr, mapReply, LSW.CorrectReply]
      refine ⟨⟨(equiv n).symm x,hc.1,by simp⟩,hc.2.1,?_⟩
      rintro y ⟨z,hz,rfl⟩
      have h := hc.2.2 z hz
      have he : x = equiv n ((equiv n).symm x) := by simp
      change objective lam (boundedObjective B D) (SDPCoordinates.lift ((equiv n).symm (equiv n z))) ≤
        value + ⟪equiv n g, equiv n z - x⟫
      rw [LinearIsometryEquiv.symm_apply_apply, he, ← map_sub, LinearIsometryEquiv.inner_map_map]
      exact h

theorem measurable_mapReply (n : ℕ) : Measurable (mapReply n) := by
  have hleft : Measurable (fun g : SDPCoordinates.Space n =>
      (Sum.inl (equiv n g) : LSW.Reply (Fin (n*n)))) :=
    measurable_inl.comp (equiv n).continuous.measurable
  have hright : Measurable (fun q : ℝ × SDPCoordinates.Space n =>
      (Sum.inr (q.1,equiv n q.2) : LSW.Reply (Fin (n*n)))) :=
    measurable_inr.comp (measurable_fst.prodMk ((equiv n).continuous.measurable.comp measurable_snd))
  exact hleft.sumElim hright

theorem measurable_answer (n : ℕ) (lam B : ℝ) : Measurable (answer (n := n) lam B) :=
  (measurable_mapReply n).comp ((SDPCoordinates.measurable_answer MatrixElimination.primitives lam B).comp
    (measurable_fst.prodMk ((equiv n).symm.continuous.measurable.comp measurable_snd)))

def oracle {n : ℕ} (hn : 2 ≤ n) {lam B : ℝ} (hlam : 0 ≤ lam) (hB : 0 ≤ B) :
    LSW.Oracle (problem hn hlam hB) where
  answer q := ⟨answer lam B q,
    (verifiedLinearAlgebra.oracleProgram n lam B (q.1, (equiv n).symm q.2)).steps⟩
  measurable_answer := measurable_answer n lam B
  correct := answer_correct hn hlam hB
  charge := SDPCoordinates.oracleCharge n
  cost_le q := verifiedLinearAlgebra.oracle_cost n lam B (q.1, (equiv n).symm q.2)

end DPCut.SDPFlat
