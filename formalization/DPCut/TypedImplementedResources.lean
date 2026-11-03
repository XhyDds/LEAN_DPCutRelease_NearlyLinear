import DPCut.TypedProgramPolynomial
import DPCut.TypedPublicSchedules
import DPCut.TypedReleaseExecution

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut.TypedMachine

theorem implementedRun_bound {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) (w : Weights n) :
    ∀ᵐ r ∂implementedRun hn p hp w,
      r.2.1 ≤ (calibrationCommand n).operations+(releaseProgram hn p hp).operations ∧
      r.2.2 ≤ (releaseProgram hn p hp).solverCalls := by
  rw [implementedRun_eq]
  have hm : Measurable (fun output : Outcome (weightType n) =>
      (decodeWeights output.1,(calibrationCommand n).operations+output.2.1,output.2.2)) :=
    ((measurable_decodeWeights n).comp measurable_fst).prodMk (by fun_prop)
  have hs : MeasurableSet {r : ReleaseOutcome n |
      r.2.1 ≤ (calibrationCommand n).operations+(releaseProgram hn p hp).operations ∧
        r.2.2 ≤ (releaseProgram hn p hp).solverCalls} :=
    (measurableSet_le (measurable_fst.comp measurable_snd) measurable_const).inter
      (measurableSet_le (measurable_snd.comp measurable_snd) measurable_const)
  apply (ae_map_iff hm.aemeasurable hs).mpr
  refine ((releaseProgram hn p hp).bound (releaseInput n p w)).mono ?_
  intro r hr
  exact ⟨Nat.add_le_add_left hr.1 _,hr.2⟩

theorem implementedRun_calls {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) (w : Weights n) :
    ∀ᵐ r ∂implementedRun hn p hp w,
      r.2.2 ≤ 2*Fintype.card (Edge n)*(fullRunConfig n (precisionParameters p)).T1*
        (fullRunConfig n (precisionParameters p)).T2 := by
  refine (implementedRun_bound hn p hp w).mono ?_
  intro r hr
  have hc := fullCommand_calls (releaseSolver hn p hp)
    (fullRunConfig n (precisionParameters p)).oracle.k (fullRunConfig n (precisionParameters p)).oracle.K
    (fullRunConfig n (precisionParameters p)).T1 (fullRunConfig n (precisionParameters p)).T2
    (runTermsOf (dataInput n)) (realPublic (dataInput n) 9) (realPublic (dataInput n) 10)
    (realPublic (dataInput n) 11) (newest : Term (releaseContext n) (weightType n))
  have heq : (releaseProgram hn p hp).solverCalls =
      2*Fintype.card (Edge n)*(fullRunConfig n (precisionParameters p)).T1*
        (fullRunConfig n (precisionParameters p)).T2 := by
    change (fullCommand _ _ _ _ _ _ _ _ _ _).solverCalls = _
    rw [hc]
    ring
  exact hr.2.trans_eq heq

theorem implemented_budget_polynomial :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ n (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid),
      (((calibrationCommand n).operations+(releaseProgram hn p hp).operations+
        (releaseProgram hn p hp).solverCalls:ℕ):ℝ) ≤ C*runtimeScale n p^d := by
  have hpoly := implemented_operations_polynomial.add implemented_calls_polynomial
  obtain ⟨C,hC,d,hbound⟩ := hpoly
  refine ⟨C,hC,d,?_⟩
  intro n hn p hp
  have h := hbound n hn p hp
  simp only [totalInstructions,dif_pos (And.intro hn hp)] at h
  have hnonnegative : 0 ≤ C*runtimeScale n p^d := by
    have hscale := (runtimeScale_bounds (n:=n) hp).2.2
    positivity
  have hto := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [ENNReal.toReal_natCast,ENNReal.toReal_ofReal hnonnegative] using hto

def ResourceBound (n : ℕ) (p : Parameters) (C : ℝ) (d : ℕ) (r : ReleaseOutcome n) : Prop :=
  (r.2.1:ℝ) ≤ C*runtimeScale n p^d ∧ (r.2.2:ℝ) ≤ C*runtimeScale n p^d ∧
    r.2.2 ≤ 2*Fintype.card (Edge n)*(fullRunConfig n (precisionParameters p)).T1*
      (fullRunConfig n (precisionParameters p)).T2

theorem resourceBound_of_budget {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) (C : ℝ) (d : ℕ)
    (hreal : (((calibrationCommand n).operations+(releaseProgram hn p hp).operations+
      (releaseProgram hn p hp).solverCalls:ℕ):ℝ) ≤ C*runtimeScale n p^d)
    (r : ReleaseOutcome n)
    (hr : r.2.1 ≤ (calibrationCommand n).operations+(releaseProgram hn p hp).operations ∧
      r.2.2 ≤ (releaseProgram hn p hp).solverCalls) :
    ResourceBound n p C d r := by
  have hs : (r.2.1:ℝ)+(r.2.2:ℝ) ≤ C*runtimeScale n p^d := by
    have hnat := Nat.add_le_add hr.1 hr.2
    have hcast : ((r.2.1+r.2.2:ℕ):ℝ) ≤
        (((calibrationCommand n).operations+(releaseProgram hn p hp).operations+
          (releaseProgram hn p hp).solverCalls:ℕ):ℝ) := Nat.cast_le.mpr hnat
    exact (by simpa only [Nat.cast_add] using hcast.trans hreal)
  have hc : (releaseProgram hn p hp).solverCalls =
      2*Fintype.card (Edge n)*(fullRunConfig n (precisionParameters p)).T1*
        (fullRunConfig n (precisionParameters p)).T2 := by
    simp only [releaseProgram,fullCommand_calls]
    ring
  exact ⟨by linarith [Nat.cast_nonneg (α:=ℝ) r.2.2],
    by linarith [Nat.cast_nonneg (α:=ℝ) r.2.1],hr.2.trans_eq hc⟩

theorem implemented_resources :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ n (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) (w : Weights n),
      (∀ r, ImplementedExecution hn p hp w r → ResourceBound n p C d r) ∧
        ∀ᵐ r ∂implementedRun hn p hp w, ResourceBound n p C d r := by
  obtain ⟨C,hC,d,hmajor⟩ := implemented_budget_polynomial
  refine ⟨C,hC,d,?_⟩
  intro n hn p hp w
  refine ⟨?_,?_⟩
  · intro r hr
    exact resourceBound_of_budget hn p hp C d (hmajor n hn p hp) r (implementedExecution_bound hn p hp w r hr)
  · exact (implementedRun_bound hn p hp w).mono
      (fun r hr => resourceBound_of_budget hn p hp C d (hmajor n hn p hp) r hr)

theorem implementedRun_resources :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ n (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) (w : Weights n),
      ∀ᵐ r ∂implementedRun hn p hp w, ResourceBound n p C d r := by
  obtain ⟨C,hC,d,h⟩ := implemented_resources
  exact ⟨C,hC,d,fun n hn p hp w => (h n hn p hp w).2⟩

end DPCut.TypedMachine
