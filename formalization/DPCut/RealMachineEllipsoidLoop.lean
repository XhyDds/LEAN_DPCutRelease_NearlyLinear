import DPCut.RealMachineEllipsoidRefinement
import DPCut.RealMachineWriteCeiling

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Metric
open scoped RealInnerProductSpace

namespace DPCut.RealMachine.EllipsoidCode

open SDP EllipsoidMethod

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

def checkLoop (m base : ℕ) (ask : Code) : ℕ → Code
  | 0 => .skip
  | fuel + 1 =>
      .seq ask (.branch (readBoolean (slot m base 14)) .skip
        (.seq (cutProgram m base) (checkLoop m base ask fuel)))

def checkProgram (m base : ℕ) (ask : Code) (fuel : ℕ) : Code :=
  .seq (writeBoolean (slot m base 14) (.boolean false)) (checkLoop m base ask fuel)

theorem checkLoop_steps (m base : ℕ) (ask : Code) (cost : ℕ) (ha : Steps ask cost) (fuel : ℕ) :
    Steps (checkLoop m base ask fuel) (fuel * (cost + 1000 * (m + 1) ^ 3 + 3)) := by
  induction fuel with
  | zero => simpa only [checkLoop, Nat.zero_mul] using Steps.skip
  | succ fuel ih =>
      have h := ha.seq (Steps.branch (readBoolean (slot m base 14)) Steps.skip ((cutProgram_steps m base).seq ih))
      exact h.mono (by simp only [Expr.operations, readBoolean, Nat.zero_max]; ring_nf; omega)

theorem checkProgram_steps (m base : ℕ) (ask : Code) (cost : ℕ) (ha : Steps ask cost) (fuel : ℕ) :
    Steps (checkProgram m base ask fuel) (3 + fuel * (cost + 1000 * (m + 1) ^ 3 + 3)) := by
  exact (Steps.boolean (.natural (slot m base 14)) (.boolean false)).seq (checkLoop_steps _ _ _ _ ha fuel)

def DecisionRealized {K : Set E} (base : ℕ) (e : Ellipsoid E) (s : State) : PointDecision K e.center → Prop
  | .accept _ => s.memory.boolean (slot m base 14) = true ∧ Matches m base s e
  | .separate g _ _ => s.memory.boolean (slot m base 14) = false ∧ Matches m base s e ∧ normal m base s = g

/-- The oracle's runtime is a restricted instruction program. This specification
contains no self-reported time and no operation returning a chosen optimum. -/
structure PointScript (m base : ℕ) (K : Set (EuclideanSpace ℝ (Fin m))) (context : State → Prop) where
  code : Code
  oracle : PointOracle K
  context_real : ∀ s t, s.memory.real = t.memory.real → context s → context t
  answer : ∀ tapes s e, context s → Matches m base s e →
    let result := code.execute tapes s
    context result ∧ DecisionRealized base e result (oracle e.center)
  cut_context : ∀ tapes s, context s → context ((cutProgram m base).execute tapes s)

def ResultRealized {K : Set E} (base : ℕ) (context : State → Prop) (s : State) :
    {x // x ∈ K} ⊕ Ellipsoid E → Prop
  | .inl x => context s ∧ s.memory.boolean (slot m base 14) = true ∧ center m base s = x.val
  | .inr e => context s ∧ s.memory.boolean (slot m base 14) = false ∧ Matches m base s e

theorem checkLoop_realizes {base : ℕ} {K : Set E} {context : State → Prop}
    (script : PointScript m base K context) (hm : 1 ≤ m) (tapes : Tapes) (fuel : ℕ)
    (s : State) (e : Ellipsoid E) (hc : context s) (he : Matches m base s e)
    (hf : s.memory.boolean (slot m base 14) = false) :
    ResultRealized base context ((checkLoop m base script.code fuel).execute tapes s)
      (run script.oracle.toSeparationOracle (m + 1) (by exact_mod_cast Nat.succ_le_succ hm) fuel e) := by
  induction fuel generalizing s e with
  | zero => exact ⟨hc, hf, he⟩
  | succ fuel ih =>
      let first := script.code.execute tapes s
      let next := first.tick ((readBoolean (slot m base 14)).operations + 1)
      have hs := script.answer tapes s e hc he
      change context first ∧ DecisionRealized base e first (script.oracle e.center) at hs
      have hnext : context next := script.context_real first next rfl hs.1
      cases ho : script.oracle e.center with
      | accept feasible =>
          have hr : first.memory.boolean (slot m base 14) = true ∧ Matches m base first e := by
            simpa only [ho, DecisionRealized] using hs.2
          change ResultRealized base context
            (if first.memory.boolean (slot m base 14) then next else
              (checkLoop m base script.code fuel).execute tapes ((cutProgram m base).execute tapes next)) _
          simp only [hr.1, Bool.true_eq, ite_true, run, PointOracle.toSeparationOracle, ho, ResultRealized]
          exact ⟨hnext, hr.1, hr.2.1⟩
      | separate g hg valid =>
          have hr : first.memory.boolean (slot m base 14) = false ∧ Matches m base first e ∧ normal m base first = g := by
            simpa only [ho, DecisionRealized] using hs.2
          have hnormal : normal m base next = g := hr.2.2
          have hnonzero : normal m base next ≠ 0 := hnormal ▸ hg
          have hshape := cutProgram_value tapes next m base hm e hr.2.1 hnonzero
          have hbool : ((cutProgram m base).execute tapes next).memory.boolean (slot m base 14) = false :=
            congrFun (Code.realOnly_control _ (cutProgram_realOnly m base) tapes next).2 _ |>.trans hr.1
          have hctx := script.cut_context tapes next hnext
          have hrec := ih ((cutProgram m base).execute tapes next)
            (e.cut (m + 1) (by exact_mod_cast Nat.succ_le_succ hm)
              (e.unitNormal (normal m base next)) (e.unitNormal_norm hnonzero)) hctx hshape hbool
          change ResultRealized base context
            (if first.memory.boolean (slot m base 14) then next else
              (checkLoop m base script.code fuel).execute tapes ((cutProgram m base).execute tapes next)) _
          simp only [hr.1, Bool.false_eq_true, ite_false, run, PointOracle.toSeparationOracle, ho]
          simpa only [hnormal] using hrec

theorem checkProgram_realizes {base : ℕ} {K : Set E} {context : State → Prop}
    (script : PointScript m base K context) (hm : 1 ≤ m) (tapes : Tapes) (fuel : ℕ)
    (s : State) (e : Ellipsoid E) (hc : context s) (he : Matches m base s e) :
    ResultRealized base context ((checkProgram m base script.code fuel).execute tapes s)
      (run script.oracle.toSeparationOracle (m + 1) (by exact_mod_cast Nat.succ_le_succ hm) fuel e) := by
  let first := (writeBoolean (slot m base 14) (.boolean false)).execute tapes s
  have hfirst : context first := script.context_real s first rfl hc
  have he' : Matches m base first e := he
  exact checkLoop_realizes script hm tapes fuel first e hfirst he'
    (writeBoolean_value _ _ _ _)

end DPCut.RealMachine.EllipsoidCode
