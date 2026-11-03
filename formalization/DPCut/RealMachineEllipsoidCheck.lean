import DPCut.RealMachineEllipsoidBall

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open scoped RealInnerProductSpace

namespace DPCut.RealMachine.EllipsoidCode

open SDP

def checkCode (n base fuel : ℕ) : Code :=
  .seq (ballProgram n base) (checkProgram (n*n) base (TargetCode.ask n base) fuel)

def result (n base : ℕ) (s : State) : Option (EuclideanSpace ℝ (Fin (n*n))) :=
  if s.memory.boolean (slot (n*n) base 14) then some (center (n*n) base s) else none

def iterations {n : ℕ} (hn : 2 ≤ n) (lam B epsilon : ℝ) (hlam : 0 ≤ lam) (hB : 0 ≤ B) : ℕ :=
  EllipsoidOptimization.feasibilityBudget (SDPFlat.problem hn hlam hB) epsilon

theorem checkCode_steps (n base fuel : ℕ) :
    Steps (checkCode n base fuel)
      (20 * (n + 1) ^ 4 + 3 + fuel * (50000 * (n + 1) ^ 6 + 1000 * (n*n + 1) ^ 3 + 3)) := by
  simpa only [checkCode, Nat.add_assoc] using
    (ballProgram_steps n base).seq (checkProgram_steps (n*n) base (TargetCode.ask n base) _
      (TargetCode.ask_steps n base) fuel)

theorem checkCode_realizes {n : ℕ} (base : ℕ) (hn : 2 ≤ n) (lam B threshold epsilon : ℝ)
    (hlam : 0 ≤ lam) (hB : 0 ≤ B) (D : Weights n) (tapes : Tapes) (s : State)
    (hs : TargetCode.Context n base lam B threshold D s) :
    ResultRealized base (TargetCode.Context n base lam B threshold D)
      ((checkCode n base (iterations hn lam B epsilon hlam hB)).execute tapes s)
      (EllipsoidMethod.run
        ((TargetCode.script base hn lam B threshold hlam hB D).oracle.toSeparationOracle)
        (n*n + 1) (by exact_mod_cast (show 2 ≤ n*n + 1 by nlinarith))
        (iterations hn lam B epsilon hlam hB)
        (EllipsoidMethod.Ellipsoid.ball 0 (2*(n:ℝ)) (by exact_mod_cast (show 0 < 2*n by omega)))) := by
  have h := checkProgram_realizes (TargetCode.script base hn lam B threshold hlam hB D) (by nlinarith) tapes
    (iterations hn lam B epsilon hlam hB)
    ((ballProgram n base).execute tapes s) _
    (ballProgram_context base lam B threshold D tapes s hs) (ballProgram_value base hn tapes s)
  simpa only [checkCode, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using h

theorem checkCode_context {n : ℕ} (base : ℕ) (hn : 2 ≤ n) (lam B threshold epsilon : ℝ)
    (hlam : 0 ≤ lam) (hB : 0 ≤ B) (D : Weights n) (tapes : Tapes) (s : State)
    (hs : TargetCode.Context n base lam B threshold D s) :
    TargetCode.Context n base lam B threshold D
      ((checkCode n base (iterations hn lam B epsilon hlam hB)).execute tapes s) := by
  have h := checkCode_realizes base hn lam B threshold epsilon hlam hB D tapes s hs
  cases hrun : EllipsoidMethod.run
      ((TargetCode.script base hn lam B threshold hlam hB D).oracle.toSeparationOracle)
      (n*n + 1) (by exact_mod_cast (show 2 ≤ n*n + 1 by nlinarith))
      (iterations hn lam B epsilon hlam hB)
      (EllipsoidMethod.Ellipsoid.ball 0 (2*(n:ℝ)) (by exact_mod_cast (show 0 < 2*n by omega))) with
  | inl x => rw [hrun] at h; exact h.1
  | inr e => rw [hrun] at h; exact h.1

theorem checkCode_correct {n : ℕ} (base : ℕ) (hn : 2 ≤ n) (lam B threshold epsilon : ℝ)
    (hlam : 0 ≤ lam) (hB : 0 ≤ B) (D : Weights n) (tapes : Tapes) (s : State)
    (hs : TargetCode.Context n base lam B threshold D s) (he : 0 < epsilon) (hehalf : epsilon ≤ 1/2) :
    let output := (checkCode n base (iterations hn lam B epsilon hlam hB)).execute tapes s
    (∀ x, result n base output = some x →
      x ∈ EllipsoidOptimization.target (SDPFlat.problem hn hlam hB) D threshold) ∧
    (result n base output = none → ∀ y ∈ (SDPFlat.problem hn hlam hB).body,
      (SDPFlat.problem hn hlam hB).value D y < threshold + epsilon/4) := by
  let P := SDPFlat.problem hn hlam hB
  let O := SDPFlat.oracle hn hlam hB
  let script := TargetCode.script base hn lam B threshold hlam hB D
  let output := (checkCode n base (iterations hn lam B epsilon hlam hB)).execute tapes s
  have hr := checkCode_realizes base hn lam B threshold epsilon hlam hB D tapes s hs
  cases hrun : EllipsoidMethod.run script.oracle.toSeparationOracle (n*n + 1)
      (by exact_mod_cast (show 2 ≤ n*n + 1 by nlinarith)) (iterations hn lam B epsilon hlam hB)
      (EllipsoidMethod.Ellipsoid.ball 0 (2*(n:ℝ)) (by exact_mod_cast (show 0 < 2*n by omega))) with
  | inl x =>
      change ResultRealized base (TargetCode.Context n base lam B threshold D) output _ at hr
      rw [hrun] at hr
      have hflag : output.memory.boolean (slot (n*n) base 14) = true := hr.2.1
      have hcenter : center (n*n) base output = x.val := hr.2.2
      refine ⟨?_, ?_⟩
      · intro y hy
        change (if output.memory.boolean (slot (n*n) base 14) then some (center (n*n) base output) else none) = some y at hy
        rw [hflag] at hy
        have heq : center (n*n) base output = y := Option.some.inj hy
        rw [← heq, hcenter]
        exact x.property
      · intro hy
        change (if output.memory.boolean (slot (n*n) base 14) then some (center (n*n) base output) else none) = none at hy
        rw [hflag] at hy
        cases hy
  | inr remaining =>
      change ResultRealized base (TargetCode.Context n base lam B threshold D) output _ at hr
      rw [hrun] at hr
      have hflag : output.memory.boolean (slot (n*n) base 14) = false := hr.2.1
      refine ⟨?_, ?_⟩
      · intro y hy
        change (if output.memory.boolean (slot (n*n) base 14) then some (center (n*n) base output) else none) = some y at hy
        rw [hflag] at hy
        cases hy
      · intro _
        have hf : EllipsoidOptimization.check P O (by nlinarith) D threshold (epsilon/4) = .inr remaining := by
          simpa only [EllipsoidOptimization.check, EllipsoidOptimization.feasibilityBudget, iterations,
            P, O, script, TargetCode.script, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
            SDPFlat.problem, SDPFlat.reindex, SDPCoordinates.problem] using hrun
        exact EllipsoidOptimization.failed_threshold P O (by nlinarith) D threshold (epsilon/4)
          (by positivity) (by linarith) remaining hf

end DPCut.RealMachine.EllipsoidCode
