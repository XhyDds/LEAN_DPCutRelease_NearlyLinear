import DPCut.RealMachineSolverInit

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace DPCut.RealMachine.EllipsoidCode

open SDP

def decodeProgram (n base : ℕ) : Code :=
  liftCoordinatesProgram n (bestAddress n base) (slot (n*n) base 0)

def outputMatrix (n base : ℕ) (s : State) : Mat n :=
  readMatrix n (slot (n*n) base 0) s.memory

def solverProgram (n base fuel rounds : ℕ) : Code :=
  .seq (initializeProgram n base) (.seq (searchLoop n base fuel rounds) (decodeProgram n base))

def solverBound (n fuel rounds : ℕ) : ℕ :=
  12000 * (n+1)^6 +
    rounds * (100 * (n+1)^4 + fuel * (50000 * (n+1)^6 + 1000 * (n*n+1)^3 + 3)) + 13*n*n

theorem solverProgram_steps (n base fuel rounds : ℕ) :
    Steps (solverProgram n base fuel rounds) (solverBound n fuel rounds) := by
  exact ((initializeProgram_steps n base).seq
    ((searchLoop_steps n base fuel rounds).seq (liftCoordinates_steps n _ _))).mono
      (by unfold solverBound; ring_nf; omega)

theorem best_coordinates (n base : ℕ) (s : State) :
    readCoordinates n (bestAddress n base) s.memory =
      (SDPFlat.equiv n).symm (searchState n base s).best := by
  apply (SDPFlat.equiv n).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext k
  change s.memory.real (matrixAddress (bestAddress n base) (finProdFinEquiv.symm k)) =
    s.memory.real (vectorAddress (bestAddress n base) k)
  simp only [matrixAddress, vectorAddress, finProdFinEquiv.apply_symm_apply]

theorem decodeProgram_value (n base : ℕ) (tapes : Tapes) (s : State) :
    outputMatrix n base ((decodeProgram n base).execute tapes s) =
      SDPCoordinates.lift ((SDPFlat.equiv n).symm (searchState n base s).best) := by
  rw [← best_coordinates]
  exact liftCoordinates_value _ _ _ _ _ (by
    intro ij kl
    have hi := (matrix_range (bestAddress n base) ij).1
    have ho := (matrix_range (slot (n*n) base 0) kl).2
    have hs : n*n ≤ stride (n*n) := by
      unfold stride
      ring_nf
      omega
    have hslots := slot_lt_slot (n*n) base 1 15 (by decide)
    unfold bestAddress slot at *
    omega)

theorem accurate_coordinates {n : ℕ} (hn : 2 ≤ n) {lam B epsilon : ℝ}
    (hlam : 0 ≤ lam) (hB : 0 ≤ B) (D : Weights n) (x : EuclideanSpace ℝ (Fin (n*n)))
    (hx : LSW.Accurate (SDPFlat.problem hn hlam hB) epsilon D x) :
    LSW.Accurate (SDPCoordinates.problem hn hlam hB) epsilon D ((SDPFlat.equiv n).symm x) := by
  refine ⟨?_,?_⟩
  · obtain ⟨y,hy,he⟩ := hx.1
    rw [← he, LinearIsometryEquiv.symm_apply_apply]
    exact hy
  · intro y hy
    have h := hx.2 (SDPFlat.equiv n y) ⟨y,hy,rfl⟩
    simpa only [SDPFlat.problem, SDPFlat.reindex, LinearIsometryEquiv.symm_apply_apply] using h

theorem solverProgram_accurate {n : ℕ} (base : ℕ) (hn : 2 ≤ n) (lam B epsilon : ℝ)
    (hlam : 0 ≤ lam) (hB : 0 ≤ B) (he : 0 < epsilon) (hehalf : epsilon ≤ 1/2) (D : Weights n)
    (tapes : Tapes) (s : State) (hs : OptimizerContext n base lam B epsilon D s) :
    let output := (solverProgram n base (iterations hn lam B epsilon hlam hB)
      (EllipsoidOptimization.rounds (SDPFlat.problem hn hlam hB) epsilon)).execute tapes s
    outputMatrix n base output ∈ feasible n ∧
      optimum lam (boundedObjective B D) - objective lam (boundedObjective B D) (outputMatrix n base output) ≤ epsilon := by
  let first := (initializeProgram n base).execute tapes s
  let second := (searchLoop n base (iterations hn lam B epsilon hlam hB)
    (EllipsoidOptimization.rounds (SDPFlat.problem hn hlam hB) epsilon)).execute tapes first
  have hi := initializeProgram_valid base hn lam B epsilon hlam hB D tapes s hs
  have ha := searchLoop_accurate base hn lam B epsilon hlam hB he hehalf D tapes first hi.1 hi.2.1 hi.2.2.le
  have hc := accurate_coordinates hn hlam hB D (searchState n base second).best ha
  have hg := (SDPCoordinates.accurate_iff hn hlam hB epsilon D _).mp hc
  change outputMatrix n base ((decodeProgram n base).execute tapes second) ∈ feasible n ∧
    optimum lam (boundedObjective B D) -
      objective lam (boundedObjective B D)
        (outputMatrix n base ((decodeProgram n base).execute tapes second)) ≤ epsilon
  rw [decodeProgram_value]
  exact ⟨hg.1.2,hg.2⟩

end DPCut.RealMachine.EllipsoidCode
