import DPCut.RealMachineTargetData

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace DPCut.RealMachine.TargetCode

open SDP EllipsoidCode

theorem gradientReject_floor (n base : ℕ) : (gradientReject n base).RealWriteFloor (slot (n*n) base 2) := by
  have hw : slot (n*n) base 2 ≤ workspace n base := (workspace_after _ _ _ (by decide)).le
  have hnorm : slot (n*n) base 2 ≤ slot n (workspace n base) 11 + 1 :=
    (hw.trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
  exact ⟨⟨floor_sum _ _ _ hnorm, floor_writeReal _ _ _ hnorm⟩,
    ⟨floor_array _ _ _ (fun i => (vector_range (slot (n*n) base 2) i).1),
      floor_array _ _ _ (fun i => (vector_range (slot (n*n) base 2) i).1)⟩, trivial⟩

theorem ask_floor (n base : ℕ) : (ask n base).RealWriteFloor (slot (n*n) base 2) := by
  have hw : slot (n*n) base 2 ≤ workspace n base := (workspace_after _ _ _ (by decide)).le
  have hs (k : ℕ) : slot (n*n) base 2 ≤ slot n (workspace n base) k := hw.trans (Nat.le_add_right _ _)
  exact ⟨floor_matrixMap _ _ _ _ (hs _), SDP.oracleProgram_floor _ _ _ (hs _),
    ⟨⟨trivial, gradientReject_floor _ _⟩, floor_array _ _ _ (fun i => (vector_range (slot (n*n) base 2) i).1), trivial⟩⟩

theorem ask_matches (n base : ℕ) (tapes : Tapes) (s : State)
    (e : EllipsoidMethod.Ellipsoid (EuclideanSpace ℝ (Fin (n*n)))) (h : Matches (n*n) base s e) :
    Matches (n*n) base ((ask n base).execute tapes s) e := by
  refine ⟨?_, ?_⟩
  · rw [← h.1]
    ext i
    exact Code.realWriteFloor_frame _ _ (ask_floor n base) tapes s _
      (vector_before_slot (n*n) base 0 2 (by decide) i)
  · rw [← h.2]
    congr 1
    funext i j
    exact Code.realWriteFloor_frame _ _ (ask_floor n base) tapes s _
      (matrix_before_slot (n*n) base 1 2 (by decide) (i,j))

theorem norm_context (n base : ℕ) (lam B threshold : ℝ) (D : Weights n) (tapes : Tapes) (s : State)
    (hs : Context n base lam B threshold D s) :
    Context n base lam B threshold D
      ((coordinateNormProgram n (slot n (workspace n base) 3) (slot n (workspace n base) 11 + 1)).execute tapes s) := by
  refine context_of_low n base lam B threshold D s _ ?_ hs
  intro address ha
  have hnorm : slot n (workspace n base) 3 ≤ slot n (workspace n base) 11 + 1 :=
    (slot_lt_slot n (workspace n base) 3 11 (by decide)).le.trans (Nat.le_add_right _ _)
  have hf : (coordinateNormProgram n (slot n (workspace n base) 3) (slot n (workspace n base) 11 + 1)).RealWriteFloor
      (slot n (workspace n base) 3) := ⟨floor_sum _ _ _ hnorm, floor_writeReal _ _ _ hnorm⟩
  exact Code.realWriteFloor_frame _ _ hf tapes s _ ha

theorem gradientReject_context (n base : ℕ) (lam B threshold : ℝ) (D : Weights n) (tapes : Tapes) (s : State)
    (hs : Context n base lam B threshold D s) :
    Context n base lam B threshold D ((gradientReject n base).execute tapes s) := by
  let first := (coordinateNormProgram n (slot n (workspace n base) 3) (slot n (workspace n base) 11 + 1)).execute tapes s
  let next := first.tick ((Expr.eq (readReal (slot n (workspace n base) 11 + 1)) (.rational 0)).operations + 1)
  have hfirst := norm_context n base lam B threshold D tapes s hs
  have hnext : Context n base lam B threshold D next := context_real _ _ _ _ _ _ _ _ rfl hfirst
  simp only [gradientReject, Code.execute]
  split
  · exact context_real _ _ _ _ _ _ _ _ rfl (fixedNormal_context n base lam B threshold D tapes next hnext)
  · exact context_real _ _ _ _ _ _ _ _ rfl (copyNormal_context n base lam B threshold D tapes next true hnext)

theorem decideReply_context (n base : ℕ) (lam B threshold : ℝ) (D : Weights n) (tapes : Tapes) (s : State)
    (hs : Context n base lam B threshold D s) :
    Context n base lam B threshold D ((decideReply n base).execute tapes s) := by
  simp only [decideReply, Code.execute]
  split
  · split
    · exact context_real _ _ _ _ _ _ _ _ rfl hs
    · apply gradientReject_context
      exact context_real _ _ _ _ _ _ _ _ rfl hs
  · exact context_real _ _ _ _ _ _ _ _ rfl
      (copyNormal_context n base lam B threshold D tapes _ false (context_real _ _ _ _ _ _ _ _ rfl hs))

theorem ask_context (n base : ℕ) (lam B threshold : ℝ) (D : Weights n) (tapes : Tapes) (s : State)
    (hs : Context n base lam B threshold D s) :
    Context n base lam B threshold D ((ask n base).execute tapes s) := by
  let first := (copyPoint n base).execute tapes s
  let second := (SDP.oracleProgram n (workspace n base)).execute tapes first
  have hfirst := copyPoint_context n base lam B threshold D tapes s hs
  have hsecond : Context n base lam B threshold D second := context_of_low _ _ _ _ _ _ _ _ (by
    exact Code.realWriteFloor_frame _ _ (SDP.oracleProgram_floor n (workspace n base) _ le_rfl) tapes first) hfirst
  exact decideReply_context n base lam B threshold D tapes second hsecond

end DPCut.RealMachine.TargetCode
