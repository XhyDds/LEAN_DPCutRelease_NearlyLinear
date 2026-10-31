import DPCut.Optimizer

/-! Continuity of the selected optimizer, needed for the adaptive kernels in Lemma 17. -/

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped BigOperators MatrixOrder

namespace DPCut

instance {n : ℕ} : MeasurableSpace (Mat n) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin n → ℝ))

instance {n : ℕ} : BorelSpace (Mat n) :=
  inferInstanceAs (BorelSpace (Fin n → Fin n → ℝ))

lemma continuous_objective_feasible {n : ℕ} (hn : 2 ≤ n) (lam : ℝ) :
    Continuous (fun p : Weights n × feasible n => objective lam p.1 p.2) := by
  unfold objective pairing fractionalQuery
  apply Continuous.add
  · apply continuous_finset_sum
    intro e _
    exact ((continuous_apply e).comp continuous_fst).mul
      ((continuous_const.sub ((continuous_subtype_val.comp continuous_snd).matrix_elem
        e.val.1 e.val.2)).div_const 2)
  · apply continuous_const.mul
    exact (continuous_subtype_val.comp continuous_snd).matrix_det.log
      (fun p => (feasible_posDef hn p.2.property).det_pos.ne')

/-- Compactness and uniqueness make the chosen optimizer continuous in the weights. -/
theorem continuous_optimizer {n : ℕ} (hn : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam) :
    Continuous (optimizer (n := n) lam) := by
  letI : CompactSpace (feasible n) := isCompact_iff_compactSpace.mp (feasible_compact hn)
  let f : Weights n → feasible n := fun D =>
    ⟨optimizer lam D, (optimizer_isOptimizer hn lam D).1⟩
  have hobj := continuous_objective_feasible hn lam
  have hgraph : IsClosed {p : Weights n × feasible n | f p.1 = p.2} := by
    have he : {p : Weights n × feasible n | f p.1 = p.2} =
        {p | ∀ Y : feasible n, objective lam p.1 Y ≤ objective lam p.1 p.2} := by
      ext p
      constructor
      · intro h Y
        have hv : optimizer lam p.1 = p.2 := congrArg Subtype.val h
        rw [← hv]
        exact (optimizer_isOptimizer hn lam p.1).2 Y Y.property
      · intro h
        apply Subtype.ext
        exact optimizer_unique hn hlam (optimizer_isOptimizer hn lam p.1)
          ⟨p.2.property, fun Y hY => h ⟨Y, hY⟩⟩
    rw [he]
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun Y => isClosed_le
      (hobj.comp (continuous_fst.prodMk continuous_const)) hobj
  have hf : Continuous f := by
    apply continuous_iff_isClosed.mpr
    intro s hs
    have he : f ⁻¹' s = Prod.fst ''
        ({p : Weights n × feasible n | f p.1 = p.2} ∩ Set.univ ×ˢ s) := by
      ext D
      constructor
      · intro h
        exact ⟨(D, f D), ⟨rfl, Set.mem_univ _, h⟩, rfl⟩
      · rintro ⟨⟨D', X⟩, ⟨h, _, hX⟩, rfl⟩
        change f D' ∈ s
        exact h ▸ hX
    rw [he]
    exact isClosedMap_fst_of_compactSpace _ (hgraph.inter (isClosed_univ.prod hs))
  exact continuous_subtype_val.comp hf

theorem measurable_optimizer {n : ℕ} (hn : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam) :
    Measurable (optimizer (n := n) lam) :=
  (continuous_optimizer hn hlam).measurable

end DPCut
