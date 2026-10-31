import DPCut.MatrixGaussianAlgorithm
import DPCut.CostedProgram

/-! Finite products implemented by independent scalar draws. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DPCut

def scalarProduct (μ : Measure ℝ) : (n : ℕ) → CostedLaw (Fin n → ℝ)
  | 0 => .pure (Fin.elim0 : Fin 0 → ℝ)
  | n+1 => (CostedLaw.sample μ 1).bind fun a =>
      (scalarProduct μ n).map (MatrixElimination.prepend a) 1

lemma scalarProduct_cost (μ : Measure ℝ) (n : ℕ) :
    (scalarProduct μ n).cost ≤ 2*n := by
  induction n with
  | zero => simp [scalarProduct, CostedLaw.pure]
  | succ n ih =>
    have h := CostedLaw.bind_cost_le (CostedLaw.sample μ 1)
      (fun a => (scalarProduct μ n).map (MatrixElimination.prepend a) 1) (le_refl _) (fun _ => add_le_add_right ih 1)
    calc
      _ ≤ 1 + (2*(n : ℝ≥0∞)+1) := h
      _ = 2*(n+1 : ℕ) := by push_cast; ring

lemma scalarProduct_law (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    (scalarProduct μ n).law = Measure.pi (fun _ : Fin n => μ) := by
  induction n with
  | zero =>
    change Measure.dirac (Fin.elim0 : Fin 0 → ℝ) = _
    exact (Measure.pi_of_empty _ _).symm
  | succ n ih =>
    have hc : Measurable (fun p : ℝ × (Fin n → ℝ) => MatrixElimination.prepend p.1 p.2) :=
      MatrixElimination.measurable_prepend n
    have hpi := ((measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm).map_eq
    have hp : (μ.prod (Measure.pi (fun _ : Fin n => μ))).map
        (fun p : ℝ × (Fin n → ℝ) => MatrixElimination.prepend p.1 p.2) = Measure.pi (fun _ : Fin (n+1) => μ) := by
      convert hpi using 1
      congr 1
      funext p i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [MatrixElimination.prepend, MeasurableEquiv.piFinSuccAbove_symm_apply]
    rw [scalarProduct, CostedLaw.bind_law]
    simp only [CostedLaw.sample, CostedLaw.map_law, ih]
    rw [← hp, Measure.prod, map_bind_eq Measurable.map_prodMk_left hc]
    congr 1
    funext a
    rw [Measure.map_map hc measurable_prodMk_left]
    rfl

def scalarFiniteProduct (ι : Type) [Fintype ι] (μ : Measure ℝ) : CostedLaw (ι → ℝ) :=
  (scalarProduct μ (Fintype.card ι)).map (fun z i => z ((Fintype.equivFin ι) i)) 0

lemma scalarFiniteProduct_law (ι : Type) [Fintype ι] (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (scalarFiniteProduct ι μ).law = Measure.pi (fun _ : ι => μ) := by
  rw [scalarFiniteProduct, CostedLaw.map_law, scalarProduct_law]
  convert (measurePreserving_piCongrLeft (fun _ : ι => μ) (Fintype.equivFin ι).symm).map_eq using 1
  congr 1
  funext z i
  simpa using (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι => ℝ)
    (Fintype.equivFin ι).symm z ((Fintype.equivFin ι) i)).symm

lemma scalarFiniteProduct_cost (ι : Type) [Fintype ι] (μ : Measure ℝ) :
    (scalarFiniteProduct ι μ).cost ≤ 2*Fintype.card ι := by
  simpa [scalarFiniteProduct, CostedLaw.map] using scalarProduct_cost μ (Fintype.card ι)

end DPCut
