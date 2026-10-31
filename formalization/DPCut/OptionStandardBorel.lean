import DPCut.ProbabilityProgramming
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! The option-valued oracle output is a standard Borel space. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace DPCut
attribute [local instance] Classical.propDecidable
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

lemma standardBorel_of_equiv [StandardBorelSpace β] (e : α ≃ᵐ β) : StandardBorelSpace α := by
  letI := upgradeStandardBorel β
  letI : TopologicalSpace α := TopologicalSpace.induced e inferInstance
  letI : PolishSpace α := e.toEquiv.polishSpace_induced
  letI : BorelSpace α := e.measurableEmbedding.borelSpace ⟨rfl⟩
  infer_instance

def optionCode (a : α) (o : Option α) : α × Bool :=
  o.elim (a, false) (fun x => (x, true))

def optionCodeEquiv (a : α) : Option α ≃ᵐ {p : α × Bool // p.2 = true ∨ p.1 = a} where
  toFun o := ⟨optionCode a o, by cases o <;> simp [optionCode]⟩
  invFun p := if p.val.2 then some p.val.1 else none
  left_inv := by intro o; cases o <;> rfl
  right_inv := by
    rintro ⟨⟨x, b⟩, hb⟩
    cases b
    · simp only [Bool.false_eq_true, false_or] at hb
      subst x
      rfl
    · rfl
  measurable_toFun := by
    apply Measurable.subtype_mk
    exact measurable_option_elim _ (measurable_id.prodMk measurable_const)
  measurable_invFun := by
    exact Measurable.ite
      ((measurable_snd.comp measurable_subtype_coe) (measurableSet_singleton true))
      (measurable_some.comp (measurable_fst.comp measurable_subtype_coe)) measurable_const

instance option_standardBorel [StandardBorelSpace α] [Inhabited α] : StandardBorelSpace (Option α) := by
  have hs : MeasurableSet {p : α × Bool | p.2 = true ∨ p.1 = (default : α)} :=
    (measurable_snd (measurableSet_singleton true)).union
      (measurable_fst (measurableSet_singleton default))
  letI : StandardBorelSpace {p : α × Bool // p.2 = true ∨ p.1 = (default : α)} := hs.standardBorel
  exact standardBorel_of_equiv (optionCodeEquiv (default : α))

end DPCut
