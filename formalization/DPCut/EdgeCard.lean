import DPCut.Definitions

/-! A simple bound on the number of unordered edges. -/
set_option autoImplicit false
namespace DPCut

lemma edge_card_le_square (n : ℕ) : (Fintype.card (Edge n) : ℝ) ≤ (n : ℝ) ^ 2 := by
  have h := Fintype.card_subtype_le (fun p : Fin n × Fin n => p.1 < p.2)
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  have h' : Fintype.card (Edge n) ≤ n ^ 2 := by simpa [Edge, pow_two] using h
  exact_mod_cast h'

end DPCut
