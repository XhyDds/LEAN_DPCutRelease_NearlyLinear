import DPCut.PrivateBalancedCuts
import DPCut.EmbeddedGraphs

/-! The public isolated-vertex padding used for odd-order bisection in C.4. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DPCut
attribute [local instance] Classical.propDecidable

def NearBisection {n : ℕ} (S : Finset (Fin n)) : Prop :=
  S.card ≤ n - S.card + 1 ∧ n - S.card ≤ S.card + 1

def ExactBisection {n : ℕ} (S : Finset (Fin n)) : Prop := 2 * S.card = n

def extendEdge {n : ℕ} (e : Edge n) : Edge (n + 1) :=
  ⟨(e.val.1.castSucc, e.val.2.castSucc), e.property⟩

def addIsolatedVertex {n : ℕ} (w : Weights n) : Weights (n + 1) := embedWeights extendEdge w

def restrictCut {n : ℕ} (S : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun v => v.castSucc ∈ S

lemma mem_restrictCut {n : ℕ} {S : Finset (Fin (n + 1))} {v : Fin n} :
    v ∈ restrictCut S ↔ v.castSucc ∈ S := by simp [restrictCut]

lemma cut_addIsolatedVertex {n : ℕ} (w : Weights n) (S : Finset (Fin (n + 1))) :
    cut (addIsolatedVertex w) S = cut w (restrictCut S) := by
  rw [cut, addIsolatedVertex, pairing_embedWeights]
  apply Finset.sum_congr rfl
  intro e he
  simp only [cutQuery, extendEdge, mem_restrictCut]

lemma addIsolatedVertex_nonnegative {n : ℕ} {w : Weights n} (hw : Nonnegative w) :
    Nonnegative (addIsolatedVertex w) := by
  intro e
  apply Finset.sum_nonneg
  intro f hf
  split_ifs <;> first | exact hw f | exact le_refl 0

lemma allCuts_addIsolatedVertex {n : ℕ} {w h : Weights n} {η E : ℝ} (hc : AllCuts w h η E) :
    AllCuts (addIsolatedVertex w) (addIsolatedVertex h) η E := by
  intro S
  simpa only [cut_addIsolatedVertex] using hc (restrictCut S)

lemma restrictCut_lift {n : ℕ} (S : Finset (Fin n)) :
    restrictCut (S.map Fin.castSuccEmb) = S := by
  ext v
  simp [mem_restrictCut]

lemma restrictCut_insert_last {n : ℕ} (S : Finset (Fin (n + 1))) :
    restrictCut (insert (Fin.last n) S) = restrictCut S := by
  ext v
  simp [mem_restrictCut, Fin.castSucc_ne_last]

lemma last_not_mem_lift {n : ℕ} (S : Finset (Fin n)) : Fin.last n ∉ S.map Fin.castSuccEmb := by
  simp only [Finset.mem_map, Fin.coe_castSuccEmb, not_exists, not_and]
  intro v hv
  exact Fin.castSucc_ne_last v

lemma cut_split_last {n : ℕ} (S : Finset (Fin (n + 1))) :
    S = if Fin.last n ∈ S then insert (Fin.last n) ((restrictCut S).map Fin.castSuccEmb)
      else (restrictCut S).map Fin.castSuccEmb := by
  ext v
  rcases Fin.eq_castSucc_or_eq_last v with ⟨u, rfl⟩ | rfl
  · split_ifs <;> simp [mem_restrictCut, Fin.castSucc_ne_last]
  · split_ifs <;> simp_all

lemma restrictCut_card {n : ℕ} (S : Finset (Fin (n + 1))) :
    S.card = (restrictCut S).card + if Fin.last n ∈ S then 1 else 0 := by
  conv_lhs => rw [cut_split_last S]
  split_ifs <;> simp

lemma restrict_exact_bisection {n : ℕ} {S : Finset (Fin (n + 1))} (hS : ExactBisection S) :
    NearBisection (restrictCut S) := by
  have hc := restrictCut_card S
  unfold ExactBisection at hS
  unfold NearBisection
  split_ifs at hc <;> omega

lemma lift_near_bisection {n : ℕ} (hn : n % 2 = 1) {S : Finset (Fin n)} (hS : NearBisection S) :
    ∃ R : Finset (Fin (n + 1)), ExactBisection R ∧ restrictCut R = S := by
  have hc : S.card ≤ n := (Finset.card_le_univ S).trans_eq (Fintype.card_fin n)
  unfold NearBisection at hS
  by_cases hsmall : S.card ≤ n - S.card
  · refine ⟨insert (Fin.last n) (S.map Fin.castSuccEmb), ?_, ?_⟩
    · unfold ExactBisection
      rw [Finset.card_insert_of_notMem (last_not_mem_lift S), Finset.card_map]
      omega
    · rw [restrictCut_insert_last, restrictCut_lift]
  · refine ⟨S.map Fin.castSuccEmb, ?_, restrictCut_lift S⟩
    unfold ExactBisection
    rw [Finset.card_map]
    omega

lemma bisection_family_nonempty (n : ℕ) : {S : Finset (Fin n) | NearBisection S}.Nonempty := by
  refine ⟨halfSubset Finset.univ, ?_⟩
  have hh := halfSubset_even (Finset.univ : Finset (Fin n))
  simpa only [Set.mem_setOf_eq, NearBisection, halfSubset_sdiff_card, halfSubset_card, Finset.card_univ, Fintype.card_fin] using hh

lemma odd_bisection_optimum {n : ℕ} (hn : n % 2 = 1) (w : Weights n) :
    constrainedOptimum (addIsolatedVertex w) {S | ExactBisection S} =
      constrainedOptimum w {S | NearBisection S} := by
  obtain ⟨S, hS, heq⟩ := constrainedOptimum_exists w (bisection_family_nonempty n)
  obtain ⟨R, hR, hr⟩ := lift_near_bisection hn hS
  have hne : {R : Finset (Fin (n + 1)) | ExactBisection R}.Nonempty := ⟨R, hR⟩
  obtain ⟨Rstar, hstar, hopt⟩ := constrainedOptimum_exists (addIsolatedVertex w) hne
  apply le_antisymm
  · have hh := constrainedOptimum_le (addIsolatedVertex w) (F := {S | ExactBisection S}) hR
    simpa only [cut_addIsolatedVertex, hr, heq] using hh
  · rw [← hopt, cut_addIsolatedVertex]
    exact constrainedOptimum_le w (restrict_exact_bisection hstar)

end DPCut
