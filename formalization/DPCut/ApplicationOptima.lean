import DPCut.PartitionTransfer
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-! Attainment and order properties of the finite application objectives. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DPCut

lemma constrainedOptimum_exists {n : ℕ} (w : Weights n) {F : Set (Finset (Fin n))}
    (hF : F.Nonempty) : ∃ S ∈ F, cut w S = constrainedOptimum w F :=
  (hF.image (cut w)).csInf_mem ((Set.toFinite F).image (cut w))

lemma constrainedOptimum_le {n : ℕ} (w : Weights n) {F : Set (Finset (Fin n))}
    {S : Finset (Fin n)} (hS : S ∈ F) : constrainedOptimum w F ≤ cut w S :=
  csInf_le ((Set.toFinite F).image (cut w)).bddBelow ⟨S, hS, rfl⟩

lemma partitions_le_nonempty {n k : ℕ} (hn : 0 < n) (hk : 1 ≤ k) :
    {π : Partition n | clusterCount π ≤ k}.Nonempty := by
  classical
  let v : Fin n := ⟨0, hn⟩
  refine ⟨fun _ => v, ?_⟩
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  change (Finset.univ.image (fun _ : Fin n => v)).card ≤ k
  calc
    _ ≤ ({v} : Finset (Fin n)).card := Finset.card_le_card (by
      intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      simp)
    _ ≤ k := by simpa using hk

lemma maxKOptimum_exists {n k : ℕ} (hn : 0 < n) (hk : 1 ≤ k) (w : Weights n) :
    ∃ π : Partition n, clusterCount π ≤ k ∧ partitionCut w π = maxKOptimum w k :=
  ((partitions_le_nonempty hn hk).image (partitionCut w)).csSup_mem
    ((Set.toFinite _).image (partitionCut w))

lemma partitionCut_le_maxKOptimum {n k : ℕ} (w : Weights n) {π : Partition n}
    (hπ : clusterCount π ≤ k) : partitionCut w π ≤ maxKOptimum w k :=
  le_csSup ((Set.toFinite _).image (partitionCut w)).bddAbove ⟨π, hπ, rfl⟩

lemma ccOptimum_exists {n : ℕ} (w : Weights n) : ∃ π : Partition n, ccCost w π = ccOptimum w := by
  haveI : Nonempty (Partition n) := ⟨id⟩
  exact (Set.range_nonempty (ccCost w)).csInf_mem (Set.finite_range _)

lemma ccOptimum_le {n : ℕ} (w : Weights n) (π : Partition n) : ccOptimum w ≤ ccCost w π :=
  csInf_le (Set.finite_range (ccCost w)).bddBelow ⟨π, rfl⟩

lemma ccOptimumK_exists {n k : ℕ} (hn : 0 < n) (hk : 1 ≤ k) (w : Weights n) :
    ∃ π : Partition n, clusterCount π ≤ k ∧ ccCost w π = ccOptimumK w k :=
  ((partitions_le_nonempty hn hk).image (ccCost w)).csInf_mem ((Set.toFinite _).image (ccCost w))

theorem max_k_transfer : MaxKTransferStatement := by
  intro n k hn hk w h η A ρ π hw hh hη hη1 hA hρ _hρ1 hc hπ happrox
  obtain ⟨πstar, hstar, hopt⟩ := maxKOptimum_exists (k := k) (by omega) (by omega) w
  have h₁ := (abs_le.mp (label_cut_transfer hc π)).2
  have h₂ := (abs_le.mp (label_cut_transfer hc πstar)).1
  change partitionCut h π - partitionCut w π ≤ η * partitionCut w π + 2 * A at h₁
  change -(η * partitionCut w πstar + 2 * A) ≤ partitionCut h πstar - partitionCut w πstar at h₂
  rw [hopt] at h₂
  have hs := partitionCut_le_maxKOptimum h hstar
  have hr := mul_le_mul_of_nonneg_left hs hρ
  have hr' := mul_le_mul_of_nonneg_left h₂ hρ
  have hp : 0 < 1 + η := by linarith
  convert (show (ρ * (1 - η) * maxKOptimum w k - 2 * (ρ + 1) * A) / (1 + η) ≤
      partitionCut w π from (div_le_iff₀ hp).mpr (by nlinarith)) using 1
  ring

end DPCut
