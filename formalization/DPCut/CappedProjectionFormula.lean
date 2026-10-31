import DPCut.CappedWaterfill

/-! A finite formula for the water-filling scale. It examines at most m+1
breakpoints, each with two sums of length m; no search over subsets is used. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DPCut
attribute [local instance] Classical.propDecidable

def capPrefix {m : ℕ} (cap q : Fin m → ℝ) : Option (Fin m) → Finset (Fin m)
  | none => ∅
  | some j => Finset.univ.filter (fun i => cap i / q i ≤ cap j / q j)

def capCandidate {m : ℕ} (cap q : Fin m → ℝ) (j : Option (Fin m)) : ℝ :=
  (1 - ∑ i ∈ capPrefix cap q j, cap i) / ∑ i ∈ (capPrefix cap q j)ᶜ, q i

def capScale {m : ℕ} (cap q : Fin m → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (capCandidate cap q)

lemma waterfill_split_bound {m : ℕ} (cap q : Fin m → ℝ) (c : ℝ) (S : Finset (Fin m)) :
    ∑ i, cappedWaterfill cap q c i ≤ (∑ i ∈ S, cap i) + c * ∑ i ∈ Sᶜ, q i := by
  rw [← Finset.sum_add_sum_compl S (fun i => cappedWaterfill cap q c i), Finset.mul_sum]
  exact add_le_add (Finset.sum_le_sum (fun i _ => min_le_left _ _))
    (Finset.sum_le_sum (fun i _ => min_le_right _ _))

lemma capCandidate_le {m : ℕ} {cap q : Fin m → ℝ} {c : ℝ}
    (hq : ∀ i, 0 < q i) (hc : 0 ≤ c) (hmass : ∑ i, cappedWaterfill cap q c i = 1)
    (j : Option (Fin m)) : capCandidate cap q j ≤ c := by
  let S := capPrefix cap q j
  have hden : 0 ≤ ∑ i ∈ Sᶜ, q i := Finset.sum_nonneg fun i _ => (hq i).le
  by_cases hz : (∑ i ∈ Sᶜ, q i) = 0
  · change (1 - ∑ i ∈ S, cap i) / (∑ i ∈ Sᶜ, q i) ≤ c
    simpa only [hz, div_zero] using hc
  · have hd : 0 < ∑ i ∈ Sᶜ, q i := lt_of_le_of_ne hden (Ne.symm hz)
    apply (div_le_iff₀ hd).mpr
    have hh := waterfill_split_bound cap q c S
    rw [hmass] at hh
    linarith

lemma capCandidate_attains {m : ℕ} {cap q : Fin m → ℝ} {c : ℝ}
    (hcap : 1 < ∑ i, cap i) (hq : ∀ i, 0 < q i)
    (hmass : ∑ i, cappedWaterfill cap q c i = 1) :
    ∃ j : Option (Fin m), capCandidate cap q j = c := by
  let S := Finset.univ.filter (fun i => cap i / q i ≤ c)
  have hmem (i : Fin m) : i ∈ S ↔ cap i / q i ≤ c := by simp [S]
  have hsplit : (∑ i ∈ S, cap i) + c * ∑ i ∈ Sᶜ, q i = 1 := by
    rw [← hmass, ← Finset.sum_add_sum_compl S (fun i => cappedWaterfill cap q c i), Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      exact (min_eq_left ((div_le_iff₀ (hq i)).mp ((hmem i).mp hi))).symm
    · apply Finset.sum_congr rfl
      intro i hi
      have hn : ¬cap i / q i ≤ c := by simpa [S] using hi
      exact (min_eq_right (le_of_lt ((lt_div_iff₀ (hq i)).mp (lt_of_not_ge hn)))).symm
  have hne : Sᶜ.Nonempty := by
    by_contra hh
    have he : Sᶜ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hh
    have he' : S = Finset.univ := by simpa using congrArg (fun s : Finset (Fin m) => sᶜ) he
    simp only [he', Finset.compl_univ, Finset.sum_empty, mul_zero, add_zero] at hsplit
    linarith
  have hd : 0 < ∑ i ∈ Sᶜ, q i := Finset.sum_pos (fun i _ => hq i) hne
  have hex : ∃ j : Option (Fin m), capPrefix cap q j = S := by
    by_cases hS : S.Nonempty
    · obtain ⟨j, hj, hmax⟩ := S.exists_max_image (fun i => cap i / q i) hS
      refine ⟨some j, ?_⟩
      ext i
      simp only [capPrefix, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hi
        exact (hmem i).mpr (hi.trans ((hmem j).mp hj))
      · intro hi
        exact hmax i hi
    · exact ⟨none, (Finset.not_nonempty_iff_eq_empty.mp hS).symm⟩
  obtain ⟨j, hj⟩ := hex
  refine ⟨j, ?_⟩
  unfold capCandidate
  rw [hj]
  apply (div_eq_iff hd.ne').mpr
  linarith

theorem capScale_eq {m : ℕ} {cap q : Fin m → ℝ} {c : ℝ}
    (hcap : 1 < ∑ i, cap i) (hq : ∀ i, 0 < q i)
    (hc : 0 ≤ c) (hmass : ∑ i, cappedWaterfill cap q c i = 1) : capScale cap q = c := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun j _ => capCandidate_le hq hc hmass j)
  · obtain ⟨j, hj⟩ := capCandidate_attains hcap hq hmass
    rw [← hj]
    exact Finset.le_sup' _ (Finset.mem_univ j)

def finiteCappedProjection {m : ℕ} (cap q : Fin m → ℝ) : Fin m → ℝ :=
  if (∑ i, cap i) = 1 then cap else cappedWaterfill cap q (capScale cap q)

theorem finiteCappedProjection_minimizes {m : ℕ} {cap q : Fin m → ℝ}
    (hcap : ∀ i, 0 ≤ cap i) (hmass : 1 ≤ ∑ i, cap i)
    (hq : IsDistribution q) (hqpos : ∀ i, 0 < q i) :
    finiteCappedProjection cap q ∈ cappedSimplex cap ∧
      ∀ z ∈ cappedSimplex cap, finiteKL (finiteCappedProjection cap q) q ≤ finiteKL z q := by
  obtain ⟨c, hc, hm⟩ := cappedWaterfill_scalar_exists hcap hmass hqpos
  have hp := cappedWaterfill_minimizes hcap hq hqpos hc hm
  by_cases he : ∑ i, cap i = 1
  · have hsame : cappedWaterfill cap q c = cap := by
      apply funext
      have hsum : (∑ i, (cap i - cappedWaterfill cap q c i)) = 0 := by
        rw [Finset.sum_sub_distrib, hm, he]; ring
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i (_ : i ∈ Finset.univ) => sub_nonneg.mpr (min_le_left (cap i) (c * q i)))).mp hsum
      intro i
      exact (sub_eq_zero.mp (hz i (Finset.mem_univ i))).symm
    simpa only [finiteCappedProjection, if_pos he, hsame] using hp
  · have hgt := lt_of_le_of_ne hmass (Ne.symm he)
    simpa only [finiteCappedProjection, if_neg he, capScale_eq hgt hqpos hc.le hm] using hp

lemma measurable_capPrefix_sum {m : ℕ} (j : Option (Fin m))
    {w : ((Fin m → ℝ) × (Fin m → ℝ)) → Fin m → ℝ} (hw : Measurable w) :
    Measurable (fun x => ∑ i ∈ capPrefix x.1 x.2 j, w x i) := by
  cases j with
  | none => simp [capPrefix]
  | some j =>
    simp only [capPrefix, Finset.sum_filter]
    apply Finset.measurable_sum
    intro i _
    apply Measurable.ite
    · exact measurableSet_le (by fun_prop) (by fun_prop)
    · exact (measurable_pi_apply i).comp hw
    · exact measurable_const

lemma measurable_capCandidate {m : ℕ} (j : Option (Fin m)) :
    Measurable (fun x : (Fin m → ℝ) × (Fin m → ℝ) => capCandidate x.1 x.2 j) := by
  have he (x : (Fin m → ℝ) × (Fin m → ℝ)) :
      ∑ i ∈ (capPrefix x.1 x.2 j)ᶜ, x.2 i = (∑ i, x.2 i) - ∑ i ∈ capPrefix x.1 x.2 j, x.2 i := by
    have hh := Finset.sum_add_sum_compl (capPrefix x.1 x.2 j) x.2
    linarith
  simp only [capCandidate, he]
  exact (measurable_const.sub (measurable_capPrefix_sum j measurable_fst)).div
    ((by fun_prop : Measurable (fun x : (Fin m → ℝ) × (Fin m → ℝ) => ∑ i, x.2 i)).sub
      (measurable_capPrefix_sum j measurable_snd))

lemma measurable_capScale {m : ℕ} :
    Measurable (fun x : (Fin m → ℝ) × (Fin m → ℝ) => capScale x.1 x.2) := by
  have hh := Finset.measurable_sup' (s := (Finset.univ : Finset (Option (Fin m))))
    Finset.univ_nonempty (fun j _ => measurable_capCandidate j)
  convert hh using 1
  funext x
  simp only [capScale, Finset.sup'_apply]

theorem measurable_finiteCappedProjection {m : ℕ} :
    Measurable (fun x : (Fin m → ℝ) × (Fin m → ℝ) => finiteCappedProjection x.1 x.2) := by
  unfold finiteCappedProjection
  apply Measurable.ite
  · exact measurableSet_eq_fun (by fun_prop) measurable_const
  · exact measurable_fst
  · apply measurable_pi_lambda
    intro i
    exact ((measurable_pi_apply i).comp measurable_fst).min
      (measurable_capScale.mul ((measurable_pi_apply i).comp measurable_snd))

end DPCut
