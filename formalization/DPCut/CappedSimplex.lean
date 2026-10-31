import DPCut.KLProjection

/-! The public capped simplex used in Lemma 29. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace DPCut

def cappedSimplex {m : ℕ} (cap : Fin m → ℝ) : Set (Fin m → ℝ) :=
  {p | IsDistribution p ∧ ∀ i, p i ≤ cap i}

lemma cappedSimplex_closed {m : ℕ} (cap : Fin m → ℝ) : IsClosed (cappedSimplex cap) := by
  have he : cappedSimplex cap =
      (⋂ i, {p : Fin m → ℝ | 0 ≤ p i}) ∩ {p | ∑ i, p i = 1} ∩
      (⋂ i, {p : Fin m → ℝ | p i ≤ cap i}) := by
    ext p; simp [cappedSimplex, IsDistribution, and_assoc]
  rw [he]
  exact ((isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_eq (by fun_prop) continuous_const)).inter
      (isClosed_iInter fun i => isClosed_le (continuous_apply i) continuous_const)

lemma cappedSimplex_convex {m : ℕ} (cap : Fin m → ℝ) : Convex ℝ (cappedSimplex cap) := by
  intro p hp z hz a b ha hb hab
  refine ⟨⟨fun i => add_nonneg (mul_nonneg ha (hp.1.1 i)) (mul_nonneg hb (hz.1.1 i)), ?_⟩, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hp.1.2, hz.1.2, mul_one, hab]
  · intro i
    change a * p i + b * z i ≤ cap i
    calc
      _ ≤ a * cap i + b * cap i := add_le_add
        (mul_le_mul_of_nonneg_left (hp.2 i) ha) (mul_le_mul_of_nonneg_left (hz.2 i) hb)
      _ = cap i := by rw [← add_mul, hab, one_mul]

lemma normalized_mask_mem_cappedSimplex {m : ℕ} {a : Fin m → ℝ} {H : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hH : 0 < H) (hHmass : H ≤ ∑ i, a i) :
    (fun i => a i / ∑ j, a j) ∈ cappedSimplex (fun i => a i / H) := by
  have hm : 0 < ∑ i, a i := hH.trans_le hHmass
  refine ⟨⟨fun i => div_nonneg (ha i) hm.le, ?_⟩, ?_⟩
  · rw [← Finset.sum_div, div_self hm.ne']
  · intro i
    exact div_le_div_of_nonneg_left (ha i) hH hHmass

lemma normalized_target_mem_cappedSimplex {m : ℕ} {a x : Fin m → ℝ} {H M : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hH : 0 < H) (hHM : H ≤ M) (hm : ∑ i, a i * x i = M) :
    (fun i => a i * x i / M) ∈ cappedSimplex (fun i => a i / H) := by
  have hM := hH.trans_le hHM
  refine ⟨⟨fun i => div_nonneg (mul_nonneg (ha i) (hx i).1) hM.le, ?_⟩, ?_⟩
  · rw [← Finset.sum_div, hm, div_self hM.ne']
  · intro i
    calc
      _ ≤ a i / M := div_le_div_of_nonneg_right (by nlinarith [(ha i), (hx i).2]) hM.le
      _ ≤ a i / H := div_le_div_of_nonneg_left (ha i) hH hHM

theorem capped_projection_existsUnique {m : ℕ} {cap q : Fin m → ℝ}
    (hne : (cappedSimplex cap).Nonempty) (hq : IsDistribution q) (hqpos : ∀ i, 0 < q i) :
    ∃! p, p ∈ cappedSimplex cap ∧ ∀ z ∈ cappedSimplex cap, finiteKL p q ≤ finiteKL z q :=
  kl_projection_existsUnique (cappedSimplex_closed cap) (cappedSimplex_convex cap) hne
    (fun _ h => h.1) hq hqpos

lemma capped_projection_positive {m : ℕ} {a q p : Fin m → ℝ} {H : ℝ}
    (ha : ∀ i, 0 < a i) (hH : 0 < H) (hHmass : H ≤ ∑ i, a i)
    (hq : IsDistribution q) (hqpos : ∀ i, 0 < q i)
    (hp : p ∈ cappedSimplex (fun i => a i / H))
    (hmin : ∀ z ∈ cappedSimplex (fun i => a i / H), finiteKL p q ≤ finiteKL z q) :
    ∀ i, 0 < p i := by
  have hz := normalized_mask_mem_cappedSimplex (fun i => (ha i).le) hH hHmass
  have hs := kl_projection_support (cappedSimplex_convex _) (fun _ h => h.1) hq hqpos hp hz hmin
  exact fun i => hs i (div_pos (ha i) (hH.trans_le hHmass))

end DPCut
