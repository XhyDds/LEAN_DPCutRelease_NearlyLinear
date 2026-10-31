import DPCut.CCApplication

/-! Appendix C's CC results, conditional only on the explicitly named external
algorithm families. There are no assumed internal reduction lemmas. -/
set_option autoImplicit false
noncomputable section
namespace DPCut

/-- Corollary 31: fixed-k PTAS, with one additive error bound for every k. -/
theorem corollary31 (baseline : CCBaselineFamily)
    (ptas : ∀ k : ℕ, 2 ≤ k → ∀ slack : ℝ, 0 < slack → FixedKCCContract k slack (1 / 2)) :
    FixedKCorrelationClusteringStatement := by
  intro ξ ε hξ hε
  obtain ⟨C, Cfail, d, hC, hCfail, hreduce⟩ := private_cc_reduction hε (half_pos hξ)
    (show 1 ≤ 1 + ξ / 2 by linarith) (baseline ε hε)
  refine ⟨C, Cfail, d, hC, hCfail, ?_⟩
  intro k hk
  let alg := ptas k hk (ξ / 2) (half_pos hξ)
  have h := hreduce (1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (fun _ => k) (fun _ _ => Nat.le_trans (by decide : 1 ≤ 2) hk) alg.kernel alg.markov
    (fun n hn w hw => alg.approximation n hn w hw)
  have he : (1 + ξ / 2) + ξ / 2 = 1 + ξ := by ring
  rwa [he] at h

/-- The introduction's 1.387 approximation, with the cited 1.38675 algorithm
supplied explicitly. -/
theorem private_correlation_clustering (baseline : CCBaselineFamily)
    (alg : CCApproximationContract (5547 / 4000) 1) : CorrelationClusteringStatement := by
  intro ε hε
  obtain ⟨C, Cfail, d, hC, hCfail, hreduce⟩ :=
    theorem30 baseline (5547 / 4000) (1 / 4000) ε (by norm_num) (by norm_num) hε
  refine ⟨C, Cfail, d, hC, hCfail, ?_⟩
  have h := hreduce 1 (by norm_num)
    alg.kernel alg.markov (fun n hn w hw => alg.approximation n hn w hw)
  norm_num at h
  exact h

end DPCut
