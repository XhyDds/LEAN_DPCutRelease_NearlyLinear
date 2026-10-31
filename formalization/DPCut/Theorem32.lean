import DPCut.MaxKApplication
import DPCut.ExternalApplicationContracts

/-! Appendix C, Theorem 32 and the Max-Cut corollary. External algorithm
contracts are explicit arguments; no external approximation theorem is axiomatized. -/
set_option autoImplicit false
noncomputable section
namespace DPCut

theorem theorem32 : PrivateMaxKStatement := private_max_k

/-- The Goemans–Williamson guarantee is supplied by the caller's contract. -/
theorem private_max_cut (gw : MaxKCutContract 2 (878 / 1000)) : PrivateMaxCutStatement := by
  intro ξ ε hξ hε
  obtain ⟨C, Cf, d, hC, hCf, h⟩ := theorem32 ξ ε hξ hε
  refine ⟨C, Cf, d, hC, hCf, h 2 (by norm_num) (878 / 1000) (by norm_num) (by norm_num)
    gw.kernel gw.markov ?_⟩
  intro n hn w hw
  exact ⟨gw.feasible n hn w hw, gw.approximation n hn w hw⟩

end DPCut
