# Lean formalization of private cut release

This project formalizes the current `../STOC2027.tex`. Completed proofs and
the computational model's explicit assumptions are listed below.
The entry point is [`DPCut.lean`](DPCut.lean); the formalization plan, assumptions,
dependencies, and complete source-to-Lean mapping are in [`PLAN.md`](PLAN.md).

The original paper-statement targets are definitions of propositions, named
`...Statement`. This makes their mathematical types reviewable without introducing axioms or `sorry` proofs.
For example, `MainStatisticalStatement : Prop` is a statement, not a proof of it.
The source files contain no admitted proofs or new axioms.

**Scope of the cost claims.** The development proves statistical guarantees,
semantic refinement of the specified routines, and polynomial bounds on loop
and sample counts, precision parameters, and assigned costs. `CostedLaw`,
`Arithmetic`, and `TimedAlgorithm` do not enforce an execution language that
derives time from permitted instructions. In particular, `TimedAlgorithm`
admits any measurable function with reported completion time zero. Consequently,
the results named `runtime` and the formal `LSWStatement` hypothesis do not
certify the actual real-arithmetic running time of the SDP solver or full release.
This is a limitation even before considering finite-bit complexity. The paper's
running-time argument relies on its algorithmic analysis and the cited results.

**Appendix C proofs are implemented.** Completed statistical results are Lemmas 28 and 29,
Theorems 30, 32 and 34, Corollary 31, and the CC and Max-Cut introduction corollaries.
The CC results take explicit private-baseline and nonprivate approximation contracts;
the Max-Cut corollary takes the external Goemans–Williamson contract. No external
algorithm contract is asserted as inhabited or introduced as an axiom.
The capped mechanism is an actual measurable sampling kernel, with privacy, an
almost-sure coordinate cap, and error `2^126 * mainError n p` (logarithmic exponent 7).
Its KL projection is given by a finite formula with m+1 threshold candidates,
including changing-support handling. The CC proofs include independent Bernoulli
rounding, simultaneous concentration over all partitions, amplification, adaptive
privacy composition, and uniform-in-n error calibration. The baseline contract's
delta budget is a function of n so its additive constants remain uniform in n.
Remark 33's lower bound, Lemma 35 (with constant `1 / b²`), and the exact and
balanced hierarchy transfer bounds also compile. Theorem 36 now compiles under
`InducedARVContract`, a one-cut weighted ARV contract. Its internal proof includes
public fallback cuts, amplification, recursion with at most n−1 successful split
steps, an exact balanced analysis comparator, and the final n log^(3/2) n error.
`AppendixRuntime.lean` provides polynomial cost certificates and law equality
for CC, Max-k-Cut, constrained cuts and hierarchical clustering using the LSW
approximate implementation. All four runtime theorems take `LSWStatement`,
construct the family with the full `verifiedLinearAlgebra` implementation, and retain the
external application-algorithm contracts. No exact-SDP or separate approximate-SDP
oracle contract is required. Their law equalities identify the **actual approximate
kernels**, whose privacy and utility are proved in `LSWCCKernel.lean` and
`LSWApplicationGuarantees.lean`.
The external contracts include statistical guarantees and bounds on assigned
costs. They permit arbitrary kernels priced at zero and therefore do not certify
the external algorithms' actual running times. The application cost conclusions
have the same scope as the cost claims described above.
`ImplementedApplications.lean` combines these with the final error calibrations
and a polynomial realization of the same kernel. In namespace `LSWApplications`,
`theorem30`, `corollary31`, `theorem32`, `theorem34`, and `theorem36`, together
with `private_correlation_clustering` and `private_max_cut`, provide the combined
application results. `constrained_cut_general` also retains arbitrary valid
privacy and accuracy parameters. `RealizedWithin` records equality of the
specified costed program's output law and the private kernel, with a uniform cost bound. The combined statements fix
the program construction and the supplied external algorithms. CC's
calibration accepts any positive release constant and is instantiated at `2^138`;
additive constants retain their stated independence from k and source success
probability. Runtime constants may depend on the external approximation algorithm.

CC uses the capped implementation in `CappedLSWRelease.lean`: the approximate
witnesses run inside the capped loops, with bounded objectives, public timeouts
and restarts. `CappedReplacementTV.lean` bounds the accumulated error; half of
the privacy delta and failure budget are reserved before running the mechanism.
The actual output is capped almost surely, is `(epsilon,delta)`-private on capped
inputs, and has error `2^138 * mainError n p` with failure at most `p.beta`.
The full-release applications use the existing `2^178 * mainError n p` bound.
These universal constants differ from the ideal statistical proofs; the
application approximation factors and asymptotic additive-error orders are
unchanged. `CappedLSWRuntime.lean` proves worst-case polynomial cost uniformly in
`1+n+1/gamma+1/epsilon+log(1/delta)+log(1/beta)`. The configured solver's timeout
is polynomial in the logarithm of inverse precision; its retry count is logarithmic.
`CappedLSW.capped_release_of_lsw` combines privacy, the output cap, utility and
this general cost guarantee for one program; `cc_cost_polynomial` is its
application specialization.
The unnumbered bisection, expansion and uniform-sparsity reductions are included;
odd-order bisection padding preserves cut values and the optimum exactly.
The project build and axiom audits check that the completed proofs use only
`propext`, `Classical.choice`, and `Quot.sound`; `AuditAll.lean` also checks all
imported helper, private and generated project declarations. `AuditAppendixC.lean`
also traverses the public runtime proofs' dependencies and rejects either legacy
SDP-oracle contract.
The active runtime model is the costed real-arithmetic model described below.
The unused bit-machine, binary arithmetic, rational rounding/numerics and finite-bit
sampler modules have been removed.

**Approximate-optimization prerequisites are proved.**
`OptimizerApproximation.lean` proves the original `ObjectiveGapStatement`:
objective gap at most `lam * mu^2 / (2*n^4)` implies normalized covariance
Frobenius error at most `mu`. `GaussianKL.lean` derives the exact Gaussian batch
KL formula from the density, absolute continuity and integrable log likelihood.
`CovarianceApproximation.lean` proves the original `ApproximateGaussianStatement`,
including the coefficient `k * mu^2 / 2`.
`KLTotalVariation.lean` proves an eventwise bound `TV <= 2*sqrt(KL)` internally,
using Jensen's inequality and the Radon–Nikodym derivative.
`OptimizerTV.lean` derives Gaussian batch error `2*sqrt(k)*mu` and the bounded
FindWitness error `K*2*sqrt(k)*mu` from the optimizer's objective gap. These
bounds use the actual score and acceptance maps; they do not supply a solver.

`ApproximationTransfer.lean` contains the shared half-budget calibration,
error-constant absorption and high-probability TV transfer used by the
approximate-SDP theorem. These lemmas have no rational-rounding or bit-machine
dependency. They and the numerical bridges are covered by `AuditTheorem1.lean`;
`AuditAll.lean` checks every imported project declaration.

**Theorem 38 is proved:** [`DPCut/Theorem38.lean`](DPCut/Theorem38.lean) contains
`theorem38 : LowerBoundStatement`, with the uniform absolute constant **c = 2⁻³⁰**.
It retains the original ranges n ≥ 33, ε ∈ (0,1), 0 ≤ δ ≤ ε/100,
β ∈ (0,1/40], and γ ∈ [0,1), including the explicit γ = 0 convention.
The prerequisites prove group privacy, measurable finite decoding, a Hamming
reconstruction bound, and the bipartite and star hard-family estimates.
A direct finite Rademacher-moment argument supplies the required discrepancy
bound; the external EKKL lemma is not assumed. No computational or SDP oracle
assumption is used. The stronger helper `theorem38_explicit` also shows that
nonnegative output weights are unnecessary for this lower bound.
Run `lake build DPCut.Theorem38` and `lake env lean AuditTheorem38.lean`.
The audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

**Theorem 1 has statistical and computational forms.**
[`DPCut/Theorem1.lean`](DPCut/Theorem1.lean) proves
`theorem1_statistical hn hp` directly about `fullReleaseLaw`, without an
optimizer-cost assumption. Its statement fixes the mechanism and the error
constant: the law is measurable, is a probability measure on every input, produces
nonnegative weights almost surely, is **(ε,δ)-edge-DP**, and has simultaneous
all-cut error **γ cut(w,S) + 2^166 mainError(n,p)** with probability **1 − β**.
The constant is uniform over n, all public parameters, and the input graph.
`theorem1_statistical_exists : MainStatisticalStatement` is its existential
corollary for application reductions that only require some private release.
`parameter_choice` also proves privacy and bounded utility with the same constants.

**The approximate release has statistical guarantees and polynomial cost accounting.**
[`DPCut/Theorem1LSW.lean`](DPCut/Theorem1LSW.lean) proves

```lean
theorem1_of_lsw (hLSW : LSWStatement) :
  MainTheoremStatement (realArithmeticLSWModel hLSW)
```

`LSWStatement` is passed explicitly as a proposition parameter, not a new axiom.
It is intended to express a polynomial specialization of
[Lee–Sidford–Wong, Theorem 42](https://arxiv.org/pdf/1508.04874), for exact
separation and first-order oracles. Its current `TimedAlgorithm` interface records
a completion-time label and a compatible timeout law, but does not require
those labels to count execution steps or oracle calls. It permits zero-time
representations of arbitrary measurable functions. Thus the hypothesis does not
isolate a verified operational version of LSW: proving or supplying it does not
by itself establish an algorithm's running time.
[`VerifiedLinearAlgebra.lean`](DPCut/VerifiedLinearAlgebra.lean) constructs the
linear-algebra implementation and its cost certificate. Recursive scalar Schur
elimination handles PSD testing, including zero pivots and explicit negative
quadratic-form witnesses. The same machinery solves positive-definite linear
systems, computes inverses and determinants, and constructs a Cholesky factor.
The proofs include measurability and exact agreement with the existing mathlib
matrix notions and covariance Gaussian laws.

The concrete `Arithmetic` routines compose counters for scalar operations,
comparisons and stored vector entries; constants, indexing and structural
rearrangement are free in this accounting. The `Arithmetic` type itself is a
value/count pair and does not enforce that convention for arbitrary inhabitants.
The proved bounds are `100*(n+1)^3` for PSD separation, `21*(n+1)^4` for the
inverse implementation, `10*(n+1)^3` for determinants, and `20*(n+1)^3` for
factorization. The complete separation/first-order oracle, including the
objective guard and coordinate adjoint, fits the existing
`1000*(n+1)^6 + 200*(n+1)^3` charge. The optimizer's fallback has a separate
verified feasibility-check implementation and cost bound.

`ScalarGaussianSampling` implements finite products by sequential scalar draws.
`VerifiedGaussianSampling` combines these draws with the verified factor and
matrix-vector algorithms. Its law is exactly `gaussianBatch`, and its cost is
at most `gaussianBatchCost`. Thus covariance-factorization cost is not left as
an unverified sampling primitive. The existing outer vector/arithmetic blocks
retain their agreed macro cost semantics. Exact scalar sampling and elementary
real functions remain model primitives. An operational runtime proof for the
optimizer and the whole mechanism remains absent.

These implementations are connected to the costed release: `LSW.Oracle` takes
an `Arithmetic` program and requires a proof that its operation count fits the
charge. The SDP oracle supplies `oracleProgram`, `oracle_value` and `oracle_cost`.
The solver family preserves the supplied implementation, and `mapArithmetic`
executes its counted decoder, charging the supremum of its operation counts.
The witness trials call `verifiedGaussianBatch` directly; their law and cost
proofs use its verified distribution and operation bounds. Positive definiteness
is discharged from feasibility of every solver output, including fallbacks.
`AuditImplementation.lean` checks these paths through Theorem 1 and the application
theorems, excluding proofs merely stored in `verifiedLinearAlgebra` from its
dependency evidence. It checks integration, not the adequacy of the cost model
as a semantics of actual computation.

The problem-specific reduction **is proved**. A bounded redundant space of
`n²` Euclidean coordinates maps onto all feasible SDP matrices, contains a
radius-`1/4` ball, and lies in a radius-`2n` ball. The log-determinant objective
has a proved supergradient, concavity, and range bound. The solver's cost
retains logarithmic dependence on objective magnitude and precision.
The public noisy-mass cap bounds every objective reached in the release.
A guard replaces objectives outside this public bound by zero, making costs
uniform even over unreachable values in `CostedLaw.bind`; the guard is proved
inactive along the actual execution.

For the public radius `r = approximationRadius n p`, the solver requests
objective gap `r²/(8*n⁴)`. Each run is cut off after a public bound of twice
its expected reported cost, rounded up. Independent restarts reduce failure to at most
`r/2`; a failed solve returns the feasible identity matrix. The proof includes
this failure probability in the TV bound, then proves the actual release is
**(ε,δ)-edge-DP**, graph-valued, and has all-cut error
**γ cut(w,S) + 2^178 mainError(n,p)** with probability at least **1 − β**.
One program, coefficient and degree give a **uniform polynomial bound on assigned cost** in
`1+n+1/γ+1/ε+log(1/δ)+log(1/β)` in this model. No exact optimizer or separate
approximate-SDP contract is assumed by this result. Identifying this bound with
real-arithmetic running time requires execution semantics not supplied here.

Run `lake build DPCut.Theorem1LSW`, `lake env lean AuditLSW.lean`, and
`lake env lean AuditLinearAlgebra.lean`, and `lake env lean AuditImplementation.lean`.
`theorem1_of_lsw_with_implementation` provides the modular interface for
alternative counted implementations with proved refinement and cost bounds;
the main theorem supplies the constructed one. The former interface accepting
only `LinearAlgebraPrimitives` has been replaced.
The previous solver-contract theorems below are retained as separate results.
Appendix C's public runtime and combined application theorems use LSW directly.

[`DPCut/Theorem1Oracle.lean`](DPCut/Theorem1Oracle.lean) separately proves
`theorem1 (sdp : ApproxSDPOracle) : MainTheoremStatement (realArithmeticOracleModel sdp)`.
**An exact optimizer is no longer required.** The external primitive returns a
measurable choice of feasible matrix X satisfying
`optimum lam D - objective lam D X <= lam * mu^2 / (2*n^4)` for the requested
`0 < mu <= 1/2`. Its charge is bounded by
`C_SDP * (1+n+abs(log mu))^d_SDP`.

The cost bound remains **uniform in the real objective D and regularization lam**,
as in the original oracle model. This is an explicit assumption, not a claimed
consequence of Lee–Sidford–Wong or a verified numerical implementation. Their
expected-time guarantee and its dependence on oracle costs are not silently
identified with this contract.

The program actually uses the returned covariance for its Gaussian draws.
`OracleReplacementTV.lean` proves error accumulation through all adaptive loops.
Writing `c = fullRunConfig n (precisionParameters p)` and
`B = 4 * card(Edge n) * c.T1 * c.T2 * c.oracle.K * (c.oracle.k+1)`, it requests
`mu = beta*delta / (16*(1+B))`. The full output law is proved within
`min(beta/2, delta/(2*(1+exp epsilon)))` of the ideal law run with delta/beta halved.
The final coordinatewise nonnegative projection fixes the ideal law almost surely.
The resulting mechanism is **(epsilon,delta)-DP**, has nonnegative output, and
satisfies the same simultaneous cut guarantee with **C = 2^178**, failure beta,
and logarithmic exponent 7. The precision charge is included in the proved
uniform polynomial bound on assigned cost.

The real-arithmetic costs used by this result are:

| Operation | Cost bound |
| --- | --- |
| Scalar Laplace draw | 1 |
| Finite vector/arithmetic block | `100 (n+1)^2` |
| Verified dense Gaussian batch of k vectors | `100 (n+1)^3 (k+1)` |
| Preprocessing noise and clipping | `card(Edge n) + 100 (n+1)^2` |

`costedApproxRelease_law` identifies the costed execution's law with the approximate
mechanism. Bind takes a supremum over **all** intermediate values. One program,
coefficient and degree work for all admissible n, p and w. The new theorem retains
real-valued primitives and assigned costs; it does not establish an operational
real-arithmetic or finite-bit runtime bound.

The previous exact-oracle result is retained as
`theorem1_exact_oracle (sdp : ExactSDPOracleCost)` for
`realArithmeticExactOracleModel sdp` as a historical result. Appendix C's public
runtime certificates now use LSW directly. The obsolete exact-oracle application
wrappers and their specialized runtime bounds have been removed.
Run `lake build DPCut.Theorem1Oracle` and `lake env lean AuditTheorem1.lean`.
Both versions have no admitted proofs or custom axioms; the permitted foundational
axioms are `propext`, `Classical.choice`, and `Quot.sound`.

**Noisy-mass clipping is included in the release.** Each outer round now uses
`min (card(Edge n)*U + 2*tau2) (max 0 (mass wi + noise + tau2))`, as in the
paper's implementation proof. The statistical, approximate, and costed laws all
use this cap. Privacy follows by postprocessing; on the existing utility good
event the cap is inactive. Theorem 1's hypotheses, error constants and probability
bounds are unchanged. `MassClipping.lean` also proves the mass bounds for the
initial estimate and every MW update, and the resulting bound for both discrepancy
objectives under the mask/nonnegativity invariants.

**The deterministic ellipsoid feasibility method is proved.**
[`DPCut/EllipsoidFeasibility.lean`](DPCut/EllipsoidFeasibility.lean) supplies a
finite recursive algorithm with an ordinary point-separation oracle as input.
The prerequisites prove the explicit central-cut update, containment, determinant
contraction, volume lower bounds, and termination. If the feasible set contains a
ball of radius `r > 0` and lies in a ball of radius `R > 0`, dimension `d >= 1`,
the algorithm succeeds with at most `floor(2*d*(d+2)*log(R/r))+1` oracle calls.
`AuditEllipsoid.lean` and the global audit cover these proofs.

The ellipsoid branch remains independent of the LSW-based cost theorem.
An operational runtime theorem requires a language or transition system whose
semantics derives both outputs and costs. One could then implement the optimizer
in that model, or supply an external LSW theorem stated over that model. The
existing linear-algebra and refinement proofs may support either route; the
current cost-accounting theorem does not discharge this obligation.

**Lemma 10 is proved:** [`DPCut/Lemma10.lean`](DPCut/Lemma10.lean) contains
`DPCut.lemma10 : DPCut.ChiStatement`, with universal constant **C = 96**.
Its immediate prerequisites are proved in [`DPCut/ChiSquare.lean`](DPCut/ChiSquare.lean)
(chi-square failure probability at most `2 * exp (-k / 32)`) and
[`DPCut/GaussianWitness.lean`](DPCut/GaussianWitness.lean)
(feasibility bounds and the exact normalized Gaussian law).
The final proof includes measurability, the union bound, and clipping.
It uses the existing statement and definitions without strengthening their hypotheses.
To compile just this proof and its dependencies, run `lake build DPCut.Lemma10`.

**Lemma 11 is proved:** [`DPCut/Lemma11.lean`](DPCut/Lemma11.lean) contains
`DPCut.lemma11 : DPCut.ChaosStatement`, with **C = 512** and **c₀ = 1/2048**.
It keeps arbitrary signed weights and the original `ChiGood` conditioning event.
Its prerequisites derive Gaussian moments through order eight, the centered
quadratic fourth-moment bound, and a one-sided probability bound using mathlib's
spectral theorem. The batch witness is identified with the concrete quadratic
form, and its mean is computed exactly. This proves the existing target without
assuming the separately stated general hypercontractivity theorem.
Run `lake build DPCut.Lemma11` to compile this proof and its dependencies.

**Lemma 12 is proved:** [`DPCut/Lemma12.lean`](DPCut/Lemma12.lean) contains
`DPCut.lemma12 : DPCut.PreprocessStatement`, with the original thresholds
**U = 8 log(n/β₀)/(ε₀γ)** and **V = 2 log(n/β₀)/ε₀**.
The actual release of the noisy excess is **ε₀-pure-DP**. With probability at
least **1 − β₀**, adding the private clipped weights gives simultaneous relative
cut error **γ/2**, with no additive error. The clipped weights are not released.
The proof includes clipping decomposition and sensitivity, the joint product
Laplace density, normalization, measurable postprocessing, and a simultaneous
noise bound. Its failure estimate is at most `card(Edge n) * (β₀/n)^2 ≤ β₀`.
The unchanged statement assumes `n ≥ 2`, nonnegative weights, and
`ε₀,β₀,γ ∈ (0,1)`; the intermediate proofs do not need the upper bounds on ε₀ or γ.
Run `lake build DPCut.Lemma12` and `lake env lean AuditLemma12.lean`.
The audit reports only `propext`, `Classical.choice`, and `Quot.sound`, with no
admitted proofs or custom axioms.

**Lemma 13 is proved:** [`DPCut/Lemma13.lean`](DPCut/Lemma13.lean) contains
`DPCut.lemma13 : DPCut.OptimizerStabilityStatement`, including both the exact
relative Frobenius bound and the factor-two query comparison.
`optimizer_stability` specializes it to the actual choices `X_D` and `X_(D+ξ)`.
The definitions of `𝓧`, `q_e(X)`, `A_D`, `F(D)`, and `X_D` are in
[`Definitions.lean`](DPCut/Definitions.lean). Their foundations are proved in
[`SDPGeometry.lean`](DPCut/SDPGeometry.lean) and
[`Optimizer.lean`](DPCut/Optimizer.lean): compactness, convexity, the quadratic
query formula, `⟨A_D,X⟩ = ⟨D,q(X)⟩`, and existence and uniqueness of the optimizer.
The supremum defining `F(D)` equals the objective at `X_D`.
The assumptions are `n ≥ 2`, `λ > 0`, and arbitrary signed weights.
Uniqueness follows from first-order optimality and the relative Frobenius identity;
it does not assume a separate strict-concavity result.
Run `lake build DPCut.Lemma13` to compile this proof and its dependencies, and
`lake env lean AuditLemma13.lean` to inspect the transitive axiom dependencies.
They are only `propext`, `Classical.choice`, and `Quot.sound`; there are no custom
axioms or `sorry` admissions.

**Lemma 15 is proved:** [`DPCut/Lemma15.lean`](DPCut/Lemma15.lean) contains
`DPCut.lemma15 : DPCut.WeightedChiSquareStatement`, with the exact constant **2**,
arbitrary signed weights, and strict tail event from the paper. The proof derives
the centered Gaussian-square exponential moment, its sharp bound, and an optimized
Chernoff estimate, then applies it to both signs. `lemma15_independent` gives the
same result for independent standard normals on any probability space.
Run `lake build DPCut.Lemma15` to compile it and its prerequisites.

**Lemma 14 is proved:** [`DPCut/Lemma14.lean`](DPCut/Lemma14.lean) contains
`DPCut.lemma14 : DPCut.GaussianPrivacyStatement`, with universal constant **C = 4**.
`lemma14_density` proves the displayed product-of-densities inequalities;
`gaussianDensity_eq` identifies the exponential form with the paper's explicit
Gaussian density formula. The proof establishes the exact distributional change
of coordinates and the log-likelihood decomposition, then applies Lemma 15.
It uses relative precision eigenvalues instead of their logarithms.
The target now matches the current manuscript's **0 < δ₁ < 1/2**; the previous
specification used δ₁ < 1. Both covariance matrices are positive definite and the
relative Frobenius distance is strictly less than 1/2.
Run `lake build DPCut.Lemma14` and `lake env lean AuditLemmas14_15.lean`.
The audits report only `propext`, `Classical.choice`, and `Quot.sound`, with no
`sorry` admissions or custom axioms. Lemma 15 was compiled before Lemma 14.

**Lemma 16 is proved:** [`DPCut/Lemma16.lean`](DPCut/Lemma16.lean) contains
`DPCut.lemma16 : DPCut.SuccessChargedStatement`, with the exact parameters
**ε = 4L + 4ℓ* log(1/δ'')** and **δ = δ'' + (1 + exp ε) kδ'**.
The existing statement is unchanged: the outputs form any standard Borel space,
the auxiliary distributions are measurable Markov kernels, and the successful
charge budget holds almost surely under each auxiliary process.
The proof includes measurability of finite transcripts, propagation of absolute
continuity on common histories, the kernel density chain rule, the one-step
exponential moment, its finite-horizon induction, and the TV transfer.
It covers ℓ* = 0 and zero mass at the failure symbol.
Run `lake build DPCut.Lemma16` and `lake env lean AuditLemma16.lean`.
The transitive audit reports only `propext`, `Classical.choice`, and `Quot.sound`;
there are no admitted proofs or custom axioms.

**Lemma 17 is proved:** [`DPCut/Lemma17.lean`](DPCut/Lemma17.lean) contains
`DPCut.lemma17 : DPCut.AggregatePrivacyStatement DPCut.privacyConstants`.
It proves the existing statement for the unchanged `aggregateLaw`, with explicit
trial coefficient **8192**, batch coefficient **512**, and regularization
coefficient **2³⁰**. Lemma 20 uses the same oracle and fixes the certificate
constant to 16; `parameter_choice` now supplies a shared choice for aggregate
privacy/utility and bounded-release privacy/utility.
The proof includes optimizer continuity, the actual Gaussian and Laplace
densities, measurable conditioned auxiliary laws, all K trials, normalization
and support of accepted witnesses, the auxiliary success budget, and Lemma 16.
The padded transcript is proved equal to the original aggregation law.
The calibration gives `λ ≥ 8`, resolving the strict `< 1/2` covariance-distance
requirement of Lemma 14. Theorem 1 uses these same oracle coefficients.
Run `lake build DPCut.Lemma17` and `lake env lean AuditLemma17.lean`.
The audit reports only `propext`, `Classical.choice`, and `Quot.sound`, with no
admitted proofs or custom axioms.

**Lemma 18 is proved:** [`DPCut/Lemma18.lean`](DPCut/Lemma18.lean) contains
`DPCut.lemma18 : DPCut.MainPrivacyStatement DPCut.privacyConstants`.
It proves `(ε,δ)` privacy of the unchanged `cutReleaseLaw`, with the original
parameter choices, `n ≥ 2`, `U ≥ 1`, `0 < ε ≤ 1`, and `δ,β,γ ∈ (0,1)`.
The prerequisites include the translated Laplace mechanism, mask sensitivity,
measurability and probability normalization of both loops, residual-mask support,
and exact identification of early stopping with a padded adaptive process.
Basic and advanced composition are proved from measurable pure-private subparts
and mathlib's Hoeffding bound; they are not assumed as axioms or hypotheses of
Lemma 18. The composition results use symmetric neighboring pairs explicitly.
The inner budget is `(ε/(2T₁), δ/T₁)`; adding the mass release and composing
`T₁` outer rounds gives exactly `(ε,δ)`. The constants are the same as Lemma 17.
Run `lake build DPCut.Lemma18` and `lake env lean AuditLemma18.lean`.
The transitive audit reports only `propext`, `Classical.choice`, and `Quot.sound`,
with no admitted proofs or custom axioms. The statistical main theorem is now
proved above using the compatible outer-loop constants.

**Lemma 19 is proved:** [`DPCut/Lemma19.lean`](DPCut/Lemma19.lean) contains
`DPCut.lemma19 : DPCut.SDPCertificateStatement`, with universal constant **C = 2**,
arbitrary signed weights, `n ≥ 2`, and `λ > 0`. It includes the exact inequality
`mass D ≤ 2 * optimum λ D`. The stronger helper `sdp_cut_bound` gives additive
error `2λn log n + ‖D‖₁/n` and also allows `λ = 0`.
[`DPCut/ShrunkenCut.lean`](DPCut/ShrunkenCut.lean) proves feasibility, the query
formula, the exact determinant and the logarithmic penalty bounds for `X_S`.
`lemma19_shrunken` proves the existing exact shrunken-cut certificate target.
Run `lake build DPCut.Lemma19` and `lake env lean AuditLemma19.lean`.
The audit reports only `propext`, `Classical.choice`, and `Quot.sound`, with no
admitted proofs or custom axioms.

**Lemma 20 is proved:** [`DPCut/Lemma20.lean`](DPCut/Lemma20.lean) contains
`DPCut.lemma20 : DPCut.AggregateUtilityStatement DPCut.utilityConstants`.
It proves both witness-sign inequalities, simultaneous accuracy of every residual
cut, and the partition invariant for the unchanged `aggregateLaw`. The explicit
error is **B = 16(τ₁ + λn log n + nU)**. The oracle parameters are identical to
Lemma 17's; `aggregate_privacy_and_utility` proves both results with these constants.
The proof includes finite active-edge retirement, the log-determinant bound,
exact Laplace tails, signed-witness normalization, fresh-trial success, and an
adaptive failure bound. In particular, running out of aggregate fuel cannot
leave active coordinates on a run of valid witnesses.
Run `lake build DPCut.Lemma20` and `lake env lean AuditLemma20.lean`.
The transitive audit reports only `propext`, `Classical.choice`, and `Quot.sound`,
with no admitted proofs or custom axioms.

**Lemma 21 is proved:** [`DPCut/Lemma21.lean`](DPCut/Lemma21.lean) contains
`DPCut.lemma21 : DPCut.InnerRoundStatement DPCut.utilityConstants`.
Under the statement's explicit stopping-threshold hypothesis
`stop ≥ 10(B + τ₂/γ)`, it proves the joint success probability
**1 − T₂β_GE − β₂**, with the exact horizon
**T₂ = 1 + ⌈64(1+γ)² log n / γ²⌉** and unchanged inner algorithm.
The prerequisites prove finiteness and the finite-sum formula for mathlib's
normalized KL, mass and support preservation, the initial potential bound,
both witness-selection margins, and the exact potential decrease
**γ²M/[64(1+γ)²]**. The latter also proves the existing `MWProgressStatement`.
The probability argument integrates over the noisy mass and adaptive oracle
calls; it does not replace the joint assertion with a conditional guarantee.
Run `lake build DPCut.Lemma21` and `lake env lean AuditLemma21.lean`.
The audit reports only `propext`, `Classical.choice`, and `Quot.sound`, with no
admissions or custom axioms. Lemma 22 below supplies a global stopping-constant
calibration for its explicit choice of constants.

**Lemma 22 is proved:** [`DPCut/Lemma22.lean`](DPCut/Lemma22.lean) contains
`DPCut.lemma22 : DPCut.OuterRoundStatement DPCut.outerUtilityConstants`.
It proves that the actual stopping test is reached with probability at least
**1 − T₁T₂β_GE − T₁β₂**, with **T₁ = ⌈80 log(nU)⌉**. This includes the noise
in the stopping round and reserves a round for that final test.
The proof averages the simultaneous cut guarantee to obtain additive mass error
`2B`, proves residual mass contraction by **19/20**, and accounts for inner
success and contraction on the same oracle good event.

`outerUtilityConstants` retains the oracle and certificate coefficients from
Lemma 20, sets the outer coefficient to **80**, and sets the stopping coefficient
to **2¹²⁰**. These deliberately coarse universal constants are fully verified:
`outer_stopping_threshold` proves `stop ≥ 10(B + τ₂/γ)` for every admissible input.
The original `OuterRoundStatement` is unchanged and has no added assumptions.
Run `lake build DPCut.Lemma22` and `lake env lean AuditLemma22.lean`.
The audit reports only `propext`, `Classical.choice`, and `Quot.sound`, with no
admitted proofs or custom axioms.

**Lemma 23 is proved:** [`DPCut/Lemma23.lean`](DPCut/Lemma23.lean) contains
`DPCut.lemma23 : DPCut.BoundedUtilityStatement DPCut.outerUtilityConstants`.
With probability at least **1 − β**, the actual bounded CutRelease output satisfies,
simultaneously for every cut, relative error **γ** and additive error
**2¹²¹(nUℒ + nℒ⁷/(γε))**, where **ℒ = log(nU/(δβγε))**.
The uniform coefficient is explicit and independent of all inputs; the algorithm,
constants from Lemma 22, and original target statement are unchanged.

The proof tracks accuracy of the retired weights `w − a ⊙ w`, adds `B` for each
released portion, and bounds the discarded residual by the stopping threshold.
Inner success, contraction, and all-cut accuracy share one good event, so the
total failure budget is exactly `T₁T₂β_GE + T₁β₂ = β`.
`cutRelease_utility_explicit` gives the sharper intermediate error `T₁B + stop`.
`cutRelease_nonnegative` separately proves nonnegative output almost surely,
including on utility failures and fallback branches.
Run `lake build DPCut.Lemma23` and `lake env lean AuditLemma23.lean`.
The audit reports only `propext`, `Classical.choice`, and `Quot.sound`, with no
admitted proofs or custom axioms. Theorem 1 is now proved above; the lower bound
and application targets remain separate tasks.

The project pins Lean **4.24.0** and mathlib tag **v4.24.0**, commit
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. Transitive dependencies are pinned in
`lake-manifest.json`. This is a reproducible version choice, not a claim that it is
the latest release.

From this directory, with the pinned toolchain available:

```bash
lake exe cache get
lake build
lake env lean DPCut.lean
```

In the workspace used to prepare this specification, the toolchain is installed
locally under `.tools/lean-4.24.0-linux`, and the equivalent command is:

```bash
bash check.sh
```

The local toolchain, dependency sources and build products are ignored by Git.
On a new machine, install Lean using the [Lean community installation instructions](https://leanprover-community.github.io/install/).
The [mathlib dependency instructions](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency)
explain fetching the pinned package and its compiled cache.

`python3 extract_inventory.py` regenerates `source_inventory.json` and
`SourceStatements.tex`. These contain all **38 active mathematical environments**
(including definitions and the substantive Max-Cut remark), all four algorithms,
and source locations. Comments, `\iffalse` blocks and the obsolete lower bound
inside `\junk{...}` are excluded. The extractor is specific to this manuscript,
not a general TeX interpreter. Named appendix proofs are listed separately;
the manually reviewed dependency map is in `PLAN.md`.

`python3 make_lemma_comparison.py` regenerates `LemmaComparison.tex`, pairing
all 38 environments with their Lean statements and available theorem declarations,
including Remark 33. It also records comparison notes, external hypotheses,
source locations, and source hashes. Run both generators after manuscript changes.
The comparison document is standalone; compile it from this directory with
`pdflatex LemmaComparison.tex` twice.

`MainTheoremStatement` is parameterized by `ComputationalModel`; its cost clause
is proved for `realArithmeticLSWModel` under the formal `LSWStatement` parameter.
It bounds the model's assigned costs. The separate `realArithmeticOracleModel`
theorem is retained with the same limitation. Connecting these costs to execution
steps is an outstanding real-arithmetic obligation, beyond the integration of
the matrix routines and before any finite-bit implementation. The statistical
result is independent of this cost model.
