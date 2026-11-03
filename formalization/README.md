# Lean formalization of private cut release

This Lean 4/mathlib project formalizes the paper *Polynomial-Time Differentially
Private Synthetic Graph Release with Nearly-Linear Additive Error*.
All proofs are complete: the sources contain no `sorry` and declare no axioms, and
[`Audit.lean`](Audit.lean) checks that every project declaration depends only on
Lean's standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

The entry point is [`DPCut.lean`](DPCut.lean). The document
[`LemmaComparison.tex`](LemmaComparison.tex) prints each numbered statement of the
paper next to its Lean statement and, where one exists, the theorem proving it
(see [Building and checking](#building-and-checking)).
Statement numbers below are those of the paper.

Paper statements are encoded as propositions named `...Statement`, so that their
formal meaning can be reviewed separately from the proofs. For example,
`MainStatisticalStatement : Prop` is a statement, and
`theorem1_statistical_exists : MainStatisticalStatement` proves it.

## Summary

| Paper | Lean | Scope |
| --- | --- | --- |
| Theorem 1 | `theorem1_machine` | Privacy, accuracy, and worst-case polynomial running time of an implementation based on the ellipsoid method, in a real RAM model |
| Theorem 1 for the ideal mechanism | `theorem1_statistical` | Privacy and accuracy with exact SDP optimizers |
| Definition 5 | `laplace_statement` | Normalization and two-sided tail of the Laplace distribution |
| Lemmas 9–23 | `advanced_composition_statement`, `lemma10`, …, `lemma23` | Lean statements follow the paper |
| Theorem 38 (lower bound) | `theorem38` | As in the paper, with `c = 2⁻³⁰` |
| Corollaries 2 and 3, Appendix C | see [Applications](#applications-appendix-c) | Privacy and approximation guarantees, assuming the guarantees of the cited algorithms; running times are not verified |
| Lemmas 6–8, 24–26, and 37, Proposition 27 | — | Only the special cases needed by the proofs; see [Scope and limitations](#scope-and-limitations) |

## Theorem 1

### The implementation theorem

[`DPCut/Theorem1Machine.lean`](DPCut/Theorem1Machine.lean) proves
`DPCut.theorem1_machine` for the program `TypedMachine.implementedRun` and its
output law `TypedMachine.implementedLaw`. Under the hypotheses of the paper's
Theorem 1 (`n ≥ 2`, `0 < γ ≤ 1/4`, `0 < ε ≤ 1`, and `0 < δ, β < 1/10`), a single
statement combines

- measurability and normalization (the output law is a probability measure on
  every input);
- nonnegative output weights, almost surely;
- **(ε,δ)-edge privacy**;
- simultaneous all-cut error **γ·cut(w,S) + 2^178·mainError(n,p)** with failure
  probability at most **β**, where `mainError n p = n/(γε)·log(n/(δβγε))^7`;
- a bound `C·runtimeScale n p ^ d` on the number of executed operations and on
  the number of optimization calls, where
  `runtimeScale n p = 1 + n + 1/γ + 1/ε + log(1/δ) + log(1/β)`; the constants `C`
  and `d` are quantified before `n`, the parameters, and the input graph.

The resource bound holds for **every** execution of the program, and hence also
almost surely under its probability kernel. The number of optimization calls is
also at most `2·card(Edge n)·T1·T2`.

The program implements Algorithms 1–4, including plus-before-minus witness
search, retirement, multiplicative-weights updates, mask and output updates,
preprocessing, and the public cap on the noisy mass estimates. Each SDP is solved
approximately by the deterministic ellipsoid method, as in the running-time
argument in the paper's proof of Theorem 1.

- The `RealMachine*` modules implement and count the numerical routines: PSD
  separation (including zero pivots), inverses, determinants, Cholesky
  factorization, ellipsoid initialization and updates, and the approximate
  optimizer. The optimizer's operation count is polynomial in the dimension and
  in the logarithms of the geometry and accuracy scales.
- The `TypedMachine*` and `Typed*Program` modules and their refinement proofs
  implement the release controller with typed arithmetic terms, scalar random
  draws, finite loops, and calls to these numerical programs.
- `TypedMachine.Term.execute_eq` identifies the values and operation counts of
  pure expressions, and `TypedMachine.Budget.execution_bound` and
  `TypedMachine.Budget.sound` derive execution bounds from the program text. The
  public calibration, including the requested accuracy and the loop schedules, is
  itself computed by counted expressions.
- `TypedMachine.implementedLaw_reference` identifies the program's output law with the
  approximate release `VerifiedRelease.release`, which is within total variation
  `min(β/2, δ/(2(1+e^ε)))` of the ideal mechanism of `theorem1_statistical` run
  with δ and β halved. Privacy and accuracy transfer from the statistical theorem.

### Computational model

Running time is measured in a real RAM. The low-level machine
([`DPCut/RealMachine.lean`](DPCut/RealMachine.lean)) has real, natural-number,
and Boolean registers with computed addresses. Its expressions are literals,
register reads, `+`, `−`, `×`, `÷` on reals and on naturals, negation, `sqrt`,
`log`, `exp`, floor, ceiling, casts, comparisons, Boolean connectives, and
selection. Its commands are assignments, the draw of one standard Gaussian or one
standard Laplace scalar, sequencing, branching, and loops with a computed
iteration count. Each expression node costs one operation, and each command adds
a constant. Programs cannot invoke arbitrary functions, optimization results, or
claimed costs. The typed controller adds pairs, arrays of public length, `min`,
`max`, `abs`, and sums and maxima over arrays (charged in proportion to the array
length), and it calls the low-level factorization and solver programs, whose
operation counts come from their executions.

The model uses exact real numbers and exact scalar Gaussian and Laplace samples.
Finite-precision arithmetic, finite-bit sampling, and bit complexity are not
considered: as for any real RAM, operation counts are not bit-level costs.
Public indexing and structural register layouts are not charged as bit operations.

`Audit.lean` checks that the dependencies of `theorem1_machine` include the
actual execution, oracle, and solver proofs, and none of the cost-interface
hypotheses `LSWStatement`, `CuttingPlaneFamily`, `TimedAlgorithm`,
`ExactSDPOracleCost`, and `ApproxSDPOracle` (see
[Assigned-cost versions of Theorem 1](#assigned-cost-versions-of-theorem-1)).

### The statistical theorem

[`DPCut/Theorem1.lean`](DPCut/Theorem1.lean) proves `theorem1_statistical hn hp`
for the ideal mechanism `fullReleaseLaw`, which uses exact SDP optimizers. The
statement fixes the mechanism and the error constant: the law is measurable, is a
probability measure on every input, produces nonnegative weights almost surely,
is **(ε,δ)-edge-DP**, and has simultaneous all-cut error
**γ·cut(w,S) + 2^166·mainError(n,p)** with probability at least **1 − β**.
The constant is uniform over n, all public parameters, and the input graph.
`theorem1_statistical_exists : MainStatisticalStatement` is its existential form,
used by the application reductions. `parameter_choice` proves privacy and bounded
utility with the same constants.

### Approximate optimization

**Ellipsoid method.**
[`DPCut/EllipsoidFeasibility.lean`](DPCut/EllipsoidFeasibility.lean) proves a
deterministic ellipsoid feasibility method that takes an ordinary
point-separation oracle: the central-cut update, containment, determinant
contraction, volume lower bounds, and termination. If the feasible set contains a
ball of radius `r > 0` and lies in a ball of radius `R > 0` in dimension `d ≥ 1`,
the method succeeds with at most `floor(2·d·(d+2)·log(R/r)) + 1` oracle calls.
`EllipsoidOptimization`, `EllipsoidAccuracy`, and `EllipsoidCallBounds` extend
this to concave optimization, and the `RealMachineSolver*` modules implement the
resulting solver on the real RAM: initialization, the feasibility and search
controller, matrix decoding, the objective-gap guarantee, and the polynomial
operation bound.

**The SDP.** The log-determinant program is solved over a bounded redundant
space of `n²` Euclidean coordinates, which maps onto all feasible SDP matrices,
contains a ball of radius `1/4`, and lies in a ball of radius `2n`. The objective
has a proved supergradient, concavity, and range bound.

**Noisy-mass cap.** Each outer round caps the noisy mass estimate at a public
bound, using `min (card(Edge n)*U + 2*tau2) (max 0 (mass wi + noise + tau2))`, as
in the paper's implementation. All release laws, including the ideal one, use
this cap. Privacy follows by post-processing, and on the utility good event the
cap is inactive. `MassClipping.lean` proves the mass bounds for the initial
estimate and every multiplicative-weights update, and the resulting bound for both
discrepancy objectives under the mask and nonnegativity invariants. Hence every
objective reached in the release is bounded by a public quantity.

**From optimization accuracy to output accuracy.** `OptimizerApproximation.lean`
proves `ObjectiveGapStatement`: objective gap at most `lam * mu^2 / (2*n^4)`
implies normalized covariance Frobenius error at most `mu`. `GaussianKL.lean`
derives the exact KL divergence between Gaussian batches from the densities,
absolute continuity, and integrability of the log-likelihood.
`CovarianceApproximation.lean` proves `ApproximateGaussianStatement`, including
the coefficient `k * mu^2 / 2`. `KLTotalVariation.lean` proves the eventwise
bound `TV <= 2*sqrt(KL)`, using Jensen's inequality and the Radon–Nikodym
derivative. `OptimizerTV.lean` derives the Gaussian batch error `2*sqrt(k)*mu`
and the FindWitness error `K*2*sqrt(k)*mu` from the objective gap, using the
actual score and acceptance maps. `ApproximationTransfer.lean` contains the
half-budget calibration, error-constant absorption, and high-probability
transfer; `OracleReplacementTV.lean` accumulates the errors through all adaptive
loops.

## Lemmas 10–23

Each lemma below is proved for a Lean statement that follows the paper;
`LemmaComparison.tex` shows both side by side, with comparison notes.
`DPCut/LemmaNN.lean` contains `DPCut.lemmaNN`, and `lake build DPCut.LemmaNN`
compiles it with its dependencies; `Audit.lean` prints its axioms.

**Lemma 10.** [`DPCut/Lemma10.lean`](DPCut/Lemma10.lean) contains
`DPCut.lemma10 : DPCut.ChiStatement`, with universal constant **C = 96**.
Its immediate prerequisites are proved in [`DPCut/ChiSquare.lean`](DPCut/ChiSquare.lean)
(chi-square failure probability at most `2 * exp (-k / 32)`) and
[`DPCut/GaussianWitness.lean`](DPCut/GaussianWitness.lean)
(feasibility bounds and the exact normalized Gaussian law).
The proof includes measurability, the union bound, and clipping.

**Lemma 11.** [`DPCut/Lemma11.lean`](DPCut/Lemma11.lean) contains
`DPCut.lemma11 : DPCut.ChaosStatement`, with **C = 512** and **c₀ = 1/2048**,
for arbitrary signed weights and conditioned on the event `ChiGood`.
Its prerequisites derive Gaussian moments through order eight, the centered
quadratic fourth-moment bound, and a one-sided probability bound using mathlib's
spectral theorem. The batch witness is identified with the concrete quadratic
form, and its mean is computed exactly. The proof does not use the general
hypercontractivity lemma (Lemma 25).

**Lemma 12.** [`DPCut/Lemma12.lean`](DPCut/Lemma12.lean) contains
`DPCut.lemma12 : DPCut.PreprocessStatement`, with the paper's thresholds
**U = 8 log(n/β₀)/(ε₀γ)** and **V = 2 log(n/β₀)/ε₀**.
The release of the noisy excess is **ε₀-pure-DP**. With probability at
least **1 − β₀**, adding the private clipped weights gives simultaneous relative
cut error **γ/2**, with no additive error. The clipped weights are not released.
The proof includes clipping decomposition and sensitivity, the joint product
Laplace density, normalization, measurable postprocessing, and a simultaneous
noise bound. Its failure estimate is at most `card(Edge n) * (β₀/n)^2 ≤ β₀`.
The statement assumes `n ≥ 2`, nonnegative weights, and `ε₀,β₀,γ ∈ (0,1)`;
the intermediate proofs do not need the upper bounds on ε₀ or γ.

**Lemma 13.** [`DPCut/Lemma13.lean`](DPCut/Lemma13.lean) contains
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
it does not use a separate strict-concavity result.

**Lemma 14.** [`DPCut/Lemma14.lean`](DPCut/Lemma14.lean) contains
`DPCut.lemma14 : DPCut.GaussianPrivacyStatement`, with universal constant **C = 4**,
for the paper's range **0 < δ₁ < 1/2**. Both covariance matrices are positive
definite and their relative Frobenius distance is strictly less than 1/2.
`lemma14_density` proves the displayed product-of-densities inequalities;
`gaussianDensity_eq` identifies the exponential form with the paper's explicit
Gaussian density formula. The proof establishes the exact distributional change
of coordinates and the log-likelihood decomposition, then applies Lemma 15.
It uses relative precision eigenvalues instead of their logarithms.

**Lemma 15.** [`DPCut/Lemma15.lean`](DPCut/Lemma15.lean) contains
`DPCut.lemma15 : DPCut.WeightedChiSquareStatement`, with the exact constant **2**,
arbitrary signed weights, and strict tail event from the paper. The proof derives
the centered Gaussian-square exponential moment, its sharp bound, and an optimized
Chernoff estimate, then applies it to both signs. `lemma15_independent` gives the
same result for independent standard normals on any probability space.

**Lemma 16.** [`DPCut/Lemma16.lean`](DPCut/Lemma16.lean) contains
`DPCut.lemma16 : DPCut.SuccessChargedStatement`, with the exact parameters
**ε = 4L + 4ℓ* log(1/δ'')** and **δ = δ'' + (1 + exp ε) kδ'**.
In the statement, the outputs form any standard Borel space,
the auxiliary distributions are measurable Markov kernels, and the successful
charge budget holds almost surely under each auxiliary process.
The proof includes measurability of finite transcripts, propagation of absolute
continuity on common histories, the kernel density chain rule, the one-step
exponential moment, its finite-horizon induction, and the TV transfer.
It covers ℓ* = 0 and zero mass at the failure symbol.

**Lemma 17.** [`DPCut/Lemma17.lean`](DPCut/Lemma17.lean) contains
`DPCut.lemma17 : DPCut.AggregatePrivacyStatement DPCut.privacyConstants`
for `aggregateLaw`, with explicit trial coefficient **8192**, batch coefficient
**512**, and regularization coefficient **2³⁰**. Lemma 20 uses the same oracle
and fixes the certificate constant to 16; `parameter_choice` supplies a shared
choice for aggregate privacy/utility and bounded-release privacy/utility.
The proof includes optimizer continuity, the actual Gaussian and Laplace
densities, measurable conditioned auxiliary laws, all K trials, normalization
and support of accepted witnesses, the auxiliary success budget, and Lemma 16.
The padded transcript is proved equal to the aggregation law.
The calibration gives `λ ≥ 8`, which ensures the strict `< 1/2` covariance-distance
requirement of Lemma 14. Theorem 1 uses these same oracle coefficients.

**Lemma 18.** [`DPCut/Lemma18.lean`](DPCut/Lemma18.lean) contains
`DPCut.lemma18 : DPCut.MainPrivacyStatement DPCut.privacyConstants`.
It proves `(ε,δ)` privacy of `cutReleaseLaw`, with the paper's
parameter choices, `n ≥ 2`, `U ≥ 1`, `0 < ε ≤ 1`, and `δ,β,γ ∈ (0,1)`.
The prerequisites include the translated Laplace mechanism, mask sensitivity,
measurability and probability normalization of both loops, residual-mask support,
and exact identification of early stopping with a padded adaptive process.
Basic and advanced composition are proved from measurable pure-private subparts
and mathlib's Hoeffding bound; they are not assumed as axioms or hypotheses of
Lemma 18. The composition results use symmetric neighboring pairs explicitly.
The inner budget is `(ε/(2T₁), δ/T₁)`; adding the mass release and composing
`T₁` outer rounds gives exactly `(ε,δ)`. The constants are the same as Lemma 17;
`mainPrivacy_shared` proves the same statement for the constants of Lemma 22,
which Theorem 1 uses.

**Lemma 19.** [`DPCut/Lemma19.lean`](DPCut/Lemma19.lean) contains
`DPCut.lemma19 : DPCut.SDPCertificateStatement`, with universal constant **C = 2**,
arbitrary signed weights, `n ≥ 2`, and `λ > 0`. It includes the exact inequality
`mass D ≤ 2 * optimum λ D`. The stronger helper `sdp_cut_bound` gives additive
error `2λn log n + ‖D‖₁/n` and also allows `λ = 0`.
[`DPCut/ShrunkenCut.lean`](DPCut/ShrunkenCut.lean) proves feasibility, the query
formula, the exact determinant and the logarithmic penalty bounds for `X_S`.
`lemma19_shrunken` proves the exact shrunken-cut certificate statement
`ShrunkenCutCertificateStatement`.

**Lemma 20.** [`DPCut/Lemma20.lean`](DPCut/Lemma20.lean) contains
`DPCut.lemma20 : DPCut.AggregateUtilityStatement DPCut.utilityConstants`.
It proves both witness-sign inequalities, simultaneous accuracy of every residual
cut, and the partition invariant for `aggregateLaw`. The explicit
error is **B = 16(τ₁ + λn log n + nU)**. The oracle parameters are identical to
Lemma 17's; `aggregate_privacy_and_utility` proves both results with these constants.
The proof includes finite active-edge retirement, the log-determinant bound,
exact Laplace tails, signed-witness normalization, fresh-trial success, and an
adaptive failure bound. In particular, running out of aggregate fuel cannot
leave active coordinates on a run of valid witnesses.

**Lemma 21.** [`DPCut/Lemma21.lean`](DPCut/Lemma21.lean) contains
`DPCut.lemma21 : DPCut.InnerRoundStatement DPCut.utilityConstants`.
Under the statement's explicit stopping-threshold hypothesis
`stop ≥ 10(B + τ₂/γ)`, it proves the joint success probability
**1 − T₂β_GE − β₂**, with the exact horizon
**T₂ = 1 + ⌈64(1+γ)² log n / γ²⌉**.
The prerequisites prove finiteness and the finite-sum formula for mathlib's
normalized KL, mass and support preservation, the initial potential bound,
both witness-selection margins, and the exact potential decrease
**γ²M/[64(1+γ)²]**. The latter also proves `MWProgressStatement`.
The probability argument integrates over the noisy mass and adaptive oracle
calls; it does not replace the joint assertion with a conditional guarantee.
Lemma 22 below verifies the stopping-threshold hypothesis for its explicit
choice of constants.

**Lemma 22.** [`DPCut/Lemma22.lean`](DPCut/Lemma22.lean) contains
`DPCut.lemma22 : DPCut.OuterRoundStatement DPCut.outerUtilityConstants`.
It proves that the actual stopping test is reached with probability at least
**1 − T₁T₂β_GE − T₁β₂**, with **T₁ = ⌈80 log(nU)⌉**. This includes the noise
in the stopping round and reserves a round for that final test.
The proof averages the simultaneous cut guarantee to obtain additive mass error
`2B`, proves residual mass contraction by **19/20**, and accounts for inner
success and contraction on the same oracle good event.
`outerUtilityConstants` uses the oracle and certificate coefficients from
Lemma 20, the outer coefficient **80**, and the stopping coefficient **2¹²⁰**.
These deliberately coarse universal constants are fully verified:
`outer_stopping_threshold` proves `stop ≥ 10(B + τ₂/γ)` for every admissible
input, so `OuterRoundStatement` needs no assumptions beyond the paper's.

**Lemma 23.** [`DPCut/Lemma23.lean`](DPCut/Lemma23.lean) contains
`DPCut.lemma23 : DPCut.BoundedUtilityStatement DPCut.outerUtilityConstants`.
With probability at least **1 − β**, the bounded CutRelease output satisfies,
simultaneously for every cut, relative error **γ** and additive error
**2¹²¹(nUℒ + nℒ⁷/(γε))**, where **ℒ = log(nU/(δβγε))**.
The coefficient is explicit and independent of all inputs; the constants are
those of Lemma 22.
The proof tracks accuracy of the retired weights `w − a ⊙ w`, adds `B` for each
released portion, and bounds the discarded residual by the stopping threshold.
Inner success, contraction, and all-cut accuracy share one good event, so the
total failure budget is exactly `T₁T₂β_GE + T₁β₂ = β`.
`cutRelease_utility_explicit` gives the sharper intermediate error `T₁B + stop`.
`cutRelease_nonnegative` separately proves nonnegative output almost surely,
including on utility failures and fallback branches.

## Theorem 38 (lower bound)

[`DPCut/Theorem38.lean`](DPCut/Theorem38.lean) contains
`theorem38 : LowerBoundStatement`, with the uniform absolute constant
**c = 2⁻³⁰**, for the paper's ranges n ≥ 33, ε ∈ (0,1), 0 ≤ δ ≤ ε/100,
β ∈ (0,1/40], and γ ∈ [0,1), including the explicit convention for γ = 0.
The prerequisites prove group privacy, measurable finite decoding, a Hamming
reconstruction bound, and the bipartite and star hard-family estimates.
A direct finite Rademacher-moment argument supplies the required discrepancy
bound in place of the general graph-discrepancy lemma (Lemma 37). No
computational or SDP-oracle assumption is used. The stronger helper
`theorem38_explicit` also shows that nonnegative output weights are unnecessary
for this lower bound.

## Applications (Appendix C)

| Paper | Lean | File |
| --- | --- | --- |
| Corollary 2 | `private_correlation_clustering` | [`Theorem30.lean`](DPCut/Theorem30.lean) |
| Corollary 3 | `private_max_cut` | [`Theorem32.lean`](DPCut/Theorem32.lean) |
| Lemma 28 | `lemma28` | [`KLPythagorean.lean`](DPCut/KLPythagorean.lean) |
| Lemma 29 | `lemma29` | [`Lemma29.lean`](DPCut/Lemma29.lean) |
| Theorem 30 | `theorem30` | [`CCApplication.lean`](DPCut/CCApplication.lean) |
| Corollary 31 | `corollary31` | [`Theorem30.lean`](DPCut/Theorem30.lean) |
| Theorem 32 | `theorem32` | [`Theorem32.lean`](DPCut/Theorem32.lean) |
| Remark 33 | `remark33` | [`Remark33.lean`](DPCut/Remark33.lean) |
| Theorem 34 | `theorem34`, `theorem34_transfer` | [`Theorem34.lean`](DPCut/Theorem34.lean) |
| Lemma 35 | `lemma35` | [`Lemma35.lean`](DPCut/Lemma35.lean) |
| Theorem 36 | `theorem36` | [`Theorem36.lean`](DPCut/Theorem36.lean) |

These results prove the privacy and approximation guarantees. Where the paper
uses a cited algorithm, the Lean statement takes that algorithm's guarantee as an
explicit hypothesis (a contract): the correlation-clustering results take a
private baseline (`CCBaselineFamily`) and a nonprivate approximation contract, the
Max-Cut corollary takes the Goemans–Williamson contract
`MaxKCutContract 2 (878 / 1000)`, and Theorem 36 takes `InducedARVContract`, a
one-cut weighted ARV contract. No contract is asserted to be inhabited or
introduced as an axiom, and none of these results takes `LSWStatement`.

- Lemma 29's capped mechanism is a measurable sampling kernel, with privacy, an
  almost-sure coordinate cap, and error `2^126 * mainError n p` (logarithmic
  exponent 7). Its KL projection is given by a finite formula with `m+1`
  threshold candidates, including changes of support.
- The correlation-clustering proofs include independent Bernoulli rounding,
  simultaneous concentration over all partitions, amplification, adaptive
  privacy composition, and error calibration uniform in n. The baseline
  contract's δ budget is a function of n, so its additive constants are uniform
  in n.
- Remark 33's lower bound, Lemma 35 (with constant `1 / b²`), and the exact and
  balanced hierarchy transfer bounds are proved. The proof of Theorem 36
  includes public fallback cuts, amplification, recursion with at most n−1
  successful split steps, an exact balanced analysis comparator, and the final
  `n log^(3/2) n` error.
- The unnumbered bisection, expansion, and uniform-sparsity reductions are
  included; odd-order bisection padding preserves cut values and the optimum
  exactly.

**Cost accounting.** The applications' running times are not verified. Their
costs are accounted for in the assigned-cost interface of the
[next section](#assigned-cost-versions-of-theorem-1), on top of the
Lee–Sidford–Wong release:

- `AppendixRuntime.lean` provides polynomial assigned-cost certificates and law
  equalities for correlation clustering, Max-k-Cut, constrained cuts, and
  hierarchical clustering. These theorems take `LSWStatement`, construct the
  solver family with the full `verifiedLinearAlgebra` implementation, and keep
  the external application-algorithm contracts; no SDP-oracle contract is used.
  Their law equalities identify the actual approximate kernels, whose privacy and
  utility are proved in `LSWCCKernel.lean` and `LSWApplicationGuarantees.lean`.
- `ImplementedApplications.lean` combines these with the final error
  calibrations and a reported-cost realization of the same kernel. In namespace
  `LSWApplications`, `theorem30`, `corollary31`, `theorem32`, `theorem34`, and
  `theorem36`, together with `private_correlation_clustering` and
  `private_max_cut`, state the combined results; `constrained_cut_general`
  allows arbitrary valid privacy and accuracy parameters. `RealizedWithin`
  records equality of the costed program's output law and the private kernel,
  with a uniform cost bound. The combined statements fix the program
  construction and the supplied external algorithms. The correlation-clustering
  calibration accepts any positive release constant and is instantiated at
  `2^138`; additive constants are independent of k and of the source success
  probability. Cost constants may depend on the external approximation
  algorithm.
- Correlation clustering uses the capped release of `CappedLSWRelease.lean`: the
  approximate witnesses run inside the capped loops, with bounded objectives,
  public timeouts, and restarts. `CappedReplacementTV.lean` bounds the
  accumulated error, reserving half of the privacy δ and of the failure budget.
  The output is capped almost surely, is (ε,δ)-private on capped inputs, and has
  error `2^138 * mainError n p` with failure probability at most β. The other
  applications use the `2^178 * mainError n p` bound of the full release. These
  universal constants differ from those of the ideal statistical proofs; the
  approximation factors and the asymptotic orders of the additive errors are the
  same. `CappedLSWRuntime.lean` proves a polynomial assigned-cost bound in
  `runtimeScale n p`; the configured solver's timeout is polynomial in the
  logarithm of the inverse precision, and its retry count is logarithmic.
  `CappedLSW.capped_release_of_lsw` combines privacy, the output cap, utility,
  and this cost bound for one program; `cc_cost_polynomial` specializes it to
  the application.

The external contracts include statistical guarantees and bounds on assigned
costs. They permit arbitrary kernels priced at zero, so they do not certify the
running times of the cited algorithms. `Audit.lean` checks that the dependencies
of the cost results include neither `ExactSDPOracleCost` nor `ApproxSDPOracle`.

## Assigned-cost versions of Theorem 1

Besides `theorem1_machine`, the development proves versions of Theorem 1 whose
cost conclusion is stated in an abstract cost interface instead of the machine
model; the Appendix C cost accounting builds on them. `MainTheoremStatement` is
parameterized by a `ComputationalModel`, and `CostedLaw`, `Arithmetic`, and
`TimedAlgorithm` pair values or laws with **assigned** costs. These types do not
define an execution semantics that derives costs from instructions; for example,
`TimedAlgorithm` admits any measurable function with reported completion time
zero. The cost conclusions of these results, including those of the theorems
named `runtime`, are therefore accounting statements, not running-time bounds.
Their privacy and accuracy conclusions are proved for the specified kernels,
assuming the solver guarantees in their hypotheses.

**Lee–Sidford–Wong release.** [`DPCut/Theorem1LSW.lean`](DPCut/Theorem1LSW.lean)
proves

```lean
theorem1_of_lsw (hLSW : LSWStatement) :
  MainTheoremStatement (realArithmeticLSWModel hLSW)
```

`LSWStatement` is a proposition parameter, not an axiom. It is intended to
express a polynomial specialization of
[Lee–Sidford–Wong, Theorem 42](https://arxiv.org/pdf/1508.04874) for exact
separation and first-order oracles. Its `TimedAlgorithm` interface records a
completion-time label and a compatible timeout law, but does not require the
labels to count execution steps or oracle calls. Hence the hypothesis does not
isolate an operational version of LSW, and supplying it does not establish a
running time.

The proof formalizes the restart argument of the paper's footnote on the
Lee–Sidford–Wong running time, at the level of assigned costs; the footnote's
`Õ(n^8)` bound is not formalized. For the public radius
`r = approximationRadius n p`, the solver requests objective gap `r²/(8*n⁴)`.
Each run is cut off after a public bound of twice its expected reported cost,
rounded up. Independent restarts reduce the failure probability to at most
`r/2`, and a failed solve returns the feasible identity matrix. The proof
includes this failure probability in the total-variation bound and proves that
the release is **(ε,δ)-edge-DP**, graph-valued, and has all-cut error
**γ·cut(w,S) + 2^178·mainError(n,p)** with probability at least **1 − β**. One
program, coefficient, and degree give a uniform polynomial bound on the assigned
cost in `runtimeScale n p`. The solver's cost depends logarithmically on the
objective magnitude and the precision. A guard replaces objectives outside the
public bound by zero, which makes costs uniform even over unreachable values in
`CostedLaw.bind`; the guard is proved inactive along the actual execution. No
exact optimizer or SDP-oracle contract is assumed.
`theorem1_of_lsw_with_implementation` accepts any counted implementation with
proved refinement and cost bounds, and `theorem1_of_lsw` supplies the
constructed one.

**Linear algebra and sampling.**
[`VerifiedLinearAlgebra.lean`](DPCut/VerifiedLinearAlgebra.lean) constructs the
linear-algebra implementation used in this interface and its cost certificate.
Recursive scalar Schur elimination handles PSD testing, including zero pivots
and explicit negative quadratic-form witnesses. The same machinery solves
positive-definite linear systems, computes inverses and determinants, and
constructs a Cholesky factor. The proofs include measurability and exact
agreement with the mathlib matrix notions and covariance Gaussian laws.

The `Arithmetic` routines compose counters for scalar operations, comparisons,
and stored vector entries; constants, indexing, and structural rearrangement are
free in this accounting. The `Arithmetic` type itself is a value/count pair and
does not enforce that convention for arbitrary inhabitants. The proved bounds
are `100*(n+1)^3` for PSD separation, `21*(n+1)^4` for inversion, `10*(n+1)^3`
for determinants, and `20*(n+1)^3` for factorization. The complete separation
and first-order oracle, including the objective guard and coordinate adjoint,
fits the charge `1000*(n+1)^6 + 200*(n+1)^3`. The optimizer's fallback has a
separate feasibility-check implementation and cost bound.

`ScalarGaussianSampling` implements finite products by sequential scalar draws.
`VerifiedGaussianSampling` combines these draws with the factorization and
matrix-vector routines; its law is exactly `gaussianBatch`, and its cost is at
most `gaussianBatchCost`. The outer vector and arithmetic blocks have fixed
macro costs, and exact scalar sampling and elementary real functions are
primitives. The operation counts of `theorem1_machine` do not use any of these
charges.

`LSW.Oracle` takes an `Arithmetic` program and a proof that its operation count
fits the charge; the SDP oracle supplies `oracleProgram`, `oracle_value`, and
`oracle_cost`. The solver family preserves the supplied implementation, and
`mapArithmetic` executes its counted decoder, charging the supremum of its
operation counts. The witness trials call `verifiedGaussianBatch` directly;
their law and cost proofs use its distribution and operation bounds. Positive
definiteness follows from feasibility of every solver output, including
fallbacks.

**SDP-oracle versions.**
[`DPCut/Theorem1Oracle.lean`](DPCut/Theorem1Oracle.lean) proves
`theorem1 (sdp : ApproxSDPOracle) : MainTheoremStatement (realArithmeticOracleModel sdp)`
and `theorem1_exact_oracle (sdp : ExactSDPOracleCost)` for
`realArithmeticExactOracleModel sdp`. Their parameters are contracts for an
external SDP solver. In the approximate version, the solver returns a measurable
choice of feasible matrix X satisfying
`optimum lam D - objective lam D X <= lam * mu^2 / (2*n^4)` for the requested
`0 < mu <= 1/2`, with charge at most `C_SDP * (1+n+abs(log mu))^d_SDP`,
uniformly in the real objective D and the regularization lam. This is an
explicit assumption, not a consequence of Lee–Sidford–Wong or of a verified
implementation.

The release uses the returned covariance for its Gaussian draws.
`OracleReplacementTV.lean` proves error accumulation through all adaptive loops.
Writing `c = fullRunConfig n (precisionParameters p)` and
`B = 4 * card(Edge n) * c.T1 * c.T2 * c.oracle.K * (c.oracle.k+1)`, the release
requests `mu = beta*delta / (16*(1+B))`. The output law is within
`min(beta/2, delta/(2*(1+exp epsilon)))` of the ideal law run with δ and β
halved, and the final coordinatewise nonnegative projection fixes the ideal law
almost surely. The mechanism is **(ε,δ)-DP**, has nonnegative output, and
satisfies the simultaneous cut guarantee with constant **2^178**, failure
probability β, and logarithmic exponent 7. `costedApproxRelease_law` identifies
the costed law with the approximate mechanism; bind takes a supremum over
**all** intermediate values. One program, coefficient, and degree bound the
assigned costs, including the precision charge, for all admissible n, p, and w,
using:

| Operation | Assigned cost |
| --- | --- |
| Scalar Laplace draw | 1 |
| Finite vector/arithmetic block | `100 (n+1)^2` |
| Verified dense Gaussian batch of k vectors | `100 (n+1)^3 (k+1)` |
| Preprocessing noise and clipping | `card(Edge n) + 100 (n+1)^2` |

## Scope and limitations

- **Computational model.** Running times are operation counts in the real RAM
  described [above](#computational-model), with exact real arithmetic and exact
  scalar Gaussian and Laplace sampling. Bit complexity and finite-precision
  implementations are not formalized.
- **Lee–Sidford–Wong.** The `Õ(n^8)` running time in the paper's footnote and
  the Lee–Sidford–Wong algorithm itself are not formalized. `LSWStatement`
  appears only as a hypothesis of assigned-cost results.
- **Applications.** The cited algorithms (the private correlation-clustering
  baseline, nonprivate approximation algorithms, Goemans–Williamson, and ARV)
  enter through contracts, and the applications' running times are covered only
  by assigned-cost accounting.
- **Auxiliary lemmas.** The following results of the paper have Lean statements
  (in `Statements.lean` and `Privacy.lean`) but no standalone proofs; the proofs
  establish the special cases they need instead.
  - Lemmas 6–8 (Laplace mechanism, post-processing, basic composition) are
    proved in the forms used, for example `shifted_laplace_pi_private`,
    `pure_adaptive_composition`, and `approximate_adaptive_composition`.
  - Lemma 24 (chi-square tail): the proof of Lemma 10 proves the bound
    `2 * exp (-k / 32)` that it needs (`ChiSquare.lean`).
  - Lemmas 25 and 26 (Gaussian hypercontractivity and interpolation of `L_p`
    norms): the proof of Lemma 11 proves the required moment bounds directly.
  - Proposition 27 (unbiased estimator): the proof of Lemma 11 computes the
    required expectation directly (`WitnessQuadratic.lean`).
  - Lemma 37 (graph discrepancy): the proof of Theorem 38 uses a direct finite
    Rademacher-moment argument.

## Building and checking

The project pins Lean **4.24.0** and mathlib tag **v4.24.0**, commit
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`; transitive dependencies are pinned in
`lake-manifest.json`. On a new machine, install Lean using the
[Lean community installation instructions](https://leanprover-community.github.io/install/);
the [mathlib dependency instructions](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency)
explain how to fetch the pinned package and its compiled cache. From this
directory:

```bash
lake exe cache get
lake build
bash check.sh
```

`check.sh` runs `lake build` and then `lake env lean Audit.lean`; it uses a local
toolchain under `.tools/lean-4.24.0-linux` if present. The local toolchain,
dependency sources, and build products are ignored by Git. To compile a single
result and its dependencies, run for example `lake build DPCut.Theorem1Machine`.

[`Audit.lean`](Audit.lean) prints the axioms of the main results and checks that

- every project declaration, including helper, private, and generated ones,
  depends only on `propext`, `Classical.choice`, and `Quot.sound`;
- the proof of `theorem1_machine` uses the machine execution, the SDP oracle
  program, and the ellipsoid solver, and none of the assigned-cost interfaces;
- the Appendix C cost results use neither SDP-oracle contract.

`python3 make_lemma_comparison.py` regenerates `LemmaComparison.tex` from the
paper's LaTeX source, which it reads from `../STOC2027.tex`. The document pairs
all 38 numbered environments of the paper (including definitions and the Max-Cut
remark) with their Lean statements and the theorems proving them, and records
comparison notes, external hypotheses, source locations, and the source hash.
Comments, `\iffalse` blocks, and `\junk{...}` arguments of the source are
ignored. The document is standalone; compile it from this directory with
`pdflatex LemmaComparison.tex` twice.
