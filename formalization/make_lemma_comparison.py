#!/usr/bin/env python3
"""Pair the paper's statements with their Lean definitions.

Run from any directory. Only LemmaComparison.tex is written. The extraction is
specific to this manuscript and the declaration layout of this Lean project.
"""

from pathlib import Path
from collections import Counter
import hashlib
import re

ROOT = Path(__file__).resolve().parent
PAPER = ROOT.parent / "STOC2027.tex"
OUTPUT = ROOT / "LemmaComparison.tex"

# Keep this mapping explicit: declaration names alone do not establish that two
# statements correspond. These associations follow the source labels.
PAIRS = {
    "thm:main": ("Private relative cut release", "Statements", ["MainStatisticalStatement", "MainTheoremStatement"]),
    "cor:cc-intro": ("Private correlation clustering", "Applications", ["CorrelationClusteringStatement"]),
    "cor:maxcut-intro": ("Private Max-Cut", "Applications", ["PrivateMaxCutStatement"]),
    "def:DP": ("Adjacency and edge differential privacy", "Definitions", ["Adjacent", "DP", "EdgeDP"]),
    "def:laplace-dist": ("Laplace distribution", "Definitions", ["laplaceDensity", "laplace"]),
    "lem:laplace-mech": ("Laplace mechanism", "Privacy", ["LaplaceMechanismStatement"]),
    "lem:post-processing": ("Post-processing", "Privacy", ["PostProcessingStatement"]),
    "lem:basic-composition": ("Basic adaptive composition", "Privacy", ["BasicCompositionStatement"]),
    "lem:advanced-composition": ("Advanced adaptive composition", "Privacy", ["AdvancedCompositionStatement"]),
    "lem:chi": ("Coordinatewise Gaussian witness estimate", "Statements", ["ChiStatement"]),
    "lem:chaos": ("A useful witness with constant probability", "Statements", ["ChaosStatement"]),
    "lem:preprocess": ("Preprocessing", "Statements", ["PreprocessStatement"]),
    "lem:stability_of_optimizer": ("Stability of the SDP optimizer", "Statements", ["OptimizerStabilityStatement"]),
    "lem:gaussian-privacy": ("Gaussian covariance privacy", "Statements", ["GaussianPrivacyStatement"]),
    "lem:concentration_chi-squares": ("Signed chi-square concentration", "Statements", ["WeightedChiSquareStatement"]),
    "lem:pay-what-you-get": ("Success-charged composition", "Privacy", ["SuccessChargedStatement"]),
    "lem:gradient_privacy": ("Privacy of AggregateWitnesses", "Statements", ["AggregatePrivacyStatement"]),
    "lem:main-privacy": ("Privacy of CutRelease", "Statements", ["MainPrivacyStatement"]),
    "lem:sdp_error": ("The SDP cut certificate", "Statements", ["SDPCertificateStatement"]),
    "lem:gradient_estimation": ("Utility of AggregateWitnesses", "Statements", ["AggregateUtilityStatement"]),
    "lem:inner_round": ("Number of inner iterations", "Utility", ["InnerRoundStatement"]),
    "lem:outer_round": ("Number of outer iterations", "Utility", ["OuterRoundStatement"]),
    "lem:utility": ("Utility of CutRelease", "Statements", ["BoundedUtilityStatement"]),
    "lem:chi_square_tail": ("Chi-square tail bound", "Statements", ["ChiSquareTailStatement"]),
    "lem:hypercontractivity": ("Gaussian hypercontractivity", "Statements", ["HypercontractivityStatement"]),
    "lem:holder_interpolation": ("Interpolation of Lp norms", "Statements", ["GeneralHolderInterpolationStatement", "HolderInterpolationStatement"]),
    "prop:unbiased_estimator": ("Unbiased fractional-query estimator", "Statements", ["UnbiasedWitnessStatement"]),
    "lem:pythagorean": ("KL Pythagorean inequality", "Applications", ["KLPythagoreanStatement"]),
    "lem:capped-unit-release": ("Capped unit-bounded cut release", "Applications", ["CappedReleaseStatement"]),
    "thm:cc-black-box-reduction": ("Private correlation-clustering reduction", "Applications", ["CCBlackBoxStatement"]),
    "cor:cc-fixed-k": ("Private fixed-k correlation clustering", "Applications", ["FixedKCorrelationClusteringStatement"]),
    "thm:private-max-k-cut": ("Private Max-k-Cut", "Applications", ["PrivateMaxKStatement", "MaxKTransferStatement"]),
    "rem:maxcut-tightness": ("Approximate-DP Max-Cut lower bound", "Applications", ["MaxCutLowerBoundStatement"]),
    "thm:private-constrained-cut": ("Private bicriteria cut minimization", "Applications", ["ConstrainedCutStatement"]),
    "lem:hc-bicriteria-recursion": ("Bicriteria balanced recursion", "Applications", ["HCRecursionStatement"]),
    "thm:private-hierarchical-clustering": ("Private hierarchical clustering", "Applications", ["PrivateHierarchyStatement", "HCTransferStatement"]),
    "lem:ekkl-discrepancy": ("Graph discrepancy", "Statements", ["EKKLDiscrepancyStatement"]),
    "thm:lower_bound": ("Lower bound for relative cut release", "Statements", ["LowerBoundStatement"]),
}

ADDITIONAL_STATEMENTS = {
    "def:laplace-dist": [("Statements", "LaplaceStatement")],
}

PROOF_DECLARATIONS = {
    "thm:main": [("Theorem1", "theorem1_statistical"),
                 ("Theorem1", "theorem1_statistical_exists"),
                 ("Theorem1LSW", "theorem1_of_lsw")],
    "cor:cc-intro": [("Theorem30", "private_correlation_clustering")],
    "lem:advanced-composition": [("AdaptiveComposition", "advanced_composition_statement")],
    "thm:cc-black-box-reduction": [("CCApplication", "theorem30")],
    "cor:cc-fixed-k": [("Theorem30", "corollary31")],
    "rem:maxcut-tightness": [("Remark33", "remark33")],
    "thm:lower_bound": [("Theorem38", "theorem38")],
    "cor:maxcut-intro": [("Theorem32", "private_max_cut")],
    "def:laplace-dist": [("LaplaceTail", "laplace_statement")],
    "lem:pythagorean": [("KLPythagorean", "lemma28")],
    "thm:private-max-k-cut": [("Theorem32", "theorem32")],
    "thm:private-constrained-cut": [("Theorem34", "theorem34_transfer")],
    "thm:private-hierarchical-clustering": [("Theorem36", "theorem36")],
}

# The strengthened statistical theorem names the mechanism directly; the
# separate existential corollary still references MainStatisticalStatement.
CONCRETE_PROOF_REFERENCES = {
    ("thm:main", "Theorem1", "theorem1_statistical"): ["fullReleaseLaw"],
    ("def:laplace-dist", "LaplaceTail", "laplace_statement"): ["LaplaceStatement"],
}

# Combined implementation theorems strengthen the statistical targets above.
# Their correspondence is explicit, rather than inferred from a target name.
IMPLEMENTATION_DECLARATIONS = {
    "thm:main": [("Theorem1Machine", "theorem1_machine")],
    "lem:capped-unit-release": [("CappedLSWRuntime", "capped_release_of_lsw")],
    "cor:cc-intro": [("ImplementedApplications", "private_correlation_clustering")],
    "cor:maxcut-intro": [("ImplementedApplications", "private_max_cut")],
    "thm:cc-black-box-reduction": [("ImplementedApplications", "theorem30")],
    "cor:cc-fixed-k": [("ImplementedApplications", "corollary31")],
    "thm:private-max-k-cut": [("ImplementedApplications", "theorem32")],
    "thm:private-constrained-cut": [("ImplementedApplications", "constrained_cut_general"),
                                    ("ImplementedApplications", "theorem34")],
    "thm:private-hierarchical-clustering": [("ImplementedApplications", "theorem36")],
}

BACKGROUND_RESULTS = {
    "lem:laplace-mech", "lem:post-processing", "lem:basic-composition",
    "lem:advanced-composition", "lem:concentration_chi-squares",
    "lem:chi_square_tail", "lem:hypercontractivity", "lem:holder_interpolation",
    "lem:pythagorean", "lem:ekkl-discrepancy",
}

APPLICATION_CONVENTION = (
    r"The statistical Lean statement records the guarantee. The combined implementation theorem "
    r"also provides a polynomial assigned-cost bound for the specified approximate program, using "
    r"the formal LSW parameter and cited external algorithm contracts. These interfaces allow "
    r"arbitrary kernels with cost zero; actual running times of the external algorithms and full "
    r"reduction are not certified. "
    r"It makes $\widetilde O(n)$ explicit as $C n(\log n)^d$ and high probability "
    r"as failure at most $C_{\rm fail}/n^2$, with constants chosen before $n$."
)

NOTES = {
    "thm:main": (
        r"The statistical theorem \texttt{theorem1\_statistical} explicitly names "
        r"\texttt{fullReleaseLaw}, bundling measurability, normalization, nonnegative "
        r"output, privacy and all-cut accuracy with constant $2^{166}$. "
        r"The first target is its existential corollary \texttt{theorem1\_statistical\_exists}. "
        r"The combined implementation theorem \texttt{theorem1\_machine} names the ellipsoid-based "
        r"program \texttt{TypedMachine.implementedRun}. It bundles measurability, normalization, "
        r"nonnegative output, privacy and all-cut accuracy with constant $2^{178}$, together with "
        r"polynomial instruction and optimization-call bounds for every execution. These counts are "
        r"derived by the interpreters of the restricted machines, not entered as prices. "
        r"The second target adds a polynomial bound on the "
        r"supplied model's cost. \texttt{theorem1\_of\_lsw} uses "
        r"\texttt{realArithmeticLSWModel} and the proposition parameter \texttt{LSWStatement}, "
        r"intended to specialize Lee--Sidford--Wong, Theorem~42 (arXiv:1508.04874v2). "
        r"Its \texttt{TimedAlgorithm} interface permits arbitrary measurable functions with "
        r"reported time zero. Thus this is cost accounting, not an operational runtime theorem "
        r"conditional only on the cited solver. The SDP geometry, public mass clipping, objective "
        r"and precision bounds, reported-time truncation, restarts and privacy/utility transfer "
        r"are proved internally. The constructed matrix routines, fallback decoder and covariance "
        r"Gaussian sampler are connected to the program through semantic refinement and counter "
        r"bounds. The value/count interfaces themselves do not enforce permitted instructions; "
        r"scalar sampling and outer-block prices remain model conventions. The parameter ranges, "
        r"nonnegative output and simultaneous cut guarantee with logarithmic exponent $7$ match "
        r"the paper. The identity covariance fallback matches the implementation footnote and "
        r"its failure probability is included in the total-variation budget. The LSW cost model "
        r"certifies neither actual polynomial runtime nor the footnote's sharper $\widetilde O(n^8)$ "
        r"bound; \texttt{theorem1\_machine} certifies polynomial running time in its real-arithmetic "
        r"machine model, not the sharper bound. The notation appendix expands the interfaces and certificates. "
        r"The SDP-oracle contracts and the application contracts share the assigned-cost limitation."
    ),
    "cor:cc-intro": APPLICATION_CONVENTION + r" Here \texttt{id} allows up to $n$ clusters, so the optimum is unrestricted.",
    "cor:maxcut-intro": APPLICATION_CONVENTION + r" The ratio is $878/1000-\xi$, with at most two clusters.",
    "def:DP": r"\texttt{Adjacent} defines the $\ell_1$ distance condition. \texttt{EdgeDP} restricts both inputs to nonnegative weights. Quantification over ordered adjacent pairs supplies both directions of the privacy inequality.",
    "def:laplace-dist": r"\texttt{laplaceDensity} is the real-valued density, and \texttt{laplace} is the measure obtained from it. \texttt{LaplaceStatement} records normalization and the tail identity for $b>0$.",
    "lem:laplace-mech": r"Lean uses a sensitivity upper bound $\Delta$ and explicitly handles $\Delta=0$ in \texttt{laplaceMechanism}.",
    "lem:advanced-composition": r"The hypothesis \texttt{Symmetric adj} ensures that each per-step DP guarantee holds in both directions. The paper's edge adjacency already has this property. The displayed theorem proves the full generic target, including $k=0$ and the trivial case $\delta_0\geq1$, without adding hypotheses.",
    "lem:chaos": r"The conditional probability is written as a ratio of two probabilities; positivity of its denominator is part of the statement. The Lean theorem chooses $c_0=1/2048$, whereas the paper's proof obtains $1/648$; both satisfy the stated existential constant guarantee.",
    "lem:stability_of_optimizer": r"The paper's implicit assumptions $n\geq2$ and $\lambda>0$ are explicit. \texttt{covarianceDistance} uses the Frobenius norm, not the default matrix norm.",
    "lem:gaussian-privacy": r"Lean states the equivalent bound on the absolute log-density ratio. Both statements require $0<\delta_1<1/2$.",
    "lem:pay-what-you-get": r"Lean states indistinguishability for one neighboring pair. Applying it to every adjacent pair gives DP. Auxiliary laws are measurable Markov kernels, and the successful-charge budget holds almost surely under each auxiliary process.",
    "lem:gradient_privacy": r"The coefficient record \texttt{c} makes the paper's hidden universal constants explicit. The displayed theorem supplies \texttt{privacyConstants}; its definition is reproduced in the notation appendix.",
    "lem:main-privacy": r"\texttt{Parameters.PrivacyValid} gives the broader privacy-only parameter range. The target refers to the same \texttt{cutReleaseLaw} as the utility target.",
    "lem:gradient_estimation": r"Lean also includes the deterministic partition invariant $g^++g^-+r=\mathbf1$ in \texttt{Aggregate.Partition}. \texttt{Aggregate.Accurate} expands to the three displayed accuracy requirements. The supplied certificate coefficient is $16$.",
    "lem:inner_round": r"Lean makes the algorithm's surrounding bounded-input setting explicit. \texttt{Parameters.IterationValid} permits $0<\delta,\beta<1$, without the main theorem's restrictions $\delta,\beta<1/10$. The proof establishes the oracle and noise prerequisites over this broader range. For each fixed preceding history, success probability is joint over the new mass estimate and the inner loop. No nonzero-mask hypothesis is needed: on the good mass-estimation event, continuing implies positive true mass. \texttt{result.2.isSome} means that \texttt{innerLoop} returned a candidate and mask; that branch requires \texttt{Aggregate.Accepts}.",
    "lem:outer_round": r"Lean makes the algorithm's surrounding bounded-input setting explicit and uses \texttt{Parameters.IterationValid}, allowing $0<\delta,\beta<1$. The stopping-threshold calibration is proved over this broader range, not assumed. \texttt{outerStopsLaw} records whether the actual stopping test is reached within the allotted horizon, rather than merely whether the loop runs out of iterations.",
    "lem:utility": r"\texttt{boundedError} contains the two additive terms, including exponent $7$. The multiplicative constant is quantified before all inputs and parameters. Lean also records nonnegative output on the accuracy event.",
    "lem:holder_interpolation": r"The first target covers the full exponent range, including $q=\infty$. The second is the $(1,2,4)$ instance used in the witness argument. Lean uses the extended $L_p$ seminorm and makes measurability explicit.",
    "lem:pythagorean": r"The paper states this cited auxiliary result without restricting the underlying space to a finite set. Lean proves the finite-domain specialization indexed by \texttt{Fin m} that the paper's applications require; formalizing the full generality of this background result is outside the validation scope. Membership and minimality of the projection are hypotheses; the nonnegative extended KL divergence also implies the final distance-reduction inequality.",
    "lem:capped-unit-release": r"This Lean target contains the statistical guarantee and capped output support. As in the paper's proof, \texttt{cappedRunConfig} keeps $\gamma$ unchanged and multiplies the main stopping threshold by ten, ensuring $M_{\mathrm{stop}}\geq100(B+\tau_2/\gamma)$. The error is \texttt{C * mainError n p}, with fixed logarithmic exponent seven and a universal coefficient; \texttt{lemma29} chooses $C=2^{126}$. The combined theorem \texttt{CappedLSW.capped\_release\_of\_lsw} proves capped support, privacy, utility with coefficient $2^{138}$, and polynomial assigned cost in the full parameter scale under the formal LSW parameter. This does not certify operational running time.",
    "thm:cc-black-box-reduction": APPLICATION_CONVENTION + r" The source algorithm is a family of Markov kernels with success probability at least $p_0$. The constants are chosen after $\rho,\xi,\varepsilon$ and before $p_0$ and the source algorithm, matching the paper's uniform additive bound. The theorem takes the cited private baseline as an explicit external input.",
    "cor:cc-fixed-k": APPLICATION_CONVENTION + r" The error coefficient, failure coefficient, and logarithmic exponent are chosen after $\xi,\varepsilon$ and before $k$, matching the paper's additive bound independent of $k$. The theorem takes the cited private baseline and fixed-$k$ PTAS family as explicit external inputs; running-time constants may still depend on $k$.",
    "thm:private-max-k-cut": APPLICATION_CONVENTION + r" Constants precede $k$ in the quantifiers, recording independence of the additive term from $k$. The second target is the deterministic transfer inequality used by the reduction; the Max-Cut specialization also appears in Corollary~\ref{cor:maxcut-intro}.",
    "rem:maxcut-tightness": r"The Lean theorem proves the remark's lower bound $B\geq\lfloor n/8\rfloor/100$ with the same parameter ranges, including $\varepsilon=0$, $\delta=0$, and $\beta=0$. The remark's explanatory argument is retained in the paper excerpt. No external algorithmic hypothesis is needed.",
    "thm:private-constrained-cut": r"The Lean statement is conditional on a release mechanism with additive error $A$ and on a nonprivate approximation kernel. It preserves the exact approximation factors and failure bound $\beta+\tau$. Instantiating the release with Theorem~\ref{thm:main} gives the paper's $A_\eta$. The combined general theorem instantiates the approximate LSW program and includes a uniform polynomial assigned-cost bound, subject to the cost-model limitation above. The application specialization additionally calibrates the error at $\delta=\beta=n^{-10}$.",
    "lem:hc-bicriteria-recursion": r"Lean expresses the recursive algorithm's hypothesis as properties of its output tree: \texttt{BalancedHierarchy} and \texttt{RecursiveApproximation}. The approximation constant may depend on $b$, and is quantified before $b'$, $a$, and the graph.",
    "thm:private-hierarchical-clustering": r"The statistical Lean statement records the guarantee, with failure at most $C_{\rm fail}/n^2$. The combined theorem includes a polynomial realization using LSW and the weighted ARV contract. It evaluates the additive error at $\delta=\beta=n^{-10}$ and assumes $0<\varepsilon\leq1$, as in the paper. The additive coefficient may depend on $\eta$; the balance and ratio constants are universal. The second target is the deterministic hierarchy-transfer inequality used in the analysis.",
    "lem:ekkl-discrepancy": r"Simple graphs are encoded by binary edge weights. The maximum-over-disjoint-sets conclusion is expressed by the existence of disjoint finite sets attaining the required lower bound.",
    "thm:lower_bound": r"\texttt{lowerScale} explicitly treats $\gamma=0$ by using $n^{3/2}/\varepsilon$ for the minimum. The universal lower-bound constant is quantified before all parameters; the displayed proof chooses $c=2^{-30}$.",
}

# Definitions that expose the notation hidden inside the proposition targets.
# The algorithm laws are included so that, for example, Option.isSome can be
# compared with the actual acceptance condition rather than just a prose gloss.
CONTEXT = [
    ("Combined application implementation guarantees", "ImplementedApplications", [
        "RealizedWithin", "ImplementedCCGuarantee", "ImplementedMaxKGuarantee"]),
    ("Graph notation and probability", "Definitions", [
        "Edge", "Weights", "Mat", "Nonnegative", "Bounded", "IsMask", "l1", "mass",
        "pairing", "hadamard", "Adjacent", "cutQuery", "cut", "between", "AllCuts",
        "prob", "HighProbability", "DP", "EdgeDP", "TVClose", "GraphValued"]),
    ("Parameters and error expressions", "Definitions", [
        "Parameters", "Parameters.Valid", "Parameters.PrivacyValid", "logFactor", "mainError", "boundedError", "lowerScale",
        "innerHorizon", "outerHorizon", "stepSize", "stoppingThreshold"]),
    ("Parameter range for standalone iteration bounds", "Utility", ["Parameters.IterationValid"]),
    ("SDP geometry and covariance distance", "Definitions", [
        "feasible", "fractionalQuery", "edgeVector", "objectiveMatrix", "matrixPairing",
        "objective", "IsOptimizer", "optimum", "optimizer", "frobenius",
        "relativeDifference", "covarianceDistance"]),
    ("Matrix optimizer predicate", "Statements", ["IsMatrixOptimizer"]),
    ("Gaussian laws and witnesses", "Definitions", [
        "standardGaussian", "gaussian", "gaussianBatch", "gaussianLogDensity",
        "batchLogRatio", "rawWitness", "clippedWitness", "ChiGood"]),
    ("Preprocessing and aggregate guarantees", "Definitions", [
        "laplaceDensity", "laplace", "clipWeights", "excess", "clipThreshold", "noiseShift",
        "noisyExcess", "preprocessLaw", "Aggregate", "Aggregate.Partition",
        "Aggregate.Accurate", "Aggregate.Accepts", "mwUpdate", "initialEstimate", "residualUpdate"]),
    ("Privacy-composition notation", "Privacy", [
        "Indistinguishable", "laplaceMechanism", "Sequential", "sequentialLaw", "advancedEpsilon",
        "CommonPrefix", "successCharge"]),
    ("Algorithm parameter records", "Algorithms", [
        "Constants", "Constants.Positive", "OracleConfig", "oracleConfig", "RunConfig", "runConfig", "clipNoisyMass"]),
    ("Concrete privacy constants", "PublicOracleCalibration", ["privacyConstants"]),
    ("Concrete oracle-utility constants", "UtilityCalibration", ["utilityConstants"]),
    ("Concrete outer-loop constants", "OuterUtilityCalibration", ["outerUtilityConstants"]),
    ("Algorithm laws referred to by the targets", "Algorithms", [
        "activeMaximum", "normalizeWitness", "findTrials", "findWitness", "plusDiscrepancy",
        "minusDiscrepancy", "aggregateLoop", "aggregateLaw", "innerLoop", "outerLoop", "cutReleaseLaw"]),
    ("Inner success and outer stopping laws", "Utility", ["innerRoundLaw", "outerStopsLaw"]),
    ("Computational-model interface", "Statements", ["ComputationalModel", "runtimeScale"]),
    ("Costed laws and real-model block charges", "CostedProgram", ["CostedLaw", "vectorBlockCost", "gaussianBatchCost"]),
    ("Reported completion times and timeout laws", "TimedAlgorithm", ["timeoutResult", "TimedAlgorithm", "expectedCost"]),
    ("Abstract LSW specification: problem, oracle, and guarantee", "LSWStatement", [
        "Space", "Problem", "Reply", "CorrectReply", "Oracle", "Accurate", "scale", "Statement", "DPCut.LSWStatement"]),
    ("Linear-algebra interface implemented internally", "SDPLinearOracle", ["LinearAlgebraPrimitives", "linearAlgebraPrimitiveCost"]),
    ("Value/counter record (not an instruction language)", "Arithmetic", ["Arithmetic"]),
    ("Constructed linear-algebra implementation certificate", "VerifiedLinearAlgebra", ["LinearAlgebraImplementation", "verifiedLinearAlgebra"]),
    ("Solver family constructed from LSW", "LSWSolverFamily", ["CuttingPlaneFamily", "cuttingPlaneFamily"]),
    ("Public objective bound", "SDPRuntimeData", ["publicObjectiveBound"]),
    ("Approximation budgets", "ApproximationTransfer", ["precisionParameters", "implementationTV"]),
    ("Public optimizer precision", "ApproxSDPPrecision", ["approximationBudget", "approximationRadius"]),
    ("Nonnegative-output post-processing", "ApproxSDPRelease", ["positiveWeights"]),
    ("LSW release program and its cost model", "Theorem1LSW", [
        "Program", "Program.run", "model", "realArithmeticLSWImplementationModel", "realArithmeticLSWModel"]),
    ("Exact-SDP oracle contract", "CostedProgram", ["ExactSDPOracleCost"]),
    ("Finite KL and capped support", "Definitions", ["discreteMeasure"]),
    ("Finite KL and capped support (continued)", "Applications", ["CappedOn", "IsDistribution", "finiteKL"]),
    ("Partitions and application objectives", "Applications", [
        "Partition", "partitionQuery", "partitionCut", "clusterCount", "ccCost", "ccOptimum",
        "ccOptimumK", "maxKOptimum", "constrainedOptimum"]),
    ("Statistical application guarantees", "Applications", ["PrivateCCGuarantee", "PrivateMaxKGuarantee"]),
    ("External correlation-clustering algorithm contracts", "ExternalApplicationContracts", [
        "PolynomialGraphAlgorithm", "PrivateCCBaselineContract", "CCApproximationContract", "FixedKCCContract"]),
    ("Private baseline family for correlation clustering", "CCApplication", ["CCBaselineFamily"]),
    ("Hierarchical-clustering predicates", "Applications", [
        "Hierarchy", "IsSplit", "IsHierarchy", "BalancedHierarchy", "lcaSize", "hcCost", "hcOptimum",
        "inducedExpansion", "BalancedWithin", "RecursiveApproximation"]),
    ("Unweighted graphs and degrees", "Statements", ["IsUnweighted", "vertexDegree"]),
]

# Most source files use DPCut directly. These excerpts use nested namespaces
# (or an explicitly qualified declaration at the root); keep that context visible.
DECLARATION_NAMESPACES = {
    ("CappedLSWRuntime", "capped_release_of_lsw"): "DPCut.CappedLSW",
    **{("ImplementedApplications", name): "DPCut.LSWApplications" for name in
       ("private_correlation_clustering", "private_max_cut", "theorem30", "corollary31",
        "theorem32", "constrained_cut_general", "theorem34", "theorem36")},
    **{("LSWStatement", name): "DPCut.LSW" for name in
       ("Space", "Problem", "Reply", "CorrectReply", "Oracle", "Accurate", "scale", "Statement")},
    ("LSWStatement", "DPCut.LSWStatement"): "_root_",
    ("TimedAlgorithm", "expectedCost"): "DPCut.TimedAlgorithm",
    **{("Theorem1LSW", name): "DPCut.LSWRelease" for name in ("Program", "Program.run", "model")},
}


def blank(text):
    return "".join("\n" if c == "\n" else " " for c in text)


def active_tex(raw):
    """Discard inactive text while retaining character offsets and line numbers."""
    text = re.sub(r"(?<!\\)%[^\n]*", lambda m: blank(m[0]), raw)
    for pattern in (r"\\begin\{comment\}.*?\\end\{comment\}", r"\\iffalse\b.*?\\fi\b"):
        text = re.sub(pattern, lambda m: blank(m[0]), text, flags=re.S)
    while match := re.search(r"\\junk\s*\{", text):
        pos, depth = match.end(), 1
        while depth:
            if pos >= len(text):
                raise ValueError("Unbalanced junk argument")
            if text[pos] in "{}" and text[pos - 1] != "\\":
                depth += 1 if text[pos] == "{" else -1
            pos += 1
        text = text[:match.start()] + blank(text[match.start():pos]) + text[pos:]
    return text


def paper_records(raw):
    active = active_tex(raw)
    envs = "theorem|lemma|proposition|corollary|definition|remark|restatable|claim|fact|observation|condition|example"
    records = []
    for number, match in enumerate(re.finditer(r"\\begin\{(" + envs + r")\}(.*?)\\end\{\1\}", active, re.S), 1):
        kind = match[1]
        if kind == "restatable":
            kind = re.search(r"\\begin\{restatable\}(?:\[[^\n]*?\])?\{([^}]+)\}", match[0])[1]
        records.append({
            "kind": kind, "number": number,
            "labels": re.findall(r"\\label\{([^}]+)\}", match[0]),
            "line": raw.count("\n", 0, match.start()) + 1,
            "end_line": raw.count("\n", 0, match.end()) + 1,
            "text": "\n".join(line.rstrip() for line in match[0].splitlines() if line.strip()),
        })
    return records, active


LEAN_FILES = {}


def declaration(module, name):
    path = ROOT / "DPCut" / f"{module}.lean"
    source = LEAN_FILES.setdefault(path, path.read_text())
    match = re.search(r"^(?:(?:noncomputable|private|protected) )*(?:def|abbrev|structure|inductive|theorem|lemma) "
                      + re.escape(name) + r"(?=[\s:{(])[^\n]*(?:\n[ \t]+[^\n]*)*", source, re.M)
    if not match:
        raise ValueError(f"Cannot extract {name} from {path}")
    return match[0].rstrip(), path.relative_to(ROOT).as_posix(), source.count("\n", 0, match.start()) + 1


def theorem_signature(code):
    boundary = re.search(r" :=(?:[ \t]*by\b|[ \t]*\n)", code)
    if not boundary:
        # One-line term-mode proof, e.g. `theorem theorem32 : S := private_max_k`.
        boundary = re.search(r" := \S[^\n]*$", code)
    if not boundary:
        raise ValueError("Cannot locate theorem proof boundary")
    return code[:boundary.start()].rstrip()


def escaped(text):
    mapping = {"\\": r"\textbackslash{}", "_": r"\_", "&": r"\&", "%": r"\%", "#": r"\#",
               "{": r"\{", "}": r"\}", "$": r"\$", "^": r"\textasciicircum{}", "~": r"\textasciitilde{}"}
    return "".join(mapping.get(c, c) for c in text)


# listings' literate table keeps the copied Lean text UTF-8 in this file while
# allowing compilation with ordinary pdfLaTeX and no external syntax highlighter.
UNICODE = {
    "ℕ": r"\mathbb{N}", "ℝ": r"\mathbb{R}", "∀": r"\forall", "∃": r"\exists",
    "→": r"\to", "↔": r"\leftrightarrow", "≤": r"\leq", "≥": r"\geq", "≠": r"\neq",
    "∧": r"\wedge", "∨": r"\vee", "∈": r"\in", "∉": r"\notin", "⊆": r"\subseteq",
    "∑": r"\sum", "∫": r"\int", "∂": r"\partial", "∞": r"\infty", "≪": r"\ll",
    "∪": r"\cup", "∅": r"\varnothing", "•": r"\bullet", "‖": r"\Vert", "×": r"\times", "⊕": r"\oplus",
    "⟨": r"\langle", "⟩": r"\rangle", "⌈": r"\lceil", "⌉": r"\rceil",
    "⟪": r"\langle\!\langle", "⟫": r"\rangle\!\rangle", "Θ": r"\Theta",
    "α": r"\alpha", "β": r"\beta", "γ": r"\gamma", "δ": r"\delta",
    "ε": r"\varepsilon", "η": r"\eta", "θ": r"\theta", "ι": r"\iota",
    "κ": r"\kappa", "μ": r"\mu", "ν": r"\nu", "ξ": r"\xi", "π": r"\pi",
    "ρ": r"\rho", "σ": r"\sigma", "τ": r"\tau", "Ω": r"\Omega", "Δ": r"\Delta",
    "₀": r"{}_{0}", "₁": r"{}_{1}", "₂": r"{}_{2}", "₊": r"{}_{+}",
    "⁻": r"{}^{-}", "¹": r"{}^{1}", "ᵐ": r"{}^{m}", "χ": r"\chi",
    "ᵥ": r"{}_{v}", "⬝": r"\cdot",
}

PREAMBLE = r"""% Generated by make_lemma_comparison.py; edit the sources, then regenerate.
% Compile from formalization/ with: pdflatex LemmaComparison.tex (twice).
\documentclass[a4paper,10pt]{article}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage[margin=23mm]{geometry}
\usepackage{amsmath,amssymb,amsthm}
\usepackage{thm-restate}
\usepackage{xcolor,listings,textcomp}
\usepackage{xparse}
\usepackage[colorlinks=true,linkcolor=blue,urlcolor=blue]{hyperref}
\setcounter{secnumdepth}{0}
\setcounter{tocdepth}{1}
\setlength{\parindent}{0pt}
\setlength{\parskip}{5pt}
\setlength{\emergencystretch}{3em}
\allowdisplaybreaks
\newtheorem{theorem}{Theorem}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem{corollary}[theorem]{Corollary}
\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
\theoremstyle{remark}
\newtheorem{remark}[theorem]{Remark}
\newcommand{\R}{\mathbb{R}}
\newcommand{\E}{\mathbb{E}}
\newcommand{\eps}{\varepsilon}
\newcommand{\del}{\delta}
\newcommand{\one}{\mathbf{1}}
\newcommand{\ind}{\mathbb{1}}
\newcommand{\Prb}{\mathbf{Pr}}
\newcommand{\cM}{\mathcal{M}}
\newcommand{\pdf}{\mathrm{pdf}}
\newcommand{\KL}{D_{\mathrm{KL}}}
\newcommand{\Lap}{\operatorname{Lap}}
\newcommand{\bottom}{\bot}
\newcommand{\norm}[1]{\left\Vert#1\right\Vert}
\newcommand{\ip}[2]{\left\langle#1,#2\right\rangle}
\newcommand{\odotc}{\mathbin{\odot}}
\DeclareMathOperator*{\argmin}{arg\,min}
\DeclareMathOperator*{\argmax}{arg\,max}
\renewcommand{\epsilon}{\varepsilon}
\renewcommand{\emptyset}{\varnothing}
\newcommand{\SourceId}[1]{\texttt{\detokenize{#1}}}
% Paper references retain paper numbering where known. Equation/section
% references and citations use stable source keys, avoiding external .aux/.bib files.
\newcommand{\PaperRef}[1]{\ifcsname PaperNumber@#1\endcsname\csname PaperNumber@#1\endcsname\else\SourceId{#1}\fi}
\newcommand{\PaperCref}[1]{\ifcsname PaperKind@#1\endcsname\csname PaperKind@#1\endcsname~\PaperRef{#1}\else\SourceId{#1}\fi}
\RenewDocumentCommand\ref{m}{\PaperRef{#1}}
\RenewDocumentCommand\eqref{m}{\textup{(\PaperRef{#1})}}
\NewDocumentCommand\Cref{m}{\PaperCref{#1}}
\NewDocumentCommand\cref{m}{\PaperCref{#1}}
\RenewDocumentCommand\cite{O{} m}{[\if\relax\detokenize{#1}\relax\else#1; \fi\SourceId{#2}]}
\lstdefinestyle{lean}{
  basicstyle=\ttfamily\footnotesize, columns=fullflexible, keepspaces=true,
  breaklines=true, breakatwhitespace=false, showstringspaces=false,
  numbers=left, numberstyle=\tiny\color{gray}, numbersep=7pt,
  xleftmargin=2em, frame=single, framerule=0.2pt, rulecolor=\color{gray!40},
  backgroundcolor=\color{gray!3}, aboveskip=7pt, belowskip=9pt,
  tabsize=2, upquote=true,
  morekeywords={def,abbrev,structure,inductive,where,Prop,Type,fun,let,if,then,else,match,with,theorem,lemma},
  keywordstyle=\color{blue!60!black},
  literate=
__LITERATE__
}
\title{Paper--Lean statement comparison}
\author{}
\date{Source snapshot: __HASH__}
\begin{document}
\maketitle
This document pairs every active theorem, corollary, lemma, proposition,
numbered definition, and remark in \SourceId{STOC2027.tex} with its Lean counterpart.
The paper statements are extracted from the manuscript source, excluding
comments and disabled material. The Lean definitions are copied from the
\SourceId{DPCut/} files, not paraphrased. Source locations accompany both versions.

Each \texttt{def ...Statement : Prop} defines a proposition; it is not itself a
proof. Where the project has a corresponding numbered theorem, its declaration
is also shown, with the proof body omitted. Absence of such a declaration here
is not a claim that no related result has been proved. This document compares
statements; it does not re-run or certify Lean proofs.

Cited and standard background lemmas are marked below and included for statement
comparison. Proving their full generality within this project is not required
to validate this paper's contributions. External hypotheses used by the
formalized proofs remain explicit. Apart from \texttt{theorem1\_machine}, whose
operation counts are derived from program execution in a real RAM model, cost
conclusions bound assigned counters and reported times. These interfaces do not
derive costs from execution steps: in particular, \texttt{TimedAlgorithm} permits
any measurable function at time zero. The formal LSW and application contracts therefore do not certify actual
polynomial running time, even in the real-arithmetic model.

Paper statement and algorithm references retain the manuscript's numbering.
Equation and section references are shown by their source labels, and citations
by their bibliography keys. Thus this file needs neither the paper's auxiliary
files nor its bibliography. Lean listings retain Unicode in the source; the
typeset glyphs are supplied by \texttt{listings}. Line numbers in listings refer
to the original Lean files.

Unless a source annotation specifies otherwise, displayed Lean declarations
are in namespace \texttt{DPCut}, using
\texttt{MeasureTheory}, \texttt{ProbabilityTheory}, and the usual
\texttt{BigOperators}/\texttt{ENNReal}/\texttt{MatrixOrder} scopes.
The LSW excerpts also use \texttt{Metric} and the \texttt{RealInnerProductSpace}
scope. Excerpts retain surrounding section variables from their source files;
in particular, \texttt{TimedAlgorithm.expectedCost} has a parameter
\texttt{A : TimedAlgorithm} $\Theta\ \alpha$.
The notation appendix expands the main predicates, parameter records, and
algorithm laws used in the targets.
\tableofcontents
"""


def main():
    raw = PAPER.read_text()
    records, active = paper_records(raw)
    selected = [r for r in records if r["kind"] in ("theorem", "corollary", "lemma", "proposition", "definition", "remark")]
    labels = {label for r in selected for label in r["labels"]}
    if labels != set(PAIRS):
        raise ValueError(f"Update PAIRS: unmapped={labels - set(PAIRS)}, missing={set(PAIRS) - labels}")
    blocks, code_samples = [], []

    def listing(module, name, signature=False):
        code, filename, line = declaration(module, name)
        if signature:
            code = theorem_signature(code)
        code_samples.append(code)
        namespace = DECLARATION_NAMESPACES.get((module, name))
        context = (rf" \textit{{Namespace:}} \SourceId{{{namespace}}}." if namespace else "")
        return (rf"\textit{{Source:}} \SourceId{{{filename}}}, line {line}." + context + "\n"
                + rf"\begin{{lstlisting}}[style=lean,firstnumber={line}]" + "\n"
                + code + "\n\\end{lstlisting}\n")

    for record in selected:
        label = record["labels"][0]
        title, module, names = PAIRS[label]
        number = record["number"]
        blocks.extend([
            r"\clearpage",
            rf"\section{{{record['kind'].capitalize()} {number}: {escaped(title)}}}",
            rf"\SourceId{{{label}}}\hfill\SourceId{{STOC2027.tex}}:{record['line']}--{record['end_line']}",
        ])
        if label in BACKGROUND_RESULTS:
            blocks.append(r"\textit{Background result; not a contribution of this paper.}")
        blocks.extend([
            r"\paragraph{Paper statement.}",
            rf"\setcounter{{theorem}}{{{number - 1}}}", record["text"],
            r"\paragraph{Lean statement.}",
        ])
        for name in names:
            blocks.append(listing(module, name))
        for extra_module, name in ADDITIONAL_STATEMENTS.get(label, []):
            blocks.append(listing(extra_module, name))
        # Numbered theorem wrappers are actual declarations, not invented aliases.
        proofs = list(PROOF_DECLARATIONS.get(label, []))
        proof_module = ROOT / "DPCut" / f"Lemma{number}.lean"
        if record["kind"] == "lemma" and proof_module.exists():
            proofs.append((f"Lemma{number}", f"lemma{number}"))
        for proof_module, proof_name in proofs:
            signature = theorem_signature(declaration(proof_module, proof_name)[0])
            references = CONCRETE_PROOF_REFERENCES.get((label, proof_module, proof_name), names)
            if not any(re.search(r"\b" + re.escape(name) + r"\b", signature) for name in references):
                raise ValueError(f"{proof_module}.{proof_name} does not refer to the mapped target")
            blocks += [r"\paragraph{Corresponding theorem declaration (proof omitted).}",
                       listing(proof_module, proof_name, signature=True)]
        for proof_module, proof_name in IMPLEMENTATION_DECLARATIONS.get(label, []):
            blocks += [r"\paragraph{Combined implementation theorem (proof omitted).}",
                       listing(proof_module, proof_name, signature=True)]
        if label in NOTES:
            blocks += [r"\paragraph{Comparison note.}", NOTES[label]]

    blocks += [r"\clearpage", r"\section{Notation appendix: definitions used by the Lean statements}"]
    for title, module, names in CONTEXT:
        blocks.append(rf"\subsection{{{escaped(title)}}}")
        for name in names:
            blocks.append(listing(module, name))

    chars = {c for sample in code_samples for c in sample if ord(c) > 127}
    if chars - UNICODE.keys():
        raise ValueError(f"Add listings glyphs for {sorted(chars - UNICODE.keys())}")
    literate = "\n".join("    {" + char + "}{{$" + UNICODE[char] + "$}}1" for char in sorted(chars))
    header = PREAMBLE.replace("__LITERATE__", literate).replace("__HASH__", hashlib.sha256(raw.encode()).hexdigest()[:16])
    refs = []
    for record in records:
        for label in record["labels"]:
            refs += [rf"\expandafter\def\csname PaperNumber@{label}\endcsname{{{record['number']}}}",
                     rf"\expandafter\def\csname PaperKind@{label}\endcsname{{{record['kind'].capitalize()}}}"]
    for number, match in enumerate(re.finditer(r"\\begin\{algorithm\}.*?\\end\{algorithm\}", active, re.S), 1):
        for label in re.findall(r"\\label\{(alg:[^}]+)\}", match[0]):
            refs += [rf"\expandafter\def\csname PaperNumber@{label}\endcsname{{{number}}}",
                     rf"\expandafter\def\csname PaperKind@{label}\endcsname{{Algorithm}}"]
    manifest = ["% Snapshot hashes (paper statements and Lean excerpts are embedded):",
                "% STOC2027.tex SHA-256 " + hashlib.sha256(raw.encode()).hexdigest()]
    for path, source in sorted(LEAN_FILES.items()):
        manifest.append(f"% {path.relative_to(ROOT)} SHA-256 {hashlib.sha256(source.encode()).hexdigest()}")
    document = "\n".join(manifest) + "\n" + header + "\n" + "\n".join(refs + blocks) + "\n\\end{document}\n"
    OUTPUT.write_text(document)
    counts = Counter(r["kind"] for r in selected)
    print(f"Wrote {OUTPUT.name}: {dict(counts)}, {len(code_samples)} Lean excerpts.")


if __name__ == "__main__":
    main()
