# probability-foundations

General probability and real-analysis results for the ~/Documents/lean workspace (Lean v4.34.1, shared Mathlib), relocated
from the Muon project's `Muon/Foundations` grab-bag (proved there; statements unchanged, namespace `ProbabilityFoundations`).

| Module | Contents |
|---|---|
| `Probability` | Efron–Stein; Lévy's upward theorem in L²; Doob's L² maximal inequality |
| `UniformIntegrability` | convergence of integrals under convergence in distribution with a uniform fourth moment (varying spaces) |
| `AnalysisExtra` | integral Grönwall; bounded-Lipschitz metric; weak convergence ⇒ BL convergence (compact metric spaces) |
| `RealAnalysis` | one-sided convolution; Chebyshev integral inequalities; unimodal sum–integral comparison; √/log/exp inequalities; half-line Beta integrals |
| `Freezing` | entrywise matrix conditional expectation `condExpMat`; freezing lemma (scalar and matrix form) |

Layering: deterministic matrix facts → `spectral-foundations`; pure Gaussian-measure facts → `gaussian-foundations`; random-matrix
results needing both → `rmt-foundations`; everything else probabilistic/analytic → here.

Compile one file: `lake env lean ProbabilityFoundations/X.lean` (never `lake build` while campaign workers run). Axiom check:
`lake env lean scripts/axcheck.lean`.
