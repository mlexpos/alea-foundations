# gaussian-foundations

Gaussian-process and Gaussian-concentration foundations for the ~/Documents/lean workspace (Lean v4.34.1,
shared Mathlib checkout), built on lean-stat-learning-theory (`../vendor/slt`, branch `v4.34.1-port`).

Targets (statements are verbatim the `Muon.External` certificates, which `Muon/External/Discharge.lean` proves):
- `GaussianFoundations.gaussianOpNorm`, `gaussianOpNormL6` — rectangular Gaussian matrix operator norm (HDP 4.4.5)
- `GaussianFoundations.gaussianQuadFormLp` — Hanson–Wright in Lᵖ form (HDP 6.2.1)
- `GaussianFoundations.gaussianPoincare` — Gaussian Poincaré on `EuclideanSpace ℝ (Fin n)` (BLM 3.20)
- `GaussianFoundations.stein_matrix` (`IBP.lean`, interface, proofs `sorry`) — Gaussian integration by parts / Stein's lemma:
  1-D (`stein_std`, `stein_gaussianReal`), product/Euclidean/coordinate-free (`stein_pi`, `stein_euclidean`, `stein_stdGaussian`),
  random-vector (`stein_isStdGaussianVector`), i.i.d. Gaussian matrix `E[Xᵢⱼ F(X)] = E[∂F/∂Xᵢⱼ(X)]`, covariance
  (`stein_multivariateGaussian`, `stein_linear_image`); hypotheses `C¹` + polynomial growth (`HasPolyGrowth`)
Relocated from `Muon.Foundations` (proved; mapping in `RELOCATION.md`):
- `Moments.lean` — 1-D Gaussian moments, Laplace/erfc, `stdGaussianPi`, `gaussian_stein` (corollary of `stein_std_real`), erfc identities
- `Combinatorics.lean` — `isserlis_wick_fin` (corollary of `isserlis_wick`), coordinate/trilinear/quartic moments, Sheppard arcsine, `poly_zero_set_null`
- `Rotation.lean` — rotation invariance, `sphereGauss`, Haar measure on O(n) (`haarO`), Wick four, radius–direction independence
- `OrthHaar.lean` — characterisation of Haar measure on O(n)
- `Sphere.lean` — sphere Gaussian facts
Matrix concentration (Lieb, Tropp master bound, matrix Azuma/Freedman) lives in the separate `matrix-concentration` package.

Compile one file: `lake env lean GaussianFoundations/X.lean` (never `lake build` while campaign workers run).
