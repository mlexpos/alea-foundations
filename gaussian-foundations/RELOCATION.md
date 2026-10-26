# Relocation map: `Muon.Foundations.*` -> `GaussianFoundations.*`

All declarations are public, statements unchanged (modulo namespace). Renamed entries are marked in the Note column.

Dropped (not relocated; use the existing GaussianFoundations declaration): `Muon.Foundations.IsPerfectMatchingInv` -> `GaussianFoundations.IsPerfectMatchingInv` (GaussianMatrix.lean, same definition, defeq), plus private Wick machinery (`fpf_*`, `gauss_moment_ite`, `isserlis_wick_aux`).


## `Muon/Foundations/Gaussian.lean` -> `GaussianFoundations/Moments.lean`

| Muon.Foundations name | GaussianFoundations name | Note |
|---|---|---|
| `stdGaussianPi` | `stdGaussianPi` |  |
| `erfc` | `erfc` |  |
| `gaussian_moment_even` | `gaussian_moment_even` |  |
| `gaussian_moment_odd` | `gaussian_moment_odd` |  |
| `gaussian_integrable_pow` | `gaussian_integrable_pow` |  |
| `gaussian_memLp_pow` | `gaussian_memLp_pow` |  |
| `gaussian_moment_two` | `gaussian_moment_two` |  |
| `gaussian_moment_four` | `gaussian_moment_four` |  |
| `gaussian_moment_six` | `gaussian_moment_six` |  |
| `gaussian_moment_eight` | `gaussian_moment_eight` |  |
| `gaussian_sq_sub_one_moment_two` | `gaussian_sq_sub_one_moment_two` |  |
| `gaussian_sq_sub_one_moment_four` | `gaussian_sq_sub_one_moment_four` |  |
| `gaussian_abs_moment` | `gaussian_abs_moment` |  |
| `gaussian_neg_half_abs_moment` | `gaussian_neg_half_abs_moment` |  |
| `gaussian_laplace` | `gaussian_laplace` |  |
| `gaussian_completed_square` | `gaussian_completed_square` |  |
| `gaussian_pdf_le` | `gaussian_pdf_le` |  |
| `gaussian_stein` | `gaussian_stein` | one-line corollary of `stein_std_real` |
| `app_de_nomomentum_ratio` | `gaussian_ratio_eq_erfc_integrand` | renamed (erfc identity) |
| `app_de_nomomentum_erfc` | `gaussian_erfc_integrand_eq` | renamed (erfc identity) |
| `stdGaussianPi_map_coord` | `stdGaussianPi_map_coord` |  |
| `stdGaussianPi_sq_norm_moment` | `stdGaussianPi_sq_norm_moment` |  |
| `stdGaussianPi_abs_mul_coord` | `stdGaussianPi_abs_mul_coord` |  |
| `stdGaussianPi_linear_map` | `stdGaussianPi_linear_map` |  |
| `stdGaussian_conditional_linear` | `stdGaussian_conditional_linear` |  |
| `stdGaussianPi_quadratic_mean` | `stdGaussianPi_quadratic_mean` |  |
| `stdGaussianPi_quadratic_variance` | `stdGaussianPi_quadratic_variance` |  |

## `Muon/Foundations/GaussianCombinatorics.lean` -> `GaussianFoundations/Combinatorics.lean`

| Muon.Foundations name | GaussianFoundations name | Note |
|---|---|---|
| `IsPerfectMatchingInv` | `IsPerfectMatchingInv` |  |
| `isserlis_wick` | `isserlis_wick_fin` | renamed; corollary of general `isserlis_wick` (GaussianMatrix) |
| `gaussian_coord_moment_two` | `gaussian_coord_moment_two` |  |
| `gaussian_coord_moment_four` | `gaussian_coord_moment_four` |  |
| `gaussian_coord_moment_six` | `gaussian_coord_moment_six` |  |
| `gaussian_coord_moment_eight` | `gaussian_coord_moment_eight` |  |
| `gaussian_trilinear_moment` | `gaussian_trilinear_moment` |  |
| `gaussian_quartic_covariance` | `gaussian_quartic_covariance` |  |
| `gaussian_weighted_square_moment` | `gaussian_weighted_square_moment` |  |
| `gaussian_weighted_linear_moment` | `gaussian_weighted_linear_moment` |  |
| `sheppard_arcsine` | `sheppard_arcsine` |  |
| `poly_zero_set_null` | `poly_zero_set_null` |  |

## `Muon/Foundations/GaussianExtra.lean` -> `GaussianFoundations/Rotation.lean`

| Muon.Foundations name | GaussianFoundations name | Note |
|---|---|---|
| `euclidNorm` | `euclidNorm` |  |
| `sphereGauss` | `sphereGauss` |  |
| `stdGaussianPi_map_toLp` | `stdGaussianPi_map_toLp` |  |
| `stdGaussianPi_map_orthogonal` | `stdGaussianPi_map_orthogonal` |  |
| `stdGaussianPi_wick_four` | `stdGaussianPi_wick_four` |  |
| `sphereGauss_isProbabilityMeasure` | `sphereGauss_isProbabilityMeasure` |  |
| `orthogonalGroup_compactSpace` | `orthogonalGroup_compactSpace` |  |
| `orthogonalGroup_compactSpace_inst` | `orthogonalGroup_compactSpace_inst` |  |
| `haarO` | `haarO` |  |
| `haarO_isProbabilityMeasure` | `haarO_isProbabilityMeasure` |  |
| `haarO_isMulLeftInvariant` | `haarO_isMulLeftInvariant` |  |
| `haarO_isMulRightInvariant` | `haarO_isMulRightInvariant` |  |
| `haarO_map_mulVec` | `haarO_map_mulVec` |  |
| `haarO_mulVec_coord_ne_zero` | `haarO_mulVec_coord_ne_zero` |  |
| `stdGaussianPi_radius_direction_indep` | `stdGaussianPi_radius_direction_indep` |  |

## `Muon/Foundations/OrthHaar.lean` -> `GaussianFoundations/OrthHaar.lean`

| Muon.Foundations name | GaussianFoundations name | Note |
|---|---|---|
| `IsOrthHaar` | `IsOrthHaar` |  |
| `orthHaar_exists` | `orthHaar_exists` |  |
| `isOrthHaar_unique` | `isOrthHaar_unique` |  |
| `haarO_isOrthHaar` | `haarO_isOrthHaar` |  |

## `Muon/Foundations/SphereGaussian.lean` -> `GaussianFoundations/Sphere.lean`

| Muon.Foundations name | GaussianFoundations name | Note |
|---|---|---|
| `orthHaar_map_mulVec_eq_sphereGauss` | `orthHaar_map_mulVec_eq_sphereGauss` |  |
| `orthHaar_mulVec_coord_ne_zero` | `orthHaar_mulVec_coord_ne_zero` |  |

## Notes

- The anonymous instance `IsProbabilityMeasure (stdGaussianPi n)` moved with `stdGaussianPi` (Moments.lean); it needs no wrapper entry.
- `Muon.Foundations.IsPerfectMatchingInv` is not relocated: use `GaussianFoundations.IsPerfectMatchingInv` (GaussianMatrix.lean); the definitions are identical.
- Private lemmas were not relocated. The private Wick machinery of Combinatorics (`fpf_cycleType`, `cycleType_fpf`, `fpf_card`, `stab_equiv`, `fpf_count`, `gauss_moment_ite`, `isserlis_wick_aux`) was dropped, replaced by the general `GaussianFoundations.isserlis_wick`.
- Definitions (`stdGaussianPi`, `erfc`, `sphereGauss`, `haarO`, `IsOrthHaar`, ...) are defs in `GaussianFoundations`; wrappers should be `abbrev`/`export` so instances and `rfl` unfoldings keep working.
