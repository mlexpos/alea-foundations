import Mathlib
import GaussianFoundations.Rotation
import GaussianFoundations.OrthHaar

/-!
# Foundations: uniform sphere and Haar images (task L-I.0b)

Statement only (`sorry`). Proof routes are in
`muon/phases-of-muon/appendix-nodes/results/L-I.0b-interface.json`.

Reused from `GaussianFoundations.Rotation` and `GaussianFoundations.Moments`, not restated:

* `euclidNorm`, `sphereGauss` (uniform law on the sphere, the law of `g / ‖g‖`);
* `haarO_map_mulVec` and `haarO_mulVec_coord_ne_zero` (the case `ν = haarO n`);
* `stdGaussianPi_radius_direction_indep` (radius–direction independence of the standard
  Gaussian vector; proved, no sorry);
* `stdGaussianPi_sq_norm_moment` (`E‖g‖^{2q} = ∏_{j<q} (n + 2j)`, i.e. the card's `d_q(n)`;
  proved).

The new statements below extend the Haar facts from the constructed measure `haarO n` to an
arbitrary left- and right-invariant probability measure `ν` (`IsOrthHaar ν`), as the ruling
requires.
-/

open MeasureTheory
open scoped Matrix

namespace GaussianFoundations

/-- For any Haar probability `ν` on `O(n)` (`IsOrthHaar ν`) and a fixed unit vector `v`, the image
of `ν` under `U ↦ U v` is the uniform law on the sphere, `sphereGauss n`. (task L-I.0b; no paper
label; snapshot cr-2026-10-23). Consumer: Appendix I, `def:app-sgd-state-law` (the Haar state
law, l. 605–618), and the Haar sign lemmas (l. 718–719, 1130) in the form `Uv =d g/‖g‖`. -/
theorem orthHaar_map_mulVec_eq_sphereGauss (n : ℕ) {ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)}
    (hν : IsOrthHaar ν) (v : Fin n → ℝ) (hv : euclidNorm n v = 1) :
    ν.map (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ v) = sphereGauss n := by
  have he : ν = haarO n := isOrthHaar_unique hν (haarO_isOrthHaar n)
  subst he
  exact haarO_map_mulVec n v hv

/-- For any Haar probability `ν` on `O(n)` (`IsOrthHaar ν`) and a fixed unit vector `v`, almost
surely no coordinate of `U v` vanishes. (task L-I.0b; no paper label; snapshot cr-2026-10-23).
Consumer: Appendix I, the Haar state law (`def:app-sgd-state-law`, l. 605–618), where the sign of
each coordinate of `U v` is used (l. 718–719, 1130). -/
theorem orthHaar_mulVec_coord_ne_zero (n : ℕ) {ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)}
    (hν : IsOrthHaar ν) (v : Fin n → ℝ) (hv : euclidNorm n v = 1) :
    ∀ᵐ U : Matrix.orthogonalGroup (Fin n) ℝ ∂ν,
      ∀ i : Fin n, ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ v) i ≠ 0 := by
  have he : ν = haarO n := isOrthHaar_unique hν (haarO_isOrthHaar n)
  subst he
  exact haarO_mulVec_coord_ne_zero n v hv

end GaussianFoundations
