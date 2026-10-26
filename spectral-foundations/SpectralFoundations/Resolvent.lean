import SpectralFoundations.Eigenvalues
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Deterministic resolvent toolkit

Resolvents of square matrices and Gram resolvents of rectangular real matrices.

## Contents
* `matResolvent A z = (A − z • 1)⁻¹` (any `z : 𝕜`), and `negResolvent A t = (A + t • 1)⁻¹` for real
  `t` (the negative-axis point `z = −t`, `t > 0`, used throughout the projects).
* Invertibility, inverse identities, Hermitian/positive-definite structure, eigenvalue and trace
  formulas (`re (trace (negResolvent A t)) = ∑ₖ (λₖ + t)⁻¹`, the identity used by `ESD.lean`).
* The general resolvent identity `A⁻¹ − B⁻¹ = A⁻¹ (B − A) B⁻¹` (any two invertible matrices), its
  resolvent and parameter forms.
* Norm bounds. **Normal** complex matrices: the sharp identity
  `‖(A − z)⁻¹‖ = 1 / infDist z (spectrum ℂ A)` off the spectrum. **Hermitian** matrices over any
  `RCLike 𝕜` (so real symmetric ones too): the same identity with `spectrum 𝕜 A`, and the
  corollaries `‖R(z)‖ ≤ 1/|Im z|` and `‖R(−t)‖ ≤ 1/t` for PSD `A`, `t > 0`.
* Lipschitz dependence on the matrix, and the rank bound
  `|tr R_A(−t) − tr R_B(−t)| ≤ rank(A − B)/t` for PSD `A`, `B`.
* Sherman–Morrison (rank-one update of an inverse, over any field), the matrix determinant lemma,
  and the PSD rank-one resolvent update.
* Gram resolvents of a real rectangular `M`: `R_s(M) = (MMᵀ + s)⁻¹`, `R̃_s(M) = (MᵀM + s)⁻¹`,
  `𝖷_s(M) = R_s(M) M`; push-through, the trace balance `card m − s tr R_s = card n − s tr R̃_s`,
  the bounds of `lem:app-de-resolvent`, the rank-two deletion
  formula of `lem:app-de-deletion`, and the Lipschitz bound of `lem:app-de-lipschitz`, both in
  operator norm and in nuclear norm.
* The nuclear norm `nuclearNorm` (sum of singular values) of a real matrix and the facts used above.

## Extraction source
`~/Documents/lean/muon/lean/Muon/DetEquiv/Resolvent.lean` (proved there): `lem_app_de_resolvent`
(l.322), `lem_app_de_deletion` (l.664), `lem_app_de_lipschitz` (l.1102), and their private helpers
`resAux_*`, `dlAux_*`, `lipAux_*`; the nuclear-norm facts are from
`~/Documents/lean/muon/lean/Muon/Foundations/Nuclear.lean` (proved there). Proof workers should port
those proofs. With `Mat m n := Matrix (Fin m) (Fin n) ℝ`:
* Muon's `Rs M s`, `Rts M s`, `Xs M s` are `gramResolvent M s`, `gramResolventT M s`,
  `mixedResolvent M s` (by `rfl`; see `gramResolvent_def`);
* Muon's `opNorm K` is `‖K‖` under `Matrix.Norms.L2Operator` (bridge lemma `Muon.opNorm_eq_norm`,
  proved by `rw [Matrix.l2_opNorm_def]; rfl`);
* Muon's `nuc K` is `nuclearNorm K` (same defining expression);
* Muon's `delU/delV/delC/delLambda/alpha1/alpha2/alpha3` are `rankOneU/…/rankOneAlpha3`, Muon's
  `outer u v` is `vecMulVec u v`, and Muon's `sqNorm x` is `∑ i, x i ^ 2`.
So `lem_app_de_resolvent`, `lem_app_de_deletion` and `lem_app_de_lipschitz` are the instances
`gramResolvent_facts`, `gramResolvent_rankOne_update`, `nuclearNorm_gramResolvent_sub_le` at
`m := Fin m`, `n := Fin n`, after rewriting with `opNorm_eq_norm`.

## References
* R. Bhatia, *Matrix Analysis*, GTM 169 (resolvent and perturbation bounds).
* Z. Bai, J. W. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*, 2nd ed.,
  Springer 2010, Appendix A.1 (rank inequalities, Sherman–Morrison) and Lemma 2.6.

## Interface choices
* All norms are l2 operator norms under `open scoped Matrix.Norms.L2Operator`; the complex normal
  case also uses the scoped `CStarAlgebra (Matrix n n ℂ)` instance of that scope.
* `⁻¹` is Mathlib's `Matrix.inv` (`nonsing_inv`), which is `0` on singular matrices. Every identity
  that needs a genuine inverse carries the invertibility hypothesis (`IsUnit _.det`, or PSD with
  `t > 0`), and every norm identity carries `z ∉ spectrum`.
* `negResolvent` uses the real scalar action `t • (1 : Matrix n n 𝕜)`, so at `𝕜 = ℝ` it is literally
  Muon's `(A + s • 1)⁻¹`. `matResolvent A (-(t : 𝕜)) = negResolvent A t` is
  `matResolvent_neg_ofReal`.
* The square-matrix resolvent is named `matResolvent`, not `resolvent`: Mathlib's root
  `resolvent a z = Ring.inverse (↑ₐ z − a)` (opposite sign) would make `resolvent A z` ambiguous in
  any file that opens `SpectralFoundations`.
* The Gram section is stated over `ℝ` with `Mᵀ`, the case used by the projects; generic `RCLike`
  versions would need `Mᴴ`, which is not syntactically `Mᵀ` at `𝕜 = ℝ`.
* Index types are arbitrary `Fintype`s with `DecidableEq`; `Fin m`, `Fin n` are instances.
-/

open Matrix Set Filter Topology
open scoped ComplexOrder

noncomputable section

namespace SpectralFoundations

/-! ## General inverse identities -/

section General

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- **Resolvent identity** (general form): for invertible `A`, `B`, `A⁻¹ − B⁻¹ = A⁻¹ (B − A) B⁻¹`.
Proof route: expand `A⁻¹ (B − A) B⁻¹ = A⁻¹ B B⁻¹ − A⁻¹ A B⁻¹` (`Matrix.mul_sub`,
`Matrix.sub_mul`) and cancel with `mul_nonsing_inv`, `nonsing_inv_mul` (Muon `lipAux_inv_diff`). -/
theorem inv_sub_inv {A B : Matrix n n K} (hA : IsUnit A.det) (hB : IsUnit B.det) :
    A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc A⁻¹ B, Matrix.mul_nonsing_inv _ hB,
    Matrix.mul_one, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]

/-- **Sherman–Morrison**: for invertible `A` and `1 + vᵀA⁻¹u ≠ 0`,
`(A + u vᵀ)⁻¹ = A⁻¹ − (1 + vᵀA⁻¹u)⁻¹ (A⁻¹u)(vᵀA⁻¹)`.
Proof route: `Matrix.add_mul_mul_inv_eq_sub` (Woodbury) with `U = replicateCol Unit u`,
`C = 1`, `V = replicateRow Unit v`, a `1 × 1` inner matrix; or verify
`(A + u vᵀ) * RHS = 1` directly and use `Matrix.inv_eq_right_inv`. -/
theorem inv_add_vecMulVec {A : Matrix n n K} (hA : IsUnit A.det) (u v : n → K)
    (huv : 1 + v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ 0) :
    (A + vecMulVec u v)⁻¹ =
      A⁻¹ - (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹ • vecMulVec (A⁻¹ *ᵥ u) (v ᵥ* A⁻¹) := by
  set w := A⁻¹ *ᵥ u with hw
  set c := (1 + v ⬝ᵥ w)⁻¹ with hc
  have hAw : A *ᵥ w = u := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA, Matrix.one_mulVec]
  have hcc : c * (1 + v ⬝ᵥ w) = 1 := inv_mul_cancel₀ huv
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_nonsing_inv _ hA,
    Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_vecMulVec, hAw, Matrix.vecMulVec_mul,
    Matrix.vecMulVec_mul_vecMulVec]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Pi.smul_apply, smul_eq_mul]
  linear_combination (-(u i * (v ᵥ* A⁻¹) j)) * hcc

/-- **Matrix determinant lemma**: `det (A + u vᵀ) = det A · (1 + vᵀA⁻¹u)`.
Proof route: `Matrix.det_add_replicateCol_mul_replicateRow` with `ι = Unit`, then compute the
`1 × 1` determinant (`det_unique`) and `replicateCol_mul_replicateRow`-type simp lemmas. -/
theorem det_add_vecMulVec {A : Matrix n n K} (hA : IsUnit A.det) (u v : n → K) :
    (A + vecMulVec u v).det = A.det * (1 + v ⬝ᵥ (A⁻¹ *ᵥ u)) := by
  rw [Matrix.vecMulVec_eq Unit, Matrix.det_add_replicateCol_mul_replicateRow hA]
  congr 1
  rw [Matrix.det_unique]
  simp [Matrix.mul_apply, dotProduct, Matrix.mulVec,
    Matrix.replicateRow, Matrix.replicateCol, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

end General

/-! ## Resolvents of square matrices -/

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The resolvent `R_A(z) = (A − z • 1)⁻¹` (Mathlib's `nonsing_inv`, junk `0` on the spectrum).
Not Mathlib's `_root_.resolvent`, which is `(z − A)⁻¹` via `Ring.inverse`. -/
def matResolvent (A : Matrix n n 𝕜) (z : 𝕜) : Matrix n n 𝕜 :=
  (A - z • (1 : Matrix n n 𝕜))⁻¹

/-- The resolvent at the negative real point `−t`: `R_A(−t) = (A + t • 1)⁻¹`, real scalar `t`. -/
def negResolvent (A : Matrix n n 𝕜) (t : ℝ) : Matrix n n 𝕜 :=
  (A + t • (1 : Matrix n n 𝕜))⁻¹

/-- `R_A(−t)` is the resolvent at `z = −t`.
Proof route: `sub_neg_eq_add`, `neg_smul`, and `RCLike.real_smul_eq_coe_smul` (or `algebraMap_smul`)
to identify `(t : 𝕜) • 1` with `t • 1`. -/
theorem matResolvent_neg_ofReal (A : Matrix n n 𝕜) (t : ℝ) :
    matResolvent A (-(t : 𝕜)) = negResolvent A t := by
  unfold matResolvent negResolvent
  rw [neg_smul, sub_neg_eq_add, RCLike.real_smul_eq_coe_smul (K := 𝕜)]

/-! ### Structure for PSD `A` and `t > 0` -/

/-- `A + t • 1` is positive definite for PSD `A` and `t > 0`.
Proof route: `PosDef.posSemidef_add` / `PosSemidef.add_posDef` with `PosDef.smul` of `posDef_one`
(the real scalar `t` acts through `RCLike.ofReal`). -/
theorem posDef_add_smul_one {A : Matrix n n 𝕜} (hA : A.PosSemidef) {t : ℝ} (ht : 0 < t) :
    (A + t • (1 : Matrix n n 𝕜)).PosDef := by
  rw [add_comm]
  exact ((Matrix.PosDef.one (n := n) (R := 𝕜)).smul ht).add_posSemidef hA

/-- `A + t • 1` is invertible for PSD `A` and `t > 0`.
Proof route: `(posDef_add_smul_one hA ht).isUnit` and `Matrix.isUnit_iff_isUnit_det`. -/
theorem isUnit_det_add_smul_one {A : Matrix n n 𝕜} (hA : A.PosSemidef) {t : ℝ} (ht : 0 < t) :
    IsUnit (A + t • (1 : Matrix n n 𝕜)).det := by
  rw [← Matrix.isUnit_iff_isUnit_det]
  exact (posDef_add_smul_one hA ht).isUnit

/-- Right inverse identity.
Proof route: `Matrix.mul_nonsing_inv _ (isUnit_det_add_smul_one hA ht)`. -/
theorem add_smul_one_mul_negResolvent {A : Matrix n n 𝕜} (hA : A.PosSemidef) {t : ℝ}
    (ht : 0 < t) : (A + t • (1 : Matrix n n 𝕜)) * negResolvent A t = 1 := by
  exact Matrix.mul_nonsing_inv _ (isUnit_det_add_smul_one hA ht)

/-- Left inverse identity.
Proof route: `Matrix.nonsing_inv_mul _ (isUnit_det_add_smul_one hA ht)`. -/
theorem negResolvent_mul_add_smul_one {A : Matrix n n 𝕜} (hA : A.PosSemidef) {t : ℝ}
    (ht : 0 < t) : negResolvent A t * (A + t • (1 : Matrix n n 𝕜)) = 1 := by
  exact Matrix.nonsing_inv_mul _ (isUnit_det_add_smul_one hA ht)

/-- `R_A(−t) A = 1 − t R_A(−t)`.
Proof route: `negResolvent_mul_add_smul_one`, `Matrix.mul_add`, `Matrix.mul_smul`, rearrange. -/
theorem negResolvent_mul_self {A : Matrix n n 𝕜} (hA : A.PosSemidef) {t : ℝ} (ht : 0 < t) :
    negResolvent A t * A = 1 - t • negResolvent A t := by
  have h := negResolvent_mul_add_smul_one hA ht
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one] at h
  rw [← h]; abel

/-- `A R_A(−t) = 1 − t R_A(−t)`.
Proof route: `add_smul_one_mul_negResolvent`, `Matrix.add_mul`, `Matrix.smul_mul`, rearrange. -/
theorem self_mul_negResolvent {A : Matrix n n 𝕜} (hA : A.PosSemidef) {t : ℝ} (ht : 0 < t) :
    A * negResolvent A t = 1 - t • negResolvent A t := by
  have h := add_smul_one_mul_negResolvent hA ht
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul] at h
  rw [← h]; abel

/-- The resolvent of a Hermitian matrix at a real point is Hermitian (also when singular, since the
junk inverse is `0`).
Proof route: `(A + t • 1)` is Hermitian (`IsHermitian.add`, `isHermitian_one.smul`), then
`IsHermitian.inv` (or `conjTranspose_nonsing_inv`). -/
theorem isHermitian_negResolvent {A : Matrix n n 𝕜} (hA : A.IsHermitian) (t : ℝ) :
    (negResolvent A t).IsHermitian := by
  have h : (A + t • (1 : Matrix n n 𝕜)).IsHermitian :=
    hA.add ((Matrix.isHermitian_one).smul (IsSelfAdjoint.all _))
  exact h.inv

/-- The resolvent of a PSD matrix at `−t`, `t > 0`, is positive definite.
Proof route: `PosDef.inv` applied to `posDef_add_smul_one hA ht`. -/
theorem posDef_negResolvent {A : Matrix n n 𝕜} (hA : A.PosSemidef) {t : ℝ} (ht : 0 < t) :
    (negResolvent A t).PosDef := by
  exact (posDef_add_smul_one hA ht).inv

/-- The resolvent is a function of `A` in the functional calculus: `R_A(−t) = (x ↦ (x + t)⁻¹)(A)`.
Proof route: `cfc_eq hA`, `IsHermitian.cfc` and the spectral theorem: `A + t = U diag(λ + t) U*`,
whose inverse is `U diag((λ + t)⁻¹) U*` because no `λᵢ + t` vanishes (`inv_eq_left_inv`). -/
theorem negResolvent_eq_cfc {A : Matrix n n 𝕜} (hA : A.IsHermitian) {t : ℝ}
    (ht : ∀ k, sortedEig A k + t ≠ 0) :
    negResolvent A t = cfc (fun x : ℝ => (x + t)⁻¹) A := by
  have hspec : ∀ x ∈ spectrum ℝ A, x + t ≠ 0 := by
    intro x hx
    rw [hA.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    have := ht ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)
    rwa [sortedEig_eq hA] at this
  have hfin : (spectrum ℝ A).Finite := by
    rw [hA.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _
  have hc1 : ContinuousOn (fun x : ℝ => x + t) (spectrum ℝ A) := by fun_prop
  have hc2 : ContinuousOn (fun x : ℝ => (x + t)⁻¹) (spectrum ℝ A) := by
    exact ContinuousOn.inv₀ (by fun_prop) hspec
  have e1 : A + t • (1 : Matrix n n 𝕜) = cfc (fun x : ℝ => x + t) A := by
    have hid : ContinuousOn (fun x : ℝ => x) (spectrum ℝ A) := continuousOn_id
    have hco : ContinuousOn (fun _ : ℝ => t) (spectrum ℝ A) := continuousOn_const
    rw [cfc_add A (fun x : ℝ => x) (fun _ : ℝ => t) hid hco, cfc_id' (R := ℝ) (a := A), cfc_const t A,
      Algebra.algebraMap_eq_smul_one]
  have h1 : (A + t • (1 : Matrix n n 𝕜)) * cfc (fun x : ℝ => (x + t)⁻¹) A = 1 := by
    rw [e1, ← cfc_mul (fun x : ℝ => x + t) (fun x : ℝ => (x + t)⁻¹) A hc1 hc2]
    rw [cfc_congr (g := fun _ => (1:ℝ)) (fun x hx => mul_inv_cancel₀ (hspec x hx))]
    exact cfc_const_one ℝ A
  exact (Matrix.inv_eq_right_inv h1)

/-- Trace of the resolvent: `re (tr R_A(−t)) = ∑ₖ (λₖ(A) + t)⁻¹` when no `λₖ + t` vanishes.
Proof route: `negResolvent_eq_cfc`, `IsHermitian.cfc`, `trace` of a unitary conjugate of a
diagonal (`trace_mul_comm`), and `sum_sortedEig_comp`. -/
theorem re_trace_negResolvent {A : Matrix n n 𝕜} (hA : A.IsHermitian) {t : ℝ}
    (ht : ∀ k, sortedEig A k + t ≠ 0) :
    RCLike.re (trace (negResolvent A t)) = ∑ k, (sortedEig A k + t)⁻¹ := by
  rw [negResolvent_eq_cfc hA ht, hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  have : star (hA.eigenvectorUnitary : Matrix n n 𝕜) * (hA.eigenvectorUnitary : Matrix n n 𝕜) = 1 :=
    Unitary.coe_star_mul_self _
  rw [this, Matrix.one_mul, Matrix.trace_diagonal, map_sum, sum_sortedEig_comp hA (fun x => (x + t)⁻¹)]
  simp only [Function.comp_apply, RCLike.ofReal_re]

/-- PSD case of `re_trace_negResolvent`.
Proof route: `sortedEig_nonneg hA` gives `sortedEig A k + t > 0`. -/
theorem re_trace_negResolvent_of_posSemidef {A : Matrix n n 𝕜} (hA : A.PosSemidef) {t : ℝ}
    (ht : 0 < t) :
    RCLike.re (trace (negResolvent A t)) = ∑ k, (sortedEig A k + t)⁻¹ := by
  refine re_trace_negResolvent hA.isHermitian fun k => ?_
  have := sortedEig_nonneg hA k
  linarith

/-! ### Resolvent identities -/

/-- Resolvent identity in the matrix, at a common point `z`, for any two matrices whose shifted
inverses exist: `R_A(z) − R_B(z) = R_A(z) (B − A) R_B(z)`.
Proof route: `inv_sub_inv` with `(B − z) − (A − z) = B − A`. -/
theorem matResolvent_sub_matResolvent {A B : Matrix n n 𝕜} {z : 𝕜}
    (hA : IsUnit (A - z • (1 : Matrix n n 𝕜)).det) (hB : IsUnit (B - z • (1 : Matrix n n 𝕜)).det) :
    matResolvent A z - matResolvent B z = matResolvent A z * (B - A) * matResolvent B z := by
  unfold matResolvent
  rw [inv_sub_inv hA hB]
  congr 2
  abel

/-- Resolvent identity in the point: `R_A(z) − R_A(w) = (z − w) R_A(z) R_A(w)`.
Proof route: `inv_sub_inv` with `(A − w) − (A − z) = (z − w) • 1`, then `Matrix.mul_smul`,
`Matrix.smul_mul`, `Matrix.mul_one`. -/
theorem matResolvent_sub_matResolvent_point {A : Matrix n n 𝕜} {z w : 𝕜}
    (hz : IsUnit (A - z • (1 : Matrix n n 𝕜)).det) (hw : IsUnit (A - w • (1 : Matrix n n 𝕜)).det) :
    matResolvent A z - matResolvent A w = (z - w) • (matResolvent A z * matResolvent A w) := by
  unfold matResolvent
  rw [inv_sub_inv hz hw]
  have : (A - w • (1 : Matrix n n 𝕜)) - (A - z • (1 : Matrix n n 𝕜)) = (z - w) • (1 : Matrix n n 𝕜) := by
    rw [sub_smul]; abel
  rw [this, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

/-- Negative-axis resolvent identity in the matrix, PSD case.
Proof route: `inv_sub_inv` with `isUnit_det_add_smul_one` for both, and
`(B + t) − (A + t) = B − A`. -/
theorem negResolvent_sub_negResolvent {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) {t : ℝ} (ht : 0 < t) :
    negResolvent A t - negResolvent B t = negResolvent A t * (B - A) * negResolvent B t := by
  unfold negResolvent
  rw [inv_sub_inv (isUnit_det_add_smul_one hA ht) (isUnit_det_add_smul_one hB ht)]
  congr 2
  abel

/-- Negative-axis resolvent identity in the point: `R(−s) − R(−s') = (s' − s) R(−s) R(−s')`.
Proof route: `inv_sub_inv`, `(A + s') − (A + s) = (s' − s) • 1` (Muon `resAux_lip`, first step). -/
theorem negResolvent_sub_negResolvent_param {A : Matrix n n 𝕜} (hA : A.PosSemidef) {s s' : ℝ}
    (hs : 0 < s) (hs' : 0 < s') :
    negResolvent A s - negResolvent A s' = (s' - s) • (negResolvent A s * negResolvent A s') := by
  unfold negResolvent
  rw [inv_sub_inv (isUnit_det_add_smul_one hA hs) (isUnit_det_add_smul_one hA hs')]
  have : (A + s' • (1 : Matrix n n 𝕜)) - (A + s • (1 : Matrix n n 𝕜)) = (s' - s) • (1 : Matrix n n 𝕜) := by
    rw [sub_smul]; abel
  rw [this, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

/-! ### Private helpers for the Hermitian resolvent norm -/

private lemma matResolvent_eq_conj {A : Matrix n n 𝕜} (hA : A.IsHermitian) {z : 𝕜}
    (hz : z ∉ spectrum 𝕜 A) :
    matResolvent A z =
      (hA.eigenvectorUnitary : Matrix n n 𝕜) *
        diagonal (fun i => ((hA.eigenvalues i : 𝕜) - z)⁻¹) *
        star (hA.eigenvectorUnitary : Matrix n n 𝕜) := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hU
  have h1 : star U * U = 1 := Unitary.coe_star_mul_self _
  have h2 : U * star U = 1 := Unitary.coe_mul_star_self _
  have hne : ∀ i, (hA.eigenvalues i : 𝕜) - z ≠ 0 := by
    intro i h
    apply hz
    rw [hA.spectrum_eq_image_range]
    exact ⟨hA.eigenvalues i, Set.mem_range_self i, by
      rw [sub_eq_zero] at h; exact h⟩
  have hA' : A = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
  have hsub : A - z • (1 : Matrix n n 𝕜) =
      U * diagonal (fun i => (hA.eigenvalues i : 𝕜) - z) * star U := by
    have : (diagonal (fun i => (hA.eigenvalues i : 𝕜) - z) : Matrix n n 𝕜) =
        diagonal (RCLike.ofReal ∘ hA.eigenvalues) - z • 1 := by
      ext i j
      by_cases h : i = j
      · subst h; simp [diagonal_apply_eq]
      · simp [diagonal_apply_ne _ h, h]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      h2, ← hA']
  unfold matResolvent
  refine Matrix.inv_eq_right_inv ?_
  rw [hsub]
  calc U * diagonal (fun i => (hA.eigenvalues i : 𝕜) - z) * star U *
        (U * diagonal (fun i => ((hA.eigenvalues i : 𝕜) - z)⁻¹) * star U)
      = U * (diagonal (fun i => (hA.eigenvalues i : 𝕜) - z) *
          diagonal (fun i => ((hA.eigenvalues i : 𝕜) - z)⁻¹)) * star U := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (star U) U, h1, Matrix.one_mul]
    _ = 1 := by
        rw [Matrix.diagonal_mul_diagonal]
        have : (fun i => ((hA.eigenvalues i : 𝕜) - z) * ((hA.eigenvalues i : 𝕜) - z)⁻¹) = fun _ => 1 :=
          funext fun i => mul_inv_cancel₀ (hne i)
        rw [this]
        simp [h2]

/-! ### Norm bounds -/

section Norms

open scoped Matrix.Norms.L2Operator

private lemma norm_unitary_conj [Nonempty n] (U E : Matrix n n 𝕜) (h1 : star U * U = 1) : ‖U * E * star U‖ = ‖E‖ := by
  have hU : ‖U‖ = 1 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self U
    rw [Matrix.star_eq_conjTranspose] at h1
    rw [h1, norm_one] at h
    have : ‖U‖ * ‖U‖ = 1 := h.symm
    nlinarith [norm_nonneg U]
  have hV : ‖star U‖ = 1 := by
    rw [Matrix.star_eq_conjTranspose, Matrix.l2_opNorm_conjTranspose]; exact hU
  apply le_antisymm
  · calc ‖U * E * star U‖ ≤ ‖U * E‖ * ‖star U‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ ‖U‖ * ‖E‖ * ‖star U‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
      _ = ‖E‖ := by rw [hU, hV]; ring
  · have : E = star U * (U * E * star U) * U := by
      calc E = (star U * U) * E * (star U * U) := by rw [h1]; simp
        _ = _ := by simp only [Matrix.mul_assoc]
    calc ‖E‖ = ‖star U * (U * E * star U) * U‖ := by rw [← this]
      _ ≤ ‖star U * (U * E * star U)‖ * ‖U‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ ‖star U‖ * ‖U * E * star U‖ * ‖U‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
      _ = ‖U * E * star U‖ := by rw [hU, hV]; ring

private lemma norm_diag_inv_eq [Nonempty n] (f : n → 𝕜) (S : Set 𝕜) (hS : S = Set.range f)
    (z : 𝕜) (hne : ∀ i, f i - z ≠ 0) :
    ‖(diagonal (fun i => (f i - z)⁻¹) : Matrix n n 𝕜)‖ = 1 / Metric.infDist z S := by
  rw [Matrix.l2_opNorm_diagonal]
  obtain ⟨i0, hi0⟩ := Finite.exists_min (fun i => ‖f i - z‖)
  have hd : Metric.infDist z S = ‖f i0 - z‖ := by
    subst hS
    apply le_antisymm
    · calc _ ≤ dist z (f i0) := Metric.infDist_le_dist_of_mem (Set.mem_range_self i0)
        _ = ‖f i0 - z‖ := by rw [dist_eq_norm, norm_sub_rev]
    · refine (Metric.le_infDist (Set.range_nonempty f)).2 ?_
      rintro y ⟨i, rfl⟩
      rw [dist_comm, dist_eq_norm]
      exact hi0 i
  have hpos : 0 < ‖f i0 - z‖ := norm_pos_iff.2 (hne i0)
  rw [hd]
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    rw [norm_inv, one_div]
    exact inv_anti₀ hpos (hi0 i)
  · have := norm_le_pi_norm (fun i => (f i - z)⁻¹) i0
    simpa [norm_inv] using this

private lemma exists_sortedEig_of_mem_spectrum {A : Matrix n n 𝕜} (hA : A.IsHermitian) {y : 𝕜}
    (hy : y ∈ spectrum 𝕜 A) : ∃ k, (sortedEig A k : 𝕜) = y := by
  rw [hA.spectrum_eq_image_range] at hy
  obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := hy
  refine ⟨(Fintype.equivOfCardEq (Fintype.card_fin _)).symm i, ?_⟩
  rw [sortedEig_eq hA]; rfl

private lemma isStarNormal_sub_smul_one {A : Matrix n n ℂ} (hA : IsStarNormal A) (z : ℂ) :
    IsStarNormal (A - z • (1 : Matrix n n ℂ)) := by
  constructor
  have hs : star (A - z • (1 : Matrix n n ℂ)) = star A - (star z) • 1 := by
    simp [star_sub, star_smul]
  rw [hs]
  exact Commute.sub_left (Commute.sub_right hA.star_comm_self ((Commute.one_right _).smul_right z))
    (Commute.sub_right ((Commute.one_left _).smul_left _)
      (((Commute.refl (1 : Matrix n n ℂ)).smul_left _).smul_right z))

private lemma isStarNormal_inv {B : Matrix n n ℂ} (hB : IsStarNormal B) :
    IsStarNormal B⁻¹ := by
  constructor
  have h : Bᴴ * B = B * Bᴴ := hB.star_comm_self.eq
  show star B⁻¹ * B⁻¹ = B⁻¹ * star B⁻¹
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_nonsing_inv, ← Matrix.mul_inv_rev,
    ← Matrix.mul_inv_rev, h]

/-- **Sharp resolvent norm, normal matrices**: for a normal complex matrix `A` and `z` off the
spectrum, `‖(A − z)⁻¹‖ = 1 / infDist z (spectrum ℂ A)`.
Proof route: under `Matrix.Norms.L2Operator`, `Matrix n n ℂ` is a `CStarAlgebra`
(`Matrix.instCStarAlgebra`). `A − z` is normal and a unit, so `(A − z)⁻¹ = Ring.inverse (A − z)` is
normal; `IsStarNormal.spectralRadius_eq_nnnorm` gives `‖R‖ = spectralRadius ℂ R`. By
`spectrum.map_inv`/`spectrum.inv_mem_iff` and `spectrum.sub_singleton_eq`-type lemmas,
`spectrum ℂ R = {(λ − z)⁻¹ : λ ∈ spectrum ℂ A}`; the spectrum is finite and nonempty (for `n`
nonempty), so the supremum of `|λ − z|⁻¹` is `1 / min |λ − z| = 1 / infDist z (spectrum ℂ A)`
(`Metric.infDist` of a finite set attained, `IsCompact.exists_infDist_eq_dist`). For `n` empty both
sides are `0`. Alternative route: unitary diagonalization and `l2_opNorm_diagonal`. -/
theorem norm_matResolvent_eq_of_isStarNormal {A : Matrix n n ℂ} (hA : IsStarNormal A) {z : ℂ}
    (hz : z ∉ spectrum ℂ A) :
    ‖matResolvent A z‖ = 1 / Metric.infDist z (spectrum ℂ A) := by
  have hB : IsUnit (A - z • (1 : Matrix n n ℂ)) := by
    have h := spectrum.notMem_iff.1 hz
    rw [Algebra.algebraMap_eq_smul_one] at h
    have := h.neg
    rwa [neg_sub] at this
  have : IsStarNormal (A - z • (1 : Matrix n n ℂ)) := isStarNormal_sub_smul_one hA z
  set u := hB.unit with hu
  have hR : matResolvent A z = ((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ) := by
    unfold matResolvent
    rw [Matrix.nonsing_inv_eq_ringInverse, ← IsUnit.unit_spec hB, Ring.inverse_unit]
  have : IsStarNormal (matResolvent A z) := by
    unfold matResolvent; exact isStarNormal_inv inferInstance
  -- spectrum of the resolvent
  have hspec : ∀ k : ℂ, k ∈ spectrum ℂ (matResolvent A z) ↔ ∃ μ ∈ spectrum ℂ A, k⁻¹ = μ - z := by
    intro k
    have h1 := spectrum.map_inv (𝕜 := ℂ) u
    have h2 : k ∈ spectrum ℂ (matResolvent A z) ↔ k⁻¹ ∈ spectrum ℂ (u : Matrix n n ℂ) := by
      rw [hR, ← h1]; simp [Set.mem_inv]
    rw [h2, hu, IsUnit.unit_spec, ← Algebra.algebraMap_eq_smul_one, ← spectrum.sub_singleton_eq]
    simp only [Set.mem_sub, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, y, rfl, h⟩; exact ⟨x, hx, h.symm⟩
    · rintro ⟨x, hx, h⟩; exact ⟨x, hx, z, rfl, h.symm⟩
  have hrad := IsStarNormal.spectralRadius_eq_nnnorm (matResolvent A z)
  rw [spectralRadius_eq_of_unital] at hrad
  have hnR : (‖matResolvent A z‖₊ : ENNReal) = ENNReal.ofReal ‖matResolvent A z‖ := by
    exact (ENNReal.ofReal_coe_nnreal (p := ‖matResolvent A z‖₊)).symm
  by_cases hne : (spectrum ℂ A).Nonempty
  · obtain ⟨μ0, hμ0, hd⟩ := (Matrix.finite_spectrum A).isCompact.exists_infDist_eq_dist hne z
    have hμz : μ0 - z ≠ 0 := fun h => hz (by rw [sub_eq_zero.1 h] at hμ0; exact hμ0)
    have hdpos : 0 < dist z μ0 := by
      rw [dist_comm, dist_eq_norm]; exact norm_pos_iff.2 hμz
    rw [hd]
    apply le_antisymm
    · -- ≤
      have h1 : ENNReal.ofReal ‖matResolvent A z‖ ≤ ENNReal.ofReal (1 / dist z μ0) := by
        rw [← hnR, ← hrad]
        refine iSup₂_le fun k hk => ?_
        obtain ⟨μ, hμ, hkμ⟩ := (hspec k).1 hk
        have h2 : dist z μ0 ≤ ‖μ - z‖ := by
          have := Metric.infDist_le_dist_of_mem (x := z) hμ
          rw [hd] at this
          rw [dist_comm z μ, dist_eq_norm μ z] at this
          exact this
        have h3 : ‖k‖ ≤ 1 / dist z μ0 := by
          have : ‖k‖ = ‖μ - z‖⁻¹ := by rw [← hkμ, norm_inv, inv_inv]
          rw [this, one_div]
          exact inv_anti₀ hdpos h2
        calc (‖k‖₊ : ENNReal) = ENNReal.ofReal ‖k‖ := (ENNReal.ofReal_coe_nnreal (p := ‖k‖₊)).symm
          _ ≤ _ := ENNReal.ofReal_le_ofReal h3
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
    · -- ≥
      have hk : (μ0 - z)⁻¹ ∈ spectrum ℂ (matResolvent A z) :=
        (hspec _).2 ⟨μ0, hμ0, by rw [inv_inv]⟩
      have h1 : ((‖(μ0 - z)⁻¹‖₊ : NNReal) : ENNReal) ≤ ‖matResolvent A z‖₊ := by
        rw [← hrad]
        exact le_iSup₂ (f := fun (k : ℂ) (_ : k ∈ spectrum ℂ (matResolvent A z)) =>
          ((‖k‖₊ : NNReal) : ENNReal)) _ hk
      have h2 : ‖(μ0 - z)⁻¹‖ ≤ ‖matResolvent A z‖ := by
        exact_mod_cast ENNReal.coe_le_coe.1 h1
      have h3 : ‖(μ0 - z)⁻¹‖ = 1 / dist z μ0 := by
        rw [norm_inv, dist_comm, dist_eq_norm, one_div]
      rw [← h3]
      exact h2
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have hs0 : spectrum ℂ (matResolvent A z) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun k hk => ?_
      obtain ⟨μ, hμ, _⟩ := (hspec k).1 hk
      rw [hne] at hμ; exact hμ
    rw [hs0] at hrad
    rw [iSup_emptyset, bot_eq_zero, eq_comm, ENNReal.coe_eq_zero, nnnorm_eq_zero] at hrad
    rw [hrad, hne, Metric.infDist_empty]
    simp

/-- `≤` corollary for normal matrices: if every spectral point is at distance `≥ δ > 0` from `z`,
then `‖(A − z)⁻¹‖ ≤ 1/δ`.
Proof route: `hδ'` gives `z ∉ spectrum` and `δ ≤ infDist` (`Metric.le_infDist`, nonempty case;
empty case: both sides trivial), then `norm_matResolvent_eq_of_isStarNormal` and
`one_div_le_one_div_of_le`. -/
theorem norm_matResolvent_le_of_isStarNormal {A : Matrix n n ℂ} (hA : IsStarNormal A) {z : ℂ}
    {δ : ℝ} (hδ : 0 < δ) (hδ' : ∀ μ ∈ spectrum ℂ A, δ ≤ ‖μ - z‖) :
    ‖matResolvent A z‖ ≤ 1 / δ := by
  have hz : z ∉ spectrum ℂ A := by
    intro h
    have := hδ' z h
    rw [sub_self, norm_zero] at this
    linarith
  rw [norm_matResolvent_eq_of_isStarNormal hA hz]
  by_cases hS : (spectrum ℂ A).Nonempty
  · have : δ ≤ Metric.infDist z (spectrum ℂ A) := by
      refine (Metric.le_infDist hS).2 fun y hy => ?_
      rw [dist_comm, dist_eq_norm]
      exact hδ' y hy
    exact one_div_le_one_div_of_le hδ this
  · rw [Set.not_nonempty_iff_eq_empty] at hS
    rw [hS, Metric.infDist_empty]
    simp only [div_zero]
    positivity

/-- **Sharp resolvent norm, Hermitian matrices** over any `RCLike 𝕜` (complex Hermitian, real
symmetric): `‖(A − z)⁻¹‖ = 1 / infDist z (spectrum 𝕜 A)` for `z ∉ spectrum 𝕜 A`.
Proof route: spectral theorem `A = U diag(λ) U*` (`IsHermitian.spectral_theorem`), so
`A − z = U diag(λ − z) U*` and `(A − z)⁻¹ = U diag((λ − z)⁻¹) U*`; the l2 operator norm is
unitarily invariant (`l2_opNorm_mul`, `‖U‖ = 1` for unitary `U`, `CStarRing.norm_of_mem_unitary`)
and `l2_opNorm_diagonal` gives `max |λᵢ − z|⁻¹`; `spectrum_eq_image_range` identifies the
spectrum. For `𝕜 = ℂ` this is also the special case `norm_matResolvent_eq_of_isStarNormal`. -/
theorem norm_matResolvent_eq_of_isHermitian {A : Matrix n n 𝕜} (hA : A.IsHermitian) {z : 𝕜}
    (hz : z ∉ spectrum 𝕜 A) :
    ‖matResolvent A z‖ = 1 / Metric.infDist z (spectrum 𝕜 A) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have h0 : matResolvent A z = 0 := by
      ext i
      exact (hn.false i).elim
    have hS : spectrum 𝕜 A = ∅ := by
      rw [hA.spectrum_eq_image_range, Set.range_eq_empty_iff.2 hn, Set.image_empty]
    rw [h0, norm_zero, hS, Metric.infDist_empty]; simp
  · have hne : ∀ i, (hA.eigenvalues i : 𝕜) - z ≠ 0 := by
      intro i h
      apply hz
      rw [hA.spectrum_eq_image_range]
      exact ⟨hA.eigenvalues i, Set.mem_range_self i, by rw [sub_eq_zero] at h; exact h⟩
    rw [matResolvent_eq_conj hA hz]
    rw [norm_unitary_conj _ _ (Unitary.coe_star_mul_self _)]
    refine norm_diag_inv_eq (fun i => (hA.eigenvalues i : 𝕜)) _ ?_ z hne
    rw [hA.spectrum_eq_image_range, ← Set.range_comp]; rfl

/-- `≤` corollary for Hermitian matrices, in eigenvalue form: if `δ ≤ |λₖ − z|` for every sorted
eigenvalue, then `‖(A − z)⁻¹‖ ≤ 1/δ`.
Proof route: `spectrum_eq_image_range`, `sortedEig_eq` and the reindexing between `eigenvalues` and
`eigenvalues₀` give `δ ≤ infDist z (spectrum 𝕜 A)` and `z ∉ spectrum`; then
`norm_matResolvent_eq_of_isHermitian`. -/
theorem norm_matResolvent_le_of_isHermitian {A : Matrix n n 𝕜} (hA : A.IsHermitian) {z : 𝕜}
    {δ : ℝ} (hδ : 0 < δ) (hδ' : ∀ k, δ ≤ ‖(sortedEig A k : 𝕜) - z‖) :
    ‖matResolvent A z‖ ≤ 1 / δ := by
  have hz : z ∉ spectrum 𝕜 A := by
    intro h
    obtain ⟨k, hk⟩ := exists_sortedEig_of_mem_spectrum hA h
    have := hδ' k
    rw [hk, sub_self, norm_zero] at this
    linarith
  rw [norm_matResolvent_eq_of_isHermitian hA hz]
  by_cases hS : (spectrum 𝕜 A).Nonempty
  · have : δ ≤ Metric.infDist z (spectrum 𝕜 A) := by
      refine (Metric.le_infDist hS).2 fun y hy => ?_
      obtain ⟨k, rfl⟩ := exists_sortedEig_of_mem_spectrum hA hy
      rw [dist_comm, dist_eq_norm]
      exact hδ' k
    exact one_div_le_one_div_of_le hδ this
  · rw [Set.not_nonempty_iff_eq_empty] at hS
    rw [hS, Metric.infDist_empty]
    simp only [div_zero]
    positivity

/-- Off the real axis: `‖(A − z)⁻¹‖ ≤ 1/|Im z|` for Hermitian `A`.
Proof route: `‖(λ : 𝕜) − z‖ ≥ |im ((λ : 𝕜) − z)| = |im z|` (`RCLike.abs_im_le_norm`,
`RCLike.ofReal_im`), then `norm_matResolvent_le_of_isHermitian` with `δ = |im z|`. -/
theorem norm_matResolvent_le_abs_im {A : Matrix n n 𝕜} (hA : A.IsHermitian) {z : 𝕜}
    (hz : RCLike.im z ≠ 0) :
    ‖matResolvent A z‖ ≤ 1 / |RCLike.im z| := by
  have hδ : 0 < |RCLike.im z| := abs_pos.2 hz
  refine norm_matResolvent_le_of_isHermitian hA hδ fun k => ?_
  calc |RCLike.im z| = |RCLike.im ((sortedEig A k : 𝕜) - z)| := by
        rw [map_sub, RCLike.ofReal_im, zero_sub, abs_neg]
    _ ≤ _ := RCLike.abs_im_le_norm _

/-- `‖R_A(−t)‖ ≤ 1/t` for PSD `A` and `t > 0` (all `RCLike 𝕜`, in particular real symmetric PSD).
Proof route: `matResolvent_neg_ofReal` and `norm_matResolvent_le_of_isHermitian` with `δ = t`, since
`‖(λₖ : 𝕜) + t‖ = λₖ + t ≥ t` by `sortedEig_nonneg`. (Muon's direct route: `resAux_opNorm_le` with
the quadratic-form bound `resAux_bound_R`.) -/
theorem norm_negResolvent_le {A : Matrix n n 𝕜} (hA : A.PosSemidef) {t : ℝ} (ht : 0 < t) :
    ‖negResolvent A t‖ ≤ 1 / t := by
  rw [← matResolvent_neg_ofReal]
  refine norm_matResolvent_le_of_isHermitian hA.isHermitian ht fun k => ?_
  have h0 := sortedEig_nonneg hA k
  have : ((sortedEig A k : ℝ) : 𝕜) - -(t : 𝕜) = ((sortedEig A k + t : ℝ) : 𝕜) := by
    push_cast; ring
  rw [this, RCLike.norm_ofReal, abs_of_nonneg (by linarith)]
  linarith

/-- Parameter Lipschitz bound: `‖R_A(−s) − R_A(−s')‖ ≤ |s − s'|/(s s')`.
Proof route: `negResolvent_sub_negResolvent_param`, `norm_smul`, `l2_opNorm_mul` and
`norm_negResolvent_le` twice (Muon `resAux_lip`). -/
theorem norm_negResolvent_sub_param_le {A : Matrix n n 𝕜} (hA : A.PosSemidef) {s s' : ℝ}
    (hs : 0 < s) (hs' : 0 < s') :
    ‖negResolvent A s - negResolvent A s'‖ ≤ |s - s'| / (s * s') := by
  rw [negResolvent_sub_negResolvent_param hA hs hs', RCLike.real_smul_eq_coe_smul (K := 𝕜),
    norm_smul, RCLike.norm_ofReal]
  have h1 := norm_negResolvent_le hA hs
  have h2 := norm_negResolvent_le hA hs'
  have hprod := Matrix.l2_opNorm_mul (negResolvent A s) (negResolvent A s')
  calc |s' - s| * ‖negResolvent A s * negResolvent A s'‖
      ≤ |s' - s| * (‖negResolvent A s‖ * ‖negResolvent A s'‖) :=
        mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
    _ ≤ |s' - s| * ((1 / s) * (1 / s')) := by gcongr
    _ = |s - s'| / (s * s') := by rw [abs_sub_comm]; field_simp

/-- **Lipschitz dependence on the matrix**: `‖R_A(−t) − R_B(−t)‖ ≤ ‖A − B‖/t²` for PSD `A`, `B`.
Proof route: `negResolvent_sub_negResolvent`, `l2_opNorm_mul` twice, `norm_negResolvent_le`
twice, `norm_sub_rev`. -/
theorem norm_negResolvent_sub_le {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {t : ℝ} (ht : 0 < t) :
    ‖negResolvent A t - negResolvent B t‖ ≤ ‖A - B‖ / t ^ 2 := by
  rw [negResolvent_sub_negResolvent hA hB ht]
  have h1 := norm_negResolvent_le hA ht
  have h2 := norm_negResolvent_le hB ht
  have e1 := Matrix.l2_opNorm_mul (negResolvent A t * (B - A)) (negResolvent B t)
  have e2 := Matrix.l2_opNorm_mul (negResolvent A t) (B - A)
  rw [norm_sub_rev] at e2
  calc ‖negResolvent A t * (B - A) * negResolvent B t‖
      ≤ ‖negResolvent A t * (B - A)‖ * ‖negResolvent B t‖ := e1
    _ ≤ (‖negResolvent A t‖ * ‖A - B‖) * ‖negResolvent B t‖ := by gcongr
    _ ≤ (1 / t * ‖A - B‖) * (1 / t) := by gcongr
    _ = ‖A - B‖ / t ^ 2 := by field_simp

private lemma re_star_dot_le (P : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n) :
    RCLike.re (star (WithLp.ofLp x) ⬝ᵥ (P *ᵥ WithLp.ofLp x)) ≤ ‖P‖ * ‖x‖ ^ 2 := by
  have h1 : star (WithLp.ofLp x) ⬝ᵥ (P *ᵥ WithLp.ofLp x) =
      inner 𝕜 x (WithLp.toLp 2 (P *ᵥ WithLp.ofLp x)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  have h2 := P.l2_opNorm_mulVec x
  calc RCLike.re (star (WithLp.ofLp x) ⬝ᵥ (P *ᵥ WithLp.ofLp x))
      ≤ ‖star (WithLp.ofLp x) ⬝ᵥ (P *ᵥ WithLp.ofLp x)‖ := RCLike.re_le_norm _
    _ = ‖inner 𝕜 x (WithLp.toLp 2 (P *ᵥ WithLp.ofLp x))‖ := by rw [h1]
    _ ≤ ‖x‖ * ‖WithLp.toLp 2 (P *ᵥ WithLp.ofLp x)‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖P‖ * ‖x‖) := by gcongr; exact h2
    _ = ‖P‖ * ‖x‖ ^ 2 := by ring

private lemma norm_le_of_eig [Nonempty n] {X : Matrix n n 𝕜} (hX : X.IsHermitian) {c : ℝ}
    (hc : ∀ i, |hX.eigenvalues i| ≤ c) : ‖X‖ ≤ c := by
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc (Classical.arbitrary n))
  have h1 : star (hX.eigenvectorUnitary : Matrix n n 𝕜) * (hX.eigenvectorUnitary : Matrix n n 𝕜) = 1 :=
    Unitary.coe_star_mul_self _
  have hX' : X = (hX.eigenvectorUnitary : Matrix n n 𝕜) * diagonal (RCLike.ofReal ∘ hX.eigenvalues) *
      star (hX.eigenvectorUnitary : Matrix n n 𝕜) := by
    conv_lhs => rw [hX.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
  have hE : ‖(diagonal (RCLike.ofReal ∘ hX.eigenvalues) : Matrix n n 𝕜)‖ ≤ c := by
    rw [Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg hc0]
    intro i
    simpa using hc i
  rw [hX']
  rw [norm_unitary_conj _ _ h1]
  exact hE

private lemma norm_sub_le_of_psd {P Q : Matrix n n 𝕜} (hP : P.PosSemidef) (hQ : Q.PosSemidef)
    {c : ℝ} (hPc : ‖P‖ ≤ c) (hQc : ‖Q‖ ≤ c) : ‖P - Q‖ ≤ c := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have : P - Q = 0 := by
      ext i; exact (hn.false i).elim
    rw [this, norm_zero]
    exact (norm_nonneg _).trans hPc
  · have hX : (P - Q).IsHermitian := hP.isHermitian.sub hQ.isHermitian
    refine norm_le_of_eig hX fun i => ?_
    set e := hX.eigenvectorBasis i with he
    have hen : ‖e‖ = 1 := hX.eigenvectorBasis.orthonormal.1 i
    have hP0 : 0 ≤ RCLike.re (star (WithLp.ofLp e) ⬝ᵥ (P *ᵥ WithLp.ofLp e)) :=
      (RCLike.nonneg_iff.1 (hP.dotProduct_mulVec_nonneg _)).1
    have hQ0 : 0 ≤ RCLike.re (star (WithLp.ofLp e) ⬝ᵥ (Q *ᵥ WithLp.ofLp e)) :=
      (RCLike.nonneg_iff.1 (hQ.dotProduct_mulVec_nonneg _)).1
    have hP1 := re_star_dot_le P e
    have hQ1 := re_star_dot_le Q e
    rw [hen] at hP1 hQ1
    have h := hX.eigenvalues_eq i
    rw [Matrix.sub_mulVec, dotProduct_sub, map_sub] at h
    rw [h, abs_le]
    constructor <;> nlinarith

/-- The difference of two PSD resolvents at `−t` has norm at most `1/t` (independently of `A − B`).
Proof route: both resolvents are Hermitian with spectra in `[0, 1/t]`, so for unit `x`,
`quadForm (R_A − R_B) x ∈ [−1/t, 1/t]`; for Hermitian `X`, `‖X‖ = sup |quadForm X x|`
(`ContinuousLinearMap.norm_eq_iSup_rayleighQuotient`-type lemma, `IsSelfAdjoint`). -/
theorem norm_negResolvent_sub_le_inv {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) {t : ℝ} (ht : 0 < t) :
    ‖negResolvent A t - negResolvent B t‖ ≤ 1 / t := by
  exact norm_sub_le_of_psd (posDef_negResolvent hA ht).posSemidef (posDef_negResolvent hB ht).posSemidef
    (norm_negResolvent_le hA ht) (norm_negResolvent_le hB ht)

/-- For Hermitian `X`, `|re tr X| ≤ rank X · ‖X‖`.
Proof route: `re tr X = ∑ λᵢ` (`trace_eq_sum_eigenvalues`), at most `rank X` eigenvalues are
nonzero (`rank_eq_card_non_zero_eigs`), and each `|λᵢ| ≤ ‖X‖` (eigenvector bound
`l2_opNorm_mulVec` with `mulVec_eigenvectorBasis`). -/
theorem abs_re_trace_le_rank_mul_norm {X : Matrix n n 𝕜} (hX : X.IsHermitian) :
    |RCLike.re (trace X)| ≤ X.rank * ‖X‖ := by
  have hb : ∀ i, |hX.eigenvalues i| ≤ ‖X‖ := by
    intro i
    set e := hX.eigenvectorBasis i with he
    have hen : ‖e‖ = 1 := hX.eigenvectorBasis.orthonormal.1 i
    have h1 := X.l2_opNorm_mulVec e
    have h2 : (EuclideanSpace.equiv n 𝕜).symm (X *ᵥ WithLp.ofLp e) = (hX.eigenvalues i) • e := by
      rw [he, hX.mulVec_eigenvectorBasis i]
      exact WithLp.toLp_smul 2 _ _
    rw [h2, norm_smul, hen, Real.norm_eq_abs] at h1
    simpa using h1
  have hsum : RCLike.re (trace X) = ∑ i, hX.eigenvalues i := by
    rw [hX.trace_eq_sum_eigenvalues, map_sum]
    simp
  rw [hsum, hX.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  have hsplit : ∑ i, hX.eigenvalues i = ∑ i ∈ Finset.univ.filter (fun i => hX.eigenvalues i ≠ 0), hX.eigenvalues i := by
    rw [Finset.sum_filter_ne_zero]
  rw [hsplit]
  calc |∑ i ∈ Finset.univ.filter (fun i => hX.eigenvalues i ≠ 0), hX.eigenvalues i|
      ≤ ∑ i ∈ Finset.univ.filter (fun i => hX.eigenvalues i ≠ 0), |hX.eigenvalues i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => hX.eigenvalues i ≠ 0), ‖X‖ :=
        Finset.sum_le_sum fun i _ => hb i
    _ = _ := by simp

/-- `rank (R_A(−t) − R_B(−t)) ≤ rank (A − B)` for PSD `A`, `B`, `t > 0`.
Proof route: `negResolvent_sub_negResolvent` and `Matrix.rank_mul_le_left`,
`Matrix.rank_mul_le_right`; `rank (B − A) = rank (A − B)` (`neg_sub`, `rank_neg`). -/
theorem rank_negResolvent_sub_le {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {t : ℝ} (ht : 0 < t) :
    (negResolvent A t - negResolvent B t).rank ≤ (A - B).rank := by
  rw [negResolvent_sub_negResolvent hA hB ht]
  calc (negResolvent A t * (B - A) * negResolvent B t).rank
      ≤ (negResolvent A t * (B - A)).rank := Matrix.rank_mul_le_left _ _
    _ ≤ (B - A).rank := Matrix.rank_mul_le_right _ _
    _ = (A - B).rank := by
      have h := Matrix.rank_smul_of_mem_nonZeroDivisors (c := (-1 : 𝕜)) (A - B)
        (mem_nonZeroDivisors_of_ne_zero (by simp))
      rw [neg_one_smul, neg_sub] at h
      exact h

/-- **Rank bound**: `|tr R_A(−t) − tr R_B(−t)| ≤ rank(A − B)/t` for PSD `A`, `B`, `t > 0`.
Proof route: `trace_sub`, `map_sub`, then `abs_re_trace_le_rank_mul_norm` for the Hermitian
difference (`isHermitian_negResolvent`), `rank_negResolvent_sub_le` and
`norm_negResolvent_sub_le_inv`. -/
theorem abs_re_trace_negResolvent_sub_le {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) {t : ℝ} (ht : 0 < t) :
    |RCLike.re (trace (negResolvent A t)) - RCLike.re (trace (negResolvent B t))| ≤
      (A - B).rank / t := by
  have hH : (negResolvent A t - negResolvent B t).IsHermitian :=
    (isHermitian_negResolvent hA.isHermitian t).sub (isHermitian_negResolvent hB.isHermitian t)
  have h1 := abs_re_trace_le_rank_mul_norm hH
  rw [Matrix.trace_sub, map_sub] at h1
  refine h1.trans ?_
  have h2 := rank_negResolvent_sub_le hA hB ht
  have h3 := norm_negResolvent_sub_le_inv hA hB ht
  calc ((negResolvent A t - negResolvent B t).rank : ℝ) * ‖negResolvent A t - negResolvent B t‖
      ≤ ((A - B).rank : ℝ) * (1 / t) := by
        gcongr
    _ = _ := by ring

end Norms

/-! ### Rank-one updates of PSD resolvents -/

private lemma one_add_star_dot_ne_zero {A : Matrix n n 𝕜} (hA : A.PosSemidef) {t : ℝ} (ht : 0 < t)
    (w : n → 𝕜) : 1 + star w ⬝ᵥ (negResolvent A t *ᵥ w) ≠ 0 := by
  intro h
  have h0 := (RCLike.nonneg_iff.1 ((posDef_negResolvent hA ht).posSemidef.dotProduct_mulVec_nonneg w)).1
  have := congrArg RCLike.re h
  rw [map_add, RCLike.one_re, map_zero] at this
  linarith

/-- **Sherman–Morrison for resolvents**: for PSD `A`, `t > 0` and a vector `w`, with `R = R_A(−t)`,
`R_{A + ww*}(−t) = R − (1 + w* R w)⁻¹ (R w)(w* R)`.
Proof route: `inv_add_vecMulVec` applied to `A + t • 1` (invertible by `isUnit_det_add_smul_one`)
with `u = w`, `v = star w`; the denominator is nonzero because `star w ⬝ᵥ R w` has nonnegative real
part (`posDef_negResolvent`). Rearrange `A + ww* + t = (A + t) + ww*` by `add_right_comm`. -/
theorem negResolvent_add_vecMulVec {A : Matrix n n 𝕜} (hA : A.PosSemidef) {t : ℝ} (ht : 0 < t)
    (w : n → 𝕜) :
    negResolvent (A + vecMulVec w (star w)) t =
      negResolvent A t - (1 + star w ⬝ᵥ (negResolvent A t *ᵥ w))⁻¹ •
        vecMulVec (negResolvent A t *ᵥ w) (star w ᵥ* negResolvent A t) := by
  have h := inv_add_vecMulVec (isUnit_det_add_smul_one hA ht) w (star w)
    (one_add_star_dot_ne_zero hA ht w)
  unfold negResolvent at h ⊢
  rw [add_right_comm]
  exact h

/-- Rank-one update applied to the update vector: `R_{A + ww*}(−t) w = (1 + w* R w)⁻¹ R w`.
Proof route: apply `negResolvent_add_vecMulVec` to `w`; `vecMulVec_mulVec`-type simp and
`(star w ᵥ* R) ⬝ᵥ w = star w ⬝ᵥ (R *ᵥ w)` (`dotProduct_mulVec`); field arithmetic. -/
theorem negResolvent_add_vecMulVec_mulVec {A : Matrix n n 𝕜} (hA : A.PosSemidef) {t : ℝ}
    (ht : 0 < t) (w : n → 𝕜) :
    negResolvent (A + vecMulVec w (star w)) t *ᵥ w =
      (1 + star w ⬝ᵥ (negResolvent A t *ᵥ w))⁻¹ • (negResolvent A t *ᵥ w) := by
  rw [negResolvent_add_vecMulVec hA ht w, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, op_smul_eq_smul, ← Matrix.dotProduct_mulVec]
  have hne := one_add_star_dot_ne_zero hA ht w
  set d := star w ⬝ᵥ (negResolvent A t *ᵥ w) with hd
  rw [smul_smul]
  have e : (1 : 𝕜) - (1 + d)⁻¹ * d = (1 + d)⁻¹ := by
    field_simp; ring
  calc negResolvent A t *ᵥ w - ((1 + d)⁻¹ * d) • (negResolvent A t *ᵥ w)
      = (1 : 𝕜) • (negResolvent A t *ᵥ w) - ((1 + d)⁻¹ * d) • (negResolvent A t *ᵥ w) := by
        rw [one_smul]
    _ = _ := by rw [← sub_smul, e]

/-! ## Nuclear norm (real matrices) -/

section Nuclear

variable {m p q : Type*} [Fintype m] [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq p]
  [DecidableEq q]

/-- Nuclear norm `‖K‖_*` of a real matrix: the sum of the singular values of `K` as a linear map
between Euclidean spaces (same defining expression as Muon's `nuc`). -/
def nuclearNorm (K : Matrix m n ℝ) : ℝ :=
  (toEuclideanLin K).singularValues.sum fun _ s => s

/-! ### Private helpers for the nuclear norm (ported from Muon `Foundations/Nuclear.lean`) -/

omit [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q] in
private lemma nuc_eig_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (S S' : E →ₗ[ℝ] E) (h : S = S') (hS : S.IsSymmetric)
    (hS' : S'.IsSymmetric) (k : ℕ) (hn : Module.finrank ℝ E = k) (i : Fin k) :
    hS.eigenvalues hn i = hS'.eigenvalues hn i := by
  subst h; rfl

omit [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q] in
/-- Nuclear norm as a sum of square roots of the eigenvalues of `KᵀK`. -/
private lemma nuclearNorm_eq_sum_sqrt (K : Matrix m n ℝ) (hA : (Kᵀ * K).IsHermitian) :
    nuclearNorm K = ∑ i, √(hA.eigenvalues i) := by
  have hop : (toEuclideanLin K).adjoint ∘ₗ toEuclideanLin K = toEuclideanLin (Kᵀ * K) := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (Matrix.toLpLin_mul (p := 2) (q := 2) (r := 2) Kᵀ K).symm
  have hsupp : (toEuclideanLin K).singularValues.support ⊆ Finset.range (Fintype.card n) := by
    intro i hi
    rw [Finset.mem_range]
    by_contra h
    push Not at h
    exact (Finsupp.mem_support_iff.mp hi)
      ((toEuclideanLin K).singularValues_of_finrank_le (by rw [finrank_euclideanSpace]; exact h))
  unfold nuclearNorm
  rw [Finsupp.sum_of_support_subset _ hsupp _ (fun i _ => rfl),
    ← Fin.sum_univ_eq_sum_range (fun i => (toEuclideanLin K).singularValues i) (Fintype.card n)]
  have e : ∑ i, √(hA.eigenvalues i) = ∑ j : Fin (Fintype.card n), √(hA.eigenvalues₀ j) :=
    Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
      (fun j => √(hA.eigenvalues₀ j)) |>.symm ▸ rfl
  rw [e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.singularValues_fin _ finrank_euclideanSpace i]
  congr 1
  exact nuc_eig_congr _ _ hop _ _ _ _ i

omit [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q] in
private lemma nuc_isHermitian_transpose_mul_self (K : Matrix m n ℝ) : (Kᵀ * K).IsHermitian := by
  simpa using Matrix.isHermitian_conjTranspose_mul_self K

omit [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q] in
private lemma nuc_isHermitian_mul_transpose_self (K : Matrix m n ℝ) : (K * Kᵀ).IsHermitian := by
  simpa using Matrix.isHermitian_mul_conjTranspose_self K

omit [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q] in
/-- Eigen-decomposition data of `Kᵀ K`. -/
private lemma nuc_exists_svd_data (K : Matrix m n ℝ) :
    ∃ (V : Matrix n n ℝ) (μ : n → ℝ), Vᵀ * V = 1 ∧ V * Vᵀ = 1 ∧
      Vᵀ * (Kᵀ * K) * V = Matrix.diagonal μ ∧ (∀ i, 0 ≤ μ i) ∧ nuclearNorm K = ∑ i, √(μ i) := by
  have hA := nuc_isHermitian_transpose_mul_self K
  have hA0 : (Kᵀ * K).PosSemidef := by
    simpa using Matrix.posSemidef_conjTranspose_mul_self K
  obtain ⟨V, hV⟩ : ∃ V : Matrix n n ℝ, V = (hA.eigenvectorUnitary : Matrix n n ℝ) := ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : n → ℝ, μ = hA.eigenvalues := ⟨_, rfl⟩
  have hstar : star V = Vᵀ := by
    rw [hV, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hVV : Vᵀ * V = 1 := by rw [← hstar, hV, Unitary.coe_star_mul_self]
  have hVV' : V * Vᵀ = 1 := by rw [← hstar, hV, ← Unitary.coe_star, Unitary.coe_mul_star_self]
  have hspec : Kᵀ * K = V * Matrix.diagonal μ * Vᵀ := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, ← hV, hstar, ← hμ]
    rfl
  refine ⟨V, μ, hVV, hVV', ?_, fun i => ?_, ?_⟩
  · rw [hspec]
    calc Vᵀ * (V * Matrix.diagonal μ * Vᵀ) * V = (Vᵀ * V) * Matrix.diagonal μ * (Vᵀ * V) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal μ := by rw [hVV, Matrix.one_mul, Matrix.mul_one]
  · rw [hμ]
    exact hA0.eigenvalues_nonneg i
  · rw [nuclearNorm_eq_sum_sqrt K hA, hμ]

private lemma nuc_sum_sqrt_eq_roots {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : A.IsHermitian) :
    ∑ i, √(hA.eigenvalues i) = ((A.charpoly.roots).map Real.sqrt).sum := by
  rw [hA.roots_charpoly_eq_eigenvalues₀]
  calc ∑ i, √(hA.eigenvalues i)
      = ∑ j : Fin (Fintype.card ι), √(hA.eigenvalues₀ j) :=
        Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
          (fun j => √(hA.eigenvalues₀ j))
    _ = _ := by rw [Finset.sum_eq_multiset_sum, Multiset.map_map]; rfl

omit [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q] in
private lemma nuc_sqrt_roots_charpoly_mul_transpose_eq (K : Matrix m n ℝ) :
    (((K * Kᵀ).charpoly.roots).map Real.sqrt).sum
      = (((Kᵀ * K).charpoly.roots).map Real.sqrt).sum := by
  have hc := Matrix.charpoly_mul_comm' K Kᵀ
  have hne : ∀ k : ℕ, (Polynomial.X ^ k : Polynomial ℝ) ≠ 0 :=
    fun k => pow_ne_zero _ Polynomial.X_ne_zero
  have hP := (Matrix.charpoly_monic (K * Kᵀ)).ne_zero
  have hQ := (Matrix.charpoly_monic (Kᵀ * K)).ne_zero
  have hr := congrArg Polynomial.roots hc
  rw [Polynomial.roots_mul (mul_ne_zero (hne _) hP),
    Polynomial.roots_mul (mul_ne_zero (hne _) hQ),
    Polynomial.roots_X_pow, Polynomial.roots_X_pow] at hr
  have := congrArg (fun s => (s.map Real.sqrt).sum) hr
  simpa [Multiset.map_add, Multiset.sum_add, Multiset.nsmul_singleton, Multiset.map_replicate,
    Multiset.sum_replicate] using this



/-- Proof route: `Finsupp.sum_nonneg` with `LinearMap.singularValues_nonneg` (Muon `nuc_nonneg`). -/
theorem nuclearNorm_nonneg (K : Matrix m n ℝ) : 0 ≤ nuclearNorm K := by
  unfold nuclearNorm
  unfold Finsupp.sum
  exact Finset.sum_nonneg fun i _ => LinearMap.singularValues_nonneg _ i

/-- Proof route: port Muon `nuc_transpose` (`Foundations/Nuclear.lean` l.73): the nonzero singular
values of `Kᵀ` and `K` agree (`KᵀK` and `KKᵀ` share their nonzero eigenvalues). -/
theorem nuclearNorm_transpose (K : Matrix m n ℝ) : nuclearNorm Kᵀ = nuclearNorm K := by
  rw [nuclearNorm_eq_sum_sqrt Kᵀ (nuc_isHermitian_transpose_mul_self Kᵀ),
    nuclearNorm_eq_sum_sqrt K (nuc_isHermitian_transpose_mul_self K),
    nuc_sum_sqrt_eq_roots, nuc_sum_sqrt_eq_roots, Matrix.transpose_transpose]
  exact nuc_sqrt_roots_charpoly_mul_transpose_eq K

section NucPort

open scoped Matrix.Norms.L2Operator

private lemma nuc_sum_sq_mulVec_eq (M : Matrix p n ℝ) (c : n → ℝ) :
    ∑ k, (M *ᵥ c) k ^ 2 = ∑ i, ∑ j, (Mᵀ * M) i j * (c i * c j) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, sq,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

private lemma nuc_sum_sq_mulVec_le (U : Matrix m n ℝ) (x : n → ℝ) :
    ∑ k, (U *ᵥ x) k ^ 2 ≤ ‖U‖ ^ 2 * ∑ i, x i ^ 2 := by
  have hb : ‖Matrix.toEuclideanLin U (WithLp.toLp 2 x)‖ ≤ ‖U‖ * ‖WithLp.toLp 2 x‖ := by
    rw [Matrix.l2_opNorm_def]
    exact (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin U)).le_opNorm (WithLp.toLp 2 x)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [mul_pow, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)] at hsq
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Real.norm_eq_abs, sq_abs] using hsq

private lemma nuc_opNorm_le_of_sq (U : Matrix m n ℝ) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ x : n → ℝ, ∑ k, (U *ᵥ x) k ^ 2 ≤ M ^ 2 * ∑ i, x i ^ 2) : ‖U‖ ≤ M := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun x => ?_
  show ‖Matrix.toEuclideanLin U x‖ ≤ M * ‖x‖
  have hx := h (WithLp.ofLp x)
  have hsq : ‖Matrix.toEuclideanLin U x‖ ^ 2 ≤ (M * ‖x‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Real.norm_eq_abs, sq_abs] using hx
  nlinarith [norm_nonneg (Matrix.toEuclideanLin U x), mul_nonneg hM (norm_nonneg x)]

private lemma nuc_colsq_eq (W : Matrix p n ℝ) (μ : n → ℝ) (h : Wᵀ * W = Matrix.diagonal μ)
    (i : n) : ∑ k, W k i ^ 2 = μ i := by
  have h2 := congrFun (congrFun h i) i
  rw [Matrix.diagonal_apply_eq] at h2
  rw [← h2]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, sq]

private lemma nuc_trace_transpose_mul_eq (Z W : Matrix p n ℝ) :
    (Zᵀ * W).trace = ∑ i, ∑ k, Z k i * W k i := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]

private lemma nuc_trace_mul_eq_sum (U K : Matrix m n ℝ) (V : Matrix n n ℝ) (hV : V * Vᵀ = 1) :
    (Uᵀ * K).trace = ∑ i, ∑ k, (U * V) k i * (K * V) k i := by
  have e : Uᵀ * K = Uᵀ * K * V * Vᵀ := by
    rw [Matrix.mul_assoc (Uᵀ * K) V Vᵀ, hV, Matrix.mul_one]
  calc (Uᵀ * K).trace = (Uᵀ * K * V * Vᵀ).trace := by rw [← e]
    _ = (Vᵀ * (Uᵀ * K * V)).trace := Matrix.trace_mul_comm _ _
    _ = ((U * V)ᵀ * (K * V)).trace := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = ∑ i, ∑ k, (U * V) k i * (K * V) k i := nuc_trace_transpose_mul_eq _ _

private lemma nuc_upper_aux (K U : Matrix m n ℝ) (hU : ‖U‖ ≤ 1) :
    (Uᵀ * K).trace ≤ nuclearNorm K := by
  obtain ⟨V, μ, hVV, hVV', hWV, hμ, hnuc⟩ := nuc_exists_svd_data K
  have hWW : (K * V)ᵀ * (K * V) = Matrix.diagonal μ := by
    rw [← hWV]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [hnuc, nuc_trace_mul_eq_sum U K V hVV']
  apply Finset.sum_le_sum
  intro i _
  have hcol : ∑ k, V k i ^ 2 = 1 := nuc_colsq_eq V (fun _ => 1) (by
    rw [hVV]; ext a b; simp [Matrix.one_apply, Matrix.diagonal_apply]) i
  have hZ : ∑ k, (U * V) k i ^ 2 ≤ 1 := by
    have h1 := nuc_sum_sq_mulVec_le U (fun k => V k i)
    have e : ∀ k, (U * V) k i = (U *ᵥ fun k => V k i) k := fun k => by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    have h0 : 0 ≤ ‖U‖ := norm_nonneg _
    have hcol' : ∑ j, (fun k => V k i) j ^ 2 = 1 := hcol
    have h2 : ∑ k, (U *ᵥ fun k => V k i) k ^ 2 ≤ 1 := by
      calc _ ≤ ‖U‖ ^ 2 * ∑ j, (fun k => V k i) j ^ 2 := h1
        _ = ‖U‖ ^ 2 * 1 := by rw [hcol']
        _ ≤ 1 := by nlinarith
    simp only [e]
    exact h2
  have hW2 : ∑ k, (K * V) k i ^ 2 = μ i := nuc_colsq_eq (K * V) μ hWW i
  calc ∑ k, (U * V) k i * (K * V) k i ≤ |∑ k, (U * V) k i * (K * V) k i| := le_abs_self _
    _ ≤ √((∑ k, (U * V) k i ^ 2) * ∑ k, (K * V) k i ^ 2) :=
        Real.abs_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
    _ ≤ √(μ i) := Real.sqrt_le_sqrt (by rw [hW2]; exact mul_le_of_le_one_left (hμ i) hZ)

private lemma nuc_attained_aux (K : Matrix m n ℝ) :
    ∃ U : Matrix m n ℝ, ‖U‖ ≤ 1 ∧ (Uᵀ * K).trace = nuclearNorm K := by
  obtain ⟨V, μ, hVV, hVV', hWV, hμ, hnuc⟩ := nuc_exists_svd_data K
  have hWW : (K * V)ᵀ * (K * V) = Matrix.diagonal μ := by
    rw [← hWV]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  obtain ⟨s, hs⟩ : ∃ s : n → ℝ, ∀ i, s i = if 0 < μ i then (√(μ i))⁻¹ else 0 :=
    ⟨_, fun i => rfl⟩
  have hms : ∀ i, μ i * s i ^ 2 ≤ 1 := by
    intro i
    by_cases h : 0 < μ i
    · rw [hs i, if_pos h, inv_pow, Real.sq_sqrt (hμ i), mul_inv_cancel₀ h.ne']
    · have h0 : μ i = 0 := le_antisymm (not_lt.mp h) (hμ i)
      rw [hs i, if_neg h, h0]; norm_num
  have hsμ : ∀ i, s i * μ i = √(μ i) := by
    intro i
    by_cases h : 0 < μ i
    · rw [hs i, if_pos h, inv_mul_eq_div, div_eq_iff (Real.sqrt_pos.mpr h).ne']
      exact (Real.mul_self_sqrt (hμ i)).symm
    · have h0 : μ i = 0 := le_antisymm (not_lt.mp h) (hμ i)
      rw [hs i, if_neg h, h0]; simp
  refine ⟨(K * V) * Matrix.diagonal s * Vᵀ, ?_, ?_⟩
  · apply nuc_opNorm_le_of_sq _ 1 zero_le_one
    intro x
    have hUx : ((K * V) * Matrix.diagonal s * Vᵀ) *ᵥ x
        = (K * V) *ᵥ (Matrix.diagonal s *ᵥ (Vᵀ *ᵥ x)) := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    have hy : ∑ k, (Vᵀ *ᵥ x) k ^ 2 = ∑ i, x i ^ 2 := by
      rw [nuc_sum_sq_mulVec_eq, Matrix.transpose_transpose, hVV']
      simp [Matrix.one_apply, sq]
    rw [hUx, nuc_sum_sq_mulVec_eq (K * V), hWW, one_pow, one_mul]
    calc ∑ i, ∑ j, Matrix.diagonal μ i j * ((Matrix.diagonal s *ᵥ (Vᵀ *ᵥ x)) i
            * (Matrix.diagonal s *ᵥ (Vᵀ *ᵥ x)) j)
        = ∑ i, μ i * (s i * (Vᵀ *ᵥ x) i) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [Matrix.diagonal_apply, Matrix.mulVec_diagonal, sq]
      _ = ∑ i, (μ i * s i ^ 2) * (Vᵀ *ᵥ x) i ^ 2 := Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i, (Vᵀ *ᵥ x) i ^ 2 := Finset.sum_le_sum fun i _ =>
          mul_le_of_le_one_left (sq_nonneg _) (hms i)
      _ = ∑ i, x i ^ 2 := hy
  · have hUV : ((K * V) * Matrix.diagonal s * Vᵀ) * V = (K * V) * Matrix.diagonal s := by
      rw [Matrix.mul_assoc, hVV, Matrix.mul_one]
    rw [nuc_trace_mul_eq_sum _ K V hVV', hUV, hnuc]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcs := nuc_colsq_eq (K * V) μ hWW i
    calc ∑ k, ((K * V) * Matrix.diagonal s) k i * (K * V) k i
        = s i * ∑ k, (K * V) k i ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Matrix.mul_diagonal]; ring
      _ = s i * μ i := by rw [hcs]
      _ = √(μ i) := hsμ i

private lemma nuc_trace_smul_mul_transpose (A : Matrix m n ℝ) (B : Matrix n m ℝ) (t : ℝ) :
    ((t • A)ᵀ * Bᵀ).trace = t * (A * B).trace := by
  have hT : (Aᵀ * Bᵀ).trace = (A * B).trace := by
    rw [← Matrix.transpose_mul, Matrix.trace_transpose, Matrix.trace_mul_comm]
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, hT]

private lemma nuc_opNorm_smul_le_one (A : Matrix m n ℝ) (t : ℝ)
    (ht : t ^ 2 * ‖A‖ ^ 2 ≤ 1) : ‖(t • A)‖ ≤ 1 := by
  apply nuc_opNorm_le_of_sq _ 1 zero_le_one
  intro x
  have e : ∑ k, ((t • A) *ᵥ x) k ^ 2 = t ^ 2 * ∑ k, (A *ᵥ x) k ^ 2 := by
    rw [Matrix.smul_mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [e, one_pow, one_mul]
  have hS : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  calc t ^ 2 * ∑ k, (A *ᵥ x) k ^ 2 ≤ t ^ 2 * (‖A‖ ^ 2 * ∑ i, x i ^ 2) :=
        mul_le_mul_of_nonneg_left (nuc_sum_sq_mulVec_le A x) (sq_nonneg t)
    _ = (t ^ 2 * ‖A‖ ^ 2) * ∑ i, x i ^ 2 := by ring
    _ ≤ 1 * ∑ i, x i ^ 2 := mul_le_mul_of_nonneg_right ht hS
    _ = ∑ i, x i ^ 2 := one_mul _

private lemma nuc_eq_zero_of_opNorm_eq_zero (A : Matrix m n ℝ) (h : ‖A‖ = 0) : A = 0 := by
  exact norm_eq_zero.mp h



private theorem nuc_add_le_aux (K L : Matrix m n ℝ) :
    nuclearNorm (K + L) ≤ nuclearNorm K + nuclearNorm L := by
  obtain ⟨U, hU, htr⟩ := nuc_attained_aux (K + L)
  rw [← htr, Matrix.mul_add, Matrix.trace_add]
  exact add_le_add (nuc_upper_aux K U hU) (nuc_upper_aux L U hU)

private theorem nuc_isGreatest_dual_aux (K : Matrix m n ℝ) :
    IsGreatest {t : ℝ | ∃ U : Matrix m n ℝ, ‖U‖ ≤ 1 ∧ t = (Uᵀ * K).trace} (nuclearNorm K) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨U, hU, h⟩ := nuc_attained_aux K
    exact ⟨U, hU, h.symm⟩
  · rintro t ⟨U, hU, rfl⟩
    exact nuc_upper_aux K U hU

omit [Fintype q] [DecidableEq q] in
private theorem nuc_trace_mul_le (A : Matrix m n ℝ) (B : Matrix n m ℝ) :
    |(A * B).trace| ≤ ‖A‖ * nuclearNorm B := by
  have key : ∀ U : Matrix m n ℝ, ‖U‖ ≤ 1 → (Uᵀ * Bᵀ).trace ≤ nuclearNorm B := by
    intro U hU
    have h := nuc_upper_aux Bᵀ U hU
    rwa [nuclearNorm_transpose] at h
  have hnn : (0 : ℝ) ≤ ‖A‖ := norm_nonneg _
  rcases eq_or_lt_of_le hnn with hc | hc
  · have hA := nuc_eq_zero_of_opNorm_eq_zero A hc.symm
    rw [← hc, hA]
    simp
  · have hc' : ‖A‖ ≠ 0 := hc.ne'
    have h1 := key _ (nuc_opNorm_smul_le_one A (‖A‖)⁻¹
      (le_of_eq (by rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hc')])))
    have h2 := key _ (nuc_opNorm_smul_le_one A (-(‖A‖)⁻¹)
      (le_of_eq (by rw [neg_sq, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hc')])))
    rw [nuc_trace_smul_mul_transpose] at h1 h2
    have f1 : (A * B).trace ≤ ‖A‖ * nuclearNorm B := by
      have := mul_le_mul_of_nonneg_left h1 hnn
      rwa [← mul_assoc, mul_inv_cancel₀ hc', one_mul] at this
    have f2 : -(A * B).trace ≤ ‖A‖ * nuclearNorm B := by
      have := mul_le_mul_of_nonneg_left h2 hnn
      have e : ‖A‖ * (-(‖A‖)⁻¹ * (A * B).trace) = -(A * B).trace := by
        field_simp
      rw [e] at this
      exact this
    exact abs_le.mpr ⟨by linarith, f1⟩

omit [Fintype q] [DecidableEq q] in
private theorem nuc_mul_le_left (A : Matrix m n ℝ) (B : Matrix n p ℝ) :
    nuclearNorm (A * B) ≤ ‖A‖ * nuclearNorm B := by
  obtain ⟨U, hU, htr⟩ := nuc_attained_aux (A * B)
  have hTA : ‖Aᵀ‖ = ‖A‖ := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.l2_opNorm_conjTranspose]
  have hAU : ‖Aᵀ * U‖ ≤ ‖A‖ := by
    calc ‖Aᵀ * U‖ ≤ ‖Aᵀ‖ * ‖U‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ ‖A‖ * 1 := by
        rw [hTA]
        exact mul_le_mul_of_nonneg_left hU (norm_nonneg A)
      _ = ‖A‖ := mul_one _
  have e : Uᵀ * (A * B) = (Aᵀ * U)ᵀ * B := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [← htr, e]
  have h := nuc_trace_mul_le (Aᵀ * U)ᵀ B
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.l2_opNorm_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact le_trans (le_abs_self _) (le_trans h (mul_le_mul_of_nonneg_right hAU (nuclearNorm_nonneg B)))

/-- Gram form in a spectral frame (private helper): if `Wᵀ W = diag μ` then
`‖W y‖² = ∑ μ_i y_i²`. -/
private lemma nuc_sum_sq_diag_aux (W : Matrix p n ℝ) (μ : n → ℝ)
    (hWW : Wᵀ * W = Matrix.diagonal μ) (y : n → ℝ) :
    ∑ k, (W *ᵥ y) k ^ 2 = ∑ i, μ i * y i ^ 2 := by
  rw [nuc_sum_sq_mulVec_eq, hWW]
  simp [Matrix.diagonal_apply, sq]

/-- Quadratic form of `Kᵀ K` in an eigenframe `V` of `Kᵀ K` (private helper). -/
private lemma nuc_sum_sq_K_eq (K : Matrix m n ℝ) (V : Matrix n n ℝ) (μ : n → ℝ)
    (hVV' : V * Vᵀ = 1) (hWW : (K * V)ᵀ * (K * V) = Matrix.diagonal μ) (x : n → ℝ) :
    ∑ k, (K *ᵥ x) k ^ 2 = ∑ i, μ i * (Vᵀ *ᵥ x) i ^ 2 := by
  have hx : (K * V) *ᵥ (Vᵀ *ᵥ x) = K *ᵥ x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hVV', Matrix.mul_one]
  rw [← hx]
  exact nuc_sum_sq_diag_aux _ _ hWW _

/-- Operator norm bounded by nuclear norm `‖K‖ ≤ ‖K‖_*` (task L-0.5c; no paper label; snapshot
`cr-2026-10-22`). Standard fact: the largest singular value is at most the sum of all. -/
private theorem nuc_opNorm_le_nuc (K : Matrix m n ℝ) : ‖K‖ ≤ nuclearNorm K := by
  obtain ⟨V, μ, hVV, hVV', hWV, hμ, hnuc⟩ := nuc_exists_svd_data K
  have hWW : (K * V)ᵀ * (K * V) = Matrix.diagonal μ := by
    rw [← hWV]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  have hμle : ∀ i, μ i ≤ nuclearNorm K ^ 2 := by
    intro i
    have h1 : √(μ i) ≤ nuclearNorm K := by
      rw [hnuc]
      exact Finset.single_le_sum (fun j _ => Real.sqrt_nonneg _) (Finset.mem_univ i)
    have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    rwa [Real.sq_sqrt (hμ i)] at h2
  refine nuc_opNorm_le_of_sq K (nuclearNorm K) (nuclearNorm_nonneg K) ?_
  intro x
  rw [nuc_sum_sq_K_eq K V μ hVV' hWW x]
  have hy : ∑ i, (Vᵀ *ᵥ x) i ^ 2 = ∑ i, x i ^ 2 := by
    rw [nuc_sum_sq_mulVec_eq, Matrix.transpose_transpose, hVV']
    simp [Matrix.one_apply, sq]
  calc ∑ i, μ i * (Vᵀ *ᵥ x) i ^ 2 ≤ ∑ i, nuclearNorm K ^ 2 * (Vᵀ *ᵥ x) i ^ 2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hμle i) (sq_nonneg _)
    _ = nuclearNorm K ^ 2 * ∑ i, x i ^ 2 := by rw [← hy, Finset.mul_sum]

private theorem nuc_le_rank_mul_opNorm_aux (K : Matrix m n ℝ) :
    nuclearNorm K ≤ (Matrix.rank K : ℝ) * ‖K‖ := by
  obtain ⟨V, μ, hVV, hVV', hWV, hμ, hnuc⟩ := nuc_exists_svd_data K
  have hWW : (K * V)ᵀ * (K * V) = Matrix.diagonal μ := by
    rw [← hWV]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  -- each singular value is at most `‖K‖`: test on the i-th column of `V`
  have hopμ : ∀ i, √(μ i) ≤ ‖K‖ := by
    intro i
    have hyx : ∀ j, (Vᵀ *ᵥ (fun k => V k i)) j = if j = i then 1 else 0 := by
      intro j
      have h := congrFun (congrFun hVV j) i
      simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.mulVec, dotProduct] using h
    have hxn : ∑ k, (fun k => V k i) k ^ 2 = 1 := by
      have h := congrFun (congrFun hVV i) i
      simpa [Matrix.mul_apply, Matrix.one_apply, sq] using h
    have e := nuc_sum_sq_K_eq K V μ hVV' hWW (fun k => V k i)
    simp only [hyx] at e
    simp at e
    have hμi : μ i ≤ ‖K‖ ^ 2 := by
      calc μ i = ∑ k, (K *ᵥ fun k => V k i) k ^ 2 := e.symm
        _ ≤ ‖K‖ ^ 2 * ∑ k, (fun k => V k i) k ^ 2 := nuc_sum_sq_mulVec_le K (fun k => V k i)
        _ = ‖K‖ ^ 2 := by rw [hxn, mul_one]
    calc √(μ i) ≤ √(‖K‖ ^ 2) := Real.sqrt_le_sqrt hμi
      _ = ‖K‖ := Real.sqrt_sq (norm_nonneg _)
  -- rank of `K` is the number of nonzero singular values
  have hrk : Matrix.rank K = (Finset.univ.filter (fun i => μ i ≠ 0)).card := by
    have hVu : IsUnit V.det := Matrix.isUnit_det_of_right_inverse hVV'
    have hVTu : IsUnit Vᵀ.det := Matrix.isUnit_det_of_right_inverse hVV
    have hc : (Kᵀ * K).rank = (Matrix.diagonal μ).rank := by
      rw [← hWV, Matrix.rank_mul_eq_left_of_isUnit_det V (Vᵀ * (Kᵀ * K)) hVu,
        Matrix.rank_mul_eq_right_of_isUnit_det Vᵀ (Kᵀ * K) hVTu]
    rw [← Matrix.rank_transpose_mul_self K, hc, Matrix.rank_diagonal, Fintype.card_subtype]
  have hsum : ∑ i, √(μ i) = ∑ i ∈ Finset.univ.filter (fun i => μ i ≠ 0), √(μ i) :=
    (Finset.sum_filter_of_ne (p := fun i => μ i ≠ 0) fun i _ h hμ0 =>
      h (by rw [hμ0, Real.sqrt_zero])).symm
  rw [hnuc, hsum]
  calc ∑ i ∈ Finset.univ.filter (fun i => μ i ≠ 0), √(μ i)
      ≤ ∑ i ∈ Finset.univ.filter (fun i => μ i ≠ 0), ‖K‖ :=
        Finset.sum_le_sum fun i _ => hopμ i
    _ = ((Finset.univ.filter (fun i => μ i ≠ 0)).card : ℝ) * ‖K‖ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (Matrix.rank K : ℝ) * ‖K‖ := by rw [hrk]


private theorem nuc_smul_aux (c : ℝ) (K : Matrix m n ℝ) :
    nuclearNorm (c • K) = |c| * nuclearNorm K := by
  have key : ∀ (c : ℝ) (K : Matrix m n ℝ), nuclearNorm (c • K) ≤ |c| * nuclearNorm K := by
    intro c K
    obtain ⟨U, hU, htr⟩ := nuc_attained_aux (c • K)
    rw [← htr, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    rcases le_total 0 c with hc | hc
    · rw [abs_of_nonneg hc]
      exact mul_le_mul_of_nonneg_left (nuc_upper_aux K U hU) hc
    · rw [abs_of_nonpos hc]
      have := nuc_upper_aux K (-U) (by rwa [norm_neg])
      rw [Matrix.transpose_neg, Matrix.neg_mul, Matrix.trace_neg] at this
      nlinarith
  apply le_antisymm (key c K)
  by_cases hc : c = 0
  · subst hc
    have h0 : nuclearNorm ((0 : ℝ) • K) = 0 := by
      rw [zero_smul]
      have := key 0 (0 : Matrix m n ℝ)
      have h1 := nuclearNorm_nonneg (0 : Matrix m n ℝ)
      simp only [abs_zero, zero_mul, zero_smul] at this
      linarith
    rw [h0]; simp
  · have h := key c⁻¹ (c • K)
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul, abs_inv] at h
    have hpos : 0 < |c| := abs_pos.2 hc
    calc |c| * nuclearNorm K ≤ |c| * (|c|⁻¹ * nuclearNorm (c • K)) := by gcongr
      _ = nuclearNorm (c • K) := by field_simp

omit [Fintype q] [DecidableEq q] in
private theorem nuc_mul_le_right (B : Matrix m n ℝ) (A : Matrix n p ℝ) :
    nuclearNorm (B * A) ≤ nuclearNorm B * ‖A‖ := by
  have h := nuc_mul_le_left Aᵀ Bᵀ
  rw [← Matrix.transpose_mul] at h
  have hA : ‖Aᵀ‖ = ‖A‖ := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.l2_opNorm_conjTranspose]
  rw [nuclearNorm_transpose, nuclearNorm_transpose, hA] at h
  rw [mul_comm]
  exact h

private theorem nuc_mul_three_aux (X : Matrix m n ℝ) (Y : Matrix n p ℝ) (Z : Matrix p q ℝ) :
    nuclearNorm (X * Y * Z) ≤ ‖X‖ * nuclearNorm Y * ‖Z‖ := by
  have h1 := nuc_mul_le_right (X * Y) Z
  have h2 := nuc_mul_le_left X Y
  exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (norm_nonneg Z))

end NucPort

/-- Proof route: port Muon `nuc_smul` (`Foundations/Nuclear.lean` l.88). -/
theorem nuclearNorm_smul (c : ℝ) (K : Matrix m n ℝ) : nuclearNorm (c • K) = |c| * nuclearNorm K := by
  exact nuc_smul_aux c K

/-- Triangle inequality.
Proof route: port Muon `nuc_add_le` (via the duality `nuc_isGreatest_dual`,
`‖K‖_* = max_{‖Q‖ ≤ 1} tr(QᵀK)`). -/
theorem nuclearNorm_add_le (K L : Matrix m n ℝ) :
    nuclearNorm (K + L) ≤ nuclearNorm K + nuclearNorm L := by
  exact nuc_add_le_aux K L

open scoped Matrix.Norms.L2Operator in
/-- `‖X Y Z‖_* ≤ ‖X‖ ‖Y‖_* ‖Z‖`.
Proof route: port Muon `nuc_mul_three_le` (`nuc_mul_le_left`, `nuc_mul_le_right`). -/
theorem nuclearNorm_mul_three_le (X : Matrix m n ℝ) (Y : Matrix n p ℝ) (Z : Matrix p q ℝ) :
    nuclearNorm (X * Y * Z) ≤ ‖X‖ * nuclearNorm Y * ‖Z‖ := by
  exact nuc_mul_three_aux X Y Z

open scoped Matrix.Norms.L2Operator in
/-- `‖K‖ ≤ ‖K‖_*`.
Proof route: port Muon `opNorm_le_nuc` (the top singular value is the operator norm). -/
theorem norm_le_nuclearNorm (K : Matrix m n ℝ) : ‖K‖ ≤ nuclearNorm K := by
  exact nuc_opNorm_le_nuc K

open scoped Matrix.Norms.L2Operator in
/-- `‖K‖_* ≤ rank K · ‖K‖`.
Proof route: port Muon `nuc_le_rank_mul_opNorm`: at most `rank K` singular values are nonzero
(`LinearMap.card_support_singularValues`, `Matrix.rank` vs `finrank` of the range), each `≤ ‖K‖`. -/
theorem nuclearNorm_le_rank_mul_norm (K : Matrix m n ℝ) :
    nuclearNorm K ≤ (K.rank : ℝ) * ‖K‖ := by
  exact nuc_le_rank_mul_opNorm_aux K

end Nuclear

/-! ## Gram resolvents of a real rectangular matrix -/

section Gram

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Output-side Gram resolvent `R_s(M) = (MMᵀ + s)⁻¹` (Muon's `Rs`). -/
def gramResolvent (M : Matrix m n ℝ) (s : ℝ) : Matrix m m ℝ :=
  negResolvent (M * Mᵀ) s

/-- Input-side Gram resolvent `R̃_s(M) = (MᵀM + s)⁻¹` (Muon's `Rts`). -/
def gramResolventT (M : Matrix m n ℝ) (s : ℝ) : Matrix n n ℝ :=
  negResolvent (Mᵀ * M) s

/-- Mixed resolvent `𝖷_s(M) = R_s(M) M` (Muon's `Xs`). -/
def mixedResolvent (M : Matrix m n ℝ) (s : ℝ) : Matrix m n ℝ :=
  gramResolvent M s * M

omit [DecidableEq n] in
/-- Unfolding check: `gramResolvent` is literally Muon's `(M * Mᵀ + s • 1)⁻¹`. -/
theorem gramResolvent_def (M : Matrix m n ℝ) (s : ℝ) :
    gramResolvent M s = (M * Mᵀ + s • (1 : Matrix m m ℝ))⁻¹ := rfl

omit [DecidableEq m] in
/-- Unfolding check for `gramResolventT`. -/
theorem gramResolventT_def (M : Matrix m n ℝ) (s : ℝ) :
    gramResolventT M s = (Mᵀ * M + s • (1 : Matrix n n ℝ))⁻¹ := rfl

/-- `MMᵀ` is PSD.
Proof route: `posSemidef_self_mul_conjTranspose M` and `conjTranspose_eq_transpose_of_trivial`. -/
theorem posSemidef_mul_transpose_self (M : Matrix m n ℝ) : (M * Mᵀ).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose M
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- `MᵀM` is PSD.
Proof route: `posSemidef_conjTranspose_mul_self M` and `conjTranspose_eq_transpose_of_trivial`. -/
theorem posSemidef_transpose_mul_self (M : Matrix m n ℝ) : (Mᵀ * M).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self M
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

section GramHelpers

open scoped Matrix.Norms.L2Operator

private def sqNorm' {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ := ∑ i, x i ^ 2

private lemma gr_isUnit (K : Matrix m n ℝ) {s : ℝ} (hs : 0 < s) :
    IsUnit (K * Kᵀ + s • (1 : Matrix m m ℝ)).det :=
  isUnit_det_add_smul_one (posSemidef_mul_transpose_self K) hs

private lemma gr_isUnit_T (K : Matrix m n ℝ) {s : ℝ} (hs : 0 < s) :
    IsUnit (Kᵀ * K + s • (1 : Matrix n n ℝ)).det := by
  have h := gr_isUnit Kᵀ hs
  rwa [Matrix.transpose_transpose] at h

private lemma gr_mulVec_inv (K : Matrix m n ℝ) (s : ℝ) (hs : 0 < s) (x : m → ℝ) :
    (K * Kᵀ + s • (1 : Matrix m m ℝ)) *ᵥ ((K * Kᵀ + s • (1 : Matrix m m ℝ))⁻¹ *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (gr_isUnit K hs), Matrix.one_mulVec]

private lemma gr_vecMul (K : Matrix m n ℝ) (y : m → ℝ) : y ᵥ* K = Kᵀ *ᵥ y := by
  have h := Matrix.vecMul_transpose Kᵀ y
  rwa [Matrix.transpose_transpose] at h

private lemma gr_dot_mulVec (K : Matrix m n ℝ) (y : m → ℝ) (x : n → ℝ) :
    y ⬝ᵥ (K *ᵥ x) = (Kᵀ *ᵥ y) ⬝ᵥ x := by
  rw [Matrix.dotProduct_mulVec, gr_vecMul]

private lemma gr_quad (K : Matrix m n ℝ) (s : ℝ) (y : m → ℝ) :
    y ⬝ᵥ ((K * Kᵀ + s • (1 : Matrix m m ℝ)) *ᵥ y) = sqNorm' (Kᵀ *ᵥ y) + s * sqNorm' y := by
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
    dotProduct_smul, smul_eq_mul, ← Matrix.mulVec_mulVec, gr_dot_mulVec]
  simp [sqNorm', dotProduct, sq]

private lemma gr_cs (y x : m → ℝ) : (y ⬝ᵥ x) ^ 2 ≤ sqNorm' y * sqNorm' x := by
  simpa [dotProduct, sqNorm'] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ y x

private lemma gr_sqNorm_nonneg (x : m → ℝ) : 0 ≤ sqNorm' x :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

private lemma gr_real_R (p t q X s : ℝ) (hs : 0 < s) (ht : 0 ≤ t) (hq : 0 ≤ q)
    (hX : 0 ≤ X) (hp : p = t + s * q) (hcs : p ^ 2 ≤ q * X) : s ^ 2 * q ≤ X := by
  by_contra hcon
  push_neg at hcon
  have hsq : s * q ≤ p := by linarith
  have hq0 : 0 < q := by
    rcases eq_or_lt_of_le hq with h0 | h0
    · rw [← h0, mul_zero] at hcon
      linarith
    · exact h0
  have h1 : (s * q) ^ 2 ≤ p ^ 2 := by nlinarith [mul_nonneg hs.le hq]
  have h2 := mul_lt_mul_of_pos_left hcon hq0
  nlinarith

private lemma gr_real_X (p t q X s : ℝ) (hs : 0 < s) (ht : 0 ≤ t) (hq : 0 ≤ q)
    (hX : 0 ≤ X) (hp : p = t + s * q) (hcs : p ^ 2 ≤ t * X) : 4 * s * q ≤ X := by
  have ht' : t = p - s * q := by linarith
  subst ht'
  have key : 0 ≤ X * (X - 4 * s * q) := by nlinarith [sq_nonneg (2 * p - X)]
  rcases eq_or_lt_of_le hX with h0 | h0
  · subst h0
    nlinarith [sq_nonneg p, mul_nonneg hs.le hq]
  · have := (mul_nonneg_iff_of_pos_left h0).mp key
    linarith

/-- Bound on `R = (K Kᵀ + s)⁻¹` in the squared-vector form. -/
private lemma gr_bound_R (K : Matrix m n ℝ) (s : ℝ) (hs : 0 < s) (x : m → ℝ) :
    s ^ 2 * sqNorm' ((K * Kᵀ + s • (1 : Matrix m m ℝ))⁻¹ *ᵥ x) ≤ sqNorm' x := by
  have hy : (K * Kᵀ + s • (1 : Matrix m m ℝ)) *ᵥ ((K * Kᵀ + s • (1 : Matrix m m ℝ))⁻¹ *ᵥ x) = x :=
    gr_mulVec_inv K s hs x
  generalize hyd : (K * Kᵀ + s • (1 : Matrix m m ℝ))⁻¹ *ᵥ x = y at hy ⊢
  have hp : y ⬝ᵥ x = sqNorm' (Kᵀ *ᵥ y) + s * sqNorm' y := by
    rw [← hy]; exact gr_quad K s y
  exact gr_real_R _ _ _ _ s hs (gr_sqNorm_nonneg _) (gr_sqNorm_nonneg _)
    (gr_sqNorm_nonneg _) hp (gr_cs y x)

/-- Bound on `R M` in the squared-vector form: `4 s ‖R M x‖² ≤ ‖x‖²`. -/
private lemma gr_bound_X (K : Matrix m n ℝ) (s : ℝ) (hs : 0 < s) (x : n → ℝ) :
    4 * s * sqNorm' ((K * Kᵀ + s • (1 : Matrix m m ℝ))⁻¹ *ᵥ (K *ᵥ x)) ≤ sqNorm' x := by
  have hy : (K * Kᵀ + s • (1 : Matrix m m ℝ)) *ᵥ ((K * Kᵀ + s • (1 : Matrix m m ℝ))⁻¹ *ᵥ (K *ᵥ x))
      = K *ᵥ x := gr_mulVec_inv K s hs _
  generalize hyd : (K * Kᵀ + s • (1 : Matrix m m ℝ))⁻¹ *ᵥ (K *ᵥ x) = y at hy ⊢
  have hp : y ⬝ᵥ (K *ᵥ x) = sqNorm' (Kᵀ *ᵥ y) + s * sqNorm' y := by
    rw [← hy]; exact gr_quad K s y
  have hcs : (y ⬝ᵥ (K *ᵥ x)) ^ 2 ≤ sqNorm' (Kᵀ *ᵥ y) * sqNorm' x := by
    rw [gr_dot_mulVec]; exact gr_cs _ _
  exact gr_real_X _ _ _ _ s hs (gr_sqNorm_nonneg _) (gr_sqNorm_nonneg _)
    (gr_sqNorm_nonneg _) hp hcs

/-- Operator-norm bound from a squared-vector bound. -/
private lemma gr_opNorm_le (K : Matrix m n ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : n → ℝ, sqNorm' (K *ᵥ x) ≤ c ^ 2 * sqNorm' x) : ‖K‖ ≤ c := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  show ‖(EuclideanSpace.equiv m ℝ).symm (K *ᵥ (EuclideanSpace.equiv n ℝ x))‖
      ≤ c * ‖x‖
  have hx : sqNorm' (EuclideanSpace.equiv n ℝ x) = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [sqNorm', Real.norm_eq_abs, sq_abs]
  have hy : sqNorm' (K *ᵥ (EuclideanSpace.equiv n ℝ x))
      = ‖(EuclideanSpace.equiv m ℝ).symm (K *ᵥ (EuclideanSpace.equiv n ℝ x))‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [sqNorm', Real.norm_eq_abs, sq_abs]
  have h2 := h (EuclideanSpace.equiv n ℝ x)
  rw [hx, hy] at h2
  refine le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg hc (norm_nonneg _)) ?_
  rw [mul_pow]
  exact h2


end GramHelpers

/-- **Push-through identity**: `R_s(M) M = M R̃_s(M)`, i.e. `(MMᵀ + s)⁻¹ M = M (MᵀM + s)⁻¹`.
Proof route: `(MMᵀ + s) M = M (MᵀM + s)`; multiply by the two inverses
(Muon `resAux_intertw`). -/
theorem gramResolvent_mul (M : Matrix m n ℝ) {s : ℝ} (hs : 0 < s) :
    gramResolvent M s * M = M * gramResolventT M s := by
  unfold gramResolvent gramResolventT negResolvent
  have hA : (M * Mᵀ + s • (1 : Matrix m m ℝ))⁻¹ * (M * Mᵀ + s • (1 : Matrix m m ℝ)) = 1 :=
    Matrix.nonsing_inv_mul _ (gr_isUnit M hs)
  have hB : (Mᵀ * M + s • (1 : Matrix n n ℝ)) * (Mᵀ * M + s • (1 : Matrix n n ℝ))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (gr_isUnit_T M hs)
  have hAM : (M * Mᵀ + s • (1 : Matrix m m ℝ)) * M = M * (Mᵀ * M + s • (1 : Matrix n n ℝ)) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  calc (M * Mᵀ + s • (1 : Matrix m m ℝ))⁻¹ * M
      = (M * Mᵀ + s • (1 : Matrix m m ℝ))⁻¹ * M * ((Mᵀ * M + s • (1 : Matrix n n ℝ)) *
          (Mᵀ * M + s • (1 : Matrix n n ℝ))⁻¹) := by rw [hB, Matrix.mul_one]
    _ = (M * Mᵀ + s • (1 : Matrix m m ℝ))⁻¹ * (M * (Mᵀ * M + s • (1 : Matrix n n ℝ))) *
          (Mᵀ * M + s • (1 : Matrix n n ℝ))⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (M * Mᵀ + s • (1 : Matrix m m ℝ))⁻¹ * ((M * Mᵀ + s • (1 : Matrix m m ℝ)) * M) *
          (Mᵀ * M + s • (1 : Matrix n n ℝ))⁻¹ := by rw [hAM]
    _ = ((M * Mᵀ + s • (1 : Matrix m m ℝ))⁻¹ * (M * Mᵀ + s • (1 : Matrix m m ℝ))) * M *
          (Mᵀ * M + s • (1 : Matrix n n ℝ))⁻¹ := by simp only [Matrix.mul_assoc]
    _ = M * (Mᵀ * M + s • (1 : Matrix n n ℝ))⁻¹ := by rw [hA, Matrix.one_mul]

/-- `Mᵀ R_s(M) M = 1 − s R̃_s(M)`.
Proof route: `gramResolvent_mul`, then `self_mul_negResolvent` for `MᵀM` (Muon `resAux_id5`). -/
theorem transpose_mul_gramResolvent_mul (M : Matrix m n ℝ) {s : ℝ} (hs : 0 < s) :
    Mᵀ * gramResolvent M s * M = 1 - s • gramResolventT M s := by
  rw [Matrix.mul_assoc, gramResolvent_mul M hs, ← Matrix.mul_assoc]
  exact self_mul_negResolvent (posSemidef_transpose_mul_self M) hs

/-- `R_s(M) MMᵀ = 1 − s R_s(M)`.
Proof route: `negResolvent_mul_self` for `MMᵀ` (Muon `resAux_id6`). -/
theorem gramResolvent_mul_gram (M : Matrix m n ℝ) {s : ℝ} (hs : 0 < s) :
    gramResolvent M s * (M * Mᵀ) = 1 - s • gramResolvent M s := by
  exact negResolvent_mul_self (posSemidef_mul_transpose_self M) hs

/-- Trace balance between the two Gram resolvents (the finite-size form of the first identity of
an isotropic measure pair, `γout − t S_out(−t) = γin − t S_in(−t)`):
`card m − s tr R_s(M) = card n − s tr R̃_s(M)`.
Proof route: take traces in `gramResolvent_mul_gram` and `transpose_mul_gramResolvent_mul`
(`trace_sub`, `trace_one`, `trace_smul`); the left sides agree because
`tr (R (M Mᵀ)) = tr ((R M) Mᵀ) = tr (Mᵀ (R M))` (`Matrix.mul_assoc`, `trace_mul_comm`). -/
theorem card_sub_mul_trace_gramResolvent (M : Matrix m n ℝ) {s : ℝ} (hs : 0 < s) :
    (Fintype.card m : ℝ) - s * trace (gramResolvent M s) =
      (Fintype.card n : ℝ) - s * trace (gramResolventT M s) := by
  have h1 := gramResolvent_mul_gram M hs
  have h2 := transpose_mul_gramResolvent_mul M hs
  have e : trace (gramResolvent M s * (M * Mᵀ)) = trace (Mᵀ * gramResolvent M s * M) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have h3 := congrArg trace h1
  have h4 := congrArg trace h2
  rw [Matrix.trace_sub, Matrix.trace_one, Matrix.trace_smul, smul_eq_mul] at h3 h4
  rw [e] at h3
  linarith

/-- Matrix-Lipschitz decomposition:
`R_s(K) − R_s(K') = R_s(K) (K' − K) (K'ᵀ R_s(K')) + R_s(K) K (K' − K)ᵀ R_s(K')`.
Proof route: `negResolvent_sub_negResolvent` and
`K'K'ᵀ − KKᵀ = (K' − K)K'ᵀ + K(K' − K)ᵀ` (Muon `lipAux_resid`). -/
theorem gramResolvent_sub_gramResolvent (K K' : Matrix m n ℝ) {s : ℝ} (hs : 0 < s) :
    gramResolvent K s - gramResolvent K' s =
      gramResolvent K s * (K' - K) * (K'ᵀ * gramResolvent K' s) +
        gramResolvent K s * K * (K' - K)ᵀ * gramResolvent K' s := by
  have h1 := negResolvent_sub_negResolvent (posSemidef_mul_transpose_self K)
    (posSemidef_mul_transpose_self K') hs
  have h2 : K' * K'ᵀ - K * Kᵀ = (K' - K) * K'ᵀ + K * (K' - K)ᵀ := by
    rw [Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub]
    abel
  unfold gramResolvent
  rw [h1, h2]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

section GramNorms

open scoped Matrix.Norms.L2Operator

/-- `‖R_s(M)‖ ≤ 1/s`. Proof route: `norm_negResolvent_le` with `posSemidef_mul_transpose_self`. -/
theorem norm_gramResolvent_le (M : Matrix m n ℝ) {s : ℝ} (hs : 0 < s) :
    ‖gramResolvent M s‖ ≤ 1 / s := by
  exact norm_negResolvent_le (posSemidef_mul_transpose_self M) hs

/-- `‖R̃_s(M)‖ ≤ 1/s`. Proof route: `norm_negResolvent_le` with `posSemidef_transpose_mul_self`. -/
theorem norm_gramResolventT_le (M : Matrix m n ℝ) {s : ℝ} (hs : 0 < s) :
    ‖gramResolventT M s‖ ≤ 1 / s := by
  exact norm_negResolvent_le (posSemidef_transpose_mul_self M) hs

/-- `‖R_s(M) M‖ ≤ 1/(2√s)`.
Proof route: `‖R M x‖² = ⟪x, Mᵀ R² M x⟫` and `Mᵀ R² M = R̃ − s R̃²` (push-through), whose
eigenvalues `μ/(μ + s)²` are `≤ 1/(4s)` (AM–GM); or port Muon `resAux_bound_X` and
`resAux_opNorm_le`. -/
theorem norm_mixedResolvent_le (M : Matrix m n ℝ) {s : ℝ} (hs : 0 < s) :
    ‖mixedResolvent M s‖ ≤ 1 / (2 * Real.sqrt s) := by
  unfold mixedResolvent gramResolvent negResolvent
  refine gr_opNorm_le _ (div_nonneg zero_le_one (by positivity)) fun x => ?_
  rw [← Matrix.mulVec_mulVec]
  have h := gr_bound_X M s hs x
  have hc : (1 / (2 * Real.sqrt s)) ^ 2 * sqNorm' x = sqNorm' x / (4 * s) := by
    rw [div_pow, one_pow, mul_pow, Real.sq_sqrt hs.le]
    ring
  rw [hc, le_div_iff₀ (by linarith)]
  linarith

/-- `‖Mᵀ R_s(M)‖ ≤ 1/(2√s)`.
Proof route: `Mᵀ R_s(M) = R̃_s(M) Mᵀ = mixedResolvent Mᵀ s` (push-through for `Mᵀ`,
`transpose_transpose`) and `norm_mixedResolvent_le` (Muon `lipAux_opNorm_Rt_K`). -/
theorem norm_transpose_mul_gramResolvent_le (M : Matrix m n ℝ) {s : ℝ} (hs : 0 < s) :
    ‖Mᵀ * gramResolvent M s‖ ≤ 1 / (2 * Real.sqrt s) := by
  have hI : Mᵀ * gramResolvent M s = gramResolventT M s * Mᵀ := by
    have h := gramResolvent_mul Mᵀ hs
    simp only [gramResolvent, gramResolventT, Matrix.transpose_transpose] at h ⊢
    exact h.symm
  rw [hI]
  have h := norm_mixedResolvent_le Mᵀ hs
  simp only [mixedResolvent, gramResolvent, Matrix.transpose_transpose] at h
  exact h

/-- **`lem:app-de-resolvent`**, in Muon's exact shape (with `‖·‖` the l2 operator norm for Muon's
`opNorm`).
Proof route: the conjunction of `norm_gramResolvent_le`, `norm_gramResolventT_le`,
`norm_mixedResolvent_le`, `gramResolvent_mul`, `transpose_mul_gramResolvent_mul`,
`gramResolvent_mul_gram` and `norm_negResolvent_sub_param_le`. -/
theorem gramResolvent_facts (M : Matrix m n ℝ) (s : ℝ) (hs : 0 < s) :
    ‖gramResolvent M s‖ ≤ 1 / s ∧
    ‖gramResolventT M s‖ ≤ 1 / s ∧
    ‖mixedResolvent M s‖ ≤ 1 / (2 * Real.sqrt s) ∧
    gramResolvent M s * M = M * gramResolventT M s ∧
    Mᵀ * gramResolvent M s * M = (1 : Matrix n n ℝ) - s • gramResolventT M s ∧
    gramResolvent M s * (M * Mᵀ) = (1 : Matrix m m ℝ) - s • gramResolvent M s ∧
    ∀ s' : ℝ, 0 < s' → ‖gramResolvent M s - gramResolvent M s'‖ ≤ |s - s'| / (s * s') := by
  exact ⟨norm_gramResolvent_le M hs, norm_gramResolventT_le M hs, norm_mixedResolvent_le M hs,
    gramResolvent_mul M hs, transpose_mul_gramResolvent_mul M hs, gramResolvent_mul_gram M hs,
    fun s' hs' => norm_negResolvent_sub_param_le (posSemidef_mul_transpose_self M) hs hs'⟩

/-- Operator-norm Lipschitz bound in the rectangular matrix:
`‖R_s(K) − R_s(K')‖ ≤ ‖K − K'‖ / (s√s)`.
Proof route: `gramResolvent_sub_gramResolvent`, `norm_add_le`, `l2_opNorm_mul`,
`l2_opNorm_conjTranspose` for the transpose (`conjTranspose_eq_transpose_of_trivial`), and the
bounds `1/s`, `1/(2√s)` of `norm_gramResolvent_le`, `norm_transpose_mul_gramResolvent_le`,
`norm_mixedResolvent_le`. -/
theorem norm_gramResolvent_sub_le (K K' : Matrix m n ℝ) {s : ℝ} (hs : 0 < s) :
    ‖gramResolvent K s - gramResolvent K' s‖ ≤ ‖K - K'‖ / (s * Real.sqrt s) := by
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  rw [gramResolvent_sub_gramResolvent K K' hs]
  have hR := norm_gramResolvent_le K hs
  have hR' := norm_gramResolvent_le K' hs
  have hT := norm_transpose_mul_gramResolvent_le K' hs
  have hX := norm_mixedResolvent_le K hs
  have hKK : ‖K' - K‖ = ‖K - K'‖ := norm_sub_rev _ _
  have hKT : ‖(K' - K)ᵀ‖ = ‖K - K'‖ := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.l2_opNorm_conjTranspose, hKK]
  have hD := norm_nonneg (K - K')
  have t1 : ‖gramResolvent K s * (K' - K) * (K'ᵀ * gramResolvent K' s)‖ ≤
      1 / s * ‖K - K'‖ * (1 / (2 * Real.sqrt s)) := by
    calc _ ≤ ‖gramResolvent K s * (K' - K)‖ * ‖K'ᵀ * gramResolvent K' s‖ :=
          Matrix.l2_opNorm_mul _ _
      _ ≤ (‖gramResolvent K s‖ * ‖K' - K‖) * ‖K'ᵀ * gramResolvent K' s‖ := by
          gcongr; exact Matrix.l2_opNorm_mul _ _
      _ ≤ (1 / s * ‖K - K'‖) * (1 / (2 * Real.sqrt s)) := by
          rw [hKK]; gcongr
  have t2 : ‖gramResolvent K s * K * (K' - K)ᵀ * gramResolvent K' s‖ ≤
      1 / (2 * Real.sqrt s) * ‖K - K'‖ * (1 / s) := by
    calc _ ≤ ‖gramResolvent K s * K * (K' - K)ᵀ‖ * ‖gramResolvent K' s‖ :=
          Matrix.l2_opNorm_mul _ _
      _ ≤ (‖gramResolvent K s * K‖ * ‖(K' - K)ᵀ‖) * ‖gramResolvent K' s‖ := by
          gcongr; exact Matrix.l2_opNorm_mul _ _
      _ ≤ (1 / (2 * Real.sqrt s) * ‖K - K'‖) * (1 / s) := by
          rw [hKT]; gcongr; exact hX
  calc _ ≤ ‖gramResolvent K s * (K' - K) * (K'ᵀ * gramResolvent K' s)‖ +
        ‖gramResolvent K s * K * (K' - K)ᵀ * gramResolvent K' s‖ := norm_add_le _ _
    _ ≤ 1 / s * ‖K - K'‖ * (1 / (2 * Real.sqrt s)) +
        1 / (2 * Real.sqrt s) * ‖K - K'‖ * (1 / s) := add_le_add t1 t2
    _ = ‖K - K'‖ / (s * Real.sqrt s) := by field_simp; ring

/-- **`lem:app-de-lipschitz`**: `‖R_s(K) − R_s(K')‖_* ≤ 2 s^{-3/2} ‖K − K'‖_*` (Muon's exact shape).
Proof route: Muon `lem_app_de_lipschitz`: `gramResolvent_sub_gramResolvent`,
`nuclearNorm_add_le`, `nuclearNorm_mul_three_le` on both terms, `nuclearNorm_transpose`, the
operator-norm bounds above, and `nuclearNorm_smul` with `c = −1` for `K − K'` vs `K' − K`. -/
theorem nuclearNorm_gramResolvent_sub_le (K K' : Matrix m n ℝ) (s : ℝ) (hs : 0 < s) :
    nuclearNorm (gramResolvent K s - gramResolvent K' s) ≤
      2 / (s * Real.sqrt s) * nuclearNorm (K - K') := by
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hΔ : nuclearNorm (K - K') = nuclearNorm (K' - K) := by
    have h : K - K' = (-1 : ℝ) • (K' - K) := by rw [neg_one_smul, neg_sub]
    rw [h, nuclearNorm_smul]
    simp
  have hD : 0 ≤ nuclearNorm (K' - K) := nuclearNorm_nonneg _
  have hR := norm_gramResolvent_le K hs
  have hR' := norm_gramResolvent_le K' hs
  have hT := norm_transpose_mul_gramResolvent_le K' hs
  have hX : ‖gramResolvent K s * K‖ ≤ 1 / (2 * Real.sqrt s) := norm_mixedResolvent_le K hs
  have hs1 : 0 ≤ 1 / s := one_div_nonneg.mpr hs.le
  have hs2 : 0 ≤ 1 / (2 * Real.sqrt s) := by positivity
  have b1 : ‖gramResolvent K s‖ * nuclearNorm (K' - K) * ‖K'ᵀ * gramResolvent K' s‖ ≤
      1 / s * nuclearNorm (K' - K) * (1 / (2 * Real.sqrt s)) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hR hD) hT (norm_nonneg _) (mul_nonneg hs1 hD)
  have b2 : ‖gramResolvent K s * K‖ * nuclearNorm (K' - K)ᵀ * ‖gramResolvent K' s‖ ≤
      1 / (2 * Real.sqrt s) * nuclearNorm (K' - K) * (1 / s) := by
    rw [nuclearNorm_transpose]
    exact mul_le_mul (mul_le_mul_of_nonneg_right hX hD) hR' (norm_nonneg _) (mul_nonneg hs2 hD)
  have t1 := le_trans (nuclearNorm_mul_three_le (gramResolvent K s) (K' - K)
    (K'ᵀ * gramResolvent K' s)) b1
  have t2 := le_trans (nuclearNorm_mul_three_le (gramResolvent K s * K) (K' - K)ᵀ
    (gramResolvent K' s)) b2
  have hsum : 1 / s * nuclearNorm (K' - K) * (1 / (2 * Real.sqrt s)) +
      1 / (2 * Real.sqrt s) * nuclearNorm (K' - K) * (1 / s) =
      1 / (s * Real.sqrt s) * nuclearNorm (K' - K) := by
    field_simp
    ring
  have hcoef : 1 / (s * Real.sqrt s) ≤ 2 / (s * Real.sqrt s) := by
    apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
  calc nuclearNorm (gramResolvent K s - gramResolvent K' s)
      = nuclearNorm (gramResolvent K s * (K' - K) * (K'ᵀ * gramResolvent K' s) +
          gramResolvent K s * K * (K' - K)ᵀ * gramResolvent K' s) := by
        rw [gramResolvent_sub_gramResolvent K K' hs]
    _ ≤ nuclearNorm (gramResolvent K s * (K' - K) * (K'ᵀ * gramResolvent K' s)) +
        nuclearNorm (gramResolvent K s * K * (K' - K)ᵀ * gramResolvent K' s) :=
        nuclearNorm_add_le _ _
    _ ≤ 1 / s * nuclearNorm (K' - K) * (1 / (2 * Real.sqrt s)) +
        1 / (2 * Real.sqrt s) * nuclearNorm (K' - K) * (1 / s) := add_le_add t1 t2
    _ = 1 / (s * Real.sqrt s) * nuclearNorm (K' - K) := hsum
    _ ≤ 2 / (s * Real.sqrt s) * nuclearNorm (K' - K) := mul_le_mul_of_nonneg_right hcoef hD
    _ = 2 / (s * Real.sqrt s) * nuclearNorm (K - K') := by rw [hΔ]

end GramNorms

/-! ### Rank-one update of the rectangular matrix (`lem:app-de-deletion`) -/

/-- `𝖴 = uᵀ R_s(M₀) u` (Muon's `delU`). -/
def rankOneU (M₀ : Matrix m n ℝ) (u : m → ℝ) (s : ℝ) : ℝ :=
  dotProduct u (gramResolvent M₀ s *ᵥ u)

/-- `𝖵 = vᵀ R̃_s(M₀) v` (Muon's `delV`). -/
def rankOneV (M₀ : Matrix m n ℝ) (v : n → ℝ) (s : ℝ) : ℝ :=
  dotProduct v (gramResolventT M₀ s *ᵥ v)

/-- `𝖢 = uᵀ 𝖷_s(M₀) v` (Muon's `delC`). -/
def rankOneC (M₀ : Matrix m n ℝ) (u : m → ℝ) (v : n → ℝ) (s : ℝ) : ℝ :=
  dotProduct u (mixedResolvent M₀ s *ᵥ v)

/-- `Λ = (1 + 𝗁𝖢)² + s𝗁²𝖴𝖵` (Muon's `delLambda`). -/
def rankOneLambda (M₀ : Matrix m n ℝ) (h : ℝ) (u : m → ℝ) (v : n → ℝ) (s : ℝ) : ℝ :=
  (1 + h * rankOneC M₀ u v s) ^ 2 + s * h ^ 2 * rankOneU M₀ u s * rankOneV M₀ v s

/-- `α₁ = 𝗁(1 + 𝗁𝖢)/Λ` (Muon's `alpha1`). -/
def rankOneAlpha1 (M₀ : Matrix m n ℝ) (h : ℝ) (u : m → ℝ) (v : n → ℝ) (s : ℝ) : ℝ :=
  h * (1 + h * rankOneC M₀ u v s) / rankOneLambda M₀ h u v s

/-- `α₂ = 𝗁²𝖴/Λ` (Muon's `alpha2`). -/
def rankOneAlpha2 (M₀ : Matrix m n ℝ) (h : ℝ) (u : m → ℝ) (v : n → ℝ) (s : ℝ) : ℝ :=
  h ^ 2 * rankOneU M₀ u s / rankOneLambda M₀ h u v s

/-- `α₃ = −s𝗁²𝖵/Λ` (Muon's `alpha3`). -/
def rankOneAlpha3 (M₀ : Matrix m n ℝ) (h : ℝ) (u : m → ℝ) (v : n → ℝ) (s : ℝ) : ℝ :=
  -(s * h ^ 2 * rankOneV M₀ v s) / rankOneLambda M₀ h u v s

section DeletionHelpers

open scoped Matrix.Norms.L2Operator

/-- Two-column matrix `[a | b]`. -/
private abbrev dlP (a b : m → ℝ) : Matrix m (Fin 2) ℝ :=
  Matrix.of fun i (j : Fin 2) => ![a i, b i] j

private lemma dl_dlP_mulVec (a b : m → ℝ) (x : Fin 2 → ℝ) :
    dlP a b *ᵥ x = x 0 • a + x 1 • b := by
  ext i
  simp [dlP, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

private lemma dl_quad (a b : m → ℝ) (θ00 θ01 θ10 θ11 : ℝ) :
    dlP a b * !![θ00, θ01; θ10, θ11] * (dlP a b)ᵀ =
      θ00 • vecMulVec a a + θ01 • vecMulVec a b + θ10 • vecMulVec b a + θ11 • vecMulVec b b := by
  ext i j
  simp [dlP, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
    Matrix.vecMulVec_apply] <;> ring

private lemma dl_det_add (G0 R0 : Matrix m m ℝ) (hR : G0 * R0 = 1)
    (P : Matrix m (Fin 2) ℝ) (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    (G0 + P * Q * Pᵀ).det = G0.det * (1 + Q * (Pᵀ * R0 * P)).det := by
  have hG : G0 + P * Q * Pᵀ = G0 * (1 + R0 * P * Q * Pᵀ) := by
    simp only [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hR, Matrix.one_mul]
  rw [hG, Matrix.det_mul]
  congr 1
  have h1 : R0 * P * Q * Pᵀ = (R0 * P) * (Q * Pᵀ) := by simp only [Matrix.mul_assoc]
  have h2 : Q * Pᵀ * (R0 * P) = Q * (Pᵀ * R0 * P) := by simp only [Matrix.mul_assoc]
  rw [h1, Matrix.det_one_add_mul_comm, h2]

private lemma dl_inv (G0 R0 : Matrix m m ℝ) (hR : G0 * R0 = 1)
    (P : Matrix m (Fin 2) ℝ) (Q T : Matrix (Fin 2) (Fin 2) ℝ)
    (hT : (1 + Q * (Pᵀ * R0 * P)) * T = Q) :
    (G0 + P * Q * Pᵀ)⁻¹ = R0 - R0 * P * T * Pᵀ * R0 := by
  refine Matrix.inv_eq_right_inv ?_
  have hT' : T + Q * (Pᵀ * R0 * P) * T = Q := by
    have h := hT
    rw [Matrix.add_mul, Matrix.one_mul] at h
    exact h
  have key : Q - T - Q * (Pᵀ * R0 * P) * T = 0 := by
    calc Q - T - Q * (Pᵀ * R0 * P) * T = (T + Q * (Pᵀ * R0 * P) * T) - T
          - Q * (Pᵀ * R0 * P) * T := by rw [hT']
      _ = 0 := by abel
  have hz : P * (Q - T - Q * (Pᵀ * R0 * P) * T) * Pᵀ * R0 = 0 := by
    rw [key]; simp
  have hexp : P * (Q - T - Q * (Pᵀ * R0 * P) * T) * Pᵀ * R0
      = P * Q * Pᵀ * R0 - P * T * Pᵀ * R0 - P * Q * Pᵀ * R0 * P * T * Pᵀ * R0 := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  have hGX : G0 * (R0 - R0 * P * T * Pᵀ * R0) = 1 - P * T * Pᵀ * R0 := by
    rw [Matrix.mul_sub, show G0 * (R0 * P * T * Pᵀ * R0) = (G0 * R0) * (P * T * Pᵀ * R0) by
      simp only [Matrix.mul_assoc], hR, Matrix.one_mul]
  have hPX : P * Q * Pᵀ * (R0 - R0 * P * T * Pᵀ * R0)
      = P * Q * Pᵀ * R0 - P * Q * Pᵀ * R0 * P * T * Pᵀ * R0 := by
    simp only [Matrix.mul_sub, Matrix.mul_assoc]
  rw [Matrix.add_mul, hGX, hPX]
  have hfin : (1 - P * T * Pᵀ * R0) + (P * Q * Pᵀ * R0 - P * Q * Pᵀ * R0 * P * T * Pᵀ * R0)
      = 1 + P * (Q - T - Q * (Pᵀ * R0 * P) * T) * Pᵀ * R0 := by
    rw [hexp]; abel
  rw [hfin, hz, add_zero]

private lemma dl_sand (R0 : Matrix m m ℝ) (P : Matrix m (Fin 2) ℝ)
    (Θ : Matrix (Fin 2) (Fin 2) ℝ) (hsym : R0ᵀ = R0) :
    R0 * P * Θ * Pᵀ * R0 = (R0 * P) * Θ * (R0 * P)ᵀ := by
  rw [Matrix.transpose_mul, hsym]
  simp only [Matrix.mul_assoc]

private lemma dl_RP (R0 : Matrix m m ℝ) (a b : m → ℝ) :
    R0 * dlP a b = dlP (R0 *ᵥ a) (R0 *ᵥ b) := by
  ext i j
  fin_cases j <;> simp [dlP, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private lemma dl_apply (R0 : Matrix m m ℝ) (P : Matrix m (Fin 2) ℝ)
    (Θ : Matrix (Fin 2) (Fin 2) ℝ) (c : Fin 2 → ℝ) :
    (R0 - R0 * P * Θ * Pᵀ * R0) *ᵥ (P *ᵥ c)
      = R0 *ᵥ (P *ᵥ (c - Θ *ᵥ (Pᵀ *ᵥ (R0 *ᵥ (P *ᵥ c))))) := by
  rw [Matrix.sub_mulVec]
  simp only [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mul_assoc]

private lemma dl_det_pos (K : Matrix m n ℝ) (s : ℝ) (hs : 0 < s) :
    0 < (K * Kᵀ + s • (1 : Matrix m m ℝ)).det := by
  have h1 : (K * Kᵀ).PosSemidef := by
    have h := Matrix.posSemidef_self_mul_conjTranspose K
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have h2 : (s • (1 : Matrix m m ℝ)).PosDef := Matrix.PosDef.one.smul hs
  rw [add_comm]
  exact (Matrix.PosDef.add_posSemidef h2 h1).det_pos

/-- Rank-two decomposition of the Gram matrix `M Mᵀ + s` for `M = M₀ + h u vᵀ`. -/
private lemma dl_G (M₀ : Matrix m n ℝ) (h s : ℝ) (u : m → ℝ) (v : n → ℝ) :
    (M₀ + h • vecMulVec u v) * (M₀ + h • vecMulVec u v)ᵀ + s • (1 : Matrix m m ℝ) =
      (M₀ * M₀ᵀ + s • (1 : Matrix m m ℝ)) +
        dlP u (M₀ *ᵥ v) * !![h ^ 2 * sqNorm' v, h; h, 0] * (dlP u (M₀ *ᵥ v))ᵀ := by
  have hA : ∀ i j : m, ∑ x, (M₀ i x + h * (u i * v x)) * (M₀ j x + h * (u j * v x)) =
      ∑ x, M₀ i x * M₀ j x + (h * u j * ∑ x, M₀ i x * v x + h * u i * ∑ x, M₀ j x * v x
        + h ^ 2 * u i * u j * ∑ x, v x ^ 2) := by
    intro i j
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  ext i j
  simp only [dlP, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.of_apply, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply,
    Matrix.one_apply, Fin.sum_univ_two, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.add_apply, Matrix.smul_apply]
  rw [hA i j]
  simp only [sqNorm']
  ring

/-- Symmetry of the output resolvent. -/
private lemma dl_Rs_symm (M : Matrix m n ℝ) (s : ℝ) : (gramResolvent M s)ᵀ = gramResolvent M s := by
  unfold gramResolvent negResolvent
  rw [Matrix.transpose_nonsing_inv]
  congr 1
  simp [Matrix.transpose_add, Matrix.transpose_mul, add_comm]

private lemma dl_cross (R0 : Matrix m m ℝ) (hsym : R0ᵀ = R0) (a b : m → ℝ) :
    b ⬝ᵥ (R0 *ᵥ a) = a ⬝ᵥ (R0 *ᵥ b) := by
  rw [Matrix.dotProduct_mulVec, gr_vecMul, hsym, dotProduct_comm]

private lemma dl_gen (R0 : Matrix m m ℝ) (A : Matrix m (Fin 2) ℝ) (i j : Fin 2) :
    (Aᵀ * R0 * A) i j = (fun k => A k i) ⬝ᵥ (R0 *ᵥ fun k => A k j) := by
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

private lemma dl_W (R0 : Matrix m m ℝ) (hsym : R0ᵀ = R0) (a b : m → ℝ) :
    (dlP a b)ᵀ * R0 * dlP a b =
      !![a ⬝ᵥ (R0 *ᵥ a), a ⬝ᵥ (R0 *ᵥ b); a ⬝ᵥ (R0 *ᵥ b), b ⬝ᵥ (R0 *ᵥ b)] := by
  have hc := dl_cross R0 hsym a b
  have ca : (fun k => dlP a b k 0) = a := by funext k; simp [dlP]
  have cb : (fun k => dlP a b k 1) = b := by funext k; simp [dlP]
  ext i j
  rw [dl_gen]
  fin_cases i <;> fin_cases j <;> simp [ca, cb, hc]

private lemma dl_W11 (M₀ : Matrix m n ℝ) (s : ℝ) (hs : 0 < s) (v : n → ℝ) :
    (M₀ *ᵥ v) ⬝ᵥ (gramResolvent M₀ s *ᵥ (M₀ *ᵥ v)) = sqNorm' v - s * rankOneV M₀ v s := by
  have hid : M₀ᵀ * gramResolvent M₀ s * M₀ = 1 - s • gramResolventT M₀ s := transpose_mul_gramResolvent_mul M₀ hs
  have hvv : v ⬝ᵥ v = sqNorm' v := by simp [sqNorm', dotProduct, sq]
  rw [dotProduct_comm, gr_dot_mulVec,
    show M₀ᵀ *ᵥ (gramResolvent M₀ s *ᵥ (M₀ *ᵥ v)) = (M₀ᵀ * gramResolvent M₀ s * M₀) *ᵥ v by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc], hid, Matrix.sub_mulVec,
    Matrix.one_mulVec, Matrix.smul_mulVec, sub_dotProduct, smul_dotProduct, hvv]
  rw [dotProduct_comm (gramResolventT M₀ s *ᵥ v) v]
  rfl

private lemma dl_scal (h s U C V N L α1 α2 α3 : ℝ) (hL : L ≠ 0)
    (hLdef : L = (1 + h * C) ^ 2 + s * h ^ 2 * U * V)
    (hα1 : α1 = h * (1 + h * C) / L) (hα2 : α2 = h ^ 2 * U / L)
    (hα3 : α3 = -(s * h ^ 2 * V) / L) :
    (1 + !![h ^ 2 * N, h; h, 0] * !![U, C; C, N - s * V]) *
      !![-α3, α1; α1, -α2] = !![h ^ 2 * N, h; h, 0] := by
  subst hα1 hα2 hα3
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    (subst hLdef; ring)

private lemma dl_vec (h s U C V N L α1 α2 α3 : ℝ) (hL : L ≠ 0)
    (hLdef : L = (1 + h * C) ^ 2 + s * h ^ 2 * U * V)
    (hα1 : α1 = h * (1 + h * C) / L) (hα2 : α2 = h ^ 2 * U / L)
    (hα3 : α3 = -(s * h ^ 2 * V) / L) :
    h • (![h * N, 1] - !![-α3, α1; α1, -α2] *ᵥ (!![U, C; C, N - s * V] *ᵥ ![h * N, 1])) =
      ![-α3, α1] := by
  subst hα1 hα2 hα3
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> field_simp <;>
    (subst hLdef; ring)

private lemma dl_det_rel (M₀ : Matrix m n ℝ) (h : ℝ) (u : m → ℝ) (v : n → ℝ)
    (M : Matrix m n ℝ) (s : ℝ) (hM : M = M₀ + h • vecMulVec u v) (hs : 0 < s) :
    (M * Mᵀ + s • (1 : Matrix m m ℝ)).det =
      (M₀ * M₀ᵀ + s • (1 : Matrix m m ℝ)).det * rankOneLambda M₀ h u v s := by
  subst hM
  have hG0 : (M₀ * M₀ᵀ + s • (1 : Matrix m m ℝ)) * gramResolvent M₀ s = 1 :=
    Matrix.mul_nonsing_inv _ (gr_isUnit M₀ hs)
  have hsym := dl_Rs_symm M₀ s
  have hU : u ⬝ᵥ (gramResolvent M₀ s *ᵥ u) = rankOneU M₀ u s := rfl
  have hC : u ⬝ᵥ (gramResolvent M₀ s *ᵥ (M₀ *ᵥ v)) = rankOneC M₀ u v s := by
    unfold rankOneC mixedResolvent; rw [Matrix.mulVec_mulVec]
  rw [dl_G M₀ h s u v, dl_det_add _ _ hG0, dl_W _ hsym, hU, hC, dl_W11 M₀ s hs v]
  congr 1
  rw [Matrix.det_fin_two]
  simp [rankOneLambda, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private lemma dl_Lam_pos (M₀ : Matrix m n ℝ) (h : ℝ) (u : m → ℝ) (v : n → ℝ)
    (M : Matrix m n ℝ) (s : ℝ) (hM : M = M₀ + h • vecMulVec u v) (hs : 0 < s) :
    0 < rankOneLambda M₀ h u v s := by
  have h1 := dl_det_rel M₀ h u v M s hM hs
  have h2 := dl_det_pos M s hs
  have h3 := dl_det_pos M₀ s hs
  have h4 : 0 < (M₀ * M₀ᵀ + s • (1 : Matrix m m ℝ)).det * rankOneLambda M₀ h u v s := by
    rw [← h1]; exact h2
  exact pos_of_mul_pos_right h4 h3.le

/-- Bounds on `𝖴 = uᵀ R_s(M) u`. -/
private lemma dl_U (M : Matrix m n ℝ) (u : m → ℝ) (s : ℝ) (hs : 0 < s) :
    0 ≤ rankOneU M u s ∧ s * rankOneU M u s ≤ sqNorm' u := by
  have hy : (M * Mᵀ + s • (1 : Matrix m m ℝ)) *ᵥ (gramResolvent M s *ᵥ u) = u :=
    gr_mulVec_inv M s hs u
  have hquad : (gramResolvent M s *ᵥ u) ⬝ᵥ u = sqNorm' (Mᵀ *ᵥ (gramResolvent M s *ᵥ u)) + s * sqNorm' (gramResolvent M s *ᵥ u) := by
    have := gr_quad M s (gramResolvent M s *ᵥ u)
    rwa [hy] at this
  have hU : rankOneU M u s = (gramResolvent M s *ᵥ u) ⬝ᵥ u := by
    unfold rankOneU; rw [dotProduct_comm]
  have hcs : ((gramResolvent M s *ᵥ u) ⬝ᵥ u) ^ 2 ≤ sqNorm' u * sqNorm' (gramResolvent M s *ᵥ u) := by
    rw [dotProduct_comm]; exact gr_cs u (gramResolvent M s *ᵥ u)
  have hb : s ^ 2 * sqNorm' (gramResolvent M s *ᵥ u) ≤ sqNorm' u := gr_bound_R M s hs u
  have hnn1 := gr_sqNorm_nonneg (Mᵀ *ᵥ (gramResolvent M s *ᵥ u))
  have hnn2 := gr_sqNorm_nonneg (gramResolvent M s *ᵥ u)
  have hnnu := gr_sqNorm_nonneg u
  rw [hU]
  have hU0 : 0 ≤ (gramResolvent M s *ᵥ u) ⬝ᵥ u := by
    rw [hquad]; exact add_nonneg hnn1 (mul_nonneg hs.le hnn2)
  refine ⟨hU0, ?_⟩
  have h1 : (s * ((gramResolvent M s *ᵥ u) ⬝ᵥ u)) ^ 2 ≤ s ^ 2 * (sqNorm' u * sqNorm' (gramResolvent M s *ᵥ u)) := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left hcs (sq_nonneg s)
  have h2 : sqNorm' u * (s ^ 2 * sqNorm' (gramResolvent M s *ᵥ u)) ≤ sqNorm' u * sqNorm' u :=
    mul_le_mul_of_nonneg_left hb hnnu
  have key : (s * ((gramResolvent M s *ᵥ u) ⬝ᵥ u)) ^ 2 ≤ sqNorm' u ^ 2 := by nlinarith
  nlinarith [key, hnnu, hU0, mul_nonneg hs.le hU0]

/-- Bounds on `𝖵 = vᵀ R̃_s(M) v`. -/
private lemma dl_V (M : Matrix m n ℝ) (v : n → ℝ) (s : ℝ) (hs : 0 < s) :
    0 ≤ rankOneV M v s ∧ s * rankOneV M v s ≤ sqNorm' v := by
  have hVU : rankOneV M v s = rankOneU Mᵀ v s := by
    unfold rankOneV rankOneU gramResolventT gramResolvent negResolvent; rw [Matrix.transpose_transpose]
  rw [hVU]
  exact dl_U Mᵀ v s hs

/-- Bound on the cross term `𝖢 = uᵀ 𝖷_s(M) v`. -/
private lemma dl_C (M : Matrix m n ℝ) (u : m → ℝ) (v : n → ℝ) (s : ℝ) (hs : 0 < s) :
    4 * s * rankOneC M u v s ^ 2 ≤ sqNorm' u * sqNorm' v := by
  have hX : mixedResolvent M s *ᵥ v = gramResolvent M s *ᵥ (M *ᵥ v) := by
    unfold mixedResolvent; rw [Matrix.mulVec_mulVec]
  have hC : rankOneC M u v s = u ⬝ᵥ (gramResolvent M s *ᵥ (M *ᵥ v)) := by
    unfold rankOneC; rw [hX]
  have hcs : (u ⬝ᵥ (gramResolvent M s *ᵥ (M *ᵥ v))) ^ 2 ≤ sqNorm' u * sqNorm' (gramResolvent M s *ᵥ (M *ᵥ v)) :=
    gr_cs u (gramResolvent M s *ᵥ (M *ᵥ v))
  have hb : 4 * s * sqNorm' (gramResolvent M s *ᵥ (M *ᵥ v)) ≤ sqNorm' v := gr_bound_X M s hs v
  have hnnu := gr_sqNorm_nonneg u
  rw [hC]
  have h1 := mul_le_mul_of_nonneg_left hcs (by positivity : (0:ℝ) ≤ 4 * s)
  have h2 := mul_le_mul_of_nonneg_left hb hnnu
  nlinarith

/-- Pure real bound behind `Λ' ≤ (1 + 3/(4√s) |h| N)²`. -/
private lemma dl_bound (h s Nu Nv U V C : ℝ) (hs : 0 < s) (hNu : 0 ≤ Nu) (hNv : 0 ≤ Nv)
    (hU0 : 0 ≤ U) (hU : s * U ≤ Nu) (hV0 : 0 ≤ V) (hV : s * V ≤ Nv)
    (hC : 4 * s * C ^ 2 ≤ Nu * Nv) :
    (1 + -h * C) ^ 2 + s * (-h) ^ 2 * U * V
      ≤ (1 + 3 / (4 * Real.sqrt s) * |h| * (Nu + Nv)) ^ 2 := by
  have hσ : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have hσpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  set σ := Real.sqrt s with hσdef
  set t := |h| * (Nu + Nv) / (4 * σ) with htdef
  have ht0 : 0 ≤ t := by positivity
  have e3 : 3 / (4 * σ) * |h| * (Nu + Nv) = 3 * t := by rw [htdef]; ring
  rw [e3]
  have htσ : t * (4 * σ) = |h| * (Nu + Nv) := div_mul_cancel₀ _ (by positivity)
  have hsq : (4 * σ * |h * C|) ^ 2 ≤ (|h| * (Nu + Nv)) ^ 2 := by
    have habs : |h * C| ^ 2 = (h * C) ^ 2 := sq_abs _
    have habs2 : |h| ^ 2 = h ^ 2 := sq_abs _
    have e1 : (4 * σ * |h * C|) ^ 2 = 16 * s * (h * C) ^ 2 := by
      calc (4 * σ * |h * C|) ^ 2 = 16 * σ ^ 2 * |h * C| ^ 2 := by ring
        _ = 16 * s * (h * C) ^ 2 := by rw [hσ, habs]
    have e2 : (|h| * (Nu + Nv)) ^ 2 = h ^ 2 * (Nu + Nv) ^ 2 := by rw [mul_pow, habs2]
    rw [e1, e2]
    have h3 := mul_le_mul_of_nonneg_left hC (sq_nonneg h)
    nlinarith [sq_nonneg (Nu - Nv), sq_nonneg h]
  have hA0 : 0 ≤ 4 * σ * |h * C| := by positivity
  have hB0 : 0 ≤ |h| * (Nu + Nv) := by positivity
  have hle : 4 * σ * |h * C| ≤ |h| * (Nu + Nv) := by nlinarith [hsq, hA0, hB0]
  have hCt : |h * C| ≤ t := by nlinarith [htσ, hle]
  have hbnd := abs_le.mp hCt
  have hpart1 : (1 + -h * C) ^ 2 ≤ (1 + t) ^ 2 := by
    have hh : -h * C = -(h * C) := by ring
    rw [hh]
    nlinarith [hbnd.1, hbnd.2]
  have ht2 : t ^ 2 * (16 * s) = h ^ 2 * (Nu + Nv) ^ 2 := by
    calc t ^ 2 * (16 * s) = (t * (4 * σ)) ^ 2 := by rw [← hσ]; ring
      _ = (|h| * (Nu + Nv)) ^ 2 := by rw [htσ]
      _ = h ^ 2 * (Nu + Nv) ^ 2 := by rw [mul_pow, sq_abs]
  have hUV : (s * U) * (s * V) ≤ Nu * Nv := mul_le_mul hU hV (mul_nonneg hs.le hV0) hNu
  have hpart2 : s * (-h) ^ 2 * U * V ≤ 4 * t ^ 2 := by
    have hk : (s * (-h) ^ 2 * U * V) * (4 * s) ≤ (4 * t ^ 2) * (4 * s) := by
      have e4 : (4 * t ^ 2) * (4 * s) = h ^ 2 * (Nu + Nv) ^ 2 := by nlinarith [ht2]
      rw [e4]
      have e5 : (s * (-h) ^ 2 * U * V) * (4 * s) = 4 * h ^ 2 * ((s * U) * (s * V)) := by
        rw [neg_sq]; ring
      rw [e5]
      have h5 := mul_le_mul_of_nonneg_left hUV (by positivity : (0:ℝ) ≤ 4 * h ^ 2)
      nlinarith [sq_nonneg (Nu - Nv), sq_nonneg h]
    exact le_of_mul_le_mul_right hk (by positivity)
  nlinarith [hpart1, hpart2, ht0]



end DeletionHelpers

/-- **`lem:app-de-deletion`** (rank-one update of `M`, a rank-two update of `MMᵀ`), in Muon's exact
shape: `Λ > 0`, the four-term formula for `R − R₀`, the formula for `𝗁 R M v`, `ΛΛ' = 1`, and
`Λ⁻¹ ≤ (1 + 3|𝗁|N/(4√s))²` with `N = ‖u‖² + ‖v‖²`.
Proof route: port Muon `lem_app_de_deletion` (l.664) and its `dlAux_*` helpers: write
`MMᵀ + s = (M₀M₀ᵀ + s) + P Θ Pᵀ` with the two-column `P = [u | M₀v]` and
`Θ = [[𝗁²‖v‖², 𝗁], [𝗁, 0]]` (`dlAux_G`), apply Woodbury (`Matrix.add_mul_mul_inv_eq_sub`), compute
the `2 × 2` inverse explicitly (`dlAux_scal`), and get `ΛΛ' = 1` from the determinant lemma
(`det_add_mul`) applied in both directions (`dlAux_det_rel`). -/
theorem gramResolvent_rankOne_update (M₀ : Matrix m n ℝ) (h : ℝ) (u : m → ℝ) (v : n → ℝ)
    (M : Matrix m n ℝ) (s : ℝ) (hM : M = M₀ + h • vecMulVec u v) (hs : 0 < s) :
    0 < rankOneLambda M₀ h u v s ∧
    gramResolvent M s - gramResolvent M₀ s =
      (rankOneAlpha3 M₀ h u v s) • vecMulVec (gramResolvent M₀ s *ᵥ u) (gramResolvent M₀ s *ᵥ u)
        - (rankOneAlpha1 M₀ h u v s) •
            vecMulVec (gramResolvent M₀ s *ᵥ u) (mixedResolvent M₀ s *ᵥ v)
        - (rankOneAlpha1 M₀ h u v s) •
            vecMulVec (mixedResolvent M₀ s *ᵥ v) (gramResolvent M₀ s *ᵥ u)
        + (rankOneAlpha2 M₀ h u v s) •
            vecMulVec (mixedResolvent M₀ s *ᵥ v) (mixedResolvent M₀ s *ᵥ v) ∧
    h • (gramResolvent M s *ᵥ (M *ᵥ v)) =
      (-rankOneAlpha3 M₀ h u v s) • (gramResolvent M₀ s *ᵥ u) +
        (rankOneAlpha1 M₀ h u v s) • (mixedResolvent M₀ s *ᵥ v) ∧
    rankOneLambda M₀ h u v s * rankOneLambda M (-h) u v s = 1 ∧
    (rankOneLambda M₀ h u v s)⁻¹ ≤
      (1 + 3 / (4 * Real.sqrt s) * |h| * ((∑ i, u i ^ 2) + (∑ j, v j ^ 2))) ^ 2 := by
  have hsym := dl_Rs_symm M₀ s
  have hG0 : (M₀ * M₀ᵀ + s • (1 : Matrix m m ℝ)) * gramResolvent M₀ s = 1 :=
    Matrix.mul_nonsing_inv _ (gr_isUnit M₀ hs)
  have hdet0 : 0 < (M₀ * M₀ᵀ + s • (1 : Matrix m m ℝ)).det := dl_det_pos M₀ s hs
  have hL : 0 < rankOneLambda M₀ h u v s := dl_Lam_pos M₀ h u v M s hM hs
  have hLne : rankOneLambda M₀ h u v s ≠ 0 := hL.ne'
  have hrel1 := dl_det_rel M₀ h u v M s hM hs
  have hM' : M₀ = M + (-h) • vecMulVec u v := by rw [hM]; module
  have hrel2 := dl_det_rel M (-h) u v M₀ s hM' hs
  have hGM : M * Mᵀ + s • (1 : Matrix m m ℝ) =
      (M₀ * M₀ᵀ + s • (1 : Matrix m m ℝ)) +
        dlP u (M₀ *ᵥ v) * !![h ^ 2 * sqNorm' v, h; h, 0] * (dlP u (M₀ *ᵥ v))ᵀ := by
    rw [hM]; exact dl_G M₀ h s u v
  have hU : u ⬝ᵥ (gramResolvent M₀ s *ᵥ u) = rankOneU M₀ u s := rfl
  have hC : u ⬝ᵥ (gramResolvent M₀ s *ᵥ (M₀ *ᵥ v)) = rankOneC M₀ u v s := by
    unfold rankOneC mixedResolvent; rw [Matrix.mulVec_mulVec]
  have hXv : mixedResolvent M₀ s *ᵥ v = gramResolvent M₀ s *ᵥ (M₀ *ᵥ v) := by
    unfold mixedResolvent; rw [Matrix.mulVec_mulVec]
  have hT : (1 + !![h ^ 2 * sqNorm' v, h; h, 0] *
      ((dlP u (M₀ *ᵥ v))ᵀ * gramResolvent M₀ s * dlP u (M₀ *ᵥ v))) *
      !![-rankOneAlpha3 M₀ h u v s, rankOneAlpha1 M₀ h u v s; rankOneAlpha1 M₀ h u v s, -rankOneAlpha2 M₀ h u v s] =
      !![h ^ 2 * sqNorm' v, h; h, 0] := by
    rw [dl_W _ hsym, hU, hC, dl_W11 M₀ s hs v]
    exact dl_scal h s (rankOneU M₀ u s) (rankOneC M₀ u v s) (rankOneV M₀ v s) (sqNorm' v)
      (rankOneLambda M₀ h u v s) (rankOneAlpha1 M₀ h u v s) (rankOneAlpha2 M₀ h u v s) (rankOneAlpha3 M₀ h u v s)
      hLne rfl rfl rfl rfl
  have hdecomp : gramResolvent M s = gramResolvent M₀ s - gramResolvent M₀ s * dlP u (M₀ *ᵥ v) *
      !![-rankOneAlpha3 M₀ h u v s, rankOneAlpha1 M₀ h u v s; rankOneAlpha1 M₀ h u v s, -rankOneAlpha2 M₀ h u v s] *
      (dlP u (M₀ *ᵥ v))ᵀ * gramResolvent M₀ s := by
    show (M * Mᵀ + s • (1 : Matrix m m ℝ))⁻¹ = _
    rw [hGM]
    exact dl_inv _ _ hG0 _ _ _ hT
  have hdec2 : gramResolvent M s = gramResolvent M₀ s - (gramResolvent M₀ s * dlP u (M₀ *ᵥ v)) *
      !![-rankOneAlpha3 M₀ h u v s, rankOneAlpha1 M₀ h u v s; rankOneAlpha1 M₀ h u v s, -rankOneAlpha2 M₀ h u v s] *
      (gramResolvent M₀ s * dlP u (M₀ *ᵥ v))ᵀ := by
    rw [hdecomp, dl_sand _ _ _ hsym]
  have conj2 : gramResolvent M s - gramResolvent M₀ s =
      (rankOneAlpha3 M₀ h u v s) • vecMulVec (gramResolvent M₀ s *ᵥ u) (gramResolvent M₀ s *ᵥ u)
        - (rankOneAlpha1 M₀ h u v s) • vecMulVec (gramResolvent M₀ s *ᵥ u) (mixedResolvent M₀ s *ᵥ v)
        - (rankOneAlpha1 M₀ h u v s) • vecMulVec (mixedResolvent M₀ s *ᵥ v) (gramResolvent M₀ s *ᵥ u)
        + (rankOneAlpha2 M₀ h u v s) • vecMulVec (mixedResolvent M₀ s *ᵥ v) (mixedResolvent M₀ s *ᵥ v) := by
    rw [hdec2, dl_RP, dl_quad, hXv]
    module
  have hB : ∀ i, ∑ x, (M₀ i x + h * (u i * v x)) * v x =
      ∑ x, M₀ i x * v x + h * u i * sqNorm' v := by
    intro i
    simp only [sqNorm', Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hMv : M *ᵥ v = dlP u (M₀ *ᵥ v) *ᵥ ![h * sqNorm' v, 1] := by
    rw [dl_dlP_mulVec]
    ext i
    simp only [hM, Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, smul_eq_mul, Pi.add_apply, Pi.smul_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [hB i]
    ring
  have hv := dl_vec h s (rankOneU M₀ u s) (rankOneC M₀ u v s) (rankOneV M₀ v s) (sqNorm' v)
    (rankOneLambda M₀ h u v s) (rankOneAlpha1 M₀ h u v s) (rankOneAlpha2 M₀ h u v s) (rankOneAlpha3 M₀ h u v s)
    hLne rfl rfl rfl rfl
  have conj3 : h • (gramResolvent M s *ᵥ (M *ᵥ v)) =
      (-rankOneAlpha3 M₀ h u v s) • (gramResolvent M₀ s *ᵥ u) + (rankOneAlpha1 M₀ h u v s) • (mixedResolvent M₀ s *ᵥ v) := by
    have hWc : (dlP u (M₀ *ᵥ v))ᵀ *ᵥ (gramResolvent M₀ s *ᵥ (dlP u (M₀ *ᵥ v) *ᵥ ![h * sqNorm' v, 1]))
        = ((dlP u (M₀ *ᵥ v))ᵀ * gramResolvent M₀ s * dlP u (M₀ *ᵥ v)) *ᵥ ![h * sqNorm' v, 1] := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [hdecomp, hMv, dl_apply, hWc, dl_W _ hsym, hU, hC, dl_W11 M₀ s hs v]
    rw [← Matrix.mulVec_smul (gramResolvent M₀ s) h, ← Matrix.mulVec_smul (dlP u (M₀ *ᵥ v)) h, hv,
      dl_dlP_mulVec]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.mulVec_add,
      Matrix.mulVec_smul, hXv]
  have hprod : rankOneLambda M₀ h u v s * rankOneLambda M (-h) u v s = 1 := by
    apply mul_left_cancel₀ hdet0.ne'
    rw [mul_one]
    calc (M₀ * M₀ᵀ + s • (1 : Matrix m m ℝ)).det * (rankOneLambda M₀ h u v s * rankOneLambda M (-h) u v s)
        = ((M₀ * M₀ᵀ + s • (1 : Matrix m m ℝ)).det * rankOneLambda M₀ h u v s) *
            rankOneLambda M (-h) u v s := by ring
      _ = (M * Mᵀ + s • (1 : Matrix m m ℝ)).det * rankOneLambda M (-h) u v s := by rw [← hrel1]
      _ = (M₀ * M₀ᵀ + s • (1 : Matrix m m ℝ)).det := hrel2.symm
  have conj4 : (rankOneLambda M₀ h u v s)⁻¹ ≤
      (1 + 3 / (4 * Real.sqrt s) * |h| * (sqNorm' u + sqNorm' v)) ^ 2 := by
    rw [inv_eq_of_mul_eq_one_right hprod]
    obtain ⟨hU0, hU⟩ := dl_U M u s hs
    obtain ⟨hV0, hV⟩ := dl_V M v s hs
    exact dl_bound h s (sqNorm' u) (sqNorm' v) (rankOneU M u s) (rankOneV M v s) (rankOneC M u v s) hs
      (gr_sqNorm_nonneg u) (gr_sqNorm_nonneg v) hU0 hU hV0 hV (dl_C M u v s hs)
  exact ⟨hL, conj2, conj3, hprod, conj4⟩

end Gram


/-! ## Appended: trace of `cfc` bounds -/

section TraceCfc

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- `re tr f(A) = ∑ₖ f(λₖ)` for Hermitian `A` and any `f : ℝ → ℝ`. -/
theorem re_trace_cfc_eq_sum {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    RCLike.re (trace (cfc f A)) = ∑ k, f (sortedEig A k) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  have hU : star (hA.eigenvectorUnitary : Matrix n n 𝕜) *
      (hA.eigenvectorUnitary : Matrix n n 𝕜) = 1 := Unitary.coe_star_mul_self _
  rw [hU, Matrix.one_mul, Matrix.trace_diagonal, map_sum, sum_sortedEig_comp hA f]
  simp only [Function.comp_apply, RCLike.ofReal_re]

/-- If `|f(λₖ)| ≤ C` at every sorted eigenvalue of Hermitian `A`, then
`|re tr f(A)| ≤ card n * C`. -/
theorem abs_re_trace_cfc_le {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) {C : ℝ}
    (hC : ∀ k, |f (sortedEig A k)| ≤ C) :
    |RCLike.re (trace (cfc f A))| ≤ Fintype.card n * C := by
  rw [re_trace_cfc_eq_sum hA]
  calc |∑ k, f (sortedEig A k)| ≤ ∑ k, |f (sortedEig A k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin (Fintype.card n), C := Finset.sum_le_sum fun k _ => hC k
    _ = Fintype.card n * C := by simp

end TraceCfc


/-! ## Appended: smoothness of the Gram resolvent trace -/

section ContDiffGram

section L2
open scoped Matrix.Norms.L2Operator

/-- Matrix multiplication is a bounded bilinear map (rectangular `ℓ²` operator norms). -/
theorem isBoundedBilinearMap_matrix_mul {p q r : Type*} [Fintype p] [Fintype q] [Fintype r]
    [DecidableEq p] [DecidableEq q] [DecidableEq r] :
    IsBoundedBilinearMap ℝ (fun x : Matrix p q ℝ × Matrix q r ℝ => x.1 * x.2) where
  add_left := fun _ _ _ => Matrix.add_mul _ _ _
  smul_left := fun _ _ _ => Matrix.smul_mul _ _ _
  add_right := fun _ _ _ => Matrix.mul_add _ _ _
  smul_right := fun _ _ _ => Matrix.mul_smul _ _ _
  bound := ⟨1, one_pos, fun x y => by simpa using Matrix.l2_opNorm_mul x y⟩

/-- `X ↦ X Xᵀ + t • 1` is smooth (polynomial), for the `ℓ²` operator norm. -/
theorem contDiff_gram_add {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (t : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun X : Matrix p q ℝ => X * Xᵀ + t • (1 : Matrix p p ℝ)) := by
  have hT : ContDiff ℝ k (fun X : Matrix p q ℝ => Xᵀ) := by
    let L : Matrix p q ℝ →L[ℝ] Matrix q p ℝ :=
      LinearMap.toContinuousLinearMap (Matrix.transposeLinearEquiv p q ℝ ℝ).toLinearMap
    exact L.contDiff
  have hB := (isBoundedBilinearMap_matrix_mul (p := p) (q := q) (r := p)).contDiff (n := k)
  exact (hB.comp (contDiff_id.prodMk hT)).add contDiff_const

/-- **Smoothness of the Gram resolvent trace** (`ℓ²` operator norm on `Matrix p q ℝ`):
for `t > 0`, `X ↦ tr (X Xᵀ + t)⁻¹` is `C^k` for every `k : WithTop ℕ∞` (in particular `C^∞` and
analytic, `k = ⊤`). Route: `X Xᵀ + t • 1` is polynomial and invertible (positive definite);
`Ring.inverse` is smooth at units of a complete normed ring; the trace is linear. -/
theorem contDiff_trace_negResolvent_gram {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p]
    [DecidableEq q] {t : ℝ} (ht : 0 < t) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun X : Matrix p q ℝ => trace (negResolvent (X * Xᵀ) t)) := by
  have hG := contDiff_gram_add (p := p) (q := q) t (k := k)
  have hinv : ContDiff ℝ k (fun X : Matrix p q ℝ => (X * Xᵀ + t • (1 : Matrix p p ℝ))⁻¹) := by
    rw [contDiff_iff_contDiffAt]
    intro X
    have hdet : IsUnit (X * Xᵀ + t • (1 : Matrix p p ℝ)).det := by
      have := posDef_add_smul_one (posSemidef_mul_transpose_self X) ht
      exact isUnit_iff_ne_zero.mpr this.det_pos.ne'
    have hu : IsUnit (X * Xᵀ + t • (1 : Matrix p p ℝ)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr hdet
    obtain ⟨u, hu'⟩ := hu
    have h1 := contDiffAt_ringInverse ℝ (n := k) u
    rw [hu'] at h1
    have h2 : ContDiffAt ℝ k
        (Ring.inverse ∘ fun X : Matrix p q ℝ => (X * Xᵀ + t • (1 : Matrix p p ℝ))) X :=
      ContDiffAt.comp X h1 hG.contDiffAt
    simpa [Function.comp_def, Matrix.nonsing_inv_eq_ringInverse] using h2
  let Tr : Matrix p p ℝ →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (Matrix.traceLinearMap p ℝ ℝ)
  exact Tr.contDiff.comp hinv

/-- Vectorised form (no matrix norm in the statement; `Matrix.of fun i j => x (i, j)` is
`matOfVec x` of `gaussian-foundations`): `x ↦ tr (M Mᵀ + t)⁻¹` with `M = (x (i, j))` is `C^k` on
`p × q → ℝ`. -/
theorem contDiff_trace_negResolvent_gram_vec {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p]
    [DecidableEq q] {t : ℝ} (ht : 0 < t) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun x : p × q → ℝ =>
      trace (negResolvent ((Matrix.of fun i j => x (i, j)) * (Matrix.of fun i j => x (i, j))ᵀ) t)) := by
  let matOfVecLinear : (p × q → ℝ) →ₗ[ℝ] Matrix p q ℝ :=
    { toFun := fun x => Matrix.of fun i j => x (i, j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let L : (p × q → ℝ) →L[ℝ] Matrix p q ℝ := LinearMap.toContinuousLinearMap matOfVecLinear
  exact (contDiff_trace_negResolvent_gram (p := p) (q := q) ht (k := k)).comp L.contDiff

end L2

section Elementwise
open scoped Matrix.Norms.Elementwise

/-- **Smoothness of the Gram resolvent trace** (entrywise sup norm on `Matrix p q ℝ`): see
`contDiff_trace_negResolvent_gram` for the `ℓ²` operator norm version. -/
theorem contDiff_trace_negResolvent_gram_elementwise {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q] {t : ℝ} (ht : 0 < t) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun X : Matrix p q ℝ => trace (negResolvent (X * Xᵀ) t)) := by
  let vecOfMatLinear : Matrix p q ℝ →ₗ[ℝ] (p × q → ℝ) :=
    { toFun := fun X => fun ij => X ij.1 ij.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let L : Matrix p q ℝ →L[ℝ] (p × q → ℝ) := LinearMap.toContinuousLinearMap vecOfMatLinear
  have hv := contDiff_trace_negResolvent_gram_vec (p := p) (q := q) ht (k := k)
  have e : (fun X : Matrix p q ℝ => trace (negResolvent (X * Xᵀ) t)) =
      (fun x : p × q → ℝ => trace (negResolvent ((Matrix.of fun i j => x (i, j)) *
        (Matrix.of fun i j => x (i, j))ᵀ) t)) ∘ (L : Matrix p q ℝ → (p × q → ℝ)) := by
    funext X
    have hX : (Matrix.of fun i j => L X (i, j)) = X := by ext i j; rfl
    simp only [Function.comp_apply, hX]
  rw [e]
  exact hv.comp L.contDiff

end Elementwise

end ContDiffGram
end SpectralFoundations
