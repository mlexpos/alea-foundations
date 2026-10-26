# SpectralFoundations

A Lean 4 foundations package (Lean `v4.34.1`, shared Mathlib checkout at `../.lake/packages/mathlib`)
that supplies the analytic tools behind the existence of the isotropic measure pair in the Muon
project. It is currently a **frozen interface**: definitions are real, and theorem proofs are
`sorry` except a few one-liners. Each theorem's docstring gives its intended proof route.

## Targets

* **Primary:** `Muon.Isotropic.prop_app_iso_measure_exists`
  (`~/Documents/lean/muon/lean/Muon/Isotropic/MeasureExistence.lean`). The glue applies
  `SpectralFoundations.exists_tendsto_of_tendsto_negStieltjes` to
  `ζ_B = B⁻¹ • E[∑ᵢ δ_{λᵢ(M Mᵀ)}]`, i.e. `ENNReal.ofReal B⁻¹ • expectedEigMeasure P (fun ω => M ω * (M ω)ᵀ)`.
  The inputs come from `negStieltjes_expectedEigMeasure`, `integral_id_expectedEigMeasure`,
  `expectedEigMeasure_univ`, `expectedEigMeasure_Iio_zero`, `posSemidef_mul_transpose_self` and
  `negStieltjes_smul`.
* **Citations back into Muon** (statements match their shapes):
  * `lem_app_iso_transforms_i` is `tendsto_of_tendsto_negStieltjes_prob`;
  * `lem_app_iso_transforms_ii` is `eq_of_negStieltjes_eq_of_mass` (or `eq_of_negStieltjes_eq`);
  * `lem_app_de_resolvent` is `gramResolvent_facts`, after `Muon.opNorm_eq_norm`;
  * `lem_app_de_deletion` is `gramResolvent_rankOne_update`;
  * `lem_app_de_lipschitz` is `nuclearNorm_gramResolvent_sub_le`.

  `negStieltjes` and `isoNegStieltjes` are the same expression, so they agree by `rfl`, and
  `gramResolvent`, `gramResolventT` and `mixedResolvent` unfold to Muon's `Rs`, `Rts` and `Xs`
  (`gramResolvent_def` is `rfl`).

## Module map (dependency order)

| File | Contents |
|---|---|
| `SpectralFoundations/Eigenvalues.lean` | `quadForm`; Courant–Fischer (attainment halves, `⨆⨅`, `⨅⨆`); Weyl `\|λₖ(A)−λₖ(B)\| ≤ ‖A−B‖`; Loewner monotonicity; `hermPart`, total `sortedEig` (= `eigenvalues₀` on Hermitian matrices), 1-Lipschitz, continuous, measurable; trace and nonnegativity facts |
| `SpectralFoundations/Resolvent.lean` | `matResolvent` (not Mathlib's `resolvent`), `negResolvent`; inverse and resolvent identities; sharp norm `‖(A−z)⁻¹‖ = 1/infDist z σ(A)` (normal over ℂ, Hermitian over `RCLike`); `≤ 1/\|Im z\|`, `≤ 1/t`; Lipschitz bounds; rank bound on traces; Sherman–Morrison; nuclear norm; Gram resolvents, push-through, deletion and Lipschitz (Muon `lem_app_de_*`); `abs_re_trace_cfc_le`; smoothness `contDiff_trace_negResolvent_gram` (+ `_elementwise`, `_vec`) of `X ↦ tr (XXᵀ+t)⁻¹` |
| `SpectralFoundations/Stieltjes.lean` | `negStieltjes`, `stieltjes`; bounds; uniqueness; continuity theorem; Fatou and half-moment; **existence/limit theorem**; holomorphy; `abs_negStieltjes_sub_le` (Lipschitz on the negative axis) |
| `SpectralFoundations/ESD.lean` | `eigMeasure`, `esd`; integral / trace / `cfc` / resolvent / first-moment / support identities; Giry measurability; `expectedEigMeasure`, `expectedEsd` and the identities through the expectation; `trace_matResolvent_eq_sum`, `stieltjes_eigMeasure`, `stieltjes_esd` (`S_{esd A}(z) = (1/N) tr (A−z)⁻¹`) |
| `SpectralFoundations/SVD.lean` | rectangular SVD `K = ∑ s_k p_k ⊗ r_k` (Mathlib singular values), rank bridge, intertwining `K f(KᵀK) = f(KKᵀ) K` |
| `SpectralFoundations/OperatorLipschitz.lean` | local `fro`; Hermitian dilation `hermDilation`/`upperRight`; `fro_cfc_sub_cfc_le` (Frobenius divided-difference bound); `lipschitz_filter_fun` for `x(x²+ϱ)^{-1/2}`; `upperRight_cfc_hermDilation` |
| `SpectralFoundations.lean` | root, imports all |

Norms on matrices are the l2 operator norm under `open scoped Matrix.Norms.L2Operator`.
Topology and measurability use Mathlib's default entrywise structures.

## Compiling

Compile one file at a time, in dependency order (Eigenvalues, Resolvent, Stieltjes, ESD, root):

```sh
cd ~/Documents/lean/spectral-foundations
export ELAN_HOME=$HOME/Documents/lean/.elan PATH=$HOME/Documents/lean/.elan/bin:$PATH
lake env lean SpectralFoundations/Eigenvalues.lean
```

To make an upstream interface visible to a downstream file, write its olean by hand:

```sh
mkdir -p .lake/build/lib/lean/SpectralFoundations
lake env lean -o .lake/build/lib/lean/SpectralFoundations/Eigenvalues.olean \
  -i .lake/build/lib/lean/SpectralFoundations/Eigenvalues.ilean SpectralFoundations/Eigenvalues.lean
```

A file passes when its only warnings are `declaration uses 'sorry'`.

## Warning

**Never run `lake build` (here or in the shared `~/Documents/lean` workspace) while campaign
workers are running.** The Mathlib checkout and toolchain are shared, and a build can rebuild or
lock shared artifacts under other workers. The machine has 36 GB of RAM shared among workers, so
run one `lean` process at a time and kill any that hang.

## Conventions
- Resolvent: `matResolvent A z = (A − z)⁻¹`, the RMT sign convention, used across spectral-foundations and rmt-foundations. Mathlib's root `resolvent a z = (z − a)⁻¹` has the OPPOSITE sign and is never used here.
- Negative axis: `negResolvent A t = (A + t)⁻¹ = matResolvent A (−t)`; `negStieltjes ν t = ∫ (x + t)⁻¹ dν`.
- Stieltjes transform: `stieltjes ν z = ∫ (x − z)⁻¹ dν`, so `(1/N) tr matResolvent A z = stieltjes (esd A) z`, and `Im > 0` on the upper half-plane.
