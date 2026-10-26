import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Sorted eigenvalues of Hermitian matrices: min–max, Weyl, regularity

Pure linear algebra over `RCLike 𝕜` with a finite index type `n`.

## Contents
* `quadForm A x = re ⟪x, A x⟫`, the (unnormalized) Rayleigh quotient of a matrix on
  `EuclideanSpace 𝕜 n`.
* **Courant–Fischer** for `hA.eigenvalues₀ k` (Mathlib's eigenvalues, sorted decreasingly, so `k = 0`
  is the largest): the two attainment halves of the max–min form, the two halves of the
  min–max form, and the closed `⨆ ⨅` / `⨅ ⨆` equalities.
* **Weyl's perturbation inequality** `|λ_k(A) − λ_k(B)| ≤ ‖A − B‖` and Loewner monotonicity.
* `hermPart A = 2⁻¹ • (A + Aᴴ)` and the total function `sortedEig A := (hermPart A).eigenvalues₀`,
  equal to `eigenvalues₀` on Hermitian matrices, 1-Lipschitz in the l2 operator norm,
  continuous, Borel measurable; measurability of `ω ↦ sortedEig (A ω) k` for random matrices.
* Trace, nonnegativity and norm-bound facts for `sortedEig`, and its invariance under base change
  `ℝ → 𝕜` of a real matrix (`sortedEig_map_ofReal`).

## References
* R. Bhatia, *Matrix Analysis*, GTM 169, §III.1 (Corollary III.1.2, Courant–Fischer;
  Corollary III.2.6, Weyl).

## Interface choices
* **Norm.** Matrices carry no global norm in Mathlib. Every norm statement here is made under
  `open scoped Matrix.Norms.L2Operator`, so `‖A‖` is the l2 operator norm; by `Matrix.cstar_norm_def`
  it is definitionally `‖Matrix.toEuclideanCLM A‖`.
* **Topology.** `continuous_sortedEig` and `measurable_sortedEig` use the default (entrywise, `Pi`)
  topology and measurable structure of `Matrix n n 𝕜`, as in `Mathlib.Topology.Instances.Matrix`
  and `Mathlib.Analysis.Matrix.MeasurableSpace`. The scoped `instL2OpMetricSpace` was constructed with
  its topology replaced by the entrywise one, so the Lipschitz bound transfers to continuity.
* **Junk value.** `sortedEig` is total. On non-Hermitian input it returns the eigenvalues of the
  Hermitian part, which makes it 1-Lipschitz everywhere (`‖hermPart A − hermPart B‖ ≤ ‖A − B‖`
  because `‖Mᴴ‖ = ‖M‖`). It is indexed by `Fin (Fintype.card n)`, like `eigenvalues₀`, and is
  antitone in the index.
* **Rayleigh form.** Courant–Fischer is stated with the homogeneous quadratic form
  (`λ‖x‖² ≤ quadForm A x`), which avoids unit-sphere bookkeeping. The `⨆ ⨅` equalities range over
  unit vectors. In `ℝ` these suprema and infima are genuine, because all index sets are nonempty
  and the values are bounded by `‖A‖`.
* **The real case.** Everything specializes to `𝕜 = ℝ` (real symmetric matrices, `Aᴴ = Aᵀ`);
  `measurable_sortedEig_real` checks that the instances agree with the default ones on `ℝ`.
-/

open Matrix Module Set Filter Topology
open scoped ComplexOrder

noncomputable section

namespace SpectralFoundations

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The quadratic form -/

/-- The quadratic form `x ↦ re ⟪x, A x⟫` of a square matrix on `EuclideanSpace 𝕜 n`. -/
def quadForm (A : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n) : ℝ :=
  RCLike.re (inner 𝕜 x (toEuclideanLin A x))

/-- `quadForm` is additive in the matrix.
Proof route: `map_sub` for `toEuclideanLin`, `LinearMap.sub_apply`, `inner_sub_right`, `map_sub`
for `RCLike.re`. -/
theorem quadForm_sub (A B : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n) :
    quadForm (A - B) x = quadForm A x - quadForm B x := by
  simp [quadForm, inner_sub_right]

open scoped Matrix.Norms.L2Operator in
/-- The quadratic form is bounded by the l2 operator norm: `|quadForm A x| ≤ ‖A‖ ‖x‖²`.
Proof route: `abs_re_le_norm`, Cauchy–Schwarz `norm_inner_le_norm`, then `l2_opNorm_mulVec`
(equivalently `ContinuousLinearMap.le_opNorm` for `toEuclideanCLM A`, via `cstar_norm_def`). -/
theorem abs_quadForm_le (A : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n) :
    |quadForm A x| ≤ ‖A‖ * ‖x‖ ^ 2 := by
  unfold quadForm
  calc |RCLike.re (inner 𝕜 x (toEuclideanLin A x))| ≤ ‖inner 𝕜 x (toEuclideanLin A x)‖ := RCLike.abs_re_le_norm _
    _ ≤ ‖x‖ * ‖toEuclideanLin A x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖A‖ * ‖x‖) := by
        gcongr
        exact Matrix.l2_opNorm_mulVec A x
    _ = _ := by ring

private theorem quadForm_real_smul (A : Matrix n n 𝕜) (r : ℝ) (x : EuclideanSpace 𝕜 n) :
    quadForm A (r • x) = r ^ 2 * quadForm A x := by
  unfold quadForm
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), map_smul, inner_smul_left, inner_smul_right,
    ← mul_assoc]
  have : (starRingEnd 𝕜) (r : 𝕜) * (r : 𝕜) = ((r ^ 2 : ℝ) : 𝕜) := by simp [pow_two]
  rw [this, RCLike.re_ofReal_mul]

private theorem quadForm_eq_sum {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : EuclideanSpace 𝕜 n) :
    quadForm A x = ∑ i, hA.eigenvalues i * ‖inner 𝕜 (hA.eigenvectorBasis i) x‖ ^ 2 := by
  unfold quadForm
  rw [← OrthonormalBasis.sum_inner_mul_inner hA.eigenvectorBasis x (toEuclideanLin A x), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : inner 𝕜 (hA.eigenvectorBasis i) (toEuclideanLin A x) = (hA.eigenvalues i : 𝕜) * inner 𝕜 (hA.eigenvectorBasis i) x := by
    have h2 := hA.mulVec_eigenvectorBasis i
    have : toEuclideanLin A (hA.eigenvectorBasis i) = (hA.eigenvalues i : 𝕜) • hA.eigenvectorBasis i := by
      apply WithLp.ofLp_injective 2
      have e1 : (toEuclideanLin A (hA.eigenvectorBasis i)).ofLp = A *ᵥ (hA.eigenvectorBasis i).ofLp := rfl
      rw [e1, h2, WithLp.ofLp_smul, RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    have hs := (isSymmetric_toEuclideanLin_iff.mpr hA) (hA.eigenvectorBasis i) x
    rw [← hs, this, inner_smul_left]
    simp
  rw [h1]
  have : inner 𝕜 x (hA.eigenvectorBasis i) * ((hA.eigenvalues i : 𝕜) * inner 𝕜 (hA.eigenvectorBasis i) x)
      = ((hA.eigenvalues i * ‖inner 𝕜 (hA.eigenvectorBasis i) x‖ ^ 2 : ℝ) : 𝕜) := by
    rw [← inner_conj_symm x (hA.eigenvectorBasis i)]
    push_cast
    rw [mul_left_comm, RCLike.conj_mul]
  rw [this, RCLike.ofReal_re]
/-! ## Courant–Fischer -/

namespace CourantFischer

variable {A : Matrix n n 𝕜}

private abbrev eqv (n : Type*) [Fintype n] : Fin (Fintype.card n) ≃ n :=
  Fintype.equivOfCardEq (Fintype.card_fin _)

private lemma eigenvalues_eqv (hA : A.IsHermitian) (j : Fin (Fintype.card n)) :
    hA.eigenvalues (eqv n j) = hA.eigenvalues₀ j := by
  simp [Matrix.IsHermitian.eigenvalues]

private def spanOf (hA : A.IsHermitian) (S : Finset n) : Submodule 𝕜 (EuclideanSpace 𝕜 n) :=
  Submodule.span 𝕜 ((hA.eigenvectorBasis : n → EuclideanSpace 𝕜 n) '' (S : Set n))

private lemma finrank_spanOf (hA : A.IsHermitian) (S : Finset n) :
    finrank 𝕜 (spanOf hA S) = S.card := by
  unfold spanOf
  have hli : LinearIndependent 𝕜 (fun i : S => (hA.eigenvectorBasis : n → EuclideanSpace 𝕜 n) i) :=
    hA.eigenvectorBasis.toBasis.linearIndependent.comp _ Subtype.val_injective
  have := finrank_span_eq_card hli
  rw [Set.image_eq_range]
  simpa using this

private lemma inner_eq_zero_of_mem_spanOf (hA : A.IsHermitian) (S : Finset n)
    {x : EuclideanSpace 𝕜 n} (hx : x ∈ spanOf hA S) {i : n} (hi : i ∉ S) :
    inner 𝕜 (hA.eigenvectorBasis i) x = 0 := by
  unfold spanOf at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    have : i ≠ j := fun h => hi (h ▸ hj)
    exact hA.eigenvectorBasis.orthonormal.2 this
  | zero => simp
  | add y z _ _ hy hz => rw [inner_add_right, hy, hz, add_zero]
  | smul c y _ hy => rw [inner_smul_right, hy, mul_zero]

private lemma sum_sq_eq (hA : A.IsHermitian) (x : EuclideanSpace 𝕜 n) :
    ‖x‖ ^ 2 = ∑ i, ‖inner 𝕜 (hA.eigenvectorBasis i) x‖ ^ 2 :=
  (hA.eigenvectorBasis.sum_sq_norm_inner_right x).symm

private lemma quadForm_le_of_mem_spanOf (hA : A.IsHermitian) (S : Finset n) (c : ℝ)
    (hc : ∀ i ∈ S, hA.eigenvalues i ≤ c) {x : EuclideanSpace 𝕜 n} (hx : x ∈ spanOf hA S) :
    quadForm A x ≤ c * ‖x‖ ^ 2 := by
  rw [quadForm_eq_sum hA, sum_sq_eq hA x, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : i ∈ S
  · exact mul_le_mul_of_nonneg_right (hc i hi) (by positivity)
  · rw [inner_eq_zero_of_mem_spanOf hA S hx hi]; simp

private lemma le_quadForm_of_mem_spanOf (hA : A.IsHermitian) (S : Finset n) (c : ℝ)
    (hc : ∀ i ∈ S, c ≤ hA.eigenvalues i) {x : EuclideanSpace 𝕜 n} (hx : x ∈ spanOf hA S) :
    c * ‖x‖ ^ 2 ≤ quadForm A x := by
  rw [quadForm_eq_sum hA, sum_sq_eq hA x, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : i ∈ S
  · exact mul_le_mul_of_nonneg_right (hc i hi) (by positivity)
  · rw [inner_eq_zero_of_mem_spanOf hA S hx hi]; simp

omit [DecidableEq n] in
private lemma exists_mem_inf {V W : Submodule 𝕜 (EuclideanSpace 𝕜 n)}
    (h : Fintype.card n < finrank 𝕜 V + finrank 𝕜 W) : ∃ x ∈ V, x ∈ W ∧ x ≠ 0 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq V W
  have h2 : finrank 𝕜 (V ⊔ W : Submodule 𝕜 _) ≤ Fintype.card n := by
    have := Submodule.finrank_le (V ⊔ W)
    simpa using this
  have h3 : 0 < finrank 𝕜 (V ⊓ W : Submodule 𝕜 _) := by omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (fun h => by rw [h] at h3; simp at h3 : (V ⊓ W) ≠ ⊥)
  exact ⟨x, (Submodule.mem_inf.mp hx).1, (Submodule.mem_inf.mp hx).2, hx0⟩

private lemma normalize {x : EuclideanSpace 𝕜 n} (hx : x ≠ 0) (A : Matrix n n 𝕜) :
    ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 ∧ quadForm A ((‖x‖⁻¹ : ℝ) • x) * ‖x‖ ^ 2 = quadForm A x := by
  have h : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  refine ⟨?_, ?_⟩
  · rw [norm_smul]; simp [h]
  · rw [quadForm_real_smul]; field_simp

open scoped Matrix.Norms.L2Operator in
private lemma exists_bound_unit (A : Matrix n n 𝕜) :
    ∃ C : ℝ, ∀ x : EuclideanSpace 𝕜 n, ‖x‖ = 1 → |quadForm A x| ≤ C :=
  ⟨‖A‖, fun x hx => by simpa [hx] using abs_quadForm_le A x⟩

private lemma aux_subspace_quadForm_le (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    ∃ W : Submodule 𝕜 (EuclideanSpace 𝕜 n), finrank 𝕜 W = Fintype.card n - k ∧
      ∀ x ∈ W, quadForm A x ≤ hA.eigenvalues₀ k * ‖x‖ ^ 2 := by
  refine ⟨spanOf hA ((Finset.Ici k).map (eqv n).toEmbedding), ?_, fun x hx => ?_⟩
  · rw [finrank_spanOf]; simp
  · refine quadForm_le_of_mem_spanOf hA _ _ (fun i hi => ?_) hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    simp only [Finset.mem_Ici] at hj
    simp only [Equiv.coe_toEmbedding]
    rw [eigenvalues_eqv]
    exact hA.eigenvalues₀_antitone hj

/-- Max–min, attainment half: the span of the top `k+1` eigenvectors is a `(k+1)`-dimensional
subspace on which `λ_k ‖x‖² ≤ re ⟪x, A x⟫`.
Proof route: take `V = span {hA.eigenvectorBasis i | eigenvalue index ≤ k}` (reindexed through
`Fintype.equivOfCardEq` as in the definition of `eigenvalues`); expand `x` in the orthonormal
eigenbasis, `quadForm A x = ∑ λ_i |c_i|²` (`mulVec_eigenvectorBasis`), and use
`eigenvalues₀_antitone` to bound each `λ_i ≥ λ_k`. -/
theorem exists_subspace_eigenvalues₀_mul_le (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    ∃ V : Submodule 𝕜 (EuclideanSpace 𝕜 n), finrank 𝕜 V = (k : ℕ) + 1 ∧
      ∀ x ∈ V, hA.eigenvalues₀ k * ‖x‖ ^ 2 ≤ quadForm A x := by
  refine ⟨spanOf hA ((Finset.Iic k).map (eqv n).toEmbedding), ?_, fun x hx => ?_⟩
  · rw [finrank_spanOf]; simp
  · refine le_quadForm_of_mem_spanOf hA _ _ (fun i hi => ?_) hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    simp only [Finset.mem_Iic] at hj
    simp only [Equiv.coe_toEmbedding]
    rw [eigenvalues_eqv]
    exact hA.eigenvalues₀_antitone hj

/-- Max–min, upper-bound half: every subspace of dimension at least `k+1` contains a nonzero `x`
with `re ⟪x, A x⟫ ≤ λ_k ‖x‖²`.
Proof route: let `W` be the span of the eigenvectors with index `≥ k` (dimension `card n − k`).
`finrank V + finrank W > card n`, so `V ⊓ W ≠ ⊥` (`Submodule.finrank_sup_add_finrank_inf_eq` and
`Submodule.finrank_le`); on `W` the eigen-expansion gives `quadForm A x ≤ λ_k ‖x‖²`. -/
theorem exists_mem_quadForm_le_eigenvalues₀_mul (hA : A.IsHermitian) (k : Fin (Fintype.card n))
    (V : Submodule 𝕜 (EuclideanSpace 𝕜 n)) (hV : (k : ℕ) + 1 ≤ finrank 𝕜 V) :
    ∃ x ∈ V, x ≠ 0 ∧ quadForm A x ≤ hA.eigenvalues₀ k * ‖x‖ ^ 2 := by
  obtain ⟨W, hW, hWq⟩ := aux_subspace_quadForm_le hA k
  obtain ⟨x, hxV, hxW, hx0⟩ := exists_mem_inf (V := V) (W := W) (by
    have := k.2; omega)
  exact ⟨x, hxV, hx0, hWq x hxW⟩

/-- Min–max, attainment half: the span of the bottom `card n − k` eigenvectors (indices `≥ k`)
is a subspace of dimension `card n − k` on which `re ⟪x, A x⟫ ≤ λ_k ‖x‖²`.
Proof route: as `exists_subspace_eigenvalues₀_mul_le`, with the reverse inequality from
`eigenvalues₀_antitone`. -/
theorem exists_subspace_quadForm_le_eigenvalues₀_mul (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    ∃ W : Submodule 𝕜 (EuclideanSpace 𝕜 n), finrank 𝕜 W = Fintype.card n - k ∧
      ∀ x ∈ W, quadForm A x ≤ hA.eigenvalues₀ k * ‖x‖ ^ 2 := by
  exact aux_subspace_quadForm_le hA k

/-- Min–max, lower-bound half: every subspace of dimension at least `card n − k` contains a
nonzero `x` with `λ_k ‖x‖² ≤ re ⟪x, A x⟫`.
Proof route: intersect with the span of the top `k+1` eigenvectors (dimensions add to
`card n + 1`), as in `exists_mem_quadForm_le_eigenvalues₀_mul`; or apply that lemma to `-A`,
whose sorted eigenvalues are `k ↦ -λ_{card n - 1 - k}(A)`. -/
theorem exists_mem_eigenvalues₀_mul_le_quadForm (hA : A.IsHermitian) (k : Fin (Fintype.card n))
    (W : Submodule 𝕜 (EuclideanSpace 𝕜 n)) (hW : Fintype.card n - k ≤ finrank 𝕜 W) :
    ∃ x ∈ W, x ≠ 0 ∧ hA.eigenvalues₀ k * ‖x‖ ^ 2 ≤ quadForm A x := by
  obtain ⟨V, hV, hVq⟩ := exists_subspace_eigenvalues₀_mul_le hA k
  obtain ⟨x, hxW, hxV, hx0⟩ := exists_mem_inf (V := W) (W := V) (by
    have := k.2; omega)
  exact ⟨x, hxW, hx0, hVq x hxV⟩

/-- **Courant–Fischer**, max–min form: `λ_k = max_{dim V = k+1} min_{x ∈ V, ‖x‖ = 1} re ⟪x, Ax⟫`.
Proof route: `le_ciSup` at the subspace of `exists_subspace_eigenvalues₀_mul_le` together with
`le_ciInf`; `ciSup_le` and `ciInf_le` with `exists_mem_quadForm_le_eigenvalues₀_mul` (rescale the
nonzero witness to the unit sphere). Boundedness: `abs_quadForm_le`; nonemptiness: unit vectors in
a subspace of positive dimension, and a `(k+1)`-dimensional subspace exists since `k < card n`. -/
theorem eigenvalues₀_eq_iSup_iInf (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    hA.eigenvalues₀ k =
      ⨆ V : {V : Submodule 𝕜 (EuclideanSpace 𝕜 n) // finrank 𝕜 V = (k : ℕ) + 1},
        ⨅ x : {x : EuclideanSpace 𝕜 n // x ∈ V.1 ∧ ‖x‖ = 1}, quadForm A x := by
  obtain ⟨C, hC⟩ := exists_bound_unit A
  have hbdd : ∀ V : {V : Submodule 𝕜 (EuclideanSpace 𝕜 n) // finrank 𝕜 V = (k : ℕ) + 1},
      BddBelow (Set.range fun x : {x : EuclideanSpace 𝕜 n // x ∈ V.1 ∧ ‖x‖ = 1} => quadForm A x) := by
    intro V
    refine ⟨-C, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (abs_le.mp (hC x.1 x.2.2)).1
  have hle : ∀ V : {V : Submodule 𝕜 (EuclideanSpace 𝕜 n) // finrank 𝕜 V = (k : ℕ) + 1},
      (⨅ x : {x : EuclideanSpace 𝕜 n // x ∈ V.1 ∧ ‖x‖ = 1}, quadForm A x) ≤ hA.eigenvalues₀ k := by
    intro V
    obtain ⟨x, hxV, hx0, hxq⟩ := exists_mem_quadForm_le_eigenvalues₀_mul hA k V.1 V.2.ge
    obtain ⟨h1, h2⟩ := normalize hx0 A
    have hpos : 0 < ‖x‖ ^ 2 := by have := norm_pos_iff.mpr hx0; positivity
    have : quadForm A ((‖x‖⁻¹ : ℝ) • x) ≤ hA.eigenvalues₀ k := by
      by_contra hcon
      rw [not_le] at hcon
      have := mul_lt_mul_of_pos_right hcon hpos
      linarith
    exact (ciInf_le (hbdd V) ⟨(‖x‖⁻¹ : ℝ) • x, V.1.smul_of_tower_mem _ hxV, h1⟩).trans this
  obtain ⟨V0, hV0, hV0q⟩ := exists_subspace_eigenvalues₀_mul_le hA k
  have hne : Nonempty {x : EuclideanSpace 𝕜 n // x ∈ V0 ∧ ‖x‖ = 1} := by
    obtain ⟨x, hxV, hx0, -⟩ := exists_mem_quadForm_le_eigenvalues₀_mul hA k V0 hV0.ge
    exact ⟨⟨(‖x‖⁻¹ : ℝ) • x, V0.smul_of_tower_mem _ hxV, (normalize hx0 A).1⟩⟩
  have : Nonempty {V : Submodule 𝕜 (EuclideanSpace 𝕜 n) // finrank 𝕜 V = (k : ℕ) + 1} :=
    ⟨⟨V0, hV0⟩⟩
  apply le_antisymm
  · refine le_trans ?_ (le_ciSup ⟨hA.eigenvalues₀ k, ?_⟩ (⟨V0, hV0⟩ :
      {V : Submodule 𝕜 (EuclideanSpace 𝕜 n) // finrank 𝕜 V = (k : ℕ) + 1}))
    · refine le_ciInf fun x => ?_
      have := hV0q x.1 x.2.1
      rw [x.2.2] at this
      simpa using this
    · rintro _ ⟨V, rfl⟩
      exact hle V
  · exact ciSup_le hle

/-- **Courant–Fischer**, min–max form:
`λ_k = min_{dim W = card n − k} max_{x ∈ W, ‖x‖ = 1} re ⟪x, Ax⟫`.
Proof route: dual to `eigenvalues₀_eq_iSup_iInf`, with
`exists_subspace_quadForm_le_eigenvalues₀_mul` and `exists_mem_eigenvalues₀_mul_le_quadForm`;
`card n − k ≥ 1` gives nonempty unit spheres. -/
theorem eigenvalues₀_eq_iInf_iSup (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    hA.eigenvalues₀ k =
      ⨅ W : {W : Submodule 𝕜 (EuclideanSpace 𝕜 n) // finrank 𝕜 W = Fintype.card n - k},
        ⨆ x : {x : EuclideanSpace 𝕜 n // x ∈ W.1 ∧ ‖x‖ = 1}, quadForm A x := by
  obtain ⟨C, hC⟩ := exists_bound_unit A
  have hbdd : ∀ W : {W : Submodule 𝕜 (EuclideanSpace 𝕜 n) // finrank 𝕜 W = Fintype.card n - k},
      BddAbove (Set.range fun x : {x : EuclideanSpace 𝕜 n // x ∈ W.1 ∧ ‖x‖ = 1} => quadForm A x) := by
    intro W
    refine ⟨C, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (abs_le.mp (hC x.1 x.2.2)).2
  have hge : ∀ W : {W : Submodule 𝕜 (EuclideanSpace 𝕜 n) // finrank 𝕜 W = Fintype.card n - k},
      hA.eigenvalues₀ k ≤ (⨆ x : {x : EuclideanSpace 𝕜 n // x ∈ W.1 ∧ ‖x‖ = 1}, quadForm A x) := by
    intro W
    obtain ⟨x, hxW, hx0, hxq⟩ := exists_mem_eigenvalues₀_mul_le_quadForm hA k W.1 W.2.ge
    obtain ⟨h1, h2⟩ := normalize hx0 A
    have hpos : 0 < ‖x‖ ^ 2 := by have := norm_pos_iff.mpr hx0; positivity
    have : hA.eigenvalues₀ k ≤ quadForm A ((‖x‖⁻¹ : ℝ) • x) := by
      by_contra hcon
      rw [not_le] at hcon
      have := mul_lt_mul_of_pos_right hcon hpos
      linarith
    exact this.trans (le_ciSup (hbdd W) ⟨(‖x‖⁻¹ : ℝ) • x, W.1.smul_of_tower_mem _ hxW, h1⟩)
  obtain ⟨W0, hW0, hW0q⟩ := exists_subspace_quadForm_le_eigenvalues₀_mul hA k
  have hne : Nonempty {x : EuclideanSpace 𝕜 n // x ∈ W0 ∧ ‖x‖ = 1} := by
    obtain ⟨x, hxW, hx0, -⟩ := exists_mem_eigenvalues₀_mul_le_quadForm hA k W0 hW0.ge
    exact ⟨⟨(‖x‖⁻¹ : ℝ) • x, W0.smul_of_tower_mem _ hxW, (normalize hx0 A).1⟩⟩
  have : Nonempty {W : Submodule 𝕜 (EuclideanSpace 𝕜 n) // finrank 𝕜 W = Fintype.card n - k} :=
    ⟨⟨W0, hW0⟩⟩
  apply le_antisymm
  · exact le_ciInf hge
  · refine le_trans (ciInf_le ⟨hA.eigenvalues₀ k, ?_⟩ (⟨W0, hW0⟩ :
      {W : Submodule 𝕜 (EuclideanSpace 𝕜 n) // finrank 𝕜 W = Fintype.card n - k})) ?_
    · rintro _ ⟨W, rfl⟩
      exact hge W
    · refine ciSup_le fun x => ?_
      have := hW0q x.1 x.2.1
      rw [x.2.2] at this
      simpa using this

end CourantFischer

/-! ## Weyl's inequality and monotonicity -/

open scoped Matrix.Norms.L2Operator in
/-- **Weyl's perturbation inequality**: `|λ_k(A) − λ_k(B)| ≤ ‖A − B‖` (l2 operator norm).
Proof route: by `CourantFischer.exists_subspace_eigenvalues₀_mul_le` for `A` take `V`; by
`exists_mem_quadForm_le_eigenvalues₀_mul` for `B` take nonzero `x ∈ V`; then
`λ_k(A)‖x‖² ≤ quadForm A x = quadForm B x + quadForm (A − B) x ≤ (λ_k(B) + ‖A − B‖)‖x‖²`
(`quadForm_sub`, `abs_quadForm_le`). Swap `A`, `B` (`norm_sub_rev`). -/
theorem abs_eigenvalues₀_sub_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (k : Fin (Fintype.card n)) :
    |hA.eigenvalues₀ k - hB.eigenvalues₀ k| ≤ ‖A - B‖ := by
  have key : ∀ {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian),
      hA.eigenvalues₀ k - hB.eigenvalues₀ k ≤ ‖A - B‖ := by
    intro A B hA hB
    obtain ⟨V, hV, hVq⟩ := CourantFischer.exists_subspace_eigenvalues₀_mul_le hA k
    obtain ⟨x, hxV, hx0, hxq⟩ := CourantFischer.exists_mem_quadForm_le_eigenvalues₀_mul hB k V hV.ge
    have h1 := hVq x hxV
    have h2 := abs_quadForm_le (A - B) x
    rw [quadForm_sub] at h2
    have h3 := (abs_le.mp h2).2
    have hpos : 0 < ‖x‖ ^ 2 := by have := norm_pos_iff.mpr hx0; positivity
    by_contra hcon
    rw [not_le] at hcon
    have := mul_lt_mul_of_pos_right hcon hpos
    nlinarith
  rw [abs_le]
  refine ⟨?_, key hA hB⟩
  have := key hB hA
  rw [norm_sub_rev] at this
  linarith

/-- Loewner monotonicity: if `B − A` is positive semidefinite then `λ_k(A) ≤ λ_k(B)`.
Proof route: `quadForm (B − A) x ≥ 0` (`PosSemidef` gives `0 ≤ re (star x ⬝ᵥ (B − A) *ᵥ x)`),
then the Weyl argument without the norm term. -/
theorem eigenvalues₀_le_of_posSemidef_sub {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : (B - A).PosSemidef) (k : Fin (Fintype.card n)) :
    hA.eigenvalues₀ k ≤ hB.eigenvalues₀ k := by
  obtain ⟨V, hV, hVq⟩ := CourantFischer.exists_subspace_eigenvalues₀_mul_le hA k
  obtain ⟨x, hxV, hx0, hxq⟩ := CourantFischer.exists_mem_quadForm_le_eigenvalues₀_mul hB k V hV.ge
  have h1 := hVq x hxV
  have h2 : 0 ≤ quadForm (B - A) x := by
    have := hAB.dotProduct_mulVec_nonneg x.ofLp
    unfold quadForm
    have e : inner 𝕜 x (toEuclideanLin (B - A) x) = star x.ofLp ⬝ᵥ ((B - A) *ᵥ x.ofLp) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]; rfl
    rw [e]
    exact (RCLike.nonneg_iff.mp this).1
  rw [quadForm_sub] at h2
  have hpos : 0 < ‖x‖ ^ 2 := by have := norm_pos_iff.mpr hx0; positivity
  by_contra hcon
  rw [not_le] at hcon
  have := mul_lt_mul_of_pos_right hcon hpos
  nlinarith

/-! ## The total sorted-eigenvalue function -/

/-- The Hermitian part `(A + Aᴴ)/2` of a square matrix (real scalar `2⁻¹`). -/
def hermPart (A : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  (2⁻¹ : ℝ) • (A + Aᴴ)

omit [Fintype n] [DecidableEq n] in
/-- The Hermitian part is Hermitian. -/
theorem isHermitian_hermPart (A : Matrix n n 𝕜) : (hermPart A).IsHermitian :=
  (isHermitian_add_transpose_self A).smul (IsSelfAdjoint.all _)

/-- The Hermitian part of a Hermitian matrix is the matrix itself.
Proof route: `hA.eq` rewrites `Aᴴ = A`; `A + A = (2 : ℝ) • A`; `smul_smul`, `inv_mul_cancel₀`. -/
theorem hermPart_of_isHermitian {A : Matrix n n 𝕜} (hA : A.IsHermitian) : hermPart A = A := by
  unfold hermPart
  rw [hA.eq, ← two_smul ℝ A, smul_smul]
  simp

/-- The sorted (decreasing) eigenvalues of the Hermitian part of `A`, indexed by
`Fin (Fintype.card n)`. On Hermitian `A` this is `hA.eigenvalues₀` (`sortedEig_eq`). -/
def sortedEig (A : Matrix n n 𝕜) : Fin (Fintype.card n) → ℝ :=
  (isHermitian_hermPart A).eigenvalues₀

/-- `sortedEig` agrees with Mathlib's `eigenvalues₀` on Hermitian matrices.
Proof route: rewrite with `hermPart_of_isHermitian hA` under the dependent proof argument
(`congr` / `Subst` on the matrix; the Hermitian proofs are equal by proof irrelevance). -/
theorem sortedEig_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian) : sortedEig A = hA.eigenvalues₀ := by
  have : ∀ (B : Matrix n n 𝕜) (hB : B.IsHermitian) (h : B = A), hB.eigenvalues₀ = hA.eigenvalues₀ := by
    intro B hB h
    subst h
    rfl
  exact this _ _ (hermPart_of_isHermitian hA)

/-- `sortedEig A` is antitone in the index. -/
theorem sortedEig_antitone (A : Matrix n n 𝕜) : Antitone (sortedEig A) :=
  (isHermitian_hermPart A).eigenvalues₀_antitone

/-- Reindexing: sums over sorted eigenvalues are sums over Mathlib's `n`-indexed `eigenvalues`.
Proof route: `sortedEig_eq`, the definition `eigenvalues i = eigenvalues₀ (e.symm i)` with
`e = Fintype.equivOfCardEq (Fintype.card_fin _)`, and `Equiv.sum_comp`. -/
theorem sum_sortedEig_comp {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    ∑ k, f (sortedEig A k) = ∑ i, f (hA.eigenvalues i) := by
  rw [sortedEig_eq hA]
  unfold Matrix.IsHermitian.eigenvalues
  exact (Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun k => f (hA.eigenvalues₀ k))).symm

/-- Trace identity, valid for every square matrix: `∑_k sortedEig A k = re (trace A)`.
Proof route: `IsHermitian.trace_eq_sum_eigenvalues` for `hermPart A`, `sum_sortedEig_comp` with
`f = id`, `RCLike.ofReal_re`-type simp; then `re (trace (hermPart A)) = re (trace A)` from
`trace_conjTranspose` and `RCLike.conj_re`. -/
theorem sum_sortedEig (A : Matrix n n 𝕜) : ∑ k, sortedEig A k = RCLike.re (trace A) := by
  have h1 := sum_sortedEig_comp (isHermitian_hermPart A) id
  have h2 := (isHermitian_hermPart A).trace_eq_sum_eigenvalues
  have h3 : sortedEig (hermPart A) = sortedEig A := by
    rw [sortedEig_eq (isHermitian_hermPart A)]; rfl
  have h4 : RCLike.re (trace (hermPart A)) = RCLike.re (trace A) := by
    unfold hermPart
    rw [trace_smul, trace_add, trace_conjTranspose]
    simp only [map_add, RCLike.smul_re, ← starRingEnd_apply, RCLike.conj_re]
    ring
  rw [← h4, h2, ← h3]
  simp only [id] at h1
  rw [h1, map_sum]
  simp

/-- Positive semidefinite matrices have nonnegative sorted eigenvalues.
Proof route: `sortedEig_eq hA.1`, then `PosSemidef.eigenvalues_nonneg` and the definition of
`eigenvalues` through `eigenvalues₀` (reindex by `Fintype.equivOfCardEq`). -/
theorem sortedEig_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef) (k : Fin (Fintype.card n)) :
    0 ≤ sortedEig A k := by
  rw [sortedEig_eq hA.1]
  have := hA.eigenvalues_nonneg (CourantFischer.eqv n k)
  rwa [CourantFischer.eigenvalues_eqv] at this

/-- For positive semidefinite `A`, each sorted eigenvalue is at most the trace.
Proof route: `sum_sortedEig` and `Finset.single_le_sum` with `sortedEig_nonneg`. -/
theorem sortedEig_le_re_trace {A : Matrix n n 𝕜} (hA : A.PosSemidef) (k : Fin (Fintype.card n)) :
    sortedEig A k ≤ RCLike.re (trace A) := by
  rw [← sum_sortedEig]
  exact Finset.single_le_sum (f := sortedEig A) (fun j _ => sortedEig_nonneg hA j) (Finset.mem_univ k)

open scoped Matrix.Norms.L2Operator in
/-- Weyl for the total function: `|sortedEig A k − sortedEig B k| ≤ ‖A − B‖` for all square
matrices (l2 operator norm).
Proof route: `abs_eigenvalues₀_sub_le` for the Hermitian parts, then
`‖hermPart A − hermPart B‖ = ‖2⁻¹ • ((A − B) + (A − B)ᴴ)‖ ≤ ‖A − B‖` by `norm_smul`,
`norm_add_le` and `l2_opNorm_conjTranspose`. -/
theorem abs_sortedEig_sub_le (A B : Matrix n n 𝕜) (k : Fin (Fintype.card n)) :
    |sortedEig A k - sortedEig B k| ≤ ‖A - B‖ := by
  refine (abs_eigenvalues₀_sub_le (isHermitian_hermPart A) (isHermitian_hermPart B) k).trans ?_
  have e : hermPart A - hermPart B = (2⁻¹ : ℝ) • ((A - B) + (A - B)ᴴ) := by
    unfold hermPart
    rw [conjTranspose_sub]
    simp only [← smul_sub]
    congr 1
    abel
  rw [e, RCLike.real_smul_eq_coe_smul (K := 𝕜), norm_smul]
  have := norm_add_le (A - B) (A - B)ᴴ
  rw [l2_opNorm_conjTranspose] at this
  have h2 : ‖((2⁻¹ : ℝ) : 𝕜)‖ = 2⁻¹ := by simp
  rw [h2]
  linarith

/-- The zero matrix has all sorted eigenvalues `0`.
Proof route: `hermPart 0 = 0` (`conjTranspose_zero`, `smul_zero`); `sortedEig_eq` for
`isHermitian_zero`; `IsHermitian.eigenvalues_eq_zero_iff` and the reindexing between `eigenvalues`
and `eigenvalues₀`. -/
theorem sortedEig_zero : sortedEig (0 : Matrix n n 𝕜) = 0 := by
  have hz : (0 : Matrix n n 𝕜).IsHermitian := isHermitian_zero
  rw [sortedEig_eq hz]
  funext k
  have := congrFun (hz.eigenvalues_eq_zero_iff.mpr rfl) (CourantFischer.eqv n k)
  rw [CourantFischer.eigenvalues_eqv] at this
  exact this

open scoped Matrix.Norms.L2Operator in
/-- Each sorted eigenvalue is bounded by the l2 operator norm: `|sortedEig A k| ≤ ‖A‖`.
Proof route: `abs_sortedEig_sub_le A 0 k`, `sortedEig_zero`, `sub_zero`. -/
theorem abs_sortedEig_le_norm (A : Matrix n n 𝕜) (k : Fin (Fintype.card n)) :
    |sortedEig A k| ≤ ‖A‖ := by
  simpa [sortedEig_zero] using abs_sortedEig_sub_le A 0 k

private lemma eigenvalues₀_map_ofReal (B : Matrix n n ℝ) (hB : B.IsHermitian)
    (hB' : (B.map ((↑) : ℝ → 𝕜)).IsHermitian) : hB'.eigenvalues₀ = hB.eigenvalues₀ := by
  have h1 := hB'.sort_roots_charpoly_eq_eigenvalues₀
  have h2 := hB.sort_roots_charpoly_eq_eigenvalues₀
  have hc : (B.map ((↑) : ℝ → 𝕜)).charpoly = B.charpoly.map (algebraMap ℝ 𝕜) :=
    Matrix.charpoly_map B (algebraMap ℝ 𝕜)
  rw [hc, hB.splits_charpoly.roots_map (algebraMap ℝ 𝕜), Multiset.map_map] at h1
  have e1 : (RCLike.re ∘ algebraMap ℝ 𝕜 : ℝ → ℝ) = id := by
    funext x; simp
  have e2 : (RCLike.re : ℝ → ℝ) = id := by
    funext x; simp
  rw [e1, Multiset.map_id] at h1
  rw [e2, Multiset.map_id] at h2
  exact List.ofFn_injective (h1.symm.trans h2)

/-- Complexification (more generally, base change `ℝ → 𝕜`) does not change the sorted
eigenvalues of a real matrix. Lets results for complex resolvents `(A − z)⁻¹`, `z ∉ ℝ`, be applied
to real symmetric matrices through `A.map (↑)`.
Proof route: `hermPart (A.map (↑)) = (hermPart A).map (↑)` (`conjTranspose_map`, `RCLike.conj_ofReal`);
then for Hermitian `B` over `ℝ`, `charpoly (B.map (↑)) = (charpoly B).map (algebraMap ℝ 𝕜)`
(`Matrix.charpoly_map`) and `sort_roots_charpoly_eq_eigenvalues₀` on both sides, with
`RCLike.ofReal_re` and `Polynomial.roots_map` (the real charpoly of a symmetric matrix splits). -/
theorem sortedEig_map_ofReal (A : Matrix n n ℝ) :
    sortedEig (A.map ((↑) : ℝ → 𝕜)) = sortedEig A := by
  have e : hermPart (A.map ((↑) : ℝ → 𝕜)) = (hermPart A).map ((↑) : ℝ → 𝕜) := by
    ext i j
    simp [hermPart, conjTranspose_apply]
  unfold sortedEig
  have key : ∀ (C : Matrix n n 𝕜) (hC : C.IsHermitian) (h : C = (hermPart A).map ((↑) : ℝ → 𝕜)),
      hC.eigenvalues₀ = (isHermitian_hermPart A).eigenvalues₀ := by
    intro C hC h
    subst h
    exact eigenvalues₀_map_ofReal _ _ _
  exact key _ _ e

open scoped Matrix.Norms.L2Operator in
/-- Each sorted eigenvalue is 1-Lipschitz for the l2 operator norm.
Proof route: `LipschitzWith.of_dist_le_mul` with `Real.dist_eq`, `dist_eq_norm` and
`abs_sortedEig_sub_le`. -/
theorem lipschitzWith_sortedEig (k : Fin (Fintype.card n)) :
    LipschitzWith 1 (fun A : Matrix n n 𝕜 => sortedEig A k) := by
  refine LipschitzWith.of_dist_le_mul fun A B => ?_
  rw [Real.dist_eq, dist_eq_norm]
  simpa using abs_sortedEig_sub_le A B k

/-- Each sorted eigenvalue is continuous (entrywise topology on matrices).
Proof route (checked to typecheck against this statement):
`let := Matrix.instL2OpMetricSpace (m := n) (n := n) (𝕜 := 𝕜)` then
`exact (lipschitzWith_sortedEig k).continuous`. The topology of `instL2OpMetricSpace` is the
entrywise one by construction (`replaceTopology`/`replaceUniformity`), so the instances unify. -/
theorem continuous_sortedEig (k : Fin (Fintype.card n)) :
    Continuous (fun A : Matrix n n 𝕜 => sortedEig A k) := by
  let := Matrix.instL2OpMetricSpace (m := n) (n := n) (𝕜 := 𝕜)
  exact (lipschitzWith_sortedEig k).continuous

/-- The vector of sorted eigenvalues is continuous.
Proof route: `continuous_pi continuous_sortedEig`. -/
theorem continuous_sortedEig_vec : Continuous (sortedEig : Matrix n n 𝕜 → Fin _ → ℝ) := by
  exact continuous_pi continuous_sortedEig

/-- Each sorted eigenvalue is Borel measurable.
Proof route: `(continuous_sortedEig k).measurable`; `Matrix n n 𝕜` is a `BorelSpace`
(`Mathlib.Analysis.Matrix.MeasurableSpace`, `n` finite and `𝕜` second countable). -/
theorem measurable_sortedEig (k : Fin (Fintype.card n)) :
    Measurable (fun A : Matrix n n 𝕜 => sortedEig A k) := by
  exact (continuous_sortedEig k).measurable

/-- The vector of sorted eigenvalues is Borel measurable.
Proof route: `measurable_pi_lambda _ measurable_sortedEig`. -/
theorem measurable_sortedEig_vec : Measurable (sortedEig : Matrix n n 𝕜 → Fin _ → ℝ) := by
  exact measurable_pi_iff.mpr measurable_sortedEig

/-- Random-matrix corollary: for a measurable random matrix `A`, `ω ↦ sortedEig (A ω) k` is
measurable. -/
theorem _root_.Measurable.sortedEig {Ω : Type*} [MeasurableSpace Ω] {A : Ω → Matrix n n 𝕜}
    (hA : Measurable A) (k : Fin (Fintype.card n)) :
    Measurable (fun ω => sortedEig (A ω) k) :=
  (measurable_sortedEig k).comp hA

/-- Random-matrix corollary, almost-everywhere version. -/
theorem _root_.AEMeasurable.sortedEig {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} {A : Ω → Matrix n n 𝕜}
    (hA : AEMeasurable A P) (k : Fin (Fintype.card n)) :
    AEMeasurable (fun ω => sortedEig (A ω) k) P :=
  (measurable_sortedEig k).comp_aemeasurable hA

/-- The real-symmetric case uses the default measurable structure on `ℝ` (instance check). -/
theorem measurable_sortedEig_real (k : Fin (Fintype.card n)) :
    Measurable (fun A : Matrix n n ℝ => sortedEig A k) :=
  measurable_sortedEig k

end SpectralFoundations
