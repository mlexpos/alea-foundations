import SpectralFoundations.SVD

/-!
# Frobenius divided-difference bound and the Hermitian dilation

* `fro_cfc_sub_cfc_le`: for symmetric `A, B` and `f` Lipschitz with constant `L` on an interval
  `I` containing both spectra, `fro (cfc f A - cfc f B) ≤ L * fro (A - B)`.
* Hermitian dilation `hermDilation K = [[0, K], [Kᵀ, 0]]` of a rectangular `K`, indexed by
  `Fin (m + n)`. Its upper-right block is `upperRight`. The odd filter `x ↦ x (x² + ϱ)^{-1/2}`
  applied to the dilation has upper-right block `K * cfc (fun x => (x + ϱ)^{-1/2}) (KᵀK)`
  (`upperRight_cfc_hermDilation`; Muon writes this block as `Q ϱ K`).
* `lipschitz_filter_fun`: the filter is globally `ϱ^{-1/2}`-Lipschitz.

Relocated from Muon `Foundations/OperatorLipschitz` (all but the Muon-specific `fro_Q_sub_Q_le`).

Norm convention: `fro` is a LOCAL definition below, with exactly Muon's body from
`Muon.Foundations.Conventions` (`sqrt (∑ i, ∑ j, ‖K i j‖^2)`, generic over `RCLike`), so that Muon's
`Muon.fro` is definitionally equal to `SpectralFoundations.fro` and the Muon wrappers are
one-liners. (Equivalent to the Mathlib Frobenius norm `Matrix.Norms.Frobenius`; not bridged here.)
`Mat m n` of Muon is written `Matrix (Fin m) (Fin n) ℝ`.
-/

open scoped Matrix MatrixOrder
open Matrix

noncomputable section

namespace SpectralFoundations

/-- Frobenius norm `‖K‖_F`; exactly Muon's `Muon.fro` (generic over `RCLike`). -/
def fro {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ} (K : Matrix (Fin m) (Fin n) 𝕜) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ‖K i j‖ ^ 2)

/-- Hermitian dilation `𝒟(K) = [[0, K], [Kᵀ, 0]]` of a real `m × n` matrix, as a matrix indexed
by `Fin (m + n)` (the sum `Fin m ⊕ Fin n` reindexed by `finSumFinEquiv`). Indexing by `Fin (m+n)`
keeps `fro`, `cfc` and `Mat` of Conventions applicable.  -/
def hermDilation {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin (m + n)) (Fin (m + n)) ℝ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 K Kᵀ 0)

/-- Upper-right `m × n` block of a `(m+n) × (m+n)` matrix.  -/
def upperRight {m n : ℕ} (X : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun i j => X (Fin.castAdd n i) (Fin.natAdd m j)

/-- The dilation of a real matrix is symmetric (`𝒟(K)ᵀ = 𝒟(K)`), so the Hermitian functional
calculus applies to it.  -/
theorem hermDilation_isHermitian {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ) :
    (hermDilation K).IsHermitian := by
  have hM : (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) K Kᵀ (0 : Matrix (Fin n) (Fin n) ℝ)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.fromBlocks_transpose]
    simp
  unfold hermDilation
  exact hM.reindex finSumFinEquiv

theorem fro_sq_eq_sum {k l : ℕ} (A : Matrix (Fin k) (Fin l) ℝ) : fro A ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  unfold fro
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)

/-- Frobenius norm of the dilation: `‖𝒟(E)‖_F² = 2 ‖E‖_F²` for every rectangular `E`
.  -/
theorem fro_hermDilation {m n : ℕ} (E : Matrix (Fin m) (Fin n) ℝ) :
    fro (hermDilation E) ^ 2 = 2 * fro E ^ 2 := by
  rw [fro_sq_eq_sum (hermDilation E), fro_sq_eq_sum E]
  simp only [Fin.sum_univ_add, Finset.sum_add_distrib, hermDilation, Matrix.reindex_apply,
    Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply,
    Matrix.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero, zero_add, add_zero]
  rw [Finset.sum_comm (f := fun i j => ‖E j i‖ ^ 2)]
  ring

/-- For a symmetric `(m+n) × (m+n)` matrix `X`, the upper-right block carries half of the
squared Frobenius mass: `2 ‖X_{12}‖_F² ≤ ‖X‖_F²`, because the lower-left block is `X_{12}ᵀ`.
 -/
theorem fro_upperRight_sq_le {m n : ℕ} (X : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) (hX : X.IsHermitian) :
    2 * fro (upperRight X) ^ 2 ≤ fro X ^ 2 := by
  have key : ∀ (i : Fin m) (j : Fin n),
      X (Fin.natAdd m j) (Fin.castAdd n i) = X (Fin.castAdd n i) (Fin.natAdd m j) := by
    intro i j
    simpa using hX.apply (Fin.castAdd n i) (Fin.natAdd m j)
  have hsw : ∑ i : Fin n, ∑ j : Fin m, ‖X (Fin.natAdd m i) (Fin.castAdd n j)‖ ^ 2 =
      ∑ i : Fin m, ∑ j : Fin n, ‖X (Fin.castAdd n i) (Fin.natAdd m j)‖ ^ 2 := by
    rw [Finset.sum_comm]
    simp only [key]
  have hA : 0 ≤ ∑ i : Fin m, ∑ j : Fin m, ‖X (Fin.castAdd n i) (Fin.castAdd n j)‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hD : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, ‖X (Fin.natAdd m i) (Fin.natAdd m j)‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [fro_sq_eq_sum (upperRight X), fro_sq_eq_sum X]
  simp only [upperRight, Matrix.of_apply, Fin.sum_univ_add, Finset.sum_add_distrib]
  linarith [hsw, hA, hD]

/-- Spectrum of a block-diagonal matrix lies in the union of the block spectra. Helper. -/
private theorem spectrum_fromBlocks_diag_sub {m n : ℕ} (P : Matrix (Fin m) (Fin m) ℝ) (R : Matrix (Fin n) (Fin n) ℝ) :
    spectrum ℝ (Matrix.fromBlocks P 0 0 R) ⊆ spectrum ℝ P ∪ spectrum ℝ R := by
  intro l hl
  by_contra hc
  simp only [Set.mem_union, not_or] at hc
  have hU1 : IsUnit (algebraMap ℝ (Matrix (Fin m) (Fin m) ℝ) l - P) := spectrum.notMem_iff.mp hc.1
  have hU2 : IsUnit (algebraMap ℝ (Matrix (Fin n) (Fin n) ℝ) l - R) := spectrum.notMem_iff.mp hc.2
  apply spectrum.mem_iff.mp hl
  have hdiag : algebraMap ℝ (Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ) l - Matrix.fromBlocks P 0 0 R
      = Matrix.fromBlocks (algebraMap ℝ (Matrix (Fin m) (Fin m) ℝ) l - P) 0 0 (algebraMap ℝ (Matrix (Fin n) (Fin n) ℝ) l - R) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.algebraMap_matrix_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  rw [hdiag, Matrix.isUnit_iff_isUnit_det, Matrix.det_fromBlocks_zero₂₁]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hU1).mul ((Matrix.isUnit_iff_isUnit_det _).mp hU2)

/-- Powers of a block-diagonal matrix are block-diagonal. Helper. -/
private theorem fromBlocks_diag_pow {m n : ℕ} (P : Matrix (Fin m) (Fin m) ℝ) (R : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    (Matrix.fromBlocks P 0 0 R) ^ k = Matrix.fromBlocks (P ^ k) 0 0 (R ^ k) := by
  induction k with
  | zero => simp [Matrix.fromBlocks_one]
  | succ k ih =>
    rw [pow_succ, ih, Matrix.fromBlocks_multiply]
    simp [pow_succ]

/-- Lower-right block of a polynomial evaluated at a block-diagonal matrix. Helper. -/
private theorem aeval_fromBlocks_inr {m n : ℕ} (P : Matrix (Fin m) (Fin m) ℝ) (R : Matrix (Fin n) (Fin n) ℝ) (q : Polynomial ℝ)
    (i j : Fin n) :
    (Polynomial.aeval (Matrix.fromBlocks P 0 0 R) q) (Sum.inr i) (Sum.inr j)
      = (Polynomial.aeval R q) i j := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial k a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, fromBlocks_diag_pow,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_mul, smul_mul,
      one_mul, one_mul]
    simp

/-- The odd filter `x ↦ x (x² + ϱ)^{-1/2}` applied to the dilation has upper-right block
`K φ_ϱ(KᵀK) = Q_ϱ(K)`, `φ_ϱ(x) = (x+ϱ)^{-1/2}`, for `ϱ > 0`. -/
theorem upperRight_cfc_hermDilation {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (K : Matrix (Fin m) (Fin n) ℝ) :
    upperRight (cfc (fun x : ℝ => x * (x ^ 2 + ϱ) ^ (-(1 / 2 : ℝ))) (hermDilation K))
      = K * cfc (fun x : ℝ => (x + ϱ) ^ (-(1 / 2 : ℝ))) (Kᵀ * K) := by
  have hsaR : IsSelfAdjoint (Kᵀ * K) := by
    have h := Matrix.isHermitian_conjTranspose_mul_self K
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hsaX : IsSelfAdjoint (hermDilation K) := hermDilation_isHermitian K
  have hX : hermDilation K
      = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 K Kᵀ 0) := rfl
  have hmul : ∀ M N : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ,
      Matrix.reindex finSumFinEquiv finSumFinEquiv M * Matrix.reindex finSumFinEquiv finSumFinEquiv N
        = Matrix.reindex finSumFinEquiv finSumFinEquiv (M * N) :=
    fun M N => (map_mul (reindexAlgEquiv ℝ ℝ finSumFinEquiv) M N).symm
  have hX2 : hermDilation K ^ 2 = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (K * Kᵀ) 0 0 (Kᵀ * K)) := by
    rw [sq, hX, hmul]
    congr 1
    rw [Matrix.fromBlocks_multiply]
    simp
  have hspec2 : spectrum ℝ (hermDilation K ^ 2) ⊆ spectrum ℝ (K * Kᵀ) ∪ spectrum ℝ (Kᵀ * K) := by
    intro x hx
    have h1 : spectrum ℝ (Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (K * Kᵀ) 0 0 (Kᵀ * K))) = spectrum ℝ (Matrix.fromBlocks (K * Kᵀ) 0 0 (Kᵀ * K)) :=
      AlgEquiv.spectrum_eq (reindexAlgEquiv ℝ ℝ finSumFinEquiv) _
    rw [hX2, h1] at hx
    exact spectrum_fromBlocks_diag_sub _ _ hx
  have hPf : (spectrum ℝ (K * Kᵀ)).Finite := Matrix.finite_real_spectrum
  have hRf : (spectrum ℝ (Kᵀ * K)).Finite := Matrix.finite_real_spectrum
  set s : Finset ℝ := (hPf.union hRf).toFinset with hs
  have hinj : Set.InjOn (id : ℝ → ℝ) (s : Set ℝ) := Set.injOn_id _
  set q : Polynomial ℝ := Lagrange.interpolate s id (fun y : ℝ => (y + ϱ) ^ (-(1 / 2 : ℝ))) with hq
  have hqU : ∀ y ∈ spectrum ℝ (K * Kᵀ) ∪ spectrum ℝ (Kᵀ * K),
      q.eval y = (y + ϱ) ^ (-(1 / 2 : ℝ)) := by
    intro y hy
    have hys : y ∈ s := (hPf.union hRf).mem_toFinset.mpr hy
    have := Lagrange.eval_interpolate_at_node (s := s) (v := id)
      (r := fun y : ℝ => (y + ϱ) ^ (-(1 / 2 : ℝ))) hinj hys
    simpa [hq] using this
  have hR_eq : cfc (fun y : ℝ => (y + ϱ) ^ (-(1 / 2 : ℝ))) (Kᵀ * K) = Polynomial.aeval (Kᵀ * K) q := by
    rw [← cfc_polynomial q (Kᵀ * K) hsaR]
    exact cfc_congr' fun y hy => (hqU y (Or.inr hy)).symm
  have hφ : cfc (fun x : ℝ => x * (x ^ 2 + ϱ) ^ (-(1 / 2 : ℝ))) (hermDilation K)
      = hermDilation K * Polynomial.aeval (hermDilation K ^ 2) q := by
    have hcongr : cfc (fun x : ℝ => x * (x ^ 2 + ϱ) ^ (-(1 / 2 : ℝ))) (hermDilation K)
        = cfc (fun x : ℝ => (Polynomial.X * q.comp (Polynomial.X ^ 2)).eval x) (hermDilation K) := by
      apply cfc_congr'
      intro x hx
      have hx2 : x ^ 2 ∈ spectrum ℝ (K * Kᵀ) ∪ spectrum ℝ (Kᵀ * K) :=
        hspec2 (spectrum.pow_image_subset (hermDilation K) 2 ⟨x, hx, rfl⟩)
      simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
        Polynomial.eval_pow, hqU _ hx2]
    rw [hcongr, cfc_polynomial _ _ hsaX, Polynomial.aeval_mul, Polynomial.aeval_X,
      Polynomial.aeval_comp, Polynomial.aeval_X_pow]
  have hA : Polynomial.aeval (hermDilation K ^ 2) q = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Polynomial.aeval (Matrix.fromBlocks (K * Kᵀ) 0 0 (Kᵀ * K)) q) := by
    rw [hX2]
    exact Polynomial.aeval_algHom_apply (reindexAlgEquiv ℝ ℝ finSumFinEquiv).toAlgHom _ q
  rw [hφ, hA, hX, hmul]
  rw [hR_eq]
  ext i j
  simp [upperRight, Matrix.reindex_apply, Matrix.mul_apply, Fintype.sum_sum_type,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    aeval_fromBlocks_inr]

/-- The filter `x ↦ x (x² + ϱ)^{-1/2}` is globally Lipschitz on `ℝ` with constant
`ϱ^{-1/2}` for `ϱ > 0` (its derivative `ϱ (x² + ϱ)^{-3/2}` is bounded by `ϱ^{-1/2}`; mean value
theorem).  -/
theorem lipschitz_filter_fun {ϱ : ℝ} (hϱ : 0 < ϱ) :
    LipschitzWith (Real.toNNReal (ϱ ^ (-(1 / 2 : ℝ))))
      (fun x : ℝ => x * (x ^ 2 + ϱ) ^ (-(1 / 2 : ℝ))) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => x * (x ^ 2 + ϱ) ^ (-(1 / 2 : ℝ)))
      (ϱ * (x ^ 2 + ϱ) ^ (-(3 / 2 : ℝ))) x := by
    intro x
    have hs : 0 < x ^ 2 + ϱ := by positivity
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2 + ϱ) (2 * x) x := by
      simpa using ((hasDerivAt_id x).pow 2).add_const ϱ
    have h2 := h1.rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hs.ne')
    have h3 : HasDerivAt (fun y : ℝ => y * (y ^ 2 + ϱ) ^ (-(1 / 2 : ℝ)))
        (1 * (x ^ 2 + ϱ) ^ (-(1 / 2 : ℝ)) +
          x * (2 * x * -(1 / 2) * (x ^ 2 + ϱ) ^ (-(1 / 2 : ℝ) - 1))) x :=
      (hasDerivAt_id x).mul h2
    have e1 : (x ^ 2 + ϱ) ^ (-(1 / 2 : ℝ)) = (x ^ 2 + ϱ) ^ (-(3 / 2 : ℝ)) * (x ^ 2 + ϱ) := by
      rw [← Real.rpow_add_one hs.ne']; norm_num
    have e2 : (x ^ 2 + ϱ) ^ (-(1 / 2 : ℝ) - 1) = (x ^ 2 + ϱ) ^ (-(3 / 2 : ℝ)) := by
      norm_num
    convert h3 using 1
    rw [e2, e1]
    ring
  refine lipschitzWith_of_nnnorm_deriv_le (fun x => (hd x).differentiableAt) ?_
  intro x
  rw [(hd x).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity)]
  have hs : 0 < x ^ 2 + ϱ := by positivity
  have hle : (x ^ 2 + ϱ) ^ (-(3 / 2 : ℝ)) ≤ ϱ ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hϱ (le_add_of_nonneg_left (sq_nonneg x)) (by norm_num)
  have e3 : ϱ ^ (-(1 / 2 : ℝ)) = ϱ * ϱ ^ (-(3 / 2 : ℝ)) := by
    rw [mul_comm, ← Real.rpow_add_one hϱ.ne']; norm_num
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), e3]
  exact mul_le_mul_of_nonneg_left hle hϱ.le

/-- Frobenius norm squared as a trace. Helper. -/
private theorem fro_sq_eq_trace {k : ℕ} (X : Matrix (Fin k) (Fin k) ℝ) : fro X ^ 2 = Matrix.trace (Xᵀ * X) := by
  rw [fro_sq_eq_sum X, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Real.norm_eq_abs, sq,
    abs_mul_abs_self]
  rw [Finset.sum_comm]

/-- The Frobenius norm is invariant under multiplication by orthogonal matrices. Helper. -/
private theorem fro_orth_conj {k : ℕ} (X U V : Matrix (Fin k) (Fin k) ℝ) (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1)
    (hV : Vᵀ * V = 1) (hV' : V * Vᵀ = 1) : fro (Uᵀ * X * V) = fro X := by
  have h2 : fro (Uᵀ * X * V) ^ 2 = fro X ^ 2 := by
    rw [fro_sq_eq_trace, fro_sq_eq_trace]
    have e : (Uᵀ * X * V)ᵀ * (Uᵀ * X * V) = Vᵀ * (Xᵀ * X) * V := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U Uᵀ, hU', Matrix.one_mul]
    rw [e, Matrix.trace_mul_comm (Vᵀ * (Xᵀ * X)) V, ← Matrix.mul_assoc V Vᵀ, hV', Matrix.one_mul]
  have hY : 0 ≤ fro (Uᵀ * X * V) := by unfold fro; exact Real.sqrt_nonneg _
  have hX : 0 ≤ fro X := by unfold fro; exact Real.sqrt_nonneg _
  exact (pow_left_inj₀ hY hX two_ne_zero).mp h2

/-- Orthogonal eigenvector matrix of a real symmetric matrix: both orthogonality relations.
Helper. -/
private theorem herm_unitary_facts {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ)ᵀ * (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ) = 1 ∧
      (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ) * (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ)ᵀ = 1 := by
  constructor
  · have h := Unitary.coe_star_mul_self hA.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  · have h := Unitary.coe_mul_star_self hA.eigenvectorUnitary
    rw [Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h

/-- Spectral form of the functional calculus of a real symmetric matrix. Helper. -/
private theorem herm_cfc_spec {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ} (hA : A.IsHermitian) (g : ℝ → ℝ) :
    cfc g A = (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ) * diagonal (fun i => g (hA.eigenvalues i)) *
      (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ)ᵀ := by
  rw [hA.cfc_eq g]
  simp [Matrix.IsHermitian.cfc, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc, Function.comp_def]

/-- Spectral decomposition of a real symmetric matrix. Helper. -/
private theorem herm_spec {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ) * diagonal (fun i => hA.eigenvalues i) *
      (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ)ᵀ := by
  refine hA.spectral_theorem.trans ?_
  simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc]

/-- Conjugation identity in the eigenbases. Helper. -/
private theorem conj_diff_ident {k : ℕ} (U V D E : Matrix (Fin k) (Fin k) ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    Uᵀ * (U * D * Uᵀ - V * E * Vᵀ) * V = D * (Uᵀ * V) - (Uᵀ * V) * E := by
  have t1 : Uᵀ * (U * D * Uᵀ) * V = D * (Uᵀ * V) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]
  have t2 : Uᵀ * (V * E * Vᵀ) * V = (Uᵀ * V) * E := by
    simp only [Matrix.mul_assoc]
    rw [hV, Matrix.mul_one]
  rw [Matrix.mul_sub, Matrix.sub_mul, t1, t2]

/-- Entrywise domination gives the Frobenius bound. Helper. -/
private theorem fro_le_of_entrywise {k : ℕ} (M N : Matrix (Fin k) (Fin k) ℝ) (L : ℝ) (hL : 0 ≤ L)
    (h : ∀ i j, |M i j| ≤ L * |N i j|) : fro M ≤ L * fro N := by
  have hS : ∑ i, ∑ j, ‖M i j‖ ^ 2 ≤ L ^ 2 * ∑ i, ∑ j, ‖N i j‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    have h1 := h i j
    have h0 := abs_nonneg (M i j)
    have h3 : |M i j| * |M i j| ≤ (L * |N i j|) * (L * |N i j|) := mul_self_le_mul_self h0 h1
    calc M i j ^ 2 = |M i j| * |M i j| := by rw [← sq_abs (M i j)]; ring
      _ ≤ (L * |N i j|) * (L * |N i j|) := h3
      _ = L ^ 2 * N i j ^ 2 := by rw [← sq_abs (N i j)]; ring
  unfold fro
  calc Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2) ≤ Real.sqrt (L ^ 2 * ∑ i, ∑ j, ‖N i j‖ ^ 2) :=
        Real.sqrt_le_sqrt hS
    _ = L * Real.sqrt (∑ i, ∑ j, ‖N i j‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL]

/-- Diagonal-in-eigenbasis form of the Frobenius divided-difference bound. Helper. -/
private theorem fro_diag_diff_le {k : ℕ} (U V : Matrix (Fin k) (Fin k) ℝ) (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1)
    (hV : Vᵀ * V = 1) (hV' : V * Vᵀ = 1) (a b : Fin k → ℝ) (f : ℝ → ℝ) (I : Set ℝ)
    (L : NNReal) (hf : LipschitzOnWith L f I) (ha : ∀ i, a i ∈ I) (hb : ∀ i, b i ∈ I) :
    fro (U * diagonal (fun i => f (a i)) * Uᵀ - V * diagonal (fun i => f (b i)) * Vᵀ)
      ≤ (L : ℝ) * fro (U * diagonal a * Uᵀ - V * diagonal b * Vᵀ) := by
  calc fro (U * diagonal (fun i => f (a i)) * Uᵀ - V * diagonal (fun i => f (b i)) * Vᵀ)
      = fro (Uᵀ * (U * diagonal (fun i => f (a i)) * Uᵀ - V * diagonal (fun i => f (b i)) * Vᵀ) * V) :=
        (fro_orth_conj _ U V hU hU' hV hV').symm
    _ = fro (diagonal (fun i => f (a i)) * (Uᵀ * V) - (Uᵀ * V) * diagonal (fun i => f (b i))) := by
        rw [conj_diff_ident U V _ _ hU hV]
    _ ≤ (L : ℝ) * fro (diagonal a * (Uᵀ * V) - (Uᵀ * V) * diagonal b) := by
        apply fro_le_of_entrywise _ _ _ L.2
        intro i j
        have hab : |f (a i) - f (b j)| ≤ (L : ℝ) * |a i - b j| := by
          have := hf.dist_le_mul (a i) (ha i) (b j) (hb j)
          simpa [Real.dist_eq] using this
        simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
        have e1 : f (a i) * (Uᵀ * V) i j - (Uᵀ * V) i j * f (b j)
            = (f (a i) - f (b j)) * (Uᵀ * V) i j := by ring
        have e2 : a i * (Uᵀ * V) i j - (Uᵀ * V) i j * b j
            = (a i - b j) * (Uᵀ * V) i j := by ring
        rw [e1, e2, abs_mul, abs_mul]
        calc |f (a i) - f (b j)| * |(Uᵀ * V) i j|
            ≤ ((L : ℝ) * |a i - b j|) * |(Uᵀ * V) i j| :=
              mul_le_mul_of_nonneg_right hab (abs_nonneg _)
          _ = (L : ℝ) * (|a i - b j| * |(Uᵀ * V) i j|) := by ring
    _ = (L : ℝ) * fro (Uᵀ * (U * diagonal a * Uᵀ - V * diagonal b * Vᵀ) * V) := by
        rw [conj_diff_ident U V _ _ hU hV]
    _ = (L : ℝ) * fro (U * diagonal a * Uᵀ - V * diagonal b * Vᵀ) := by
        rw [fro_orth_conj _ U V hU hU' hV hV']

/-- Frobenius divided-difference bound for Hermitian functional calculus: for symmetric `A`, `B`
and `f` Lipschitz with constant `L` on an interval `I` containing both spectra,
`‖f(A) − f(B)‖_F ≤ L ‖A − B‖_F` ).  -/
theorem fro_cfc_sub_cfc_le {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f : ℝ → ℝ) (I : Set ℝ) (hI : I.OrdConnected) (L : NNReal) (hf : LipschitzOnWith L f I)
    (hAI : spectrum ℝ A ⊆ I) (hBI : spectrum ℝ B ⊆ I) :
    fro (cfc f A - cfc f B) ≤ (L : ℝ) * fro (A - B) := by
  have hAB : A - B = (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ) * diagonal (fun i => hA.eigenvalues i) *
      (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ)ᵀ - (hB.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ) *
      diagonal (fun i => hB.eigenvalues i) * (hB.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ)ᵀ := by
    rw [← herm_spec hA, ← herm_spec hB]
  rw [hAB, herm_cfc_spec hA f, herm_cfc_spec hB f]
  exact fro_diag_diff_le _ _ (herm_unitary_facts hA).1 (herm_unitary_facts hA).2
    (herm_unitary_facts hB).1 (herm_unitary_facts hB).2
    (fun i => hA.eigenvalues i) (fun i => hB.eigenvalues i) f I L hf
    (fun i => hAI (hA.eigenvalues_mem_spectrum_real i))
    (fun i => hBI (hB.eigenvalues_mem_spectrum_real i))

/-- Frobenius norm is nonnegative. Helper. -/
theorem fro_nonneg {k l : ℕ} (A : Matrix (Fin k) (Fin l) ℝ) : 0 ≤ fro A := by
  unfold fro; exact Real.sqrt_nonneg _

/-- Dilation is additive in the difference. Helper. -/
theorem hermDilation_sub {m n : ℕ} (K L : Matrix (Fin m) (Fin n) ℝ) :
    hermDilation K - hermDilation L = hermDilation (K - L) := by
  unfold hermDilation
  ext i j
  simp only [Matrix.sub_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  generalize finSumFinEquiv.symm i = a
  generalize finSumFinEquiv.symm j = b
  cases a <;> cases b <;>
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.transpose_sub]

/-- Upper-right block is additive. Helper. -/
theorem upperRight_sub {m n : ℕ} (X Y : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) :
    upperRight (X - Y) = upperRight X - upperRight Y := by
  ext i j
  simp [upperRight]

/-- Functional calculus of a real symmetric matrix is symmetric. Helper. -/
theorem isHermitian_cfc {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ} (hA : A.IsHermitian) (g : ℝ → ℝ) :
    (cfc g A).IsHermitian := by
  rw [herm_cfc_spec hA g]
  unfold Matrix.IsHermitian
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.conjTranspose_eq_transpose_of_trivial]

end SpectralFoundations

end
