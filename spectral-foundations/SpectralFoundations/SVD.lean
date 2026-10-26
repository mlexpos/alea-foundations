import Mathlib

/-!
# Rectangular SVD and intertwining of the functional calculus

* Rectangular SVD `K = ∑_{k<rank K} s_k p_k ⊗ r_k` with orthonormal families, `s_k > 0`, and
  `s_k` the Mathlib singular values `LinearMap.singularValues` of `Matrix.toEuclideanLin K`.
* Intertwining `K f(KᵀK) = f(KKᵀ) K` for every real `f`.

Relocated from Muon `Foundations/SVD` (+ the intertwining proof from Muon `Conventions`).
Muon's `Mat m n` is `Matrix (Fin m) (Fin n) ℝ`, `Vec m` is `Fin m → ℝ`, `outer = Matrix.vecMulVec`.
-/

open scoped Matrix MatrixOrder
open Matrix

noncomputable section

namespace SpectralFoundations

/-- Bridge: the Mathlib rank of a real matrix is the dimension of the range of its Euclidean
linear map. Needed to read the positive singular values as `0 ≤ k < K.rank`. Helper; no paper
label (`CARD.md` §2, rank bridge row). Snapshot `cr-2026-10-23`. -/
theorem rank_eq_finrank_range_toEuclideanLin {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ) :
    Module.finrank ℝ (Matrix.toEuclideanLin K).range = K.rank := by
  rw [Matrix.rank_eq_finrank_range_toLin K (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis, Matrix.toEuclideanLin_eq_toLin_orthonormal]

/-- Positivity of the first `rank K` singular values: `s_k > 0` for `k < rank K`
(`CARD.md` §4, "Rectangular SVD"). Helper; no paper label. Snapshot `cr-2026-10-23`. -/
theorem singularValues_pos_of_lt_rank {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ) {k : ℕ} (hk : k < K.rank) :
    0 < (Matrix.toEuclideanLin K).singularValues k := by
  rw [LinearMap.singularValues_pos_iff_lt_finrank_range, rank_eq_finrank_range_toEuclideanLin]
  exact hk

/-- Coordinates of `toEuclideanLin` (helper, `P-A.F1.P2`). -/
private theorem toEuclideanLin_coe' {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    (Matrix.toEuclideanLin A x : Fin m → ℝ) = A *ᵥ (x : Fin n → ℝ) := by
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply]

/-- Coordinates of the adjoint (helper, `P-A.F1.P2`). -/
private theorem adjoint_coe' {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    ((Matrix.toEuclideanLin A).adjoint x : Fin n → ℝ) = Aᴴ *ᵥ (x : Fin m → ℝ) := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, toEuclideanLin_coe']

/-- Quadratic identity `(K u)·(K v) = u·(KᵀK v)` (helper, `P-A.F1.P2`). -/
private theorem dot_K_K' {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ) (u v : Fin n → ℝ) :
    (K *ᵥ u) ⬝ᵥ (K *ᵥ v) = u ⬝ᵥ ((Kᴴ * K) *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.vecMul_transpose]

/-- Rectangular SVD (`CARD.md` §4, "Rectangular SVD: `K = ∑_{k<rank} s_k p_k⊗r_k` with
orthonormal families and s_k > 0, the s_k equal to `singularValues`"). The singular values are
Mathlib's `LinearMap.singularValues` of `Matrix.toEuclideanLin K`, so the `s_k` are fixed by
`K`; the existential supplies the left and right singular families `p`, `r` (orthonormal in
`(Fin m → ℝ)` and `(Fin n → ℝ)`). Helper; no paper label. Snapshot `cr-2026-10-23`. -/
theorem svd_rect_exists {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ) :
    ∃ (p : Fin K.rank → (Fin m → ℝ)) (r : Fin K.rank → (Fin n → ℝ)),
      (∀ k l : Fin K.rank, p k ⬝ᵥ p l = if k = l then 1 else 0) ∧
      (∀ k l : Fin K.rank, r k ⬝ᵥ r l = if k = l then 1 else 0) ∧
      K = ∑ k : Fin K.rank,
        (Matrix.toEuclideanLin K).singularValues (k : ℕ) • Matrix.vecMulVec (p k) (r k) := by
  classical
  let T := Matrix.toEuclideanLin K
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hS := LinearMap.isSymmetric_adjoint_comp_self T
  let w := hS.eigenvectorBasis hn
  let μ := hS.eigenvalues hn
  have hsq : ∀ j : Fin n, μ j = T.singularValues j ^ 2 := fun j =>
    (T.sq_singularValues_fin hn j).symm
  have hev : ∀ j : Fin n, (T.adjoint ∘ₗ T) (w j) = μ j • w j := fun j =>
    hS.apply_eigenvectorBasis hn j
  -- eigen equation in coordinates
  have hAv : ∀ j : Fin n, (Kᴴ * K) *ᵥ (w j : Fin n → ℝ) = μ j • (w j : Fin n → ℝ) := by
    intro j
    have h2 := congrArg (fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) (hev j)
    simp only [LinearMap.comp_apply] at h2
    rw [adjoint_coe', toEuclideanLin_coe', Matrix.mulVec_mulVec] at h2
    simpa using h2
  -- orthonormality in coordinates
  have horth : ∀ j l : Fin n, (w j : Fin n → ℝ) ⬝ᵥ (w l : Fin n → ℝ) = if j = l then 1 else 0 := by
    intro j l
    have h := (orthonormal_iff_ite.mp w.orthonormal) j l
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    rw [dotProduct_comm, ← h]
    simp only [dotProduct, star_trivial]
  -- completeness in coordinates
  have hcomp : ∀ i k : Fin n, ∑ j, (w j : Fin n → ℝ) i * (w j : Fin n → ℝ) k
      = if i = k then 1 else 0 := by
    intro i k
    have hU := (EuclideanSpace.basisFun (Fin n) ℝ).toMatrix_orthonormalBasis_mem_unitary w
    rw [Matrix.mem_unitaryGroup_iff] at hU
    have h := congrFun (congrFun hU i) k
    rw [Matrix.mul_apply] at h
    simp only [Matrix.star_apply, star_trivial, Matrix.one_apply] at h
    simpa [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr] using h
  have hrk : K.rank ≤ n := Matrix.rank_le_width K
  have hrange : Module.finrank ℝ T.range = K.rank :=
    rank_eq_finrank_range_toEuclideanLin K
  -- vanishing beyond the rank
  have hzero : ∀ j : Fin n, K.rank ≤ (j : ℕ) → K *ᵥ (w j : Fin n → ℝ) = 0 := by
    intro j hj
    have hs0 : T.singularValues j = 0 := by
      rw [LinearMap.singularValues_eq_zero_iff_le_finrank_range, hrange]
      exact hj
    have hμ0 : μ j = 0 := by rw [hsq j, hs0]; ring
    have h1 := hAv j
    rw [hμ0, zero_smul] at h1
    have h3 := dot_K_K' K (w j : Fin n → ℝ) (w j : Fin n → ℝ)
    rw [h1, dotProduct_zero] at h3
    exact dotProduct_self_eq_zero.mp h3
  have hKK : ∀ j l : Fin n, (K *ᵥ (w j : Fin n → ℝ)) ⬝ᵥ (K *ᵥ (w l : Fin n → ℝ))
      = μ l * (if j = l then 1 else 0) := by
    intro j l
    rw [dot_K_K', hAv l, dotProduct_smul, smul_eq_mul, horth j l]
  -- the index map from Fin rank to Fin n
  let e : Fin K.rank → Fin n := fun k => Fin.castLE hrk k
  have he : ∀ k : Fin K.rank, T.singularValues ((e k : Fin n) : ℕ) = T.singularValues (k : ℕ) := by
    intro k; simp [e]
  have hpos : ∀ k : Fin K.rank, 0 < T.singularValues (k : ℕ) := fun k =>
    singularValues_pos_of_lt_rank K k.isLt
  have hμe : ∀ k : Fin K.rank, μ (e k) = T.singularValues (k : ℕ) ^ 2 := by
    intro k; rw [hsq, he]
  have hinj : ∀ k l : Fin K.rank, e k = e l ↔ k = l := by
    intro k l
    constructor
    · intro h; exact Fin.ext (by simpa [e] using congrArg Fin.val h)
    · intro h; rw [h]
  refine ⟨fun k => (T.singularValues (k : ℕ))⁻¹ • (K *ᵥ (w (e k) : Fin n → ℝ)),
    fun k => (w (e k) : Fin n → ℝ), ?_, ?_, ?_⟩
  · intro k l
    simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul]
    rw [hKK, hμe]
    simp only [hinj]
    have hk := (hpos k).ne'
    have hl := (hpos l).ne'
    by_cases h : k = l
    · subst h
      simp only [if_true]
      field_simp
    · simp [h]
  · intro k l
    rw [horth]
    simp only [hinj]
  · ext i j
    beta_reduce
    have hterm : ∀ k : Fin K.rank,
        (T.singularValues (k : ℕ) • vecMulVec ((T.singularValues (k : ℕ))⁻¹ •
          (K *ᵥ (w (e k) : Fin n → ℝ))) (w (e k) : Fin n → ℝ)) i j
        = (K *ᵥ (w (e k) : Fin n → ℝ)) i * (w (e k) : Fin n → ℝ) j := by
      intro k
      have hk := (hpos k).ne'
      simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
    have hmem : ∀ j' ∈ (Finset.univ : Finset (Fin n)),
        j' ∉ (Finset.univ : Finset (Fin K.rank)).map (Fin.castLEEmb hrk) →
        (K *ᵥ (w j' : Fin n → ℝ)) i * (w j' : Fin n → ℝ) j = 0 := by
      intro j' _ hnot
      have hj : K.rank ≤ (j' : ℕ) := by
        by_contra hlt
        push_neg at hlt
        exact hnot (Finset.mem_map.mpr ⟨⟨j', hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      rw [hzero j' hj]
      simp
    have hreindex : ∑ k : Fin K.rank, (K *ᵥ (w (e k) : Fin n → ℝ)) i * (w (e k) : Fin n → ℝ) j
        = ∑ j' : Fin n, (K *ᵥ (w j' : Fin n → ℝ)) i * (w j' : Fin n → ℝ) j := by
      rw [← Finset.sum_subset (Finset.subset_univ _) hmem, Finset.sum_map]
      rfl
    have hfin : ∑ j' : Fin n, (K *ᵥ (w j' : Fin n → ℝ)) i * (w j' : Fin n → ℝ) j = K i j := by
      simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
      rw [Finset.sum_comm]
      have hx : ∀ x : Fin n, ∑ j' : Fin n, K i x * (w j' : Fin n → ℝ) x * (w j' : Fin n → ℝ) j
          = K i x * (if x = j then 1 else 0) := by
        intro x
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum, hcomp x j]
      simp only [hx, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [Matrix.sum_apply]
    rw [Finset.sum_congr rfl (fun k _ => hterm k), hreindex, hfin]

private theorem svd_intertwine_pow_aux {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    K * (Kᵀ * K) ^ k = (K * Kᵀ) ^ k * K := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, ← Matrix.mul_assoc K, ih]
    simp only [Matrix.mul_assoc]

private theorem svd_intertwine_aeval_aux {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ) (q : Polynomial ℝ) :
    K * Polynomial.aeval (Kᵀ * K) q = Polynomial.aeval (K * Kᵀ) q * K := by
  induction q using Polynomial.induction_on with
  | C a =>
    rw [Polynomial.aeval_C, Polynomial.aeval_C]
    simp [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul]
  | add p q hp hq => rw [map_add, map_add, Matrix.mul_add, Matrix.add_mul, hp, hq]
  | monomial k a ih =>
    simp only [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
    have hc : K * algebraMap ℝ (Matrix (Fin n) (Fin n) ℝ) a = algebraMap ℝ (Matrix (Fin m) (Fin m) ℝ) a * K := by
      simp [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul]
    rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc, svd_intertwine_pow_aux K (k + 1)]
    simp only [Matrix.mul_assoc]

/-- Intertwining `K f(KᵀK) = f(KKᵀ) K` for every real function `f` (the identity that makes
`Q_ϱ(K) = K φ_ϱ(KᵀK)` equal `(KKᵀ+ϱ)^{-1/2} K`; `section.tex` l.273–275, "the sum does not
depend on the choice of decomposition"). Holds for all `f` because both spectra are finite
(`Matrix.finite_real_spectrum`), so the functional calculus reduces to a polynomial
interpolant on the union of the two spectra. -/
theorem cfc_intertwine_rect {m n : ℕ} (f : ℝ → ℝ) (K : Matrix (Fin m) (Fin n) ℝ) :
    K * cfc f (Kᵀ * K) = cfc f (K * Kᵀ) * K := by
  classical
  have hA : (spectrum ℝ (Kᵀ * K)).Finite := Matrix.finite_real_spectrum
  have hB : (spectrum ℝ (K * Kᵀ)).Finite := Matrix.finite_real_spectrum
  have hsaA : IsSelfAdjoint (Kᵀ * K) := by
    have h := Matrix.isHermitian_conjTranspose_mul_self K
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hsaB : IsSelfAdjoint (K * Kᵀ) := by
    have h := Matrix.isHermitian_mul_conjTranspose_self K
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  set s : Finset ℝ := (hA.union hB).toFinset with hs
  have hinj : Set.InjOn (id : ℝ → ℝ) (s : Set ℝ) := Set.injOn_id _
  set p : Polynomial ℝ := Lagrange.interpolate s id f with hp
  have hAp : ∀ x ∈ spectrum ℝ (Kᵀ * K), f x = p.eval x := by
    intro x hx
    have hxs : x ∈ s := by simp [hs, hx]
    have := Lagrange.eval_interpolate_at_node (s := s) (v := id) (r := f) hinj hxs
    simpa [hp] using this.symm
  have hBp : ∀ x ∈ spectrum ℝ (K * Kᵀ), f x = p.eval x := by
    intro x hx
    have hxs : x ∈ s := by simp [hs, hx]
    have := Lagrange.eval_interpolate_at_node (s := s) (v := id) (r := f) hinj hxs
    simpa [hp] using this.symm
  rw [cfc_congr' hAp, cfc_congr' hBp, cfc_polynomial p (Kᵀ * K) hsaA,
    cfc_polynomial p (K * Kᵀ) hsaB]
  exact svd_intertwine_aeval_aux K p

end SpectralFoundations

end
