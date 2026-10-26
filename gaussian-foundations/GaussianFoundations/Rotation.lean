import Mathlib
import GaussianFoundations.Moments

/-!
# Foundations: rotation, sphere and Haar facts for the standard Gaussian (task L-0.5d)

Uncited standard facts used by Appendix A (`L-A.F4`: rotation invariance and the
`stdGaussianPi` ↔ `stdGaussian` bridge; 4-point Wick) and Appendix I (`L-I.0b`: Haar probability
on `O(n)`, the law of `Uv`, radius–direction independence). Source of record: snapshot
`cr-2026-10-23`.

Reused from `GaussianFoundations.Moments`, not restated: `stdGaussianPi`, the scalar moments,
`stdGaussianPi_map_coord`, `stdGaussianPi_sq_norm_moment` (`E‖g‖^{2q} = d_q(n)`),
`stdGaussian_conditional_linear`.

Declarations without a proof body carry `sorry`; proof routes are in the interface JSON.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal ENNReal

namespace GaussianFoundations

/-- Euclidean norm on `ℝⁿ = Fin n → ℝ`, written out so that it is not the sup norm. -/
noncomputable def euclidNorm (n : ℕ) (z : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, z i ^ 2)

/-- Uniform law on the unit sphere of `ℝⁿ`, realized as the law of `g / ‖g‖` for
`g ~ stdGaussianPi n`. The value at `g = 0` is `0`, a null event for `n ≥ 1`. -/
noncomputable def sphereGauss (n : ℕ) : Measure (Fin n → ℝ) :=
  (stdGaussianPi n).map (fun z => (euclidNorm n z)⁻¹ • z)

/-! ## Standard Gaussian vector: rotation invariance and bridge to `stdGaussian` -/

/-- Bridge to Mathlib's standard Gaussian on the Euclidean space: the coordinatewise
`stdGaussianPi n`, pushed forward by `WithLp.toLp 2`, is
`stdGaussian (EuclideanSpace ℝ (Fin n))`. -/
theorem stdGaussianPi_map_toLp (n : ℕ) :
    (stdGaussianPi n).map (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))
      = stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  unfold stdGaussianPi
  exact map_pi_eq_stdGaussian

/-- Private helper: the rotation `x ↦ O x` of `EuclideanSpace ℝ (Fin n)` as a linear isometry
equivalence, for `O ∈ O(n)`. -/
private noncomputable def rotE (n : ℕ) (O : Matrix.orthogonalGroup (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearEquiv.isometryOfInner
    { toFun := fun x => WithLp.toLp 2 ((O : Matrix (Fin n) (Fin n) ℝ) *ᵥ WithLp.ofLp x)
      invFun := fun x => WithLp.toLp 2 ((O : Matrix (Fin n) (Fin n) ℝ)ᵀ *ᵥ WithLp.ofLp x)
      map_add' := by
        intro x y
        ext i
        simp [Matrix.mulVec_add]
      map_smul' := by
        intro c x
        ext i
        simp [Matrix.mulVec_smul]
      left_inv := by
        intro x
        have h : (O : Matrix (Fin n) (Fin n) ℝ)ᵀ * (O : Matrix (Fin n) (Fin n) ℝ) = 1 :=
          (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 O.2
        ext i
        change ((O : Matrix (Fin n) (Fin n) ℝ)ᵀ *ᵥ
          ((O : Matrix (Fin n) (Fin n) ℝ) *ᵥ WithLp.ofLp x)) i
          = WithLp.ofLp x i
        rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
      right_inv := by
        intro x
        have h : (O : Matrix (Fin n) (Fin n) ℝ) * (O : Matrix (Fin n) (Fin n) ℝ)ᵀ = 1 :=
          (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).1 O.2
        ext i
        change ((O : Matrix (Fin n) (Fin n) ℝ) *ᵥ
          ((O : Matrix (Fin n) (Fin n) ℝ)ᵀ *ᵥ WithLp.ofLp x)) i
          = WithLp.ofLp x i
        rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec] }
    (by
      intro x y
      have h : (O : Matrix (Fin n) (Fin n) ℝ)ᵀ * (O : Matrix (Fin n) (Fin n) ℝ) = 1 :=
        (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 O.2
      simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
      simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.star_mulVec,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, h, Matrix.vecMul_one,
        dotProduct_comm])

/-- Rotation invariance: for `O ∈ O(n)`, `O g` has the same law as `g`. -/
theorem stdGaussianPi_map_orthogonal (n : ℕ) (O : Matrix.orthogonalGroup (Fin n) ℝ) :
    (stdGaussianPi n).map (fun z : Fin n → ℝ => (O : Matrix (Fin n) (Fin n) ℝ) *ᵥ z)
      = stdGaussianPi n := by
  have hrot : Measurable (rotE n O) := (rotE n O).continuous.measurable
  have hf : Measurable (fun z : Fin n → ℝ => (O : Matrix (Fin n) (Fin n) ℝ) *ᵥ z) := by
    fun_prop
  have he : Measurable (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
  have hG := stdGaussian_map (rotE n O)
  have hcomp : (WithLp.toLp 2 ∘ fun z : Fin n → ℝ => (O : Matrix (Fin n) (Fin n) ℝ) *ᵥ z)
      = (rotE n O) ∘ (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) := by
    funext z
    ext i
    simp [rotE]
  have key : ((stdGaussianPi n).map
      (fun z : Fin n → ℝ => (O : Matrix (Fin n) (Fin n) ℝ) *ᵥ z)).map (WithLp.toLp 2)
      = (stdGaussianPi n).map (WithLp.toLp 2) := by
    rw [Measure.map_map he hf, hcomp, ← Measure.map_map hrot he, stdGaussianPi_map_toLp, hG]
  exact hemb.map_injective key

/-- Private helper: exponent-product form of a monomial in the coordinates. -/
private lemma wick_four_eq_prod (n : ℕ) (i j k l : Fin n) (z : Fin n → ℝ) :
    z i * z j * z k * z l = ∏ c, z c ^ ((if c = i then 1 else 0) + (if c = j then 1 else 0)
      + (if c = k then 1 else 0) + (if c = l then 1 else 0)) := by
  simp only [pow_add, Finset.prod_mul_distrib, pow_ite, pow_one, pow_zero,
    Finset.prod_ite_eq', Finset.mem_univ, if_true]

/-- Private helper: the 4-point integral by factorization over coordinates (proof copied from
`GaussianFoundations.Moments`, where it is private). -/
private lemma wick_four_integral (n : ℕ) (i j k l : Fin n) :
    ∫ z : Fin n → ℝ, z i * z j * z k * z l ∂(stdGaussianPi n)
      = (if i = j then 1 else 0) * (if k = l then 1 else 0)
        + (if i = k then 1 else 0) * (if j = l then 1 else 0)
        + (if i = l then 1 else 0) * (if j = k then 1 else 0) := by
  simp_rw [wick_four_eq_prod]
  unfold stdGaussianPi
  rw [integral_fintype_prod_eq_prod (f := fun (c : Fin n) (x : ℝ) => x ^ ((if c = i then 1 else 0)
    + (if c = j then 1 else 0) + (if c = k then 1 else 0) + (if c = l then 1 else 0)))]
  have m0 : ∫ x : ℝ, x ^ 0 ∂(gaussianReal 0 1) = 1 := by simp
  have m1 : ∫ x : ℝ, x ^ 1 ∂(gaussianReal 0 1) = 0 := by simpa using gaussian_moment_odd 0
  have m2 : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) = 1 := gaussian_moment_two
  have m3 : ∫ x : ℝ, x ^ 3 ∂(gaussianReal 0 1) = 0 := by simpa using gaussian_moment_odd 1
  have m4 : ∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 1) = 3 := gaussian_moment_four
  by_cases hij : i = j <;> by_cases hik : i = k <;> by_cases hil : i = l <;>
    by_cases hjk : j = k <;> by_cases hjl : j = l <;> by_cases hkl : k = l <;>
    first
    | (exfalso; simp_all; done)
    | skip
  all_goals subst_vars
  all_goals have key : ∀ {a b : Fin n}, ¬ a = b → (b = a) = False := fun h => by simp [eq_comm, h]
  all_goals first
    | (refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).trans ?_
       · simp_all [key]
       · simp_all)
    | (refine (Finset.prod_eq_zero (Finset.mem_univ j) ?_).trans ?_
       · simp_all [key]
       · simp_all)
    | (refine (Finset.prod_eq_zero (Finset.mem_univ k) ?_).trans ?_
       · simp_all [key]
       · simp_all)
    | (refine (Finset.prod_eq_zero (Finset.mem_univ l) ?_).trans ?_
       · simp_all [key]
       · simp_all)
    | (refine (Finset.prod_eq_one fun c _ => ?_).trans ?_
       · split_ifs <;> simp_all [key]
       · simp_all)
    | (refine (Finset.prod_eq_single_of_mem i (Finset.mem_univ _) (fun c _ hc => ?_)).trans ?_
       · split_ifs <;> simp_all [key]
       · simp_all)
    | (refine (Finset.prod_eq_single_of_mem j (Finset.mem_univ _) (fun c _ hc => ?_)).trans ?_
       · split_ifs <;> simp_all [key]
       · simp_all)
    | (refine (Finset.prod_eq_single_of_mem k (Finset.mem_univ _) (fun c _ hc => ?_)).trans ?_
       · split_ifs <;> simp_all [key]
       · simp_all)
    | (refine (Finset.prod_eq_single_of_mem l (Finset.mem_univ _) (fun c _ hc => ?_)).trans ?_
       · split_ifs <;> simp_all [key]
       · simp_all)
    | skip
  all_goals
    refine (Finset.prod_eq_single_of_mem l (Finset.mem_univ _) (fun c _ hc => ?_)).trans ?_
  · simp [hc, m0]
  · norm_num [m4]

/-- 4-point Wick formula for iid `N(0,1)` coordinates:
`E[g_i g_j g_k g_l] = δ_ij δ_kl + δ_ik δ_jl + δ_il δ_jk`. -/
theorem stdGaussianPi_wick_four (n : ℕ) (i j k l : Fin n) :
    ∫ z : Fin n → ℝ, z i * z j * z k * z l ∂(stdGaussianPi n)
      = (if i = j then 1 else 0) * (if k = l then 1 else 0)
        + (if i = k then 1 else 0) * (if j = l then 1 else 0)
        + (if i = l then 1 else 0) * (if j = k then 1 else 0) :=
  wick_four_integral n i j k l

/-- `sphereGauss n` is a probability measure. -/
instance sphereGauss_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (sphereGauss n) := by
  unfold sphereGauss
  infer_instance

/-! ## Haar probability measure on `O(n)` -/

/-- The orthogonal group is compact: its entries are bounded by `1` and it is closed. -/
theorem orthogonalGroup_compactSpace (n : ℕ) :
    CompactSpace (Matrix.orthogonalGroup (Fin n) ℝ) := by
  have hSeq : ((Matrix.orthogonalGroup (Fin n) ℝ : Submonoid (Matrix (Fin n) (Fin n) ℝ)) :
      Set (Matrix (Fin n) (Fin n) ℝ)) = {A | A * Aᵀ = 1} :=
    Set.ext fun A => Matrix.mem_orthogonalGroup_iff (Fin n) ℝ
  have hS : IsClosed ((Matrix.orthogonalGroup (Fin n) ℝ : Submonoid (Matrix (Fin n) (Fin n) ℝ)) :
      Set (Matrix (Fin n) (Fin n) ℝ)) := by
    rw [hSeq]
    exact isClosed_eq (Continuous.matrix_mul continuous_id continuous_id.matrix_transpose)
      continuous_const
  have hK : IsCompact (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n =>
      Set.Icc (-1 : ℝ) 1 : Set (Fin n → Fin n → ℝ)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hSK : ((Matrix.orthogonalGroup (Fin n) ℝ : Submonoid (Matrix (Fin n) (Fin n) ℝ)) :
      Set (Matrix (Fin n) (Fin n) ℝ)) ⊆ (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n =>
      Set.Icc (-1 : ℝ) 1 : Set (Fin n → Fin n → ℝ)) := by
    intro A hA
    rw [hSeq] at hA
    have hA' : A * Aᵀ = 1 := hA
    have hbound : ∀ i j, A i j ∈ Set.Icc (-1 : ℝ) 1 := by
      intro i j
      have h := congrFun (congrFun hA' i) i
      rw [Matrix.mul_apply] at h
      simp only [Matrix.transpose_apply, Matrix.one_apply_eq] at h
      have hle : A i j * A i j ≤ 1 := by
        rw [← h]
        exact Finset.single_le_sum (f := fun k => A i k * A i k)
          (fun k _ => mul_self_nonneg _) (Finset.mem_univ j)
      rw [Set.mem_Icc]
      constructor <;> nlinarith
    exact Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => hbound i j
  have hcpt : IsCompact ((Matrix.orthogonalGroup (Fin n) ℝ : Submonoid (Matrix (Fin n) (Fin n) ℝ)) :
      Set (Matrix (Fin n) (Fin n) ℝ)) :=
    hK.of_isClosed_subset hS hSK
  exact isCompact_iff_compactSpace.mp hcpt

instance orthogonalGroup_compactSpace_inst (n : ℕ) :
    CompactSpace (Matrix.orthogonalGroup (Fin n) ℝ) :=
  orthogonalGroup_compactSpace n

/-- Haar probability measure on `O(n)`: the Haar measure of the compact group, normalized by
`haarMeasure K₀ K₀ = 1` with `K₀ = ⊤`, so that the total mass is `1`. -/
noncomputable def haarO (n : ℕ) : Measure (Matrix.orthogonalGroup (Fin n) ℝ) :=
  Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (Matrix.orthogonalGroup (Fin n) ℝ))

/-- `haarO n` is a probability measure. -/
instance haarO_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (haarO n) := by
  unfold haarO
  constructor
  simpa using (Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts
    (Matrix.orthogonalGroup (Fin n) ℝ))))

/-- `haarO n` is left invariant. -/
instance haarO_isMulLeftInvariant (n : ℕ) : (haarO n).IsMulLeftInvariant := by
  unfold haarO
  infer_instance

/-- Private helper: right translation by `g` fixes `haarO n`. The modular character `Δ(g)` is
defined by `map (· * g) μ = Δ(g) • μ`; evaluating at `univ` (both sides are probability
measures) gives `Δ(g) = 1`. -/
private lemma haarO_map_mul_right_eq_self (n : ℕ) (g : Matrix.orthogonalGroup (Fin n) ℝ) :
    (haarO n).map (fun h => h * g) = haarO n := by
  have hH : (haarO n).IsHaarMeasure := by
    unfold haarO
    infer_instance
  have h := Measure.map_right_mul_eq_modularCharacterFun_smul (haarO n) g
  have hu := congrArg (fun m : Measure (Matrix.orthogonalGroup (Fin n) ℝ) => m Set.univ) h
  simp only [Measure.map_apply (continuous_mul_const g).measurable MeasurableSet.univ,
    Set.preimage_univ, Measure.smul_apply, ENNReal.smul_def, measure_univ] at hu
  have hc : Measure.modularCharacterFun g = 1 := by
    have h1 : ((Measure.modularCharacterFun g : NNReal) : ENNReal) = 1 := by
      simpa using hu.symm
    exact_mod_cast h1
  rw [hc, one_smul] at h
  exact h

/-- `haarO n` is right invariant (the group is compact, hence unimodular). -/
instance haarO_isMulRightInvariant (n : ℕ) : (haarO n).IsMulRightInvariant :=
  ⟨fun g => haarO_map_mul_right_eq_self n g⟩

/-! ## Law of `Uv` and radius–direction independence -/

/-- Private helper: the squared Euclidean norm is the dot product. -/
private lemma euclidNorm_sq_eq (n : ℕ) (z : Fin n → ℝ) : euclidNorm n z ^ 2 = z ⬝ᵥ z := by
  unfold euclidNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [dotProduct, sq]

/-- Private helper: `euclidNorm = 1` iff `z ⬝ᵥ z = 1`. -/
private lemma dot_self_eq_one_of_euclidNorm (n : ℕ) (z : Fin n → ℝ) (h : euclidNorm n z = 1) :
    z ⬝ᵥ z = 1 := by
  rw [← euclidNorm_sq_eq, h]; norm_num

/-- Private helper: orthogonal matrices preserve the dot product. -/
private lemma orth_dot (n : ℕ) (R : Matrix.orthogonalGroup (Fin n) ℝ) (a b : Fin n → ℝ) :
    ((R : Matrix (Fin n) (Fin n) ℝ) *ᵥ a) ⬝ᵥ ((R : Matrix (Fin n) (Fin n) ℝ) *ᵥ b) = a ⬝ᵥ b := by
  have h : (R : Matrix (Fin n) (Fin n) ℝ)ᵀ * (R : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 R.2
  rw [← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, h,
    Matrix.vecMul_one]

/-- Private helper: orthogonal matrices preserve `euclidNorm`. -/
private lemma orth_euclidNorm (n : ℕ) (R : Matrix.orthogonalGroup (Fin n) ℝ) (z : Fin n → ℝ) :
    euclidNorm n ((R : Matrix (Fin n) (Fin n) ℝ) *ᵥ z) = euclidNorm n z := by
  have h := orth_dot n R z z
  unfold euclidNorm
  congr 1
  simpa [dotProduct, sq] using h

/-- Private helper: normalization commutes with orthogonal maps. -/
private lemma orth_normalize (n : ℕ) (R : Matrix.orthogonalGroup (Fin n) ℝ) (z : Fin n → ℝ) :
    (euclidNorm n ((R : Matrix (Fin n) (Fin n) ℝ) *ᵥ z))⁻¹ •
        ((R : Matrix (Fin n) (Fin n) ℝ) *ᵥ z)
      = (R : Matrix (Fin n) (Fin n) ℝ) *ᵥ ((euclidNorm n z)⁻¹ • z) := by
  rw [orth_euclidNorm, Matrix.mulVec_smul]

/-- Private helper: transitivity of `O(n)` on unit vectors (Householder reflection). -/
private lemma exists_orth_mulVec_eq (n : ℕ) (x v : Fin n → ℝ) (hx : euclidNorm n x = 1)
    (hv : euclidNorm n v = 1) :
    ∃ W : Matrix.orthogonalGroup (Fin n) ℝ, (W : Matrix (Fin n) (Fin n) ℝ) *ᵥ v = x := by
  have hxx := dot_self_eq_one_of_euclidNorm n x hx
  have hvv := dot_self_eq_one_of_euclidNorm n v hv
  by_cases hxv : x = v
  · exact ⟨1, by simp [hxv]⟩
  set u : Fin n → ℝ := x - v with hu
  set N : ℝ := u ⬝ᵥ u with hN
  have hN0 : N ≠ 0 := fun h => hxv (sub_eq_zero.1 ((dotProduct_self_eq_zero).1 h))
  have hNe : N = 2 - 2 * (x ⬝ᵥ v) := by
    rw [hN, hu, sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm v x, hxx, hvv]
    ring
  have huv : u ⬝ᵥ v = -(N / 2) := by
    rw [hu, sub_dotProduct, hvv]; linarith
  set P : Matrix (Fin n) (Fin n) ℝ := Matrix.vecMulVec u u with hP
  have hPP : P * P = N • P := by
    rw [hP, Matrix.vecMulVec_mul_vecMulVec]
    ext i j
    simp [Matrix.vecMulVec_apply, hN]
    ring
  have hPT : Pᵀ = P := by rw [hP, Matrix.transpose_vecMulVec]
  set W : Matrix (Fin n) (Fin n) ℝ := 1 - (2 / N) • P with hW
  have hWT : Wᵀ = W := by
    rw [hW, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hPT]
  have hWW : W * Wᵀ = 1 := by
    rw [hWT, hW, sub_mul, mul_sub, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, hPP]
    simp only [one_mul, mul_one, smul_smul]
    have h1 : (2 / N) * ((2 / N) * N) = 2 * (2 / N) := by field_simp
    rw [h1, two_mul, add_smul]
    abel
  refine ⟨⟨W, (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).2 hWW⟩, ?_⟩
  show W *ᵥ v = x
  rw [hW, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hP,
    Matrix.vecMulVec_mulVec, huv]
  have : x = v + u := by rw [hu]; abel
  conv_rhs => rw [this]
  simp only [op_smul_eq_smul, smul_smul]
  have h3 : (2 / N) * -(N / 2) = -1 := by field_simp
  rw [h3]
  simp

/-- Private helper: a fixed coordinate of the standard Gaussian vanishes with probability `0`. -/
private lemma coord_zero_null_aux (n : ℕ) (i : Fin n) :
    (stdGaussianPi n) {z : Fin n → ℝ | z i = 0} = 0 := by
  have hm : Measurable (fun z : Fin n → ℝ => z i) := measurable_pi_apply i
  have h1 : (stdGaussianPi n) ((fun z : Fin n → ℝ => z i) ⁻¹' {0}) = 0 := by
    rw [← Measure.map_apply hm (measurableSet_singleton 0), stdGaussianPi_map_coord]
    exact gaussianReal_absolutelyContinuous (0 : ℝ) (v := 1) one_ne_zero Real.volume_singleton
  simpa [Set.preimage] using h1

/-- Private helper: `∫ f(Ux) dH(U)` does not depend on the unit vector `x`. -/
private lemma haarO_integral_orbit (n : ℕ) (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) (x v : Fin n → ℝ)
    (hx : euclidNorm n x = 1) (hv : euclidNorm n v = 1) :
    ∫ U, f ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) ∂(haarO n)
      = ∫ U, f ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ v) ∂(haarO n) := by
  obtain ⟨W, hW⟩ := exists_orth_mulVec_eq n x v hx hv
  rw [← hW]
  have := integral_mul_right_eq_self
    (fun U : Matrix.orthogonalGroup (Fin n) ℝ => f ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ v)) W
    (μ := haarO n)
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  simp [Matrix.mulVec_mulVec]

/-- For `U` Haar on `O(n)` and a fixed unit vector `v`, `Uv` is uniform on the sphere, i.e. its law
is the law of `g / ‖g‖`. -/
theorem haarO_map_mulVec (n : ℕ) (v : Fin n → ℝ) (hv : euclidNorm n v = 1) :
    (haarO n).map (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ v) = sphereGauss n := by
  have hn : n ≠ 0 := by
    rintro rfl
    simp [euclidNorm] at hv
  have hc : Continuous (euclidNorm n) := by
    unfold euclidNorm
    fun_prop
  have hh : Measurable (fun z : Fin n → ℝ => (euclidNorm n z)⁻¹ • z) :=
    (hc.measurable.inv).smul measurable_id
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  have hmeasU : Measurable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ v) := by fun_prop
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hmeasU.aemeasurable f.continuous.aestronglyMeasurable]
  unfold sphereGauss
  rw [integral_map hh.aemeasurable f.continuous.aestronglyMeasurable]
  set I : ℝ := ∫ z, f ((euclidNorm n z)⁻¹ • z) ∂(stdGaussianPi n) with hI
  set J : ℝ := ∫ U, f ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ v) ∂(haarO n) with hJ
  -- step 1: invariance of the sphere law
  have step1 : ∀ U : Matrix.orthogonalGroup (Fin n) ℝ,
      ∫ z, f ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ ((euclidNorm n z)⁻¹ • z)) ∂(stdGaussianPi n)
        = I := by
    intro U
    have hφ : Measurable (fun z : Fin n → ℝ => (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ z) := by
      fun_prop
    have hf : AEStronglyMeasurable (fun z : Fin n → ℝ => f ((euclidNorm n z)⁻¹ • z))
        ((stdGaussianPi n).map (fun z : Fin n → ℝ => (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ z)) :=
      (f.continuous.measurable.comp hh).aestronglyMeasurable
    have hm := integral_map hφ.aemeasurable hf
    rw [stdGaussianPi_map_orthogonal n U] at hm
    calc ∫ z, f ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ ((euclidNorm n z)⁻¹ • z)) ∂(stdGaussianPi n)
        = ∫ z, f ((euclidNorm n ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ z))⁻¹ •
            ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ z)) ∂(stdGaussianPi n) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          simp only [orth_normalize]
      _ = I := hm.symm
  -- step 2: the inner integral over `U` is `J` almost surely
  have hnz : ∀ᵐ z ∂(stdGaussianPi n), z ≠ 0 := by
    have h0 := coord_zero_null_aux n (Classical.arbitrary (Fin n))
    have : ∀ᵐ z ∂(stdGaussianPi n), z (Classical.arbitrary (Fin n)) ≠ 0 := by
      rw [ae_iff]
      simpa using h0
    filter_upwards [this] with z hz hz0
    exact hz (by simp [hz0])
  have step2 : ∀ᵐ z ∂(stdGaussianPi n),
      ∫ U, f ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ ((euclidNorm n z)⁻¹ • z)) ∂(haarO n) = J := by
    filter_upwards [hnz] with z hz
    have hne : euclidNorm n z ≠ 0 := by
      intro h0
      have h1 := euclidNorm_sq_eq n z
      rw [h0] at h1
      exact hz (dotProduct_self_eq_zero.1 (by simpa using h1.symm))
    have hnorm : euclidNorm n ((euclidNorm n z)⁻¹ • z) = 1 := by
      have hd : ((euclidNorm n z)⁻¹ • z) ⬝ᵥ ((euclidNorm n z)⁻¹ • z) = 1 := by
        rw [smul_dotProduct, dotProduct_smul, ← euclidNorm_sq_eq]
        simp only [smul_eq_mul]
        field_simp
      have hsq := euclidNorm_sq_eq n ((euclidNorm n z)⁻¹ • z)
      rw [hd] at hsq
      have hnn : 0 ≤ euclidNorm n ((euclidNorm n z)⁻¹ • z) := Real.sqrt_nonneg _
      nlinarith
    exact haarO_integral_orbit n f _ v hnorm hv
  -- step 3: Fubini
  have hjoint : Measurable (fun p : Matrix.orthogonalGroup (Fin n) ℝ × (Fin n → ℝ) =>
      f ((p.1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ ((euclidNorm n p.2)⁻¹ • p.2))) := by
    refine f.continuous.measurable.comp ?_
    have : Measurable (fun p : Matrix.orthogonalGroup (Fin n) ℝ × (Fin n → ℝ) =>
        (euclidNorm n p.2)⁻¹ • p.2) := hh.comp measurable_snd
    fun_prop
  have hint : Integrable (Function.uncurry fun (U : Matrix.orthogonalGroup (Fin n) ℝ)
      (z : Fin n → ℝ) => f ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ ((euclidNorm n z)⁻¹ • z)))
      ((haarO n).prod (stdGaussianPi n)) := by
    refine Integrable.of_bound hjoint.aestronglyMeasurable ‖f‖ ?_
    exact Filter.Eventually.of_forall fun p => f.norm_coe_le_norm _
  have hswap := integral_integral_swap hint
  have e1 : ∫ U, ∫ z, f ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ ((euclidNorm n z)⁻¹ • z))
      ∂(stdGaussianPi n) ∂(haarO n) = I := by
    simp only [step1]
    simp
  have e2 : ∫ z, ∫ U, f ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ ((euclidNorm n z)⁻¹ • z))
      ∂(haarO n) ∂(stdGaussianPi n) = J := by
    rw [integral_congr_ae step2]
    simp
  rw [← hswap, e1] at e2
  exact e2.symm

/-- Private helper: a fixed coordinate of the standard Gaussian vector vanishes with probability `0`. -/
private lemma stdGaussianPi_coord_zero_null (n : ℕ) (i : Fin n) :
    (stdGaussianPi n) {z : Fin n → ℝ | z i = 0} = 0 := by
  have hm : Measurable (fun z : Fin n → ℝ => z i) := measurable_pi_apply i
  have h1 : (stdGaussianPi n) ((fun z : Fin n → ℝ => z i) ⁻¹' {0}) = 0 := by
    rw [← Measure.map_apply hm (measurableSet_singleton 0), stdGaussianPi_map_coord]
    exact gaussianReal_absolutelyContinuous (0 : ℝ) (v := 1) one_ne_zero Real.volume_singleton
  simpa [Set.preimage] using h1

/-- Private helper: the sphere law gives no more mass to `{z i = 0}` than the Gaussian does. -/
private lemma sphereGauss_coord_zero_le (n : ℕ) (i : Fin n) :
    sphereGauss n {z : Fin n → ℝ | z i = 0} ≤ (stdGaussianPi n) {z : Fin n → ℝ | z i = 0} := by
  have hc : Continuous (euclidNorm n) := by
    unfold euclidNorm
    fun_prop
  have hm : Measurable (fun z : Fin n → ℝ => (euclidNorm n z)⁻¹ • z) :=
    (hc.measurable.inv).smul measurable_id
  have hS : MeasurableSet {z : Fin n → ℝ | z i = 0} :=
    measurableSet_eq_fun (measurable_pi_apply i) measurable_const
  unfold sphereGauss
  rw [Measure.map_apply hm hS]
  apply measure_mono
  intro z hz
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at hz ⊢
  by_contra hne
  have hpos : 0 < ∑ j, z j ^ 2 :=
    lt_of_lt_of_le (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne)))
      (Finset.single_le_sum (f := fun j => z j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  have hnorm : euclidNorm n z ≠ 0 := by
    unfold euclidNorm
    exact (Real.sqrt_pos.2 hpos).ne'
  rcases mul_eq_zero.1 hz with h | h
  · exact (inv_ne_zero hnorm) h
  · exact hne h

/-- For `U` Haar on `O(n)` and a fixed unit `v`, almost surely no coordinate of `Uv` vanishes. -/
theorem haarO_mulVec_coord_ne_zero (n : ℕ) (v : Fin n → ℝ) (hv : euclidNorm n v = 1) :
    ∀ᵐ U : Matrix.orthogonalGroup (Fin n) ℝ ∂(haarO n),
      ∀ i : Fin n, ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ v) i ≠ 0 := by
  rw [ae_all_iff]
  intro i
  rw [ae_iff]
  have hmeas : Measurable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ v) := by
    fun_prop
  have hS : MeasurableSet {z : Fin n → ℝ | z i = 0} :=
    measurableSet_eq_fun (measurable_pi_apply i) measurable_const
  have hset : {U : Matrix.orthogonalGroup (Fin n) ℝ |
      ¬ (((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ v) i ≠ 0)}
      = (fun U : Matrix.orthogonalGroup (Fin n) ℝ => (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ v)
          ⁻¹' {z : Fin n → ℝ | z i = 0} := by
    ext U
    simp
  rw [hset]
  refine le_antisymm ?_ zero_le
  calc haarO n ((fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
          (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ v) ⁻¹' {z : Fin n → ℝ | z i = 0})
      = (haarO n).map (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
          (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ v) {z : Fin n → ℝ | z i = 0} :=
        (Measure.map_apply hmeas hS).symm
    _ = sphereGauss n {z : Fin n → ℝ | z i = 0} := by
        rw [haarO_map_mulVec n v hv]
    _ ≤ (stdGaussianPi n) {z : Fin n → ℝ | z i = 0} := sphereGauss_coord_zero_le n i
    _ = 0 := stdGaussianPi_coord_zero_null n i

/-- Private helper: `euclidNorm` is continuous. -/
private lemma euclidNorm_continuous (n : ℕ) : Continuous (euclidNorm n) := by
  unfold euclidNorm
  fun_prop

/-- Private helper: the direction map `z ↦ z / ‖z‖` (value `0` at `z = 0`) is measurable. -/
private lemma dir_measurable (n : ℕ) :
    Measurable (fun z : Fin n → ℝ => (euclidNorm n z)⁻¹ • z) :=
  ((euclidNorm_continuous n).measurable.inv).smul measurable_id

/-- Private helper: a nonzero vector has unit direction. -/
private lemma dir_unit (n : ℕ) (z : Fin n → ℝ) (hz : z ≠ 0) :
    euclidNorm n ((euclidNorm n z)⁻¹ • z) = 1 := by
  have hpos : 0 < euclidNorm n z := by
    unfold euclidNorm
    refine Real.sqrt_pos.2 ?_
    by_contra h
    apply hz
    have hsum : ∑ i, z i ^ 2 = 0 :=
      le_antisymm (not_lt.1 h) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    funext i
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (z i))).1 hsum i
      (Finset.mem_univ i)
    exact (pow_eq_zero_iff two_ne_zero).1 h2
  have hsq : euclidNorm n ((euclidNorm n z)⁻¹ • z) ^ 2 = 1 := by
    rw [euclidNorm_sq_eq]
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [← euclidNorm_sq_eq]
    field_simp
  have hnn : 0 ≤ euclidNorm n ((euclidNorm n z)⁻¹ • z) := by
    unfold euclidNorm
    exact Real.sqrt_nonneg _
  exact (pow_eq_one_iff_of_nonneg hnn two_ne_zero).1 hsq

/-- Private helper: rectangle form of radius–direction independence, for the Gaussian. -/
private lemma radius_dir_rect (n : ℕ) (A : Set ℝ) (B : Set (Fin n → ℝ))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (stdGaussianPi n) {z : Fin n → ℝ | euclidNorm n z ∈ A ∧ (euclidNorm n z)⁻¹ • z ∈ B}
      = (stdGaussianPi n) {z : Fin n → ℝ | euclidNorm n z ∈ A} * sphereGauss n B := by
  have hnm : Measurable (euclidNorm n) := (euclidNorm_continuous n).measurable
  have hθm := dir_measurable n
  have hSA : MeasurableSet {z : Fin n → ℝ | euclidNorm n z ∈ A} := hnm hA
  have hSet : MeasurableSet {z : Fin n → ℝ | euclidNorm n z ∈ A ∧ (euclidNorm n z)⁻¹ • z ∈ B} :=
    hSA.inter (hθm hB)
  -- Step 1: each rotation leaves the event's Gaussian probability unchanged
  have hrot : ∀ U : Matrix.orthogonalGroup (Fin n) ℝ,
      (stdGaussianPi n) {z : Fin n → ℝ | euclidNorm n z ∈ A ∧ (euclidNorm n z)⁻¹ • z ∈ B}
        = (stdGaussianPi n) {z : Fin n → ℝ | euclidNorm n z ∈ A ∧
            (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ ((euclidNorm n z)⁻¹ • z) ∈ B} := by
    intro U
    have hT : Measurable (fun z : Fin n → ℝ => (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ z) := by
      fun_prop
    conv_lhs => rw [← stdGaussianPi_map_orthogonal n U]
    rw [Measure.map_apply hT hSet]
    congr 1
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [orth_normalize, orth_euclidNorm]
  -- Step 2: Fubini over Haar × Gaussian
  set W : Set (Matrix.orthogonalGroup (Fin n) ℝ × (Fin n → ℝ)) :=
    {p | euclidNorm n p.2 ∈ A ∧
      (p.1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ ((euclidNorm n p.2)⁻¹ • p.2) ∈ B} with hWdef
  have hmv : Measurable (fun p : Matrix.orthogonalGroup (Fin n) ℝ × (Fin n → ℝ) =>
      (p.1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ ((euclidNorm n p.2)⁻¹ • p.2)) := by
    have h1 : Measurable (fun p : Matrix.orthogonalGroup (Fin n) ℝ × (Fin n → ℝ) =>
        (euclidNorm n p.2)⁻¹ • p.2) := (dir_measurable n).comp measurable_snd
    have h2 : Measurable (fun p : Matrix.orthogonalGroup (Fin n) ℝ × (Fin n → ℝ) =>
        (p.1 : Matrix (Fin n) (Fin n) ℝ)) :=
      (continuous_subtype_val.comp continuous_fst).measurable
    fun_prop
  have hWm : MeasurableSet W :=
    ((hnm.comp measurable_snd) hA).inter (hmv hB)
  have hI1 : (haarO n).prod (stdGaussianPi n) W = (stdGaussianPi n) {z : Fin n → ℝ |
      euclidNorm n z ∈ A ∧ (euclidNorm n z)⁻¹ • z ∈ B} := by
    rw [Measure.prod_apply hWm]
    have hfib : ∀ U : Matrix.orthogonalGroup (Fin n) ℝ,
        (stdGaussianPi n) (Prod.mk U ⁻¹' W) = (stdGaussianPi n) {z : Fin n → ℝ |
          euclidNorm n z ∈ A ∧ (euclidNorm n z)⁻¹ • z ∈ B} := fun U => (hrot U).symm
    simp only [hfib, lintegral_const, measure_univ, mul_one]
  have hI2 : (haarO n).prod (stdGaussianPi n) W
      = sphereGauss n B * (stdGaussianPi n) {z : Fin n → ℝ | euclidNorm n z ∈ A} := by
    rw [Measure.prod_apply_symm hWm]
    have hae : ∀ᵐ z ∂(stdGaussianPi n), haarO n ((fun U => (U, z)) ⁻¹' W)
        = {z : Fin n → ℝ | euclidNorm n z ∈ A}.indicator (fun _ => sphereGauss n B) z := by
      by_cases hn : n = 0
      · subst hn
        refine Filter.Eventually.of_forall (fun z => ?_)
        have hz : z = 0 := Subsingleton.elim _ _
        subst hz
        have hsg : sphereGauss 0 B = B.indicator (fun _ => (1 : ℝ≥0∞)) 0 := by
          rw [sphereGauss, Measure.map_apply (dir_measurable 0) hB]
          by_cases h0 : (0 : Fin 0 → ℝ) ∈ B
          · have hu : (fun z : Fin 0 → ℝ => (euclidNorm 0 z)⁻¹ • z) ⁻¹' B = Set.univ := by
              ext z
              simp only [Set.mem_preimage, Set.mem_univ, iff_true]
              rw [Subsingleton.elim z 0, smul_zero]
              exact h0
            rw [hu, measure_univ, Set.indicator_of_mem h0]
          · have hu : (fun z : Fin 0 → ℝ => (euclidNorm 0 z)⁻¹ • z) ⁻¹' B = ∅ := by
              ext z
              simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
              rw [Subsingleton.elim z 0, smul_zero]
              exact h0
            rw [hu, measure_empty, Set.indicator_of_notMem h0]
        have hpre : (fun U : Matrix.orthogonalGroup (Fin 0) ℝ => (U, (0 : Fin 0 → ℝ))) ⁻¹' W
            = {U : Matrix.orthogonalGroup (Fin 0) ℝ |
                euclidNorm 0 (0 : Fin 0 → ℝ) ∈ A ∧ (0 : Fin 0 → ℝ) ∈ B} := by
          ext U
          simp [hWdef]
        rw [hpre, hsg]
        by_cases hA0 : euclidNorm 0 (0 : Fin 0 → ℝ) ∈ A
        · rw [Set.indicator_of_mem (show (0 : Fin 0 → ℝ) ∈ {z : Fin 0 → ℝ | euclidNorm 0 z ∈ A}
            from hA0)]
          by_cases hB0 : (0 : Fin 0 → ℝ) ∈ B
          · have hall : {U : Matrix.orthogonalGroup (Fin 0) ℝ |
                euclidNorm 0 (0 : Fin 0 → ℝ) ∈ A ∧ (0 : Fin 0 → ℝ) ∈ B} = Set.univ :=
              Set.eq_univ_of_forall fun U => ⟨hA0, hB0⟩
            rw [hall, measure_univ, Set.indicator_of_mem hB0]
          · have hnone : {U : Matrix.orthogonalGroup (Fin 0) ℝ |
                euclidNorm 0 (0 : Fin 0 → ℝ) ∈ A ∧ (0 : Fin 0 → ℝ) ∈ B} = ∅ := by
              ext U
              exact ⟨fun h => hB0 h.2, fun h => False.elim h⟩
            rw [hnone, measure_empty, Set.indicator_of_notMem hB0]
        · rw [Set.indicator_of_notMem (show (0 : Fin 0 → ℝ) ∉ {z : Fin 0 → ℝ |
            euclidNorm 0 z ∈ A} from hA0)]
          have hnone : {U : Matrix.orthogonalGroup (Fin 0) ℝ |
              euclidNorm 0 (0 : Fin 0 → ℝ) ∈ A ∧ (0 : Fin 0 → ℝ) ∈ B} = ∅ := by
            ext U
            exact ⟨fun h => hA0 h.1, fun h => False.elim h⟩
          rw [hnone, measure_empty]
      · have hz0 : (stdGaussianPi n) {z : Fin n → ℝ | z = 0} = 0 := by
          exact measure_mono_null
            (fun z (hz : z = 0) => show z ⟨0, Nat.pos_of_ne_zero hn⟩ = 0 by rw [hz]; rfl)
            (stdGaussianPi_coord_zero_null n ⟨0, Nat.pos_of_ne_zero hn⟩)
        have hne : ∀ᵐ z ∂(stdGaussianPi n), z ≠ 0 := by
          rw [ae_iff]
          simpa using hz0
        filter_upwards [hne] with z hz
        have hf : Measurable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
            (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ ((euclidNorm n z)⁻¹ • z)) := by
          fun_prop
        by_cases hA' : euclidNorm n z ∈ A
        · rw [Set.indicator_of_mem (show z ∈ {z : Fin n → ℝ | euclidNorm n z ∈ A} from hA')]
          have hpre : (fun U : Matrix.orthogonalGroup (Fin n) ℝ => (U, z)) ⁻¹' W
              = (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
                  (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ ((euclidNorm n z)⁻¹ • z)) ⁻¹' B := by
            ext U
            simp [hWdef, hA']
          rw [hpre, ← Measure.map_apply hf hB, haarO_map_mulVec n _ (dir_unit n z hz)]
        · rw [Set.indicator_of_notMem (show z ∉ {z : Fin n → ℝ | euclidNorm n z ∈ A} from hA')]
          have hpre : (fun U : Matrix.orthogonalGroup (Fin n) ℝ => (U, z)) ⁻¹' W = ∅ := by
            ext U
            simp [hWdef, hA']
          rw [hpre, measure_empty]
    rw [lintegral_congr_ae hae, lintegral_indicator_const hSA]
  exact (hI1.symm.trans hI2).trans (mul_comm _ _)

/-- Radius–direction independence of the standard Gaussian vector: the radius `‖g‖` and the
direction `g / ‖g‖` are independent, with the direction having law `sphereGauss n`. -/
theorem stdGaussianPi_radius_direction_indep (n : ℕ) :
    (stdGaussianPi n).map (fun z : Fin n → ℝ => (euclidNorm n z, (euclidNorm n z)⁻¹ • z))
      = ((stdGaussianPi n).map (euclidNorm n)).prod (sphereGauss n) := by
  haveI : IsProbabilityMeasure (sphereGauss n) :=
    ⟨by
      unfold sphereGauss
      rw [Measure.map_apply (dir_measurable n) MeasurableSet.univ, Set.preimage_univ,
        measure_univ]⟩
  have hnm : Measurable (euclidNorm n) := (euclidNorm_continuous n).measurable
  have hΨ : Measurable (fun z : Fin n → ℝ => (euclidNorm n z, (euclidNorm n z)⁻¹ • z)) :=
    hnm.prodMk (dir_measurable n)
  symm
  apply Measure.prod_eq
  intro s t hs ht
  rw [Measure.map_apply hnm hs, Measure.map_apply hΨ (hs.prod ht)]
  exact radius_dir_rect n s t hs ht

end GaussianFoundations
