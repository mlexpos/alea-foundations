import GaussianFoundations.Defs

/-!
# Gaussian integration by parts (Stein's lemma)

Frozen interface. Statements and definitions are final; every proof is `sorry` unless it is a
one-line consequence of another declaration of this file.

Contents, from scalar to matrix:
* `HasPolyGrowth f`: `‖f x‖ ≤ C (1 + ‖x‖ ^ k)`, the growth class in which all Stein identities
  below are stated, with a small closure/integrability API.
* One dimension: `stein_std_of_integrable` (integrability hypotheses), `stein_std` /
  `stein_std_real` (polynomial growth), `stein_gaussianReal` / `stein_gaussianReal_real`
  (`N(μ, v)`), `stein_hasLaw` (random-variable form).
* Product Gaussian on `ι → ℝ`: `stein_pi_of_integrable`, `stein_pi_of_hasDerivAt` (only a
  continuous partial derivative in the active coordinate), `stein_pi`; Euclidean bridges
  `stein_euclidean` (on `stdGaussian (EuclideanSpace ℝ ι)`) and the coordinate-free
  `stein_stdGaussian`; random-vector form `stein_isStdGaussianVector`.
* Gaussian matrices: the entrywise equivalence `vecOfMat` / `matOfVec`, the entrywise partial
  derivative `matPartial F i j X = d/dt F (X + t E_ij)|_{t=0}`, and `stein_matrix`,
  `stein_matrix_real` for `IsIIDGaussianMatrix`.
* Covariance forms: `stein_multivariateGaussian` (Mathlib's `multivariateGaussian μ S`) and
  `stein_linear_image` (`ξ = A z`, covariance `A Aᵀ`).

Hypothesis choices:
* Functions take values in an arbitrary real normed space `E` (so `ℂ`-valued resolvent traces
  are covered); `x • f x` is scalar multiplication by the real coordinate. No `CompleteSpace E`
  is needed: when `E` is not complete both Bochner integrals vanish.
* Primary hypotheses are `ContDiff ℝ 1 f` plus polynomial growth of `f` and of the relevant
  partial derivative. These are pointwise, closed under the algebraic operations used in
  random-matrix proofs, and restrict to every one-dimensional slice, which is what the Fubini
  reduction needs. The integrability versions (`*_of_integrable`) are the weaker forms the
  growth versions are derived from.
* Matrices carry no global norm in Mathlib, so smoothness and growth of `F : Matrix → E` are
  stated for the vectorisation `fun x => F (matOfVec x)` on `Fin p × Fin q → ℝ` (sup norm), and
  the partial derivative is a line derivative, which needs no norm on matrices.
  `matPartial_eq_fderiv` identifies it with `fderiv` under `Matrix.Norms.Elementwise`, and
  `contDiff_comp_matOfVec` / `HasPolyGrowth.comp_matOfVec` (with `_frobenius`, `_l2Op` variants)
  discharge the vectorised hypotheses from smoothness and growth under a matrix norm.

Existing material: Mathlib has no Gaussian IBP/Stein lemma. It provides the real-line IBP
`integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable`, `gaussianPDFReal`,
`stdGaussian`, `map_pi_eq_stdGaussian`, `multivariateGaussian`, `lineDeriv`, `HasLaw` and
Fernique's moment bounds `IsGaussian.memLp_id`. SLT has none either. Muon proves the 1-D case
`Muon.Foundations.gaussian_stein` (real-valued, polynomial growth) and a private coordinate
version `st_stein_pi` (`Muon/DetEquiv/Gaussian.lean`), whose proofs transfer to
`stein_std_real` and `stein_pi_of_hasDerivAt`. Both Muon statements are direct corollaries:
`gaussian_stein` is `stein_std_real` (growth by `hasPolyGrowth_real_iff`, i.e. `Iff.rfl`), and
`st_stein_pi` is `stein_pi_of_hasDerivAt` with growth by `HasPolyGrowth.of_le_sum_sq`.
-/

namespace GaussianFoundations

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace Matrix

/-! ## Polynomial growth -/

/-- `f` has polynomial growth: `‖f x‖ ≤ C (1 + ‖x‖ ^ k)` for some `C : ℝ` and `k : ℕ`. The class
does not change when the norm on the domain is replaced by an equivalent one. -/
def HasPolyGrowth {α β : Type*} [Norm α] [Norm β] (f : α → β) : Prop :=
  ∃ C : ℝ, ∃ k : ℕ, ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖ ^ k)

/-- On `ℝ → ℝ`, `HasPolyGrowth` is exactly the hypothesis of `Muon.Foundations.gaussian_stein`. -/
lemma hasPolyGrowth_real_iff (f : ℝ → ℝ) :
    HasPolyGrowth f ↔ ∃ C : ℝ, ∃ k : ℕ, ∀ x, |f x| ≤ C * (1 + |x| ^ k) := Iff.rfl

/-- Bounded functions have polynomial growth (`k = 0`, `C = max C 0`). -/
lemma HasPolyGrowth.of_bounded {α β : Type*} [Norm α] [Norm β] {f : α → β} (C : ℝ)
    (h : ∀ x, ‖f x‖ ≤ C) : HasPolyGrowth f := by
  refine ⟨max C 0, 0, fun x => ?_⟩
  simp only [pow_zero]
  have hC : C ≤ max C 0 := le_max_left _ _
  have hC' : 0 ≤ max C 0 := le_max_right _ _
  nlinarith [h x]

private lemma poly_bound_normalize (C s : ℝ) (k : ℕ) :
    C * (1 + s ^ k) ≤ 2 * |C| * (1 + s ^ (2 * k)) := by
  have hy : 0 ≤ |s ^ k| := abs_nonneg _
  have hy' : |s ^ k| ≤ 1 + |s ^ k| ^ 2 := by
    nlinarith [sq_nonneg (|s ^ k| - (1 / 2 : ℝ))]
  calc
    C * (1 + s ^ k) ≤ |C * (1 + s ^ k)| := le_abs_self _
    _ = |C| * |1 + s ^ k| := abs_mul _ _
    _ ≤ |C| * (1 + |s ^ k|) := by
      gcongr
      simpa [Real.norm_eq_abs] using norm_add_le (1 : ℝ) (s ^ k)
    _ ≤ |C| * (2 * (1 + |s ^ k| ^ 2)) := by gcongr; nlinarith
    _ = 2 * |C| * (1 + s ^ (2 * k)) := by
      have hs : |s| ^ k * |s| ^ k = s ^ (2 * k) := by
        rw [← pow_two, ← pow_mul, Nat.mul_comm, pow_mul, sq_abs]
        exact (pow_mul s 2 k).symm
      rw [abs_pow, pow_two, hs]
      ring

private lemma pow_le_one_add_pow_of_le (t : ℝ) (ht : 0 ≤ t) {a b : ℕ} (hab : a ≤ b) :
    t ^ a ≤ 1 + t ^ b := by
  rcases le_total t 1 with h | h
  · exact (pow_le_one₀ ht h).trans (le_add_of_nonneg_right (by positivity))
  · exact (pow_le_pow_right₀ h hab).trans (le_add_of_nonneg_left (by positivity))

/-- Sums: take `k = max k₁ k₂` and `C = 2 (|C₁| + |C₂|)`, using `‖x‖ ^ kᵢ ≤ 1 + ‖x‖ ^ k`.
Caution for the proof: `[Norm α]` does not force `0 ≤ ‖x‖`, so the bound `‖x‖ ^ kᵢ ≤ 1 + ‖x‖ ^ k`
must be run with `|‖x‖|`; e.g. first normalise each bound to
`‖f x‖ ≤ 2 |C| (1 + ‖x‖ ^ (2 k))` (even exponent, `|s| ^ k ≤ 1 + s ^ (2 k)`). The statement is
true for every `Norm α`. -/
lemma HasPolyGrowth.add {α β : Type*} [Norm α] [SeminormedAddCommGroup β] {f g : α → β}
    (hf : HasPolyGrowth f) (hg : HasPolyGrowth g) : HasPolyGrowth (fun x => f x + g x) := by
  rcases hf with ⟨Cf, kf, hf⟩
  rcases hg with ⟨Cg, kg, hg⟩
  refine ⟨4 * (|Cf| + |Cg|), 2 * max kf kg, fun x => ?_⟩
  have hf' : ‖f x‖ ≤ 2 * |Cf| * (1 + ‖x‖ ^ (2 * kf)) :=
    (hf x).trans (poly_bound_normalize Cf ‖x‖ kf)
  have hg' : ‖g x‖ ≤ 2 * |Cg| * (1 + ‖x‖ ^ (2 * kg)) :=
    (hg x).trans (poly_bound_normalize Cg ‖x‖ kg)
  have hx : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
  have hfk : (‖x‖ ^ 2) ^ kf ≤ 1 + (‖x‖ ^ 2) ^ max kf kg :=
    pow_le_one_add_pow_of_le _ hx (le_max_left _ _)
  have hgk : (‖x‖ ^ 2) ^ kg ≤ 1 + (‖x‖ ^ 2) ^ max kf kg :=
    pow_le_one_add_pow_of_le _ hx (le_max_right _ _)
  have hff : 2 * |Cf| * (1 + (‖x‖ ^ 2) ^ kf) ≤
      4 * |Cf| * (1 + (‖x‖ ^ 2) ^ max kf kg) := by
    have : 1 + (‖x‖ ^ 2) ^ kf ≤ 2 * (1 + (‖x‖ ^ 2) ^ max kf kg) := by
      nlinarith [show 0 ≤ (‖x‖ ^ 2) ^ max kf kg by positivity]
    calc
      _ ≤ 2 * |Cf| * (2 * (1 + (‖x‖ ^ 2) ^ max kf kg)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have hgg : 2 * |Cg| * (1 + (‖x‖ ^ 2) ^ kg) ≤
      4 * |Cg| * (1 + (‖x‖ ^ 2) ^ max kf kg) := by
    have : 1 + (‖x‖ ^ 2) ^ kg ≤ 2 * (1 + (‖x‖ ^ 2) ^ max kf kg) := by
      nlinarith [show 0 ≤ (‖x‖ ^ 2) ^ max kf kg by positivity]
    calc
      _ ≤ 2 * |Cg| * (2 * (1 + (‖x‖ ^ 2) ^ max kf kg)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  calc
    ‖f x + g x‖ ≤ ‖f x‖ + ‖g x‖ := norm_add_le _ _
    _ ≤ 2 * |Cf| * (1 + ‖x‖ ^ (2 * kf)) +
        2 * |Cg| * (1 + ‖x‖ ^ (2 * kg)) := add_le_add hf' hg'
    _ ≤ 4 * (|Cf| + |Cg|) * (1 + ‖x‖ ^ (2 * max kf kg)) := by
      rw [show ‖x‖ ^ (2 * kf) = (‖x‖ ^ 2) ^ kf by rw [pow_mul],
        show ‖x‖ ^ (2 * kg) = (‖x‖ ^ 2) ^ kg by rw [pow_mul],
        show ‖x‖ ^ (2 * max kf kg) = (‖x‖ ^ 2) ^ max kf kg by rw [pow_mul]]
      calc
        _ ≤ 4 * |Cf| * (1 + (‖x‖ ^ 2) ^ max kf kg) +
            4 * |Cg| * (1 + (‖x‖ ^ 2) ^ max kf kg) := add_le_add hff hgg
        _ = _ := by ring

/-- Products by a real scalar function: take `k = k₁ + k₂`, using `‖a • v‖ = |a| ‖v‖` and
`(1 + s ^ k₁)(1 + s ^ k₂) ≤ 3 (1 + s ^ (k₁ + k₂))` for `s ≥ 0`. As in `HasPolyGrowth.add`,
`‖x‖` may be negative under a bare `[Norm α]`: normalise to `|C|` and even exponents first. -/
lemma HasPolyGrowth.smul {α E : Type*} [Norm α] [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {a : α → ℝ} {f : α → E} (ha : HasPolyGrowth a) (hf : HasPolyGrowth f) :
    HasPolyGrowth (fun x => a x • f x) := by
  rcases ha with ⟨Ca, ka, ha⟩
  rcases hf with ⟨Cf, kf, hf⟩
  refine ⟨16 * |Ca| * |Cf|, 2 * (ka + kf), fun x => ?_⟩
  have ha' : |a x| ≤ 2 * |Ca| * (1 + ‖x‖ ^ (2 * ka)) :=
    (ha x).trans (poly_bound_normalize Ca ‖x‖ ka)
  have hf' : ‖f x‖ ≤ 2 * |Cf| * (1 + ‖x‖ ^ (2 * kf)) :=
    (hf x).trans (poly_bound_normalize Cf ‖x‖ kf)
  have ht : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
  have hka : (‖x‖ ^ 2) ^ ka ≤ 1 + (‖x‖ ^ 2) ^ (ka + kf) :=
    pow_le_one_add_pow_of_le _ ht (Nat.le_add_right _ _)
  have hkf : (‖x‖ ^ 2) ^ kf ≤ 1 + (‖x‖ ^ 2) ^ (ka + kf) :=
    pow_le_one_add_pow_of_le _ ht (Nat.le_add_left _ _)
  have hprod : (1 + (‖x‖ ^ 2) ^ ka) * (1 + (‖x‖ ^ 2) ^ kf) ≤
      4 * (1 + (‖x‖ ^ 2) ^ (ka + kf)) := by
    rw [show (‖x‖ ^ 2) ^ (ka + kf) =
      (‖x‖ ^ 2) ^ ka * (‖x‖ ^ 2) ^ kf by rw [pow_add]] at *
    nlinarith [show 0 ≤ (‖x‖ ^ 2) ^ ka by positivity,
      show 0 ≤ (‖x‖ ^ 2) ^ kf by positivity]
  rw [norm_smul, Real.norm_eq_abs]
  calc
    |a x| * ‖f x‖ ≤ (2 * |Ca| * (1 + ‖x‖ ^ (2 * ka))) *
        (2 * |Cf| * (1 + ‖x‖ ^ (2 * kf))) :=
      mul_le_mul ha' hf' (norm_nonneg _) (le_trans (abs_nonneg _) ha')
    _ ≤ 16 * |Ca| * |Cf| * (1 + ‖x‖ ^ (2 * (ka + kf))) := by
      rw [show ‖x‖ ^ (2 * ka) = (‖x‖ ^ 2) ^ ka by rw [pow_mul],
        show ‖x‖ ^ (2 * kf) = (‖x‖ ^ 2) ^ kf by rw [pow_mul],
        show ‖x‖ ^ (2 * (ka + kf)) = (‖x‖ ^ 2) ^ (ka + kf) by rw [pow_mul]]
      calc
        _ = 4 * |Ca| * |Cf| *
            ((1 + (‖x‖ ^ 2) ^ ka) * (1 + (‖x‖ ^ 2) ^ kf)) := by ring
        _ ≤ 4 * |Ca| * |Cf| * (4 * (1 + (‖x‖ ^ 2) ^ (ka + kf))) := by
          gcongr
        _ = _ := by ring

/-- Precomposition with a continuous linear map: `‖L x‖ ≤ ‖L‖ ‖x‖`, so
`1 + ‖L x‖ ^ k ≤ max 1 ‖L‖ ^ k (1 + ‖x‖ ^ k)`. -/
lemma HasPolyGrowth.comp_continuousLinearMap {V W β : Type*} [SeminormedAddCommGroup V]
    [NormedSpace ℝ V] [SeminormedAddCommGroup W] [NormedSpace ℝ W] [Norm β] {f : W → β}
    (hf : HasPolyGrowth f) (L : V →L[ℝ] W) : HasPolyGrowth (fun x => f (L x)) := by
  rcases hf with ⟨C, k, hC⟩
  let K : ℝ := max 1 (‖L‖ ^ k)
  refine ⟨|C| * K, k, fun x => (hC (L x)).trans ?_⟩
  have hL : ‖L x‖ ^ k ≤ (‖L‖ * ‖x‖) ^ k :=
    pow_le_pow_left₀ (norm_nonneg _) (L.le_opNorm x) k
  have hK_one : 1 ≤ K := le_max_left _ _
  have hK_L : ‖L‖ ^ k ≤ K := le_max_right _ _
  have hxk : 0 ≤ ‖x‖ ^ k := by positivity
  calc
    C * (1 + ‖L x‖ ^ k) ≤ |C| * (1 + ‖L x‖ ^ k) := by
      gcongr
      exact le_abs_self C
    _ ≤ |C| * (1 + (‖L‖ * ‖x‖) ^ k) := by gcongr
    _ = |C| * (1 + ‖L‖ ^ k * ‖x‖ ^ k) := by rw [mul_pow]
    _ ≤ |C| * (K * (1 + ‖x‖ ^ k)) := by
      gcongr
      calc
        1 + ‖L‖ ^ k * ‖x‖ ^ k ≤ K + K * ‖x‖ ^ k :=
          add_le_add hK_one (mul_le_mul_of_nonneg_right hK_L hxk)
        _ = K * (1 + ‖x‖ ^ k) := by ring
    _ = (|C| * K) * (1 + ‖x‖ ^ k) := by ring

/-- Coordinate functions have polynomial growth: `|x i| ≤ ‖x‖ ≤ 1 · (1 + ‖x‖ ^ 1)`
(`norm_le_pi_norm`). Combined with `HasPolyGrowth.smul` this gives growth of `x ↦ x i • f x`,
e.g. of `X ↦ Xᵢⱼ F(X)` through `matOfVec`. -/
lemma hasPolyGrowth_apply {ι : Type*} [Fintype ι] (i : ι) :
    HasPolyGrowth (fun x : ι → ℝ => x i) := by
  refine ⟨1, 1, fun x => ?_⟩
  simp only [Real.norm_eq_abs, one_mul, pow_one]
  exact (norm_le_pi_norm x i).trans (le_add_of_nonneg_left (by positivity))

/-- Muon-style growth bounds `‖f x‖ ≤ K (1 + ∑ᵢ xᵢ²) ^ p` (as in the private `st_stein_pi`,
`Muon/DetEquiv/Gaussian.lean`) give polynomial growth in the sup norm.
Proof: if `K < 0` then `‖f x‖ ≤ 0`, take `C = 0`. Otherwise `∑ᵢ xᵢ² ≤ card ι · ‖x‖ ^ 2`, so
`(1 + ∑ᵢ xᵢ²) ^ p ≤ (1 + card ι) ^ p (1 + ‖x‖ ^ 2) ^ p ≤ (1 + card ι) ^ p 2 ^ p (1 + ‖x‖ ^ (2 p))`;
take `k = 2 p`. -/
lemma HasPolyGrowth.of_le_sum_sq {ι β : Type*} [Fintype ι] [Norm β] {f : (ι → ℝ) → β} (K : ℝ)
    (p : ℕ) (h : ∀ x, ‖f x‖ ≤ K * (1 + ∑ i, x i ^ 2) ^ p) : HasPolyGrowth f := by
  by_cases hK : 0 ≤ K
  · refine ⟨K * (1 + Fintype.card ι) ^ p * 2 ^ (p - 1), 2 * p, fun x => ?_⟩
    have hsum : (∑ i, x i ^ 2) ≤ (Fintype.card ι : ℝ) * ‖x‖ ^ 2 := by
      calc
        (∑ i, x i ^ 2) ≤ ∑ _i : ι, ‖x‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          have hi := norm_le_pi_norm x i
          rw [Real.norm_eq_abs] at hi
          simpa [sq_abs] using
            (sq_le_sq₀ (abs_nonneg (x i)) (norm_nonneg x)).2 hi
        _ = (Fintype.card ι : ℝ) * ‖x‖ ^ 2 := by simp
    have hbase : 1 + ∑ i, x i ^ 2 ≤
        (1 + Fintype.card ι) * (1 + ‖x‖ ^ 2) := by
      have hc : 0 ≤ (Fintype.card ι : ℝ) := by positivity
      nlinarith [sq_nonneg ‖x‖]
    have hpbase := pow_le_pow_left₀ (by positivity) hbase p
    have hadd : (1 + ‖x‖ ^ 2) ^ p ≤
        2 ^ (p - 1) * (1 + (‖x‖ ^ 2) ^ p) := by
      simpa using add_pow_le (a := (1 : ℝ)) (b := ‖x‖ ^ 2)
        (by positivity) (sq_nonneg ‖x‖) p
    calc
      ‖f x‖ ≤ K * (1 + ∑ i, x i ^ 2) ^ p := h x
      _ ≤ K * ((1 + Fintype.card ι) * (1 + ‖x‖ ^ 2)) ^ p := by gcongr
      _ = K * (1 + Fintype.card ι) ^ p * (1 + ‖x‖ ^ 2) ^ p := by rw [mul_pow]; ring
      _ ≤ K * (1 + Fintype.card ι) ^ p *
          (2 ^ (p - 1) * (1 + (‖x‖ ^ 2) ^ p)) := by gcongr
      _ = (K * (1 + Fintype.card ι) ^ p * 2 ^ (p - 1)) *
          (1 + ‖x‖ ^ (2 * p)) := by rw [pow_mul]; ring
  · refine ⟨0, 0, fun x => ?_⟩
    have hneg : K < 0 := lt_of_not_ge hK
    have hs : 0 ≤ (1 + ∑ i, x i ^ 2) ^ p := by positivity
    calc
      ‖f x‖ ≤ K * (1 + ∑ i, x i ^ 2) ^ p := h x
      _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg.le hs
      _ = 0 * (1 + ‖x‖ ^ 0) := by simp

/-- Polynomially growing a.e.-strongly measurable functions are integrable for any Gaussian
measure on a separable Banach space (`gaussianReal`, `stdGaussian`, `multivariateGaussian`):
dominate by `C (1 + ‖x‖ ^ k)`, integrable by Fernique (`IsGaussian.memLp_id` with `p = k`). -/
lemma HasPolyGrowth.integrable_of_isGaussian {V E : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]
    [SecondCountableTopology V] [NormedAddCommGroup E] {f : V → E} (hf : HasPolyGrowth f)
    (μ : Measure V) [IsGaussian μ] (hm : AEStronglyMeasurable f μ) : Integrable f μ := by
  rcases hf with ⟨C, k, h⟩
  have hk : Integrable (fun x : V => ‖x‖ ^ k) μ :=
    (IsGaussian.memLp_id μ k (by simp)).integrable_norm_pow'
  have hdom : Integrable (fun x : V => |C| * (1 + ‖x‖ ^ k)) μ :=
    ((integrable_const (1 : ℝ)).add hk).const_mul |C|
  refine hdom.mono' hm (ae_of_all _ fun x => ?_)
  exact (h x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))

/-- Polynomially growing a.e.-strongly measurable functions are integrable for the product
Gaussian on `ι → ℝ`: the sup norm satisfies `‖x‖ ^ k ≤ 1 + ∑ i, |x i| ^ k`, and each `|x i| ^ k` is
integrable (`memLp_id_gaussianReal` on the `i`-th marginal). -/
lemma HasPolyGrowth.integrable_pi {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    {f : (ι → ℝ) → E} (hf : HasPolyGrowth f)
    (hm : AEStronglyMeasurable f (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    Integrable f (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  rcases hf with ⟨C, k, h⟩
  let μ : Measure (ι → ℝ) := Measure.pi fun _ : ι => gaussianReal 0 1
  have hi (i : ι) : Integrable (fun x : ι → ℝ => |x i| ^ k) μ := by
    have hk : Integrable (fun x : ℝ => ‖x‖ ^ k) (gaussianReal 0 1) :=
      (memLp_id_gaussianReal (μ := 0) (v := 1) k).integrable_norm_pow'
    simpa only [Real.norm_eq_abs] using
      (integrable_comp_eval (μ := fun _ : ι => gaussianReal 0 1) (i := i) hk)
  have hsum : Integrable (fun x : ι → ℝ => ∑ i, |x i| ^ k) μ :=
    integrable_finsetSum _ fun i _ => hi i
  have hnorm (x : ι → ℝ) : ‖x‖ ^ k ≤ 1 + ∑ i, |x i| ^ k := by
    cases isEmpty_or_nonempty ι with
    | inl hι =>
      simp only [Subsingleton.elim x 0, norm_zero]
      by_cases hk : k = 0
      · simp [hk]
      · simp [zero_pow hk]
    | inr hι =>
      let _ := hι
      rcases (IsGreatest.pi_norm x).1 with ⟨i, hi⟩
      rw [← hi]
      change |x i| ^ k ≤ 1 + ∑ i, |x i| ^ k
      exact (Finset.single_le_sum (s := Finset.univ) (f := fun j => |x j| ^ k)
        (fun j _ => pow_nonneg (abs_nonneg _) _) (Finset.mem_univ i)).trans
        (le_add_of_nonneg_left (by positivity))
  have hdom : Integrable (fun x : ι → ℝ => |C| * (2 + ∑ i, |x i| ^ k)) μ :=
    ((integrable_const (2 : ℝ)).add hsum).const_mul |C|
  refine hdom.mono' hm (ae_of_all _ fun x => ?_)
  exact (h x).trans <| (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans <|
    mul_le_mul_of_nonneg_left (by linarith [hnorm x]) (abs_nonneg C)

/-! ## One-dimensional Stein lemma -/

section OneDim

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private lemma stein_pdf_eq (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ *
      Real.exp (-((1 / 2 : ℝ) * x ^ 2)) := by
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  congr 2
  ring

private lemma stein_pdf_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have hfun : gaussianPDFReal 0 1 = fun y : ℝ =>
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((1 / 2 : ℝ) * y ^ 2)) :=
    funext stein_pdf_eq
  have h1 : HasDerivAt (fun y : ℝ => -((1 / 2 : ℝ) * y ^ 2)) (-x) x := by
    have h := ((hasDerivAt_pow 2 x).const_mul (1 / 2 : ℝ)).neg
    convert h using 1
    · ring_nf
  have h2 := (h1.exp).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  rw [hfun]
  dsimp only
  convert h2 using 1
  ring

private lemma stein_pdf_integrable_smul_iff (f : ℝ → E) :
    Integrable (fun x => gaussianPDFReal 0 1 x • f x) ↔
      Integrable f (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [toReal_gaussianPDF]

private lemma gaussian_pdf_hasDerivAt (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal μ v)
      (-((x - μ) / (v : ℝ)) * gaussianPDFReal μ v x) x := by
  have hvR : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have hfun : gaussianPDFReal μ v = fun y : ℝ =>
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
        Real.exp (-((y - μ) ^ 2 / (2 * (v : ℝ)))) := by
    funext y
    rw [gaussianPDFReal_def]
    change (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
      Real.exp (-((y - μ) ^ 2) / (2 * (v : ℝ))) = _
    ring
  have h1 : HasDerivAt (fun y : ℝ => -((y - μ) ^ 2 / (2 * (v : ℝ))))
      (-((x - μ) / (v : ℝ))) x := by
    have h := (((hasDerivAt_id x).sub_const μ).pow 2).neg.div_const (2 * (v : ℝ))
    convert h using 1
    · funext y
      change -((y - μ) ^ 2 / (2 * (v : ℝ))) =
        -((y - μ) ^ 2) / (2 * (v : ℝ))
      ring
    · simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, id_eq]
      field_simp [hvR]
  have h2 := (h1.exp).const_mul (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
  rw [hfun]
  dsimp only
  convert h2 using 1
  ring

private lemma gaussian_pdf_integrable_smul_iff (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (f : ℝ → E) :
    Integrable (fun x => gaussianPDFReal μ v x • f x) ↔ Integrable f (gaussianReal μ v) := by
  rw [gaussianReal_of_var_ne_zero μ hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF μ v)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [toReal_gaussianPDF]

/-- Stein's lemma for `g ∼ N(0,1)`, integrability form: for differentiable `f : ℝ → E` with
`x • f x` and `f'` integrable, `E[g f(g)] = E[f'(g)]`.
Proof: write both sides against the density `φ = gaussianPDFReal 0 1`, use `φ' = -x φ`, and
apply `integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable` with `L = lsmul`. The
missing integrability of `φ f` follows from continuity of `f` on `[-1,1]` and `‖f‖ ≤ ‖x • f‖`
off it. (Muon's `gaussian_stein` is this argument for `E = ℝ`.) -/
theorem stein_std_of_integrable {f : ℝ → E} (hf : Differentiable ℝ f)
    (h1 : Integrable (fun x => x • f x) (gaussianReal 0 1))
    (h2 : Integrable (deriv f) (gaussianReal 0 1)) :
    ∫ x, x • f x ∂(gaussianReal 0 1) = ∫ x, deriv f x ∂(gaussianReal 0 1) := by
  have hfc : Continuous f := hf.continuous
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ y ∈ (fun x => ‖f x‖) '' Set.Icc (-1 : ℝ) 1, y ≤ C :=
    (isCompact_Icc.image hfc.norm).bddAbove
  have hIf : Integrable f (gaussianReal 0 1) := by
    refine ((integrable_const |C|).add h1.norm).mono' hfc.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    simp only [Pi.add_apply]
    by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
    · exact (hC _ ⟨x, hx, rfl⟩).trans
        ((le_abs_self C).trans (le_add_of_nonneg_right (norm_nonneg _)))
    · have hx' : 1 ≤ |x| := by
        simp only [Set.mem_Icc, not_and_or, not_le] at hx
        rcases hx with hx | hx
        · rw [abs_of_nonpos (by linarith)]
          linarith
        · rw [abs_of_nonneg (by linarith)]
          linarith
      have hm : ‖f x‖ ≤ ‖x • f x‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        exact (le_mul_of_one_le_left (norm_nonneg _) hx')
      exact hm.trans (le_add_of_nonneg_left (abs_nonneg C))
  have hA : Integrable (fun x => gaussianPDFReal 0 1 x • deriv f x) :=
    (stein_pdf_integrable_smul_iff (deriv f)).2 h2
  have hB : Integrable (fun x => (-x * gaussianPDFReal 0 1 x) • f x) := by
    have hneg : Integrable (fun x => (-x) • f x) (gaussianReal 0 1) := by
      exact h1.neg.congr (ae_of_all _ fun x => by simp)
    exact ((stein_pdf_integrable_smul_iff (fun x => (-x) • f x)).2 hneg).congr
      (ae_of_all _ fun x => by dsimp; rw [smul_smul]; congr 1; ring)
  have hD : Integrable (fun x => gaussianPDFReal 0 1 x • f x) :=
    (stein_pdf_integrable_smul_iff f).2 hIf
  have hIBP := integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (u := gaussianPDFReal 0 1) (v := f)
    (u' := fun x => -x * gaussianPDFReal 0 1 x) (v' := deriv f)
    (fun x _ => stein_pdf_hasDerivAt x) (fun x _ => (hf x).hasDerivAt) hA hB hD
  beta_reduce at hIBP
  simp only [ContinuousLinearMap.lsmul_apply] at hIBP
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  calc
    (∫ x, gaussianPDFReal 0 1 x • (x • f x)) =
        -∫ x, (-x * gaussianPDFReal 0 1 x) • f x := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with x
      calc
        gaussianPDFReal 0 1 x • (x • f x) =
            (gaussianPDFReal 0 1 x * x) • f x :=
          smul_smul (gaussianPDFReal 0 1 x) x (f x)
        _ =
            (-(-x * gaussianPDFReal 0 1 x)) • f x := by congr 1; ring
        _ = -((-x * gaussianPDFReal 0 1 x) • f x) :=
          neg_smul (-x * gaussianPDFReal 0 1 x) (f x)
    _ = ∫ x, gaussianPDFReal 0 1 x • deriv f x := hIBP.symm

/-- Stein's lemma for `g ∼ N(0,1)`: for `f ∈ C¹(ℝ, E)` with `f` and `f'` of polynomial growth,
`E[g f(g)] = E[f'(g)]`.
Proof: `x • f x` and `f'` have polynomial growth and are continuous, hence integrable
(`HasPolyGrowth.integrable_of_isGaussian`); conclude by `stein_std_of_integrable`. -/
theorem stein_std {f : ℝ → E} (hf : ContDiff ℝ 1 f) (hg : HasPolyGrowth f)
    (hg' : HasPolyGrowth (deriv f)) :
    ∫ x, x • f x ∂(gaussianReal 0 1) = ∫ x, deriv f x ∂(gaussianReal 0 1) := by
  apply stein_std_of_integrable (hf.differentiable one_ne_zero)
  · have hx : HasPolyGrowth (fun x : ℝ => x) := by
      refine ⟨1, 1, fun x => ?_⟩
      simp only [Real.norm_eq_abs, one_mul, pow_one]
      linarith [abs_nonneg x]
    exact (hx.smul hg).integrable_of_isGaussian _
      (continuous_id.smul hf.continuous).aestronglyMeasurable
  · exact hg'.integrable_of_isGaussian _ hf.continuous_deriv_one.aestronglyMeasurable

/-- Real-valued Stein's lemma for `g ∼ N(0,1)`; the statement of `Muon.Foundations.gaussian_stein`
(whose growth hypotheses are `HasPolyGrowth` by `hasPolyGrowth_real_iff`). -/
theorem stein_std_real {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hg : HasPolyGrowth f)
    (hg' : HasPolyGrowth (deriv f)) :
    ∫ x, x * f x ∂(gaussianReal 0 1) = ∫ x, deriv f x ∂(gaussianReal 0 1) := by
  simpa only [smul_eq_mul] using stein_std hf hg hg'

/-- Stein's lemma for `g ∼ N(μ, v)`: `E[(g - μ) f(g)] = v E[f'(g)]`, for `f ∈ C¹(ℝ, E)` with `f`
and `f'` of polynomial growth. Holds also for `v = 0` (both sides vanish).
Proof: for `v ≠ 0`, `gaussianReal μ v` is the image of `gaussianReal 0 1` under
`z ↦ μ + √v z` (`gaussianReal_map_const_mul`, `gaussianReal_map_add_const`); apply `stein_std` to
`z ↦ f (μ + √v z)`, whose derivative is `√v f'(μ + √v z)` and which keeps polynomial growth. For
`v = 0` the measure is `dirac μ`. -/
theorem stein_gaussianReal (μ : ℝ) (v : ℝ≥0) {f : ℝ → E} (hf : ContDiff ℝ 1 f)
    (hg : HasPolyGrowth f) (hg' : HasPolyGrowth (deriv f)) :
    ∫ x, (x - μ) • f x ∂(gaussianReal μ v) = (v : ℝ) • ∫ x, deriv f x ∂(gaussianReal μ v) := by
  by_cases hv : v = 0
  · subst v
    rw [gaussianReal_zero_var]
    have hz : (fun x => (x - μ) • f x) =ᵐ[Measure.dirac μ] 0 := by
      exact (ae_eq_dirac (fun x => (x - μ) • f x)).trans
        (Filter.Eventually.of_forall fun _ => by simp)
    rw [integral_congr_ae hz]
    simp
  have hvR : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have ha : HasPolyGrowth (fun x : ℝ => x - μ) := by
    refine ⟨1 + |μ|, 1, fun x => ?_⟩
    simp only [Real.norm_eq_abs, pow_one]
    calc
      |x - μ| ≤ |x| + |μ| := abs_sub _ _
      _ ≤ (1 + |μ|) * (1 + |x|) := by
        nlinarith [abs_nonneg x, abs_nonneg μ]
  have hIshift : Integrable (fun x => (x - μ) • f x) (gaussianReal μ v) :=
    (ha.smul hg).integrable_of_isGaussian _
      ((continuous_id.sub continuous_const).smul hf.continuous).aestronglyMeasurable
  have hIf : Integrable f (gaussianReal μ v) :=
    hg.integrable_of_isGaussian _ hf.continuous.aestronglyMeasurable
  have hId : Integrable (deriv f) (gaussianReal μ v) :=
    hg'.integrable_of_isGaussian _ hf.continuous_deriv_one.aestronglyMeasurable
  have hA : Integrable (fun x => gaussianPDFReal μ v x • deriv f x) :=
    (gaussian_pdf_integrable_smul_iff μ v hv (deriv f)).2 hId
  have hscaled : Integrable (fun x => (-((x - μ) / (v : ℝ))) • f x)
      (gaussianReal μ v) := by
    have := hIshift.smul (-(v : ℝ)⁻¹)
    exact this.congr (ae_of_all _ fun x => by
      dsimp
      rw [smul_smul]
      congr 1
      field_simp [hvR])
  have hB : Integrable (fun x =>
      (-((x - μ) / (v : ℝ)) * gaussianPDFReal μ v x) • f x) :=
    ((gaussian_pdf_integrable_smul_iff μ v hv
      (fun x => (-((x - μ) / (v : ℝ))) • f x)).2 hscaled).congr
        (ae_of_all _ fun x => by dsimp; rw [smul_smul]; congr 1; ring)
  have hD : Integrable (fun x => gaussianPDFReal μ v x • f x) :=
    (gaussian_pdf_integrable_smul_iff μ v hv f).2 hIf
  have hIBP := integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (u := gaussianPDFReal μ v) (v := f)
    (u' := fun x => -((x - μ) / (v : ℝ)) * gaussianPDFReal μ v x)
    (v' := deriv f) (fun x _ => gaussian_pdf_hasDerivAt μ v hv x)
    (fun x _ => ((hf.differentiable one_ne_zero) x).hasDerivAt) hA hB hD
  beta_reduce at hIBP
  simp only [ContinuousLinearMap.lsmul_apply] at hIBP
  rw [integral_gaussianReal_eq_integral_smul hv,
    integral_gaussianReal_eq_integral_smul hv]
  rw [hIBP, smul_neg, ← integral_smul, ← integral_neg]
  apply integral_congr_ae
  filter_upwards with x
  rw [smul_smul]
  let b : ℝ := v • (-((x - μ) / (v : ℝ)) * gaussianPDFReal μ v x)
  calc
    (gaussianPDFReal μ v x * (x - μ)) • f x = (-b) • f x := by
      congr 1
      simp only [b, smul_eq_mul, NNReal.smul_def]
      field_simp [hvR]
    _ = -(b • f x) := neg_smul b (f x)
    _ = -((v : ℝ) •
        ((-((x - μ) / (v : ℝ)) * gaussianPDFReal μ v x) • f x)) := by
      congr 1
      rw [← smul_smul]
      simp only [b, NNReal.smul_def, smul_smul, smul_eq_mul]
    _ = -(v • ((-((x - μ) / (v : ℝ)) * gaussianPDFReal μ v x) • f x)) := by
      rw [NNReal.smul_def]

/-- Real-valued Stein's lemma for `g ∼ N(μ, v)`: `E[(g - μ) f(g)] = v E[f'(g)]`. -/
theorem stein_gaussianReal_real (μ : ℝ) (v : ℝ≥0) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : HasPolyGrowth f) (hg' : HasPolyGrowth (deriv f)) :
    ∫ x, (x - μ) * f x ∂(gaussianReal μ v) = v * ∫ x, deriv f x ∂(gaussianReal μ v) := by
  simpa only [smul_eq_mul] using stein_gaussianReal μ v hf hg hg'

/-- Random-variable form: if `g` has law `N(μ, v)` under `P`, then
`∫ (g - μ) f(g) dP = v ∫ f'(g) dP`.
Proof: `integral_map` along `g` (a.e.-measurable by `HasLaw`) turns both sides into the
integrals of `stein_gaussianReal`. -/
theorem stein_hasLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {g : Ω → ℝ} {μ : ℝ}
    {v : ℝ≥0} (hlaw : HasLaw g (gaussianReal μ v) P) {f : ℝ → E} (hf : ContDiff ℝ 1 f)
    (hg : HasPolyGrowth f) (hg' : HasPolyGrowth (deriv f)) :
    ∫ ω, (g ω - μ) • f (g ω) ∂P = (v : ℝ) • ∫ ω, deriv f (g ω) ∂P := by
  have hleft : AEStronglyMeasurable (fun x => (x - μ) • f x) (gaussianReal μ v) :=
    (continuous_id.sub continuous_const).smul hf.continuous |>.aestronglyMeasurable
  have hright : AEStronglyMeasurable (deriv f) (gaussianReal μ v) :=
    hf.continuous_deriv_one.aestronglyMeasurable
  calc
    (∫ ω, (g ω - μ) • f (g ω) ∂P) =
        ∫ x, (x - μ) • f x ∂(gaussianReal μ v) := by
      simpa only [Function.comp_apply] using hlaw.integral_comp hleft
    _ = (v : ℝ) • ∫ x, deriv f x ∂(gaussianReal μ v) :=
      stein_gaussianReal μ v hf hg hg'
    _ = (v : ℝ) • ∫ ω, deriv f (g ω) ∂P := by
      have heq := hlaw.integral_comp hright
      exact congrArg (fun z => (v : ℝ) • z) heq.symm

end OneDim

/-! ## Multivariate standard Gaussian -/

section Multivariate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private lemma aemeasurable_of_map_eq_pi_gaussian {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] {P : Measure Ω} {ξ : Ω → ι → ℝ} (i : ι)
    (hξ : P.map ξ = Measure.pi (fun _ : ι => gaussianReal 0 1)) :
    AEMeasurable ξ P := by
  have hP : P ≠ 0 := by
    intro hP
    subst P
    rw [Measure.map_zero] at hξ
    exact IsProbabilityMeasure.ne_zero
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) hξ.symm
  by_contra hmeas
  rw [Measure.map_of_not_aemeasurable_of_ne_zero hmeas hP] at hξ
  have heval := congrArg
    (fun Q : Measure (ι → ℝ) => Q.map (fun x => x i)) hξ
  rw [(measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).map_eq] at heval
  simp only [Measure.map_dirac] at heval
  let a : ℝ := (Classical.ofNonempty : ι → ℝ) i
  have ha := congrArg (fun Q : Measure ℝ => Q {a}) heval
  let : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal one_ne_zero
  simp [a] at ha

private lemma aemeasurable_of_map_eq_pi_gaussian' {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] {P : Measure Ω} {ξ : Ω → ι → ℝ}
    (hξ : P.map ξ = Measure.pi (fun _ : ι => gaussianReal 0 1)) :
    AEMeasurable ξ P := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      exact aemeasurable_of_subsingleton_codomain
  | inr hι =>
      let _ := hι
      exact aemeasurable_of_map_eq_pi_gaussian (Classical.choice hι) hξ

private lemma stein_fin_of_hasDerivAt {N : ℕ} (k : Fin N) {f f' : (Fin N → ℝ) → E}
    (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ x, HasDerivAt (fun t => f (Function.update x k t)) (f' x) (x k))
    (hg : HasPolyGrowth f) (hg' : HasPolyGrowth f') :
    ∫ x, x k • f x ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) =
      ∫ x, f' x ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) := by
  cases N with
  | zero => exact k.elim0
  | succ N =>
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => gaussianReal 0 1) k
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) k with he
    set ν := (gaussianReal 0 1).prod (Measure.pi fun _ : Fin N => gaussianReal 0 1) with hν
    have hI : ∀ G : (Fin (N + 1) → ℝ) → E,
        ∫ z, G z ∂(Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) =
          ∫ q, G (e.symm q) ∂ν := by
      intro G
      have h := hmp.integral_comp' (g := fun q => G (e.symm q))
      simpa [hν] using h
    have hIn : ∀ G : (Fin (N + 1) → ℝ) → E,
        Integrable G (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) →
          Integrable (fun q => G (e.symm q)) ν := by
      intro G hG
      exact ((hmp.symm).integrable_comp_emb
        (MeasurableEquiv.measurableEmbedding e.symm) (g := G)).2 hG
    have hsym (q : ℝ × (Fin N → ℝ)) : e.symm q = Fin.insertNth k q.1 q.2 := by
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    have hint1 : Integrable (fun z : Fin (N + 1) → ℝ => z k • f z)
        (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) :=
      ((hasPolyGrowth_apply k).smul hg).integrable_pi
        ((continuous_apply k).smul hf).aestronglyMeasurable
    have hint2 : Integrable f' (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) :=
      hg'.integrable_pi hf'.aestronglyMeasurable
    have hint1' := hIn _ hint1
    have hint2' := hIn _ hint2
    rw [hI, hI, integral_prod_symm _ hint1', integral_prod_symm _ hint2']
    apply integral_congr_ae
    filter_upwards [hint1'.prod_left_ae, hint2'.prod_left_ae] with y hy1 hy2
    simp only [hsym, Fin.insertNth_apply_same]
    have hdy : ∀ t : ℝ, HasDerivAt (fun s => f (Fin.insertNth k s y))
        (f' (Fin.insertNth k t y)) t := by
      intro t
      have h := hd (Fin.insertNth k t y)
      simpa only [Fin.insertNth_apply_same, Fin.update_insertNth] using h
    have hder : deriv (fun s => f (Fin.insertNth k s y)) =
        fun t => f' (Fin.insertNth k t y) := funext fun t => (hdy t).deriv
    have hy1' : Integrable (fun t => t • f (Fin.insertNth k t y)) (gaussianReal 0 1) :=
      hy1.congr (ae_of_all _ fun t => by dsimp; rw [hsym (t, y)]; simp)
    have hy2' : Integrable (fun t => f' (Fin.insertNth k t y)) (gaussianReal 0 1) :=
      hy2.congr (ae_of_all _ fun t => by dsimp; rw [hsym (t, y)])
    have hs := stein_std_of_integrable (fun t => (hdy t).differentiableAt) hy1' (by
      simpa only [hder] using hy2')
    simpa only [hder] using hs

private lemma stein_fin_of_integrable {N : ℕ} (k : Fin N) {f : (Fin N → ℝ) → E}
    (hf : Differentiable ℝ f)
    (h1 : Integrable (fun x => x k • f x)
      (Measure.pi fun _ : Fin N => gaussianReal 0 1))
    (h2 : Integrable (fun x => fderiv ℝ f x (Pi.single k 1))
      (Measure.pi fun _ : Fin N => gaussianReal 0 1)) :
    ∫ x, x k • f x ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) =
      ∫ x, fderiv ℝ f x (Pi.single k 1)
        ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) := by
  cases N with
  | zero => exact k.elim0
  | succ N =>
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => gaussianReal 0 1) k
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) k with he
    set ν := (gaussianReal 0 1).prod (Measure.pi fun _ : Fin N => gaussianReal 0 1) with hν
    have hI : ∀ G : (Fin (N + 1) → ℝ) → E,
        ∫ z, G z ∂(Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) =
          ∫ q, G (e.symm q) ∂ν := by
      intro G
      have h := hmp.integral_comp' (g := fun q => G (e.symm q))
      simpa [hν] using h
    have hIn : ∀ G : (Fin (N + 1) → ℝ) → E,
        Integrable G (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) →
          Integrable (fun q => G (e.symm q)) ν := by
      intro G hG
      exact ((hmp.symm).integrable_comp_emb
        (MeasurableEquiv.measurableEmbedding e.symm) (g := G)).2 hG
    have hsym (q : ℝ × (Fin N → ℝ)) : e.symm q = Fin.insertNth k q.1 q.2 := by
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    have hint1' := hIn _ h1
    have hint2' := hIn _ h2
    rw [hI, hI, integral_prod_symm _ hint1', integral_prod_symm _ hint2']
    apply integral_congr_ae
    filter_upwards [hint1'.prod_left_ae, hint2'.prod_left_ae] with y hy1 hy2
    simp only [hsym, Fin.insertNth_apply_same]
    have hdy : ∀ t : ℝ, HasDerivAt (fun s => f (Fin.insertNth k s y))
        (fderiv ℝ f (Fin.insertNth k t y) (Pi.single k 1)) t := by
      intro t
      have h := (hf (Function.update (Fin.insertNth k t y) k t)).hasFDerivAt.comp_hasDerivAt t
        (hasDerivAt_update (Fin.insertNth k t y) k t)
      change HasDerivAt (fun s => f (Function.update (Fin.insertNth k t y) k s))
        (fderiv ℝ f (Function.update (Fin.insertNth k t y) k t) (Pi.single k 1)) t at h
      simpa only [Fin.update_insertNth] using h
    have hder : deriv (fun s => f (Fin.insertNth k s y)) =
        fun t => fderiv ℝ f (Fin.insertNth k t y) (Pi.single k 1) :=
      funext fun t => (hdy t).deriv
    have hy1' : Integrable (fun t => t • f (Fin.insertNth k t y)) (gaussianReal 0 1) :=
      hy1.congr (ae_of_all _ fun t => by dsimp; rw [hsym (t, y)]; simp)
    have hy2' : Integrable
        (fun t => fderiv ℝ f (Fin.insertNth k t y) (Pi.single k 1))
        (gaussianReal 0 1) :=
      hy2.congr (ae_of_all _ fun t => by dsimp; rw [hsym (t, y)])
    have hs := stein_std_of_integrable (fun t => (hdy t).differentiableAt) hy1' (by
      simpa only [hder] using hy2')
    simpa only [hder] using hs

/-- Coordinate Stein identity on the product Gaussian, integrability form: for differentiable
`f : (ι → ℝ) → E` with `x i • f x` and `∂ᵢ f` integrable, `E[gᵢ f(g)] = E[∂ᵢ f(g)]`.
Proof: `MeasurableEquiv.piFinSuccAbove` / `measurePreserving_piFinSuccAbove` (after
`Fintype.equivFin`) splits the measure as `gaussianReal 0 1 ⊗ (product over the other
coordinates)`; Fubini gives, for a.e. value `y` of the other coordinates, integrability of the
slices `t ↦ t • f(t, y)` and `t ↦ ∂ᵢ f(t, y)`, the slice derivative is `∂ᵢ f(t, y)`, and
`stein_std_of_integrable` applies slicewise. -/
theorem stein_pi_of_integrable {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    {f : (ι → ℝ) → E} (hf : Differentiable ℝ f)
    (h1 : Integrable (fun x => x i • f x) (Measure.pi fun _ : ι => gaussianReal 0 1))
    (h2 : Integrable (fun x => fderiv ℝ f x (Pi.single i 1))
      (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    ∫ x, x i • f x ∂(Measure.pi fun _ : ι => gaussianReal 0 1) =
      ∫ x, fderiv ℝ f x (Pi.single i 1) ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  let e := Fintype.equivFin ι
  let R : (Fin (Fintype.card ι) → ℝ) → (ι → ℝ) := fun y a => y (e a)
  let L₀ : (Fin (Fintype.card ι) → ℝ) →ₗ[ℝ] (ι → ℝ) :=
    { toFun := R
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  let L : (Fin (Fintype.card ι) → ℝ) →L[ℝ] (ι → ℝ) :=
    ⟨L₀, LinearMap.continuous_of_finiteDimensional L₀⟩
  have hLR (y : Fin (Fintype.card ι) → ℝ) : L y = R y := rfl
  have hsingle : L (Pi.single (e i) 1) = Pi.single i 1 := by
    ext a
    by_cases hai : a = i
    · subst a
      simp [hLR, R]
    · have heai : e a ≠ e i := fun h => hai (e.injective h)
      simp [hLR, R, hai, heai]
  have hp (y : Fin (Fintype.card ι) → ℝ) :
      fderiv ℝ (fun z => f (L z)) y (Pi.single (e i) 1) =
        fderiv ℝ f (L y) (Pi.single i 1) := by
    change fderiv ℝ (f ∘ L) y (Pi.single (e i) 1) = _
    rw [fderiv_comp y (hf (L y)) L.differentiableAt]
    simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply]
    rw [hsingle]
  have hr : ((MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e.symm :
      (Fin (Fintype.card ι) → ℝ) ≃ᵐ (ι → ℝ)) :
      (Fin (Fintype.card ι) → ℝ) → (ι → ℝ)) = R := by
    funext y a
    change (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e.symm) y a = y (e a)
    convert MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : ι => ℝ) e.symm y (e a) using 1
    simp
  have hmp := measurePreserving_piCongrLeft
    (fun _ : ι => gaussianReal 0 1) e.symm
  have h1' : Integrable (fun y => y (e i) • f (L y))
      (Measure.pi fun _ : Fin (Fintype.card ι) => gaussianReal 0 1) := by
    have h := hmp.integrable_comp_of_integrable h1
    refine h.congr (ae_of_all _ fun y => ?_)
    simp only [Function.comp_apply, hr]
    change y (e i) • f (R y) = y (e i) • f (L y)
    rw [hLR]
  have h2' : Integrable
      (fun y => fderiv ℝ (fun z => f (L z)) y (Pi.single (e i) 1))
      (Measure.pi fun _ : Fin (Fintype.card ι) => gaussianReal 0 1) := by
    have h := hmp.integrable_comp_of_integrable h2
    exact h.congr (ae_of_all _ fun y => by
      simp only [Function.comp_apply, hr, hLR]
      exact (hp y).symm)
  have hs := stein_fin_of_integrable (E := E) (e i)
    (hf.comp L.differentiable) h1' h2'
  calc
    (∫ x, x i • f x ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
        ∫ y, y (e i) • f (L y)
          ∂(Measure.pi fun _ : Fin (Fintype.card ι) => gaussianReal 0 1) := by
      symm
      simpa only [hr, hLR, R] using hmp.integral_comp' (g := fun x => x i • f x)
    _ = ∫ y, fderiv ℝ (fun z => f (L z)) y (Pi.single (e i) 1)
          ∂(Measure.pi fun _ : Fin (Fintype.card ι) => gaussianReal 0 1) := hs
    _ = ∫ y, fderiv ℝ f (L y) (Pi.single i 1)
          ∂(Measure.pi fun _ : Fin (Fintype.card ι) => gaussianReal 0 1) := by
      apply integral_congr_ae
      exact ae_of_all _ hp
    _ = ∫ x, fderiv ℝ f x (Pi.single i 1)
          ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
      simpa only [hr, hLR] using
        hmp.integral_comp' (g := fun x => fderiv ℝ f x (Pi.single i 1))

/-- Coordinate Stein identity on the product Gaussian with only a continuous partial derivative
in the `i`-th coordinate (no joint differentiability): if `f`, `f'` are continuous with
polynomial growth and, for every `x`, `t ↦ f (update x i t)` has derivative `f' x` at
`t = x i`, then `E[gᵢ f(g)] = E[f'(g)]`. This is exactly the statement of Muon's private
`st_stein_pi` (`Muon/DetEquiv/Gaussian.lean`; `stdGaussianPi N` is this measure by `rfl`, and its
growth bounds are `HasPolyGrowth` by `HasPolyGrowth.of_le_sum_sq`), which needs it because its
`F` is only coordinatewise differentiable.
Proof: integrability of `x ↦ x i • f x` (`HasPolyGrowth.smul`, `hasPolyGrowth_apply`) and of `f'`
from `HasPolyGrowth.integrable_pi`. Split off coordinate `i` as in `stein_pi_of_integrable`; the
slice `t ↦ f (insertNth i t y)` has derivative `f' (insertNth i t y)` at every `t` (apply `hd` at
`insertNth i t y`, using `update (update x i t) i s = update x i s`), so
`stein_std_of_integrable` applies slicewise. Muon's `st_stein_pi` proof transfers. -/
theorem stein_pi_of_hasDerivAt {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    {f f' : (ι → ℝ) → E} (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ x, HasDerivAt (fun t => f (Function.update x i t)) (f' x) (x i))
    (hg : HasPolyGrowth f) (hg' : HasPolyGrowth f') :
    ∫ x, x i • f x ∂(Measure.pi fun _ : ι => gaussianReal 0 1) =
      ∫ x, f' x ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  let e := Fintype.equivFin ι
  let R : (Fin (Fintype.card ι) → ℝ) → (ι → ℝ) := fun y a => y (e a)
  let L₀ : (Fin (Fintype.card ι) → ℝ) →ₗ[ℝ] (ι → ℝ) :=
    { toFun := R
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  let L : (Fin (Fintype.card ι) → ℝ) →L[ℝ] (ι → ℝ) :=
    ⟨L₀, LinearMap.continuous_of_finiteDimensional L₀⟩
  have hLR (y : Fin (Fintype.card ι) → ℝ) : L y = R y := rfl
  have hupdate (y : Fin (Fintype.card ι) → ℝ) (t : ℝ) :
      R (Function.update y (e i) t) = Function.update (R y) i t := by
    ext a
    by_cases hai : a = i
    · subst a
      simp [R]
    · have heai : e a ≠ e i := fun h => hai (e.injective h)
      simp [R, Function.update, hai, heai]
  have hd' : ∀ y, HasDerivAt
      (fun t => f (L (Function.update y (e i) t))) (f' (L y)) (y (e i)) := by
    intro y
    simpa only [hLR, hupdate] using hd (R y)
  have hs := stein_fin_of_hasDerivAt (E := E) (e i)
    (hf.comp L.continuous) (hf'.comp L.continuous) hd'
    (hg.comp_continuousLinearMap L) (hg'.comp_continuousLinearMap L)
  have hr : ((MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e.symm :
      (Fin (Fintype.card ι) → ℝ) ≃ᵐ (ι → ℝ)) :
      (Fin (Fintype.card ι) → ℝ) → (ι → ℝ)) = R := by
    funext y a
    change (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e.symm) y a = y (e a)
    convert MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : ι => ℝ) e.symm y (e a) using 1
    simp
  have hmp := measurePreserving_piCongrLeft
    (fun _ : ι => gaussianReal 0 1) e.symm
  calc
    (∫ x, x i • f x ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
        ∫ y, y (e i) • f (L y)
          ∂(Measure.pi fun _ : Fin (Fintype.card ι) => gaussianReal 0 1) := by
      symm
      simpa only [hr, hLR, R] using hmp.integral_comp' (g := fun x => x i • f x)
    _ = ∫ y, f' (L y)
          ∂(Measure.pi fun _ : Fin (Fintype.card ι) => gaussianReal 0 1) := hs
    _ = ∫ x, f' x ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
      simpa only [hr, hLR] using hmp.integral_comp' (g := f')

/-- Coordinate Stein identity on the product Gaussian `N(0, I)` on `ι → ℝ` (SLT's
`GaussianMeasure.stdGaussianPi n` is this measure for `ι = Fin n`, by `rfl`): for
`f ∈ C¹((ι → ℝ), E)` with `f` and `∂ᵢ f` of polynomial growth, `E[gᵢ f(g)] = E[∂ᵢ f(g)]`.
Proof: both integrands are continuous with polynomial growth, hence integrable
(`HasPolyGrowth.integrable_pi`); conclude by `stein_pi_of_integrable`. Alternatively apply
`stein_pi_of_hasDerivAt` with `f' x = fderiv ℝ f x (Pi.single i 1)` (chain rule along
`t ↦ update x i t`). -/
theorem stein_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) {f : (ι → ℝ) → E}
    (hf : ContDiff ℝ 1 f) (hg : HasPolyGrowth f)
    (hg' : HasPolyGrowth (fun x => fderiv ℝ f x (Pi.single i 1))) :
    ∫ x, x i • f x ∂(Measure.pi fun _ : ι => gaussianReal 0 1) =
      ∫ x, fderiv ℝ f x (Pi.single i 1) ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  apply stein_pi_of_integrable i (hf.differentiable one_ne_zero)
  · exact ((hasPolyGrowth_apply i).smul hg).integrable_pi
      ((continuous_apply i).smul hf.continuous).aestronglyMeasurable
  · exact hg'.integrable_pi
      ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable

/-- Coordinate Stein identity on `stdGaussian (EuclideanSpace ℝ ι)`:
`E[gᵢ f(g)] = E[∂ᵢ f(g)]`, with `∂ᵢ f x = fderiv ℝ f x (EuclideanSpace.single i 1)`.
Proof: `map_pi_eq_stdGaussian` writes the measure as the image of the product Gaussian under
`toLp 2`; transport by `integral_map` and apply `stein_pi` to `f ∘ toLp 2`, whose `i`-th partial
is `∂ᵢ f ∘ toLp 2` (chain rule; `toLp 2 (Pi.single i 1) = EuclideanSpace.single i 1`). Growth
transfers since `toLp 2` is a continuous linear equivalence. -/
theorem stein_euclidean {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    {f : EuclideanSpace ℝ ι → E} (hf : ContDiff ℝ 1 f) (hg : HasPolyGrowth f)
    (hg' : HasPolyGrowth (fun x => fderiv ℝ f x (EuclideanSpace.single i 1))) :
    ∫ x, x i • f x ∂(stdGaussian (EuclideanSpace ℝ ι)) =
      ∫ x, fderiv ℝ f x (EuclideanSpace.single i 1) ∂(stdGaussian (EuclideanSpace ℝ ι)) := by
  let T : (ι → ℝ) ≃L[ℝ] EuclideanSpace ℝ ι :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  have hTf : ContDiff ℝ 1 (fun y => f (T y)) := hf.comp T.contDiff
  have hp (y : ι → ℝ) :
      fderiv ℝ (fun z => f (T z)) y (Pi.single i 1) =
        fderiv ℝ f (T y) (EuclideanSpace.single i 1) := by
    change fderiv ℝ (f ∘ T) y (Pi.single i 1) = _
    rw [fderiv_comp y (hf.differentiable one_ne_zero (T y)) T.differentiableAt]
    simp [T, ContinuousLinearEquiv.fderiv]
  have hs := stein_pi (E := E) i hTf
    (hg.comp_continuousLinearMap T.toContinuousLinearMap)
    (by
      have := hg'.comp_continuousLinearMap T.toContinuousLinearMap
      rw [show (fun x => fderiv ℝ (fun z => f (T z)) x (Pi.single i 1)) =
        (fun x => fderiv ℝ f (T x) (EuclideanSpace.single i 1)) from funext hp]
      exact this)
  rw [← ProbabilityTheory.map_pi_eq_stdGaussian]
  change (∫ x, x i • f x ∂Measure.map T (Measure.pi fun _ : ι => gaussianReal 0 1)) =
    ∫ x, fderiv ℝ f x (EuclideanSpace.single i 1)
      ∂Measure.map T (Measure.pi fun _ : ι => gaussianReal 0 1)
  rw [integral_map T.continuous.aemeasurable, integral_map T.continuous.aemeasurable]
  calc
    (∫ x, x i • f (T x) ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
        ∫ x, fderiv ℝ (fun y => f (T y)) x (Pi.single i 1)
          ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := hs
    _ = ∫ x, fderiv ℝ f (T x) (EuclideanSpace.single i 1)
          ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
      apply integral_congr_ae
      exact ae_of_all _ hp
  · exact ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable
  · exact (((continuous_apply i).comp T.symm.continuous).smul hf.continuous).aestronglyMeasurable

/-- Coordinate-free Stein identity on a finite-dimensional inner product space `V`: for every
direction `v`, `E[⟪v, g⟫ f(g)] = E[D f(g) v]`.
Proof: `v = 0` is trivial. Otherwise choose an orthonormal basis `b` with `b 0 = v / ‖v‖`
(`Orthonormal.exists_orthonormalBasis_extension`); `stdGaussian_eq_map_pi_orthonormalBasis`
transports to the product Gaussian, where `⟪v, ∑ xᵢ bᵢ⟫ = ‖v‖ x₀` and `D f(·) v = ‖v‖ ∂₀`;
apply `stein_pi` with `i = 0`. -/
theorem stein_stdGaussian {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (v : V) {f : V → E}
    (hf : ContDiff ℝ 1 f) (hg : HasPolyGrowth f)
    (hg' : HasPolyGrowth (fun x => fderiv ℝ f x v)) :
    ∫ x, ⟪v, x⟫ • f x ∂(stdGaussian V) = ∫ x, fderiv ℝ f x v ∂(stdGaussian V) := by
  by_cases hv : v = 0
  · subst v
    simp
  classical
  let w : V := ‖v‖⁻¹ • v
  have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hwnorm : ‖w‖ = 1 := by
    simp [w, norm_smul, hvnorm]
  have hw : Orthonormal ℝ ((↑) : ({w} : Set V) → V) := by
    rw [orthonormal_subsingleton_iff]
    intro a
    rcases a with ⟨a, ha⟩
    simp only [Set.mem_singleton_iff] at ha
    simpa [ha] using hwnorm
  obtain ⟨u, b, hwu, hb⟩ := hw.exists_orthonormalBasis_extension
  let k : u := ⟨w, hwu (Set.mem_singleton w)⟩
  have hbk : b k = w := by
    rw [hb]
  have hvb : ‖v‖ • b k = v := by
    rw [hbk]
    simp [w, smul_smul, hvnorm]
  let L₀ : (u → ℝ) →ₗ[ℝ] V := b.toBasis.equivFun.symm
  let L : (u → ℝ) →L[ℝ] V :=
    ⟨L₀, LinearMap.continuous_of_finiteDimensional L₀⟩
  have hLsum (x : u → ℝ) : L x = ∑ a, x a • b a := by
    change b.toBasis.equivFun.symm x = _
    exact b.toBasis.equivFun_symm_apply x
  have hLsingle : L (Pi.single k 1) = b k := by
    change b.toBasis.equivFun.symm (Pi.single k 1) = b k
    exact Basis.equivFun_symm_single b.toBasis k
  let g : (u → ℝ) → E := fun x => ‖v‖ • f (L x)
  have hgdiff : ContDiff ℝ 1 g :=
    (hf.comp L.contDiff).const_smul ‖v‖
  have hpg : HasPolyGrowth g := by
    have hc : HasPolyGrowth (fun _ : u → ℝ => ‖v‖) :=
      HasPolyGrowth.of_bounded ‖v‖ (fun _ => by simp)
    exact hc.smul (hg.comp_continuousLinearMap L)
  have hp (x : u → ℝ) :
      fderiv ℝ g x (Pi.single k 1) = fderiv ℝ f (L x) v := by
    rw [show fderiv ℝ g x = ‖v‖ • fderiv ℝ (fun y => f (L y)) x by
      exact fderiv_fun_const_smul
        ((hf.comp L.contDiff).differentiable one_ne_zero x) ‖v‖]
    change ‖v‖ • fderiv ℝ (fun y => f (L y)) x (Pi.single k 1) = _
    change ‖v‖ • fderiv ℝ (f ∘ L) x (Pi.single k 1) = _
    rw [fderiv_comp x (hf.differentiable one_ne_zero (L x)) L.differentiableAt]
    simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply, hLsingle]
    rw [← map_smul, hvb]
  have hpg' : HasPolyGrowth (fun x => fderiv ℝ g x (Pi.single k 1)) := by
    rw [show (fun x => fderiv ℝ g x (Pi.single k 1)) =
      (fun x => fderiv ℝ f (L x) v) from funext hp]
    exact hg'.comp_continuousLinearMap L
  have hs := stein_pi (E := E) k hgdiff hpg hpg'
  have hinner (x : u → ℝ) : ⟪v, L x⟫ = ‖v‖ * x k := by
    have hk : ⟪b k, L x⟫ = x k := by
      rw [← b.repr_apply_apply]
      change b.repr (b.toBasis.equivFun.symm x) k = x k
      simp
    calc
      ⟪v, L x⟫ = ⟪‖v‖ • b k, L x⟫ := by rw [hvb]
      _ = ‖v‖ * ⟪b k, L x⟫ := real_inner_smul_left _ _ _
      _ = ‖v‖ * x k := by rw [hk]
  have hmap : stdGaussian V =
      (Measure.pi fun _ : u => gaussianReal 0 1).map L := by
    rw [stdGaussian_eq_map_pi_orthonormalBasis b]
    congr 1
    funext x
    exact (hLsum x).symm
  rw [hmap]
  calc
    (∫ x, ⟪v, x⟫ • f x
        ∂(Measure.pi fun _ : u => gaussianReal 0 1).map L) =
        ∫ x, ⟪v, L x⟫ • f (L x)
          ∂(Measure.pi fun _ : u => gaussianReal 0 1) :=
      integral_map L.continuous.aemeasurable
        (((continuous_const.inner continuous_id).smul hf.continuous).aestronglyMeasurable)
    _ =
        ∫ x, x k • g x ∂(Measure.pi fun _ : u => gaussianReal 0 1) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hinner]
      simp only [g, smul_smul]
      congr 1
      ring
    _ = ∫ x, fderiv ℝ g x (Pi.single k 1)
          ∂(Measure.pi fun _ : u => gaussianReal 0 1) := hs
    _ = ∫ x, fderiv ℝ f (L x) v
          ∂(Measure.pi fun _ : u => gaussianReal 0 1) := by
      apply integral_congr_ae
      exact ae_of_all _ hp
    _ = ∫ x, fderiv ℝ f x v
          ∂(Measure.pi fun _ : u => gaussianReal 0 1).map L :=
      (integral_map L.continuous.aemeasurable
        (((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable)).symm

/-- Random-vector form: if `ξ` is a standard Gaussian vector under `P` (`IsStdGaussianVector`),
then `∫ ξᵢ f(ξ) dP = ∫ (∂ᵢ f)(ξ) dP`.
Proof: `P.map ξ` is a probability measure, so `ξ` is a.e.-measurable (a non-a.e.-measurable map
pushes forward to `0`); `integral_map` reduces both sides to `stein_pi` with `ι = Fin n`. -/
theorem stein_isStdGaussianVector {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {ξ : Ω → Fin n → ℝ} (hξ : IsStdGaussianVector P ξ) (i : Fin n) {f : (Fin n → ℝ) → E}
    (hf : ContDiff ℝ 1 f) (hg : HasPolyGrowth f)
    (hg' : HasPolyGrowth (fun x => fderiv ℝ f x (Pi.single i 1))) :
    ∫ ω, ξ ω i • f (ξ ω) ∂P = ∫ ω, fderiv ℝ f (ξ ω) (Pi.single i 1) ∂P := by
  have hmeas : AEMeasurable ξ P := aemeasurable_of_map_eq_pi_gaussian i hξ
  have hleft : AEStronglyMeasurable (fun x : Fin n → ℝ => x i • f x) (P.map ξ) :=
    ((continuous_apply i).smul hf.continuous).aestronglyMeasurable
  have hright : AEStronglyMeasurable
      (fun x : Fin n → ℝ => fderiv ℝ f x (Pi.single i 1)) (P.map ξ) :=
    ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable
  calc
    (∫ ω, ξ ω i • f (ξ ω) ∂P) =
        ∫ x, x i • f x ∂(P.map ξ) := (integral_map hmeas hleft).symm
    _ = ∫ x, x i • f x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := by rw [hξ]
    _ = ∫ x, fderiv ℝ f x (Pi.single i 1)
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := stein_pi i hf hg hg'
    _ = ∫ x, fderiv ℝ f x (Pi.single i 1) ∂(P.map ξ) := by rw [hξ]
    _ = ∫ ω, fderiv ℝ f (ξ ω) (Pi.single i 1) ∂P := integral_map hmeas hright

end Multivariate

/-! ## Gaussian matrices -/

section Matrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Vectorisation of a matrix, `X ↦ ((i, j) ↦ X i j)`; `IsIIDGaussianMatrix` is stated through
it (`isIIDGaussianMatrix_iff`). -/
def vecOfMat {m n : Type*} (X : Matrix m n ℝ) : m × n → ℝ := fun ij => X ij.1 ij.2

/-- Inverse of `vecOfMat`, `x ↦ Matrix.of (fun i j => x (i, j))`. -/
def matOfVec {m n : Type*} (x : m × n → ℝ) : Matrix m n ℝ := Matrix.of fun i j => x (i, j)

private def matOfVecLinear {m n : Type*} : (m × n → ℝ) →ₗ[ℝ] Matrix m n ℝ where
  toFun := matOfVec
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma vecOfMat_matOfVec {m n : Type*} (x : m × n → ℝ) : vecOfMat (matOfVec x) = x := rfl

@[simp] lemma matOfVec_vecOfMat {m n : Type*} (X : Matrix m n ℝ) : matOfVec (vecOfMat X) = X :=
  rfl

/-- `IsIIDGaussianMatrix` says exactly that the vectorised matrix has the product Gaussian law. -/
lemma isIIDGaussianMatrix_iff {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {p q : ℕ}
    {X : Ω → Matrix (Fin p) (Fin q) ℝ} :
    IsIIDGaussianMatrix P X ↔
      P.map (fun ω => vecOfMat (X ω)) = Measure.pi (fun _ : Fin p × Fin q => gaussianReal 0 1) :=
  Iff.rfl

/-- Entrywise partial derivative `∂F/∂Xᵢⱼ (X) = d/dt F(X + t Eᵢⱼ)|_{t=0}`, with
`Eᵢⱼ = Matrix.single i j 1`. Defined as a line derivative so that no norm on matrices is
needed; `0` if the derivative does not exist. -/
noncomputable def matPartial {m n : Type*} [DecidableEq m] [DecidableEq n]
    (F : Matrix m n ℝ → E) (i : m) (j : n) (X : Matrix m n ℝ) : E :=
  lineDeriv ℝ F X (Matrix.single i j 1)

/-- Unfolding: `matPartial F i j X = d/dt F(X + t Eᵢⱼ)|_{t=0}`. -/
lemma matPartial_eq_deriv {m n : Type*} [DecidableEq m] [DecidableEq n]
    (F : Matrix m n ℝ → E) (i : m) (j : n) (X : Matrix m n ℝ) :
    matPartial F i j X = deriv (fun t : ℝ => F (X + t • Matrix.single i j 1)) 0 := rfl

/-- Through the vectorisation, `matPartial` is the `(i, j)` partial derivative:
`∂F/∂Xᵢⱼ (matOfVec x) = D(F ∘ matOfVec)(x) (Pi.single (i, j) 1)`.
Proof: `matOfVec x + t Eᵢⱼ = matOfVec (x + t • Pi.single (i, j) 1)` (`matOfVec` is linear), so
the line derivative of `F` at `matOfVec x` along `Eᵢⱼ` is that of `F ∘ matOfVec` at `x` along
`Pi.single (i, j) 1`; conclude by `DifferentiableAt.lineDeriv_eq_fderiv`. -/
lemma matPartial_matOfVec {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] {F : Matrix m n ℝ → E} (i : m) (j : n) {x : m × n → ℝ}
    (hF : DifferentiableAt ℝ (fun y => F (matOfVec y)) x) :
    matPartial F i j (matOfVec x) =
      fderiv ℝ (fun y => F (matOfVec y)) x (Pi.single (i, j) 1) := by
  rw [matPartial_eq_deriv, ← hF.lineDeriv_eq_fderiv]
  apply congrArg (fun g : ℝ → E => deriv g 0)
  funext t
  congr 1
  ext a b
  simp [matOfVec, Matrix.single_apply, Pi.single_apply, eq_comm]

section Elementwise

open scoped Matrix.Norms.Elementwise

/-- With the entrywise (sup) norm on matrices, `matPartial F i j X = DF(X) Eᵢⱼ`. The same holds
for any other matrix norm by `DifferentiableAt.lineDeriv_eq_fderiv`. -/
lemma matPartial_eq_fderiv {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] {F : Matrix m n ℝ → E} (i : m) (j : n) {X : Matrix m n ℝ}
    (hF : DifferentiableAt ℝ F X) :
    matPartial F i j X = fderiv ℝ F X (Matrix.single i j 1) :=
  hF.lineDeriv_eq_fderiv

/-- Smoothness transfers to the vectorisation: if `F` is `Cᵏ` for the entrywise norm on
matrices then so is `F ∘ matOfVec` (the form required by `stein_matrix`).
Proof: `matOfVec` is a linear map between finite-dimensional spaces (indeed a linear isometry
for the sup norms), hence a continuous linear map (`LinearMap.continuous_of_finiteDimensional`);
`ContDiff.comp` with `ContinuousLinearMap.contDiff`. -/
lemma contDiff_comp_matOfVec {m n : Type*} [Fintype m] [Fintype n] {k : WithTop ℕ∞}
    {F : Matrix m n ℝ → E} (hF : ContDiff ℝ k F) : ContDiff ℝ k (fun x => F (matOfVec x)) := by
  let L : (m × n → ℝ) →L[ℝ] Matrix m n ℝ :=
    ⟨matOfVecLinear, LinearMap.continuous_of_finiteDimensional matOfVecLinear⟩
  exact hF.comp L.contDiff

/-- Growth transfers to the vectorisation: for the entrywise norm, `‖matOfVec x‖ = ‖x‖` (both are
the sup of `|x (i, j)|`), so `HasPolyGrowth F` gives `HasPolyGrowth (F ∘ matOfVec)`. -/
lemma HasPolyGrowth.comp_matOfVec {m n β : Type*} [Fintype m] [Fintype n] [Norm β]
    {F : Matrix m n ℝ → β} (hF : HasPolyGrowth F) : HasPolyGrowth (fun x => F (matOfVec x)) := by
  let L : (m × n → ℝ) →L[ℝ] Matrix m n ℝ :=
    ⟨matOfVecLinear, LinearMap.continuous_of_finiteDimensional matOfVecLinear⟩
  exact hF.comp_continuousLinearMap L

end Elementwise

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- `contDiff_comp_matOfVec` for the Frobenius norm on matrices. Proof: as in the entrywise case;
`matOfVec` is linear on a finite-dimensional space, hence continuous linear. -/
lemma contDiff_comp_matOfVec_frobenius {m n : Type*} [Fintype m] [Fintype n] {k : WithTop ℕ∞}
    {F : Matrix m n ℝ → E} (hF : ContDiff ℝ k F) : ContDiff ℝ k (fun x => F (matOfVec x)) := by
  let L : (m × n → ℝ) →L[ℝ] Matrix m n ℝ :=
    ⟨matOfVecLinear, LinearMap.continuous_of_finiteDimensional matOfVecLinear⟩
  exact hF.comp L.contDiff

/-- `HasPolyGrowth.comp_matOfVec` for the Frobenius norm: `‖matOfVec x‖_F ≤ √(card (m × n)) ‖x‖`,
or `HasPolyGrowth.comp_continuousLinearMap` with `matOfVec` as a continuous linear map. -/
lemma HasPolyGrowth.comp_matOfVec_frobenius {m n β : Type*} [Fintype m] [Fintype n] [Norm β]
    {F : Matrix m n ℝ → β} (hF : HasPolyGrowth F) : HasPolyGrowth (fun x => F (matOfVec x)) := by
  let L : (m × n → ℝ) →L[ℝ] Matrix m n ℝ :=
    ⟨matOfVecLinear, LinearMap.continuous_of_finiteDimensional matOfVecLinear⟩
  exact hF.comp_continuousLinearMap L

end Frobenius

section L2Operator

open scoped Matrix.Norms.L2Operator

/-- `contDiff_comp_matOfVec` for the `ℓ²` operator norm on matrices (the natural norm for
resolvent bounds). Proof: as in the entrywise case. -/
lemma contDiff_comp_matOfVec_l2Op {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {k : WithTop ℕ∞} {F : Matrix m n ℝ → E} (hF : ContDiff ℝ k F) :
    ContDiff ℝ k (fun x => F (matOfVec x)) := by
  let L : (m × n → ℝ) →L[ℝ] Matrix m n ℝ :=
    ⟨matOfVecLinear, LinearMap.continuous_of_finiteDimensional matOfVecLinear⟩
  exact hF.comp L.contDiff

/-- `HasPolyGrowth.comp_matOfVec` for the `ℓ²` operator norm: `‖matOfVec x‖ ≤ ‖matOfVec x‖_F ≤
√(card (m × n)) ‖x‖`, or `HasPolyGrowth.comp_continuousLinearMap` with `matOfVec` as a continuous
linear map. -/
lemma HasPolyGrowth.comp_matOfVec_l2Op {m n β : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    [Norm β] {F : Matrix m n ℝ → β} (hF : HasPolyGrowth F) :
    HasPolyGrowth (fun x => F (matOfVec x)) := by
  let L : (m × n → ℝ) →L[ℝ] Matrix m n ℝ :=
    ⟨matOfVecLinear, LinearMap.continuous_of_finiteDimensional matOfVecLinear⟩
  exact hF.comp_continuousLinearMap L

end L2Operator

/-- Gaussian integration by parts for an i.i.d. `N(0,1)` matrix: if `X` is
`IsIIDGaussianMatrix` under `P` and `F : Matrix (Fin p) (Fin q) ℝ → E` is `C¹` with `F` and
`∂F/∂Xᵢⱼ` of polynomial growth (through the vectorisation), then
`E[Xᵢⱼ F(X)] = E[∂F/∂Xᵢⱼ (X)]`.
Proof: by `isIIDGaussianMatrix_iff` the vector `ω ↦ vecOfMat (X ω)` has the product Gaussian
law on `Fin p × Fin q → ℝ`; rewrite `X ω = matOfVec (vecOfMat (X ω))`, transport by
`integral_map`, apply `stein_pi` with index `(i, j)` to `F ∘ matOfVec`, and identify the partial
by `matPartial_matOfVec`. -/
theorem stein_matrix {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {p q : ℕ}
    {X : Ω → Matrix (Fin p) (Fin q) ℝ} (hX : IsIIDGaussianMatrix P X) (i : Fin p) (j : Fin q)
    {F : Matrix (Fin p) (Fin q) ℝ → E} (hF : ContDiff ℝ 1 (fun x => F (matOfVec x)))
    (hg : HasPolyGrowth (fun x => F (matOfVec x)))
    (hg' : HasPolyGrowth (fun x => matPartial F i j (matOfVec x))) :
    ∫ ω, X ω i j • F (X ω) ∂P = ∫ ω, matPartial F i j (X ω) ∂P := by
  let Y : Ω → Fin p × Fin q → ℝ := fun ω => vecOfMat (X ω)
  have hY : P.map Y = Measure.pi
      (fun _ : Fin p × Fin q => gaussianReal 0 1) := isIIDGaussianMatrix_iff.mp hX
  have hYmeas : AEMeasurable Y P :=
    aemeasurable_of_map_eq_pi_gaussian (i, j) hY
  have hpartial (x : Fin p × Fin q → ℝ) :
      fderiv ℝ (fun y => F (matOfVec y)) x (Pi.single (i, j) 1) =
        matPartial F i j (matOfVec x) :=
    (matPartial_matOfVec i j (hF.differentiable one_ne_zero x)).symm
  have hgpartial : HasPolyGrowth
      (fun x => fderiv ℝ (fun y => F (matOfVec y)) x (Pi.single (i, j) 1)) := by
    rw [show (fun x => fderiv ℝ (fun y => F (matOfVec y)) x (Pi.single (i, j) 1)) =
      (fun x => matPartial F i j (matOfVec x)) from funext hpartial]
    exact hg'
  have hleft : AEStronglyMeasurable
      (fun x : Fin p × Fin q → ℝ => x (i, j) • F (matOfVec x)) (P.map Y) :=
    ((continuous_apply (i, j)).smul hF.continuous).aestronglyMeasurable
  have hright : AEStronglyMeasurable
      (fun x : Fin p × Fin q → ℝ => matPartial F i j (matOfVec x)) (P.map Y) := by
    rw [show (fun x : Fin p × Fin q → ℝ => matPartial F i j (matOfVec x)) =
      (fun x => fderiv ℝ (fun y => F (matOfVec y)) x (Pi.single (i, j) 1)) from
        funext fun x => (hpartial x).symm]
    exact ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable
  have hs := stein_pi (E := E) (i, j) hF hg hgpartial
  calc
    (∫ ω, X ω i j • F (X ω) ∂P) =
        ∫ x, x (i, j) • F (matOfVec x) ∂(P.map Y) := by
      rw [integral_map hYmeas hleft]
      apply integral_congr_ae
      filter_upwards with ω
      rw [show Y ω (i, j) = X ω i j by rfl,
        show matOfVec (Y ω) = X ω by exact matOfVec_vecOfMat (X ω)]
    _ = ∫ x, x (i, j) • F (matOfVec x)
          ∂(Measure.pi fun _ : Fin p × Fin q => gaussianReal 0 1) := by rw [hY]
    _ = ∫ x, fderiv ℝ (fun y => F (matOfVec y)) x (Pi.single (i, j) 1)
          ∂(Measure.pi fun _ : Fin p × Fin q => gaussianReal 0 1) := hs
    _ = ∫ x, matPartial F i j (matOfVec x)
          ∂(Measure.pi fun _ : Fin p × Fin q => gaussianReal 0 1) := by
      apply integral_congr_ae
      exact ae_of_all _ hpartial
    _ = ∫ x, matPartial F i j (matOfVec x) ∂(P.map Y) := by rw [hY]
    _ = ∫ ω, matPartial F i j (X ω) ∂P := by
      rw [integral_map hYmeas hright]
      apply integral_congr_ae
      filter_upwards with ω
      rw [show matOfVec (Y ω) = X ω by exact matOfVec_vecOfMat (X ω)]

/-- Real-valued Gaussian-matrix integration by parts: `E[Xᵢⱼ F(X)] = E[∂F/∂Xᵢⱼ (X)]`. -/
theorem stein_matrix_real {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {p q : ℕ}
    {X : Ω → Matrix (Fin p) (Fin q) ℝ} (hX : IsIIDGaussianMatrix P X) (i : Fin p) (j : Fin q)
    {F : Matrix (Fin p) (Fin q) ℝ → ℝ} (hF : ContDiff ℝ 1 (fun x => F (matOfVec x)))
    (hg : HasPolyGrowth (fun x => F (matOfVec x)))
    (hg' : HasPolyGrowth (fun x => matPartial F i j (matOfVec x))) :
    ∫ ω, X ω i j * F (X ω) ∂P = ∫ ω, matPartial F i j (X ω) ∂P := by
  simpa only [smul_eq_mul] using stein_matrix hX i j hF hg hg'

end Matrix

/-! ## Covariance forms -/

section Covariance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open scoped MatrixOrder Matrix.Norms.L2Operator

private lemma HasPolyGrowth.clm_apply_const {X V W : Type*} [Norm X]
    [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    [SeminormedAddCommGroup W] [NormedSpace ℝ W]
    {F : X → V →L[ℝ] W} (hF : HasPolyGrowth F) (v : V) :
    HasPolyGrowth (fun x => F x v) := by
  rcases hF with ⟨C, k, hC⟩
  refine ⟨2 * |C| * ‖v‖, 2 * k, fun x => ?_⟩
  calc
    ‖F x v‖ ≤ ‖F x‖ * ‖v‖ := (F x).le_opNorm v
    _ ≤ (2 * |C| * (1 + ‖x‖ ^ (2 * k))) * ‖v‖ := by
      gcongr
      exact (hC x).trans (poly_bound_normalize C ‖x‖ k)
    _ = (2 * |C| * ‖v‖) * (1 + ‖x‖ ^ (2 * k)) := by ring

private lemma HasPolyGrowth.comp_add_const {V W : Type*} [NormedAddCommGroup V]
    [NormedAddCommGroup W] {F : V → W} (hF : HasPolyGrowth F) (a : V) :
    HasPolyGrowth (fun x => F (a + x)) := by
  rcases hF with ⟨C, k, hC⟩
  let B : ℝ := 2 ^ (k - 1)
  let D : ℝ := 1 + B * (1 + ‖a‖ ^ k)
  refine ⟨|C| * D, k, fun x => (hC (a + x)).trans ?_⟩
  have hpow : (‖a‖ + ‖x‖) ^ k ≤ B * (‖a‖ ^ k + ‖x‖ ^ k) := by
    simpa [B, add_comm] using add_pow_le (norm_nonneg a) (norm_nonneg x) k
  have hbase : 1 + ‖a + x‖ ^ k ≤ D * (1 + ‖x‖ ^ k) := by
    have hnorm : ‖a + x‖ ^ k ≤ (‖a‖ + ‖x‖) ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) k
    have hB : 0 ≤ B := by positivity
    have hx : 0 ≤ ‖x‖ ^ k := by positivity
    have ha : 0 ≤ ‖a‖ ^ k := by positivity
    have hax : ‖a + x‖ ^ k ≤ B * (‖a‖ ^ k + ‖x‖ ^ k) := hnorm.trans hpow
    calc
      1 + ‖a + x‖ ^ k ≤ 1 + B * (‖a‖ ^ k + ‖x‖ ^ k) := by linarith
      _ ≤ D * (1 + ‖x‖ ^ k) := by
        dsimp only [D]
        nlinarith [mul_nonneg (mul_nonneg hB ha) hx]
  calc
    C * (1 + ‖a + x‖ ^ k) ≤ |C| * (1 + ‖a + x‖ ^ k) := by
      gcongr
      exact le_abs_self C
    _ ≤ |C| * (D * (1 + ‖x‖ ^ k)) := by gcongr
    _ = (|C| * D) * (1 + ‖x‖ ^ k) := by ring

/-- Stein identity for `ξ ∼ N(μ, S)` (Mathlib's `multivariateGaussian`, `S` positive
semidefinite): `E[(ξᵢ - μᵢ) f(ξ)] = ∑ⱼ Sᵢⱼ E[∂ⱼ f(ξ)]`, i.e. `E[(ξ - μ) f(ξ)] = S E[∇f(ξ)]`.
Positive semidefiniteness is needed: otherwise the measure is `dirac μ` and the left side is `0`.
Proof: the measure is the image of `stdGaussian` under `x ↦ μ + R x`, `R = CFC.sqrt S`
symmetric with `R * R = S`; then `ξᵢ - μᵢ = ∑ₖ Rᵢₖ gₖ`, apply `stein_euclidean` to
`f (μ + R ·)` in each coordinate `k`, whose `k`-th partial is `∑ⱼ Rⱼₖ ∂ⱼ f`, and sum
`∑ₖ Rᵢₖ Rⱼₖ = Sᵢⱼ`. -/
theorem stein_multivariateGaussian {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (i : ι)
    {f : EuclideanSpace ℝ ι → E} (hf : ContDiff ℝ 1 f) (hg : HasPolyGrowth f)
    (hg' : HasPolyGrowth (fderiv ℝ f)) :
    ∫ x, (x i - μ i) • f x ∂(multivariateGaussian μ S) =
      ∑ j, S i j • ∫ x, fderiv ℝ f x (EuclideanSpace.single j 1) ∂(multivariateGaussian μ S) := by
  let R : Matrix ι ι ℝ := CFC.sqrt S
  let M : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) R
  let T : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι := fun x => μ + M x
  let e : ι → EuclideanSpace ℝ ι := fun j => EuclideanSpace.single j 1
  let v : EuclideanSpace ℝ ι := M (e i)
  have hRself : R.IsHermitian := (CFC.sqrt_nonneg S).isSelfAdjoint
  have hRR : R * R = S := CFC.sqrt_mul_sqrt_self S hS.nonneg
  have hSsymm (j k : ι) : S j k = S k j := by
    simpa using hS.isHermitian.apply k j
  have hRij (j k : ι) : R j k = R k j := by
    simpa using hRself.apply k j
  have hinner (x : EuclideanSpace ℝ ι) : ⟪v, x⟫ = (M x) i := by
    change (∑ j, x j * (R *ᵥ Pi.single i 1) j) = (R *ᵥ x) i
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    simp [Pi.single_apply, hRij, mul_comm]
  have hMv : M v = ∑ j, S i j • e j := by
    ext j
    have hv' : v.ofLp = R *ᵥ Pi.single i 1 := by
      change (M (e i)).ofLp = _
      rw [Matrix.ofLp_toEuclideanCLM]
      congr 1
    rw [show (M v) j = (R *ᵥ v.ofLp) j by
      exact congrFun (Matrix.ofLp_toEuclideanCLM R v) j]
    rw [hv', Matrix.mulVec_mulVec, hRR]
    simp [e, Pi.single_apply, hSsymm]
  let q : EuclideanSpace ℝ ι → E := fun x => f (T x)
  have hTcont : Continuous T := continuous_const.add M.continuous
  have hTdiff : ∀ x, HasFDerivAt T M x := by
    intro x
    change HasFDerivAt (fun y => μ + M y) M x
    exact M.hasFDerivAt.const_add μ
  have hqdiff : ContDiff ℝ 1 q := by
    apply hf.comp
    exact contDiff_const.add M.contDiff
  have hqgrowth : HasPolyGrowth q := by
    exact (hg.comp_add_const μ).comp_continuousLinearMap M
  have hp (x : EuclideanSpace ℝ ι) :
      fderiv ℝ q x v =
        ∑ j, S i j • fderiv ℝ f (T x) (e j) := by
    have hc := (hf.differentiable one_ne_zero (T x)).hasFDerivAt.comp x (hTdiff x)
    have hd := hc.fderiv
    change fderiv ℝ q x = (fderiv ℝ f (T x)).comp M at hd
    rw [hd]
    simp only [ContinuousLinearMap.comp_apply, hMv, map_sum, map_smul]
  have hqdergrowth : HasPolyGrowth (fun x => fderiv ℝ q x v) := by
    rw [show (fun x => fderiv ℝ q x v) =
      (fun x => fderiv ℝ f (T x) (M v)) by
        funext x
        have hc := (hf.differentiable one_ne_zero (T x)).hasFDerivAt.comp x (hTdiff x)
        have hd := hc.fderiv
        change fderiv ℝ q x = (fderiv ℝ f (T x)).comp M at hd
        rw [hd]
        rfl]
    exact ((hg'.comp_add_const μ).comp_continuousLinearMap M).clm_apply_const (M v)
  have hs := stein_stdGaussian (E := E) v hqdiff hqgrowth hqdergrowth
  have hcompgrowth : HasPolyGrowth (fun x => fderiv ℝ f (T x)) :=
    (hg'.comp_add_const μ).comp_continuousLinearMap M
  have hInt (j : ι) : Integrable (fun x => fderiv ℝ f (T x) (e j))
      (stdGaussian (EuclideanSpace ℝ ι)) :=
    (hcompgrowth.clm_apply_const (e j)).integrable_of_isGaussian _
      ((((hf.continuous_fderiv one_ne_zero).comp
        (continuous_const.add M.continuous)).clm_apply continuous_const).aestronglyMeasurable)
  have hmap : multivariateGaussian μ S =
      (stdGaussian (EuclideanSpace ℝ ι)).map T := rfl
  have heval : Continuous (fun x : EuclideanSpace ℝ ι => x i) := by fun_prop
  have hconst : Continuous (fun _ : EuclideanSpace ℝ ι => μ i) := continuous_const
  have hleftcont : Continuous (fun x : EuclideanSpace ℝ ι => (x i - μ i) • f x) :=
    (heval.sub hconst).smul hf.continuous
  rw [hmap]
  calc
    (∫ x, (x i - μ i) • f x
        ∂(stdGaussian (EuclideanSpace ℝ ι)).map T) =
        ∫ x, ⟪v, x⟫ • q x ∂(stdGaussian (EuclideanSpace ℝ ι)) := by
      rw [integral_map (μ := stdGaussian (EuclideanSpace ℝ ι)) (φ := T) hTcont.aemeasurable
        hleftcont.aestronglyMeasurable]
      apply integral_congr_ae
      filter_upwards with x
      change ((μ i + (M x) i) - μ i) • f (T x) = ⟪v, x⟫ • q x
      rw [add_sub_cancel_left, hinner]
    _ = ∫ x, fderiv ℝ q x v ∂(stdGaussian (EuclideanSpace ℝ ι)) := hs
    _ = ∫ x, ∑ j, S i j • fderiv ℝ f (T x) (e j)
          ∂(stdGaussian (EuclideanSpace ℝ ι)) := by
      apply integral_congr_ae
      exact ae_of_all _ hp
    _ = ∑ j, S i j • ∫ x, fderiv ℝ f (T x) (e j)
          ∂(stdGaussian (EuclideanSpace ℝ ι)) := by
      rw [integral_finsetSum]
      · congr with j
        rw [integral_smul]
      · intro j _
        exact (hInt j).smul (S i j)
    _ = ∑ j, S i j • ∫ x, fderiv ℝ f x (e j)
          ∂(stdGaussian (EuclideanSpace ℝ ι)).map T := by
      congr with j
      rw [integral_map (μ := stdGaussian (EuclideanSpace ℝ ι)) (φ := T) hTcont.aemeasurable
        (((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable)]

/-- Stein identity for a linear image of a standard Gaussian vector, `ξ = A z` with covariance
`Σ = A Aᵀ`: `E[ξᵢ f(ξ)] = ∑ⱼ Σᵢⱼ E[∂ⱼ f(ξ)]`. With `A = Σ^{1/2}` this is the `Σ^{1/2} g` form.
Proof: `ξᵢ = ∑ₖ Aᵢₖ zₖ`; apply `stein_isStdGaussianVector` to `f (A *ᵥ ·)` in coordinate `k`,
whose `k`-th partial is `∑ⱼ Aⱼₖ (∂ⱼ f)(A *ᵥ ·)` by the chain rule (growth by
`HasPolyGrowth.comp_continuousLinearMap`), and sum `∑ₖ Aᵢₖ Aⱼₖ = (A Aᵀ)ᵢⱼ`. -/
theorem stein_linear_image {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {m n : ℕ}
    {z : Ω → Fin m → ℝ} (hz : IsStdGaussianVector P z) (A : Matrix (Fin n) (Fin m) ℝ)
    (i : Fin n) {f : (Fin n → ℝ) → E} (hf : ContDiff ℝ 1 f) (hg : HasPolyGrowth f)
    (hg' : HasPolyGrowth (fderiv ℝ f)) :
    ∫ ω, (A *ᵥ z ω) i • f (A *ᵥ z ω) ∂P =
      ∑ j, (A * Aᵀ) i j • ∫ ω, fderiv ℝ f (A *ᵥ z ω) (Pi.single j 1) ∂P := by
  let L₀ : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ) := A.mulVecLin
  let L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ) :=
    ⟨L₀, LinearMap.continuous_of_finiteDimensional L₀⟩
  have hL (x : Fin m → ℝ) : L x = A *ᵥ x := rfl
  let g : (Fin m → ℝ) → E := fun x => f (L x)
  have hgf : ContDiff ℝ 1 g := hf.comp L.contDiff
  have hgg : HasPolyGrowth g := hg.comp_continuousLinearMap L
  have hp (k : Fin m) (x : Fin m → ℝ) :
      fderiv ℝ g x (Pi.single k 1) =
        ∑ j, A j k • fderiv ℝ f (L x) (Pi.single j 1) := by
    change fderiv ℝ (f ∘ L) x (Pi.single k 1) = _
    rw [fderiv_comp x (hf.differentiable one_ne_zero (L x)) L.differentiableAt]
    simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply]
    rw [show L (Pi.single k 1) = fun j => A j k by
      ext j
      change (A *ᵥ Pi.single k 1) j = A j k
      simp]
    rw [show (fun j => A j k) = ∑ j, A j k • Pi.single j 1 by
      ext j
      simp [Pi.single_apply]]
    rw [map_sum]
    congr with j
    rw [map_smul]
  have hgp (k : Fin m) :
      HasPolyGrowth (fun x => fderiv ℝ g x (Pi.single k 1)) := by
    rw [show (fun x => fderiv ℝ g x (Pi.single k 1)) =
      (fun x => fderiv ℝ f (L x) (L (Pi.single k 1))) by
        funext x
        change fderiv ℝ (f ∘ L) x (Pi.single k 1) = _
        rw [fderiv_comp x (hf.differentiable one_ne_zero (L x)) L.differentiableAt]
        simp [ContinuousLinearMap.fderiv]]
    exact (hg'.comp_continuousLinearMap L).clm_apply_const (L (Pi.single k 1))
  have hmeas : AEMeasurable z P := aemeasurable_of_map_eq_pi_gaussian' hz
  have hbaseInt (k : Fin m) : Integrable (fun ω => z ω k • g (z ω)) P := by
    let q : (Fin m → ℝ) → E := fun x => x k • g x
    have hq : Integrable q (P.map z) := by
      rw [hz]
      exact ((hasPolyGrowth_apply k).smul hgg).integrable_pi
        ((continuous_apply k).smul hgf.continuous).aestronglyMeasurable
    exact (integrable_map_measure
      ((continuous_apply k).smul hgf.continuous |>.aestronglyMeasurable) hmeas).mp hq
  have hderInt (j : Fin n) :
      Integrable (fun ω => fderiv ℝ f (L (z ω)) (Pi.single j 1)) P := by
    let q : (Fin m → ℝ) → E := fun x => fderiv ℝ f (L x) (Pi.single j 1)
    have hq : Integrable q (P.map z) := by
      rw [hz]
      exact ((hg'.comp_continuousLinearMap L).clm_apply_const (Pi.single j 1)).integrable_pi
        ((((hf.continuous_fderiv one_ne_zero).comp L.continuous).clm_apply
          continuous_const).aestronglyMeasurable)
    exact (integrable_map_measure
      ((((hf.continuous_fderiv one_ne_zero).comp L.continuous).clm_apply
        continuous_const).aestronglyMeasurable) hmeas).mp hq
  have hstein (k : Fin m) :
      ∫ ω, z ω k • g (z ω) ∂P =
        ∑ j, A j k • ∫ ω, fderiv ℝ f (L (z ω)) (Pi.single j 1) ∂P := by
    calc
      (∫ ω, z ω k • g (z ω) ∂P) =
          ∫ ω, fderiv ℝ g (z ω) (Pi.single k 1) ∂P :=
        stein_isStdGaussianVector hz k hgf hgg (hgp k)
      _ = ∫ ω, ∑ j, A j k • fderiv ℝ f (L (z ω)) (Pi.single j 1) ∂P := by
        apply integral_congr_ae
        exact ae_of_all _ (fun ω => hp k (z ω))
      _ = ∑ j, A j k • ∫ ω, fderiv ℝ f (L (z ω)) (Pi.single j 1) ∂P := by
        rw [integral_finsetSum]
        · congr with j
          rw [integral_smul]
        · intro j _
          exact (hderInt j).smul (A j k)
  calc
    (∫ ω, (A *ᵥ z ω) i • f (A *ᵥ z ω) ∂P) =
        ∫ ω, ∑ k, A i k • (z ω k • g (z ω)) ∂P := by
      apply integral_congr_ae
      filter_upwards with ω
      simp only [g, hL]
      simp [Matrix.mulVec, dotProduct, Finset.sum_smul, smul_smul]
    _ = ∑ k, A i k • ∫ ω, z ω k • g (z ω) ∂P := by
      rw [integral_finsetSum]
      · congr with k
        rw [integral_smul]
      · intro k _
        exact (hbaseInt k).smul (A i k)
    _ = ∑ k, A i k •
        (∑ j, A j k • ∫ ω, fderiv ℝ f (L (z ω)) (Pi.single j 1) ∂P) := by
      congr with k
      rw [hstein]
    _ = ∑ j, (A * Aᵀ) i j •
        ∫ ω, fderiv ℝ f (L (z ω)) (Pi.single j 1) ∂P := by
      simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Matrix.transpose_apply,
        Finset.sum_smul]
      rw [Finset.sum_comm]
    _ = ∑ j, (A * Aᵀ) i j •
        ∫ ω, fderiv ℝ f (A *ᵥ z ω) (Pi.single j 1) ∂P := by
      simp only [hL]

end Covariance

end GaussianFoundations
