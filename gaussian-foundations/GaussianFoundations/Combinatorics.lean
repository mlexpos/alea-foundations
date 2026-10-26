import Mathlib
import GaussianFoundations.Moments
import GaussianFoundations.GaussianMatrix

/-!
# Foundations: Gaussian combinatorics and cited Gaussian facts (task L-0.6b)

Statements of three cited results, with their proofs left to the proof workers (proof routes in
`phases-of-muon/appendix-nodes/results/L-0.6b-interface.json`):

* `isserlis_wick`: Isserlis / Wick moment formula for products of i.i.d. standard Gaussian
  coordinates, in the perfect-matching form; the instances `gaussian_coord_moment_*`,
  `gaussian_trilinear_moment`, `gaussian_quartic_covariance`,
  `gaussian_weighted_square_moment`, `gaussian_weighted_linear_moment` that the sign-SGD card
  (#7, #23) and the volatility card (tree closure) use.
* `sheppard_arcsine`: `P(sign g ≠ sign h) = arccos ρ / π` for a centered unit-variance jointly
  Gaussian pair with correlation `ρ`.
* `poly_zero_set_null`: the zero set of a nonzero real multivariate polynomial is Lebesgue-null,
  hence null for the product Gaussian `stdGaussianPi`.

Certificates in `Muon.External` are not used here: these are proved statements (EXTERNAL-RESULTS
rows `IsserlisWick`, `SheppardArcsine`, `PolyZeroSetNull`, plan **prove**).
Snapshot `cr-2026-10-23`.
The standard Gaussian vector `stdGaussianPi n` and the one-dimensional moments are reused from
`GaussianFoundations.Moments`.
-/

namespace GaussianFoundations

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Matrix

/-! ## Isserlis / Wick

`IsPerfectMatchingInv` and the general-index-type `isserlis_wick` live in `GaussianFoundations.GaussianMatrix`;
`isserlis_wick_fin` is Muon's `Fin d` statement for `stdGaussianPi d`, as a corollary. -/

/-- Isserlis / Wick formula, coordinate form, for `g ~ N(0, I_d)` (`stdGaussianPi d`), indices
`c : Fin k → Fin d`: `E ∏_{r=1}^{k} g_{c(r)} = #{π perfect matching of [k] : c is constant on each pair of π}`,
the matching `π` encoded as a fixed-point-free involution `σ` of `Fin k`. Corollary of the general
`GaussianFoundations.isserlis_wick`. -/
theorem isserlis_wick_fin (d k : ℕ) (c : Fin k → Fin d) :
    ∫ z, (∏ r : Fin k, z (c r)) ∂(stdGaussianPi d)
      = (Nat.card {σ : Equiv.Perm (Fin k) // IsPerfectMatchingInv σ ∧ ∀ i, c (σ i) = c i} : ℝ) :=
  isserlis_wick k c

private lemma coord_pow_integral (d k : ℕ) (i : Fin d) :
    ∫ z, z i ^ k ∂(stdGaussianPi d) = ∫ x, x ^ k ∂(gaussianReal 0 1) := by
  have hf : Measurable (fun x : ℝ => x ^ k) := measurable_id.pow_const k
  rw [← stdGaussianPi_map_coord d i,
    integral_map (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable]

/-- Instance of `isserlis_wick`: `E g_i² = 1` for a standard Gaussian coordinate. -/
theorem gaussian_coord_moment_two (d : ℕ) (i : Fin d) :
    ∫ z, z i ^ 2 ∂(stdGaussianPi d) = 1 := by
  rw [coord_pow_integral, gaussian_moment_two]

/-- Instance of `isserlis_wick`: `E g_i⁴ = 3`. -/
theorem gaussian_coord_moment_four (d : ℕ) (i : Fin d) :
    ∫ z, z i ^ 4 ∂(stdGaussianPi d) = 3 := by
  rw [coord_pow_integral, gaussian_moment_four]

/-- Instance of `isserlis_wick`: `E g_i⁶ = 15`. -/
theorem gaussian_coord_moment_six (d : ℕ) (i : Fin d) :
    ∫ z, z i ^ 6 ∂(stdGaussianPi d) = 15 := by
  rw [coord_pow_integral, gaussian_moment_six]

/-- Instance of `isserlis_wick`: `E g_i⁸ = 105`. -/
theorem gaussian_coord_moment_eight (d : ℕ) (i : Fin d) :
    ∫ z, z i ^ 8 ∂(stdGaussianPi d) = 105 := by
  rw [coord_pow_integral, gaussian_moment_eight]

private lemma perm2_fpf (σ : Equiv.Perm (Fin 2)) :
    IsPerfectMatchingInv σ ↔ σ = Equiv.swap 0 1 := by
  have h : ∀ σ : Equiv.Perm (Fin 2), IsPerfectMatchingInv σ ↔ σ = Equiv.swap 0 1 := by
    unfold IsPerfectMatchingInv; decide
  exact h σ

private lemma perm4_fpf (σ : Equiv.Perm (Fin 4)) :
    IsPerfectMatchingInv σ ↔ (σ = Equiv.swap 0 1 * Equiv.swap 2 3 ∨ σ = Equiv.swap 0 2 * Equiv.swap 1 3 ∨ σ = Equiv.swap 0 3 * Equiv.swap 1 2) := by
  have h : ∀ σ : Equiv.Perm (Fin 4), IsPerfectMatchingInv σ ↔ (σ = Equiv.swap 0 1 * Equiv.swap 2 3 ∨ σ = Equiv.swap 0 2 * Equiv.swap 1 3 ∨ σ = Equiv.swap 0 3 * Equiv.swap 1 2) := by
    unfold IsPerfectMatchingInv; decide
  exact h σ

private lemma forall_fin4 {P : Fin 4 → Prop} : (∀ i, P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 := by
  constructor
  · intro h; exact ⟨h 0, h 1, h 2, h 3⟩
  · rintro ⟨h0, h1, h2, h3⟩ i; fin_cases i <;> assumption

private lemma forall_fin2 {P : Fin 2 → Prop} : (∀ i, P i) ↔ P 0 ∧ P 1 := by
  constructor
  · intro h; exact ⟨h 0, h 1⟩
  · rintro ⟨h0, h1⟩ i; fin_cases i <;> assumption

private lemma card2_match {n : ℕ} (c : Fin 2 → Fin n) :
    Nat.card {σ : Equiv.Perm (Fin 2) // IsPerfectMatchingInv σ ∧ ∀ i, c (σ i) = c i}
      = if c 0 = c 1 then 1 else 0 := by
  classical
  have hS : Finset.univ.filter (fun σ : Equiv.Perm (Fin 2) => IsPerfectMatchingInv σ ∧ ∀ i, c (σ i) = c i)
      = ({Equiv.swap 0 1} : Finset (Equiv.Perm (Fin 2))).filter (fun σ => ∀ i, c (σ i) = c i) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, perm2_fpf, Finset.mem_singleton]
  have hQ : (∀ i, c ((Equiv.swap 0 1 : Equiv.Perm (Fin 2)) i) = c i) ↔ c 0 = c 1 := by
    rw [forall_fin2]
    have v0 : (Equiv.swap 0 1 : Equiv.Perm (Fin 2)) 0 = 1 := by decide
    have v1 : (Equiv.swap 0 1 : Equiv.Perm (Fin 2)) 1 = 0 := by decide
    rw [v0, v1]
    constructor
    · rintro ⟨h0, -⟩; exact h0.symm
    · intro h; exact ⟨h.symm, h⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hS, Finset.card_filter, Finset.sum_singleton]
  simp only [hQ]

private lemma card4_match {n : ℕ} (c : Fin 4 → Fin n) :
    Nat.card {σ : Equiv.Perm (Fin 4) // IsPerfectMatchingInv σ ∧ ∀ i, c (σ i) = c i}
      = (if c 0 = c 1 ∧ c 2 = c 3 then 1 else 0) + (if c 0 = c 2 ∧ c 1 = c 3 then 1 else 0)
        + (if c 0 = c 3 ∧ c 1 = c 2 then 1 else 0) := by
  classical
  have hS : Finset.univ.filter (fun σ : Equiv.Perm (Fin 4) => IsPerfectMatchingInv σ ∧ ∀ i, c (σ i) = c i)
      = ({Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.swap 0 3 * Equiv.swap 1 2} : Finset (Equiv.Perm (Fin 4))).filter (fun σ => ∀ i, c (σ i) = c i) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, perm4_fpf, Finset.mem_insert, Finset.mem_singleton]
  have hQ1 : (∀ i, c ((Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) i) = c i) ↔ (c 0 = c 1 ∧ c 2 = c 3) := by
    rw [forall_fin4]
    have v0 : (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) 0 = 1 := by decide
    have v1 : (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) 1 = 0 := by decide
    have v2 : (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) 2 = 3 := by decide
    have v3 : (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) 3 = 2 := by decide
    rw [v0, v1, v2, v3]
    constructor
    · rintro ⟨h0, -, h2, -⟩; exact ⟨h0.symm, h2.symm⟩
    · rintro ⟨h0, h2⟩; exact ⟨h0.symm, h0, h2.symm, h2⟩
  have hQ2 : (∀ i, c ((Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) i) = c i) ↔ (c 0 = c 2 ∧ c 1 = c 3) := by
    rw [forall_fin4]
    have v0 : (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) 0 = 2 := by decide
    have v1 : (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) 1 = 3 := by decide
    have v2 : (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) 2 = 0 := by decide
    have v3 : (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) 3 = 1 := by decide
    rw [v0, v1, v2, v3]
    constructor
    · rintro ⟨h0, h1, -, -⟩; exact ⟨h0.symm, h1.symm⟩
    · rintro ⟨h0, h1⟩; exact ⟨h0.symm, h1.symm, h0, h1⟩
  have hQ3 : (∀ i, c ((Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) i) = c i) ↔ (c 0 = c 3 ∧ c 1 = c 2) := by
    rw [forall_fin4]
    have v0 : (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) 0 = 3 := by decide
    have v1 : (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) 1 = 2 := by decide
    have v2 : (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) 2 = 1 := by decide
    have v3 : (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) 3 = 0 := by decide
    rw [v0, v1, v2, v3]
    constructor
    · rintro ⟨h0, h1, -, -⟩; exact ⟨h0.symm, h1.symm⟩
    · rintro ⟨h0, h1⟩; exact ⟨h0.symm, h1.symm, h1, h0⟩
  have d12 : (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) ∉
      ({Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.swap 0 3 * Equiv.swap 1 2} : Finset (Equiv.Perm (Fin 4))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; decide
  have d23 : (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) ≠ Equiv.swap 0 3 * Equiv.swap 1 2 := by
    decide
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hS, Finset.card_filter,
    Finset.sum_insert d12, Finset.sum_pair d23]
  simp only [hQ1, hQ2, hQ3]
  ring


private lemma gauss_mono_integrable {n k : ℕ} (c : Fin k → Fin n) :
    Integrable (fun z : Fin n → ℝ => ∏ r : Fin k, z (c r)) (stdGaussianPi n) := by
  have hprod : (fun z : Fin n → ℝ => ∏ r : Fin k, z (c r))
      = fun z : Fin n → ℝ => ∏ i : Fin n, (fun (x : ℝ) => x ^ Fintype.card {r // c r = i}) (z i) := by
    funext z
    rw [← Fintype.prod_fiberwise c (fun r => z (c r))]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_congr rfl (fun (r : {r // c r = i}) _ => by rw [r.2]), Finset.prod_const,
      Finset.card_univ]
  rw [hprod]
  unfold stdGaussianPi
  exact Integrable.fintype_prod (fun i => gaussian_integrable_pow _)

private lemma gauss_two_integrable {n : ℕ} (p q : Fin n) :
    Integrable (fun z : Fin n → ℝ => z p * z q) (stdGaussianPi n) := by
  have h := gauss_mono_integrable (n := n) ![p, q]
  simpa [Fin.prod_univ_two] using h

private lemma gauss_four_integrable {n : ℕ} (p q r s : Fin n) :
    Integrable (fun z : Fin n → ℝ => z p * z q * z r * z s) (stdGaussianPi n) := by
  have h := gauss_mono_integrable (n := n) ![p, q, r, s]
  simpa [Fin.prod_univ_four] using h

/-- Two-point Gaussian moment, from `isserlis_wick`. -/
private lemma gauss_two_index {n : ℕ} (p q : Fin n) :
    ∫ z : Fin n → ℝ, z p * z q ∂(stdGaussianPi n) = if p = q then 1 else 0 := by
  have h := isserlis_wick_fin n 2 ![p, q]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
  rw [card2_match ![p, q]] at h
  rw [h]
  simp

/-- Four-point Gaussian moment, from `isserlis_wick`. -/
private lemma gauss_four_index {n : ℕ} (p q r s : Fin n) :
    ∫ z : Fin n → ℝ, z p * z q * z r * z s ∂(stdGaussianPi n)
      = (if p = q ∧ r = s then 1 else 0) + (if p = r ∧ q = s then 1 else 0)
        + (if p = s ∧ q = r then 1 else 0) := by
  have h := isserlis_wick_fin n 4 ![p, q, r, s]
  rw [card4_match ![p, q, r, s]] at h
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, Nat.cast_add, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero] at h
  exact h

private lemma expand2 {n : ℕ} (a b z : Fin n → ℝ) :
    (a ⬝ᵥ z) * (b ⬝ᵥ z) = ∑ p, ∑ q, (a p * b q) * (z p * z q) := by
  simp only [dotProduct]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

private lemma expand4 {n : ℕ} (a b c d z : Fin n → ℝ) :
    (a ⬝ᵥ z) * (b ⬝ᵥ z) * (c ⬝ᵥ z) * (d ⬝ᵥ z)
      = ∑ p, ∑ q, ∑ r, ∑ s, (a p * b q * c r * d s) * (z p * z q * z r * z s) := by
  have e : (a ⬝ᵥ z) * (b ⬝ᵥ z) * (c ⬝ᵥ z) * (d ⬝ᵥ z)
      = ((a ⬝ᵥ z) * (b ⬝ᵥ z)) * ((c ⬝ᵥ z) * (d ⬝ᵥ z)) := by ring
  rw [e, expand2 a b z, expand2 c d z]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by ring

/-- Two linear forms: `E[(a·g)(b·g)] = a·b`. -/
private lemma gauss_lin2 {n : ℕ} (a b : Fin n → ℝ) :
    ∫ z : Fin n → ℝ, (a ⬝ᵥ z) * (b ⬝ᵥ z) ∂(stdGaussianPi n) = a ⬝ᵥ b := by
  have hint : ∀ p q : Fin n, Integrable (fun z : Fin n → ℝ => (a p * b q) * (z p * z q))
      (stdGaussianPi n) := fun p q => (gauss_two_integrable p q).const_mul _
  have hp : ∀ p : Fin n, ∫ z : Fin n → ℝ, ∑ q, (a p * b q) * (z p * z q) ∂(stdGaussianPi n)
      = a p * b p := by
    intro p
    rw [integral_finset_sum _ (fun q _ => hint p q)]
    simp only [integral_const_mul, gauss_two_index]
    simp [mul_ite]
  simp only [expand2]
  rw [integral_finset_sum _ (fun p _ => integrable_finset_sum _ (fun q _ => hint p q))]
  rw [Finset.sum_congr rfl (fun p _ => hp p)]
  simp only [dotProduct]

private lemma ite_and_mul_real (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P ∧ Q then (1 : ℝ) else 0) = (if P then 1 else 0) * (if Q then 1 else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

/-- Four-point moment in Kronecker form. -/
private lemma gauss_four_kron {n : ℕ} (p q r s : Fin n) :
    ∫ z : Fin n → ℝ, z p * z q * z r * z s ∂(stdGaussianPi n)
      = (if p = q then (1 : ℝ) else 0) * (if r = s then (1 : ℝ) else 0)
        + (if p = r then (1 : ℝ) else 0) * (if q = s then (1 : ℝ) else 0)
        + (if p = s then (1 : ℝ) else 0) * (if q = r then (1 : ℝ) else 0) := by
  rw [gauss_four_index, ite_and_mul_real, ite_and_mul_real, ite_and_mul_real]

private lemma delta_sum {n : ℕ} (x y : Fin n → ℝ) :
    ∑ p, ∑ q, x p * y q * (if p = q then (1 : ℝ) else 0) = x ⬝ᵥ y := by
  simp [mul_ite, dotProduct, Finset.sum_ite_eq]

private lemma sum4_prod {n : ℕ} (F G : Fin n → Fin n → ℝ) :
    ∑ p, ∑ q, ∑ r, ∑ s, F p q * G r s = (∑ p, ∑ q, F p q) * (∑ r, ∑ s, G r s) := by
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]

private lemma sum4_swap1 {n : ℕ} (F G : Fin n → Fin n → ℝ) :
    ∑ p, ∑ q, ∑ r, ∑ s, F p r * G q s = (∑ p, ∑ r, F p r) * (∑ q, ∑ s, G q s) := by
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_comm

private lemma sum4_swap2 {n : ℕ} (F G : Fin n → Fin n → ℝ) :
    ∑ p, ∑ q, ∑ r, ∑ s, F p s * G q r = (∑ p, ∑ s, F p s) * (∑ q, ∑ r, G q r) := by
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_congr rfl fun q _ => Finset.sum_comm]
  exact Finset.sum_comm

/-- Four linear forms: `E[(a·g)(b·g)(c·g)(d·g)] = (a·b)(c·d) + (a·c)(b·d) + (a·d)(b·c)`. -/
private lemma gauss_lin4 {n : ℕ} (a b c d : Fin n → ℝ) :
    ∫ z : Fin n → ℝ, (a ⬝ᵥ z) * (b ⬝ᵥ z) * (c ⬝ᵥ z) * (d ⬝ᵥ z) ∂(stdGaussianPi n)
      = (a ⬝ᵥ b) * (c ⬝ᵥ d) + (a ⬝ᵥ c) * (b ⬝ᵥ d) + (a ⬝ᵥ d) * (b ⬝ᵥ c) := by
  have hint : ∀ p q r s : Fin n, Integrable
      (fun z : Fin n → ℝ => (a p * b q * c r * d s) * (z p * z q * z r * z s)) (stdGaussianPi n) :=
    fun p q r s => (gauss_four_integrable p q r s).const_mul _
  have hsum : ∫ z : Fin n → ℝ, (a ⬝ᵥ z) * (b ⬝ᵥ z) * (c ⬝ᵥ z) * (d ⬝ᵥ z) ∂(stdGaussianPi n)
      = ∑ p, ∑ q, ∑ r, ∑ s, (a p * b q * c r * d s) *
          ((if p = q then (1 : ℝ) else 0) * (if r = s then (1 : ℝ) else 0)
            + (if p = r then (1 : ℝ) else 0) * (if q = s then (1 : ℝ) else 0)
            + (if p = s then (1 : ℝ) else 0) * (if q = r then (1 : ℝ) else 0)) := by
    simp only [expand4]
    rw [integral_finset_sum _ (fun p _ => integrable_finset_sum _ fun q _ =>
      integrable_finset_sum _ fun r _ => integrable_finset_sum _ fun s _ => hint p q r s)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_finset_sum _ (fun q _ => integrable_finset_sum _ fun r _ =>
      integrable_finset_sum _ fun s _ => hint p q r s)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_finset_sum _ (fun r _ => integrable_finset_sum _ fun s _ => hint p q r s)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [integral_finset_sum _ (fun s _ => hint p q r s)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [integral_const_mul, gauss_four_kron]
  have T1 : ∑ p, ∑ q, ∑ r, ∑ s, (a p * b q * c r * d s) *
      ((if p = q then (1 : ℝ) else 0) * (if r = s then (1 : ℝ) else 0))
      = (a ⬝ᵥ b) * (c ⬝ᵥ d) := by
    have e : ∀ p q r s : Fin n, (a p * b q * c r * d s) *
        ((if p = q then (1 : ℝ) else 0) * (if r = s then (1 : ℝ) else 0))
        = (a p * b q * (if p = q then (1 : ℝ) else 0)) * (c r * d s * (if r = s then (1 : ℝ) else 0)) :=
      fun p q r s => by ring
    simp only [e]
    rw [sum4_prod, delta_sum, delta_sum]
  have T2 : ∑ p, ∑ q, ∑ r, ∑ s, (a p * b q * c r * d s) *
      ((if p = r then (1 : ℝ) else 0) * (if q = s then (1 : ℝ) else 0))
      = (a ⬝ᵥ c) * (b ⬝ᵥ d) := by
    have e : ∀ p q r s : Fin n, (a p * b q * c r * d s) *
        ((if p = r then (1 : ℝ) else 0) * (if q = s then (1 : ℝ) else 0))
        = (a p * c r * (if p = r then (1 : ℝ) else 0)) * (b q * d s * (if q = s then (1 : ℝ) else 0)) :=
      fun p q r s => by ring
    simp only [e]
    rw [sum4_swap1, delta_sum, delta_sum]
  have T3 : ∑ p, ∑ q, ∑ r, ∑ s, (a p * b q * c r * d s) *
      ((if p = s then (1 : ℝ) else 0) * (if q = r then (1 : ℝ) else 0))
      = (a ⬝ᵥ d) * (b ⬝ᵥ c) := by
    have e : ∀ p q r s : Fin n, (a p * b q * c r * d s) *
        ((if p = s then (1 : ℝ) else 0) * (if q = r then (1 : ℝ) else 0))
        = (a p * d s * (if p = s then (1 : ℝ) else 0)) * (b q * c r * (if q = r then (1 : ℝ) else 0)) :=
      fun p q r s => by ring
    simp only [e]
    rw [sum4_swap2, delta_sum, delta_sum]
  rw [hsum]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [T1, T2, T3]
private lemma gauss_lin4_integrable {n : ℕ} (a b c d : Fin n → ℝ) :
    Integrable (fun z : Fin n → ℝ => (a ⬝ᵥ z) * (b ⬝ᵥ z) * (c ⬝ᵥ z) * (d ⬝ᵥ z))
      (stdGaussianPi n) := by
  simp only [expand4]
  exact integrable_finset_sum _ fun p _ => integrable_finset_sum _ fun q _ =>
    integrable_finset_sum _ fun r _ => integrable_finset_sum _ fun s _ =>
      (gauss_four_integrable p q r s).const_mul _


/-- Algebra for the quartic covariance: `Σ_{kl} M_kl (Λ_ij Λ_kl + Λ_ik Λ_jl + Λ_il Λ_jk)
= Tr(ΛM) Λ_ij + 2 (ΛMΛ)_ij` for symmetric `Λ`, `M`. -/
private lemma quartic_alg {n : ℕ} (Λ M : Matrix (Fin n) (Fin n) ℝ) (hΛs : Λᵀ = Λ) (hMs : Mᵀ = M)
    (i j : Fin n) :
    ∑ k, ∑ l, M k l * (Λ i j * Λ k l + Λ i k * Λ j l + Λ i l * Λ j k)
      = Matrix.trace (Λ * M) * Λ i j + 2 * (Λ * M * Λ) i j := by
  have hMe : ∀ a b, M a b = M b a := fun a b => by
    have h := congrFun (congrFun hMs b) a
    simpa [Matrix.transpose_apply] using h
  have hΛe : ∀ a b, Λ a b = Λ b a := fun a b => by
    have h := congrFun (congrFun hΛs b) a
    simpa [Matrix.transpose_apply] using h
  have htr : Matrix.trace (Λ * M) = ∑ k, ∑ l, Λ k l * M k l := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by rw [hMe l k]
  have hA : (Λ * M * Λ) i j = ∑ k, ∑ l, Λ i k * M k l * Λ j l := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
      rw [hΛe l j]
  have hsplit : ∑ k, ∑ l, M k l * (Λ i j * Λ k l + Λ i k * Λ j l + Λ i l * Λ j k)
      = (∑ k, ∑ l, M k l * (Λ i j * Λ k l)) + (∑ k, ∑ l, M k l * (Λ i k * Λ j l))
        + (∑ k, ∑ l, M k l * (Λ i l * Λ j k)) := by
    simp only [mul_add, Finset.sum_add_distrib]
  have T1 : ∑ k, ∑ l, M k l * (Λ i j * Λ k l) = Λ i j * (∑ k, ∑ l, Λ k l * M k l) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
  have T3 : ∑ k, ∑ l, M k l * (Λ i l * Λ j k) = ∑ k, ∑ l, Λ i k * M k l * Λ j l := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
      rw [hMe l k, hΛe j l]; ring
  rw [hsplit, T1, T3, hA, htr]
  have T2 : ∑ k, ∑ l, M k l * (Λ i k * Λ j l) = ∑ k, ∑ l, Λ i k * M k l * Λ j l := by
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  rw [T2]
  ring

/-- Quartic covariance under measurability of `y` (helper for the frozen target). -/
private lemma gaussian_quartic_covariance_of_aem (n : ℕ) (A M Λ : Matrix (Fin n) (Fin n) ℝ)
    (hΛ : Λ = A * Aᵀ) (hM : Mᵀ = M)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (y : Ω → Fin n → ℝ)
    (hy : P.map y = (stdGaussianPi n).map (fun g => A *ᵥ g)) (hyM : AEMeasurable y P)
    (i j : Fin n) :
    ∫ ω, y ω i * y ω j * (y ω ⬝ᵥ (M *ᵥ y ω)) ∂P
      = Matrix.trace (Λ * M) * Λ i j + 2 * (Λ * M * Λ) i j := by
  have hF : Measurable (fun x : Fin n → ℝ => x i * x j * (x ⬝ᵥ (M *ᵥ x))) := by
    fun_prop
  have hlin : Measurable (fun g : Fin n → ℝ => A *ᵥ g) := by fun_prop
  have step1 : ∫ ω, y ω i * y ω j * (y ω ⬝ᵥ (M *ᵥ y ω)) ∂P
      = ∫ g, (A *ᵥ g) i * (A *ᵥ g) j * ((A *ᵥ g) ⬝ᵥ (M *ᵥ (A *ᵥ g))) ∂(stdGaussianPi n) := by
    have h1 := integral_map (μ := P) hyM hF.aestronglyMeasurable
    rw [← h1, hy, integral_map hlin.aemeasurable hF.aestronglyMeasurable]
  have hq : ∀ x : Fin n → ℝ, x ⬝ᵥ (M *ᵥ x) = ∑ k, ∑ l, M k l * (x k * x l) := by
    intro x
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have hexp : ∀ g : Fin n → ℝ, (A *ᵥ g) i * (A *ᵥ g) j * ((A *ᵥ g) ⬝ᵥ (M *ᵥ (A *ᵥ g)))
      = ∑ k, ∑ l, M k l * ((A i ⬝ᵥ g) * (A j ⬝ᵥ g) * (A k ⬝ᵥ g) * (A l ⬝ᵥ g)) := by
    intro g
    rw [hq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have e1 : (A *ᵥ g) k = A k ⬝ᵥ g := rfl
    have e2 : (A *ᵥ g) l = A l ⬝ᵥ g := rfl
    have e3 : (A *ᵥ g) i = A i ⬝ᵥ g := rfl
    have e4 : (A *ᵥ g) j = A j ⬝ᵥ g := rfl
    rw [e1, e2, e3, e4]
    ring
  have hint : ∀ k l : Fin n, Integrable (fun g : Fin n → ℝ =>
      (A i ⬝ᵥ g) * (A j ⬝ᵥ g) * (A k ⬝ᵥ g) * (A l ⬝ᵥ g)) (stdGaussianPi n) :=
    fun k l => gauss_lin4_integrable _ _ _ _
  have hval : ∫ g, (A *ᵥ g) i * (A *ᵥ g) j * ((A *ᵥ g) ⬝ᵥ (M *ᵥ (A *ᵥ g))) ∂(stdGaussianPi n)
      = ∑ k, ∑ l, M k l * ((A i ⬝ᵥ A j) * (A k ⬝ᵥ A l) + (A i ⬝ᵥ A k) * (A j ⬝ᵥ A l)
          + (A i ⬝ᵥ A l) * (A j ⬝ᵥ A k)) := by
    simp only [hexp]
    rw [integral_finset_sum (Finset.univ) (f := fun k g => ∑ l, M k l *
        ((A i ⬝ᵥ g) * (A j ⬝ᵥ g) * (A k ⬝ᵥ g) * (A l ⬝ᵥ g)))
      (fun k _ => integrable_finset_sum _ fun l _ => (hint k l).const_mul _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finset_sum _ (fun l _ => (hint k l).const_mul _)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul]
    congr 1
    rw [gauss_lin4]
  have hL : ∀ a b, Λ a b = A a ⬝ᵥ A b := by
    intro a b
    rw [hΛ]
    simp [Matrix.mul_apply, dotProduct]
  have hΛs : Λᵀ = Λ := by
    rw [hΛ, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [step1, hval]
  simp only [← hL]
  exact quartic_alg Λ M hΛs hM i j

/-- Instance of `isserlis_wick` (sign-SGD #7, #23): for `Δ ∈ ℝ^{n×n}`, `r, q ∈ ℝⁿ` and
independent standard Gaussian vectors `w, z ~ N(0, I_n)`,
`E[(rᵀw)(qᵀz)(zᵀΔw)] = qᵀΔr`. The expectation is over the product law of `(w, z)`. -/
theorem gaussian_trilinear_moment (n : ℕ) (Δ : Matrix (Fin n) (Fin n) ℝ) (r q : Fin n → ℝ) :
    ∫ p : (Fin n → ℝ) × (Fin n → ℝ),
        (r ⬝ᵥ p.1) * (q ⬝ᵥ p.2) * (p.2 ⬝ᵥ (Δ *ᵥ p.1))
      ∂((stdGaussianPi n).prod (stdGaussianPi n))
      = q ⬝ᵥ (Δ *ᵥ r) := by
  have e1 : ∀ w z : Fin n → ℝ, (r ⬝ᵥ w) * (q ⬝ᵥ z) = ∑ a, ∑ b, (r a * w a) * (q b * z b) := by
    intro w z
    simp only [dotProduct]
    rw [Finset.sum_mul_sum]
  have e2 : ∀ w z : Fin n → ℝ, z ⬝ᵥ (Δ *ᵥ w) = ∑ c, ∑ e, z c * (Δ c e * w e) := by
    intro w z
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  have expand : ∀ p : (Fin n → ℝ) × (Fin n → ℝ),
      (r ⬝ᵥ p.1) * (q ⬝ᵥ p.2) * (p.2 ⬝ᵥ (Δ *ᵥ p.1))
        = ∑ a, ∑ b, ∑ c, ∑ e, (r a * q b * Δ c e) * ((p.1 a * p.1 e) * (p.2 b * p.2 c)) := by
    intro p
    rw [e1, e2, ← sum4_prod]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => by ring
  have hI : ∀ a b c e : Fin n, Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      (r a * q b * Δ c e) * ((p.1 a * p.1 e) * (p.2 b * p.2 c)))
      ((stdGaussianPi n).prod (stdGaussianPi n)) := fun a b c e =>
    ((Integrable.mul_prod (gauss_two_integrable a e) (gauss_two_integrable b c)).const_mul _)
  have hval : ∫ p : (Fin n → ℝ) × (Fin n → ℝ), (r ⬝ᵥ p.1) * (q ⬝ᵥ p.2) * (p.2 ⬝ᵥ (Δ *ᵥ p.1))
      ∂((stdGaussianPi n).prod (stdGaussianPi n))
      = ∑ a, ∑ b, ∑ c, ∑ e, (r a * q b * Δ c e) * ((if a = e then (1 : ℝ) else 0)
          * (if b = c then (1 : ℝ) else 0)) := by
    simp only [expand]
    rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ fun b _ =>
      integrable_finset_sum _ fun c _ => integrable_finset_sum _ fun e _ => hI a b c e)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finset_sum _ (fun b _ => integrable_finset_sum _ fun c _ =>
      integrable_finset_sum _ fun e _ => hI a b c e)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_finset_sum _ (fun c _ => integrable_finset_sum _ fun e _ => hI a b c e)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_finset_sum _ (fun e _ => hI a b c e)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [integral_const_mul, integral_prod_mul (fun w : Fin n → ℝ => w a * w e)
      (fun z : Fin n → ℝ => z b * z c), gauss_two_index, gauss_two_index]
  rw [hval]
  simp [mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', dotProduct, Matrix.mulVec,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-- Instance of `isserlis_wick` (sign-SGD #23, Gaussian pairing): let `A ∈ ℝ^{n×n}`,
`Λ = A Aᵀ`, and let `y` have the law of `A g` with `g ~ N(0, I_n)`, i.e. `y ~ N(0, Λ)`. For a
symmetric `M`, `E[y ⊗ y (yᵀ M y)] = Tr(Λ M) Λ + 2 Λ M Λ`, written entrywise. -/
theorem gaussian_quartic_covariance (n : ℕ) (A M Λ : Matrix (Fin n) (Fin n) ℝ)
    (hΛ : Λ = A * Aᵀ) (hM : Mᵀ = M)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (y : Ω → Fin n → ℝ)
    (hy : P.map y = (stdGaussianPi n).map (fun g => A *ᵥ g)) (hyM : AEMeasurable y P)
    (i j : Fin n) :
    ∫ ω, y ω i * y ω j * (y ω ⬝ᵥ (M *ᵥ y ω)) ∂P
      = Matrix.trace (Λ * M) * Λ i j + 2 * (Λ * M * Λ) i j :=
  gaussian_quartic_covariance_of_aem n A M Λ hΛ hM P y hy hyM i j

/-- Instance of `isserlis_wick` (sign-SGD #23, #24): for `u ∈ ℝⁿ`, `w ~ N(0, I_n)` and a
coordinate `j`, `E[(uᵀw)² w_j²] = ‖u‖² + 2 u_j²`. -/
theorem gaussian_weighted_square_moment (n : ℕ) (u : Fin n → ℝ) (j : Fin n) :
    ∫ w, (u ⬝ᵥ w) ^ 2 * w j ^ 2 ∂(stdGaussianPi n)
      = (∑ a, u a ^ 2) + 2 * u j ^ 2 := by
  have key : ∀ w : Fin n → ℝ, (u ⬝ᵥ w) ^ 2 * w j ^ 2
      = (u ⬝ᵥ w) * (u ⬝ᵥ w) * (Pi.single j 1 ⬝ᵥ w) * (Pi.single j 1 ⬝ᵥ w) :=
    fun w => by simp only [single_dotProduct, one_mul]; ring
  simp only [key]
  rw [gauss_lin4]
  have h1 : u ⬝ᵥ u = ∑ a, u a ^ 2 := by simp [dotProduct, sq]
  have h2 : (Pi.single j (1 : ℝ) : Fin n → ℝ) ⬝ᵥ Pi.single j 1 = 1 := by
    simp [dotProduct, Pi.single_apply]
  have h3 : u ⬝ᵥ Pi.single j (1 : ℝ) = u j := by simp [dotProduct_single]
  rw [h1, h2, h3]
  ring

/-- Instance of `isserlis_wick` (sign-SGD #23): for `u ∈ ℝⁿ`, `w ~ N(0, I_n)` and a coordinate
`j`, `E[(uᵀw) w_j] = u_j`. -/
theorem gaussian_weighted_linear_moment (n : ℕ) (u : Fin n → ℝ) (j : Fin n) :
    ∫ w, (u ⬝ᵥ w) * w j ∂(stdGaussianPi n) = u j := by
  have key : ∀ w : Fin n → ℝ, (u ⬝ᵥ w) * w j = (u ⬝ᵥ w) * (Pi.single j 1 ⬝ᵥ w) :=
    fun w => by simp [single_dotProduct]
  simp only [key]
  rw [gauss_lin2, dotProduct_single]
  simp

private lemma poly_zero_volume_null (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) :
    volume {x : Fin n → ℝ | MvPolynomial.eval x p = 0} = 0 := by
  induction n with
  | zero =>
    have hc : ∀ x : Fin 0 → ℝ, MvPolynomial.eval x p ≠ 0 := by
      intro x
      rw [MvPolynomial.eq_C_of_isEmpty p, MvPolynomial.eval_C]
      intro h
      apply hp
      rw [MvPolynomial.eq_C_of_isEmpty p, h]
      simp
    have : {x : Fin 0 → ℝ | MvPolynomial.eval x p = 0} = ∅ := by
      ext x; simpa using hc x
    rw [this, measure_empty]
  | succ n ih =>
    set q := MvPolynomial.finSuccEquiv ℝ n p with hq_def
    have hq : q ≠ 0 := by
      intro h
      apply hp
      have h0 : (MvPolynomial.finSuccEquiv ℝ n) p = (MvPolynomial.finSuccEquiv ℝ n) 0 := by
        rw [map_zero]; exact h
      exact (MvPolynomial.finSuccEquiv ℝ n).injective h0
    set c := q.leadingCoeff with hc_def
    have hc : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
    have hcnull : volume {y : Fin n → ℝ | MvPolynomial.eval y c = 0} = 0 := ih c hc
    set S : Set (Fin (n + 1) → ℝ) := {x | MvPolynomial.eval x p = 0} with hS_def
    have hSm : MeasurableSet S :=
      (isClosed_eq (MvPolynomial.continuous_eval p) continuous_const).measurableSet
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 with he_def
    have hpres : MeasurePreserving e volume (volume.prod volume) :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have hT : MeasurableSet (e.symm ⁻¹' S) := e.symm.measurable hSm
    have hSeq : S = e ⁻¹' (e.symm ⁻¹' S) := by
      ext x; simp
    have hslice : ∀ t : ℝ, ∀ y : Fin n → ℝ, e.symm (t, y) = Fin.cons t y := by
      intro t y
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [he_def]
      · simp [he_def, MeasurableEquiv.piFinSuccAbove]
    rw [hSeq, hpres.measure_preimage hT.nullMeasurableSet, Measure.prod_apply_symm hT]
    have hae : ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)),
        volume ((fun t : ℝ => (t, y)) ⁻¹' (e.symm ⁻¹' S)) = 0 := by
      rw [ae_iff]
      refine measure_mono_null ?_ hcnull
      intro y hy
      show MvPolynomial.eval y c = 0
      by_contra hcy
      apply hy
      have hlc := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero
        (MvPolynomial.eval y) hcy
      have hr : Polynomial.map (MvPolynomial.eval y) q ≠ 0 := by
        intro h0
        rw [h0, Polynomial.leadingCoeff_zero] at hlc
        exact hcy hlc.symm
      have hset : (fun t : ℝ => (t, y)) ⁻¹' (e.symm ⁻¹' S)
          = {x : ℝ | (Polynomial.map (MvPolynomial.eval y) q).IsRoot x} := by
        ext t
        simp only [Set.mem_preimage, Set.mem_setOf_eq, hS_def, hslice,
          MvPolynomial.eval_eq_eval_mv_eval', Polynomial.IsRoot.def]
        exact Iff.rfl
      rw [hset]
      exact (Polynomial.finite_setOf_isRoot hr).measure_zero _
    exact (lintegral_congr_ae hae).trans lintegral_zero

private lemma gauss_pi_absCont (n : ℕ) :
    Measure.pi (fun _ : Fin n => gaussianReal 0 1) ≪ (volume : Measure (Fin n → ℝ)) := by
  induction n with
  | zero =>
    intro S hS
    have h1 : Measure.pi (fun _ : Fin 0 => gaussianReal 0 1) = Measure.dirac (fun i => isEmptyElim i) :=
      Measure.pi_of_empty _ _
    have h2 : (volume : Measure (Fin 0 → ℝ)) = Measure.dirac (fun i => isEmptyElim i) := by
      rw [volume_pi]
      exact Measure.pi_of_empty _ _
    rw [h2] at hS
    rw [h1]
    exact hS
  | succ n ih =>
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 with he_def
    have hpres : MeasurePreserving e (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1))
        ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) 0
    have hpresV : MeasurePreserving e (volume : Measure (Fin (n + 1) → ℝ))
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have hprod : (gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)
        ≪ (volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)) :=
      Measure.AbsolutelyContinuous.prod (gaussianReal_absolutelyContinuous 0 one_ne_zero) ih
    have key : ∀ T : Set (Fin (n + 1) → ℝ), MeasurableSet T → volume T = 0 →
        Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) T = 0 := by
      intro T hT hT0
      have hW : MeasurableSet (e.symm ⁻¹' T) := e.symm.measurable hT
      have hSeq : T = e ⁻¹' (e.symm ⁻¹' T) := by
        ext x; simp
      have hW0 : ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) (e.symm ⁻¹' T) = 0 := by
        rw [← hpresV.measure_preimage hW.nullMeasurableSet, ← hSeq]
        exact hT0
      rw [hSeq, hpres.measure_preimage hW.nullMeasurableSet]
      exact hprod hW0
    intro S hS
    refine le_antisymm ?_ zero_le
    calc Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) S
        ≤ Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) (toMeasurable volume S) :=
          measure_mono (subset_toMeasurable _ _)
      _ = 0 := key _ (measurableSet_toMeasurable _ _) (by rw [measure_toMeasurable]; exact hS)

/-! ## Sheppard's arcsine law -/

section SheppardAux
open Set Real
private lemma cos_zero_null : (volume : Measure ℝ) {θ : ℝ | Real.cos θ = 0} = 0 := by
  have : {θ : ℝ | Real.cos θ = 0} ⊆ Set.range (fun k : ℤ => ((2 * (k : ℝ) + 1) * π / 2)) := by
    intro θ hθ
    obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.1 hθ
    exact ⟨k, hk.symm⟩
  exact measure_mono_null this ((Set.countable_range _).measure_zero _)

private lemma cos_sub_zero_null (α : ℝ) :
    (volume : Measure ℝ) {θ : ℝ | Real.cos (θ - α) = 0} = 0 := by
  have h := cos_zero_null
  have : {θ : ℝ | Real.cos (θ - α) = 0} = (fun θ => θ - α) ⁻¹' {θ : ℝ | Real.cos θ = 0} := rfl
  rw [this]
  have := (measurePreserving_sub_right (volume : Measure ℝ) α).measure_preimage
    (s := {θ : ℝ | Real.cos θ = 0}) ?_
  · rw [this]; exact h
  · exact (isClosed_eq Real.continuous_cos continuous_const).measurableSet.nullMeasurableSet

private lemma sign_ne_iff_of_ne {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    SignType.sign x ≠ SignType.sign y ↔ x * y < 0 := by
  rcases lt_or_gt_of_ne hx with h1 | h1 <;> rcases lt_or_gt_of_ne hy with h2 | h2
  · simp [_root_.sign_neg h1, _root_.sign_neg h2, (mul_pos_of_neg_of_neg h1 h2).not_gt]
  · simp [_root_.sign_neg h1, _root_.sign_pos h2, mul_neg_of_neg_of_pos h1 h2]
  · simp [_root_.sign_pos h1, _root_.sign_neg h2, mul_neg_of_pos_of_neg h1 h2]
  · simp [_root_.sign_pos h1, _root_.sign_pos h2, (mul_pos h1 h2).not_gt]

private lemma ang_i {α θ : ℝ} (h0 : 0 ≤ α) (hπ : α ≤ π) (h1 : -(π / 2) < θ) (h2 : θ < π / 2) :
    Real.cos θ * Real.cos (θ - α) < 0 ↔ θ < α - π / 2 := by
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨h1, h2⟩
  rw [mul_neg_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · by_contra hh
      push_neg at hh
      have : 0 ≤ Real.cos (θ - α) :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
      linarith
    · linarith
  · intro h
    left
    refine ⟨hc, ?_⟩
    rw [← Real.cos_neg]
    exact Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)

private lemma ang_ii {α θ : ℝ} (h0 : 0 ≤ α) (hπ : α ≤ π) (h1 : π / 2 < θ) (h2 : θ < π) :
    Real.cos θ * Real.cos (θ - α) < 0 ↔ θ < α + π / 2 := by
  have hc : Real.cos θ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt h1 (by linarith)
  rw [mul_neg_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · linarith
    · by_contra hh
      push_neg at hh
      have : Real.cos (θ - α) ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
      linarith
  · intro h
    right
    refine ⟨hc, ?_⟩
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

private lemma ang_iii {α θ : ℝ} (h0 : 0 ≤ α) (hπ : α ≤ π) (h1 : -π < θ) (h2 : θ < -(π / 2)) :
    Real.cos θ * Real.cos (θ - α) < 0 ↔ θ < α - 3 * π / 2 := by
  have hc : Real.cos θ < 0 := by
    rw [← Real.cos_neg]
    exact Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
  rw [mul_neg_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · linarith
    · by_contra hh
      push_neg at hh
      have : Real.cos (-(θ - α)) ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
      rw [Real.cos_neg] at this
      linarith
  · intro h
    right
    refine ⟨hc, ?_⟩
    have : Real.cos (θ - α + 2 * π) = Real.cos (θ - α) := Real.cos_add_two_pi _
    rw [← this]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

private lemma ang_measure {α : ℝ} (h0 : 0 ≤ α) (hπ : α ≤ π) :
    (volume : Measure ℝ) {θ : ℝ | θ ∈ Ioo (-π) π ∧
      SignType.sign (Real.cos θ) ≠ SignType.sign (Real.cos (θ - α))} = ENNReal.ofReal (2 * α) := by
  set D : Set ℝ := {θ : ℝ | θ ∈ Ioo (-π) π ∧
      SignType.sign (Real.cos θ) ≠ SignType.sign (Real.cos (θ - α))} with hD
  set D2 : Set ℝ := {θ : ℝ | θ ∈ Ioo (-π) π ∧ Real.cos θ * Real.cos (θ - α) < 0} with hD2
  have hD2D : D2 ⊆ D := by
    rintro θ ⟨hθ, hp⟩
    refine ⟨hθ, ?_⟩
    have hx : Real.cos θ ≠ 0 := fun h => by simp [h] at hp
    have hy : Real.cos (θ - α) ≠ 0 := fun h => by simp [h] at hp
    exact (sign_ne_iff_of_ne hx hy).2 hp
  have hDD2 : D ⊆ D2 ∪ ({θ | Real.cos θ = 0} ∪ {θ | Real.cos (θ - α) = 0}) := by
    rintro θ ⟨hθ, hp⟩
    by_cases hx : Real.cos θ = 0
    · exact Or.inr (Or.inl hx)
    by_cases hy : Real.cos (θ - α) = 0
    · exact Or.inr (Or.inr hy)
    exact Or.inl ⟨hθ, (sign_ne_iff_of_ne hx hy).1 hp⟩
  have hnull : (volume : Measure ℝ) ({θ | Real.cos θ = 0} ∪ {θ | Real.cos (θ - α) = 0}) = 0 :=
    measure_union_null cos_zero_null (cos_sub_zero_null α)
  have hvol : volume D = volume D2 := by
    refine le_antisymm ?_ (measure_mono hD2D)
    calc volume D ≤ volume (D2 ∪ ({θ | Real.cos θ = 0} ∪ {θ | Real.cos (θ - α) = 0})) :=
          measure_mono hDD2
      _ ≤ volume D2 + volume ({θ | Real.cos θ = 0} ∪ {θ | Real.cos (θ - α) = 0}) :=
          measure_union_le _ _
      _ = volume D2 := by rw [hnull, add_zero]
  have hπ0 : 0 < π := Real.pi_pos
  have hsplit : D2 = (Ioo (-(π / 2)) (α - π / 2) ∪ Ioo (π / 2) (min π (α + π / 2))) ∪
      Ioo (-π) (α - 3 * π / 2) := by
    ext θ
    simp only [hD2, mem_setOf_eq, mem_union, mem_Ioo, lt_min_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp⟩
      rcases lt_trichotomy θ (-(π / 2)) with ha | ha | ha
      · right; exact ⟨h1, (ang_iii h0 hπ h1 ha).1 hp⟩
      · subst ha; simp at hp
      · rcases lt_trichotomy θ (π / 2) with hb | hb | hb
        · left; left; exact ⟨ha, (ang_i h0 hπ ha hb).1 hp⟩
        · subst hb; simp at hp
        · left; right; exact ⟨hb, h2, (ang_ii h0 hπ hb h2).1 hp⟩
    · rintro ((⟨h1, h2⟩ | ⟨h1, h2, h3⟩) | ⟨h1, h2⟩)
      · exact ⟨⟨by linarith, by linarith⟩, (ang_i h0 hπ h1 (by linarith)).2 h2⟩
      · exact ⟨⟨by linarith, h2⟩, (ang_ii h0 hπ h1 h2).2 h3⟩
      · exact ⟨⟨h1, by linarith⟩, (ang_iii h0 hπ h1 (by linarith)).2 h2⟩
  rw [hvol, hsplit]
  have hdis1 : Disjoint (Ioo (-(π / 2)) (α - π / 2)) (Ioo (π / 2) (min π (α + π / 2))) := by
    rw [Set.disjoint_left]
    rintro x ⟨_, hx⟩ ⟨hy, _⟩
    linarith
  have hdis2 : Disjoint (Ioo (-(π / 2)) (α - π / 2) ∪ Ioo (π / 2) (min π (α + π / 2)))
      (Ioo (-π) (α - 3 * π / 2)) := by
    rw [Set.disjoint_left]
    rintro x (⟨hx, _⟩ | ⟨hx, _⟩) ⟨_, hy⟩ <;> linarith
  rw [measure_union hdis2 measurableSet_Ioo, measure_union hdis1 measurableSet_Ioo]
  simp only [Real.volume_Ioo]
  rcases le_total α (π / 2) with h | h
  · rw [min_eq_right (by linarith), ENNReal.ofReal_of_nonpos (p := α - 3 * π / 2 - -π) (by linarith),
      add_zero, ← ENNReal.ofReal_add (by linarith) (by linarith)]
    congr 1; ring
  · rw [min_eq_left (by linarith), ← ENNReal.ofReal_add (by linarith) (by linarith),
      ← ENNReal.ofReal_add (by linarith) (by linarith)]
    congr 1; ring

private lemma sign_ne_measurable {α : Type*} [MeasurableSpace α] {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {a | SignType.sign (f a) ≠ SignType.sign (g a)} := by
  have : {a | SignType.sign (f a) ≠ SignType.sign (g a)} =
      (symmDiff {a | 0 < f a} {a | 0 < g a} ∪ symmDiff {a | f a < 0} {a | g a < 0}) := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_symmDiff]
    rcases lt_trichotomy (f a) 0 with h1 | h1 | h1 <;>
      rcases lt_trichotomy (g a) 0 with h2 | h2 | h2 <;>
      simp [h1, h2, _root_.sign_neg, _root_.sign_pos, h1.not_gt, h2.not_gt, h1.le, h2.le]
  rw [this]
  exact (((measurableSet_lt measurable_const hf).symmDiff (measurableSet_lt measurable_const hg)).union
    ((measurableSet_lt hf measurable_const).symmDiff (measurableSet_lt hg measurable_const)))

private lemma gpdf_mul (x y : ℝ) :
    gaussianPDF 0 1 x * gaussianPDF 0 1 y =
      ENNReal.ofReal ((2 * π)⁻¹ * Real.exp (-((x ^ 2 + y ^ 2) / 2))) := by
  unfold gaussianPDF gaussianPDFReal
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have h : (Real.sqrt (2 * π)) ⁻¹ * (Real.sqrt (2 * π))⁻¹ = (2 * π)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  have e : Real.exp (-x ^ 2 / 2) * Real.exp (-y ^ 2 / 2) = Real.exp (-((x ^ 2 + y ^ 2) / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc _ = ((Real.sqrt (2 * π)) ⁻¹ * (Real.sqrt (2 * π))⁻¹) *
        (Real.exp (-x ^ 2 / 2) * Real.exp (-y ^ 2 / 2)) := by ring
    _ = _ := by rw [h, e]

private lemma radial_integral :
    ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r * Real.exp (-(r ^ 2 / 2))) = 1 := by
  have hint : IntegrableOn (fun r : ℝ => r * Real.exp (-(r ^ 2 / 2))) (Ioi 0) := by
    have := (integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).integrableOn
      (s := Ioi (0:ℝ))
    refine this.congr_fun (fun r _ => ?_) measurableSet_Ioi
    simp only
    congr 2; ring
  have hderiv : ∀ x ∈ Ici (0:ℝ), HasDerivAt (fun r : ℝ => -Real.exp (-(r ^ 2 / 2)))
      (x * Real.exp (-(x ^ 2 / 2))) x := by
    intro x _
    have h1 : HasDerivAt (fun r : ℝ => -(r ^ 2 / 2)) (-x) x := by
      have := ((hasDerivAt_pow 2 x).div_const 2).neg
      convert this using 1
      simp
    have := (h1.exp).neg
    convert this using 1
    ring
  have htend : Filter.Tendsto (fun r : ℝ => -Real.exp (-(r ^ 2 / 2))) Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun r : ℝ => -(r ^ 2 / 2)) Filter.atTop Filter.atBot := by
      apply Filter.tendsto_neg_atTop_atBot.comp
      apply Filter.Tendsto.atTop_div_const (by norm_num)
      exact Filter.tendsto_pow_atTop (by norm_num)
    simpa using (Real.tendsto_exp_atBot.comp h).neg
  have hI := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] fun r : ℝ => r * Real.exp (-(r ^ 2 / 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact (mul_pos hr (Real.exp_pos _)).le
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, hI]
  simp

private lemma sector_gauss {α : ℝ} (h0 : 0 ≤ α) (hπ : α ≤ π) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1))
      {p : ℝ × ℝ | SignType.sign p.1 ≠ SignType.sign (Real.cos α * p.1 + Real.sin α * p.2)} =
      ENNReal.ofReal (α / π) := by
  set S : Set (ℝ × ℝ) :=
    {p : ℝ × ℝ | SignType.sign p.1 ≠ SignType.sign (Real.cos α * p.1 + Real.sin α * p.2)} with hS
  have hSm : MeasurableSet S :=
    sign_ne_measurable (f := fun p : ℝ × ℝ => p.1)
      (g := fun p : ℝ × ℝ => Real.cos α * p.1 + Real.sin α * p.2) (by fun_prop) (by fun_prop)
  set E : Set ℝ := {θ : ℝ | SignType.sign (Real.cos θ) ≠ SignType.sign (Real.cos (θ - α))} with hE
  have hEm : MeasurableSet E :=
    sign_ne_measurable (f := fun θ : ℝ => Real.cos θ) (g := fun θ : ℝ => Real.cos (θ - α))
      (by fun_prop) (by fun_prop)
  have hg : gaussianReal 0 1 = volume.withDensity (gaussianPDF 0 1) :=
    gaussianReal_of_var_ne_zero 0 one_ne_zero
  rw [hg, prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1),
    withDensity_apply _ hSm, ← Measure.volume_eq_prod, ← lintegral_indicator hSm]
  set F : ℝ × ℝ → ENNReal := S.indicator (fun z => gaussianPDF 0 1 z.1 * gaussianPDF 0 1 z.2)
    with hF
  rw [← lintegral_comp_polarCoord_symm F]
  have hmem : ∀ r θ : ℝ, 0 < r → ((r * Real.cos θ, r * Real.sin θ) ∈ S ↔ θ ∈ E) := by
    intro r θ hr
    have e : Real.cos α * (r * Real.cos θ) + Real.sin α * (r * Real.sin θ) =
        r * Real.cos (θ - α) := by
      rw [Real.cos_sub]; ring
    simp only [hS, hE, mem_setOf_eq, e, sign_mul, _root_.sign_pos hr, one_mul]
  have hpt : ∀ p ∈ polarCoord.target, ENNReal.ofReal p.1 • F (polarCoord.symm p) =
      ENNReal.ofReal ((2 * π)⁻¹ * (p.1 * Real.exp (-(p.1 ^ 2 / 2)))) * E.indicator 1 p.2 := by
    intro p hp
    rw [polarCoord_target] at hp
    obtain ⟨hr, hθ⟩ := hp
    have hr' : 0 < p.1 := hr
    rw [polarCoord_symm_apply]
    simp only [hF, smul_eq_mul]
    by_cases hθE : p.2 ∈ E
    · rw [indicator_of_mem ((hmem _ _ hr').2 hθE), indicator_of_mem hθE, gpdf_mul]
      simp only [Pi.one_apply, mul_one]
      rw [← ENNReal.ofReal_mul hr'.le]
      congr 1
      have : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq p.2]
      rw [this]; ring
    · rw [indicator_of_notMem (fun h => hθE ((hmem _ _ hr').1 h)), indicator_of_notMem hθE]
      simp
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hpt, polarCoord_target,
    Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [lintegral_prod_mul (f := fun r : ℝ => ENNReal.ofReal ((2 * π)⁻¹ * (r * Real.exp (-(r ^ 2 / 2)))))
    (g := fun θ : ℝ => E.indicator (1 : ℝ → ENNReal) θ) (by fun_prop)
    ((measurable_one.indicator hEm).aemeasurable)]
  have h1 : ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal ((2 * π)⁻¹ * (r * Real.exp (-(r ^ 2 / 2)))) =
      ENNReal.ofReal (2 * π)⁻¹ := by
    simp_rw [ENNReal.ofReal_mul (inv_nonneg.2 (by positivity : (0:ℝ) ≤ 2 * π))]
    rw [lintegral_const_mul _ (by fun_prop), radial_integral, mul_one]
  have h2 : ∫⁻ θ in Ioo (-π) π, E.indicator (1 : ℝ → ENNReal) θ = ENNReal.ofReal (2 * α) := by
    rw [lintegral_indicator_one hEm, Measure.restrict_apply hEm, ← ang_measure h0 hπ]
    congr 1
    ext θ
    simp [hE, and_comm]
  rw [h1, h2, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp


private lemma charFun_pair {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (g h : Ω → ℝ) (ρ : ℝ) (hlaw : HasGaussianLaw (fun ω => (g ω, h ω)) Q)
    (hmean_g : ∫ ω, g ω ∂Q = 0) (hmean_h : ∫ ω, h ω ∂Q = 0)
    (hvar_g : ∫ ω, g ω ^ 2 ∂Q = 1) (hvar_h : ∫ ω, h ω ^ 2 ∂Q = 1)
    (hcov : ∫ ω, g ω * h ω ∂Q = ρ) (L : StrongDual ℝ (ℝ × ℝ)) :
    charFunDual (Q.map (fun ω => (g ω, h ω))) L =
      Complex.exp (((-(((L (1, 0)) ^ 2 + (L (0, 1)) ^ 2 + 2 * (L (1, 0)) * (L (0, 1)) * ρ) / 2) : ℝ)
        : ℂ)) := by
  have hg : MemLp g 2 Q := hlaw.fst.memLp_two
  have hh : MemLp h 2 Q := hlaw.snd.memLp_two
  have hgi : Integrable g Q := hg.integrable (by norm_num)
  have hhi : Integrable h Q := hh.integrable (by norm_num)
  have hg2 : Integrable (fun ω => g ω ^ 2) Q := hg.integrable_sq
  have hh2 : Integrable (fun ω => h ω ^ 2) Q := hh.integrable_sq
  have hgh : Integrable (fun ω => g ω * h ω) Q := hg.integrable_mul hh
  set a := L (1, 0) with ha
  set b := L (0, 1) with hb
  have hL : ∀ x y : ℝ, L (x, y) = a * x + b * y := by
    intro x y
    have : ((x, y) : ℝ × ℝ) = x • ((1, 0) : ℝ × ℝ) + y • ((0, 1) : ℝ × ℝ) := by simp
    rw [this, map_add, map_smul, map_smul]
    simp [ha, hb]
    ring
  rw [hlaw.charFunDual_map_eq_fun L]
  simp only [hL]
  have hm : ∫ ω, (a * g ω + b * h ω) ∂Q = 0 := by
    rw [integral_add (hgi.const_mul a) (hhi.const_mul b), integral_const_mul, integral_const_mul,
      hmean_g, hmean_h]; ring
  have hv : Var[fun ω => a * g ω + b * h ω; Q] =
      a ^ 2 + b ^ 2 + 2 * a * b * ρ := by
    have hae : AEMeasurable (fun ω => a * g ω + b * h ω) Q :=
      ((hgi.const_mul a).add (hhi.const_mul b)).aemeasurable
    rw [variance_of_integral_eq_zero hae hm]
    have : ∀ ω, (a * g ω + b * h ω) ^ 2 =
        a ^ 2 * g ω ^ 2 + 2 * a * b * (g ω * h ω) + b ^ 2 * h ω ^ 2 := fun ω => by ring
    simp_rw [this]
    have i1 : Integrable (fun ω => a ^ 2 * g ω ^ 2) Q := hg2.const_mul _
    have i2 : Integrable (fun ω => 2 * a * b * (g ω * h ω)) Q := hgh.const_mul _
    have i3 : Integrable (fun ω => b ^ 2 * h ω ^ 2) Q := hh2.const_mul _
    have i12 : Integrable (fun ω => a ^ 2 * g ω ^ 2 + 2 * a * b * (g ω * h ω)) Q := i1.add i2
    rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
      integral_const_mul, hvar_g, hvar_h, hcov]
    ring
  rw [hm, hv]
  congr 1
  push_cast
  ring

private lemma std_law (α : ℝ) :
    ∃ (_ : HasGaussianLaw (fun p : ℝ × ℝ => (p.1, Real.cos α * p.1 + Real.sin α * p.2))
        ((gaussianReal 0 1).prod (gaussianReal 0 1))),
      ∀ L : StrongDual ℝ (ℝ × ℝ),
        charFunDual (((gaussianReal 0 1).prod (gaussianReal 0 1)).map
          (fun p : ℝ × ℝ => (p.1, Real.cos α * p.1 + Real.sin α * p.2))) L =
        Complex.exp (((-(((L (1, 0)) ^ 2 + (L (0, 1)) ^ 2 + 2 * (L (1, 0)) * (L (0, 1)) *
          Real.cos α) / 2) : ℝ) : ℂ)) := by
  set ν : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1) with hν
  set T : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (Real.cos α • ContinuousLinearMap.fst ℝ ℝ ℝ + Real.sin α • ContinuousLinearMap.snd ℝ ℝ ℝ)
    with hT
  have hTf : (fun p : ℝ × ℝ => (p.1, Real.cos α * p.1 + Real.sin α * p.2)) = ⇑T := by
    ext p <;> simp [hT]
  have hlaw : HasGaussianLaw (fun p : ℝ × ℝ => (p.1, Real.cos α * p.1 + Real.sin α * p.2)) ν := by
    rw [hTf]
    have : IsGaussian (ν.map T) := inferInstance
    exact IsGaussian.hasGaussianLaw T.continuous.aemeasurable
  refine ⟨hlaw, fun L => ?_⟩
  have hm1 : ∫ x, x ∂(gaussianReal 0 1) = 0 := integral_id_gaussianReal
  have hm2 : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
    have h := variance_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_of_integral_eq_zero aemeasurable_id (by simpa using hm1)] at h
    simpa using h
  have hf : MemLp (fun p : ℝ × ℝ => p.1) 2 ν :=
    IsGaussian.memLp_dual ν (ContinuousLinearMap.fst ℝ ℝ ℝ) 2 (by simp)
  have hs : MemLp (fun p : ℝ × ℝ => p.2) 2 ν :=
    IsGaussian.memLp_dual ν (ContinuousLinearMap.snd ℝ ℝ ℝ) 2 (by simp)
  have hfi : Integrable (fun p : ℝ × ℝ => p.1) ν := hf.integrable (by norm_num)
  have hsi : Integrable (fun p : ℝ × ℝ => p.2) ν := hs.integrable (by norm_num)
  have hf2 : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) ν := hf.integrable_sq
  have hs2 : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) ν := hs.integrable_sq
  have hfs : Integrable (fun p : ℝ × ℝ => p.1 * p.2) ν := hf.integrable_mul hs
  have e1 : ∫ p : ℝ × ℝ, p.1 ∂ν = 0 := by
    simpa [hν, integral_fun_fst (f := fun x : ℝ => x)] using hm1
  have e2 : ∫ p : ℝ × ℝ, p.2 ∂ν = 0 := by
    simpa [hν, integral_fun_snd (f := fun x : ℝ => x)] using hm1
  have e11 : ∫ p : ℝ × ℝ, p.1 ^ 2 ∂ν = 1 := by
    simpa [hν, integral_fun_fst (f := fun x : ℝ => x ^ 2)] using hm2
  have e22 : ∫ p : ℝ × ℝ, p.2 ^ 2 ∂ν = 1 := by
    simpa [hν, integral_fun_snd (f := fun x : ℝ => x ^ 2)] using hm2
  have e12 : ∫ p : ℝ × ℝ, p.1 * p.2 ∂ν = 0 := by
    have := integral_prod_mul (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
      (fun x : ℝ => x) (fun x : ℝ => x)
    simpa [hν, hm1] using this
  have c := charFun_pair ν (fun p : ℝ × ℝ => p.1)
    (fun p : ℝ × ℝ => Real.cos α * p.1 + Real.sin α * p.2) (Real.cos α) hlaw
    e1 (by
      rw [integral_add (hfi.const_mul _) (hsi.const_mul _), integral_const_mul, integral_const_mul,
        e1, e2]; ring)
    e11 (by
      have i1 : Integrable (fun p : ℝ × ℝ => Real.cos α ^ 2 * p.1 ^ 2) ν := hf2.const_mul _
      have i2 : Integrable (fun p : ℝ × ℝ => 2 * Real.cos α * Real.sin α * (p.1 * p.2)) ν :=
        hfs.const_mul _
      have i3 : Integrable (fun p : ℝ × ℝ => Real.sin α ^ 2 * p.2 ^ 2) ν := hs2.const_mul _
      have i12 : Integrable (fun p : ℝ × ℝ => Real.cos α ^ 2 * p.1 ^ 2 +
          2 * Real.cos α * Real.sin α * (p.1 * p.2)) ν := i1.add i2
      have : ∀ p : ℝ × ℝ, (Real.cos α * p.1 + Real.sin α * p.2) ^ 2 =
          Real.cos α ^ 2 * p.1 ^ 2 + 2 * Real.cos α * Real.sin α * (p.1 * p.2) +
            Real.sin α ^ 2 * p.2 ^ 2 := fun p => by ring
      simp_rw [this]
      rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
        integral_const_mul, e11, e22, e12]
      nlinarith [Real.sin_sq_add_cos_sq α])
    (by
      have i1 : Integrable (fun p : ℝ × ℝ => Real.cos α * p.1 ^ 2) ν := hf2.const_mul _
      have i2 : Integrable (fun p : ℝ × ℝ => Real.sin α * (p.1 * p.2)) ν := hfs.const_mul _
      have : ∀ p : ℝ × ℝ, p.1 * (Real.cos α * p.1 + Real.sin α * p.2) =
          Real.cos α * p.1 ^ 2 + Real.sin α * (p.1 * p.2) := fun p => by ring
      simp_rw [this]
      rw [integral_add i1 i2, integral_const_mul, integral_const_mul, e11, e12]; ring) L
  exact c

end SheppardAux

/-- Sheppard's formula (cited result `SheppardArcsine`, L-0.6b).

Let `(g, h)` be a jointly Gaussian pair of real random variables on a probability space, with
`E g = E h = 0`, `E g² = E h² = 1`, `E[g h] = ρ` and `ρ ∈ [-1, 1]`. Then
`P(sign g ≠ sign h) = arccos ρ / π`. The law of `(g, h)` is `N(0, [[1, ρ], [ρ, 1]])`, so the
statement depends only on `ρ`. -/
theorem sheppard_arcsine {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g h : Ω → ℝ) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (hlaw : HasGaussianLaw (fun ω => (g ω, h ω)) P)
    (hmean_g : ∫ ω, g ω ∂P = 0) (hmean_h : ∫ ω, h ω ∂P = 0)
    (hvar_g : ∫ ω, g ω ^ 2 ∂P = 1) (hvar_h : ∫ ω, h ω ^ 2 ∂P = 1)
    (hcov : ∫ ω, g ω * h ω ∂P = ρ) :
    P.real {ω | SignType.sign (g ω) ≠ SignType.sign (h ω)} = Real.arccos ρ / Real.pi := by
  have hcos : Real.cos (Real.arccos ρ) = ρ := Real.cos_arccos hρ.1 hρ.2
  have hα0 : 0 ≤ Real.arccos ρ := Real.arccos_nonneg ρ
  have hαReal.pi : Real.arccos ρ ≤ Real.pi := Real.arccos_le_pi ρ
  obtain ⟨_, hcfν⟩ := std_law (Real.arccos ρ)
  have hX : AEMeasurable (fun ω => (g ω, h ω)) P := hlaw.aemeasurable
  have hμ : P.map (fun ω => (g ω, h ω)) = ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      (fun p : ℝ × ℝ => (p.1, Real.cos (Real.arccos ρ) * p.1 + Real.sin (Real.arccos ρ) * p.2)) := by
    apply Measure.ext_of_charFunDual
    ext L
    rw [charFun_pair P g h ρ hlaw hmean_g hmean_h hvar_g hvar_h hcov L, hcfν L, hcos]
  have hS0 : MeasurableSet {p : ℝ × ℝ | SignType.sign p.1 ≠ SignType.sign p.2} :=
    sign_ne_measurable (f := fun p : ℝ × ℝ => p.1) (g := fun p : ℝ × ℝ => p.2)
      (by fun_prop) (by fun_prop)
  have hmeas : Measurable (fun p : ℝ × ℝ =>
      (p.1, Real.cos (Real.arccos ρ) * p.1 + Real.sin (Real.arccos ρ) * p.2)) := by fun_prop
  have hPA : P {ω | SignType.sign (g ω) ≠ SignType.sign (h ω)} =
      ENNReal.ofReal (Real.arccos ρ / Real.pi) := by
    rw [← sector_gauss hα0 hαReal.pi]
    have h1 : {ω | SignType.sign (g ω) ≠ SignType.sign (h ω)} =
        (fun ω => (g ω, h ω)) ⁻¹' {p : ℝ × ℝ | SignType.sign p.1 ≠ SignType.sign p.2} := rfl
    rw [h1, ← Measure.map_apply_of_aemeasurable hX hS0, hμ, Measure.map_apply hmeas hS0]
    rfl
  rw [Measure.real, hPA, ENNReal.toReal_ofReal (div_nonneg hα0 Real.pi_pos.le)]

/-! ## Null zero sets of polynomials -/

/-- The zero set of a nonzero real multivariate polynomial is Lebesgue-null (cited result
`PolyZeroSetNull`, L-0.6b).

If `p ∈ ℝ[x₁, …, x_d]` is not the zero polynomial, then `{x | p(x) = 0}` has Lebesgue measure
zero on `Fin d → ℝ`; hence it is null for every measure `μ ≪ volume` and in particular for the
product Gaussian `stdGaussianPi d`. -/
theorem poly_zero_set_null (d : ℕ) (p : MvPolynomial (Fin d) ℝ) (hp : p ≠ 0) :
    volume {x : Fin d → ℝ | MvPolynomial.eval x p = 0} = 0 ∧
    (∀ μ : Measure (Fin d → ℝ), μ ≪ volume →
        μ {x : Fin d → ℝ | MvPolynomial.eval x p = 0} = 0) ∧
    stdGaussianPi d {x : Fin d → ℝ | MvPolynomial.eval x p = 0} = 0 := by
  refine ⟨poly_zero_volume_null d p hp, fun μ hμ => hμ (poly_zero_volume_null d p hp), ?_⟩
  exact gauss_pi_absCont d (poly_zero_volume_null d p hp)

end GaussianFoundations
