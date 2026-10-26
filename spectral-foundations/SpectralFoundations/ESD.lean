import SpectralFoundations.Resolvent
import SpectralFoundations.Stieltjes
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Empirical spectral measures and their expectations

## Contents
* `eigMeasure A = ∑ₖ δ_{λₖ(A)}`, the unnormalized eigenvalue counting measure (mass `card n`), and
  `esd A = (card n)⁻¹ • eigMeasure A`, the empirical spectral distribution. Both use the total
  function `sortedEig`, so they are defined for every square matrix and depend measurably on it.
* Integral identities: `∫ f d(eigMeasure A) = ∑ₖ f(λₖ)` for every `f`; `= re tr f(A)` (continuous
  functional calculus) for Hermitian `A`; the resolvent case
  `∫ (x + t)⁻¹ d(eigMeasure A) = re tr R_A(−t)` with `R_A(−t) = negResolvent A t` of
  `SpectralFoundations.Resolvent`; the first moment `∫ x d(eigMeasure A) = re tr A`; mass; support
  in `[0, ∞)` for PSD `A`.
* Transform forms `negStieltjes_eigMeasure`, `negStieltjes_expectedEigMeasure` (imports `Stieltjes`).
* Giry measurability of `A ↦ eigMeasure A`, and the expected measures
  `expectedEigMeasure P A = P.bind (eigMeasure ∘ A)` and `expectedEsd P A = P.bind (esd ∘ A)`,
  with the mass, integral, resolvent, first-moment and support identities passed through the
  expectation.

## Glue note
The Muon glue needs `ζ = B⁻¹ • ∑ᵢ δ_{λᵢ(MMᵀ)}` averaged over `ω`. That is
`ENNReal.ofReal B⁻¹ • expectedEigMeasure P (fun ω => M ω * (M ω)ᵀ)`; `posSemidef_mul_transpose_self`
(Resolvent) supplies the PSD hypotheses and `AEMeasurable.mul_transpose_self` the kernel
measurability. The section "Scaled expected measures" packages the scalar: the instance
`isFiniteMeasure_ofReal_smul_expectedEigMeasure`, the real mass
`measureReal_ofReal_smul_expectedEigMeasure_univ`, the support
`ofReal_smul_expectedEigMeasure_Iio_zero`, the transform
`negStieltjes_ofReal_smul_expectedEigMeasure` (`negStieltjes_smul` with
`negStieltjes_expectedEigMeasure`), and the first moment
`integral_id_ofReal_smul_expectedEigMeasure`. Over `𝕜 = ℝ`, `RCLike.re` is removed by
`RCLike.re_to_real`, and `negResolvent (M * Mᵀ) t` is `gramResolvent M t` (Muon's `Rs`) by `rfl`.

## References
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, CUP 2010,
  §2.4 (empirical and expected spectral measures).

## Interface choices
* The primary object is the unnormalized `eigMeasure`. The glue normalizes by `B`, not by the
  dimension, and `esd` is a scalar multiple of it (`esd` is `0` for `n` empty, since
  `∞ • 0 = 0`).
* Expectations are Giry binds. Every expectation theorem assumes `AEMeasurable A P`, since `bind`
  of a non-measurable kernel is junk. Integrability hypotheses are explicit: the general integral
  identity asks for integrability of each `ω ↦ f (λₖ(A ω))`; the resolvent identity needs only
  `IsFiniteMeasure P` and a.e. PSD; the first-moment identity asks for integrability of
  `ω ↦ re tr (A ω)` and a.e. PSD.
* The structural lemma `expectedEigMeasure_eq_sum_map` (`= ∑ₖ P.map (λₖ ∘ A)`) is the
  recommended entry point for the proofs, because Mathlib has `lintegral_bind` but no Bochner
  `integral_bind`.
-/

open MeasureTheory Matrix Set Filter Topology
open scoped ENNReal ComplexOrder

noncomputable section

namespace SpectralFoundations

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Deterministic spectral measures -/

/-- The eigenvalue counting measure `∑ₖ δ_{λₖ(A)}` (mass `card n`), with `λₖ = sortedEig A k`. -/
def eigMeasure (A : Matrix n n 𝕜) : Measure ℝ :=
  ∑ k, Measure.dirac (sortedEig A k)

/-- The empirical spectral distribution `(card n)⁻¹ ∑ₖ δ_{λₖ(A)}`. -/
def esd (A : Matrix n n 𝕜) : Measure ℝ :=
  ((Fintype.card n : ℝ≥0∞)⁻¹) • eigMeasure A

/-- Evaluation on an arbitrary set: `eigMeasure A s = #{k : λₖ ∈ s}` as an indicator sum.
Proof route: `Measure.coe_finset_sum`, `Finset.sum_apply`, `Measure.dirac_apply`
(`MeasurableSingletonClass ℝ`, any set). -/
theorem eigMeasure_apply (A : Matrix n n 𝕜) (s : Set ℝ) :
    eigMeasure A s = ∑ k, s.indicator 1 (sortedEig A k) := by
  simp only [eigMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.dirac_apply]

/-- Total mass `card n`.
Proof route: `eigMeasure_apply` with `s = univ`, `indicator_univ`, `Finset.sum_const`,
`Finset.card_univ`, `Fintype.card_fin`. -/
theorem eigMeasure_univ (A : Matrix n n 𝕜) : eigMeasure A univ = Fintype.card n := by
  simp [eigMeasure_apply]

/-- `eigMeasure A` is a finite measure. Proof route: `eigMeasure_univ`, `ENNReal.natCast_ne_top`. -/
theorem isFiniteMeasure_eigMeasure (A : Matrix n n 𝕜) : IsFiniteMeasure (eigMeasure A) := by
  refine ⟨?_⟩
  rw [eigMeasure_univ]
  exact ENNReal.natCast_lt_top _

instance (A : Matrix n n 𝕜) : IsFiniteMeasure (eigMeasure A) := isFiniteMeasure_eigMeasure A

/-- Real total mass. Proof route: `measureReal_def`, `eigMeasure_univ`, `ENNReal.toReal_natCast`. -/
theorem measureReal_eigMeasure_univ (A : Matrix n n 𝕜) :
    (eigMeasure A).real univ = Fintype.card n := by
  rw [measureReal_def, eigMeasure_univ, ENNReal.toReal_natCast]

/-- Every function is integrable against `eigMeasure A`.
Proof route: `integrable_finset_sum_measure`; against `dirac a` every `f` is integrable, because
`f =ᵐ[dirac a] const (f a)` (`ae_dirac_eq`) and the measure is finite. -/
theorem integrable_eigMeasure (A : Matrix n n 𝕜) (f : ℝ → ℝ) : Integrable f (eigMeasure A) := by
  rw [eigMeasure, integrable_finsetSum_measure]
  intro k _
  exact integrable_dirac (by simp)

/-- `∫ f d(eigMeasure A) = ∑ₖ f(λₖ)` for every `f : ℝ → ℝ`.
Proof route: `integral_finset_sum_measure` (integrability from `integrable_eigMeasure`'s dirac
step) and `integral_dirac`. -/
theorem integral_eigMeasure (A : Matrix n n 𝕜) (f : ℝ → ℝ) :
    ∫ x, f x ∂(eigMeasure A) = ∑ k, f (sortedEig A k) := by
  rw [eigMeasure]
  rw [integral_finsetSum_measure]
  · simp only [integral_dirac]
  · intro k _
    exact integrable_dirac (by simp)

/-- Functional-calculus form: `∫ f d(eigMeasure A) = re tr f(A)` for Hermitian `A` and every `f`
(on a finite spectrum every function is continuous, so no continuity hypothesis is needed).
Proof route: `integral_eigMeasure`, `sum_sortedEig_comp hA`, `IsHermitian.cfc_eq`, and
`trace (U D U*) = trace D` for the unitary `eigenvectorUnitary` (`trace_mul_comm`), with
`trace_diagonal` and `RCLike.ofReal_re`. -/
theorem integral_eigMeasure_eq_re_trace_cfc {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (f : ℝ → ℝ) :
    ∫ x, f x ∂(eigMeasure A) = RCLike.re (trace (cfc f A)) := by
  rw [integral_eigMeasure, hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  have hU : star (hA.eigenvectorUnitary : Matrix n n 𝕜) *
      (hA.eigenvectorUnitary : Matrix n n 𝕜) = 1 := Unitary.coe_star_mul_self _
  rw [hU, Matrix.one_mul, Matrix.trace_diagonal, map_sum,
    sum_sortedEig_comp hA f]
  simp only [Function.comp_apply, RCLike.ofReal_re]

/-- Resolvent case: `∫ (x + t)⁻¹ d(eigMeasure A) = re tr R_A(−t)` for PSD `A` and `t > 0`.
Proof route: `integral_eigMeasure` and `re_trace_negResolvent_of_posSemidef`. -/
theorem integral_eigMeasure_resolvent {A : Matrix n n 𝕜} (hA : A.PosSemidef) {t : ℝ}
    (ht : 0 < t) :
    ∫ x, (x + t)⁻¹ ∂(eigMeasure A) = RCLike.re (trace (negResolvent A t)) := by
  rw [integral_eigMeasure, re_trace_negResolvent_of_posSemidef hA ht]

/-- Transform form of `integral_eigMeasure_resolvent`: `S_{eigMeasure A}(−t) = re tr R_A(−t)`. -/
theorem negStieltjes_eigMeasure {A : Matrix n n 𝕜} (hA : A.PosSemidef) {t : ℝ} (ht : 0 < t) :
    negStieltjes (eigMeasure A) t = RCLike.re (trace (negResolvent A t)) :=
  integral_eigMeasure_resolvent hA ht

/-- First moment: `∫ x d(eigMeasure A) = re tr A`, for every square matrix.
Proof route: `integral_eigMeasure` with `f = id` and `sum_sortedEig`. -/
theorem integral_id_eigMeasure (A : Matrix n n 𝕜) :
    ∫ x, x ∂(eigMeasure A) = RCLike.re (trace A) := by
  rw [integral_eigMeasure, sum_sortedEig]

/-- Support in `[0, ∞)` for PSD `A`.
Proof route: `eigMeasure_apply`; each indicator vanishes by `sortedEig_nonneg`. -/
theorem eigMeasure_Iio_zero {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    eigMeasure A (Iio 0) = 0 := by
  rw [eigMeasure_apply]
  apply Finset.sum_eq_zero
  intro k _
  simp [not_lt.mpr (sortedEig_nonneg hA k)]

/-- Giry measurability of `A ↦ eigMeasure A`.
Proof route: `Finset.measurable_sum` for measure-valued maps (or `Measure.measurable_of_measurable_coe`
with `eigMeasure_apply`), each summand `measurable_dirac.comp (measurable_sortedEig k)`. -/
theorem measurable_eigMeasure : Measurable (eigMeasure : Matrix n n 𝕜 → Measure ℝ) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  rw [show (fun A : Matrix n n 𝕜 => eigMeasure A s) =
      fun A => ∑ k, s.indicator 1 (sortedEig A k) by funext A; exact eigMeasure_apply A s]
  exact Finset.measurable_sum _ fun k _ =>
    (measurable_const.indicator hs).comp (measurable_sortedEig k)

/-- Random-matrix corollary. -/
theorem _root_.AEMeasurable.eigMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A : Ω → Matrix n n 𝕜} (hA : AEMeasurable A P) :
    AEMeasurable (fun ω => eigMeasure (A ω)) P :=
  measurable_eigMeasure.comp_aemeasurable hA

/-! ### The normalized ESD -/

/-- `esd A` is a probability measure for `n` nonempty.
Proof route: `Measure.smul_apply`, `eigMeasure_univ`, `ENNReal.inv_mul_cancel` (`card n ≠ 0`). -/
theorem isProbabilityMeasure_esd [Nonempty n] (A : Matrix n n 𝕜) : IsProbabilityMeasure (esd A) := by
  refine ⟨?_⟩
  rw [esd, Measure.smul_apply, eigMeasure_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simp) (ENNReal.natCast_ne_top _)

/-- `∫ f d(esd A) = (card n)⁻¹ ∑ₖ f(λₖ)` (both sides `0` for `n` empty).
Proof route: `integral_smul_measure`, `ENNReal.toReal_inv`, `ENNReal.toReal_natCast`,
`integral_eigMeasure`. -/
theorem integral_esd (A : Matrix n n 𝕜) (f : ℝ → ℝ) :
    ∫ x, f x ∂(esd A) = (Fintype.card n : ℝ)⁻¹ * ∑ k, f (sortedEig A k) := by
  rw [esd, integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    integral_eigMeasure, smul_eq_mul]

/-- `∫ f d(esd A) = (card n)⁻¹ re tr f(A)` for Hermitian `A`.
Proof route: `integral_smul_measure` and `integral_eigMeasure_eq_re_trace_cfc`. -/
theorem integral_esd_eq_re_trace_cfc {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    ∫ x, f x ∂(esd A) = (Fintype.card n : ℝ)⁻¹ * RCLike.re (trace (cfc f A)) := by
  rw [esd, integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    integral_eigMeasure_eq_re_trace_cfc hA, smul_eq_mul]

/-- `∫ (x + t)⁻¹ d(esd A) = (card n)⁻¹ re tr R_A(−t)` for PSD `A`, `t > 0`.
Proof route: `integral_smul_measure` and `integral_eigMeasure_resolvent`. -/
theorem integral_esd_resolvent {A : Matrix n n 𝕜} (hA : A.PosSemidef) {t : ℝ} (ht : 0 < t) :
    ∫ x, (x + t)⁻¹ ∂(esd A) = (Fintype.card n : ℝ)⁻¹ * RCLike.re (trace (negResolvent A t)) := by
  rw [esd, integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    integral_eigMeasure_resolvent hA ht, smul_eq_mul]

/-- `∫ x d(esd A) = (card n)⁻¹ re tr A`.
Proof route: `integral_smul_measure` and `integral_id_eigMeasure`. -/
theorem integral_id_esd (A : Matrix n n 𝕜) :
    ∫ x, x ∂(esd A) = (Fintype.card n : ℝ)⁻¹ * RCLike.re (trace A) := by
  rw [esd, integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    integral_id_eigMeasure, smul_eq_mul]

/-- Support of the ESD in `[0, ∞)` for PSD `A`.
Proof route: `Measure.smul_apply`, `eigMeasure_Iio_zero`, `mul_zero`. -/
theorem esd_Iio_zero {A : Matrix n n 𝕜} (hA : A.PosSemidef) : esd A (Iio 0) = 0 := by
  rw [esd, Measure.smul_apply, eigMeasure_Iio_zero hA, smul_zero]

/-- Giry measurability of `A ↦ esd A`.
Proof route: `measurable_eigMeasure.const_smul` (`Measure.measurable_smul`-type lemma). -/
theorem measurable_esd : Measurable (esd : Matrix n n 𝕜 → Measure ℝ) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [esd, Measure.smul_apply, smul_eq_mul]
  exact ((Measure.measurable_coe hs).comp measurable_eigMeasure).const_mul _

/-! ## Expected spectral measures -/

section Expected

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The expected eigenvalue counting measure `E[∑ₖ δ_{λₖ(A ω)}]` (Giry bind). -/
def expectedEigMeasure (P : Measure Ω) (A : Ω → Matrix n n 𝕜) : Measure ℝ :=
  P.bind (fun ω => eigMeasure (A ω))

/-- The expected ESD `E[esd (A ω)]` (Giry bind). -/
def expectedEsd (P : Measure Ω) (A : Ω → Matrix n n 𝕜) : Measure ℝ :=
  P.bind (fun ω => esd (A ω))

variable {P : Measure Ω} {A : Ω → Matrix n n 𝕜}

/-- Structural form: `expectedEigMeasure P A = ∑ₖ P.map (ω ↦ λₖ(A ω))`.
Proof route: `Measure.ext`; for measurable `s`, `Measure.bind_apply` (kernel measurability from
`AEMeasurable.eigMeasure`), `eigMeasure_apply`, `lintegral_finset_sum'` and
`Measure.map_apply_of_aemeasurable` with `AEMeasurable.sortedEig`. -/
theorem expectedEigMeasure_eq_sum_map (hA : AEMeasurable A P) :
    expectedEigMeasure P A = ∑ k, P.map (fun ω => sortedEig (A ω) k) := by
  ext s hs
  rw [expectedEigMeasure, Measure.bind_apply hs hA.eigMeasure]
  simp_rw [eigMeasure_apply]
  rw [lintegral_finsetSum' Finset.univ]
  · simp only [Measure.coe_finsetSum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [Measure.map_apply_of_aemeasurable (hA.sortedEig k) hs]
    calc
      ∫⁻ ω, s.indicator 1 (sortedEig (A ω) k) ∂P =
          ∫⁻ ω, ((fun ω => sortedEig (A ω) k) ⁻¹' s).indicator 1 ω ∂P := by
            congr 1
      _ = P ((fun ω => sortedEig (A ω) k) ⁻¹' s) :=
        lintegral_indicator_one₀ ((hA.sortedEig k).nullMeasurableSet_preimage hs)
  · intro k _
    exact (measurable_const.indicator hs).comp_aemeasurable (hA.sortedEig k)

/-- Evaluation on a measurable set.
Proof route: `Measure.bind_apply hs (AEMeasurable.eigMeasure hA)`. -/
theorem expectedEigMeasure_apply (hA : AEMeasurable A P) {s : Set ℝ} (hs : MeasurableSet s) :
    expectedEigMeasure P A s = ∫⁻ ω, eigMeasure (A ω) s ∂P := by
  exact Measure.bind_apply hs hA.eigMeasure

/-- Mass: `card n · P(Ω)`.
Proof route: `expectedEigMeasure_apply` with `s = univ`, `eigMeasure_univ`, `lintegral_const`. -/
theorem expectedEigMeasure_univ (hA : AEMeasurable A P) :
    expectedEigMeasure P A univ = Fintype.card n * P univ := by
  rw [expectedEigMeasure_apply hA MeasurableSet.univ]
  simp only [eigMeasure_univ, lintegral_const]

/-- Finite for finite `P`.
Proof route: `expectedEigMeasure_univ`, `ENNReal.mul_lt_top`. -/
theorem isFiniteMeasure_expectedEigMeasure [IsFiniteMeasure P] (hA : AEMeasurable A P) :
    IsFiniteMeasure (expectedEigMeasure P A) := by
  refine ⟨?_⟩
  rw [expectedEigMeasure_univ hA]
  exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (measure_lt_top P univ)

/-- Real mass for a probability measure `P`: `card n`.
Proof route: `measureReal_def`, `expectedEigMeasure_univ`, `measure_univ`. -/
theorem measureReal_expectedEigMeasure_univ [IsProbabilityMeasure P] (hA : AEMeasurable A P) :
    (expectedEigMeasure P A).real univ = Fintype.card n := by
  rw [measureReal_def, expectedEigMeasure_univ hA, measure_univ, mul_one,
    ENNReal.toReal_natCast]

/-- Support in `[0, ∞)` when `A` is a.e. PSD.
Proof route: `expectedEigMeasure_apply measurableSet_Iio`, `lintegral_eq_zero_iff'`-type argument
with `eigMeasure_Iio_zero` a.e. (`lintegral_congr_ae`, `lintegral_zero`). -/
theorem expectedEigMeasure_Iio_zero (hA : AEMeasurable A P)
    (hpsd : ∀ᵐ ω ∂P, (A ω).PosSemidef) : expectedEigMeasure P A (Iio 0) = 0 := by
  rw [expectedEigMeasure_apply hA measurableSet_Iio]
  calc
    ∫⁻ ω, eigMeasure (A ω) (Iio 0) ∂P = ∫⁻ _ : Ω, 0 ∂P :=
      lintegral_congr_ae (hpsd.mono fun ω hω => eigMeasure_Iio_zero hω)
    _ = 0 := lintegral_zero

/-- Integrability through the expectation: a measurable `f` is integrable against
`expectedEigMeasure P A` if each `ω ↦ f (λₖ(A ω))` is `P`-integrable.
Proof route: `expectedEigMeasure_eq_sum_map`, `integrable_finset_sum_measure`, and
`integrable_map_measure` (`hf.aestronglyMeasurable`, `AEMeasurable.sortedEig`). -/
theorem integrable_expectedEigMeasure (hA : AEMeasurable A P) {f : ℝ → ℝ} (hf : Measurable f)
    (hint : ∀ k, Integrable (fun ω => f (sortedEig (A ω) k)) P) :
    Integrable f (expectedEigMeasure P A) := by
  rw [expectedEigMeasure_eq_sum_map hA, integrable_finsetSum_measure]
  intro k _
  rw [integrable_map_measure hf.aestronglyMeasurable (hA.sortedEig k)]
  exact hint k

/-- Integral through the expectation: `∫ f d(E eigMeasure) = E ∑ₖ f(λₖ)`.
Proof route: `expectedEigMeasure_eq_sum_map`, `integral_finset_sum_measure`, `integral_map`,
then `integral_finset_sum` back inside the `P`-integral. -/
theorem integral_expectedEigMeasure (hA : AEMeasurable A P) {f : ℝ → ℝ} (hf : Measurable f)
    (hint : ∀ k, Integrable (fun ω => f (sortedEig (A ω) k)) P) :
    ∫ x, f x ∂(expectedEigMeasure P A) = ∫ ω, ∑ k, f (sortedEig (A ω) k) ∂P := by
  rw [expectedEigMeasure_eq_sum_map hA]
  calc
    ∫ x, f x ∂∑ k, P.map (fun ω => sortedEig (A ω) k) =
        ∑ k, ∫ x, f x ∂P.map (fun ω => sortedEig (A ω) k) := by
      apply integral_finsetSum_measure
      intro k _
      rw [integrable_map_measure hf.aestronglyMeasurable (hA.sortedEig k)]
      exact hint k
    _ = ∑ k, ∫ ω, f (sortedEig (A ω) k) ∂P := by
      apply Finset.sum_congr rfl
      intro k _
      exact integral_map (hA.sortedEig k) hf.aestronglyMeasurable
    _ = ∫ ω, ∑ k, f (sortedEig (A ω) k) ∂P := by
      symm
      exact integral_finsetSum Finset.univ fun k _ => hint k

/-- Integral through the expectation, kernel form: `∫ f d(E eigMeasure) = E ∫ f d(eigMeasure (A ω))`.
Proof route: `integral_expectedEigMeasure` and `integral_eigMeasure` under the integral. -/
theorem integral_expectedEigMeasure' (hA : AEMeasurable A P) {f : ℝ → ℝ} (hf : Measurable f)
    (hint : ∀ k, Integrable (fun ω => f (sortedEig (A ω) k)) P) :
    ∫ x, f x ∂(expectedEigMeasure P A) = ∫ ω, ∫ x, f x ∂(eigMeasure (A ω)) ∂P := by
  rw [integral_expectedEigMeasure hA hf hint]
  simp_rw [integral_eigMeasure]

/-- Functional-calculus form through the expectation (a.e. Hermitian `A`).
Proof route: `integral_expectedEigMeasure'`, then `integral_congr_ae` with
`integral_eigMeasure_eq_re_trace_cfc` on the a.e. set. -/
theorem integral_expectedEigMeasure_eq_re_trace_cfc (hA : AEMeasurable A P) {f : ℝ → ℝ}
    (hf : Measurable f) (hint : ∀ k, Integrable (fun ω => f (sortedEig (A ω) k)) P)
    (hherm : ∀ᵐ ω ∂P, (A ω).IsHermitian) :
    ∫ x, f x ∂(expectedEigMeasure P A) = ∫ ω, RCLike.re (trace (cfc f (A ω))) ∂P := by
  rw [integral_expectedEigMeasure' hA hf hint]
  apply integral_congr_ae
  filter_upwards [hherm] with ω hω
  exact integral_eigMeasure_eq_re_trace_cfc hω f

/-- **Expected resolvent identity**: for finite `P`, a.e. PSD `A` and `t > 0`, the resolvent is
integrable against the expected measure and
`∫ (x + t)⁻¹ d(E eigMeasure) = E re tr R_{A ω}(−t)`.
Proof route: the integrands `ω ↦ (λₖ(A ω) + t)⁻¹` are a.e. in `[0, 1/t]` (`sortedEig_nonneg`),
`AEStronglyMeasurable` by `AEMeasurable.sortedEig`, hence integrable for finite `P`
(`Integrable.of_bound`-type lemma); then `integral_expectedEigMeasure'` and
`integral_eigMeasure_resolvent` a.e. -/
theorem integral_expectedEigMeasure_resolvent [IsFiniteMeasure P] (hA : AEMeasurable A P)
    (hpsd : ∀ᵐ ω ∂P, (A ω).PosSemidef) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => (x + t)⁻¹) (expectedEigMeasure P A) ∧
      ∫ x, (x + t)⁻¹ ∂(expectedEigMeasure P A) =
        ∫ ω, RCLike.re (trace (negResolvent (A ω) t)) ∂P := by
  have hf : Measurable (fun x : ℝ => (x + t)⁻¹) := by fun_prop
  have hint : ∀ k, Integrable (fun ω => (sortedEig (A ω) k + t)⁻¹) P := by
    intro k
    apply Integrable.of_bound
      ((hf.comp_aemeasurable (hA.sortedEig k)).aestronglyMeasurable) t⁻¹
    filter_upwards [hpsd] with ω hω
    have hnonneg := sortedEig_nonneg hω k
    have hpos : 0 < sortedEig (A ω) k + t := by linarith
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
    exact (inv_le_inv₀ hpos ht).2 (by linarith)
  refine ⟨integrable_expectedEigMeasure hA hf hint, ?_⟩
  rw [integral_expectedEigMeasure' hA hf hint]
  apply integral_congr_ae
  filter_upwards [hpsd] with ω hω
  exact integral_eigMeasure_resolvent hω ht

/-- Transform form of `integral_expectedEigMeasure_resolvent`:
`S_{E eigMeasure}(−t) = E re tr R_{A ω}(−t)`. -/
theorem negStieltjes_expectedEigMeasure [IsFiniteMeasure P] (hA : AEMeasurable A P)
    (hpsd : ∀ᵐ ω ∂P, (A ω).PosSemidef) {t : ℝ} (ht : 0 < t) :
    negStieltjes (expectedEigMeasure P A) t = ∫ ω, RCLike.re (trace (negResolvent (A ω) t)) ∂P :=
  (integral_expectedEigMeasure_resolvent hA hpsd ht).2

/-- **Expected first moment**: for a.e. PSD `A` with `P`-integrable trace, `x` is integrable
against the expected measure and `∫ x d(E eigMeasure) = E re tr A`.
Proof route: a.e. `0 ≤ λₖ(A ω) ≤ re tr A ω` (`sortedEig_nonneg`, `sortedEig_le_re_trace`) gives
integrability of each `ω ↦ λₖ(A ω)` (`Integrable.mono'`); then `integral_expectedEigMeasure'`
with `f = id` and `integral_id_eigMeasure`. -/
theorem integral_id_expectedEigMeasure (hA : AEMeasurable A P)
    (hpsd : ∀ᵐ ω ∂P, (A ω).PosSemidef)
    (htr : Integrable (fun ω => RCLike.re (trace (A ω))) P) :
    Integrable (fun x : ℝ => x) (expectedEigMeasure P A) ∧
      ∫ x, x ∂(expectedEigMeasure P A) = ∫ ω, RCLike.re (trace (A ω)) ∂P := by
  have hint : ∀ k, Integrable (fun ω => sortedEig (A ω) k) P := by
    intro k
    apply htr.mono' (hA.sortedEig k).aestronglyMeasurable
    filter_upwards [hpsd] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sortedEig_nonneg hω k)]
    exact sortedEig_le_re_trace hω k
  refine ⟨integrable_expectedEigMeasure hA measurable_id hint, ?_⟩
  rw [integral_expectedEigMeasure' hA (f := fun x : ℝ => x) measurable_id hint]
  apply integral_congr_ae
  filter_upwards with ω
  exact integral_id_eigMeasure (A ω)

/-! ### Scaled expected measures (glue form)

The Muon existence glue uses `ζ = ENNReal.ofReal c • expectedEigMeasure P A` with `c = B⁻¹`.
These lemmas give the finite-measure instance, real mass, support, transform and first moment of
`ζ` in the hypothesis shapes of `exists_tendsto_of_tendsto_negStieltjes`. -/

/-- A real-scaled expected measure of a finite `P` is finite (`ENNReal.ofReal c ≠ ∞`).
Proof route: `isFiniteMeasure_expectedEigMeasure hA`, then `Measure.smul_finite _
ENNReal.ofReal_ne_top`. -/
theorem isFiniteMeasure_ofReal_smul_expectedEigMeasure [IsFiniteMeasure P]
    (hA : AEMeasurable A P) (c : ℝ) :
    IsFiniteMeasure (ENNReal.ofReal c • expectedEigMeasure P A) :=
  haveI := isFiniteMeasure_expectedEigMeasure hA
  Measure.smul_finite _ ENNReal.ofReal_ne_top

/-- Real mass of the scaled expected measure for a probability measure `P`: `c · card n`.
Proof route: `measureReal_def`, `Measure.smul_apply`, `smul_eq_mul`, `ENNReal.toReal_mul`,
`ENNReal.toReal_ofReal hc`, and `measureReal_expectedEigMeasure_univ hA` (in `toReal` form). -/
theorem measureReal_ofReal_smul_expectedEigMeasure_univ [IsProbabilityMeasure P]
    (hA : AEMeasurable A P) {c : ℝ} (hc : 0 ≤ c) :
    (ENNReal.ofReal c • expectedEigMeasure P A).real univ = c * Fintype.card n := by
  rw [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hc, ← measureReal_def, measureReal_expectedEigMeasure_univ hA]

/-- Support of the scaled expected measure in `[0, ∞)` for a.e. PSD `A`.
Proof route: `Measure.smul_apply`, `expectedEigMeasure_Iio_zero hA hpsd`, `smul_zero`. -/
theorem ofReal_smul_expectedEigMeasure_Iio_zero (hA : AEMeasurable A P)
    (hpsd : ∀ᵐ ω ∂P, (A ω).PosSemidef) (c : ℝ) :
    (ENNReal.ofReal c • expectedEigMeasure P A) (Iio 0) = 0 := by
  rw [Measure.smul_apply, expectedEigMeasure_Iio_zero hA hpsd, smul_zero]

/-- Transform of the scaled expected measure: `S_ζ(−t) = c · E re tr R_{A ω}(−t)`.
Proof route: `negStieltjes_smul`, `ENNReal.toReal_ofReal hc`, `negStieltjes_expectedEigMeasure`. -/
theorem negStieltjes_ofReal_smul_expectedEigMeasure [IsFiniteMeasure P] (hA : AEMeasurable A P)
    (hpsd : ∀ᵐ ω ∂P, (A ω).PosSemidef) {c : ℝ} (hc : 0 ≤ c) {t : ℝ} (ht : 0 < t) :
    negStieltjes (ENNReal.ofReal c • expectedEigMeasure P A) t =
      c * ∫ ω, RCLike.re (trace (negResolvent (A ω) t)) ∂P := by
  rw [negStieltjes_smul, ENNReal.toReal_ofReal hc, negStieltjes_expectedEigMeasure hA hpsd ht]

/-- First moment of the scaled expected measure: `x` is integrable and `∫ x dζ = c · E re tr A`.
Proof route: `integral_id_expectedEigMeasure`, `Integrable.smul_measure` (`ENNReal.ofReal_ne_top`),
`integral_smul_measure`, `ENNReal.toReal_ofReal hc`. -/
theorem integral_id_ofReal_smul_expectedEigMeasure (hA : AEMeasurable A P)
    (hpsd : ∀ᵐ ω ∂P, (A ω).PosSemidef)
    (htr : Integrable (fun ω => RCLike.re (trace (A ω))) P) {c : ℝ} (hc : 0 ≤ c) :
    Integrable (fun x : ℝ => x) (ENNReal.ofReal c • expectedEigMeasure P A) ∧
      ∫ x, x ∂(ENNReal.ofReal c • expectedEigMeasure P A) =
        c * ∫ ω, RCLike.re (trace (A ω)) ∂P := by
  obtain ⟨h1, h2⟩ := integral_id_expectedEigMeasure hA hpsd htr
  refine ⟨h1.smul_measure ENNReal.ofReal_ne_top, ?_⟩
  rw [integral_smul_measure, ENNReal.toReal_ofReal hc, h2, smul_eq_mul]

/-- Measurability of the output Gram map `ω ↦ M ω (M ω)ᵀ` for a random real rectangular matrix.
Proof route: `(continuous_id.matrix_mul continuous_id.matrix_transpose).measurable` (Borel
`Matrix` spaces, `Mathlib.Analysis.Matrix.MeasurableSpace`), then `comp_aemeasurable hM`. -/
theorem _root_.AEMeasurable.mul_transpose_self {m p : Type*} [Fintype m] [Fintype p]
    {M : Ω → Matrix m p ℝ} (hM : AEMeasurable M P) :
    AEMeasurable (fun ω => M ω * (M ω)ᵀ) P :=
  ((continuous_id.matrix_mul continuous_id.matrix_transpose).measurable).comp_aemeasurable hM

/-- Measurability of the input Gram map `ω ↦ (M ω)ᵀ M ω`. Proof route: as for
`AEMeasurable.mul_transpose_self`. -/
theorem _root_.AEMeasurable.transpose_mul_self {m p : Type*} [Fintype m] [Fintype p]
    {M : Ω → Matrix m p ℝ} (hM : AEMeasurable M P) :
    AEMeasurable (fun ω => (M ω)ᵀ * M ω) P :=
  ((continuous_id.matrix_transpose.matrix_mul continuous_id).measurable).comp_aemeasurable hM

/-! ### The expected normalized ESD -/

/-- `expectedEsd = (card n)⁻¹ • expectedEigMeasure`.
Proof route: `Measure.ext`; `Measure.bind_apply` on both sides, `Measure.smul_apply`, and
`lintegral_const_mul''` (a.e.-measurable integrand from `Measure.measurable_coe`); the factor
`(card n)⁻¹ = ∞` only occurs for `n` empty, where `eigMeasure = 0`. -/
theorem expectedEsd_eq_smul (hA : AEMeasurable A P) :
    expectedEsd P A = ((Fintype.card n : ℝ≥0∞)⁻¹) • expectedEigMeasure P A := by
  ext s hs
  rw [expectedEsd]
  have hE : AEMeasurable (fun ω => esd (A ω)) P :=
    measurable_esd.comp_aemeasurable hA
  rw [Measure.bind_apply hs hE, Measure.smul_apply, expectedEigMeasure_apply hA hs]
  simp only [esd, Measure.smul_apply, smul_eq_mul]
  rw [lintegral_const_mul'']
  exact ((Measure.measurable_coe hs).comp_aemeasurable hA.eigMeasure)

/-- The expected ESD of a probability measure is a probability measure (for `n` nonempty).
Proof route: `expectedEsd_eq_smul`, `expectedEigMeasure_univ`, `measure_univ`,
`ENNReal.inv_mul_cancel`. -/
theorem isProbabilityMeasure_expectedEsd [Nonempty n] [IsProbabilityMeasure P]
    (hA : AEMeasurable A P) : IsProbabilityMeasure (expectedEsd P A) := by
  refine ⟨?_⟩
  rw [expectedEsd_eq_smul hA, Measure.smul_apply, expectedEigMeasure_univ hA,
    measure_univ, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simp) (ENNReal.natCast_ne_top _)

/-- Support of the expected ESD in `[0, ∞)` for a.e. PSD `A`.
Proof route: `expectedEsd_eq_smul`, `Measure.smul_apply`, `expectedEigMeasure_Iio_zero`. -/
theorem expectedEsd_Iio_zero (hA : AEMeasurable A P) (hpsd : ∀ᵐ ω ∂P, (A ω).PosSemidef) :
    expectedEsd P A (Iio 0) = 0 := by
  rw [expectedEsd_eq_smul hA, Measure.smul_apply,
    expectedEigMeasure_Iio_zero hA hpsd, smul_zero]

/-- Integral against the expected ESD.
Proof route: `expectedEsd_eq_smul`, `integral_smul_measure`, `integral_expectedEigMeasure`,
`integral_const_mul`. -/
theorem integral_expectedEsd (hA : AEMeasurable A P) {f : ℝ → ℝ} (hf : Measurable f)
    (hint : ∀ k, Integrable (fun ω => f (sortedEig (A ω) k)) P) :
    ∫ x, f x ∂(expectedEsd P A) =
      (Fintype.card n : ℝ)⁻¹ * ∫ ω, ∑ k, f (sortedEig (A ω) k) ∂P := by
  rw [expectedEsd_eq_smul hA, integral_smul_measure,
    integral_expectedEigMeasure hA hf hint, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul]

/-- Expected-ESD resolvent identity.
Proof route: `expectedEsd_eq_smul`, `Integrable.smul_measure`, `integral_smul_measure`,
`integral_expectedEigMeasure_resolvent`. -/
theorem integral_expectedEsd_resolvent [IsFiniteMeasure P] (hA : AEMeasurable A P)
    (hpsd : ∀ᵐ ω ∂P, (A ω).PosSemidef) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => (x + t)⁻¹) (expectedEsd P A) ∧
      ∫ x, (x + t)⁻¹ ∂(expectedEsd P A) =
        (Fintype.card n : ℝ)⁻¹ * ∫ ω, RCLike.re (trace (negResolvent (A ω) t)) ∂P := by
  cases isEmpty_or_nonempty n with
  | inl h =>
      let _ := h
      simp [expectedEsd_eq_smul hA, expectedEigMeasure_eq_sum_map hA]
  | inr h =>
      let _ := h
      obtain ⟨hint, hid⟩ := integral_expectedEigMeasure_resolvent hA hpsd ht
      rw [expectedEsd_eq_smul hA]
      refine ⟨hint.smul_measure (by simp), ?_⟩
      rw [integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_natCast,
        hid, smul_eq_mul]

/-- Expected-ESD first moment.
Proof route: `expectedEsd_eq_smul`, `integral_smul_measure`, `integral_id_expectedEigMeasure`
(integrability against a smul measure with finite factor; for `n` empty the measure is `0`). -/
theorem integral_id_expectedEsd (hA : AEMeasurable A P) (hpsd : ∀ᵐ ω ∂P, (A ω).PosSemidef)
    (htr : Integrable (fun ω => RCLike.re (trace (A ω))) P) :
    Integrable (fun x : ℝ => x) (expectedEsd P A) ∧
      ∫ x, x ∂(expectedEsd P A) = (Fintype.card n : ℝ)⁻¹ * ∫ ω, RCLike.re (trace (A ω)) ∂P := by
  cases isEmpty_or_nonempty n with
  | inl h =>
      let _ := h
      simp [expectedEsd_eq_smul hA, expectedEigMeasure_eq_sum_map hA]
  | inr h =>
      let _ := h
      obtain ⟨hint, hid⟩ := integral_id_expectedEigMeasure hA hpsd htr
      rw [expectedEsd_eq_smul hA]
      refine ⟨hint.smul_measure (by simp), ?_⟩
      rw [integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_natCast,
        hid, smul_eq_mul]

end Expected


/-! ## Appended: Stieltjes transform of the ESD = normalised trace of the resolvent -/

section StieltjesESD

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- Spectral formula for the trace of the resolvent (convention `(A − z)⁻¹`): for Hermitian `A`
and `z` away from the spectrum, `tr (A − z)⁻¹ = ∑ₖ (λₖ − z)⁻¹`. -/
theorem trace_matResolvent_eq_sum {A : Matrix n n 𝕜} (hA : A.IsHermitian) {z : 𝕜}
    (hz : ∀ k, ((sortedEig A k : ℝ) : 𝕜) - z ≠ 0) :
    trace (matResolvent A z) = ∑ k, (((sortedEig A k : ℝ) : 𝕜) - z)⁻¹ := by
  have hz' : ∀ i, ((hA.eigenvalues i : ℝ) : 𝕜) - z ≠ 0 := by
    intro i
    have := hz ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)
    rwa [sortedEig_eq hA] at this
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hUdef
  have hU1 : star U * U = 1 := Unitary.coe_star_mul_self _
  have hU2 : U * star U = 1 := Unitary.coe_mul_star_self _
  have hAeq : A = U * Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : 𝕜)) * star U := by
    have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have h1 : A - z • (1 : Matrix n n 𝕜) =
      U * Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : 𝕜) - z) * star U := by
    have e1 : z • (1 : Matrix n n 𝕜) = U * (z • (1 : Matrix n n 𝕜)) * star U := by
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU2]
    have e2 : Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : 𝕜) - z) =
        Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : 𝕜)) - z • (1 : Matrix n n 𝕜) := by
      ext i j
      by_cases h : i = j
      · subst h; simp
      · simp [h]
    rw [e2, Matrix.mul_sub, Matrix.sub_mul, ← e1, ← hAeq]
  have h2 : matResolvent A z =
      U * Matrix.diagonal (fun i => (((hA.eigenvalues i : ℝ) : 𝕜) - z)⁻¹) * star U := by
    unfold matResolvent
    rw [h1]
    refine Matrix.inv_eq_right_inv ?_
    calc U * Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : 𝕜) - z) * star U *
          (U * Matrix.diagonal (fun i => (((hA.eigenvalues i : ℝ) : 𝕜) - z)⁻¹) * star U)
        = U * (Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : 𝕜) - z) *
            (star U * U) * Matrix.diagonal (fun i => (((hA.eigenvalues i : ℝ) : 𝕜) - z)⁻¹)) *
            star U := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hU1, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
        have : (fun i => (((hA.eigenvalues i : ℝ) : 𝕜) - z) * (((hA.eigenvalues i : ℝ) : 𝕜) - z)⁻¹)
            = fun _ => (1 : 𝕜) := funext fun i => mul_inv_cancel₀ (hz' i)
        rw [this, Matrix.diagonal_one, Matrix.mul_one, hU2]
  rw [h2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU1, Matrix.one_mul, Matrix.trace_diagonal,
    sortedEig_eq hA]
  exact Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun k => (((hA.eigenvalues₀ k : ℝ) : 𝕜) - z)⁻¹)

end StieltjesESD

/-- **Stieltjes transform of the eigenvalue counting measure** (unnormalised):
`stieltjes (eigMeasure A) z = tr (A − z)⁻¹` for Hermitian complex `A` and `z` off the spectrum. -/
theorem stieltjes_eigMeasure {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : ∀ k, ((sortedEig A k : ℝ) : ℂ) ≠ z) :
    stieltjes (eigMeasure A) z = trace (matResolvent A z) := by
  rw [trace_matResolvent_eq_sum hA (fun k => sub_ne_zero.mpr (hz k))]
  unfold stieltjes eigMeasure
  rw [integral_finsetSum_measure]
  · simp only [integral_dirac]
    rfl
  · intro k _
    exact integrable_dirac (by simp)

/-- **`stieltjes_esd`**: `S_{esd A}(z) = (card n)⁻¹ · tr (A − z)⁻¹` for Hermitian complex `A` and
`z` off the spectrum. (If `n` is empty both sides are `0`.) -/
theorem stieltjes_esd {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : ∀ k, ((sortedEig A k : ℝ) : ℂ) ≠ z) :
    stieltjes (esd A) z = ((Fintype.card n : ℂ))⁻¹ * trace (matResolvent A z) := by
  rw [← stieltjes_eigMeasure hA hz]
  unfold stieltjes esd
  rw [integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_natCast, Complex.real_smul]
  push_cast
  rfl

/-- `stieltjes_esd` off the real axis: no spectral hypothesis needed when `Im z ≠ 0`. -/
theorem stieltjes_esd_of_im_ne_zero {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) :
    stieltjes (esd A) z = ((Fintype.card n : ℂ))⁻¹ * trace (matResolvent A z) :=
  stieltjes_esd hA fun k h => hz (by rw [← h]; simp)

/-- `stieltjes_eigMeasure` off the real axis. -/
theorem stieltjes_eigMeasure_of_im_ne_zero {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) :
    stieltjes (eigMeasure A) z = trace (matResolvent A z) :=
  stieltjes_eigMeasure hA fun k h => hz (by rw [← h]; simp)

end SpectralFoundations
