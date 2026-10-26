import Mathlib
import GaussianFoundations.IBP

/-!
# Foundations: standard Gaussian facts (task L-0.5a)

Uncited standard facts about the standard Gaussian law `gaussianReal 0 1` on `ℝ` and about the
standard Gaussian vector `stdGaussianPi n` on `Fin n → ℝ`, used by the appendix sections
(B `eqn:app-de-erfc`, G `L-G.1`, H `L-H.0`, I `L-I.0a`). Source of record: snapshot `cr-2026-10-22`.

Stein's lemma (`GaussianIBP`) is proved here, not certified (`EXTERNAL-RESULTS.md`).

Every theorem below is a statement only (`sorry`); proof routes are in the interface JSON.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace GaussianFoundations

/-- Standard Gaussian vector in `ℝⁿ`: coordinates i.i.d. `N(0,1)`. -/
noncomputable def stdGaussianPi (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => gaussianReal 0 1

instance (n : ℕ) : IsProbabilityMeasure (stdGaussianPi n) := by
  unfold stdGaussianPi
  infer_instance

/-- Complementary error function, as used in Appendix B:
`erfc x = (2/√π) ∫_x^∞ exp(-t²) dt`. Mathlib has no `erfc`. -/
noncomputable def erfc (x : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) * ∫ t in Set.Ioi x, Real.exp (-t ^ 2)

/-! ## Scalar moments of `gaussianReal 0 1` -/

/-- Auxiliary: every monomial is integrable against `gaussianReal 0 1`. -/
private lemma gaussian_pow_integrable_aux (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 1) := by
  have h := (memLp_id_gaussianReal' (μ := 0) (v := 1) (n : ℝ≥0∞)
    (ENNReal.natCast_ne_top n)).integrable_norm_pow'
  refine h.mono' (measurable_id.pow_const n).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  simp [norm_pow]

/-- Auxiliary half-line Gamma integral: `∫_{(0,∞)} y^{2k} e^{-y²/2} dy = 2^{k-1/2} Γ(k+1/2)`. -/
private lemma gaussian_half_line_aux (k : ℕ) :
    ∫ y in Set.Ioi (0 : ℝ), y ^ (2 * k) * Real.exp (-((1 / 2 : ℝ) * y ^ 2))
      = (1 / 2 : ℝ) * ((1 / (1 / 2 : ℝ)) ^ ((k : ℝ) + 1 / 2) * Real.Gamma ((k : ℝ) + 1 / 2)) := by
  have hsub := integral_comp_rpow_Ioi_of_pos
    (g := fun s : ℝ => (1 / 2 : ℝ) * s ^ ((k : ℝ) + 1 / 2 - 1) * Real.exp (-((1 / 2 : ℝ) * s)))
    (p := 2) (by norm_num)
  beta_reduce at hsub
  have hL : ∫ y in Set.Ioi (0 : ℝ), y ^ (2 * k) * Real.exp (-((1 / 2 : ℝ) * y ^ 2))
      = ∫ x in Set.Ioi (0 : ℝ), ((2 : ℝ) * x ^ ((2 : ℝ) - 1)) •
          ((1 / 2 : ℝ) * (x ^ (2 : ℝ)) ^ ((k : ℝ) + 1 / 2 - 1)
            * Real.exp (-((1 / 2 : ℝ) * x ^ (2 : ℝ)))) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx' : (0 : ℝ) < x := hx
    have e1 : (x ^ 2) ^ ((k : ℝ) + 1 / 2 - 1) = x ^ ((k : ℝ) * 2 - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx'.le]; congr 1; push_cast; ring
    have e2 : x ^ ((2 : ℝ) - 1) * x ^ ((k : ℝ) * 2 - 1) = x ^ (2 * k) := by
      rw [← Real.rpow_add hx']
      rw [show ((2 : ℝ) - 1) + ((k : ℝ) * 2 - 1) = ((2 * k : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    rw [smul_eq_mul, Real.rpow_two x, e1]
    linear_combination (-Real.exp (-((1 / 2 : ℝ) * x ^ 2))) * e2
  have hG : ∫ y in Set.Ioi (0 : ℝ), (1 / 2 : ℝ) * y ^ ((k : ℝ) + 1 / 2 - 1)
        * Real.exp (-((1 / 2 : ℝ) * y))
      = (1 / 2 : ℝ) * ∫ y in Set.Ioi (0 : ℝ), y ^ ((k : ℝ) + 1 / 2 - 1)
        * Real.exp (-((1 / 2 : ℝ) * y)) := by
    rw [← integral_const_mul]
    congr 1
    ext y
    ring
  rw [hL, hsub, hG, Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1 / 2) (r := 1 / 2)
    (by positivity) (by norm_num)]

/-- Card P1. Even moments: `E g^{2k} = (2k-1)!!`. -/
theorem gaussian_moment_even (k : ℕ) :
    ∫ x, x ^ (2 * k) ∂(gaussianReal 0 1) = (((2 * k - 1).doubleFactorial : ℕ) : ℝ) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have hpt : (fun x : ℝ => gaussianPDFReal 0 1 x • x ^ (2 * k))
      = fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹
          * (fun y : ℝ => y ^ (2 * k) * Real.exp (-((1 / 2 : ℝ) * y ^ 2))) |x| := by
    funext x
    rw [gaussianPDFReal_def, smul_eq_mul, ← Even.pow_abs (even_two_mul k) x]
    have hexp : -(x - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)) = -((1 / 2 : ℝ) * |x| ^ 2) := by
      rw [sq_abs]; simp; ring
    simp only [hexp]
    simp only [NNReal.coe_one, mul_one]
    ring
  rw [hpt, integral_const_mul, integral_comp_abs
    (f := fun y : ℝ => y ^ (2 * k) * Real.exp (-((1 / 2 : ℝ) * y ^ 2))),
    gaussian_half_line_aux k, Real.Gamma_nat_add_half k]
  have h2 : (1 / (1 / 2 : ℝ)) ^ ((k : ℝ) + 1 / 2) = 2 ^ k * Real.sqrt 2 := by
    rw [show (1 / (1 / 2 : ℝ)) = (2 : ℝ) by norm_num, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_natCast, Real.sqrt_eq_rpow]
  rw [h2, Real.sqrt_mul (by norm_num) Real.pi]
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have h2k : (2 : ℝ) ^ k ≠ 0 := by positivity
  have hs2ne : Real.sqrt 2 ≠ 0 := by positivity
  field_simp

/-- Card P1. Odd moments vanish: `E g^{2k+1} = 0`. -/
theorem gaussian_moment_odd (k : ℕ) :
    ∫ x, x ^ (2 * k + 1) ∂(gaussianReal 0 1) = 0 := by
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg]; simp
  have h1 : ∫ x, (-x) ^ (2 * k + 1) ∂(gaussianReal 0 1)
      = ∫ x, x ^ (2 * k + 1) ∂(gaussianReal 0 1) := by
    conv_rhs => rw [← hmap]
    rw [integral_map (by fun_prop) (by fun_prop)]
  have h2 : ∫ x, (-x) ^ (2 * k + 1) ∂(gaussianReal 0 1)
      = - ∫ x, x ^ (2 * k + 1) ∂(gaussianReal 0 1) := by
    rw [← integral_neg]
    congr 1
    funext x
    rw [Odd.neg_pow ⟨k, rfl⟩]
  linarith

/-- Card P1. Every monomial is integrable against `gaussianReal 0 1`. -/
theorem gaussian_integrable_pow (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 1) :=
  gaussian_pow_integrable_aux n

/-- Card P1. Every monomial lies in `L^p` for every finite `p`. -/
theorem gaussian_memLp_pow (n : ℕ) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun x : ℝ => x ^ n) p (gaussianReal 0 1) := by
  by_cases h0 : p = 0
  · subst h0
    exact memLp_zero_iff_aestronglyMeasurable.2 (measurable_id.pow_const n).aestronglyMeasurable
  · have hf : AEStronglyMeasurable (fun x : ℝ => x ^ n) (gaussianReal 0 1) :=
      (measurable_id.pow_const n).aestronglyMeasurable
    rw [← integrable_norm_rpow_iff hf h0 hp]
    have hint : Integrable (fun x : ℝ => ‖x ^ n‖ ^ ((⌈p.toReal⌉₊ : ℕ) : ℝ)) (gaussianReal 0 1) := by
      refine (gaussian_pow_integrable_aux (n * ⌈p.toReal⌉₊)).norm.congr
        (Filter.Eventually.of_forall fun x => ?_)
      simp only [norm_pow]
      rw [Real.rpow_natCast, pow_mul]
    exact integrable_norm_rpow_of_le (μ := gaussianReal 0 1) hf ENNReal.toReal_nonneg
      (Nat.cast_nonneg _) (Nat.le_ceil _) hint

/-- Card P2. `E g² = 1`. -/
theorem gaussian_moment_two : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := gaussian_moment_even 1
  have e : (2 * 1 - 1).doubleFactorial = 1 := by decide
  rw [e] at h
  norm_num at h
  exact h

/-- Card P2. `E g⁴ = 3`. -/
theorem gaussian_moment_four : ∫ x, x ^ 4 ∂(gaussianReal 0 1) = 3 := by
  have h := gaussian_moment_even 2
  have e : (2 * 2 - 1).doubleFactorial = 3 := by decide
  rw [e] at h
  norm_num at h
  exact h

/-- Card P2. `E g⁶ = 15`. -/
theorem gaussian_moment_six : ∫ x, x ^ 6 ∂(gaussianReal 0 1) = 15 := by
  have h := gaussian_moment_even 3
  have e : (2 * 3 - 1).doubleFactorial = 15 := by decide
  rw [e] at h
  norm_num at h
  exact h

/-- Card P2. `E g⁸ = 105`. -/
theorem gaussian_moment_eight : ∫ x, x ^ 8 ∂(gaussianReal 0 1) = 105 := by
  have h := gaussian_moment_even 4
  have e : (2 * 4 - 1).doubleFactorial = 105 := by decide
  rw [e] at h
  norm_num at h
  exact h

/-- Card P3. `E (g² - 1)² = 2`. -/
theorem gaussian_sq_sub_one_moment_two :
    ∫ x, (x ^ 2 - 1) ^ 2 ∂(gaussianReal 0 1) = 2 := by
  have hi4 : Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 1) := gaussian_integrable_pow 4
  have hi2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) := gaussian_integrable_pow 2
  have h1 : Integrable (fun x : ℝ => 2 * x ^ 2) (gaussianReal 0 1) := hi2.const_mul 2
  have h2 : Integrable (fun x : ℝ => x ^ 4 - 2 * x ^ 2) (gaussianReal 0 1) := hi4.sub h1
  have e : (fun x : ℝ => (x ^ 2 - 1) ^ 2) = fun x : ℝ => ((x ^ 4 - 2 * x ^ 2) + 1) := by
    funext x; ring
  rw [e, integral_add h2 (integrable_const 1), integral_sub hi4 h1, integral_const_mul,
    gaussian_moment_four, gaussian_moment_two, integral_const]
  norm_num

/-- Card P3. `E (g² - 1)⁴ = 60`. -/
theorem gaussian_sq_sub_one_moment_four :
    ∫ x, (x ^ 2 - 1) ^ 4 ∂(gaussianReal 0 1) = 60 := by
  have hi8 : Integrable (fun x : ℝ => x ^ 8) (gaussianReal 0 1) := gaussian_integrable_pow 8
  have hi6 : Integrable (fun x : ℝ => x ^ 6) (gaussianReal 0 1) := gaussian_integrable_pow 6
  have hi4 : Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 1) := gaussian_integrable_pow 4
  have hi2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) := gaussian_integrable_pow 2
  have a1 : Integrable (fun x : ℝ => 4 * x ^ 6) (gaussianReal 0 1) := hi6.const_mul 4
  have a2 : Integrable (fun x : ℝ => x ^ 8 - 4 * x ^ 6) (gaussianReal 0 1) := hi8.sub a1
  have a3 : Integrable (fun x : ℝ => 6 * x ^ 4) (gaussianReal 0 1) := hi4.const_mul 6
  have a4 : Integrable (fun x : ℝ => x ^ 8 - 4 * x ^ 6 + 6 * x ^ 4) (gaussianReal 0 1) :=
    a2.add a3
  have a5 : Integrable (fun x : ℝ => 4 * x ^ 2) (gaussianReal 0 1) := hi2.const_mul 4
  have a6 : Integrable (fun x : ℝ => x ^ 8 - 4 * x ^ 6 + 6 * x ^ 4 - 4 * x ^ 2)
      (gaussianReal 0 1) := a4.sub a5
  have e : (fun x : ℝ => (x ^ 2 - 1) ^ 4)
      = fun x : ℝ => ((((x ^ 8 - 4 * x ^ 6) + 6 * x ^ 4) - 4 * x ^ 2) + 1) := by
    funext x; ring
  rw [e, integral_add a6 (integrable_const 1), integral_sub a4 a5, integral_add a2 a3,
    integral_sub hi8 a1, integral_const_mul, integral_const_mul, integral_const_mul,
    gaussian_moment_eight, gaussian_moment_six, gaussian_moment_four, gaussian_moment_two,
    integral_const]
  norm_num

/-- Auxiliary: `∫_{(0,∞)} y e^{-y²/2} dy = 1`, by the fundamental theorem of calculus. -/
private lemma gaussian_odd_half_line_aux :
    ∫ y in Set.Ioi (0 : ℝ), y * Real.exp (-((1 / 2 : ℝ) * y ^ 2)) = 1 := by
  have hcont : ContinuousWithinAt (fun y : ℝ => -Real.exp (-((1 / 2 : ℝ) * y ^ 2)))
      (Set.Ici 0) 0 :=
    Continuous.continuousWithinAt (by fun_prop)
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun y : ℝ => -Real.exp (-((1 / 2 : ℝ) * y ^ 2)))
      (x * Real.exp (-((1 / 2 : ℝ) * x ^ 2))) x := by
    intro x _
    have h := (((hasDerivAt_pow 2 x).const_mul (1 / 2 : ℝ)).neg.exp).neg
    convert h using 1
    norm_num
    ring
  have hint : IntegrableOn (fun y : ℝ => y * Real.exp (-((1 / 2 : ℝ) * y ^ 2)))
      (Set.Ioi (0 : ℝ)) := by
    simpa [neg_mul] using (integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).integrableOn
  have hlim : Filter.Tendsto (fun y : ℝ => -Real.exp (-((1 / 2 : ℝ) * y ^ 2)))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun y : ℝ => (1 / 2 : ℝ) * y ^ 2) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num) (Filter.tendsto_pow_atTop two_ne_zero)
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).neg
    simpa using h2
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := (0 : ℝ))
    (f := fun y : ℝ => -Real.exp (-((1 / 2 : ℝ) * y ^ 2)))
    (f' := fun y : ℝ => y * Real.exp (-((1 / 2 : ℝ) * y ^ 2))) (m := 0) hcont hderiv hint hlim
  rw [h]
  simp

/-- Card P3. First absolute moment: `E|g| = √(2/π)`. -/
theorem gaussian_abs_moment :
    ∫ x, |x| ∂(gaussianReal 0 1) = Real.sqrt (2 / Real.pi) := by
  have hpt : (fun x : ℝ => gaussianPDFReal 0 1 x • |x|)
      = fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹
          * (fun y : ℝ => y * Real.exp (-((1 / 2 : ℝ) * y ^ 2))) |x| := by
    funext x
    dsimp only
    have hexp : -(x - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)) = -((1 / 2 : ℝ) * |x| ^ 2) := by
      rw [sq_abs]; simp only [NNReal.coe_one, mul_one, sub_zero]; ring
    rw [gaussianPDFReal_def, smul_eq_mul]
    dsimp only
    rw [hexp]
    simp only [NNReal.coe_one, mul_one]
    ring
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero, hpt, integral_const_mul,
    integral_comp_abs (f := fun y : ℝ => y * Real.exp (-((1 / 2 : ℝ) * y ^ 2))),
    gaussian_odd_half_line_aux]
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  linarith [h2]

/-- Auxiliary: the half-line substitution `x ↦ x²` used for the negative-half moment. -/
private lemma p4_neg_half_pt (x : ℝ) (hx : 0 < x) :
    x ^ (-(1 / 2 : ℝ)) * Real.exp (-((1 / 2 : ℝ) * x ^ 2))
      = (2 * x ^ ((2 : ℝ) - 1)) • ((1 / 2 : ℝ) * (x ^ (2 : ℝ)) ^ ((1 / 4 : ℝ) - 1)
          * Real.exp (-((1 / 2 : ℝ) * x ^ (2 : ℝ)))) := by
  have e1 : (x ^ (2 : ℝ)) ^ ((1 / 4 : ℝ) - 1) = x ^ (-(3 / 2) : ℝ) := by
    rw [← Real.rpow_mul hx.le]; norm_num
  have e2 : x ^ ((2 : ℝ) - 1) * x ^ (-(3 / 2) : ℝ) = x ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_add hx]; norm_num
  rw [smul_eq_mul, e1, Real.rpow_two x]
  linear_combination (-Real.exp (-((1 / 2 : ℝ) * x ^ 2))) * e2

/-- Card P4. `E|g|^{-1/2} = 2^{-1/4} Γ(1/4) / √π`, with real power `|x| ^ (-(1/2))`. -/
theorem gaussian_neg_half_abs_moment :
    ∫ x, |x| ^ (-(1 / 2 : ℝ)) ∂(gaussianReal 0 1)
      = (2 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4 : ℝ) / Real.sqrt Real.pi := by
  have hpt : (fun x : ℝ => gaussianPDFReal 0 1 x • |x| ^ (-(1 / 2 : ℝ)))
      = fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹
          * (fun y : ℝ => y ^ (-(1 / 2 : ℝ)) * Real.exp (-((1 / 2 : ℝ) * y ^ 2))) |x| := by
    funext x
    dsimp only
    have hexp : -(x - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)) = -((1 / 2 : ℝ) * |x| ^ 2) := by
      rw [sq_abs]; simp only [NNReal.coe_one, mul_one, sub_zero]; ring
    rw [gaussianPDFReal_def, smul_eq_mul]
    dsimp only
    rw [hexp]
    simp only [NNReal.coe_one, mul_one]
    ring
  have hL : ∫ x in Set.Ioi (0 : ℝ), x ^ (-(1 / 2 : ℝ)) * Real.exp (-((1 / 2 : ℝ) * x ^ 2))
      = ∫ x in Set.Ioi (0 : ℝ), (2 * x ^ ((2 : ℝ) - 1)) • ((1 / 2 : ℝ) * (x ^ (2 : ℝ)) ^ ((1 / 4 : ℝ) - 1)
          * Real.exp (-((1 / 2 : ℝ) * x ^ (2 : ℝ)))) :=
    setIntegral_congr_fun measurableSet_Ioi (fun x hx => p4_neg_half_pt x hx)
  have hsub := integral_comp_rpow_Ioi_of_pos
    (g := fun s : ℝ => (1 / 2 : ℝ) * s ^ ((1 / 4 : ℝ) - 1) * Real.exp (-((1 / 2 : ℝ) * s)))
    (p := 2) (by norm_num)
  beta_reduce at hsub
  have hG : ∫ y in Set.Ioi (0 : ℝ), (1 / 2 : ℝ) * y ^ ((1 / 4 : ℝ) - 1) * Real.exp (-((1 / 2 : ℝ) * y))
      = (1 / 2 : ℝ) * ∫ y in Set.Ioi (0 : ℝ), y ^ ((1 / 4 : ℝ) - 1) * Real.exp (-((1 / 2 : ℝ) * y)) := by
    rw [← integral_const_mul]
    congr 1
    ext y
    ring
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero, hpt, integral_const_mul,
    integral_comp_abs (f := fun y : ℝ => y ^ (-(1 / 2 : ℝ)) * Real.exp (-((1 / 2 : ℝ) * y ^ 2))),
    hL, hsub, hG, Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (1 / 4 : ℝ)) (r := 1 / 2)
      (by norm_num) (by norm_num)]
  have h2 : (2 : ℝ) ^ (1 / 4 : ℝ) / Real.sqrt 2 = (2 : ℝ) ^ (-(1 / 4 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub (by norm_num)]; norm_num
  rw [show (1 / (1 / 2 : ℝ)) = (2 : ℝ) by norm_num, Real.sqrt_mul (by norm_num) Real.pi, ← h2]
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
  have h2p : (2 : ℝ) ^ (1 / 4 : ℝ) ≠ 0 := by positivity
  field_simp

/-- Auxiliary: pointwise identity `φ(x) e^{-b x²} = (2π)^{-1/2} e^{-(1/2+b)x²}`. -/
private lemma p4_gauss_pt (b x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (-b * x ^ 2)
      = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 + b) * x ^ 2) := by
  rw [gaussianPDFReal_def, mul_assoc, ← Real.exp_add]
  congr 1
  · simp
  · congr 1; simp; ring

/-- Auxiliary: `(2π)^{-1/2} √(π/b) = (1+2t)^{-1/2}` for `b = 1/2 + t`. -/
private lemma p4_laplace_alg (t : ℝ) (ht : 0 ≤ t) :
    (Real.sqrt (2 * Real.pi))⁻¹ * √(Real.pi / (1 / 2 + t)) = (1 + 2 * t) ^ (-(1 / 2 : ℝ)) := by
  have hb : (0 : ℝ) < 1 + 2 * t := by positivity
  have e : Real.pi / (1 / 2 + t) = (2 * Real.pi) / (1 + 2 * t) := by
    field_simp
  rw [e, Real.sqrt_div (by positivity), Real.sqrt_eq_rpow (1 + 2 * t),
    Real.rpow_neg hb.le]
  have h2 : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have h3 : (1 + 2 * t) ^ (1 / 2 : ℝ) ≠ 0 := by positivity
  field_simp

/-- Card P4. Laplace transform of `g²`: for `t ≥ 0`, `E e^{-t g²} = (1 + 2t)^{-1/2}`. -/
theorem gaussian_laplace (t : ℝ) (ht : 0 ≤ t) :
    ∫ x, Real.exp (-t * x ^ 2) ∂(gaussianReal 0 1) = (1 + 2 * t) ^ (-(1 / 2 : ℝ)) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  have hpt : ∀ x : ℝ, gaussianPDFReal 0 1 x * Real.exp (-t * x ^ 2)
      = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 + t) * x ^ 2) :=
    fun x => p4_gauss_pt t x
  simp only [hpt]
  have hb : (0 : ℝ) < 1 / 2 + t := by positivity
  rw [integral_const_mul, integral_gaussian, p4_laplace_alg t ht]

/-- Auxiliary: `(2π)^{-1/2} √(π/(A/2)) = A^{-1/2}` for `A > 0`. -/
private lemma p4_mgf_alg (A : ℝ) (hA : 0 < A) :
    (Real.sqrt (2 * Real.pi))⁻¹ * √(Real.pi / (A / 2)) = A ^ (-(1 / 2 : ℝ)) := by
  have e : Real.pi / (A / 2) = (2 * Real.pi) / A := by
    field_simp
  rw [e, Real.sqrt_div (by positivity), Real.sqrt_eq_rpow A, Real.rpow_neg hA.le]
  have h2 : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have h3 : A ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hA _).ne'
  field_simp

/-- Card P4. Completed-square MGF: for `λ ≥ 0`, `σ, c ∈ ℝ`,
`E exp(-λ(σg + c)²/2) = (1 + λσ²)^{-1/2} exp(-λc² / (2(1 + λσ²)))`. -/
theorem gaussian_completed_square (lam σ c : ℝ) (hlam : 0 ≤ lam) :
    ∫ x, Real.exp (-lam * (σ * x + c) ^ 2 / 2) ∂(gaussianReal 0 1)
      = (1 + lam * σ ^ 2) ^ (-(1 / 2 : ℝ))
        * Real.exp (-lam * c ^ 2 / (2 * (1 + lam * σ ^ 2))) := by
  have hA : 0 < 1 + lam * σ ^ 2 :=
    add_pos_of_pos_of_nonneg one_pos (mul_nonneg hlam (sq_nonneg σ))
  have hA0 : (1 + lam * σ ^ 2) ≠ 0 := hA.ne'
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  have hpt : ∀ x : ℝ, gaussianPDFReal 0 1 x * Real.exp (-lam * (σ * x + c) ^ 2 / 2)
      = (Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (-lam * c ^ 2 / (2 * (1 + lam * σ ^ 2)))
          * Real.exp (-((1 + lam * σ ^ 2) / 2) * (x + lam * σ * c / (1 + lam * σ ^ 2)) ^ 2)) := by
    intro x
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 2
    field_simp
    ring
  simp only [hpt]
  rw [integral_const_mul, integral_const_mul]
  have htr : ∫ x : ℝ, Real.exp (-((1 + lam * σ ^ 2) / 2) * (x + lam * σ * c / (1 + lam * σ ^ 2)) ^ 2)
      = ∫ x : ℝ, Real.exp (-((1 + lam * σ ^ 2) / 2) * x ^ 2) :=
    integral_add_right_eq_self (fun y : ℝ => Real.exp (-((1 + lam * σ ^ 2) / 2) * y ^ 2))
      (lam * σ * c / (1 + lam * σ ^ 2))
  rw [htr, integral_gaussian, ← p4_mgf_alg _ hA]
  ring

/-- Card P4. Density bound: `φ(x) ≤ 1/√(2π)` for the standard normal density. -/
theorem gaussian_pdf_le (x : ℝ) :
    gaussianPDFReal 0 1 x ≤ 1 / Real.sqrt (2 * Real.pi) := by
  rw [gaussianPDFReal_def, one_div]
  have h : Real.exp (-(x - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) ≤ 1 :=
    Real.exp_le_one_iff.2 (by simp only [NNReal.coe_one, mul_one, sub_zero]; nlinarith [sq_nonneg x])
  have hp : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹ := by positivity
  calc _ ≤ (Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹ * 1 := mul_le_mul_of_nonneg_left h hp
    _ = _ := by simp

/-! ## Stein's lemma (proved here; `GaussianIBP`) -/

/-- Auxiliary: closed form of the standard Gaussian density. -/
private lemma stein_pdf_eq (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((1 / 2 : ℝ) * x ^ 2)) := by
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  congr 2
  ring

/-- Auxiliary: derivative of the standard Gaussian density, `φ' = -x φ`. -/
private lemma stein_pdf_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have hfun : gaussianPDFReal 0 1
      = fun y : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((1 / 2 : ℝ) * y ^ 2)) :=
    funext stein_pdf_eq
  have h1 : HasDerivAt (fun y : ℝ => -((1 / 2 : ℝ) * y ^ 2)) (-x) x := by
    have h := ((hasDerivAt_pow 2 x).const_mul (1 / 2 : ℝ)).neg
    convert h using 1
    norm_num
    ring
  have h2 := (h1.exp).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  rw [hfun]
  dsimp only
  convert h2 using 1
  ring

/-- Auxiliary: `f ↦ φ·f` integrability transfers between `gaussianReal 0 1` and the
Lebesgue measure weighted by the density. -/
private lemma stein_pdf_integrable_smul_iff (f : ℝ → ℝ) :
    Integrable (fun x => gaussianPDFReal 0 1 x • f x) ↔ Integrable f (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  simp only [toReal_gaussianPDF]

/-- Auxiliary: polynomially bounded measurable functions are `gaussianReal 0 1`-integrable. -/
private lemma stein_integrable_of_bound {f : ℝ → ℝ} (hf : AEStronglyMeasurable f (gaussianReal 0 1))
    (C : ℝ) (k : ℕ) (h : ∀ x, |f x| ≤ C * (1 + |x| ^ k)) :
    Integrable f (gaussianReal 0 1) := by
  have hk : Integrable (fun x : ℝ => |x| ^ k) (gaussianReal 0 1) := by
    simpa [norm_pow, Real.norm_eq_abs, abs_pow] using (gaussian_pow_integrable_aux k).norm
  have hg : Integrable (fun x : ℝ => C * (1 + |x| ^ k)) (gaussianReal 0 1) :=
    ((integrable_const (1 : ℝ)).add hk).const_mul C
  refine hg.mono' hf (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact h x

/-- Auxiliary: `|x| ≤ 1 + |x|^(k+1)`. -/
private lemma stein_abs_le (x : ℝ) (k : ℕ) : |x| ≤ 1 + |x| ^ (k + 1) := by
  rcases le_total |x| 1 with h | h
  · have : 0 ≤ |x| ^ (k + 1) := by positivity
    linarith
  · have : |x| ≤ |x| ^ (k + 1) := le_self_pow₀ h (Nat.succ_ne_zero k)
    linarith

/-- Stein's lemma for `g ~ N(0,1)`: for `φ ∈ C¹(ℝ)` with `φ` and `φ'` bounded by
polynomials, `E[g φ(g)] = E[φ'(g)]`. -/
theorem gaussian_stein (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hφb : ∃ C : ℝ, ∃ k : ℕ, ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ k))
    (hdb : ∃ C : ℝ, ∃ k : ℕ, ∀ x : ℝ, |deriv φ x| ≤ C * (1 + |x| ^ k)) :
    ∫ x, x * φ x ∂(gaussianReal 0 1) = ∫ x, deriv φ x ∂(gaussianReal 0 1) := by
  exact stein_std_real hφ hφb hdb

/-! ## The identity of Appendix B, `eqn:app-de-erfc` -/

/-- Auxiliary: `2ξ² = 1/q` for `ξ = (2q)^{-1/2}`. -/
private lemma app_de_two_xi_sq (q ξ : ℝ) (hq : 0 < q) (hξ : ξ = (2 * q) ^ (-(1 / 2 : ℝ))) :
    2 * ξ ^ 2 = 1 / q := by
  have h : ξ ^ 2 = (2 * q)⁻¹ := by
    rw [hξ, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num [Real.rpow_neg_one]
  rw [h]
  field_simp

/-- Auxiliary: pointwise ratio identity `q g²/(1+q g²) = g²/(g²+2s)` when `2s = 1/q`. -/
private lemma app_de_ratio_pt (q g s : ℝ) (hq : 0 < q) (hs : 2 * s = 1 / q) :
    q * g ^ 2 / (1 + q * g ^ 2) = g ^ 2 / (g ^ 2 + 2 * s) := by
  rw [hs]
  have h1 : (0 : ℝ) < 1 + q * g ^ 2 := add_pos_of_pos_of_nonneg one_pos (mul_nonneg hq.le (sq_nonneg g))
  have h2 : (0 : ℝ) < g ^ 2 + 1 / q := add_pos_of_nonneg_of_pos (sq_nonneg g) (one_div_pos.mpr hq)
  rw [div_eq_div_iff h1.ne' h2.ne']
  field_simp
  ring

/-- Auxiliary: `g²/(g²+2s) = 1 - 1/(1+q g²)` when `2s = 1/q`. -/
private lemma app_de_one_sub_pt (q g s : ℝ) (hq : 0 < q) (hs : 2 * s = 1 / q) :
    g ^ 2 / (g ^ 2 + 2 * s) = 1 - 1 / (1 + q * g ^ 2) := by
  rw [hs]
  have h1 : (0 : ℝ) < 1 + q * g ^ 2 := add_pos_of_pos_of_nonneg one_pos (mul_nonneg hq.le (sq_nonneg g))
  have h2 : (0 : ℝ) < g ^ 2 + 1 / q := add_pos_of_nonneg_of_pos (sq_nonneg g) (one_div_pos.mpr hq)
  have h1' := h1.ne'
  have h2' := h2.ne'
  field_simp
  ring

/-- Auxiliary: `g ↦ 1/(1+q g²)` is integrable against `gaussianReal 0 1`. -/
private lemma app_de_inv_integrable (q : ℝ) (hq : 0 < q) :
    Integrable (fun g : ℝ => 1 / (1 + q * g ^ 2)) (gaussianReal 0 1) := by
  refine (integrable_const (1 : ℝ)).mono'
    (Continuous.aestronglyMeasurable
      (Continuous.div continuous_const (by fun_prop)
        (fun g => (add_pos_of_pos_of_nonneg one_pos (mul_nonneg hq.le (sq_nonneg g))).ne'))) ?_
  refine Filter.Eventually.of_forall fun g => ?_
  have h : (0 : ℝ) < 1 + q * g ^ 2 := add_pos_of_pos_of_nonneg one_pos (mul_nonneg hq.le (sq_nonneg g))
  rw [Real.norm_eq_abs, abs_of_pos (div_pos one_pos h), div_le_one h]
  nlinarith [mul_nonneg hq.le (sq_nonneg g)]

/-- Auxiliary: `∫_{(0,∞)} e^{-u(1+q g²)} du = 1/(1+q g²)`. -/
private lemma app_de_laplace_inv (q g : ℝ) (hq : 0 < q) :
    ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(1 + q * g ^ 2) * u) = 1 / (1 + q * g ^ 2) := by
  have hb : -(1 + q * g ^ 2) < 0 := by
    nlinarith [mul_nonneg hq.le (sq_nonneg g)]
  rw [integral_exp_mul_Ioi hb 0, mul_zero, Real.exp_zero, neg_div_neg_eq]

/-- Auxiliary: Gaussian average of `e^{-u(1+q g²)}` is `e^{-u}(1+2uq)^{-1/2}`. -/
private lemma app_de_gauss_inner (q u : ℝ) (hq : 0 < q) (hu : 0 ≤ u) :
    ∫ g, Real.exp (-(1 + q * g ^ 2) * u) ∂(gaussianReal 0 1)
      = Real.exp (-u) * (1 + 2 * (u * q)) ^ (-(1 / 2 : ℝ)) := by
  have hpt : ∀ g : ℝ, Real.exp (-(1 + q * g ^ 2) * u) = Real.exp (-u) * Real.exp (-(u * q) * g ^ 2) := by
    intro g
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [hpt]
  rw [integral_const_mul, gaussian_laplace (u * q) (mul_nonneg hu hq.le)]

/-- Auxiliary: Fubini for the Laplace representation of `E[1/(1+q g²)]`. -/
private lemma app_de_fubini (q : ℝ) (hq : 0 < q) :
    ∫ g, 1 / (1 + q * g ^ 2) ∂(gaussianReal 0 1)
      = ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * (1 + 2 * (u * q)) ^ (-(1 / 2 : ℝ)) := by
  have hμ : ∀ᵐ p ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod (gaussianReal 0 1)),
      p.1 ∈ Set.Ioi (0 : ℝ) :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_Ioi.preimage measurable_fst)).2
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact ae_of_all _ fun g => hu)
  have hF : Integrable (fun p : ℝ × ℝ => Real.exp (-(1 + q * p.2 ^ 2) * p.1))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (gaussianReal 0 1)) := by
    refine Integrable.mono' (g := fun p : ℝ × ℝ => Real.exp (-1 * p.1) * 1) ?_
      (by fun_prop : Continuous fun p : ℝ × ℝ => Real.exp (-(1 + q * p.2 ^ 2) * p.1)).aestronglyMeasurable ?_
    · exact Integrable.mul_prod (exp_neg_integrableOn_Ioi 0 one_pos) (integrable_const (1 : ℝ))
    · filter_upwards [hμ] with p hp
      have hp' : (0 : ℝ) < p.1 := hp
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_one]
      apply Real.exp_le_exp.2
      nlinarith [mul_nonneg (mul_nonneg hq.le (sq_nonneg p.2)) hp'.le]
  have hswap := integral_integral_swap (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (ν := gaussianReal 0 1) (f := fun u g => Real.exp (-(1 + q * g ^ 2) * u)) hF
  calc ∫ g, 1 / (1 + q * g ^ 2) ∂(gaussianReal 0 1)
      = ∫ g, (∫ u in Set.Ioi (0 : ℝ), Real.exp (-(1 + q * g ^ 2) * u)) ∂(gaussianReal 0 1) := by
        congr 1
        funext g
        exact (app_de_laplace_inv q g hq).symm
    _ = ∫ u in Set.Ioi (0 : ℝ), ∫ g, Real.exp (-(1 + q * g ^ 2) * u) ∂(gaussianReal 0 1) := hswap.symm
    _ = ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * (1 + 2 * (u * q)) ^ (-(1 / 2 : ℝ)) :=
        setIntegral_congr_fun measurableSet_Ioi (fun u hu => app_de_gauss_inner q u hq (le_of_lt hu))

/-- Auxiliary: pointwise identity for the substitution `u = ρ² - ξ²`. -/
private lemma app_de_subst_pt (ξ x : ℝ) (hξ : 0 < ξ) (hx : ξ ≤ x) :
    (Real.exp (-(x ^ 2 - ξ ^ 2)) * (1 + (x ^ 2 - ξ ^ 2) / ξ ^ 2) ^ (-(1 / 2 : ℝ))) * (2 * x)
      = 2 * ξ * Real.exp (ξ ^ 2) * Real.exp (-1 * x ^ 2) := by
  have hx0 : 0 < x := lt_of_lt_of_le hξ hx
  have hx0' : x ≠ 0 := hx0.ne'
  have hξ0' : ξ ≠ 0 := hξ.ne'
  have hb : 1 + (x ^ 2 - ξ ^ 2) / ξ ^ 2 = (x / ξ) ^ 2 := by
    field_simp
    ring
  have hr : ((x / ξ) ^ 2) ^ (-(1 / 2 : ℝ)) = ξ / x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_pos hx0 hξ).le]
    norm_num [Real.rpow_neg_one, inv_div]
  have he : Real.exp (-(x ^ 2 - ξ ^ 2)) = Real.exp (ξ ^ 2) * Real.exp (-1 * x ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hb, hr, he]
  field_simp

/-- Auxiliary: substitution `u = ρ² - ξ²` in the Laplace-type integral. -/
private lemma app_de_subst (ξ : ℝ) (hξ : 0 < ξ) :
    ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * (1 + u / ξ ^ 2) ^ (-(1 / 2 : ℝ))
      = Real.sqrt Real.pi * ξ * Real.exp (ξ ^ 2) * erfc ξ := by
  have hf : ContinuousOn (fun ρ : ℝ => ρ ^ 2 - ξ ^ 2) (Set.Ici ξ) :=
    (by fun_prop : Continuous fun ρ : ℝ => ρ ^ 2 - ξ ^ 2).continuousOn
  have hft : Filter.Tendsto (fun ρ : ℝ => ρ ^ 2 - ξ ^ 2) Filter.atTop Filter.atTop := by
    have h := Filter.tendsto_atTop_add_const_right _ (-ξ ^ 2) (Filter.tendsto_pow_atTop two_ne_zero)
    exact h.congr (fun ρ => by ring)
  have hff' : ∀ x ∈ Set.Ioi ξ, HasDerivWithinAt (fun ρ : ℝ => ρ ^ 2 - ξ ^ 2) (2 * x) (Set.Ioi x) x :=
    fun x _ => (((hasDerivAt_pow 2 x).sub_const (ξ ^ 2)).hasDerivWithinAt).congr_deriv (by norm_num)
  have hgc : ContinuousOn (fun u : ℝ => Real.exp (-u) * (1 + u / ξ ^ 2) ^ (-(1 / 2 : ℝ))) (Set.Ioi 0) := by
    apply ContinuousOn.mul
    · exact (by fun_prop : Continuous fun u : ℝ => Real.exp (-u)).continuousOn
    · apply ContinuousOn.rpow_const
      · exact (continuous_const.add (continuous_id.div_const _)).continuousOn
      · intro u hu
        left
        have hu' : (0 : ℝ) < u := hu
        exact (add_pos_of_pos_of_nonneg one_pos (div_nonneg hu'.le (sq_nonneg ξ))).ne'
  have hgi : IntegrableOn (fun u : ℝ => Real.exp (-u) * (1 + u / ξ ^ 2) ^ (-(1 / 2 : ℝ))) (Set.Ioi 0) := by
    refine Integrable.mono' (g := fun u : ℝ => Real.exp (-1 * u)) (exp_neg_integrableOn_Ioi 0 one_pos)
      (hgc.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu' : (0 : ℝ) < u := hu
    have hbase : (0 : ℝ) < 1 + u / ξ ^ 2 := add_pos_of_pos_of_nonneg one_pos (div_nonneg hu'.le (sq_nonneg ξ))
    have hle : (1 + u / ξ ^ 2) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos
        (by have := div_nonneg hu'.le (sq_nonneg ξ); linarith) (by norm_num)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hbase.le _))]
    calc Real.exp (-u) * (1 + u / ξ ^ 2) ^ (-(1 / 2 : ℝ)) ≤ Real.exp (-u) * 1 :=
          mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
      _ = Real.exp (-1 * u) := by rw [mul_one, neg_one_mul]
  have hgi' : IntegrableOn (fun u : ℝ => Real.exp (-u) * (1 + u / ξ ^ 2) ^ (-(1 / 2 : ℝ))) (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by simp)).2 hgi
  have hg1 : IntegrableOn (fun u : ℝ => Real.exp (-u) * (1 + u / ξ ^ 2) ^ (-(1 / 2 : ℝ)))
      ((fun ρ : ℝ => ρ ^ 2 - ξ ^ 2) '' Set.Ici ξ) := by
    refine hgi'.mono_set ?_
    rintro _ ⟨ρ, hρ, rfl⟩
    have hρ' : ξ ≤ ρ := hρ
    show (0 : ℝ) ≤ ρ ^ 2 - ξ ^ 2
    nlinarith
  have hg2 : IntegrableOn (fun x : ℝ => ((fun u : ℝ => Real.exp (-u) * (1 + u / ξ ^ 2) ^ (-(1 / 2 : ℝ)))
      ∘ (fun ρ : ℝ => ρ ^ 2 - ξ ^ 2)) x * (fun ρ : ℝ => 2 * ρ) x) (Set.Ici ξ) := by
    refine IntegrableOn.congr_fun
      (f := fun x : ℝ => 2 * ξ * Real.exp (ξ ^ 2) * Real.exp (-1 * x ^ 2)) ?_
      (fun x hx => (app_de_subst_pt ξ x hξ hx).symm) measurableSet_Ici
    exact ((integrable_exp_neg_mul_sq one_pos).const_mul (2 * ξ * Real.exp (ξ ^ 2))).integrableOn
  have hsub : (fun ρ : ℝ => ρ ^ 2 - ξ ^ 2) '' Set.Ioi ξ ⊆ Set.Ioi 0 := by
    rintro _ ⟨ρ, hρ, rfl⟩
    have hρ' : ξ < ρ := hρ
    change (0 : ℝ) < ρ ^ 2 - ξ ^ 2
    nlinarith
  have hcomp := integral_comp_mul_deriv_Ioi (a := ξ) (f := fun ρ : ℝ => ρ ^ 2 - ξ ^ 2)
    (f' := fun ρ : ℝ => 2 * ρ)
    (g := fun u : ℝ => Real.exp (-u) * (1 + u / ξ ^ 2) ^ (-(1 / 2 : ℝ)))
    hf hft hff' (hgc.mono hsub) hg1 hg2
  have hcalc : ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * (1 + u / ξ ^ 2) ^ (-(1 / 2 : ℝ))
      = ∫ x in Set.Ioi ξ, 2 * ξ * Real.exp (ξ ^ 2) * Real.exp (-1 * x ^ 2) := by
    calc ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * (1 + u / ξ ^ 2) ^ (-(1 / 2 : ℝ))
        = ∫ u in Set.Ioi ((fun ρ : ℝ => ρ ^ 2 - ξ ^ 2) ξ),
            Real.exp (-u) * (1 + u / ξ ^ 2) ^ (-(1 / 2 : ℝ)) := by simp
      _ = ∫ x in Set.Ioi ξ, ((fun u : ℝ => Real.exp (-u) * (1 + u / ξ ^ 2) ^ (-(1 / 2 : ℝ)))
            ∘ (fun ρ : ℝ => ρ ^ 2 - ξ ^ 2)) x * (fun ρ : ℝ => 2 * ρ) x := hcomp.symm
      _ = ∫ x in Set.Ioi ξ, 2 * ξ * Real.exp (ξ ^ 2) * Real.exp (-1 * x ^ 2) :=
          setIntegral_congr_fun measurableSet_Ioi
            (fun x hx => app_de_subst_pt ξ x hξ (le_of_lt hx))
  have h4 : ∫ x in Set.Ioi ξ, Real.exp (-1 * x ^ 2) = erfc ξ * Real.sqrt Real.pi / 2 := by
    simp only [neg_one_mul]
    unfold erfc
    have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
    field_simp
  rw [hcalc, integral_const_mul, h4]
  ring

/-- Card P6. Appendix B `eqn:app-de-erfc`, first equality (`q J(q) = E[qg²/(1+qg²)]`,
`J(x) = E g²/(1+xg²)`): for `q > 0` and `ξ = (2q)^{-1/2}`,
`E[qg²/(1+qg²)] = E[g²/(g²+2ξ²)]`. -/
theorem gaussian_ratio_eq_erfc_integrand (q ξ : ℝ) (hq : 0 < q) (hξ : ξ = (2 * q) ^ (-(1 / 2 : ℝ))) :
    ∫ g, q * g ^ 2 / (1 + q * g ^ 2) ∂(gaussianReal 0 1)
      = ∫ g, g ^ 2 / (g ^ 2 + 2 * ξ ^ 2) ∂(gaussianReal 0 1) := by
  have hs := app_de_two_xi_sq q ξ hq hξ
  congr 1
  funext g
  exact app_de_ratio_pt q g (ξ ^ 2) hq hs

/-- Card P6. Appendix B `eqn:app-de-erfc`, second equality: for `q > 0` and `ξ = (2q)^{-1/2}`,
`E[g²/(g²+2ξ²)] = 1 - √π ξ e^{ξ²} erfc(ξ)`. -/
theorem gaussian_erfc_integrand_eq (q ξ : ℝ) (hq : 0 < q) (hξ : ξ = (2 * q) ^ (-(1 / 2 : ℝ))) :
    ∫ g, g ^ 2 / (g ^ 2 + 2 * ξ ^ 2) ∂(gaussianReal 0 1)
      = 1 - Real.sqrt Real.pi * ξ * Real.exp (ξ ^ 2) * erfc ξ := by
  have hξpos : 0 < ξ := by
    rw [hξ]
    exact Real.rpow_pos_of_pos (by linarith) _
  have hs := app_de_two_xi_sq q ξ hq hξ
  have hpt : ∀ g : ℝ, g ^ 2 / (g ^ 2 + 2 * ξ ^ 2) = 1 - 1 / (1 + q * g ^ 2) :=
    fun g => app_de_one_sub_pt q g (ξ ^ 2) hq hs
  have h2q : ∀ u : ℝ, 2 * (u * q) = u / ξ ^ 2 := by
    intro u
    have hq' : q * (2 * ξ ^ 2) = 1 := by
      rw [hs]
      field_simp
    rw [eq_div_iff (pow_pos hξpos 2).ne']
    linear_combination u * hq'
  have hconv : ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * (1 + 2 * (u * q)) ^ (-(1 / 2 : ℝ))
      = ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * (1 + u / ξ ^ 2) ^ (-(1 / 2 : ℝ)) :=
    setIntegral_congr_fun measurableSet_Ioi (fun u _ => by rw [h2q u])
  simp_rw [hpt]
  rw [integral_sub (integrable_const (1 : ℝ)) (app_de_inv_integrable q hq)]
  rw [integral_const, app_de_fubini q hq, hconv, app_de_subst ξ hξpos, probReal_univ, one_smul]

/-! ## Standard Gaussian vector `g ~ stdGaussianPi n` -/

/-- Auxiliary: `(1+x²)^N ≤ 2^N (1+|x|^(2N))`. -/
private lemma p7_one_add_sq_pow (N : ℕ) (x : ℝ) :
    (1 + x ^ 2) ^ N ≤ 2 ^ N * (1 + |x| ^ (2 * N)) := by
  have hx : (x ^ 2) ^ N = |x| ^ (2 * N) := by
    rw [← sq_abs x, ← pow_mul]
  have h0 : 0 ≤ |x| ^ (2 * N) := by positivity
  rcases le_total (x ^ 2) 1 with h | h
  · calc (1 + x ^ 2) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      _ ≤ 2 ^ N * (1 + |x| ^ (2 * N)) := by
        have : (0 : ℝ) < 2 ^ N := by positivity
        nlinarith
  · calc (1 + x ^ 2) ^ N ≤ (2 * x ^ 2) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      _ = 2 ^ N * |x| ^ (2 * N) := by rw [mul_pow, hx]
      _ ≤ 2 ^ N * (1 + |x| ^ (2 * N)) := by
        have : (0 : ℝ) < 2 ^ N := by positivity
        nlinarith

/-- Auxiliary: polynomial bound `|x|^a (x²+c)^b ≤ (1+c)^b 2^(a+b) (1+|x|^(2(a+b)))`. -/
private lemma p7_poly_bound (a b : ℕ) (c x : ℝ) (hc : 0 ≤ c) :
    |x| ^ a * (x ^ 2 + c) ^ b ≤ (1 + c) ^ b * 2 ^ (a + b) * (1 + |x| ^ (2 * (a + b))) := by
  have h1 : |x| ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg (|x| - 1), sq_abs x]
  have h2 : x ^ 2 + c ≤ (1 + c) * (1 + x ^ 2) := by nlinarith [sq_nonneg x]
  have h3 : |x| ^ a ≤ (1 + x ^ 2) ^ a := pow_le_pow_left₀ (abs_nonneg x) h1 a
  have h4 : (x ^ 2 + c) ^ b ≤ ((1 + c) * (1 + x ^ 2)) ^ b :=
    pow_le_pow_left₀ (by positivity) h2 b
  calc |x| ^ a * (x ^ 2 + c) ^ b ≤ (1 + x ^ 2) ^ a * ((1 + c) * (1 + x ^ 2)) ^ b :=
        mul_le_mul h3 h4 (by positivity) (by positivity)
    _ = (1 + c) ^ b * (1 + x ^ 2) ^ (a + b) := by rw [mul_pow, pow_add]; ring
    _ ≤ (1 + c) ^ b * (2 ^ (a + b) * (1 + |x| ^ (2 * (a + b)))) :=
        mul_le_mul_of_nonneg_left (p7_one_add_sq_pow _ x) (by positivity)
    _ = _ := by ring

/-- Auxiliary: `∫ z_i^{k}` type integrability: powers of `‖z‖²` are integrable. -/
private lemma p7_sq_pow_integrable (n q : ℕ) :
    Integrable (fun z : Fin n → ℝ => (∑ i, z i ^ 2) ^ q) (stdGaussianPi n) := by
  cases q with
  | zero => simpa using integrable_const (1 : ℝ)
  | succ p =>
    have hint : ∀ i : Fin n, Integrable (fun z : Fin n → ℝ => (z i ^ 2) ^ (p + 1))
        (stdGaussianPi n) := by
      intro i
      have h := gaussian_integrable_pow (2 * (p + 1))
      have hm : MeasurePreserving (fun z : Fin n → ℝ => z i) (stdGaussianPi n)
          (gaussianReal 0 1) := measurePreserving_eval _ i
      have := (hm.integrable_comp (g := fun x : ℝ => x ^ (2 * (p + 1)))
        (by fun_prop)).2 h
      refine this.congr (Filter.Eventually.of_forall fun z => ?_)
      simp [← pow_mul]
    have hsum : Integrable (fun z : Fin n → ℝ => ∑ i, (z i ^ 2) ^ (p + 1)) (stdGaussianPi n) :=
      integrable_finset_sum _ fun i _ => hint i
    refine (hsum.const_mul ((n : ℝ) ^ p)).mono' (Continuous.aestronglyMeasurable (by fun_prop))
      (Filter.Eventually.of_forall fun z => ?_)
    have h := pow_sum_div_card_le_sum_pow (s := Finset.univ) (f := fun i : Fin n => z i ^ 2)
      (fun i _ => by positivity) p
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [Finset.card_univ, Fintype.card_fin] at h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (0 : ℝ) < (n : ℝ) ^ p := by positivity
      rw [div_le_iff₀ hn'] at h
      linarith

/-- Auxiliary: `z_i² (∑ z²)^k` is integrable. -/
private lemma p7_coord_integrable (n : ℕ) (i : Fin n) (k : ℕ) :
    Integrable (fun z : Fin n → ℝ => z i ^ 2 * (∑ j, z j ^ 2) ^ k) (stdGaussianPi n) := by
  refine (p7_sq_pow_integrable n (k + 1)).mono' (Continuous.aestronglyMeasurable (by fun_prop))
    (Filter.Eventually.of_forall fun z => ?_)
  have hle : z i ^ 2 ≤ ∑ j, z j ^ 2 :=
    Finset.single_le_sum (f := fun j => z j ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
  have hS0 : 0 ≤ ∑ j, z j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg (z j)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hS0 k))]
  exact (mul_le_mul_of_nonneg_right hle (pow_nonneg hS0 k)).trans_eq (pow_succ' _ _).symm

/-- Auxiliary: one-dimensional Stein identity for the polynomial `x (x²+c)^(r+1)`. -/
private lemma p7_inner (c : ℝ) (hc : 0 ≤ c) (r : ℕ) :
    ∫ x, (x ^ 2 * (x ^ 2 + c) ^ (r + 1) - (x ^ 2 + c) ^ (r + 1)
      - 2 * ((r : ℝ) + 1) * (x ^ 2 * (x ^ 2 + c) ^ r)) ∂(gaussianReal 0 1) = 0 := by
  set φ : ℝ → ℝ := fun x => x * (x ^ 2 + c) ^ (r + 1) with hφ
  have hφd : ∀ x, HasDerivAt φ ((x ^ 2 + c) ^ (r + 1)
      + 2 * ((r : ℝ) + 1) * (x ^ 2 * (x ^ 2 + c) ^ r)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2 + c) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).add_const c
    have h := (hasDerivAt_id' x).fun_mul (h1.fun_pow (r + 1))
    convert h using 1
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  have hderiv : ∀ x, deriv φ x = (x ^ 2 + c) ^ (r + 1)
      + 2 * ((r : ℝ) + 1) * (x ^ 2 * (x ^ 2 + c) ^ r) := fun x => (hφd x).deriv
  have hcd : ContDiff ℝ 1 φ := by rw [hφ]; fun_prop
  have hb1 : ∀ x : ℝ, |φ x| ≤ ((1 + c) ^ (r + 1) * 2 ^ (1 + (r + 1)))
      * (1 + |x| ^ (2 * (1 + (r + 1)))) := by
    intro x
    have := p7_poly_bound 1 (r + 1) c x hc
    have hxc : 0 ≤ x ^ 2 + c := by positivity
    rw [hφ, abs_mul, abs_of_nonneg (pow_nonneg hxc (r + 1))]
    simpa [pow_one, mul_assoc] using this
  have hb2 : ∀ x : ℝ, |deriv φ x| ≤ ((2 * (r : ℝ) + 3) * ((1 + c) ^ (r + 1) * 2 ^ (0 + (r + 1))))
      * (1 + |x| ^ (2 * (0 + (r + 1)))) := by
    intro x
    have := p7_poly_bound 0 (r + 1) c x hc
    have hxc : 0 ≤ x ^ 2 + c := by positivity
    have h3 : 0 ≤ (x ^ 2 + c) ^ r := pow_nonneg hxc r
    rw [hderiv, abs_of_nonneg (by positivity)]
    have h2 : x ^ 2 ≤ x ^ 2 + c := by linarith
    have h4 : (x ^ 2 + c) ^ (r + 1) + 2 * ((r : ℝ) + 1) * (x ^ 2 * (x ^ 2 + c) ^ r)
        ≤ (2 * (r : ℝ) + 3) * (x ^ 2 + c) ^ (r + 1) := by
      rw [pow_succ]
      have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * ((r : ℝ) + 1) * (x ^ 2 + c) ^ r),
        mul_nonneg h3 hxc]
    have h5 : (0 : ℝ) ≤ 2 * (r : ℝ) + 3 := by positivity
    calc _ ≤ (2 * (r : ℝ) + 3) * (x ^ 2 + c) ^ (r + 1) := h4
      _ ≤ (2 * (r : ℝ) + 3) * ((1 + c) ^ (r + 1) * 2 ^ (0 + (r + 1))
            * (1 + |x| ^ (2 * (0 + (r + 1))))) := by
          refine mul_le_mul_of_nonneg_left ?_ h5
          simpa using this
      _ = _ := by ring
  have hS := gaussian_stein φ hcd ⟨_, _, hb1⟩ ⟨_, _, hb2⟩
  have hi1 : Integrable (fun x => x * φ x) (gaussianReal 0 1) := by
    refine stein_integrable_of_bound (Continuous.aestronglyMeasurable (by rw [hφ]; fun_prop))
      (((1 + c) ^ (r + 1) * 2 ^ (2 + (r + 1)))) (2 * (2 + (r + 1))) fun x => ?_
    have := p7_poly_bound 2 (r + 1) c x hc
    have hxc : 0 ≤ x ^ 2 + c := by positivity
    rw [hφ]
    simp only
    rw [← mul_assoc, ← sq, abs_of_nonneg (by positivity)]
    simpa [sq_abs] using this
  have hi2 : Integrable (deriv φ) (gaussianReal 0 1) :=
    stein_integrable_of_bound hcd.continuous_deriv_one.aestronglyMeasurable _ _ hb2
  have hfun : (fun x : ℝ => x ^ 2 * (x ^ 2 + c) ^ (r + 1) - (x ^ 2 + c) ^ (r + 1)
      - 2 * ((r : ℝ) + 1) * (x ^ 2 * (x ^ 2 + c) ^ r)) = fun x => x * φ x - deriv φ x := by
    funext x
    rw [hderiv, hφ]
    ring
  rw [hfun, integral_sub hi1 hi2, hS, sub_self]

/-- Auxiliary: slicing `stdGaussianPi (m+1)` along coordinate `i`. -/
private lemma p7_slice (m : ℕ) (i : Fin (m + 1)) (f : (Fin (m + 1) → ℝ) → ℝ)
    (hint : Integrable f (stdGaussianPi (m + 1))) :
    ∫ z, f z ∂(stdGaussianPi (m + 1))
      = ∫ y, ∫ x, f (i.insertNth x y) ∂(gaussianReal 0 1) ∂(stdGaussianPi m) := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => gaussianReal (0 : ℝ) 1) i
  have hg : ∫ z, f z ∂(stdGaussianPi (m + 1))
      = ∫ p, f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm p)
          ∂((gaussianReal 0 1).prod (stdGaussianPi m)) := by
    have := hmp.integral_comp' (g := fun p => f ((MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (m + 1) => ℝ) i).symm p))
    simp only [MeasurableEquiv.symm_apply_apply] at this
    exact this
  have hint' : Integrable (fun p => f ((MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (m + 1) => ℝ) i).symm p)) ((gaussianReal 0 1).prod (stdGaussianPi m)) :=
    (MeasurePreserving.symm _ hmp).integrable_comp_of_integrable hint
  rw [hg, integral_prod_symm _ hint']
  rfl


/-- Auxiliary: the sum of squares of an `insertNth`. -/
private lemma p7_sum_insertNth (m : ℕ) (i : Fin (m + 1)) (x : ℝ) (y : Fin m → ℝ) :
    ∑ j, (i.insertNth x y j) ^ 2 = x ^ 2 + ∑ j, y j ^ 2 := by
  rw [Fin.sum_univ_succAbove _ i]
  simp

/-- Auxiliary: coordinatewise Gaussian integration by parts for `z_i² (∑ z²)^(r+1)`. -/
private lemma p7_coord_rec (m r : ℕ) (i : Fin (m + 1)) :
    ∫ z : Fin (m + 1) → ℝ, z i ^ 2 * (∑ j, z j ^ 2) ^ (r + 1) ∂(stdGaussianPi (m + 1))
      = ∫ z : Fin (m + 1) → ℝ, (∑ j, z j ^ 2) ^ (r + 1) ∂(stdGaussianPi (m + 1))
        + 2 * ((r : ℝ) + 1) * ∫ z : Fin (m + 1) → ℝ, z i ^ 2 * (∑ j, z j ^ 2) ^ r
          ∂(stdGaussianPi (m + 1)) := by
  have hA := p7_coord_integrable (m + 1) i (r + 1)
  have hB := p7_sq_pow_integrable (m + 1) (r + 1)
  have hC := p7_coord_integrable (m + 1) i r
  have hAB : Integrable (fun z : Fin (m + 1) → ℝ => z i ^ 2 * (∑ j, z j ^ 2) ^ (r + 1)
      - (∑ j, z j ^ 2) ^ (r + 1)) (stdGaussianPi (m + 1)) := hA.sub hB
  have hC' : Integrable (fun z : Fin (m + 1) → ℝ =>
      2 * ((r : ℝ) + 1) * (z i ^ 2 * (∑ j, z j ^ 2) ^ r)) (stdGaussianPi (m + 1)) :=
    hC.const_mul _
  have hD : Integrable (fun z : Fin (m + 1) → ℝ => (z i ^ 2 * (∑ j, z j ^ 2) ^ (r + 1)
      - (∑ j, z j ^ 2) ^ (r + 1) - 2 * ((r : ℝ) + 1) * (z i ^ 2 * (∑ j, z j ^ 2) ^ r)))
      (stdGaussianPi (m + 1)) := hAB.sub hC'
  have h0 : ∫ z : Fin (m + 1) → ℝ, (z i ^ 2 * (∑ j, z j ^ 2) ^ (r + 1)
      - (∑ j, z j ^ 2) ^ (r + 1) - 2 * ((r : ℝ) + 1) * (z i ^ 2 * (∑ j, z j ^ 2) ^ r))
      ∂(stdGaussianPi (m + 1)) = 0 := by
    rw [p7_slice m i _ hD]
    have : ∀ y : Fin m → ℝ, ∫ x, ((i.insertNth x y : Fin (m + 1) → ℝ) i ^ 2
        * (∑ j, (i.insertNth x y : Fin (m + 1) → ℝ) j ^ 2) ^ (r + 1)
        - (∑ j, (i.insertNth x y : Fin (m + 1) → ℝ) j ^ 2) ^ (r + 1)
        - 2 * ((r : ℝ) + 1) * ((i.insertNth x y : Fin (m + 1) → ℝ) i ^ 2
          * (∑ j, (i.insertNth x y : Fin (m + 1) → ℝ) j ^ 2) ^ r)) ∂(gaussianReal 0 1) = 0 := by
      intro y
      have := p7_inner (∑ j, y j ^ 2) (Finset.sum_nonneg fun j _ => sq_nonneg (y j)) r
      simpa only [p7_sum_insertNth, Fin.insertNth_apply_same] using this
    simp only [this, integral_zero]
  rw [integral_sub hAB hC', integral_sub hA hB, integral_const_mul] at h0
  linarith

/-- Auxiliary: `∑_i E[z_i² S^q] = E[S^{q+1}]`. -/
private lemma p7_sum_coord (n q : ℕ) :
    ∑ i : Fin n, ∫ z : Fin n → ℝ, z i ^ 2 * (∑ j, z j ^ 2) ^ q ∂(stdGaussianPi n)
      = ∫ z : Fin n → ℝ, (∑ j, z j ^ 2) ^ (q + 1) ∂(stdGaussianPi n) := by
  rw [← integral_finset_sum _ fun i _ => p7_coord_integrable n i q]
  congr 1
  funext z
  rw [pow_succ, mul_comm, Finset.sum_mul]

/-- Auxiliary: the moment recursion `E S^{q+1} = (n + 2q) E S^q`. -/
private lemma p7_moment_rec (m q : ℕ) :
    ∫ z : Fin (m + 1) → ℝ, (∑ j, z j ^ 2) ^ (q + 1) ∂(stdGaussianPi (m + 1))
      = ((m + 1 : ℕ) + 2 * (q : ℝ)) * ∫ z : Fin (m + 1) → ℝ, (∑ j, z j ^ 2) ^ q
          ∂(stdGaussianPi (m + 1)) := by
  cases q with
  | zero =>
    rw [← p7_sum_coord]
    have h1 : ∀ i : Fin (m + 1), ∫ z : Fin (m + 1) → ℝ, z i ^ 2 * (∑ j, z j ^ 2) ^ 0
        ∂(stdGaussianPi (m + 1)) = 1 := by
      intro i
      have : (stdGaussianPi (m + 1)).map (fun z : Fin (m + 1) → ℝ => z i) = gaussianReal 0 1 :=
        (measurePreserving_eval (fun _ : Fin (m + 1) => gaussianReal (0 : ℝ) 1) i).map_eq
      simp only [pow_zero, mul_one]
      have h2 := integral_map (μ := stdGaussianPi (m + 1)) (φ := fun z : Fin (m + 1) → ℝ => z i)
        (f := fun x : ℝ => x ^ 2) (measurable_pi_apply i).aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))
      rw [this] at h2
      exact h2.symm.trans gaussian_moment_two
    rw [Finset.sum_congr rfl (fun i _ => h1 i)]
    simp
  | succ r =>
    rw [← p7_sum_coord]
    simp_rw [p7_coord_rec m r]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, p7_sum_coord]
    simp
    push_cast
    ring

/-- Card P7. Each coordinate of `g` is `N(0,1)`. -/
theorem stdGaussianPi_map_coord (n : ℕ) (i : Fin n) :
    (stdGaussianPi n).map (fun z : Fin n → ℝ => z i) = gaussianReal 0 1 := by
  unfold stdGaussianPi
  exact (measurePreserving_eval (fun _ : Fin n => gaussianReal (0 : ℝ) 1) i).map_eq

/-- Card P7. `E‖g‖^{2q} = d_q(n) = n(n+2)⋯(n+2q-2)` for `q ≥ 1`, where `‖g‖² = ∑ g_i²`. -/
theorem stdGaussianPi_sq_norm_moment (n q : ℕ) (hq : 1 ≤ q) :
    ∫ z : Fin n → ℝ, (∑ i, z i ^ 2) ^ q ∂(stdGaussianPi n)
      = ∏ j ∈ Finset.range q, ((n : ℝ) + 2 * (j : ℝ)) := by
  cases n with
  | zero =>
    have h0 : ∏ j ∈ Finset.range q, (((0 : ℕ) : ℝ) + 2 * (j : ℝ)) = 0 :=
      Finset.prod_eq_zero (i := 0) (Finset.mem_range.2 hq) (by simp)
    rw [h0]
    simp [zero_pow (by omega : q ≠ 0)]
  | succ m =>
    clear hq
    induction q with
    | zero => simp
    | succ q ih =>
      rw [p7_moment_rec, ih, Finset.prod_range_succ]
      ring

/-- Card P7. For `i ≠ j`, `E|g_i g_j| = 2/π`. -/
theorem stdGaussianPi_abs_mul_coord (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    ∫ z : Fin n → ℝ, |z i * z j| ∂(stdGaussianPi n) = 2 / Real.pi := by
  unfold stdGaussianPi
  have hprod : ∀ z : Fin n → ℝ,
      ∏ k, (if k = i ∨ k = j then |z k| else 1) = |z i| * |z j| := by
    intro z
    exact Finset.prod_eq_mul (f := fun k => if k = i ∨ k = j then |z k| else 1) i j hij
      (fun c _ hc => by simp [hc.1, hc.2])
      (fun h => absurd (Finset.mem_univ i) h) (fun h => absurd (Finset.mem_univ j) h)
      |>.trans (by simp)
  have hfun : (fun z : Fin n → ℝ => |z i * z j|)
      = fun z : Fin n → ℝ => ∏ k, (fun (k : Fin n) (x : ℝ) =>
          if k = i ∨ k = j then |x| else 1) k (z k) := by
    funext z
    change |z i * z j| = ∏ k, (if k = i ∨ k = j then |z k| else 1)
    rw [hprod z, abs_mul]
  have hint : ∀ k : Fin n, ∫ x, (if k = i ∨ k = j then |x| else 1) ∂(gaussianReal 0 1)
      = if k = i ∨ k = j then Real.sqrt (2 / Real.pi) else 1 := by
    intro k
    split_ifs
    · exact gaussian_abs_moment
    · simp
  have hconst : ∏ k, (if k = i ∨ k = j then Real.sqrt (2 / Real.pi) else 1)
      = Real.sqrt (2 / Real.pi) * Real.sqrt (2 / Real.pi) :=
    (Finset.prod_eq_mul (f := fun k => if k = i ∨ k = j then Real.sqrt (2 / Real.pi) else 1)
      i j hij (fun c _ hc => by simp [hc.1, hc.2])
      (fun h => absurd (Finset.mem_univ i) h) (fun h => absurd (Finset.mem_univ j) h)).trans
      (by simp)
  rw [hfun, integral_fintype_prod_eq_prod
    (f := fun (k : Fin n) (x : ℝ) => if k = i ∨ k = j then |x| else 1)]
  change ∏ k, ∫ x, (if k = i ∨ k = j then |x| else 1) ∂(gaussianReal 0 1) = _
  rw [Finset.prod_congr rfl (fun k _ => hint k), hconst, Real.mul_self_sqrt (by positivity)]

/-- Card P7. Linear functionals: `∑_i g_i u_i ~ N(0, ‖u‖²)`. -/
theorem stdGaussianPi_linear_map (n : ℕ) (u : Fin n → ℝ) :
    (stdGaussianPi n).map (fun z : Fin n → ℝ => ∑ i, z i * u i)
      = gaussianReal 0 (Real.toNNReal (∑ i, u i ^ 2)) := by
  set v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 u with hv
  set L : StrongDual ℝ (EuclideanSpace ℝ (Fin n)) := innerSL ℝ v with hL
  have hfun : (fun z : Fin n → ℝ => ∑ i, z i * u i)
      = (fun x => L x) ∘ (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) := by
    funext z
    simp [hL, hv, PiLp.inner_apply, mul_comm]
  have hmap : (stdGaussianPi n).map (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))
      = stdGaussian (EuclideanSpace ℝ (Fin n)) := by
    unfold stdGaussianPi
    exact map_pi_eq_stdGaussian
  have hLm : Measurable (fun x : EuclideanSpace ℝ (Fin n) => L x) := L.continuous.measurable
  have hTm : Measurable (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) := by
    fun_prop
  rw [hfun, ← Measure.map_map hLm hTm, hmap, IsGaussian.map_eq_gaussianReal L,
    integral_strongDual_stdGaussian, variance_dual_stdGaussian]
  congr 2
  rw [hL, innerSL_apply_norm, hv, EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

/-- Card P8. Conditional Gaussian lemma. For `Δ ∈ ℝ^{n×m}`, measurable `f : ℝ → ℝ`, and
`g ~ N(0,I_n)`, `h ~ N(0,I_m)`: integrating over `z` first for fixed `w` gives a
`N(0, ‖Δw‖²)` law, i.e. `E_w E_z f(zᵀΔw) = E_w E_{x~N(0,‖Δw‖²)} f(x)`. -/
theorem stdGaussian_conditional_linear (n m : ℕ) (Δ : Matrix (Fin n) (Fin m) ℝ)
    (f : ℝ → ℝ) (hf : Measurable f) :
    ∫ w : Fin m → ℝ, (∫ z : Fin n → ℝ, f (∑ i, z i * (Δ.mulVec w) i) ∂(stdGaussianPi n))
        ∂(stdGaussianPi m)
      = ∫ w : Fin m → ℝ,
          (∫ x, f x ∂(gaussianReal 0 (Real.toNNReal (∑ i, (Δ.mulVec w) i ^ 2))))
          ∂(stdGaussianPi m) := by
  congr 1
  funext w
  have hφ : Measurable (fun z : Fin n → ℝ => ∑ i, z i * (Δ.mulVec w) i) := by fun_prop
  have h := integral_map (μ := stdGaussianPi n) (φ := fun z : Fin n → ℝ => ∑ i, z i * (Δ.mulVec w) i)
    hφ.aemeasurable hf.aestronglyMeasurable
  rw [stdGaussianPi_linear_map] at h
  exact h.symm

/-- Auxiliary: each squared coordinate is integrable. -/
private lemma p8_sq_coord_integrable (n : ℕ) (i : Fin n) :
    Integrable (fun z : Fin n → ℝ => z i ^ 2) (stdGaussianPi n) := by
  have hm : MeasurePreserving (fun z : Fin n → ℝ => z i) (stdGaussianPi n)
      (gaussianReal 0 1) := measurePreserving_eval _ i
  exact (hm.integrable_comp (g := fun x : ℝ => x ^ 2) (by fun_prop)).2 (gaussian_integrable_pow 2)

/-- Auxiliary: each product of two coordinates is integrable. -/
private lemma p8_coord_mul_integrable (n : ℕ) (i j : Fin n) :
    Integrable (fun z : Fin n → ℝ => z i * z j) (stdGaussianPi n) := by
  refine ((((p8_sq_coord_integrable n i).add (p8_sq_coord_integrable n j)).div_const 2)).mono'
    (Continuous.aestronglyMeasurable (by fun_prop))
    (Filter.Eventually.of_forall fun z => ?_)
  show ‖z i * z j‖ ≤ (z i ^ 2 + z j ^ 2) / 2
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|z i| - |z j|), sq_abs (z i), sq_abs (z j)]

/-- Auxiliary: `E[g_i g_j] = δ_ij`. -/
private lemma p8_coord_mul_integral (n : ℕ) (i j : Fin n) :
    ∫ z : Fin n → ℝ, z i * z j ∂(stdGaussianPi n) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have h := integral_map (μ := stdGaussianPi n) (φ := fun z : Fin n → ℝ => z i)
      (f := fun x : ℝ => x ^ 2) (measurable_pi_apply i).aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop))
    rw [stdGaussianPi_map_coord, gaussian_moment_two] at h
    simp only [← pow_two]
    exact h.symm
  · rw [if_neg hij]
    unfold stdGaussianPi
    have hprod : ∀ z : Fin n → ℝ,
        ∏ k, (if k = i ∨ k = j then z k else 1) = z i * z j := by
      intro z
      exact (Finset.prod_eq_mul (f := fun k => if k = i ∨ k = j then z k else 1) i j hij
        (fun c _ hc => by simp [hc.1, hc.2])
        (fun h => absurd (Finset.mem_univ i) h) (fun h => absurd (Finset.mem_univ j) h)).trans
        (by simp)
    have hfun : (fun z : Fin n → ℝ => z i * z j)
        = fun z : Fin n → ℝ => ∏ k, (fun (k : Fin n) (x : ℝ) =>
            if k = i ∨ k = j then x else 1) k (z k) := by
      funext z
      change z i * z j = ∏ k, (if k = i ∨ k = j then z k else 1)
      rw [hprod z]
    have hint : ∀ k : Fin n, ∫ x, (if k = i ∨ k = j then x else 1) ∂(gaussianReal 0 1)
        = if k = i ∨ k = j then 0 else 1 := by
      intro k
      split_ifs
      · simpa using gaussian_moment_odd 0
      · simp
    have h0 : ∏ k : Fin n, (if k = i ∨ k = j then (0 : ℝ) else 1) = 0 :=
      Finset.prod_eq_zero (f := fun k : Fin n => if k = i ∨ k = j then (0 : ℝ) else 1)
        (Finset.mem_univ i) (by simp)
    rw [hfun, integral_fintype_prod_eq_prod
      (f := fun (k : Fin n) (x : ℝ) => if k = i ∨ k = j then x else 1)]
    change ∏ k, ∫ x, (if k = i ∨ k = j then x else 1) ∂(gaussianReal 0 1) = _
    rw [Finset.prod_congr rfl (fun k _ => hint k), h0]

/-- Card P8. Quadratic form mean: `E[gᵀMg] = tr M` for any real matrix `M`. -/
theorem stdGaussianPi_quadratic_mean (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    ∫ z : Fin n → ℝ, ∑ i, ∑ j, z i * M i j * z j ∂(stdGaussianPi n) = M.trace := by
  have e : ∀ z : Fin n → ℝ, ∑ i, ∑ j, z i * M i j * z j
      = ∑ i, ∑ j, M i j * (z i * z j) := by
    intro z
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e]
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
    (p8_coord_mul_integrable n i j).const_mul (M i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ fun j _ => (p8_coord_mul_integrable n i j).const_mul (M i j)]
  simp_rw [integral_const_mul, p8_coord_mul_integral]
  simp [Matrix.trace, Matrix.diag]

/-- Auxiliary: exponent-product form of a monomial in the coordinates. -/
private lemma p8_four_eq_prod (n : ℕ) (i j k l : Fin n) (z : Fin n → ℝ) :
    z i * z j * z k * z l = ∏ c, z c ^ ((if c = i then 1 else 0) + (if c = j then 1 else 0)
      + (if c = k then 1 else 0) + (if c = l then 1 else 0)) := by
  simp only [pow_add, Finset.prod_mul_distrib, pow_ite, pow_one, pow_zero,
    Finset.prod_ite_eq', Finset.mem_univ, if_true]

private lemma p8_four_integrable (n : ℕ) (i j k l : Fin n) :
    Integrable (fun z : Fin n → ℝ => z i * z j * z k * z l) (stdGaussianPi n) := by
  simp_rw [p8_four_eq_prod]
  unfold stdGaussianPi
  exact Integrable.fintype_prod (f := fun (c : Fin n) (x : ℝ) => x ^ ((if c = i then 1 else 0)
    + (if c = j then 1 else 0) + (if c = k then 1 else 0) + (if c = l then 1 else 0)))
    (fun c => gaussian_integrable_pow _)

private lemma p8_four_integral (n : ℕ) (i j k l : Fin n) :
    ∫ z : Fin n → ℝ, z i * z j * z k * z l ∂(stdGaussianPi n)
      = (if i = j then 1 else 0) * (if k = l then 1 else 0)
        + (if i = k then 1 else 0) * (if j = l then 1 else 0)
        + (if i = l then 1 else 0) * (if j = k then 1 else 0) := by
  simp_rw [p8_four_eq_prod]
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

private lemma p8_centered_pair (n : ℕ) (i j k l : Fin n) :
    ∫ z : Fin n → ℝ, (z i * z j - (if i = j then 1 else 0)) * (z k * z l - (if k = l then 1 else 0))
        ∂(stdGaussianPi n)
      = (if i = k then 1 else 0) * (if j = l then 1 else 0)
        + (if i = l then 1 else 0) * (if j = k then 1 else 0) := by
  have e : ∀ z : Fin n → ℝ,
      (z i * z j - (if i = j then (1 : ℝ) else 0)) * (z k * z l - (if k = l then (1 : ℝ) else 0))
      = z i * z j * z k * z l - (if k = l then (1 : ℝ) else 0) * (z i * z j)
        - (if i = j then (1 : ℝ) else 0) * (z k * z l)
        + (if i = j then (1 : ℝ) else 0) * (if k = l then (1 : ℝ) else 0) := by
    intro z; ring
  simp_rw [e]
  rw [integral_add, integral_sub, integral_sub, integral_const_mul, integral_const_mul,
    p8_four_integral, p8_coord_mul_integral, p8_coord_mul_integral]
  · simp only [integral_const]
    split_ifs <;> simp_all
  · exact p8_four_integrable n i j k l
  · exact (p8_coord_mul_integrable n i j).const_mul _
  · exact (p8_four_integrable n i j k l).sub ((p8_coord_mul_integrable n i j).const_mul _)
  · exact (p8_coord_mul_integrable n k l).const_mul _
  · exact ((p8_four_integrable n i j k l).sub ((p8_coord_mul_integrable n i j).const_mul _)).sub
      ((p8_coord_mul_integrable n k l).const_mul _)
  · exact integrable_const _

private lemma p8_centered_integrable (n : ℕ) (i j k l : Fin n) :
    Integrable (fun z : Fin n → ℝ =>
      (z i * z j - (if i = j then 1 else 0)) * (z k * z l - (if k = l then 1 else 0)))
      (stdGaussianPi n) := by
  have e : ∀ z : Fin n → ℝ,
      (z i * z j - (if i = j then (1 : ℝ) else 0)) * (z k * z l - (if k = l then (1 : ℝ) else 0))
      = z i * z j * z k * z l - (if k = l then (1 : ℝ) else 0) * (z i * z j)
        - (if i = j then (1 : ℝ) else 0) * (z k * z l)
        + (if i = j then (1 : ℝ) else 0) * (if k = l then (1 : ℝ) else 0) := by
    intro z; ring
  simp_rw [e]
  exact (((p8_four_integrable n i j k l).sub ((p8_coord_mul_integrable n i j).const_mul _)).sub
      ((p8_coord_mul_integrable n k l).const_mul _)).add (integrable_const _)

/-- Card P8. Quadratic form variance: for symmetric `M`,
`Var(gᵀMg) = 2 tr(M²)`. -/
theorem stdGaussianPi_quadratic_variance (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.transpose = M) :
    ∫ z : Fin n → ℝ, (∑ i, ∑ j, z i * M i j * z j - M.trace) ^ 2 ∂(stdGaussianPi n)
      = 2 * (M * M).trace := by
  have e : ∀ z : Fin n → ℝ, ∑ i, ∑ j, z i * M i j * z j - M.trace
      = ∑ i, ∑ j, M i j * (z i * z j - (if i = j then 1 else 0)) := by
    intro z
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.trace, Matrix.diag]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e, sq, Finset.sum_mul_sum]
  have e2 : ∀ z : Fin n → ℝ, ∑ i, ∑ k, ∑ j, ∑ l, M i j * (z i * z j - (if i = j then 1 else 0))
      * (M k l * (z k * z l - (if k = l then 1 else 0)))
      = ∑ i, ∑ k, ∑ j, ∑ l, (M i j * M k l) *
        ((z i * z j - (if i = j then 1 else 0)) * (z k * z l - (if k = l then 1 else 0))) := by
    intro z
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  simp_rw [e2]
  have hI : ∀ i j k l : Fin n, Integrable (fun z : Fin n → ℝ => (M i j * M k l) *
      ((z i * z j - (if i = j then 1 else 0)) * (z k * z l - (if k = l then 1 else 0))))
      (stdGaussianPi n) := fun i j k l => (p8_centered_integrable n i j k l).const_mul _
  have step : ∀ i j k l : Fin n, ∫ z : Fin n → ℝ, (M i j * M k l) *
      ((z i * z j - (if i = j then 1 else 0)) * (z k * z l - (if k = l then 1 else 0)))
      ∂(stdGaussianPi n) = (M i j * M k l) *
        ((if i = k then 1 else 0) * (if j = l then 1 else 0)
        + (if i = l then 1 else 0) * (if j = k then 1 else 0)) := fun i j k l => by
    rw [integral_const_mul, p8_centered_pair]
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun k _ =>
    integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun l _ => hI i j k l]
  have hs : ∀ i : Fin n, ∫ z : Fin n → ℝ, ∑ k, ∑ j, ∑ l, (M i j * M k l) *
      ((z i * z j - (if i = j then 1 else 0)) * (z k * z l - (if k = l then 1 else 0)))
      ∂(stdGaussianPi n) = ∑ k, ∑ j, ∑ l, (M i j * M k l) *
        ((if i = k then 1 else 0) * (if j = l then 1 else 0)
        + (if i = l then 1 else 0) * (if j = k then 1 else 0)) := by
    intro i
    rw [integral_finset_sum _ fun k _ => integrable_finset_sum _ fun j _ =>
      integrable_finset_sum _ fun l _ => hI i j k l]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finset_sum _ fun j _ => integrable_finset_sum _ fun l _ => hI i j k l]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finset_sum _ fun l _ => hI i j k l]
    exact Finset.sum_congr rfl fun l _ => step i j k l
  simp_rw [hs]
  have hMM : (M * M).trace = ∑ i, ∑ j, M i j * M j i := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [hMM]
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hsym : ∀ i j, M j i = M i j := fun i j => by
    have := congrFun (congrFun hM i) j
    simpa [Matrix.transpose_apply] using this
  simp only [hsym]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', two_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hsym i j]

end GaussianFoundations
