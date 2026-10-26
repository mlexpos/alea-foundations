import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Negative-axis Stieltjes transforms of finite measures on `[0, ∞)`

## Contents
* `negStieltjes ν t = ∫ (x + t)⁻¹ dν` (`S_ν(−t)` in the paper; the same expression as Muon's
  `Muon.Isotropic.isoNegStieltjes`, so the two agree by `rfl`), and the complex transform
  `stieltjes ν z = ∫ (x − z)⁻¹ dν`.
* Basic bounds: integrability, `0 ≤ S_ν(−t) ≤ ν(ℝ)/t`, positivity, antitonicity, continuity,
  `t S_ν(−t) → ν(ℝ)`, and linearity in `ν`.
* **Uniqueness**: finite measures on `[0, ∞)` with equal transforms on `t > 0` are equal (the
  masses are then automatically equal), which generalizes Muon's `lem_app_iso_transforms_ii`.
* **Continuity theorem**: with masses converging, transform convergence on `t > 0` implies weak
  convergence, tested against `BoundedContinuousFunction ℝ ℝ`, and conversely. Also Fatou for the
  first moment, the half-moment corollary, and the probability-measure statement in the exact
  shape of Muon's `lem_app_iso_transforms_i`.
* **Existence / limit theorem** `exists_tendsto_of_tendsto_negStieltjes`, the key new tool: a
  sequence of finite measures on `[0, ∞)` with masses `→ c`, bounded first moments and pointwise
  convergent transforms `→ g` has a weak limit `ν` (the whole sequence converges) with mass `c`,
  support in `[0, ∞)`, transform `g`, and first moment `≤ B`.
* Optional: holomorphy of `stieltjes ν` on `ℂ ∖ [0, ∞)`, its value at `−t`, and the bound
  `‖S_ν(z)‖ ≤ ν(ℝ)/|Im z|`.

## References
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, CUP 2010, §2.4
  (Stieltjes transforms, Theorem 2.4.4).
* P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley 1999, Theorem 5.1
  (Prokhorov), §2 (Portmanteau).
* Mathlib: `MeasureTheory.isCompact_closure_of_isTightMeasureSet` and
  `isCompact_setOfPred_finiteMeasure_mass_eq_compl_isCompact_le` (Prokhorov),
  `MeasureTheory.FiniteMeasure.tendsto_iff_forall_integral_tendsto`.

## Proved prior art to port
`~/Documents/lean/muon/lean/Muon/Isotropic/Measure.lean`, l.79–583 (proved): `resPow_hasDeriv`,
`moment_eq`, `ext_of_moments` (uniqueness from the derivatives `∫ (x + t)^{−k}` and density of
polynomials in `(x + 1)⁻¹` on `[0, ∞]`), `resolvent_integrable`, `tail_bound`, `seq_tight`,
`weak_conv`, `sqrt_tail`, `sqrt_part`. Those are stated for probability measures; the finite-mass
versions here reduce to them by normalizing (`negStieltjes_smul`).

## Interface choices
* `negStieltjes` and Muon's `isoNegStieltjes` are distinct constants with the same body, so they
  agree definitionally, not syntactically: term-mode application (`exact`, or passing a hypothesis)
  unifies them, while `rw` and `simp` need `show` or `unfold` first.
* "Support in `[0, ∞)`" is `ν (Iio 0) = 0`, as in `Muon.Isotropic.IsIsoMeasurePair`.
* Masses are real (`(ν j).real univ`) in convergence hypotheses and `ENNReal.ofReal c` in the
  existence conclusion, matching `IsIsoMeasurePair.mass_out`.
* Weak convergence is the `BoundedContinuousFunction ℝ ℝ` test form used in Muon.
* First moments are Bochner integrals with explicit `Integrable` hypotheses, because a
  non-integrable Bochner integral is `0`.
* The probability-measure theorem `tendsto_of_tendsto_negStieltjes_prob` copies the hypotheses of
  `lem_app_iso_transforms_i` (explicit `IsProbabilityMeasure` arguments) for direct citation; the
  other theorems use instance arguments.
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal

noncomputable section

namespace SpectralFoundations

/-! ## Definitions -/

/-- The negative-axis Stieltjes transform `S_ν(−t) = ∫ (x + t)⁻¹ dν(x)`. -/
def negStieltjes (ν : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ x, (x + t)⁻¹ ∂ν

/-- The complex Stieltjes transform `S_ν(z) = ∫ (x − z)⁻¹ dν(x)`. -/
def stieltjes (ν : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ x, ((x : ℂ) - z)⁻¹ ∂ν

private theorem ae_nonneg_of_Iio (μ : Measure ℝ) (h0 : μ (Iio 0) = 0) : ∀ᵐ x ∂μ, 0 ≤ x := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 ≤ a} = Iio 0 := by ext; simp
  rw [this]; exact h0

private theorem inv_pow_le (t x s : ℝ) (ht : 0 < t) (hx : 0 ≤ x) (hs : t / 2 < s) (n : ℕ) :
    ((x + s) ^ n)⁻¹ ≤ (2 / t) ^ n := by
  have h1 : (x + s)⁻¹ ≤ 2 / t := by
    have h2 : t / 2 ≤ x + s := by linarith
    calc (x + s)⁻¹ ≤ (t / 2)⁻¹ := inv_anti₀ (by positivity) h2
      _ = 2 / t := by rw [inv_div]
  rw [← inv_pow]
  exact pow_le_pow_left₀ (by have : 0 < x + s := by linarith
                             positivity) h1 n

private theorem hasDerivAt_inv_pow_aux (x s : ℝ) (hxs : 0 < x + s) (k : ℕ) :
    HasDerivAt (fun s : ℝ => ((x + s) ^ (k + 1))⁻¹) (-((k : ℝ) + 1) * ((x + s) ^ (k + 2))⁻¹) s := by
  have h1 : HasDerivAt (fun s : ℝ => x + s) 1 s := by simpa using (hasDerivAt_id s).const_add x
  have h2 := HasDerivAt.fun_pow h1 (k + 1)
  have hne : (x + s) ^ (k + 1) ≠ 0 := (pow_pos hxs (k + 1)).ne'
  have h3 := (hasStrictFDerivAt_ringInverse (𝕜 := ℝ) (Units.mk0 _ hne)).hasFDerivAt.comp_hasDerivAt s h2
  convert h3 using 1
  · funext s; simp [Ring.inverse_eq_inv']
  · simp
    field_simp
    ring

private theorem resPow_hasDeriv (μ : Measure ℝ) [IsFiniteMeasure μ] (h0 : μ (Iio 0) = 0)
    (k : ℕ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∫ x, (((x + s) ^ (k + 1))⁻¹) ∂μ)
      (-((k : ℝ) + 1) * ∫ x, (((x + t) ^ (k + 2))⁻¹) ∂μ) t := by
  have hnn := ae_nonneg_of_Iio μ h0
  have hs : Ioi (t / 2) ∈ 𝓝 t := Ioi_mem_nhds (by linarith)
  have hmeas : ∀ s : ℝ, Measurable (fun x : ℝ => ((x + s) ^ (k + 1))⁻¹) := fun s => by fun_prop
  have hmeas' : ∀ s : ℝ, Measurable (fun x : ℝ => -((k : ℝ) + 1) * ((x + s) ^ (k + 2))⁻¹) :=
    fun s => by fun_prop
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := t)
    (F := fun s x => ((x + s) ^ (k + 1))⁻¹)
    (F' := fun s x => -((k : ℝ) + 1) * ((x + s) ^ (k + 2))⁻¹)
    (bound := fun _ => ((k : ℝ) + 1) * (2 / t) ^ (k + 2)) hs
    (Eventually.of_forall fun s => (hmeas s).aestronglyMeasurable)
    (by
      refine Integrable.mono' (integrable_const ((2 / t) ^ (k + 1)))
        (hmeas t).aestronglyMeasurable ?_
      filter_upwards [hnn] with x hx
      have hxt : 0 < x + t := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact inv_pow_le t x t ht hx (by linarith) _)
    (hmeas' t).aestronglyMeasurable
    (by
      filter_upwards [hnn] with x hx s hs'
      have hs'' : t / 2 < s := hs'
      have hxs : 0 < x + s := by linarith
      have := inv_pow_le t x s ht hx hs'' (k + 2)
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ) + 1),
        abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left this (by positivity))
    (integrable_const _)
    (by
      filter_upwards [hnn] with x hx s hs'
      have hs'' : t / 2 < s := hs'
      have hxs : 0 < x + s := by linarith
      exact hasDerivAt_inv_pow_aux x s hxs k)
  have := key.2
  rwa [integral_const_mul] at this

private theorem resPow_eq (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ0 : μ (Iio 0) = 0) (hν0 : ν (Iio 0) = 0)
    (htr : ∀ t : ℝ, 0 < t → ∫ x, (x + t)⁻¹ ∂μ = ∫ x, (x + t)⁻¹ ∂ν) :
    ∀ k : ℕ, ∀ t : ℝ, 0 < t →
      ∫ x, (((x + t) ^ (k + 1))⁻¹) ∂μ = ∫ x, (((x + t) ^ (k + 1))⁻¹) ∂ν := by
  intro k
  induction k with
  | zero => intro t ht; simpa using htr t ht
  | succ k ih =>
    intro t ht
    have h1 := resPow_hasDeriv μ hμ0 k t ht
    have h2 := resPow_hasDeriv ν hν0 k t ht
    have h3 : HasDerivAt (fun s : ℝ => ∫ x, (((x + s) ^ (k + 1))⁻¹) ∂ν)
        (-((k : ℝ) + 1) * ∫ x, (((x + t) ^ (k + 2))⁻¹) ∂μ) t := by
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds ht] with s hs using (ih s hs).symm
    have := h3.unique h2
    have hk : (-((k : ℝ) + 1)) ≠ 0 := by have : (0:ℝ) ≤ k := Nat.cast_nonneg k
                                         linarith
    exact mul_left_cancel₀ hk this

private theorem moment_eq (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ0 : μ (Iio 0) = 0) (hν0 : ν (Iio 0) = 0)
    (hmass : μ univ = ν univ)
    (htr : ∀ t : ℝ, 0 < t → ∫ x, (x + t)⁻¹ ∂μ = ∫ x, (x + t)⁻¹ ∂ν) (n : ℕ) :
    ∫ x, ((1 + x)⁻¹) ^ n ∂μ = ∫ x, ((1 + x)⁻¹) ^ n ∂ν := by
  cases n with
  | zero =>
    simp only [pow_zero, integral_const, smul_eq_mul, mul_one]
    simp [Measure.real, hmass]
  | succ k =>
    have := resPow_eq μ ν hμ0 hν0 htr k 1 one_pos
    simpa [inv_pow, add_comm] using this

private theorem poly_integral_eq (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ0 : μ (Iio 0) = 0) (hν0 : ν (Iio 0) = 0)
    (hmom : ∀ n : ℕ, ∫ x, ((1 + x)⁻¹) ^ n ∂μ = ∫ x, ((1 + x)⁻¹) ^ n ∂ν) (P : Polynomial ℝ) :
    ∫ x, P.eval ((1 + x)⁻¹) ∂μ = ∫ x, P.eval ((1 + x)⁻¹) ∂ν := by
  have hint : ∀ (m : Measure ℝ) [IsFiniteMeasure m], m (Iio 0) = 0 → ∀ i : ℕ,
      Integrable (fun x : ℝ => ((1 + x)⁻¹) ^ i) m := by
    intro m _ hm0 i
    refine Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop : Measurable _).aestronglyMeasurable ?_
    filter_upwards [ae_nonneg_of_Iio m hm0] with x hx
    have h1 : (1 + x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have h2 : 0 ≤ (1 + x)⁻¹ := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h2 _)]
    exact pow_le_one₀ h2 h1
  have key : ∀ (m : Measure ℝ) [IsFiniteMeasure m], m (Iio 0) = 0 →
      ∫ x, P.eval ((1 + x)⁻¹) ∂m =
        ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * ∫ x, ((1 + x)⁻¹) ^ i ∂m := by
    intro m _ hm0
    simp_rw [Polynomial.eval_eq_sum_range]
    rw [integral_finsetSum _ (fun i _ => (hint m hm0 i).const_mul _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
  rw [key μ hμ0, key ν hν0]
  exact Finset.sum_congr rfl fun i _ => by rw [hmom i]


private theorem tendsto_poly_ind (s : ℝ) (hs : 0 ≤ s) (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun k : ℕ => (1 - ((1 + x)⁻¹) ^ k) ^ (⌈(k : ℝ) * (1 + s) ^ k⌉₊))
      atTop (𝓝 ((Ioi s).indicator (fun _ => (1 : ℝ)) x)) := by
  have hx1 : 0 < 1 + x := by linarith
  set y := (1 + x)⁻¹ with hy
  have hy0 : 0 < y := inv_pos.mpr hx1
  have hy1 : y ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hyk0 : ∀ k : ℕ, 0 ≤ y ^ k := fun k => pow_nonneg hy0.le k
  have hyk1 : ∀ k : ℕ, y ^ k ≤ 1 := fun k => pow_le_one₀ hy0.le hy1
  by_cases hxs : s < x
  · rw [Set.indicator_of_mem (mem_Ioi.2 hxs)]
    have hr : y * (1 + s) < 1 := by
      rw [hy, ← div_eq_inv_mul, div_lt_one hx1]; linarith
    have hy1' : y < 1 := by
      have : y ≤ y * (1 + s) := by nlinarith
      linarith
    have h1 : Tendsto (fun k : ℕ => (k : ℝ) * (y * (1 + s)) ^ k) atTop (𝓝 0) :=
      tendsto_self_mul_const_pow_of_lt_one (by positivity) hr
    have h2 : Tendsto (fun k : ℕ => y ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hy0.le hy1'
    have h3 : Tendsto (fun k : ℕ => 1 - ((k : ℝ) * (y * (1 + s)) ^ k + y ^ k)) atTop (𝓝 1) := by
      have := tendsto_const_nhds (x := (1 : ℝ)) |>.sub (h1.add h2)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le h3 tendsto_const_nhds (fun k => ?_) (fun k => ?_)
    · have hb := one_add_mul_le_pow (a := -(y ^ k)) (by linarith [hyk1 k]) (⌈(k : ℝ) * (1 + s) ^ k⌉₊)
      have hM : (⌈(k : ℝ) * (1 + s) ^ k⌉₊ : ℝ) ≤ (k : ℝ) * (1 + s) ^ k + 1 :=
        (Nat.ceil_lt_add_one (by positivity)).le
      have : (⌈(k : ℝ) * (1 + s) ^ k⌉₊ : ℝ) * y ^ k ≤ ((k : ℝ) * (1 + s) ^ k + 1) * y ^ k :=
        mul_le_mul_of_nonneg_right hM (hyk0 k)
      have e : ((k : ℝ) * (1 + s) ^ k + 1) * y ^ k = (k : ℝ) * (y * (1 + s)) ^ k + y ^ k := by
        rw [mul_pow]; ring
      simp only [← sub_eq_add_neg] at hb
      nlinarith
    · exact pow_le_one₀ (by linarith [hyk1 k]) (by linarith [hyk0 k])
  · rw [Set.indicator_of_notMem (by exact hxs)]
    have hxs' : x ≤ s := not_lt.1 hxs
    have hr : 1 ≤ y * (1 + s) := by
      rw [hy, ← div_eq_inv_mul, one_le_div hx1]; linarith
    have hlim : Tendsto (fun k : ℕ => Real.exp (-(k : ℝ))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun k => ?_) (fun k => ?_)
    · exact pow_nonneg (by linarith [hyk1 k]) _
    · have h1 : 1 - y ^ k ≤ Real.exp (-(y ^ k)) := by
        have := Real.add_one_le_exp (-(y ^ k)); linarith
      have h2 : (1 - y ^ k) ^ (⌈(k : ℝ) * (1 + s) ^ k⌉₊)
          ≤ (Real.exp (-(y ^ k))) ^ (⌈(k : ℝ) * (1 + s) ^ k⌉₊) :=
        pow_le_pow_left₀ (by linarith [hyk1 k]) h1 _
      refine h2.trans ?_
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.2
      have hM : (k : ℝ) * (1 + s) ^ k ≤ (⌈(k : ℝ) * (1 + s) ^ k⌉₊ : ℝ) := Nat.le_ceil _
      have h3 : (1 : ℝ) ≤ (y * (1 + s)) ^ k := one_le_pow₀ hr
      have h4 : (k : ℝ) * (y * (1 + s)) ^ k = ((k : ℝ) * (1 + s) ^ k) * y ^ k := by
        rw [mul_pow]; ring
      have h5 : (k : ℝ) ≤ (k : ℝ) * (y * (1 + s)) ^ k := by
        have : (0:ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith
      have h6 : ((k : ℝ) * (1 + s) ^ k) * y ^ k ≤ (⌈(k : ℝ) * (1 + s) ^ k⌉₊ : ℝ) * y ^ k :=
        mul_le_mul_of_nonneg_right hM (hyk0 k)
      nlinarith

private theorem ext_of_moments (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ0 : μ (Iio 0) = 0) (hν0 : ν (Iio 0) = 0)
    (hmom : ∀ n : ℕ, ∫ x, ((1 + x)⁻¹) ^ n ∂μ = ∫ x, ((1 + x)⁻¹) ^ n ∂ν) : μ = ν := by
  have hmass : μ univ = ν univ := by
    have h := hmom 0
    simp only [pow_zero, integral_const, smul_eq_mul, mul_one] at h
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h
  have hlim : ∀ (m : Measure ℝ) [IsFiniteMeasure m], m (Iio 0) = 0 → ∀ s : ℝ, 0 ≤ s →
      Tendsto (fun k : ℕ => ∫ x, (1 - ((1 + x)⁻¹) ^ k) ^ (⌈(k : ℝ) * (1 + s) ^ k⌉₊) ∂m)
        atTop (𝓝 (m.real (Ioi s))) := by
    intro m _ hm s hs
    have h := tendsto_integral_of_dominated_convergence (μ := m)
      (F := fun (k : ℕ) (x : ℝ) => (1 - ((1 + x)⁻¹) ^ k) ^ (⌈(k : ℝ) * (1 + s) ^ k⌉₊))
      (f := (Ioi s).indicator (fun _ => (1 : ℝ))) (bound := fun _ => 1)
      (fun k => (by fun_prop : Measurable _).aestronglyMeasurable) (integrable_const _)
      (fun k => by
        filter_upwards [ae_nonneg_of_Iio m hm] with x hx
        have hx1 : 0 < 1 + x := by linarith
        have hy0 : 0 < (1 + x)⁻¹ := inv_pos.mpr hx1
        have hy1 : (1 + x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
        have h1 : ((1 + x)⁻¹) ^ k ≤ 1 := pow_le_one₀ hy0.le hy1
        have h2 : 0 ≤ ((1 + x)⁻¹) ^ k := pow_nonneg hy0.le k
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by linarith) _)]
        exact pow_le_one₀ (by linarith) (by linarith))
      (by
        filter_upwards [ae_nonneg_of_Iio m hm] with x hx
        exact tendsto_poly_ind s hs x hx)
    rwa [integral_indicator_const (1 : ℝ) measurableSet_Ioi, smul_eq_mul, mul_one] at h
  have htail : ∀ s : ℝ, 0 ≤ s → μ (Ioi s) = ν (Ioi s) := by
    intro s hs
    have h1 := hlim μ hμ0 s hs
    have h2 := hlim ν hν0 s hs
    have heq : ∀ k : ℕ, ∫ x, (1 - ((1 + x)⁻¹) ^ k) ^ (⌈(k : ℝ) * (1 + s) ^ k⌉₊) ∂μ
        = ∫ x, (1 - ((1 + x)⁻¹) ^ k) ^ (⌈(k : ℝ) * (1 + s) ^ k⌉₊) ∂ν := by
      intro k
      have := poly_integral_eq μ ν hμ0 hν0 hmom
        ((1 - Polynomial.X ^ k : Polynomial ℝ) ^ (⌈(k : ℝ) * (1 + s) ^ k⌉₊))
      simpa using this
    simp_rw [heq] at h1
    have := tendsto_nhds_unique h1 h2
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 this
  have hIic : ∀ s : ℝ, μ (Iic s) = ν (Iic s) := by
    intro s
    by_cases hs : 0 ≤ s
    · have e1 := measure_add_measure_compl (μ := μ) (measurableSet_Ioi (a := s))
      have e2 := measure_add_measure_compl (μ := ν) (measurableSet_Ioi (a := s))
      rw [compl_Ioi] at e1 e2
      refine (ENNReal.add_right_inj (measure_ne_top ν (Ioi s))).1 ?_
      calc ν (Ioi s) + μ (Iic s) = μ (Ioi s) + μ (Iic s) := by rw [htail s hs]
        _ = μ univ := e1
        _ = ν univ := hmass
        _ = ν (Ioi s) + ν (Iic s) := e2.symm
    · have hs' : s < 0 := not_le.1 hs
      rw [measure_mono_null (Iic_subset_Iio.2 hs') hμ0, measure_mono_null (Iic_subset_Iio.2 hs') hν0]
  exact Measure.ext_of_Iic μ ν hIic


private theorem resolvent_integrable (m : Measure ℝ) [IsFiniteMeasure m] (h0 : m (Iio 0) = 0)
    (T : ℝ) (hT : 0 < T) : Integrable (fun x : ℝ => (x + T)⁻¹) m := by
  refine Integrable.mono' (integrable_const T⁻¹) (by fun_prop : Measurable _).aestronglyMeasurable ?_
  filter_upwards [ae_nonneg_of_Iio m h0] with x hx
  have h1 : 0 < x + T := by linarith
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h1)]
  exact inv_anti₀ hT (by linarith)

private theorem tail_bound (m : Measure ℝ) [IsProbabilityMeasure m] (h0 : m (Iio 0) = 0)
    (T : ℝ) (hT : 0 < T) :
    (m (Ioi T)).toReal ≤ 2 * (1 - T * ∫ x, (x + T)⁻¹ ∂m) := by
  have hint := resolvent_integrable m h0 T hT
  have e1 : (m (Ioi T)).toReal = ∫ x, (Ioi T).indicator (fun _ => (1:ℝ)) x ∂m := by
    rw [integral_indicator_const (1:ℝ) measurableSet_Ioi]; simp [Measure.real]
  have e2 : ∫ x, 2 * (1 - T * (x + T)⁻¹) ∂m = 2 * (1 - T * ∫ x, (x + T)⁻¹ ∂m) := by
    rw [integral_const_mul, integral_sub (integrable_const _) (hint.const_mul T),
      integral_const_mul]
    simp
  rw [e1, ← e2]
  refine integral_mono_ae ((integrable_const (1:ℝ)).indicator measurableSet_Ioi)
    ((integrable_const _).sub (hint.const_mul T) |>.const_mul 2) ?_
  filter_upwards [ae_nonneg_of_Iio m h0] with x hx
  have h1 : 0 < x + T := by linarith
  have h2 : T * (x + T)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one h1]; linarith
  by_cases hxT : T < x
  · rw [Set.indicator_of_mem (by exact hxT)]
    have : T * (x + T)⁻¹ ≤ 1 / 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ h1]; linarith
    linarith
  · rw [Set.indicator_of_notMem (by exact hxT)]
    linarith

private theorem tail_small (m : Measure ℝ) [IsProbabilityMeasure m] (h0 : m (Iio 0) = 0) :
    Tendsto (fun T : ℝ => 1 - T * ∫ x, (x + T)⁻¹ ∂m) atTop (𝓝 0) := by
  have hlim : Tendsto (fun T : ℝ => ∫ x, x / (x + T) ∂m) atTop (𝓝 (∫ _x : ℝ, (0:ℝ) ∂m)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1:ℝ)) ?_ ?_
      (integrable_const _) ?_
    · exact Eventually.of_forall fun T => (by fun_prop : Measurable _).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop 0] with T hT
      filter_upwards [ae_nonneg_of_Iio m h0] with x hx
      have h1 : 0 < x + T := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hx h1.le), div_le_one h1]
      linarith
    · filter_upwards with x
      exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ _ tendsto_id)
  simp only [integral_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hint := resolvent_integrable m h0 T hT
  have : ∫ x, x / (x + T) ∂m = ∫ x, (1 - T * (x + T)⁻¹) ∂m := by
    refine integral_congr_ae ?_
    filter_upwards [ae_nonneg_of_Iio m h0] with x hx
    have h1 : 0 < x + T := by linarith
    field_simp
    ring
  rw [this, integral_sub (integrable_const _) (hint.const_mul T), integral_const_mul]
  simp

private theorem seq_tight (ν : ℕ → Measure ℝ) (ν₀ : Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (ν j)) (hsupp : ∀ j, ν j (Iio 0) = 0)
    (hprob₀ : IsProbabilityMeasure ν₀) (hsupp₀ : ν₀ (Iio 0) = 0)
    (hconv : ∀ t : ℝ, 0 < t →
      Tendsto (fun j => ∫ x, (x + t)⁻¹ ∂(ν j)) atTop (𝓝 (∫ x, (x + t)⁻¹ ∂ν₀))) :
    ∀ ε : ENNReal, 0 < ε → ∃ K : Set ℝ, IsCompact K ∧ ∀ j, ν j Kᶜ ≤ ε := by
  intro ε hε
  by_cases hεt : ε = ⊤
  · exact ⟨∅, isCompact_empty, fun j => by simp [hεt]⟩
  have hδ : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
  set δ := ε.toReal with hδdef
  obtain ⟨T, hT1, hT0⟩ := ((tail_small ν₀ hsupp₀).eventually
      (eventually_lt_nhds (show (0:ℝ) < δ / 4 by positivity))).and
      (eventually_gt_atTop (0:ℝ)) |>.exists
  obtain ⟨J, hJ⟩ := eventually_atTop.1
    ((tendsto_const_nhds.sub ((hconv T hT0).const_mul T)).eventually
      (eventually_lt_nhds (show 1 - T * ∫ x, (x + T)⁻¹ ∂ν₀ < δ / 2 by linarith)))
  have hK : ∀ j, ∃ K : Set ℝ, IsCompact K ∧ ν j Kᶜ ≤ ε := by
    intro j
    have := hprob j
    obtain ⟨K, hK, h⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1
      (isTightMeasureSet_singleton (μ := ν j)) ε hε
    exact ⟨K, hK, h _ rfl⟩
  choose Kj hKj using hK
  refine ⟨Icc 0 T ∪ ⋃ j ∈ Finset.range J, Kj j, isCompact_Icc.union
    (Finset.isCompact_biUnion _ fun j _ => (hKj j).1), fun j => ?_⟩
  by_cases hj : j < J
  · refine le_trans (measure_mono ?_) (hKj j).2
    intro x hx hx'
    exact hx (Or.inr (mem_biUnion (Finset.mem_range.2 hj) hx'))
  · have := hprob j
    have hb := tail_bound (ν j) (hsupp j) T hT0
    have hj' := hJ j (not_lt.1 hj)
    have h3 : (ν j (Ioi T)).toReal ≤ δ := by
      linarith
    refine le_trans (measure_mono ?_) (le_trans (measure_union_le (Iio 0) (Ioi T)) ?_)
    · intro x hx
      by_contra hxn
      simp only [mem_union, mem_Iio, mem_Ioi, not_or, not_lt] at hxn
      exact hx (Or.inl ⟨hxn.1, hxn.2⟩)
    · rw [hsupp j, zero_add, ← ENNReal.ofReal_toReal (measure_ne_top (ν j) (Ioi T)),
        ← ENNReal.ofReal_toReal hεt]
      exact ENNReal.ofReal_le_ofReal h3

private theorem weak_conv (ν : ℕ → Measure ℝ) (ν₀ : Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (ν j)) (hsupp : ∀ j, ν j (Iio 0) = 0)
    (hprob₀ : IsProbabilityMeasure ν₀) (hsupp₀ : ν₀ (Iio 0) = 0)
    (hconv : ∀ t : ℝ, 0 < t →
      Tendsto (fun j => ∫ x, (x + t)⁻¹ ∂(ν j)) atTop (𝓝 (∫ x, (x + t)⁻¹ ∂ν₀))) :
    ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun j => ∫ x, f x ∂(ν j)) atTop (𝓝 (∫ x, f x ∂ν₀)) := by
  let P : ℕ → ProbabilityMeasure ℝ := fun j => ⟨ν j, hprob j⟩
  let P₀ : ProbabilityMeasure ℝ := ⟨ν₀, hprob₀⟩
  have hP : Tendsto P atTop (𝓝 P₀) := by
    refine tendsto_of_subseq_tendsto fun ns hns => ?_
    have htight : IsTightMeasureSet
        {((μ : ProbabilityMeasure ℝ) : Measure ℝ) | μ ∈ Set.range P} := by
      rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
      intro ε hε
      obtain ⟨K, hK, h⟩ := seq_tight ν ν₀ hprob hsupp hprob₀ hsupp₀ hconv ε hε
      refine ⟨K, hK, ?_⟩
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      exact h j
    have hcomp : IsCompact (closure (Set.range P)) := isCompact_closure_of_isTightMeasureSet htight
    obtain ⟨a, -, φ, hφ, hlim⟩ := hcomp.tendsto_subseq (x := P ∘ ns)
      (fun n => subset_closure ⟨ns n, rfl⟩)
    refine ⟨φ, ?_⟩
    suffices ha : a = P₀ by rw [← ha]; exact hlim
    have ha0 : (a : Measure ℝ) (Iio 0) = 0 := by
      have h := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim (G := Iio (0:ℝ)) isOpen_Iio
      have : (fun n => (((P ∘ ns) ∘ φ) n : Measure ℝ) (Iio 0)) = fun _ => 0 :=
        funext fun n => hsupp _
      rw [this, liminf_const] at h
      exact le_antisymm h (zero_le)
    have htr : ∀ t : ℝ, 0 < t → ∫ x, (x + t)⁻¹ ∂(a : Measure ℝ) = ∫ x, (x + t)⁻¹ ∂ν₀ := by
      intro t ht
      obtain ⟨h, hh⟩ : ∃ h : BoundedContinuousFunction ℝ ℝ, ∀ x, h x = (max x 0 + t)⁻¹ := by
        refine ⟨BoundedContinuousFunction.mkOfBound ⟨fun x => (max x 0 + t)⁻¹, ?_⟩ t⁻¹ ?_,
          fun _ => rfl⟩
        · exact Continuous.inv₀ (by fun_prop) (fun x => by
            have := le_max_right x 0; linarith)
        · intro x y
          have hx : (max x 0 + t)⁻¹ ≤ t⁻¹ := inv_anti₀ ht (by have := le_max_right x 0; linarith)
          have hy : (max y 0 + t)⁻¹ ≤ t⁻¹ := inv_anti₀ ht (by have := le_max_right y 0; linarith)
          have hx0 : 0 ≤ (max x 0 + t)⁻¹ := inv_nonneg.mpr (by have := le_max_right x 0; linarith)
          have hy0 : 0 ≤ (max y 0 + t)⁻¹ := inv_nonneg.mpr (by have := le_max_right y 0; linarith)
          simp only [ContinuousMap.coe_mk, Real.dist_eq]
          rw [abs_le]; constructor <;> linarith
      have hae : ∀ m : Measure ℝ, m (Iio 0) = 0 →
          ∫ x, h x ∂m = ∫ x, (x + t)⁻¹ ∂m := by
        intro m hm
        refine integral_congr_ae ?_
        filter_upwards [ae_nonneg_of_Iio m hm] with x hx
        rw [hh, max_eq_left hx]
      have h1 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim) h
      have h2 : Tendsto (fun n => ∫ x, h x ∂(((P ∘ ns) ∘ φ) n : Measure ℝ)) atTop
          (𝓝 (∫ x, (x + t)⁻¹ ∂ν₀)) := by
        have := (hconv t ht).comp (hns.comp hφ.tendsto_atTop)
        refine this.congr fun n => ?_
        exact (hae _ (hsupp _)).symm
      rw [← hae _ ha0, ← hae _ hsupp₀]
      have h2' : Tendsto (fun n => ∫ x, h x ∂(((P ∘ ns) ∘ φ) n : Measure ℝ)) atTop
          (𝓝 (∫ x, h x ∂ν₀)) := by rw [hae _ hsupp₀]; exact h2
      exact tendsto_nhds_unique h1 h2'
    have := a.prop
    exact Subtype.ext (ext_of_moments (a : Measure ℝ) ν₀ ha0 hsupp₀
      (moment_eq (a : Measure ℝ) ν₀ ha0 hsupp₀ (by simp) htr))
  intro f
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hP f

private theorem sqrt_tail (m : Measure ℝ) [IsFiniteMeasure m] (h0 : m (Iio 0) = 0)
    (hint : Integrable (fun x : ℝ => x) m) (K : ℝ) (hK : 0 < K) :
    Integrable (fun x : ℝ => Real.sqrt x) m ∧
    |∫ x, Real.sqrt x ∂m - ∫ x, min (Real.sqrt x) K ∂m| ≤ (∫ x, x ∂m) / K := by
  have hsq : Integrable (fun x : ℝ => Real.sqrt x) m := by
    refine Integrable.mono' (hint.add (integrable_const (1:ℝ)))
      Real.continuous_sqrt.measurable.aestronglyMeasurable ?_
    filter_upwards [ae_nonneg_of_Iio m h0] with x hx
    have h1 := Real.sq_sqrt hx
    have h2 := Real.sqrt_nonneg x
    rw [Real.norm_eq_abs, abs_of_nonneg h2]
    show Real.sqrt x ≤ x + 1
    nlinarith [sq_nonneg (Real.sqrt x - 1)]
  have hmin : Integrable (fun x : ℝ => min (Real.sqrt x) K) m := by
    refine Integrable.mono' (integrable_const K)
      (Real.continuous_sqrt.measurable.min measurable_const).aestronglyMeasurable ?_
    filter_upwards with x
    have h2 := Real.sqrt_nonneg x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min h2 hK.le)]
    exact min_le_right _ _
  refine ⟨hsq, ?_⟩
  rw [← integral_sub hsq hmin]
  have hnn : 0 ≤ᵐ[m] fun x => Real.sqrt x - min (Real.sqrt x) K := by
    filter_upwards with x using sub_nonneg.2 (min_le_left _ _)
  rw [abs_of_nonneg (integral_nonneg_of_ae hnn), ← integral_div]
  refine integral_mono_ae (hsq.sub hmin) (hint.div_const K) ?_
  filter_upwards [ae_nonneg_of_Iio m h0] with x hx
  have h1 := Real.sq_sqrt hx
  have h2 := Real.sqrt_nonneg x
  rw [le_div_iff₀ hK]
  by_cases hs : Real.sqrt x ≤ K
  · rw [min_eq_left hs]; simp; positivity
  · rw [not_le] at hs
    rw [min_eq_right hs.le]
    nlinarith

private theorem sqrt_part (ν : ℕ → Measure ℝ) (ν₀ : Measure ℝ)
    [∀ j, IsFiniteMeasure (ν j)] [IsFiniteMeasure ν₀] (hsupp : ∀ j, ν j (Iio 0) = 0)
    (hsupp₀ : ν₀ (Iio 0) = 0)
    (hweak : ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun j => ∫ x, f x ∂(ν j)) atTop (𝓝 (∫ x, f x ∂ν₀)))
    (hint : ∀ j, Integrable (fun x : ℝ => x) (ν j)) (hint₀ : Integrable (fun x : ℝ => x) ν₀)
    (hbdd : BddAbove (Set.range fun j => ∫ x, x ∂(ν j))) :
    Tendsto (fun j => ∫ x, Real.sqrt x ∂(ν j)) atTop (𝓝 (∫ x, Real.sqrt x ∂ν₀)) := by
  obtain ⟨C, hC⟩ := hbdd
  set B := max C (∫ x, x ∂ν₀) with hB
  have hBj : ∀ j, ∫ x, x ∂(ν j) ≤ B := fun j => (hC ⟨j, rfl⟩).trans (le_max_left _ _)
  have hB0 : ∫ x, x ∂ν₀ ≤ B := le_max_right _ _
  have hBpos : 0 ≤ B := by
    refine le_trans ?_ hB0
    exact integral_nonneg_of_ae (by
      filter_upwards [ae_nonneg_of_Iio ν₀ hsupp₀] with x hx using hx)
  rw [Metric.tendsto_atTop]
  intro ε hε
  set K := 3 * (B + 1) / ε with hKdef
  have hK : 0 < K := by positivity
  have hBK : B / K < ε / 3 := by
    rw [div_lt_iff₀ hK, hKdef]
    field_simp
    nlinarith
  obtain ⟨f, hf⟩ : ∃ f : BoundedContinuousFunction ℝ ℝ, ∀ x, f x = min (Real.sqrt x) K := by
    refine ⟨BoundedContinuousFunction.mkOfBound
      ⟨fun x => min (Real.sqrt x) K, Real.continuous_sqrt.min continuous_const⟩ K ?_,
      fun _ => rfl⟩
    intro x y
    have hx := Real.sqrt_nonneg x
    have hy := Real.sqrt_nonneg y
    have a1 : min (Real.sqrt x) K ≤ K := min_le_right _ _
    have a2 : min (Real.sqrt y) K ≤ K := min_le_right _ _
    have b1 : 0 ≤ min (Real.sqrt x) K := le_min hx hK.le
    have b2 : 0 ≤ min (Real.sqrt y) K := le_min hy hK.le
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    rw [abs_le]; constructor <;> linarith
  have hfun : (fun x => f x) = fun x => min (Real.sqrt x) K := funext hf
  have hw := hweak f
  simp_rw [hf] at hw
  rw [Metric.tendsto_atTop] at hw
  obtain ⟨N, hN⟩ := hw (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := (sqrt_tail (ν n) (hsupp n) (hint n) K hK).2
  have h2 := (sqrt_tail ν₀ hsupp₀ hint₀ K hK).2
  have h3 := hN n hn
  rw [Real.dist_eq] at h3 ⊢
  have e1 : (∫ x, x ∂(ν n)) / K ≤ B / K := div_le_div_of_nonneg_right (hBj n) hK.le
  have e2 : (∫ x, x ∂ν₀) / K ≤ B / K := div_le_div_of_nonneg_right hB0 hK.le
  rw [abs_le] at h1 h2
  rw [abs_lt] at h3 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]


/-! ## Basic properties -/

section Basic

variable {ν : Measure ℝ}

/-- `(x + t)⁻¹` is integrable for a finite measure on `[0, ∞)` and `t > 0`.
Proof route: Muon `resolvent_integrable`: `Integrable.mono'` with the constant `1/t`, using
`ν`-a.e. `0 ≤ x` (from `ν (Iio 0) = 0`). -/
theorem integrable_inv_add [IsFiniteMeasure ν] (hν : ν (Iio 0) = 0) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => (x + t)⁻¹) ν := by
  exact resolvent_integrable ν hν t ht

/-- `0 ≤ S_ν(−t)` (no finiteness needed).
Proof route: `integral_nonneg_of_ae` with a.e. `0 ≤ x`. -/
theorem negStieltjes_nonneg (hν : ν (Iio 0) = 0) {t : ℝ} (ht : 0 < t) : 0 ≤ negStieltjes ν t := by
  unfold negStieltjes
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_nonneg_of_Iio ν hν] with x hx
  exact inv_nonneg.mpr (by linarith)

/-- `S_ν(−t) ≤ ν(ℝ)/t`.
Proof route: `integral_mono_ae` against the constant `t⁻¹`, `integral_const`, `measureReal_def`. -/
theorem negStieltjes_le [IsFiniteMeasure ν] (hν : ν (Iio 0) = 0) {t : ℝ} (ht : 0 < t) :
    negStieltjes ν t ≤ ν.real univ / t := by
  unfold negStieltjes
  have hint := integrable_inv_add hν ht
  calc ∫ x, (x + t)⁻¹ ∂ν ≤ ∫ _x : ℝ, t⁻¹ ∂ν := by
        refine integral_mono_ae hint (integrable_const _) ?_
        filter_upwards [ae_nonneg_of_Iio ν hν] with x hx
        exact inv_anti₀ ht (by linarith)
    _ = ν.real univ / t := by rw [integral_const, smul_eq_mul, div_eq_mul_inv]

/-- `S_ν(−t) > 0` for a nonzero finite measure on `[0, ∞)`.
Proof route: Muon `m_neg_pos`: `integral_pos_iff_support_of_nonneg_ae`, the support of
`(x + t)⁻¹` contains `[0, ∞)`, which has full measure. -/
theorem negStieltjes_pos [IsFiniteMeasure ν] (hν : ν (Iio 0) = 0) (hν0 : ν univ ≠ 0) {t : ℝ}
    (ht : 0 < t) : 0 < negStieltjes ν t := by
  have hint := integrable_inv_add hν ht
  have hpos : (0 : ℝ≥0∞) < ν univ := pos_iff_ne_zero.2 hν0
  unfold negStieltjes
  rw [integral_pos_iff_support_of_nonneg_ae _ hint]
  · have h2 : ν univ ≤ ν (Ici 0) := by
      have := measure_union_le (μ := ν) (Iio 0) (Ici 0)
      rw [Set.Iio_union_Ici, hν, zero_add] at this
      exact this
    refine lt_of_lt_of_le hpos (h2.trans (measure_mono ?_))
    intro x hx
    have hx' : (0 : ℝ) ≤ x := hx
    simp only [Function.mem_support]
    exact inv_ne_zero (by linarith)
  · filter_upwards [ae_nonneg_of_Iio ν hν] with x hx
    exact inv_nonneg.mpr (by linarith)

/-- `t ↦ S_ν(−t)` is antitone on `(0, ∞)`.
Proof route: `integral_mono_ae` with `inv_anti₀` pointwise on `x ≥ 0`. -/
theorem antitoneOn_negStieltjes [IsFiniteMeasure ν] (hν : ν (Iio 0) = 0) :
    AntitoneOn (negStieltjes ν) (Ioi 0) := by
  intro s hs t ht hst
  have hs' : (0 : ℝ) < s := hs
  have ht' : (0 : ℝ) < t := ht
  unfold negStieltjes
  refine integral_mono_ae (integrable_inv_add hν ht') (integrable_inv_add hν hs') ?_
  filter_upwards [ae_nonneg_of_Iio ν hν] with x hx
  exact inv_anti₀ (by linarith) (by linarith)

/-- `t ↦ S_ν(−t)` is continuous on `(0, ∞)`.
Proof route: `continuousOn_of_dominated` (dominated convergence) with the bound `2/t₀` near
`t₀`, or Muon `resPow_hasDeriv` (`k = 0`) for differentiability. -/
theorem continuousOn_negStieltjes [IsFiniteMeasure ν] (hν : ν (Iio 0) = 0) :
    ContinuousOn (negStieltjes ν) (Ioi 0) := by
  intro t0 ht0
  have ht0' : (0 : ℝ) < t0 := ht0
  apply ContinuousAt.continuousWithinAt
  unfold negStieltjes
  refine continuousAt_of_dominated (bound := fun _ => (t0 / 2)⁻¹) ?_ ?_ (integrable_const _) ?_
  · filter_upwards with t
    exact (by fun_prop : Measurable fun x : ℝ => (x + t)⁻¹).aestronglyMeasurable
  · filter_upwards [Ioi_mem_nhds (show t0 / 2 < t0 by linarith)] with t ht
    have ht2 : t0 / 2 < t := ht
    filter_upwards [ae_nonneg_of_Iio ν hν] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by linarith))]
    exact inv_anti₀ (by positivity) (by linarith)
  · filter_upwards [ae_nonneg_of_Iio ν hν] with x hx
    exact (continuousAt_const.add continuousAt_id).inv₀ (by simp; linarith)

/-- Mass recovery: `t S_ν(−t) → ν(ℝ)` as `t → ∞`.
Proof route: `t S_ν(−t) = ∫ t/(x + t) dν` for `t > 0`; dominated convergence
(`tendsto_integral_filter_of_dominated_convergence`) with bound `1` on `x ≥ 0` and pointwise limit
`1`; `integral_const`. -/
theorem tendsto_mul_negStieltjes_atTop [IsFiniteMeasure ν] (hν : ν (Iio 0) = 0) :
    Tendsto (fun t => t * negStieltjes ν t) atTop (𝓝 (ν.real univ)) := by
  have hlim : Tendsto (fun t : ℝ => ∫ x, t * (x + t)⁻¹ ∂ν) atTop (𝓝 (∫ _x : ℝ, (1 : ℝ) ∂ν)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_
      (integrable_const _) ?_
    · exact Eventually.of_forall fun t =>
        (by fun_prop : Measurable fun x : ℝ => t * (x + t)⁻¹).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop 0] with t ht
      filter_upwards [ae_nonneg_of_Iio ν hν] with x hx
      have h1 : 0 < x + t := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← div_eq_mul_inv, div_le_one h1]
      linarith
    · filter_upwards [ae_nonneg_of_Iio ν hν] with x hx
      have h : Tendsto (fun t : ℝ => (1 + x * t⁻¹)⁻¹) atTop (𝓝 1) := by
        have h0 := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul x
        have := ((tendsto_const_nhds (x := (1 : ℝ))).add h0).inv₀ (by simp)
        simpa using this
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      have h1 : 0 < x + t := by linarith
      field_simp
      ring
  have hconst : (∫ _x : ℝ, (1 : ℝ) ∂ν) = ν.real univ := by simp
  rw [hconst] at hlim
  refine hlim.congr' ?_
  filter_upwards with t
  unfold negStieltjes
  exact integral_const_mul t _

/-- Scaling: `S_{c • ν} = c.toReal · S_ν`. -/
theorem negStieltjes_smul (c : ℝ≥0∞) (ν : Measure ℝ) (t : ℝ) :
    negStieltjes (c • ν) t = c.toReal * negStieltjes ν t := by
  rw [negStieltjes, negStieltjes, integral_smul_measure, smul_eq_mul]

/-- Additivity for finite measures on `[0, ∞)`.
Proof route: `integral_add_measure` with `integrable_inv_add` for both measures. -/
theorem negStieltjes_add {μ : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (Iio 0) = 0) (hν : ν (Iio 0) = 0) {t : ℝ} (ht : 0 < t) :
    negStieltjes (μ + ν) t = negStieltjes μ t + negStieltjes ν t := by
  unfold negStieltjes
  exact integral_add_measure (integrable_inv_add hμ ht) (integrable_inv_add hν ht)

/-- The transform of a point mass. -/
theorem negStieltjes_dirac (a t : ℝ) : negStieltjes (Measure.dirac a) t = (a + t)⁻¹ := by
  rw [negStieltjes, integral_dirac]

end Basic

/-! ## Uniqueness -/

/-- **Uniqueness**: two finite measures on `[0, ∞)` with equal transforms at every `−t`, `t > 0`,
are equal. Masses need not be assumed; they are recovered by `tendsto_mul_negStieltjes_atTop`.
Proof route: equal masses from `tendsto_mul_negStieltjes_atTop` and `tendsto_nhds_unique`; then
port Muon `lem_app_iso_transforms_ii`: `resPow_hasDeriv` shows the `k`-th derivatives
`∫ (x + t)^{−(k+1)}` agree (`moment_eq`), so `∫ p((x + 1)⁻¹)` agree for all polynomials `p`
(`poly_integral_eq`), and Stone–Weierstrass on `[0, 1]` plus `ext_of_measure_eq`-type uniqueness
of the push-forward under `x ↦ (x + 1)⁻¹` (`ext_of_moments`) gives `μ = ν`. -/
theorem eq_of_negStieltjes_eq {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (Iio 0) = 0) (hν : ν (Iio 0) = 0)
    (htr : ∀ t : ℝ, 0 < t → negStieltjes μ t = negStieltjes ν t) : μ = ν := by
  have hmass : μ univ = ν univ := by
    have h1 := tendsto_mul_negStieltjes_atTop (ν := μ) hμ
    have h2 := tendsto_mul_negStieltjes_atTop (ν := ν) hν
    have h2' : Tendsto (fun t => t * negStieltjes μ t) atTop (𝓝 (ν.real univ)) := by
      refine h2.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      rw [htr t ht]
    have := tendsto_nhds_unique h1 h2'
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 this
  exact ext_of_moments μ ν hμ hν
    (moment_eq μ ν hμ hν hmass (fun t ht => by simpa [negStieltjes] using htr t ht))

/-- Uniqueness in the exact hypothesis shape of Muon's `lem_app_iso_transforms_ii`. -/
theorem eq_of_negStieltjes_eq_of_mass {μ ν : Measure ℝ} (hμ : IsFiniteMeasure μ)
    (hν : IsFiniteMeasure ν) (hμ0 : μ (Iio 0) = 0) (hν0 : ν (Iio 0) = 0)
    (_hmass : μ univ = ν univ)
    (htr : ∀ t : ℝ, 0 < t → negStieltjes μ t = negStieltjes ν t) : μ = ν :=
  eq_of_negStieltjes_eq hμ0 hν0 htr

/-! ## Weak convergence and transforms -/

private theorem exists_bcf_resolvent {t : ℝ} (ht : 0 < t) :
    ∃ h : BoundedContinuousFunction ℝ ℝ, ∀ x, h x = (max x 0 + t)⁻¹ := by
  refine ⟨BoundedContinuousFunction.mkOfBound ⟨fun x => (max x 0 + t)⁻¹, ?_⟩ t⁻¹ ?_,
    fun _ => rfl⟩
  · exact Continuous.inv₀ (by fun_prop) (fun x => by
      have := le_max_right x 0; linarith)
  · intro x y
    have hx : (max x 0 + t)⁻¹ ≤ t⁻¹ := inv_anti₀ ht (by have := le_max_right x 0; linarith)
    have hy : (max y 0 + t)⁻¹ ≤ t⁻¹ := inv_anti₀ ht (by have := le_max_right y 0; linarith)
    have hx0 : 0 ≤ (max x 0 + t)⁻¹ := inv_nonneg.mpr (by have := le_max_right x 0; linarith)
    have hy0 : 0 ≤ (max y 0 + t)⁻¹ := inv_nonneg.mpr (by have := le_max_right y 0; linarith)
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    rw [abs_le]; constructor <;> linarith

private theorem integral_bcf_resolvent {t : ℝ} (h : BoundedContinuousFunction ℝ ℝ)
    (hh : ∀ x, h x = (max x 0 + t)⁻¹) (m : Measure ℝ) (hm : m (Iio 0) = 0) :
    ∫ x, h x ∂m = ∫ x, (x + t)⁻¹ ∂m := by
  refine integral_congr_ae ?_
  filter_upwards [ae_nonneg_of_Iio m hm] with x hx
  rw [hh, max_eq_left hx]

/-- Weak convergence implies transform convergence (finite measures on `[0, ∞)`, `t > 0`).
Proof route: test against the bounded continuous `x ↦ (max x 0 + t)⁻¹` (bounded by `1/t`), which
equals `(x + t)⁻¹` on `[0, ∞)`, hence a.e. for every measure in sight (`integral_congr_ae`). -/
theorem tendsto_negStieltjes_of_tendsto_integral (ν : ℕ → Measure ℝ) (ν₀ : Measure ℝ)
    [∀ j, IsFiniteMeasure (ν j)] [IsFiniteMeasure ν₀]
    (hsupp : ∀ j, ν j (Iio 0) = 0) (hsupp₀ : ν₀ (Iio 0) = 0)
    (hweak : ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun j => ∫ x, f x ∂(ν j)) atTop (𝓝 (∫ x, f x ∂ν₀)))
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun j => negStieltjes (ν j) t) atTop (𝓝 (negStieltjes ν₀ t)) := by
  obtain ⟨h, hh⟩ := exists_bcf_resolvent ht
  have key := hweak h
  simp only [negStieltjes]
  rw [← integral_bcf_resolvent h hh ν₀ hsupp₀]
  exact key.congr (fun j => integral_bcf_resolvent h hh (ν j) (hsupp j))

private def normM (ν : Measure ℝ) : Measure ℝ := (ν univ)⁻¹ • ν

private theorem integral_normM (ν : Measure ℝ) (f : ℝ → ℝ) :
    ∫ x, f x ∂(normM ν) = (ν.real univ)⁻¹ * ∫ x, f x ∂ν := by
  unfold normM
  rw [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]; rfl

private theorem isProb_normM (ν : Measure ℝ) [IsFiniteMeasure ν] (h : ν univ ≠ 0) :
    IsProbabilityMeasure (normM ν) :=
  ⟨by simp [normM, Measure.smul_apply, ENNReal.inv_mul_cancel h (measure_ne_top _ _)]⟩

private theorem normM_Iio (ν : Measure ℝ) (h : ν (Iio 0) = 0) : normM ν (Iio 0) = 0 := by
  simp [normM, h]

private theorem negStieltjes_normM (ν : Measure ℝ) (t : ℝ) :
    negStieltjes (normM ν) t = (ν.real univ)⁻¹ * negStieltjes ν t := by
  unfold normM; rw [negStieltjes_smul, ENNReal.toReal_inv]; rfl

private theorem tendsto_integral_of_mass_zero (ν : ℕ → Measure ℝ) [∀ j, IsFiniteMeasure (ν j)]
    (hmass : Tendsto (fun j => (ν j).real univ) atTop (𝓝 0))
    (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun j => ∫ x, f x ∂(ν j)) atTop (𝓝 0) := by
  refine squeeze_zero_norm (a := fun j => ‖f‖ * (ν j).real univ) (fun j => ?_) ?_
  · exact norm_integral_le_of_norm_le_const (Eventually.of_forall fun x => f.norm_coe_le_norm x)
  · simpa using hmass.const_mul ‖f‖

/-- **Continuity theorem** (finite measures): if the masses converge to that of `ν₀` and the
transforms converge on `t > 0`, then `ν j → ν₀` weakly. Mass convergence is necessary
(`δ_j → 0` has transforms `→ 0`).
Proof route: if `ν₀ = 0`, `|∫ f dν j| ≤ ‖f‖ ν_j(ℝ) → 0`. Otherwise normalize by the masses
(`negStieltjes_smul`; eventually positive) and apply Muon `weak_conv` (probability case: the
transforms give tightness, `seq_tight`; every weak subsequential limit (Prokhorov) has the
transform of `ν₀` by `tendsto_negStieltjes_of_tendsto_integral`, hence equals `ν₀` by
`eq_of_negStieltjes_eq`); rescale back. -/
theorem tendsto_integral_of_tendsto_negStieltjes (ν : ℕ → Measure ℝ) (ν₀ : Measure ℝ)
    [∀ j, IsFiniteMeasure (ν j)] [IsFiniteMeasure ν₀]
    (hsupp : ∀ j, ν j (Iio 0) = 0) (hsupp₀ : ν₀ (Iio 0) = 0)
    (hmass : Tendsto (fun j => (ν j).real univ) atTop (𝓝 (ν₀.real univ)))
    (hconv : ∀ t : ℝ, 0 < t →
      Tendsto (fun j => negStieltjes (ν j) t) atTop (𝓝 (negStieltjes ν₀ t))) :
    ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun j => ∫ x, f x ∂(ν j)) atTop (𝓝 (∫ x, f x ∂ν₀)) := by
  intro f
  by_cases h0 : ν₀ univ = 0
  · have hz : ν₀ = 0 := Measure.measure_univ_eq_zero.1 h0
    have hm0 : ν₀.real univ = 0 := by simp [Measure.real, h0]
    rw [hm0] at hmass
    rw [hz, integral_zero_measure]
    exact tendsto_integral_of_mass_zero ν hmass f
  · have hpos : 0 < ν₀.real univ := ENNReal.toReal_pos h0 (measure_ne_top _ _)
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hmass.eventually (eventually_gt_nhds hpos))
    have hposj : ∀ j, 0 < (ν (j + N)).real univ := fun j => hN (j + N) (by omega)
    have hne : ∀ j, ν (j + N) univ ≠ 0 := fun j h => by
      have := hposj j
      simp [Measure.real, h] at this
    have : ∀ j, IsProbabilityMeasure (normM (ν (j + N))) := fun j => isProb_normM _ (hne j)
    have : IsProbabilityMeasure (normM ν₀) := isProb_normM _ h0
    have hmass' : Tendsto (fun j => (ν (j + N)).real univ) atTop (𝓝 (ν₀.real univ)) :=
      hmass.comp (tendsto_add_atTop_nat N)
    have hw := weak_conv (fun j => normM (ν (j + N))) (normM ν₀) inferInstance
      (fun j => normM_Iio _ (hsupp _)) inferInstance (normM_Iio _ hsupp₀) (fun t ht => by
        have e : ∀ m : Measure ℝ, ∫ x, (x + t)⁻¹ ∂(normM m)
            = (m.real univ)⁻¹ * negStieltjes m t := fun m =>
          integral_normM m (fun x => (x + t)⁻¹)
        simp only [e]
        exact (hmass'.inv₀ hpos.ne').mul ((hconv t ht).comp (tendsto_add_atTop_nat N)))
    have hw' := hw f
    simp only [integral_normM] at hw'
    have hprod := hmass'.mul hw'
    have e1 : ν₀.real univ * ((ν₀.real univ)⁻¹ * ∫ x, f x ∂ν₀) = ∫ x, f x ∂ν₀ := by
      field_simp
    rw [e1] at hprod
    have : Tendsto (fun j => ∫ x, f x ∂(ν (j + N))) atTop (𝓝 (∫ x, f x ∂ν₀)) := by
      refine hprod.congr (fun j => ?_)
      have := (hposj j).ne'
      field_simp
    exact (tendsto_add_atTop_iff_nat N).1 this

private theorem exists_bcf_trunc {L : ℝ} (hL : 0 ≤ L) :
    ∃ h : BoundedContinuousFunction ℝ ℝ, ∀ x, h x = min (max x 0) L := by
  refine ⟨BoundedContinuousFunction.mkOfBound
    ⟨fun x => min (max x 0) L, by fun_prop⟩ L ?_, fun _ => rfl⟩
  intro x y
  have a1 : min (max x 0) L ≤ L := min_le_right _ _
  have a2 : min (max y 0) L ≤ L := min_le_right _ _
  have b1 : 0 ≤ min (max x 0) L := le_min (le_max_right _ _) hL
  have b2 : 0 ≤ min (max y 0) L := le_min (le_max_right _ _) hL
  simp only [ContinuousMap.coe_mk, Real.dist_eq]
  rw [abs_le]; constructor <;> linarith

private theorem integrable_trunc (m : Measure ℝ) [IsFiniteMeasure m] {L : ℝ} (hL : 0 ≤ L) :
    Integrable (fun x : ℝ => min (max x 0) L) m := by
  obtain ⟨h, hh⟩ := exists_bcf_trunc hL
  have : (fun x : ℝ => min (max x 0) L) = ⇑h := funext fun x => (hh x).symm
  rw [this]
  exact h.integrable m

private theorem integral_trunc_le_integral (m : Measure ℝ) [IsFiniteMeasure m]
    (hm : m (Iio 0) = 0) (hint : Integrable (fun x : ℝ => x) m) {L : ℝ} (hL : 0 ≤ L) :
    ∫ x, min (max x 0) L ∂m ≤ ∫ x, x ∂m := by
  refine integral_mono_ae (integrable_trunc m hL) hint ?_
  filter_upwards [ae_nonneg_of_Iio m hm] with x hx
  exact (min_le_left _ _).trans (by rw [max_eq_left hx])

private theorem tendsto_integral_trunc (ν : ℕ → Measure ℝ) (ν₀ : Measure ℝ)
    [∀ j, IsFiniteMeasure (ν j)] [IsFiniteMeasure ν₀]
    (hweak : ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun j => ∫ x, f x ∂(ν j)) atTop (𝓝 (∫ x, f x ∂ν₀))) {L : ℝ} (hL : 0 ≤ L) :
    Tendsto (fun j => ∫ x, min (max x 0) L ∂(ν j)) atTop
      (𝓝 (∫ x, min (max x 0) L ∂ν₀)) := by
  obtain ⟨h, hh⟩ := exists_bcf_trunc hL
  have : (fun x : ℝ => min (max x 0) L) = ⇑h := funext fun x => (hh x).symm
  rw [this]
  exact hweak h

private theorem tendsto_trunc_nat (m : Measure ℝ) [IsFiniteMeasure m] (hm : m (Iio 0) = 0)
    (hint : Integrable (fun x : ℝ => x) m) :
    Tendsto (fun n : ℕ => ∫ x, min (max x 0) (n : ℝ) ∂m) atTop (𝓝 (∫ x, x ∂m)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => ‖x‖) ?_ hint.norm ?_ ?_
  · intro n
    exact (integrable_trunc m (Nat.cast_nonneg n)).aestronglyMeasurable
  · intro n
    filter_upwards [ae_nonneg_of_Iio m hm] with x hx
    have h1 : 0 ≤ min (max x 0) (n : ℝ) := le_min (le_max_right _ _) (Nat.cast_nonneg n)
    rw [Real.norm_eq_abs, abs_of_nonneg h1, Real.norm_eq_abs, abs_of_nonneg hx]
    exact (min_le_left _ _).trans (by rw [max_eq_left hx])
  · filter_upwards [ae_nonneg_of_Iio m hm] with x hx
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈x⌉₊] with n hn
    have : x ≤ (n : ℝ) := (Nat.le_ceil x).trans (by exact_mod_cast hn)
    rw [max_eq_left hx, min_eq_left this]

private theorem integrable_id_of_trunc_bound (m : Measure ℝ) [IsFiniteMeasure m]
    (hm : m (Iio 0) = 0) {B : ℝ} (hB : ∀ n : ℕ, ∫ x, min (max x 0) (n : ℝ) ∂m ≤ B) :
    Integrable (fun x : ℝ => x) m ∧ ∫ x, x ∂m ≤ B := by
  have hI : Integrable (fun x : ℝ => x) m := by
    refine ⟨aestronglyMeasurable_id, ?_⟩
    have hmono : Monotone (fun (n : ℕ) (x : ℝ) => ENNReal.ofReal (min (max x 0) (n : ℝ))) := by
      intro a b hab x
      exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (by exact_mod_cast hab))
    have hsup : ∀ᵐ x ∂m, ‖x‖ₑ = ⨆ n : ℕ, ENNReal.ofReal (min (max x 0) (n : ℝ)) := by
      filter_upwards [ae_nonneg_of_Iio m hm] with x hx
      refine le_antisymm ?_ (iSup_le fun n => ?_)
      · refine le_iSup_of_le ⌈x⌉₊ ?_
        rw [max_eq_left hx, min_eq_left (Nat.le_ceil x), Real.enorm_eq_ofReal hx]
      · rw [Real.enorm_eq_ofReal hx]
        exact ENNReal.ofReal_le_ofReal ((min_le_left _ _).trans (by rw [max_eq_left hx]))
    have hmeas : ∀ n : ℕ, Measurable fun x : ℝ => ENNReal.ofReal (min (max x 0) (n : ℝ)) :=
      fun n => by fun_prop
    unfold HasFiniteIntegral
    rw [lintegral_congr_ae hsup, lintegral_iSup hmeas hmono]
    refine lt_of_le_of_lt (iSup_le fun n => ?_) (ENNReal.ofReal_lt_top (r := B))
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_trunc m (Nat.cast_nonneg n))]
    · exact ENNReal.ofReal_le_ofReal (hB n)
    · exact Eventually.of_forall fun x => le_min (le_max_right _ _) (Nat.cast_nonneg n)
  exact ⟨hI, le_of_tendsto' (tendsto_trunc_nat m hm hI) hB⟩

/-- **Fatou for the first moment** under weak convergence on `[0, ∞)`: with bounded first moments,
the limit has an integrable first moment and `∫ x dν₀ ≤ liminf ∫ x dν_j`.
Proof route: `x ↦ min (max x 0) L` is bounded continuous, so
`∫ min(x, L) dν₀ = lim_j ∫ min(x, L) dν_j ≤ liminf_j ∫ x dν_j`; let `L → ∞` by monotone
convergence (`lintegral_iSup` on `ENNReal.ofReal`), which also gives integrability
(`hasFiniteIntegral` from the uniform bound). The real `liminf` is genuine because the sequence
lies in `[0, sup]` (`isBoundedUnder` side conditions). -/
theorem integral_id_le_liminf (ν : ℕ → Measure ℝ) (ν₀ : Measure ℝ)
    [∀ j, IsFiniteMeasure (ν j)] [IsFiniteMeasure ν₀]
    (hsupp : ∀ j, ν j (Iio 0) = 0) (hsupp₀ : ν₀ (Iio 0) = 0)
    (hweak : ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun j => ∫ x, f x ∂(ν j)) atTop (𝓝 (∫ x, f x ∂ν₀)))
    (hint : ∀ j, Integrable (fun x : ℝ => x) (ν j))
    (hB : BddAbove (Set.range fun j => ∫ x, x ∂(ν j))) :
    Integrable (fun x : ℝ => x) ν₀ ∧
      ∫ x, x ∂ν₀ ≤ Filter.liminf (fun j => ∫ x, x ∂(ν j)) atTop := by
  obtain ⟨C, hC⟩ := hB
  have hbd : ∀ j, ∫ x, x ∂(ν j) ≤ C := fun j => hC ⟨j, rfl⟩
  have hnn : ∀ j, 0 ≤ ∫ x, x ∂(ν j) := fun j =>
    integral_nonneg_of_ae (by filter_upwards [ae_nonneg_of_Iio (ν j) (hsupp j)] with x hx using hx)
  have hI := integrable_id_of_trunc_bound ν₀ hsupp₀ (B := C) (fun n =>
    le_of_tendsto (tendsto_integral_trunc ν ν₀ hweak (Nat.cast_nonneg n))
      (Eventually.of_forall fun j =>
        (integral_trunc_le_integral (ν j) (hsupp j) (hint j) (Nat.cast_nonneg n)).trans (hbd j)))
  refine ⟨hI.1, ?_⟩
  refine le_of_tendsto' (tendsto_trunc_nat ν₀ hsupp₀ hI.1) (fun n => ?_)
  have hw := tendsto_integral_trunc ν ν₀ hweak (Nat.cast_nonneg n)
  rw [← hw.liminf_eq]
  refine liminf_le_liminf (Eventually.of_forall fun j =>
    integral_trunc_le_integral (ν j) (hsupp j) (hint j) (Nat.cast_nonneg n))
    hw.isBoundedUnder_ge (isBoundedUnder_of ⟨C, hbd⟩).isCoboundedUnder_ge

/-- **Half-moment convergence** under weak convergence on `[0, ∞)` with bounded first moments.
Proof route: port Muon `sqrt_part`/`sqrt_tail`: truncate `√x` at `L`
(`min (√(max x 0)) (√L)` is bounded continuous), with tail
`∫_{x > L} √x dν ≤ L^{−1/2} ∫ x dν` uniformly in `j` and for `ν₀`. -/
theorem tendsto_integral_sqrt_of_tendsto_integral (ν : ℕ → Measure ℝ) (ν₀ : Measure ℝ)
    [∀ j, IsFiniteMeasure (ν j)] [IsFiniteMeasure ν₀]
    (hsupp : ∀ j, ν j (Iio 0) = 0) (hsupp₀ : ν₀ (Iio 0) = 0)
    (hweak : ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun j => ∫ x, f x ∂(ν j)) atTop (𝓝 (∫ x, f x ∂ν₀)))
    (hint : ∀ j, Integrable (fun x : ℝ => x) (ν j)) (hint₀ : Integrable (fun x : ℝ => x) ν₀)
    (hB : BddAbove (Set.range fun j => ∫ x, x ∂(ν j))) :
    Tendsto (fun j => ∫ x, Real.sqrt x ∂(ν j)) atTop (𝓝 (∫ x, Real.sqrt x ∂ν₀)) := by
  exact sqrt_part ν ν₀ hsupp hsupp₀ hweak hint hint₀ hB

/-- Continuity theorem for probability measures, in the exact shape of Muon's
`lem_app_iso_transforms_i` (weak convergence, and half-moment convergence under first-moment
bounds).
Proof route: `tendsto_integral_of_tendsto_negStieltjes` (masses are constantly `1`) and
`tendsto_integral_sqrt_of_tendsto_integral`. -/
theorem tendsto_of_tendsto_negStieltjes_prob (ν : ℕ → Measure ℝ) (ν₀ : Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (ν j)) (hsupp : ∀ j, ν j (Iio 0) = 0)
    (hprob₀ : IsProbabilityMeasure ν₀) (hsupp₀ : ν₀ (Iio 0) = 0)
    (hconv : ∀ t : ℝ, 0 < t →
      Tendsto (fun j => negStieltjes (ν j) t) atTop (𝓝 (negStieltjes ν₀ t))) :
    (∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun j => ∫ x, f x ∂(ν j)) atTop (𝓝 (∫ x, f x ∂ν₀))) ∧
    ((∀ j, Integrable (fun x : ℝ => x) (ν j)) → Integrable (fun x : ℝ => x) ν₀ →
      BddAbove (Set.range fun j => ∫ x, x ∂(ν j)) →
      Tendsto (fun j => ∫ x, Real.sqrt x ∂(ν j)) atTop (𝓝 (∫ x, Real.sqrt x ∂ν₀))) := by
  have hweak := weak_conv ν ν₀ hprob hsupp hprob₀ hsupp₀ (fun t ht => hconv t ht)
  refine ⟨hweak, fun h1 h2 h3 => ?_⟩
  exact tendsto_integral_sqrt_of_tendsto_integral ν ν₀ hsupp hsupp₀ hweak h1 h2 h3

/-! ## Existence of the limit measure -/

private theorem mul_measure_Ioi_le (m : Measure ℝ) [IsFiniteMeasure m] (hm : m (Iio 0) = 0)
    (hint : Integrable (fun x : ℝ => x) m) {L : ℝ} (hL : 0 < L) :
    L * (m (Ioi L)).toReal ≤ ∫ x, x ∂m := by
  have := mul_meas_ge_le_integral_of_nonneg (μ := m) (f := fun x : ℝ => x)
    (by filter_upwards [ae_nonneg_of_Iio m hm] with x hx using hx) hint L
  refine le_trans (mul_le_mul_of_nonneg_left ?_ hL.le) this
  exact measureReal_mono (fun x (hx : L < x) => show L ≤ x from hx.le) (measure_ne_top _ _)

private theorem exists_prob_limit (p : ℕ → Measure ℝ) [hp : ∀ j, IsProbabilityMeasure (p j)]
    (hsupp : ∀ j, p j (Iio 0) = 0)
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set ℝ, IsCompact K ∧ ∀ j, p j Kᶜ ≤ ε)
    {h : ℝ → ℝ}
    (hh : ∀ t : ℝ, 0 < t → Tendsto (fun j => negStieltjes (p j) t) atTop (𝓝 (h t))) :
    ∃ a : Measure ℝ, IsProbabilityMeasure a ∧ a (Iio 0) = 0 ∧
      (∀ t : ℝ, 0 < t → negStieltjes a t = h t) ∧
      ∀ f : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun j => ∫ x, f x ∂(p j)) atTop (𝓝 (∫ x, f x ∂a)) := by
  let P : ℕ → ProbabilityMeasure ℝ := fun j => ⟨p j, hp j⟩
  have htight' : IsTightMeasureSet
      {((μ : ProbabilityMeasure ℝ) : Measure ℝ) | μ ∈ Set.range P} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    obtain ⟨K, hK, hKj⟩ := htight ε hε
    refine ⟨K, hK, ?_⟩
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact hKj j
  have hcomp : IsCompact (closure (Set.range P)) := isCompact_closure_of_isTightMeasureSet htight'
  have hsub : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∃ a : ProbabilityMeasure ℝ,
      (a : Measure ℝ) (Iio 0) = 0 ∧ (∀ t : ℝ, 0 < t → negStieltjes (a : Measure ℝ) t = h t) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto ((P ∘ ns) ∘ φ) atTop (𝓝 a) := by
    intro ns hns
    obtain ⟨a, -, φ, hφ, hlim⟩ := hcomp.tendsto_subseq (x := P ∘ ns)
      (fun n => subset_closure ⟨ns n, rfl⟩)
    have ha0 : (a : Measure ℝ) (Iio 0) = 0 := by
      have h := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim (G := Iio (0:ℝ))
        isOpen_Iio
      have : (fun n => (((P ∘ ns) ∘ φ) n : Measure ℝ) (Iio 0)) = fun _ => 0 :=
        funext fun n => hsupp _
      rw [this, liminf_const] at h
      exact le_antisymm h (zero_le)
    refine ⟨a, ha0, ?_, φ, hφ, hlim⟩
    intro t ht
    obtain ⟨hb, hhb⟩ := exists_bcf_resolvent ht
    have h1 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim) hb
    have h2 : Tendsto (fun n => ∫ x, hb x ∂(((P ∘ ns) ∘ φ) n : Measure ℝ)) atTop (𝓝 (h t)) :=
      ((hh t ht).comp (hns.comp hφ.tendsto_atTop)).congr fun n =>
        (integral_bcf_resolvent hb hhb _ (hsupp _)).symm
    show ∫ x, (x + t)⁻¹ ∂(a : Measure ℝ) = h t
    rw [← integral_bcf_resolvent hb hhb _ ha0]
    exact tendsto_nhds_unique h1 h2
  obtain ⟨a₀, ha0s, ha0t, -⟩ := hsub id tendsto_id
  refine ⟨a₀, a₀.prop, ha0s, ha0t, fun f => ?_⟩
  have hP : Tendsto P atTop (𝓝 a₀) := by
    refine tendsto_of_subseq_tendsto fun ns hns => ?_
    obtain ⟨a', hs, ht, φ, hφ, hlim⟩ := hsub ns hns
    have := a'.prop
    have := a₀.prop
    have : a' = a₀ := Subtype.ext
      (eq_of_negStieltjes_eq hs ha0s (fun t ht' => (ht t ht').trans (ha0t t ht').symm))
    exact ⟨φ, this ▸ hlim⟩
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hP f

/-- **Existence / limit theorem.** Let `ν j` be finite measures on `[0, ∞)` with real masses
`→ c`, integrable first moments `∫ x dν_j ≤ B`, and transforms `S_{ν_j}(−t) → g t` for every
`t > 0`. Then there is a finite measure `ν₀` on `[0, ∞)` of mass `c` with `S_{ν₀}(−t) = g t` for
all `t > 0`, integrable first moment `∫ x dν₀ ≤ B`, and `ν j → ν₀` weakly (the whole sequence).
Proof route: (1) Tightness: `ν_j([L, ∞)) ≤ B/L` (Markov, using the support). (2) Prokhorov for
finite measures with bounded masses (`isCompact_setOfPred_finiteMeasure_mass_eq_compl_isCompact_le`,
or normalize and use `isCompact_closure_of_isTightMeasureSet`; for `c = 0` take `ν₀ = 0`): a
subsequence converges weakly to a finite `ν₀`, in `FiniteMeasure ℝ` (convert with
`FiniteMeasure.tendsto_iff_forall_integral_tendsto`). (3) Mass: the constant `1` is bounded
continuous, so `ν₀(ℝ) = c`. (4) Support: `Iio 0` is open, so Portmanteau
(`FiniteMeasure.le_liminf_measure_open_of_tendsto`-type) gives `ν₀ (Iio 0) ≤ liminf 0 = 0`.
(5) Transform: `tendsto_negStieltjes_of_tendsto_integral` along the subsequence, via the bounded
continuous extension `(max x 0 + t)⁻¹`, and uniqueness of limits gives `S_{ν₀}(−t) = g t`.
(6) Moment: `integral_id_le_liminf` along the subsequence. (7) Whole sequence: every subsequence
has a further subsequence converging to some `ν₁` with the same mass, support and transform `g`,
so `ν₁ = ν₀` by `eq_of_negStieltjes_eq`; conclude with `tendsto_of_subseq_tendsto`. -/
theorem exists_tendsto_of_tendsto_negStieltjes (ν : ℕ → Measure ℝ) [∀ j, IsFiniteMeasure (ν j)]
    (hsupp : ∀ j, ν j (Iio 0) = 0) {c : ℝ}
    (hmass : Tendsto (fun j => (ν j).real univ) atTop (𝓝 c))
    (hint : ∀ j, Integrable (fun x : ℝ => x) (ν j)) {B : ℝ} (hB : ∀ j, ∫ x, x ∂(ν j) ≤ B)
    {g : ℝ → ℝ} (hg : ∀ t : ℝ, 0 < t → Tendsto (fun j => negStieltjes (ν j) t) atTop (𝓝 (g t))) :
    ∃ ν₀ : Measure ℝ, IsFiniteMeasure ν₀ ∧ ν₀ univ = ENNReal.ofReal c ∧ ν₀ (Iio 0) = 0 ∧
      (∀ t : ℝ, 0 < t → negStieltjes ν₀ t = g t) ∧
      Integrable (fun x : ℝ => x) ν₀ ∧ ∫ x, x ∂ν₀ ≤ B ∧
      ∀ f : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun j => ∫ x, f x ∂(ν j)) atTop (𝓝 (∫ x, f x ∂ν₀)) := by
  have hnn : ∀ j, 0 ≤ ∫ x, x ∂(ν j) := fun j =>
    integral_nonneg_of_ae (by filter_upwards [ae_nonneg_of_Iio (ν j) (hsupp j)] with x hx using hx)
  have hB0 : 0 ≤ B := (hnn 0).trans (hB 0)
  have hc0 : 0 ≤ c := ge_of_tendsto hmass (Eventually.of_forall fun j => measureReal_nonneg)
  rcases hc0.eq_or_lt with hc | hc
  · subst hc
    refine ⟨0, inferInstance, by simp, by simp, fun t ht => ?_, integrable_zero_measure, by simpa using hB0,
      fun f => ?_⟩
    · have h1 : Tendsto (fun j => negStieltjes (ν j) t) atTop (𝓝 0) := by
        refine squeeze_zero (fun j => negStieltjes_nonneg (hsupp j) ht)
          (fun j => negStieltjes_le (hsupp j) ht) ?_
        simpa using hmass.div_const t
      rw [tendsto_nhds_unique (hg t ht) h1]
      simp [negStieltjes]
    · simp only [integral_zero_measure]
      exact tendsto_integral_of_mass_zero ν hmass f
  · obtain ⟨N, hN⟩ := eventually_atTop.1
      (hmass.eventually (eventually_gt_nhds (half_lt_self hc)))
    have hmj : ∀ j, c / 2 < (ν (j + N)).real univ := fun j => hN (j + N) (by omega)
    have hmj0 : ∀ j, 0 < (ν (j + N)).real univ := fun j => by
      have := hmj j; linarith
    have hne : ∀ j, ν (j + N) univ ≠ 0 := fun j h => by
      have := hmj0 j
      simp [Measure.real, h] at this
    have hpr : ∀ j, IsProbabilityMeasure (normM (ν (j + N))) := fun j => isProb_normM _ (hne j)
    have hmass' : Tendsto (fun j => (ν (j + N)).real univ) atTop (𝓝 c) :=
      hmass.comp (tendsto_add_atTop_nat N)
    have htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set ℝ, IsCompact K ∧
        ∀ j, normM (ν (j + N)) Kᶜ ≤ ε := by
      intro ε hε
      by_cases hεt : ε = ⊤
      · exact ⟨∅, isCompact_empty, fun j => by simp [hεt]⟩
      have hδ : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
      set δ := ε.toReal with hδdef
      set L : ℝ := 2 * B / (c * δ) + 1 with hL
      have hLpos : 0 < L := by positivity
      have e : L * (c * δ) = 2 * B + c * δ := by
        rw [hL]; field_simp
      refine ⟨Icc 0 L, isCompact_Icc, fun j => ?_⟩
      have hmark := mul_measure_Ioi_le (ν (j + N)) (hsupp _) (hint _) hLpos
      have hm := hmj j
      have hm0 := hmj0 j
      have hnorm : (normM (ν (j + N)) (Ioi L)).toReal
          = ((ν (j + N)).real univ)⁻¹ * (ν (j + N) (Ioi L)).toReal := by
        simp [normM, Measure.smul_apply, ENNReal.toReal_mul, ENNReal.toReal_inv, Measure.real]
      have h3 : (normM (ν (j + N)) (Ioi L)).toReal ≤ δ := by
        rw [hnorm, inv_mul_le_iff₀ hm0]
        refine le_of_mul_le_mul_left ?_ hLpos
        nlinarith [mul_pos (mul_pos hLpos hδ) (sub_pos.2 hm), hB j, hB (j + N), hmark]
      have hI0 : normM (ν (j + N)) (Iio 0) = 0 := normM_Iio _ (hsupp _)
      refine le_trans (measure_mono ?_) (le_trans (measure_union_le (Iio 0) (Ioi L)) ?_)
      · intro x hx
        by_contra hxn
        simp only [mem_union, mem_Iio, mem_Ioi, not_or, not_lt] at hxn
        exact hx ⟨hxn.1, hxn.2⟩
      · rw [hI0, zero_add, ← ENNReal.ofReal_toReal (measure_ne_top _ (Ioi L)),
          ← ENNReal.ofReal_toReal hεt]
        exact ENNReal.ofReal_le_ofReal h3
    have hh : ∀ t : ℝ, 0 < t →
        Tendsto (fun j => negStieltjes (normM (ν (j + N))) t) atTop (𝓝 (c⁻¹ * g t)) := by
      intro t ht
      simp only [negStieltjes_normM]
      exact (hmass'.inv₀ hc.ne').mul ((hg t ht).comp (tendsto_add_atTop_nat N))
    obtain ⟨a, ha, ha0, hat, hwa⟩ := exists_prob_limit (fun j => normM (ν (j + N)))
      (fun j => normM_Iio _ (hsupp _)) htight hh
    set ν₀ : Measure ℝ := ENNReal.ofReal c • a with hν₀
    have hu : ν₀ univ = ENNReal.ofReal c := by simp [hν₀, Measure.smul_apply]
    have hfin : IsFiniteMeasure ν₀ := ⟨by rw [hu]; exact ENNReal.ofReal_lt_top⟩
    have hsupp0 : ν₀ (Iio 0) = 0 := by simp [hν₀, Measure.smul_apply, ha0]
    have htr : ∀ t : ℝ, 0 < t → negStieltjes ν₀ t = g t := by
      intro t ht
      rw [hν₀, negStieltjes_smul, hat t ht, ENNReal.toReal_ofReal hc.le]
      field_simp
    have hint0 : ∀ f : ℝ → ℝ, ∫ x, f x ∂ν₀ = c * ∫ x, f x ∂a := by
      intro f
      rw [hν₀, integral_smul_measure, ENNReal.toReal_ofReal hc.le, smul_eq_mul]
    have hweak0 : ∀ f : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun j => ∫ x, f x ∂(ν j)) atTop (𝓝 (∫ x, f x ∂ν₀)) := by
      intro f
      have hw' := hwa f
      simp only [integral_normM] at hw'
      have hprod := hmass'.mul hw'
      rw [← hint0 (fun x => f x)] at hprod
      have : Tendsto (fun j => ∫ x, f x ∂(ν (j + N))) atTop (𝓝 (∫ x, f x ∂ν₀)) := by
        refine hprod.congr (fun j => ?_)
        have := (hmj0 j).ne'
        field_simp
      exact (tendsto_add_atTop_iff_nat N).1 this
    have hI := integrable_id_of_trunc_bound ν₀ hsupp0 (B := B) (fun n =>
      le_of_tendsto (tendsto_integral_trunc ν ν₀ hweak0 (Nat.cast_nonneg n))
        (Eventually.of_forall fun j =>
          (integral_trunc_le_integral (ν j) (hsupp j) (hint j) (Nat.cast_nonneg n)).trans (hB j)))
    exact ⟨ν₀, hfin, hu, hsupp0, htr, hI.1, hI.2, hweak0⟩

/-! ## The complex transform -/

/-- At `z = −t` the complex transform is the real one.
Proof route: `integral_ofReal` (`integral_complex_ofReal`) after `Complex.ofReal_add`,
`Complex.ofReal_inv` and `sub_neg_eq_add`. -/
theorem stieltjes_neg_ofReal (ν : Measure ℝ) (t : ℝ) :
    stieltjes ν (-(t : ℂ)) = (negStieltjes ν t : ℂ) := by
  unfold stieltjes negStieltjes
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  push_cast
  rw [sub_neg_eq_add]

/-- `‖S_ν(z)‖ ≤ ν(ℝ)/|Im z|` off the real axis.
Proof route: `norm_integral_le_of_norm_le_const` with `‖(x − z)⁻¹‖ ≤ 1/|Im z|`
(`Complex.abs_im_le_norm`). -/
theorem norm_stieltjes_le (ν : Measure ℝ) [IsFiniteMeasure ν] {z : ℂ} (hz : z.im ≠ 0) :
    ‖stieltjes ν z‖ ≤ ν.real univ / |z.im| := by
  have hz' : 0 < |z.im| := abs_pos.2 hz
  have h := norm_integral_le_of_norm_le_const (μ := ν) (f := fun x : ℝ => ((x : ℂ) - z)⁻¹)
    (C := |z.im|⁻¹) (Eventually.of_forall fun x => by
      rw [norm_inv]
      refine inv_anti₀ hz' ?_
      have := Complex.abs_im_le_norm ((x : ℂ) - z)
      simpa using this)
  calc ‖stieltjes ν z‖ ≤ |z.im|⁻¹ * ν.real univ := h
    _ = ν.real univ / |z.im| := by rw [div_eq_inv_mul]

private theorem hasDerivAt_inv_sub_aux (x : ℝ) (z : ℂ) (hz : (x : ℂ) - z ≠ 0) :
    HasDerivAt (fun z : ℂ => ((x : ℂ) - z)⁻¹) ((((x : ℂ) - z) ^ 2)⁻¹) z := by
  have h1 : HasDerivAt (fun z : ℂ => (x : ℂ) - z) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (x : ℂ)
  have h3 := (hasStrictFDerivAt_ringInverse (𝕜 := ℂ) (Units.mk0 _ hz)).hasFDerivAt.comp_hasDerivAt
    z h1
  convert h3 using 1
  · funext z; simp [Ring.inverse_eq_inv']
  · simp
    field_simp

/-- **Holomorphy** of the Stieltjes transform of a finite measure on `[0, ∞)` on
`ℂ ∖ [0, ∞) = {z | Im z ≠ 0 ∨ Re z < 0}`.
Proof route: `hasDerivAt_integral_of_dominated_loc_of_deriv_le` at each `z₀`, with
`d = dist(z₀, [0, ∞)) > 0`, the bounds `‖(x − z)⁻¹‖ ≤ 2/d` and `‖(x − z)⁻²‖ ≤ 4/d²` for
`|z − z₀| < d/2` and `x ≥ 0` (a.e.), as in Muon's `resPow_hasDeriv`; or the series argument of
`section.tex` (proof of `lem:app-iso-transforms`). -/
theorem differentiableOn_stieltjes (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν (Iio 0) = 0) :
    DifferentiableOn ℂ (stieltjes ν) {z : ℂ | z.im ≠ 0 ∨ z.re < 0} := by
  intro z0 hz0
  obtain ⟨δ, hδ, hδx⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 ≤ x → δ ≤ ‖(x : ℂ) - z0‖ := by
    rcases hz0 with h | h
    · refine ⟨|z0.im|, abs_pos.2 h, fun x hx => ?_⟩
      have := Complex.abs_im_le_norm ((x : ℂ) - z0)
      simpa using this
    · have h' : z0.re < 0 := h
      refine ⟨-z0.re, by linarith, fun x hx => ?_⟩
      have := Complex.abs_re_le_norm ((x : ℂ) - z0)
      simp only [Complex.sub_re, Complex.ofReal_re] at this
      have h2 : -z0.re ≤ |x - z0.re| := by rw [abs_of_nonneg (by linarith)]; linarith
      exact h2.trans this
  have hnn := ae_nonneg_of_Iio ν hν
  have hlow : ∀ x : ℝ, 0 ≤ x → ∀ z ∈ Metric.ball z0 (δ / 2), δ / 2 ≤ ‖(x : ℂ) - z‖ := by
    intro x hx z hz
    have h1 := hδx x hx
    have h2 : ‖z - z0‖ < δ / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hz
    have h3 : ‖(x : ℂ) - z0‖ ≤ ‖(x : ℂ) - z‖ + ‖z - z0‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub (x : ℂ) z z0
      exact this
    linarith
  have hmeasF : ∀ z : ℂ, Measurable fun x : ℝ => ((x : ℂ) - z)⁻¹ := fun z => by fun_prop
  have hmeasF' : ∀ z : ℂ, Measurable fun x : ℝ => ((((x : ℂ) - z) ^ 2)⁻¹) := fun z => by fun_prop
  have hd : HasDerivAt (stieltjes ν) (∫ x, (((x : ℂ) - z0) ^ 2)⁻¹ ∂ν) z0 := by
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := z0)
      (F := fun z x => ((x : ℂ) - z)⁻¹) (F' := fun z x => (((x : ℂ) - z) ^ 2)⁻¹)
      (s := Metric.ball z0 (δ / 2)) (bound := fun _ => 4 / δ ^ 2)
      (Metric.ball_mem_nhds _ (by positivity))
      (Eventually.of_forall fun z => (hmeasF z).aestronglyMeasurable)
      (by
        refine Integrable.mono' (integrable_const δ⁻¹) (hmeasF z0).aestronglyMeasurable ?_
        filter_upwards [hnn] with x hx
        rw [norm_inv]
        exact inv_anti₀ hδ (hδx x hx))
      (hmeasF' z0).aestronglyMeasurable
      (by
        filter_upwards [hnn] with x hx z hz
        have h1 := hlow x hx z hz
        rw [norm_inv, norm_pow]
        have h2 : (δ / 2) ^ 2 ≤ ‖(x : ℂ) - z‖ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
        calc (‖(x : ℂ) - z‖ ^ 2)⁻¹ ≤ ((δ / 2) ^ 2)⁻¹ := inv_anti₀ (by positivity) h2
          _ = 4 / δ ^ 2 := by field_simp; norm_num)
      (integrable_const _)
      (by
        filter_upwards [hnn] with x hx z hz
        have h1 := hlow x hx z hz
        refine hasDerivAt_inv_sub_aux x z ?_
        intro h0
        rw [h0, norm_zero] at h1
        linarith)
    exact key.2
  exact hd.differentiableAt.differentiableWithinAt


/-! ## Appended: Lipschitz bound on the negative axis -/

/-- `|S_ν(−t) − S_ν(−t')| ≤ ν(ℝ) |t − t'| / (t t')` for a finite measure on `[0, ∞)` and
`t, t' > 0`. -/
theorem abs_negStieltjes_sub_le (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν (Iio 0) = 0)
    {t t' : ℝ} (ht : 0 < t) (ht' : 0 < t') :
    |negStieltjes ν t - negStieltjes ν t'| ≤ ν.real univ * |t - t'| / (t * t') := by
  unfold negStieltjes
  rw [← integral_sub (integrable_inv_add hν ht) (integrable_inv_add hν ht')]
  have h := norm_integral_le_of_norm_le_const (μ := ν)
    (f := fun x : ℝ => (x + t)⁻¹ - (x + t')⁻¹) (C := |t - t'| / (t * t'))
    (by
      filter_upwards [ae_nonneg_of_Iio ν hν] with x hx
      have h1 : 0 < x + t := by linarith
      have h2 : 0 < x + t' := by linarith
      have e : (x + t)⁻¹ - (x + t')⁻¹ = (t' - t) / ((x + t) * (x + t')) := by
        field_simp; ring
      rw [Real.norm_eq_abs, e, abs_div, abs_of_pos (mul_pos h1 h2), abs_sub_comm]
      apply div_le_div₀ (abs_nonneg _) le_rfl (mul_pos ht ht') 
      exact mul_le_mul (by linarith) (by linarith) ht'.le h1.le)
  rw [Real.norm_eq_abs] at h
  calc _ ≤ |t - t'| / (t * t') * ν.real univ := h
    _ = _ := by ring

end SpectralFoundations
