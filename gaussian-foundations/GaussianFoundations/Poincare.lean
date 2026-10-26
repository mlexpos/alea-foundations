import GaussianFoundations.Defs
import SLT.EfronStein
import SLT.GaussianLSI.TensorizedGLSI
import SLT.GaussianPoincare.Limit
import SLT.GaussianSobolevDense.Density

/-!
# The Gaussian Poincaré inequality on `EuclideanSpace ℝ (Fin n)` for `C¹` functions of finite Dirichlet energy.
-/

namespace GaussianFoundations

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

private lemma stdGaussian_eq_stdGaussianE (n : ℕ) :
    stdGaussian (EuclideanSpace ℝ (Fin n)) = GaussianMeasure.stdGaussianE n := by
  unfold GaussianMeasure.stdGaussianE GaussianMeasure.stdGaussianPi
  rw [← ProbabilityTheory.map_pi_eq_stdGaussian]
  rfl

private lemma memLp_fderiv_of_finite_energy {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f)
    (henergy :
      ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2 ∂(GaussianMeasure.stdGaussianE n) < ⊤) :
    MemLp (fun x => fderiv ℝ f x) 2 (GaussianMeasure.stdGaussianE n) := by
  have hmeas : AEStronglyMeasurable (fun x => fderiv ℝ f x)
      (GaussianMeasure.stdGaussianE n) :=
    (hf.continuous_fderiv (by norm_num)).aestronglyMeasurable
  rw [MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas]
  refine ⟨hmeas.norm.pow 2, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
    (ae_of_all _ fun x => sq_nonneg ‖fderiv ℝ f x‖)]
  simpa only [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm] using henergy

private lemma tendsto_toLp_of_eLpNorm_sub_tendsto_zero
    {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    {mu : Measure α} {u : α → F} {v : ℕ → α → F}
    (hu : MemLp u 2 mu) (hv : ∀ k, MemLp (v k) 2 mu)
    (hlim : Tendsto (fun k => eLpNorm (u - v k) 2 mu) atTop (nhds 0)) :
    Tendsto (fun k => (hv k).toLp (v k)) atTop (nhds (hu.toLp u)) := by
  rw [tendsto_iff_edist_tendsto_0]
  simpa only [Lp.edist_toLp_toLp, eLpNorm_sub_comm] using hlim

private lemma toLp_norm_sq_eq_integral_sq
    {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {mu : Measure α} {u : α → F}
    (hu : MemLp u 2 mu) :
    ‖hu.toLp u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂mu := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp] with x hx
  simp [hx]

private lemma variance_eq_continuous_Lp_functional
    {α : Type*} [MeasurableSpace α] {mu : Measure α} [IsProbabilityMeasure mu]
    {u : α → ℝ} (hu : MemLp u 2 mu) :
    variance u mu =
      ‖hu.toLp u‖ ^ 2 -
        inner ℝ ((memLp_const (p := 2) (μ := mu) (1 : ℝ)).toLp (fun _ => 1))
          (hu.toLp u) ^ 2 := by
  rw [variance_eq_sub hu]
  have hsq : ∫ x, (u ^ 2) x ∂mu = ∫ x, ‖u x‖ ^ 2 ∂mu := by
    apply integral_congr_ae
    filter_upwards with x
    simp [Pi.pow_apply, Real.norm_eq_abs, sq_abs]
  rw [hsq, ← toLp_norm_sq_eq_integral_sq hu]
  congr 2
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_const (p := 2) (μ := mu) (1 : ℝ)).coeFn_toLp,
    hu.coeFn_toLp] with x h1 hx
  simp [hx]

private lemma tendsto_variance_of_eLpNorm_sub_tendsto_zero
    {α : Type*} [MeasurableSpace α] {mu : Measure α} [IsProbabilityMeasure mu]
    {u : α → ℝ} {v : ℕ → α → ℝ}
    (hu : MemLp u 2 mu) (hv : ∀ k, MemLp (v k) 2 mu)
    (hlim : Tendsto (fun k => eLpNorm (u - v k) 2 mu) atTop (nhds 0)) :
    Tendsto (fun k => variance (v k) mu) atTop (nhds (variance u mu)) := by
  have hLp := tendsto_toLp_of_eLpNorm_sub_tendsto_zero hu hv hlim
  have hcont : Continuous (fun w : Lp ℝ 2 mu =>
      ‖w‖ ^ 2 - inner ℝ ((memLp_const (p := 2) (μ := mu) (1 : ℝ)).toLp (fun _ => 1)) w ^ 2) := by
    fun_prop
  rw [variance_eq_continuous_Lp_functional hu]
  have heq : (fun k => variance (v k) mu) = fun k =>
      ‖(hv k).toLp (v k)‖ ^ 2 -
        inner ℝ ((memLp_const (p := 2) (μ := mu) (1 : ℝ)).toLp (fun _ => 1))
          ((hv k).toLp (v k)) ^ 2 := by
    funext k
    exact variance_eq_continuous_Lp_functional (hv k)
  rw [heq]
  exact (hcont.tendsto _).comp hLp

private lemma tendsto_integral_norm_sq_of_eLpNorm_sub_tendsto_zero
    {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {mu : Measure α}
    {u : α → F} {v : ℕ → α → F}
    (hu : MemLp u 2 mu) (hv : ∀ k, MemLp (v k) 2 mu)
    (hlim : Tendsto (fun k => eLpNorm (u - v k) 2 mu) atTop (nhds 0)) :
    Tendsto (fun k => ∫ x, ‖v k x‖ ^ 2 ∂mu) atTop
      (nhds (∫ x, ‖u x‖ ^ 2 ∂mu)) := by
  have hLp := tendsto_toLp_of_eLpNorm_sub_tendsto_zero hu hv hlim
  have hcont : Continuous (fun w : Lp F 2 mu => ‖w‖ ^ 2) := by fun_prop
  rw [← toLp_norm_sq_eq_integral_sq hu]
  have heq : (fun k => ∫ x, ‖v k x‖ ^ 2 ∂mu) =
      fun k => ‖(hv k).toLp (v k)‖ ^ 2 := by
    funext k
    exact (toLp_norm_sq_eq_integral_sq (hv k)).symm
  rw [heq]
  exact (hcont.tendsto _).comp hLp

private lemma tendsto_component_of_add_tendsto_zero
    {a b : ℕ → ℝ≥0∞} (h : Tendsto (fun k => a k + b k) atTop (nhds 0)) :
    Tendsto a atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with k hk
  exact (le_add_right (le_refl (a k))).trans hk

private lemma tendsto_of_le_of_tendsto_zero {a b : ℕ → ℝ≥0∞}
    (hab : ∀ k, a k ≤ b k) (h : Tendsto b atTop (nhds 0)) :
    Tendsto a atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with k hk
  exact (hab k).trans hk

private lemma tendsto_of_sq_tendsto_zero {a : ℕ → ℝ≥0∞}
    (h : Tendsto (fun k => a k ^ 2) atTop (nhds 0)) :
    Tendsto a atTop (nhds 0) := by
  have hr := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp h
  have hsqrt (x : ℝ≥0∞) : (x ^ 2) ^ (1 / 2 : ℝ) = x := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  change Tendsto (fun k => (a k ^ 2) ^ (1 / 2 : ℝ)) atTop
    (nhds ((0 : ℝ≥0∞) ^ (1 / 2 : ℝ))) at hr
  simpa only [hsqrt, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using hr

private lemma compactlySupportedSmooth_slice {n : ℕ} {g : (Fin n → ℝ) → ℝ}
    (hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g) (hg_supp : HasCompactSupport g)
    (i : Fin n) (x : Fin n → ℝ) :
    EfronSteinApp.CompactlySupportedSmooth (fun y => g (Function.update x i y)) := by
  constructor
  · exact (hg_smooth.of_le (by norm_num)).comp (contDiff_update 2 x i)
  · obtain ⟨R, hR⟩ := hg_supp.isBounded.exists_norm_le
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Set.Icc (-R) R))
    intro y hy
    have hmem : Function.update x i y ∈ tsupport g := subset_tsupport g hy
    have hbound := hR (Function.update x i y) hmem
    have hy_le : |y| ≤ ‖Function.update x i y‖ := by
      calc
        |y| = ‖(Function.update x i y) i‖ := by simp [Real.norm_eq_abs]
        _ ≤ ‖Function.update x i y‖ := norm_le_pi_norm _ i
    constructor
    · exact (neg_le_neg (hy_le.trans hbound)).trans (neg_abs_le y)
    · exact (le_abs_self y).trans (hy_le.trans hbound)

private lemma measurePreserving_update_gaussian {n : ℕ} (i : Fin n) :
    MeasurePreserving (fun p : (Fin n → ℝ) × ℝ => Function.update p.1 i p.2)
      ((GaussianMeasure.stdGaussianPi n).prod (gaussianReal 0 1))
      (GaussianMeasure.stdGaussianPi n) := by
  constructor
  · exact measurable_update' (a := i)
  · have hmap : Measurable (fun q : ℝ × (Fin n → ℝ) => Function.update q.2 i q.1) :=
      (measurable_update' (a := i)).comp measurable_swap
    calc
      Measure.map (fun p : (Fin n → ℝ) × ℝ => Function.update p.1 i p.2)
          ((GaussianMeasure.stdGaussianPi n).prod (gaussianReal 0 1)) =
        Measure.map (fun q : ℝ × (Fin n → ℝ) => Function.update q.2 i q.1)
          (Measure.map Prod.swap
            ((GaussianMeasure.stdGaussianPi n).prod (gaussianReal 0 1))) := by
              rw [Measure.map_map hmap measurable_swap]
              rfl
      _ = Measure.map (fun q : ℝ × (Fin n → ℝ) => Function.update q.2 i q.1)
          ((gaussianReal 0 1).prod (GaussianMeasure.stdGaussianPi n)) := by
            rw [Measure.prod_swap]
      _ = GaussianMeasure.stdGaussianPi n := by
            simpa [GaussianMeasure.stdGaussianPi] using
              (map_update_prod_pi (μs := fun _ : Fin n => gaussianReal 0 1) (i := i))

private theorem gaussianPoincare_pi_smooth_compactSupport {n : ℕ}
    {g : (Fin n → ℝ) → ℝ}
    (hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g) (hg_supp : HasCompactSupport g) :
    variance g (GaussianMeasure.stdGaussianPi n) ≤
      ∫ x, ∑ i : Fin n, (GaussianLSI.partialDeriv i g x) ^ 2
        ∂(GaussianMeasure.stdGaussianPi n) := by
  let μ := GaussianMeasure.stdGaussianPi n
  have hg_mem : MemLp g 2 μ :=
    hg_smooth.continuous.memLp_of_hasCompactSupport hg_supp
  have hp_cont (i : Fin n) : Continuous (GaussianLSI.partialDeriv i g) := by
    unfold GaussianLSI.partialDeriv
    exact ((ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)).continuous.comp
      (hg_smooth.continuous_fderiv (by simp)))
  have hp_supp (i : Fin n) : HasCompactSupport (GaussianLSI.partialDeriv i g) := by
    unfold GaussianLSI.partialDeriv
    change HasCompactSupport
      ((fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) ∘ fun x => fderiv ℝ g x)
    exact (hg_supp.fderiv ℝ).comp_left (by simp)
  have hp_mem (i : Fin n) : MemLp (GaussianLSI.partialDeriv i g) 2 μ :=
    (hp_cont i).memLp_of_hasCompactSupport (hp_supp i)
  have hES : variance g μ ≤ ∑ i : Fin n,
      ∫ x, (g x - condExpExceptCoord (μs := fun _ : Fin n => gaussianReal 0 1) i g x) ^ 2 ∂μ := by
    simpa [μ, GaussianMeasure.stdGaussianPi] using
      (efronStein (μs := fun _ : Fin n => gaussianReal 0 1) g hg_mem)
  have hterm (i : Fin n) :
      ∫ x, (g x - condExpExceptCoord (μs := fun _ : Fin n => gaussianReal 0 1) i g x) ^ 2 ∂μ ≤
        ∫ x, ∫ y, (GaussianLSI.partialDeriv i g (Function.update x i y)) ^ 2
          ∂(gaussianReal 0 1) ∂μ := by
    have hcond_mem : MemLp
        (condExpExceptCoord (μs := fun _ : Fin n => gaussianReal 0 1) i g) 2 μ := by
      simpa [μ, GaussianMeasure.stdGaussianPi] using
        (memLp_condExpExceptCoord (μs := fun _ : Fin n => gaussianReal 0 1) i g hg_mem)
    have hdiff_int : Integrable (fun x =>
        (g x - condExpExceptCoord (μs := fun _ : Fin n => gaussianReal 0 1) i g x) ^ 2) μ :=
      (hg_mem.sub hcond_mem).integrable_sq
    have heq_cond :
        ∫ x, (g x - condExpExceptCoord (μs := fun _ : Fin n => gaussianReal 0 1) i g x) ^ 2 ∂μ =
          ∫ x, condVarExceptCoord (μs := fun _ : Fin n => gaussianReal 0 1) i g x ∂μ := by
      simpa [μ, GaussianMeasure.stdGaussianPi] using
        (expectation_sq_diff_eq_expectation_condVar
          (μs := fun _ : Fin n => gaussianReal 0 1) g i
          (hg_mem.integrable one_le_two) hdiff_int)
    have hcond_int : Integrable
        (condVarExceptCoord (μs := fun _ : Fin n => gaussianReal 0 1) i g) μ := by
      let q := fun z =>
        (g z - condExpExceptCoord (μs := fun _ : Fin n => gaussianReal 0 1) i g z) ^ 2
      have hq : Integrable q μ := hdiff_int
      have hprod : Integrable
          (fun p : (Fin n → ℝ) × ℝ => q (Function.update p.1 i p.2))
          (μ.prod (gaussianReal 0 1)) := by
        exact (measurePreserving_update_gaussian i).integrable_comp hq.aestronglyMeasurable |>.mpr hq
      have hout := hprod.integral_prod_left
      change Integrable (fun x => ∫ y,
        (g (Function.update x i y) -
          condExpExceptCoord (μs := fun _ : Fin n => gaussianReal 0 1) i g x) ^ 2
          ∂(gaussianReal 0 1)) μ
      simpa [q, condExpExceptCoord_update] using hout
    have hright_int : Integrable (fun x =>
        ∫ y, (GaussianLSI.partialDeriv i g (Function.update x i y)) ^ 2
          ∂(gaussianReal 0 1)) μ := by
      let q := fun z => (GaussianLSI.partialDeriv i g z) ^ 2
      have hq : Integrable q μ := (hp_mem i).integrable_sq
      have hprod : Integrable
          (fun p : (Fin n → ℝ) × ℝ => q (Function.update p.1 i p.2))
          (μ.prod (gaussianReal 0 1)) := by
        exact (measurePreserving_update_gaussian i).integrable_comp hq.aestronglyMeasurable |>.mpr hq
      simpa [q] using hprod.integral_prod_left
    rw [heq_cond]
    apply integral_mono_ae hcond_int hright_int
    filter_upwards with x
    have hP := GaussianPoincare.gaussianPoincare
      (compactlySupportedSmooth_slice hg_smooth hg_supp i x)
    have hvar_eq : variance (fun y => g (Function.update x i y)) (gaussianReal 0 1) =
        condVarExceptCoord (μs := fun _ : Fin n => gaussianReal 0 1) i g x := by
      rw [variance_eq_integral]
      · rfl
      · exact (compactlySupportedSmooth_slice hg_smooth hg_supp i x).continuous.aemeasurable
    rw [← hvar_eq]
    have hP' : variance (fun y => g (Function.update x i y)) (gaussianReal 0 1) ≤
        ∫ y, (deriv (fun y => g (Function.update x i y)) y) ^ 2
          ∂(gaussianReal 0 1) := by
      simpa [GaussianPoincare.stdGaussian] using hP
    calc
      variance (fun y => g (Function.update x i y)) (gaussianReal 0 1) ≤
          ∫ y, (deriv (fun y => g (Function.update x i y)) y) ^ 2
            ∂(gaussianReal 0 1) := hP'
      _ = ∫ y, (GaussianLSI.partialDeriv i g (Function.update x i y)) ^ 2
            ∂(gaussianReal 0 1) := by
        apply integral_congr_ae
        filter_upwards with y
        change deriv (GaussianLSI.sliceFunction i g x) y ^ 2 = _
        exact congrArg (fun z : ℝ => z ^ 2)
          (GaussianLSI.deriv_sliceFunction_eq_partialDeriv i g
            (hg_smooth.differentiable (by simp)) x y)
  calc
    variance g μ ≤ ∑ i : Fin n,
        ∫ x, (g x - condExpExceptCoord (μs := fun _ : Fin n => gaussianReal 0 1) i g x) ^ 2 ∂μ := hES
    _ ≤ ∑ i : Fin n, ∫ x, ∫ y,
        (GaussianLSI.partialDeriv i g (Function.update x i y)) ^ 2
          ∂(gaussianReal 0 1) ∂μ := Finset.sum_le_sum fun i _ => hterm i
    _ = ∑ i : Fin n, ∫ z, (GaussianLSI.partialDeriv i g z) ^ 2 ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      let q := fun z => (GaussianLSI.partialDeriv i g z) ^ 2
      have hq : Integrable q μ := (hp_mem i).integrable_sq
      have hprod : Integrable
          (fun p : (Fin n → ℝ) × ℝ => q (Function.update p.1 i p.2))
          (μ.prod (gaussianReal 0 1)) := by
        exact (measurePreserving_update_gaussian i).integrable_comp hq.aestronglyMeasurable |>.mpr hq
      calc
        ∫ x, ∫ y, q (Function.update x i y) ∂(gaussianReal 0 1) ∂μ =
            ∫ y, ∫ x, q (Function.update x i y) ∂μ ∂(gaussianReal 0 1) := by
              rw [integral_integral_swap hprod]
        _ = ∫ z, q z ∂μ := by
          simpa [μ, GaussianMeasure.stdGaussianPi] using
            (integral_update_eq_integral
              (μs := fun _ : Fin n => gaussianReal 0 1) (i := i) (f := q) hq)
    _ = ∫ x, ∑ i : Fin n, (GaussianLSI.partialDeriv i g x) ^ 2 ∂μ := by
      symm
      apply integral_finsetSum
      intro i _
      exact (hp_mem i).integrable_sq

private theorem gaussianPoincare_smooth_compactSupport {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f) (hf_supp : HasCompactSupport f) :
    variance f (GaussianMeasure.stdGaussianE n) ≤
      ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂(GaussianMeasure.stdGaussianE n) := by
  let e : (Fin n → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm
  let g : (Fin n → ℝ) → ℝ := f ∘ e
  have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g := hf_smooth.comp e.contDiff
  have hg_supp : HasCompactSupport g := by
    exact hf_supp.comp_homeomorph e.toHomeomorph
  have hpi := gaussianPoincare_pi_smooth_compactSupport hg_smooth hg_supp
  have he_basis (i : Fin n) :
      e (Pi.single i 1) = EuclideanSpace.basisFun (Fin n) ℝ i := by
    ext j
    classical
    simp [e, EuclideanSpace.basisFun_apply, Pi.single, Function.update]
  have hpartial (w : Fin n → ℝ) (i : Fin n) :
      GaussianLSI.partialDeriv i g w =
        fderiv ℝ f (e w) (EuclideanSpace.basisFun (Fin n) ℝ i) := by
    have hfd : fderiv ℝ g w = (fderiv ℝ f (e w)).comp e.toContinuousLinearMap := by
      exact ((hf_smooth.differentiable (by simp) (e w)).hasFDerivAt.comp w
        e.hasFDerivAt).fderiv
    rw [GaussianLSI.partialDeriv, hfd, ContinuousLinearMap.comp_apply]
    congr 1
    exact he_basis i
  have hsum (w : Fin n → ℝ) :
      ∑ i : Fin n, (GaussianLSI.partialDeriv i g w) ^ 2 = ‖fderiv ℝ f (e w)‖ ^ 2 := by
    rw [(EuclideanSpace.basisFun (Fin n) ℝ).norm_dual (fderiv ℝ f (e w))]
    apply Finset.sum_congr rfl
    intro i _
    rw [hpartial]
  have hvar : variance f (GaussianMeasure.stdGaussianE n) =
      variance g (GaussianMeasure.stdGaussianPi n) := by
    unfold GaussianMeasure.stdGaussianE
    simpa [g, e] using
      (variance_map_equiv f
        e.toHomeomorph.toMeasurableEquiv (μ := GaussianMeasure.stdGaussianPi n))
  have henergy :
      ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂(GaussianMeasure.stdGaussianE n) =
        ∫ w, ∑ i : Fin n, (GaussianLSI.partialDeriv i g w) ^ 2
          ∂(GaussianMeasure.stdGaussianPi n) := by
    rw [GaussianMeasure.integral_stdGaussianE_eq]
    apply integral_congr_ae
    filter_upwards with w
    simpa [e] using (hsum w).symm
  rw [hvar, henergy]
  exact hpi

private theorem gaussianPoincare_memW12 {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : GaussianSobolev.MemW12Gaussian n f (GaussianMeasure.stdGaussianE n))
    (hf_diff : Differentiable ℝ f)
    (hf_grad_cont : Continuous (fun x => fderiv ℝ f x)) :
    evariance f (GaussianMeasure.stdGaussianE n) ≤
      ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2 ∂(GaussianMeasure.stdGaussianE n) := by
  let μ := GaussianMeasure.stdGaussianE n
  obtain ⟨g, hg_smooth, hg_supp, hg_tendsto⟩ :=
    GaussianSobolev.exists_smooth_compactSupport_seq_tendsto f hf hf_diff hf_grad_cont
  have hg_mem : ∀ k, MemLp (g k) 2 μ := fun k =>
    (hg_smooth k).continuous.memLp_of_hasCompactSupport (hg_supp k)
  have hdg_mem : ∀ k, MemLp (fun x => fderiv ℝ (g k) x) 2 μ := fun k =>
    ((hg_smooth k).continuous_fderiv (by simp)).memLp_of_hasCompactSupport
      ((hg_supp k).fderiv ℝ)
  have hsum : Tendsto (fun k =>
      eLpNorm (f - g k) 2 μ ^ 2 +
        eLpNorm (fun x => ‖fderiv ℝ (f - g k) x‖) 2 μ ^ 2) atTop (nhds 0) := by
    simpa [μ, GaussianSobolev.GaussianSobolevNormSq] using hg_tendsto
  have hf_sq : Tendsto (fun k => eLpNorm (f - g k) 2 μ ^ 2) atTop (nhds 0) :=
    tendsto_component_of_add_tendsto_zero hsum
  have hdf_sq : Tendsto (fun k =>
      eLpNorm (fun x => ‖fderiv ℝ (f - g k) x‖) 2 μ ^ 2) atTop (nhds 0) := by
    apply tendsto_component_of_add_tendsto_zero
    simpa [add_comm] using hsum
  have hf_lim : Tendsto (fun k => eLpNorm (f - g k) 2 μ) atTop (nhds 0) :=
    tendsto_of_sq_tendsto_zero hf_sq
  have hdf_lim' : Tendsto (fun k =>
      eLpNorm (fun x => ‖fderiv ℝ (f - g k) x‖) 2 μ) atTop (nhds 0) :=
    tendsto_of_sq_tendsto_zero hdf_sq
  have hderiv_sub (k : ℕ) :
      (fun x => fderiv ℝ (f - g k) x) =
        (fun x => fderiv ℝ f x) - fun x => fderiv ℝ (g k) x := by
    funext x
    exact fderiv_sub (hf_diff x) ((hg_smooth k).differentiable (by simp) x)
  have hdf_lim : Tendsto (fun k => eLpNorm
      ((fun x => fderiv ℝ f x) - fun x => fderiv ℝ (g k) x) 2 μ)
      atTop (nhds 0) := by
    have hmeas : ∀ k, AEStronglyMeasurable (fun x => fderiv ℝ (f - g k) x) μ := fun k =>
      by
        rw [hderiv_sub k]
        exact (hf_grad_cont.sub ((hg_smooth k).continuous_fderiv (by simp))).aestronglyMeasurable
    simpa only [← hderiv_sub, eLpNorm_norm _ (hmeas _)] using hdf_lim'
  have hvar_tendsto := tendsto_variance_of_eLpNorm_sub_tendsto_zero hf.1 hg_mem hf_lim
  have hnorm_df_lim : Tendsto (fun k => eLpNorm
      ((fun x => ‖fderiv ℝ f x‖) - fun x => ‖fderiv ℝ (g k) x‖) 2 μ)
      atTop (nhds 0) := by
    apply tendsto_of_le_of_tendsto_zero _ hdf_lim
    intro k
    apply eLpNorm_mono_ae
    · exact (hf_grad_cont.norm.sub
        ((hg_smooth k).continuous_fderiv (by simp)).norm).aestronglyMeasurable
    · filter_upwards with x
      simpa [Pi.sub_apply, Real.norm_eq_abs] using
        (abs_norm_sub_norm_le (fderiv ℝ f x) (fderiv ℝ (g k) x))
  have henergy_tendsto : Tendsto
      (fun k => ∫ x, ‖fderiv ℝ (g k) x‖ ^ 2 ∂μ) atTop
      (nhds (∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ)) := by
    simpa only [norm_norm] using
      (tendsto_integral_norm_sq_of_eLpNorm_sub_tendsto_zero
        hf.2.norm (fun k => (hdg_mem k).norm) hnorm_df_lim)
  have hineq : ∀ k, variance (g k) μ ≤
      ∫ x, ‖fderiv ℝ (g k) x‖ ^ 2 ∂μ := fun k => by
    simpa [μ] using gaussianPoincare_smooth_compactSupport (hg_smooth k) (hg_supp k)
  have hreal : variance f μ ≤ ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ :=
    le_of_tendsto_of_tendsto hvar_tendsto henergy_tendsto (Eventually.of_forall hineq)
  have henergy_int : Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hf.2.aestronglyMeasurable).mp hf.2
  have henergy_eq : ENNReal.ofReal (∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ) =
      ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2 ∂μ := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun x => sq_nonneg ‖fderiv ℝ f x‖)
      henergy_int.aestronglyMeasurable]
    rw [ENNReal.ofReal_toReal henergy_int.lintegral_lt_top.ne]
    apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
  rw [← hf.1.ofReal_variance_eq, ← henergy_eq]
  exact ENNReal.ofReal_le_ofReal hreal

private lemma tendsto_nat_mul_arctan_div (t : ℝ) :
    Tendsto (fun k : ℕ => (k + 1 : ℝ) * Real.arctan (t / (k + 1 : ℝ)))
      atTop (nhds t) := by
  by_cases ht : t = 0
  · simp [ht]
  have ha : Tendsto (fun k : ℕ => (k + 1 : ℝ)) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun k : ℕ => t / (k + 1 : ℝ)) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.div_atTop ha
  have hz_ne : ∀ k : ℕ, t / (k + 1 : ℝ) ≠ 0 := by
    intro k
    exact div_ne_zero ht (by positivity)
  have hz_within : Tendsto (fun k : ℕ => t / (k + 1 : ℝ)) atTop (nhdsWithin 0 {0}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hz, Eventually.of_forall (fun k => hz_ne k)⟩
  have hslope : Tendsto (slope Real.arctan 0) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
    simpa using (Real.hasDerivAt_arctan 0).tendsto_slope
  have hcomp := hslope.comp hz_within
  have hmul : Tendsto
      (fun k : ℕ => t * slope Real.arctan 0 (t / (k + 1 : ℝ)))
      atTop (nhds (t * 1)) := tendsto_const_nhds.mul hcomp
  convert hmul using 1
  · funext k
    rw [slope]
    simp only [Real.arctan_zero, vsub_eq_sub, sub_zero, smul_eq_mul]
    field_simp
  · simp

private lemma lintegral_pair_sub_sq_eq_two_evariance
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {u : α → ℝ} (hu : MemLp u 2 μ) :
    ∫⁻ p : α × α, ‖u p.1 - u p.2‖ₑ ^ 2 ∂(μ.prod μ) = 2 * evariance u μ := by
  have hu_int : Integrable u μ := hu.integrable one_le_two
  have hfst : Integrable (fun p : α × α => u p.1 ^ 2) (μ.prod μ) :=
    hu.integrable_sq.comp_fst μ
  have hsnd : Integrable (fun p : α × α => u p.2 ^ 2) (μ.prod μ) :=
    hu.integrable_sq.comp_snd μ
  have hcross : Integrable (fun p : α × α => u p.1 * u p.2) (μ.prod μ) :=
    hu_int.mul_prod hu_int
  have hmiddle : Integrable (fun p : α × α => 2 * (u p.1 * u p.2)) (μ.prod μ) :=
    hcross.const_mul 2
  have hpair : Integrable (fun p : α × α => (u p.1 - u p.2) ^ 2) (μ.prod μ) := by
    have h := (hfst.sub hmiddle).add hsnd
    convert h using 1
    ext p
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hreal :
      ∫ p : α × α, (u p.1 - u p.2) ^ 2 ∂(μ.prod μ) = 2 * variance u μ := by
    rw [show (fun p : α × α => (u p.1 - u p.2) ^ 2) =
        ((fun p => u p.1 ^ 2) - (fun p => 2 * (u p.1 * u p.2))) +
          (fun p => u p.2 ^ 2) by
      funext p; simp only [Pi.add_apply, Pi.sub_apply]; ring]
    calc
      integral (μ.prod μ)
          (((fun p => u p.1 ^ 2) - (fun p => 2 * (u p.1 * u p.2))) +
            (fun p => u p.2 ^ 2)) =
          integral (μ.prod μ) (fun p => u p.1 ^ 2) -
            integral (μ.prod μ) (fun p => 2 * (u p.1 * u p.2)) +
              integral (μ.prod μ) (fun p => u p.2 ^ 2) := by
        calc
          integral (μ.prod μ)
              (((fun p => u p.1 ^ 2) - (fun p => 2 * (u p.1 * u p.2))) +
                (fun p => u p.2 ^ 2)) =
              integral (μ.prod μ)
                  ((fun p => u p.1 ^ 2) - (fun p => 2 * (u p.1 * u p.2))) +
                integral (μ.prod μ) (fun p => u p.2 ^ 2) :=
            integral_add (hfst.sub hmiddle) hsnd
          _ = _ := by
            have hsubeq : integral (μ.prod μ)
                ((fun p => u p.1 ^ 2) - (fun p => 2 * (u p.1 * u p.2))) =
                integral (μ.prod μ) (fun p => u p.1 ^ 2) -
                  integral (μ.prod μ) (fun p => 2 * (u p.1 * u p.2)) := by
              change (∫ p, u p.1 ^ 2 - 2 * (u p.1 * u p.2) ∂(μ.prod μ)) = _
              exact integral_sub hfst hmiddle
            rw [hsubeq]
      _ = 2 * variance u μ := by
        rw [integral_const_mul,
      integral_fun_fst (fun x => u x ^ 2), integral_fun_snd (fun x => u x ^ 2),
      integral_prod_mul u u,
      variance_eq_sub hu]
        simp only [Pi.pow_apply, probReal_univ, one_smul]
        ring
  have hleft : ENNReal.ofReal
      (∫ p : α × α, (u p.1 - u p.2) ^ 2 ∂(μ.prod μ)) =
      ∫⁻ p : α × α, ‖u p.1 - u p.2‖ₑ ^ 2 ∂(μ.prod μ) := by
    have hconvert := integral_eq_lintegral_of_nonneg_ae
      (ae_of_all (μ.prod μ) fun p : α × α => sq_nonneg (u p.1 - u p.2))
      hpair.aestronglyMeasurable
    rw [hconvert]
    rw [ENNReal.ofReal_toReal hpair.lintegral_lt_top.ne]
    apply lintegral_congr
    intro p
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _) 2]
    congr 1
    exact (sq_abs (u p.1 - u p.2)).symm
  rw [← hleft, hreal, ENNReal.ofReal_mul (by positivity), hu.ofReal_variance_eq]
  norm_num

private theorem memLp_of_finite_gaussian_energy {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f)
    (henergy :
      ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2 ∂(GaussianMeasure.stdGaussianE n) < ⊤) :
    MemLp f 2 (GaussianMeasure.stdGaussianE n) := by
  let μ := GaussianMeasure.stdGaussianE n
  let a : ℕ → ℝ := fun k => k + 1
  let g : ℕ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun k x => a k * Real.arctan (f x / a k)
  have ha_pos (k : ℕ) : 0 < a k := by dsimp [a]; positivity
  have hg_diff (k : ℕ) : ContDiff ℝ 1 (g k) := by
    dsimp [g]
    simpa only [Function.comp_apply, smul_eq_mul] using
      ContDiff.const_smul (a k) (Real.contDiff_arctan.comp (hf.div_const (a k)))
  have hg_fderiv (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (g k) x =
        (1 / (1 + (f x / a k) ^ 2)) • fderiv ℝ f x := by
    have hdiv : HasFDerivAt (fun y => f y / a k)
        ((a k)⁻¹ • fderiv ℝ f x) x := by
      simpa [div_eq_inv_mul] using
        ((hf.differentiable (by norm_num) x).hasFDerivAt.const_mul (a k)⁻¹)
    have h := ((hdiv.arctan).const_mul (a k)).fderiv
    rw [h]
    simp only [one_div, smul_smul]
    congr 1
    field_simp [ne_of_gt (ha_pos k)]
  have hg_mem (k : ℕ) : MemLp (g k) 2 μ := by
    refine memLp_of_bounded
      (a := -(a k * (Real.pi / 2))) (b := a k * (Real.pi / 2)) ?_
      (hg_diff k).continuous.aestronglyMeasurable 2
    refine ae_of_all μ fun x => ?_
    constructor
    · have h := Real.neg_pi_div_two_lt_arctan (f x / a k)
      nlinarith [ha_pos k]
    · have h := Real.arctan_lt_pi_div_two (f x / a k)
      nlinarith [ha_pos k]
  have hg_fderiv_norm_le (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
      ‖fderiv ℝ (g k) x‖ ≤ ‖fderiv ℝ f x‖ := by
    rw [hg_fderiv, norm_smul]
    have hc_nonneg : 0 ≤ 1 / (1 + (f x / a k) ^ 2) := by positivity
    have hc_le : 1 / (1 + (f x / a k) ^ 2) ≤ 1 := by
      exact (div_le_one (by positivity)).2 (by nlinarith [sq_nonneg (f x / a k)])
    rw [Real.norm_eq_abs, abs_of_nonneg hc_nonneg]
    exact mul_le_of_le_one_left (norm_nonneg _) hc_le
  have hg_energy_le (k : ℕ) :
      ∫⁻ x, ‖fderiv ℝ (g k) x‖ₑ ^ 2 ∂μ ≤
        ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2 ∂μ := by
    apply lintegral_mono
    intro x
    have hen : ‖fderiv ℝ (g k) x‖ₑ ≤ ‖fderiv ℝ f x‖ₑ := by
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_le_coe]
      exact_mod_cast hg_fderiv_norm_le k x
    exact pow_le_pow_left₀ (by positivity) hen 2
  have hg_deriv_mem (k : ℕ) : MemLp (fun x => fderiv ℝ (g k) x) 2 μ := by
    apply memLp_fderiv_of_finite_energy (hg_diff k)
    exact (hg_energy_le k).trans_lt (by simpa [μ] using henergy)
  have hg_poincare (k : ℕ) :
      evariance (g k) μ ≤ ∫⁻ x, ‖fderiv ℝ (g k) x‖ₑ ^ 2 ∂μ := by
    apply gaussianPoincare_memW12
    · exact ⟨hg_mem k, hg_deriv_mem k⟩
    · exact (hg_diff k).differentiable (by norm_num)
    · exact (hg_diff k).continuous_fderiv (by norm_num)
  have hg_var_le (k : ℕ) :
      evariance (g k) μ ≤ ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2 ∂μ :=
    (hg_poincare k).trans (hg_energy_le k)
  have hg_tendsto (x : EuclideanSpace ℝ (Fin n)) :
      Tendsto (fun k => g k x) atTop (nhds (f x)) := by
    simpa only [g, a] using tendsto_nat_mul_arctan_div (f x)
  have hpair_le (k : ℕ) :
      ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          ‖g k p.1 - g k p.2‖ₑ ^ 2 ∂(μ.prod μ) ≤
        2 * ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2 ∂μ := by
    rw [lintegral_pair_sub_sq_eq_two_evariance (hg_mem k)]
    gcongr
    exact hg_var_le k
  have hpair_tendsto (p :
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
      Tendsto (fun k => ‖g k p.1 - g k p.2‖ₑ ^ 2) atTop
        (nhds (‖f p.1 - f p.2‖ₑ ^ 2)) :=
    ENNReal.Tendsto.pow (((hg_tendsto p.1).sub (hg_tendsto p.2)).enorm)
  have hpair_meas (k : ℕ) : Measurable (fun p :
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ‖g k p.1 - g k p.2‖ₑ ^ 2) := by
    exact ((ENNReal.continuous_pow 2).comp
      (((hg_diff k).continuous.comp continuous_fst).sub
        ((hg_diff k).continuous.comp continuous_snd)).enorm).measurable
  have hpair_bound :
      ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          ‖f p.1 - f p.2‖ₑ ^ 2 ∂(μ.prod μ) ≤
        2 * ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2 ∂μ := by
    calc
      _ = ∫⁻ p, liminf (fun k => ‖g k p.1 - g k p.2‖ₑ ^ 2) atTop
          ∂(μ.prod μ) := by
        apply lintegral_congr
        intro p
        exact (hpair_tendsto p).liminf_eq.symm
      _ ≤ liminf (fun k => ∫⁻ p, ‖g k p.1 - g k p.2‖ₑ ^ 2 ∂(μ.prod μ))
          atTop := lintegral_liminf_le hpair_meas
      _ ≤ 2 * ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2 ∂μ := by
        refine (liminf_le_limsup).trans ?_
        exact limsup_le_of_le (f := atTop)
          (u := fun k => ∫⁻ p, ‖g k p.1 - g k p.2‖ₑ ^ 2 ∂(μ.prod μ))
          (a := 2 * ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2 ∂μ)
          (hf := by isBoundedDefault) (Eventually.of_forall hpair_le)
  have hpair_lt :
      ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          ‖f p.1 - f p.2‖ₑ ^ 2 ∂(μ.prod μ) < ⊤ := by
    exact hpair_bound.trans_lt (ENNReal.mul_lt_top (by norm_num) (by simpa [μ] using henergy))
  have hpair_mem : MemLp
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        f p.1 - f p.2) 2 (μ.prod μ) := by
    have hmeas : AEStronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          f p.1 - f p.2) (μ.prod μ) :=
      ((hf.continuous.comp continuous_fst).sub
        (hf.continuous.comp continuous_snd)).aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq hmeas]
    refine ⟨hmeas.pow 2, ?_⟩
    change (∫⁻ p, ‖(f p.1 - f p.2) ^ 2‖ₑ ∂(μ.prod μ)) < ⊤
    simpa only [enorm_pow] using hpair_lt
  have hslices : ∀ᵐ y ∂μ,
      Integrable (fun x => (f x - f y) ^ 2) μ :=
    hpair_mem.integrable_sq.prod_left_ae
  obtain ⟨y, hy⟩ := hslices.exists
  have hcenter : MemLp (fun x => f x - f y) 2 μ := by
    have hmeas : AEStronglyMeasurable (fun x => f x - f y) μ :=
      (hf.continuous.sub continuous_const).aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq hmeas]
    exact hy
  have hsum := hcenter.add (memLp_const (p := 2) (μ := μ) (f y))
  have hfinal : MemLp f 2 μ := by
    convert hsum using 1
    ext x
    exact (sub_add_cancel (f x) (f y)).symm
  simpa [μ] using hfinal

/-- Statement of `Muon.External.GaussianPoincare`. -/
theorem gaussianPoincare :
    ∀ n : ℕ, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
    ContDiff ℝ 1 f →
    ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) < ⊤ →
      evariance f (stdGaussian (EuclideanSpace ℝ (Fin n)))
        ≤ ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  intro n f hf henergy
  rw [stdGaussian_eq_stdGaussianE] at henergy ⊢
  apply gaussianPoincare_memW12
  · exact ⟨memLp_of_finite_gaussian_energy hf henergy,
      memLp_fderiv_of_finite_energy hf henergy⟩
  · exact hf.differentiable (by norm_num)
  · exact hf.continuous_fderiv (by norm_num)

end GaussianFoundations
