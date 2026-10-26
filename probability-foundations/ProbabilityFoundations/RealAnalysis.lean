import Mathlib

/-!
# Real-analysis helpers (Foundations, work package L-0.5b)

Generic real-analysis facts used without citation by the appendix sections
(source of record: snapshot `cr-2026-10-22`).

* one-sided convolution on `[0,∞)` and its triangle Fubini identities, used by
  Appendix H (`sections/07-phase-comparison/section.tex`, `eqn:app-phase-volterra`,
  `lem:app-phase-mass`, `lem:app-phase-square`);
* Chebyshev's integral inequality, unimodal sum–integral comparison, elementary
  inequalities (H §4 table of the section card);
* the half-line Beta integral (DLMF 5.12.3, `Muon.External.BetaHalfLine`, proved
  here rather than certified) and its instances used by F, G, H.

Only Mathlib is imported. Statements are exact; proofs are `sorry` pending the
proof cards listed in the interface report.
-/

open MeasureTheory Set intervalIntegral

namespace ProbabilityFoundations

/-! ## One-sided convolution -/

/-- One-sided convolution on `[0,∞)`: `(f ⋆ g)(t) = ∫_0^t f(t-s) g(s) ds`.
Matches the Volterra convolution `k * f` of Appendix H up to the substitution
`s ↦ t - s`, which exchanges the roles of the two factors. -/
noncomputable def oneSidedConv (f g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, f (t - s) * g s

private theorem osc_inner_eq {f g : ℝ → ℝ} {T u : ℝ} (hu : u ∈ Icc (0:ℝ) T) :
    (∫ s in (0:ℝ)..u, f (u - s) * g s) =
      ∫ s, (Icc (0:ℝ) T).indicator g s * (Icc (0:ℝ) T).indicator f (u - s) := by
  have hzero : ∀ s ∉ Icc (0:ℝ) u, (Icc (0:ℝ) T).indicator g s * (Icc (0:ℝ) T).indicator f (u - s) = 0 := by
    intro s hs
    rcases lt_or_ge s 0 with h1 | h1
    · have hG0 : (Icc (0:ℝ) T).indicator g s = 0 :=
        indicator_of_notMem (fun h => by linarith [h.1]) g
      simp [hG0]
    · have hu' : u < s := by
        by_contra hc
        exact hs ⟨h1, not_lt.mp hc⟩
      have hF0 : (Icc (0:ℝ) T).indicator f (u - s) = 0 :=
        indicator_of_notMem (fun h => by linarith [h.1]) f
      simp [hF0]
  have hA := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
    (s := Icc (0:ℝ) u)
    (f := fun s => (Icc (0:ℝ) T).indicator g s * (Icc (0:ℝ) T).indicator f (u - s)) hzero
  rw [intervalIntegral.integral_of_le hu.1, integral_Icc_eq_integral_Ioc.symm, ← hA]
  refine setIntegral_congr_fun measurableSet_Icc (fun s hs => ?_)
  have hsT : s ∈ Icc (0:ℝ) T := ⟨hs.1, hs.2.trans hu.2⟩
  have huT : u - s ∈ Icc (0:ℝ) T := ⟨by linarith [hs.2], by linarith [hs.1, hu.2]⟩
  show f (u - s) * g s = _
  rw [indicator_of_mem huT, indicator_of_mem hsT, mul_comm]

private theorem osc_bound {k : ℝ → ℝ} (hk : ContinuousOn k (Ici 0)) (t : ℝ) :
    ∃ C, ∀ x, ‖(Icc (0:ℝ) t).indicator k x‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hk.mono Icc_subset_Ici_self)
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : x ∈ Icc (0:ℝ) t
  · rw [indicator_of_mem hx]; exact (hC x hx).trans (le_max_left _ _)
  · rw [indicator_of_notMem hx]; simp

open scoped Convolution in
private theorem osc_assoc_aux {f g h : ℝ → ℝ}
    (hf : ContinuousOn f (Ici 0)) (hg : ContinuousOn g (Ici 0))
    (hh : ContinuousOn h (Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    oneSidedConv (oneSidedConv f g) h t = oneSidedConv f (oneSidedConv g h) t := by
  set F : ℝ → ℝ := (Icc 0 t).indicator f with hFdef
  set G : ℝ → ℝ := (Icc 0 t).indicator g with hGdef
  set H : ℝ → ℝ := (Icc 0 t).indicator h with hHdef
  have hI : ∀ {k : ℝ → ℝ}, ContinuousOn k (Ici 0) → Integrable ((Icc (0:ℝ) t).indicator k) :=
    fun hk => ((hk.mono Icc_subset_Ici_self).integrableOn_compact
      isCompact_Icc).integrable_indicator measurableSet_Icc
  have hFi : Integrable F := hI hf
  have hGi : Integrable G := hI hg
  have hHi : Integrable H := hI hh
  obtain ⟨CF, hCF⟩ := osc_bound hf t
  have ht0 : t ∈ Icc (0:ℝ) t := ⟨ht, le_rfl⟩
  have hL : ∀ x y z : ℝ, (ContinuousLinearMap.mul ℝ ℝ) ((ContinuousLinearMap.mul ℝ ℝ) x y) z
      = (ContinuousLinearMap.mul ℝ ℝ) x ((ContinuousLinearMap.mul ℝ ℝ) y z) := by
    intro x y z; simp [mul_assoc]
  have hassoc : ((H ⋆[ContinuousLinearMap.mul ℝ ℝ] G) ⋆[ContinuousLinearMap.mul ℝ ℝ] F) t
      = (H ⋆[ContinuousLinearMap.mul ℝ ℝ] (G ⋆[ContinuousLinearMap.mul ℝ ℝ] F)) t := by
    refine convolution_assoc' (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
      (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ) hL
      (hHi.ae_convolution_exists _ hGi) (hGi.ae_convolution_exists _ hFi) ?_
    have h1 := hHi.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hGi
    have h2 : Integrable (fun p : ℝ × ℝ => F (t - p.1) * (H p.2 * G (p.1 - p.2)))
        (volume.prod volume) := by
      have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => F (t - p.1)) (volume.prod volume) := by
        have hm0 : AEStronglyMeasurable (fun x : ℝ => F (t - x)) (volume : Measure ℝ) :=
          hFi.aestronglyMeasurable.comp_quasiMeasurePreserving
            (quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure ℝ) t)
        exact hm0.comp_quasiMeasurePreserving
          (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)))
      exact (Integrable.bdd_mul h1 hm (ae_of_all _ fun p => hCF _))
    refine h2.congr (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, ContinuousLinearMap.mul_apply']
    ring
  have hLHS : oneSidedConv (oneSidedConv f g) h t =
      (H ⋆[ContinuousLinearMap.mul ℝ ℝ] (G ⋆[ContinuousLinearMap.mul ℝ ℝ] F)) t := by
    unfold oneSidedConv
    rw [osc_inner_eq (f := fun u => ∫ s in (0:ℝ)..u, f (u - s) * g s) (g := h) ht0]
    rw [convolution_def]
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    simp only [ContinuousLinearMap.mul_apply']
    by_cases hr : r ∈ Icc (0:ℝ) t
    · have htr : t - r ∈ Icc (0:ℝ) t := ⟨by linarith [hr.2], by linarith [hr.1]⟩
      congr 1
      rw [indicator_of_mem htr, convolution_def]
      rw [osc_inner_eq (f := f) (g := g) htr]
      simp only [ContinuousLinearMap.mul_apply']
      rfl
    · have h1 : (Icc (0:ℝ) t).indicator h r = 0 := indicator_of_notMem hr h
      have h2 : H r = 0 := indicator_of_notMem hr h
      simp only [h1, h2, zero_mul]
  have hRHS : oneSidedConv f (oneSidedConv g h) t =
      ((H ⋆[ContinuousLinearMap.mul ℝ ℝ] G) ⋆[ContinuousLinearMap.mul ℝ ℝ] F) t := by
    unfold oneSidedConv
    rw [osc_inner_eq (f := f) (g := fun s => ∫ r in (0:ℝ)..s, g (s - r) * h r) ht0]
    rw [convolution_def]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    simp only [ContinuousLinearMap.mul_apply']
    by_cases hs : s ∈ Icc (0:ℝ) t
    · congr 1
      rw [indicator_of_mem hs, convolution_def]
      rw [osc_inner_eq (f := g) (g := h) hs]
      simp only [ContinuousLinearMap.mul_apply']
      rfl
    · have h1 : (Icc (0:ℝ) t).indicator (fun s => ∫ r in (0:ℝ)..s, g (s - r) * h r) s = 0 :=
        indicator_of_notMem hs _
      have hF0 : (Icc (0:ℝ) t).indicator f (t - s) = 0 :=
        indicator_of_notMem (fun hm => hs ⟨by linarith [hm.2], by linarith [hm.1]⟩) f
      have hF1 : F (t - s) = 0 := hF0
      simp only [h1, hF0, hF1, mul_zero]
  rw [hLHS, hRHS, hassoc]

/-- Triangle Fubini, associativity: `(f ⋆ g) ⋆ h = f ⋆ (g ⋆ h)` on `[0,∞)` for
continuous `f`, `g`, `h` on `[0,∞)`. The integrand is continuous on the compact
triangle `{0 ≤ r ≤ s ≤ t}`. -/
theorem oneSidedConv_assoc {f g h : ℝ → ℝ}
    (hf : ContinuousOn f (Ici 0)) (hg : ContinuousOn g (Ici 0))
    (hh : ContinuousOn h (Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    oneSidedConv (oneSidedConv f g) h t = oneSidedConv f (oneSidedConv g h) t := by
  exact osc_assoc_aux hf hg hh ht

/-- Triangle Fubini, exchange of order: for `f` locally integrable on `[0,∞)` and
`g` continuous on `[0,∞)`, and `T ≥ 0`,
`∫_0^T (f ⋆ g)(u) du = ∫_0^T g(s) (∫_0^{T-s} f(w) dw) ds`.
This is the identity used in Appendix H for `∫_0^{û} (g * √Y)` (the kernel `g`
is integrable with possible singularity at `0`, and `√Y` is continuous). -/
theorem integral_oneSidedConv_eq {f g : ℝ → ℝ}
    (hf : ∀ T : ℝ, IntegrableOn f (Ioc 0 T))
    (hg : ContinuousOn g (Ici 0)) {T : ℝ} (hT : 0 ≤ T) :
    ∫ u in (0 : ℝ)..T, oneSidedConv f g u =
      ∫ s in (0 : ℝ)..T, g s * ∫ w in (0 : ℝ)..(T - s), f w := by
  unfold oneSidedConv
  set F : ℝ → ℝ := (Icc 0 T).indicator f with hFdef
  set G : ℝ → ℝ := (Icc 0 T).indicator g with hGdef
  have hgI : IntegrableOn g (Icc 0 T) :=
    (hg.mono Icc_subset_Ici_self).integrableOn_compact isCompact_Icc
  have hfI : IntegrableOn f (Icc 0 T) := (integrableOn_Icc_iff_integrableOn_Ioc).2 (hf T)
  have hF : Integrable F := hfI.integrable_indicator measurableSet_Icc
  have hG : Integrable G := hgI.integrable_indicator measurableSet_Icc
  have h2 : Integrable (Function.uncurry fun x t => (ContinuousLinearMap.mul ℝ ℝ) (G t) (F (x - t)))
      (volume.prod volume) := hG.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hF
  have h2'' : Integrable (Function.uncurry fun (u s : ℝ) => F (u - s) * G s) (volume.prod volume) := by
    refine h2.congr (ae_of_all _ fun p => ?_)
    simp [Function.uncurry, mul_comm]
  have hint : Integrable (Function.uncurry fun (u s : ℝ) => F (u - s) * G s)
      ((volume.restrict (Icc (0:ℝ) T)).prod volume) :=
    h2''.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  -- pointwise identity for the inner integral
  have hstep1 : ∀ u ∈ Icc (0:ℝ) T, (∫ s in (0:ℝ)..u, f (u - s) * g s) = ∫ s, F (u - s) * G s := by
    intro u hu
    have hzero : ∀ s ∉ Icc (0:ℝ) u, F (u - s) * G s = 0 := by
      intro s hs
      rcases lt_or_ge s 0 with h1 | h1
      · have hG0 : G s = 0 := indicator_of_notMem (fun h => by linarith [h.1]) g
        simp [hG0]
      · have hu' : u < s := by
          by_contra hc
          exact hs ⟨h1, not_lt.mp hc⟩
        have hF0 : F (u - s) = 0 := indicator_of_notMem (fun h => by linarith [h.1]) f
        simp [hF0]
    have hA := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (s := Icc (0:ℝ) u) (f := fun s => F (u - s) * G s) hzero
    rw [intervalIntegral.integral_of_le hu.1, integral_Icc_eq_integral_Ioc.symm, ← hA]
    refine setIntegral_congr_fun measurableSet_Icc (fun s hs => ?_)
    have hsT : s ∈ Icc (0:ℝ) T := ⟨hs.1, hs.2.trans hu.2⟩
    have huT : u - s ∈ Icc (0:ℝ) T := ⟨by linarith [hs.2], by linarith [hs.1, hu.2]⟩
    show f (u - s) * g s = (Icc 0 T).indicator f (u - s) * (Icc 0 T).indicator g s
    rw [indicator_of_mem huT, indicator_of_mem hsT]
  -- inner claim
  have hinner : ∀ s ∈ Icc (0:ℝ) T, ∫ u in Icc (0:ℝ) T, F (u - s) = ∫ w in (0:ℝ)..(T - s), f w := by
    intro s hs
    have hz : ∀ x ∈ Icc (0:ℝ) T \ Icc s T, F (x - s) = 0 := by
      intro x hx
      have hxs : x < s := by
        by_contra hc
        exact hx.2 ⟨not_lt.mp hc, hx.1.2⟩
      exact indicator_of_notMem (fun h => by linarith [h.1]) f
    have hA : ∫ u in Icc (0:ℝ) T, F (u - s) = ∫ u in Icc s T, F (u - s) :=
      (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
        (Icc_subset_Icc hs.1 le_rfl) hz)
    have hcongr : ∫ u in Icc s T, F (u - s) = ∫ u in Icc s T, f (u - s) :=
      setIntegral_congr_fun measurableSet_Icc (fun u hu => by
        show (Icc 0 T).indicator f (u - s) = f (u - s)
        exact indicator_of_mem (show u - s ∈ Icc (0:ℝ) T from ⟨by linarith [hu.1], by linarith [hu.2, hs.1]⟩) f)
    rw [hA, hcongr, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs.2]
    rw [intervalIntegral.integral_comp_sub_right (fun w => f w) s, sub_self]
  have hLHS : ∫ u in (0:ℝ)..T, (∫ s in (0:ℝ)..u, f (u - s) * g s)
      = ∫ u in Icc (0:ℝ) T, ∫ s, F (u - s) * G s := by
    rw [intervalIntegral.integral_of_le hT, integral_Icc_eq_integral_Ioc]
    exact setIntegral_congr_fun measurableSet_Ioc (fun u hu => hstep1 u ⟨hu.1.le, hu.2⟩)
  have hR : ∫ s in (0:ℝ)..T, g s * ∫ w in (0:ℝ)..(T - s), f w
      = ∫ s in Icc (0:ℝ) T, g s * ∫ w in (0:ℝ)..(T - s), f w := by
    rw [intervalIntegral.integral_of_le hT, integral_Icc_eq_integral_Ioc]
  have hzeroG : ∀ s ∉ Icc (0:ℝ) T, (∫ u in Icc (0:ℝ) T, F (u - s)) * G s = 0 := by
    intro s hs
    have : G s = 0 := indicator_of_notMem hs g
    rw [this, mul_zero]
  rw [hLHS, integral_integral_swap hint, hR]
  simp_rw [MeasureTheory.integral_mul_const]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzeroG]
  refine setIntegral_congr_fun measurableSet_Icc (fun s hs => ?_)
  show (∫ u in Icc (0:ℝ) T, F (u - s)) * (Icc 0 T).indicator g s = g s * ∫ w in (0:ℝ)..(T - s), f w
  rw [hinner s hs, indicator_of_mem hs g, mul_comm]

/-! ## Chebyshev's integral inequality -/

private lemma cheb_bound {u : ℝ → ℝ} {a b lo hi : ℝ}
    (h : ∀ x ∈ Ioc a b, lo ≤ u x ∧ u x ≤ hi) :
    ∀ᵐ x ∂(volume.restrict (Ioc a b)), ‖u x‖ ≤ |lo| + |hi| := by
  refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_le]
  have := h x hx
  constructor <;> linarith [neg_abs_le lo, le_abs_self hi, abs_nonneg lo, abs_nonneg hi]

private lemma cheb_inner {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntegrableOn f (Ioc a b)) (hg : IntegrableOn g (Ioc a b))
    (hfg : IntegrableOn (fun x => f x * g x) (Ioc a b)) (x : ℝ) :
    ∫ y in Ioc a b, (f x - f y) * (g x - g y)
      = (b - a) * (f x * g x) - f x * (∫ y in Ioc a b, g y)
        - g x * (∫ y in Ioc a b, f y) + ∫ y in Ioc a b, f y * g y := by
  have e : ∀ y, (f x - f y) * (g x - g y)
      = ((f x * g x - f x * g y) - g x * f y) + f y * g y := fun y => by ring
  simp only [e]
  have i1 : IntegrableOn (fun y => f x * g x - f x * g y) (Ioc a b) :=
    (integrable_const _).sub (hg.const_mul (f x))
  have i2 : IntegrableOn (fun y => g x * f y) (Ioc a b) := hf.const_mul (g x)
  have i12 : IntegrableOn (fun y => f x * g x - f x * g y - g x * f y) (Ioc a b) := i1.sub i2
  have j1 : ∫ y in Ioc a b, (f x * g x - f x * g y - g x * f y + f y * g y)
      = (∫ y in Ioc a b, (f x * g x - f x * g y - g x * f y)) + ∫ y in Ioc a b, f y * g y :=
    integral_add i12 hfg
  have j2 : ∫ y in Ioc a b, (f x * g x - f x * g y - g x * f y)
      = (∫ y in Ioc a b, (f x * g x - f x * g y)) - ∫ y in Ioc a b, g x * f y :=
    integral_sub i1 i2
  have j3 : ∫ y in Ioc a b, (f x * g x - f x * g y)
      = (∫ y in Ioc a b, f x * g x) - ∫ y in Ioc a b, f x * g y :=
    integral_sub (integrable_const _) (hg.const_mul (f x))
  have j4 : ∫ y in Ioc a b, f x * g x = (b - a) * (f x * g x) := by
    rw [setIntegral_const, Real.volume_real_Ioc_of_le hab, smul_eq_mul]
  have j5 : ∫ y in Ioc a b, f x * g y = f x * ∫ y in Ioc a b, g y := integral_const_mul _ _
  have j6 : ∫ y in Ioc a b, g x * f y = g x * ∫ y in Ioc a b, f y := integral_const_mul _ _
  rw [j1, j2, j3, j4, j5, j6]

private lemma cheb_identity {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntegrableOn f (Ioc a b)) (hg : IntegrableOn g (Ioc a b))
    (hfg : IntegrableOn (fun x => f x * g x) (Ioc a b)) :
    ∫ x in Ioc a b, ∫ y in Ioc a b, (f x - f y) * (g x - g y)
      = 2 * ((b - a) * ∫ x in Ioc a b, f x * g x)
        - 2 * ((∫ x in Ioc a b, f x) * ∫ x in Ioc a b, g x) := by
  simp_rw [cheb_inner hab hf hg hfg]
  set F := ∫ x in Ioc a b, f x with hF
  set G := ∫ x in Ioc a b, g x with hG
  set P := ∫ x in Ioc a b, f x * g x with hP
  have k1 : IntegrableOn (fun x => (b - a) * (f x * g x) - f x * G) (Ioc a b) :=
    (hfg.const_mul _).sub (hf.mul_const _)
  have k2 : IntegrableOn (fun x => (b - a) * (f x * g x) - f x * G - g x * F) (Ioc a b) :=
    k1.sub (hg.mul_const _)
  have m0 : ∫ x in Ioc a b, ((b - a) * (f x * g x) - f x * G - g x * F + P)
      = (∫ x in Ioc a b, ((b - a) * (f x * g x) - f x * G - g x * F)) + ∫ x in Ioc a b, P :=
    integral_add k2 (integrable_const _)
  have m1 : ∫ x in Ioc a b, ((b - a) * (f x * g x) - f x * G - g x * F)
      = (∫ x in Ioc a b, ((b - a) * (f x * g x) - f x * G)) - ∫ x in Ioc a b, g x * F :=
    integral_sub k1 (hg.mul_const _)
  have m2 : ∫ x in Ioc a b, ((b - a) * (f x * g x) - f x * G)
      = (∫ x in Ioc a b, (b - a) * (f x * g x)) - ∫ x in Ioc a b, f x * G :=
    integral_sub (hfg.const_mul _) (hf.mul_const _)
  have m3 : ∫ x in Ioc a b, (b - a) * (f x * g x) = (b - a) * P := integral_const_mul _ _
  have m4 : ∫ x in Ioc a b, f x * G = F * G := integral_mul_const _ _
  have m5 : ∫ x in Ioc a b, g x * F = G * F := integral_mul_const _ _
  have m6 : ∫ x in Ioc a b, P = (b - a) * P := by
    rw [setIntegral_const, Real.volume_real_Ioc_of_le hab, smul_eq_mul]
  rw [m0, m1, m2, m3, m4, m5, m6]
  ring

/-- Chebyshev's integral inequality, oppositely monotone pair (the form used in
`lem:app-phase-mass`): for `f` antitone and `g` monotone on `[a,b]`,
`(b-a) ∫_a^b f g ≤ (∫_a^b f) (∫_a^b g)`. Integrability is automatic from monotonicity. -/
theorem chebyshev_integral_opposite {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : AntitoneOn f (Icc a b)) (hg : MonotoneOn g (Icc a b)) :
    (b - a) * ∫ x in a..b, f x * g x ≤ (∫ x in a..b, f x) * ∫ x in a..b, g x := by
  have hf' : AntitoneOn f (uIcc a b) := by rw [uIcc_of_le hab]; exact hf
  have hg' : MonotoneOn g (uIcc a b) := by rw [uIcc_of_le hab]; exact hg
  have hfI : IntegrableOn f (Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hf'.intervalIntegrable
  have hgI : IntegrableOn g (Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hg'.intervalIntegrable
  have hfg : IntegrableOn (fun x => f x * g x) (Ioc a b) := by
    refine hfI.mul_bdd hgI.aestronglyMeasurable (cheb_bound (lo := g a) (hi := g b) ?_)
    intro x hx
    exact ⟨hg (left_mem_Icc.2 hab) ⟨hx.1.le, hx.2⟩ hx.1.le,
      hg ⟨hx.1.le, hx.2⟩ (right_mem_Icc.2 hab) hx.2⟩
  have hsign : ∫ x in Ioc a b, ∫ y in Ioc a b, (f x - f y) * (g x - g y) ≤ 0 := by
    refine setIntegral_nonpos measurableSet_Ioc (fun x hx => ?_)
    refine setIntegral_nonpos measurableSet_Ioc (fun y hy => ?_)
    have hx' : x ∈ Icc a b := Ioc_subset_Icc_self hx
    have hy' : y ∈ Icc a b := Ioc_subset_Icc_self hy
    rcases le_total x y with h | h
    · have h1 : f y ≤ f x := hf hx' hy' h
      have h2 : g x ≤ g y := hg hx' hy' h
      nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]
    · have h1 : f x ≤ f y := hf hy' hx' h
      have h2 : g y ≤ g x := hg hy' hx' h
      nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]
  have hid := cheb_identity hab hfI hgI hfg
  simp only [intervalIntegral.integral_of_le hab]
  linarith

/-- Chebyshev's integral inequality, similarly monotone pair: for `f`, `g` both
nondecreasing on `[a,b]`, `(∫_a^b f) (∫_a^b g) ≤ (b-a) ∫_a^b f g`. -/
theorem chebyshev_integral_same {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : MonotoneOn f (Icc a b)) (hg : MonotoneOn g (Icc a b)) :
    (∫ x in a..b, f x) * (∫ x in a..b, g x) ≤ (b - a) * ∫ x in a..b, f x * g x := by
  have hf' : MonotoneOn f (uIcc a b) := by rw [uIcc_of_le hab]; exact hf
  have hg' : MonotoneOn g (uIcc a b) := by rw [uIcc_of_le hab]; exact hg
  have hfI : IntegrableOn f (Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hf'.intervalIntegrable
  have hgI : IntegrableOn g (Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hg'.intervalIntegrable
  have hfg : IntegrableOn (fun x => f x * g x) (Ioc a b) := by
    refine hfI.mul_bdd hgI.aestronglyMeasurable (cheb_bound (lo := g a) (hi := g b) ?_)
    intro x hx
    exact ⟨hg (left_mem_Icc.2 hab) ⟨hx.1.le, hx.2⟩ hx.1.le,
      hg ⟨hx.1.le, hx.2⟩ (right_mem_Icc.2 hab) hx.2⟩
  have hsign : 0 ≤ ∫ x in Ioc a b, ∫ y in Ioc a b, (f x - f y) * (g x - g y) := by
    refine setIntegral_nonneg measurableSet_Ioc (fun x hx => ?_)
    refine setIntegral_nonneg measurableSet_Ioc (fun y hy => ?_)
    have hx' : x ∈ Icc a b := Ioc_subset_Icc_self hx
    have hy' : y ∈ Icc a b := Ioc_subset_Icc_self hy
    rcases le_total x y with h | h
    · have h1 : f x ≤ f y := hf hx' hy' h
      have h2 : g x ≤ g y := hg hx' hy' h
      nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]
    · have h1 : f y ≤ f x := hf hy' hx' h
      have h2 : g y ≤ g x := hg hy' hx' h
      nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]
  have hid := cheb_identity hab hfI hgI hfg
  simp only [intervalIntegral.integral_of_le hab]
  linarith

/-! ## Unimodal sum–integral comparison -/

private lemma unimodal_tele {g : ℕ → ℝ} {a n : ℕ} (h : a ≤ n) :
    ∑ i ∈ Finset.Ico a n, (g (i + 1) - g i) = g n - g a := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hn ih => rw [Finset.sum_Ico_succ_top hn, ih]; ring

/-- Unimodal sum–integral comparison. Let `f ≥ 0` be nondecreasing on `[a,m]` and
nonincreasing on `[m,b]` for integers `a ≤ m ≤ b`, and bounded above by `M` on `[a,b]`.
Then `|∑_{k=a}^{b} f(k) - ∫_a^b f| ≤ M`.
This implies the constant `2 max f` of `lem:app-phase-variation` (there `a = 0`,
`f(0) = 0`, and the sum runs over `1 ≤ k ≤ N`). -/
theorem unimodal_sum_sub_integral_le {f : ℝ → ℝ} {a m b : ℕ}
    (ham : a ≤ m) (hmb : m ≤ b)
    (hnonneg : ∀ x ∈ Icc (a : ℝ) (b : ℝ), 0 ≤ f x)
    (hup : MonotoneOn f (Icc (a : ℝ) (m : ℝ)))
    (hdown : AntitoneOn f (Icc (m : ℝ) (b : ℝ)))
    {M : ℝ} (hM : ∀ x ∈ Icc (a : ℝ) (b : ℝ), f x ≤ M) :
    |(∑ k ∈ Finset.Icc a b, f (k : ℝ)) - ∫ x in (a : ℝ)..(b : ℝ), f x| ≤ M := by
  have ham' : (a : ℝ) ≤ (m : ℝ) := Nat.cast_le.2 ham
  have hmb' : (m : ℝ) ≤ (b : ℝ) := Nat.cast_le.2 hmb
  have hab' : (a : ℝ) ≤ (b : ℝ) := ham'.trans hmb'
  have hfa : 0 ≤ f (a : ℝ) := hnonneg a ⟨le_rfl, hab'⟩
  have hfb : 0 ≤ f (b : ℝ) := hnonneg b ⟨hab', le_rfl⟩
  have hfm : 0 ≤ f (m : ℝ) := hnonneg m ⟨ham', hmb'⟩
  have hfmM : f (m : ℝ) ≤ M := hM m ⟨ham', hmb'⟩
  have hup' : MonotoneOn f (uIcc (a : ℝ) (m : ℝ)) := by rw [uIcc_of_le ham']; exact hup
  have hdown' : AntitoneOn f (uIcc (m : ℝ) (b : ℝ)) := by rw [uIcc_of_le hmb']; exact hdown
  have hI1 : IntervalIntegrable f volume (a : ℝ) (m : ℝ) := hup'.intervalIntegrable
  have hI2 : IntervalIntegrable f volume (m : ℝ) (b : ℝ) := hdown'.intervalIntegrable
  have hsplit : ∫ x in (a : ℝ)..(b : ℝ), f x
      = (∫ x in (a : ℝ)..(m : ℝ), f x) + ∫ x in (m : ℝ)..(b : ℝ), f x :=
    (intervalIntegral.integral_add_adjacent_intervals hI1 hI2).symm
  have hL1 : ∑ i ∈ Finset.Ico a m, f (i : ℝ) ≤ ∫ x in (a : ℝ)..(m : ℝ), f x :=
    MonotoneOn.sum_le_integral_Ico ham hup
  have hL2 : ∫ x in (a : ℝ)..(m : ℝ), f x ≤ ∑ i ∈ Finset.Ico a m, f ((i + 1 : ℕ) : ℝ) :=
    MonotoneOn.integral_le_sum_Ico ham hup
  have hR1 : ∫ x in (m : ℝ)..(b : ℝ), f x ≤ ∑ i ∈ Finset.Ico m b, f (i : ℝ) :=
    AntitoneOn.integral_le_sum_Ico hmb hdown
  have hR2 : ∑ i ∈ Finset.Ico m b, f ((i + 1 : ℕ) : ℝ) ≤ ∫ x in (m : ℝ)..(b : ℝ), f x :=
    AntitoneOn.sum_le_integral_Ico hmb hdown
  have tL : ∑ i ∈ Finset.Ico a m, f ((i + 1 : ℕ) : ℝ)
      = ∑ i ∈ Finset.Ico a m, f (i : ℝ) + (f (m : ℝ) - f (a : ℝ)) := by
    have key := unimodal_tele (g := fun i : ℕ => f (i : ℝ)) ham
    rw [Finset.sum_sub_distrib] at key
    linarith
  have tR : ∑ i ∈ Finset.Ico m b, f ((i + 1 : ℕ) : ℝ)
      = ∑ i ∈ Finset.Ico m b, f (i : ℝ) + (f (b : ℝ) - f (m : ℝ)) := by
    have key := unimodal_tele (g := fun i : ℕ => f (i : ℝ)) hmb
    rw [Finset.sum_sub_distrib] at key
    linarith
  have hS : ∑ k ∈ Finset.Icc a b, f (k : ℝ)
      = ∑ i ∈ Finset.Ico a m, f (i : ℝ) + ∑ i ∈ Finset.Ico m b, f (i : ℝ) + f (b : ℝ) := by
    have hIcc : Finset.Icc a b = Finset.Ico a (b + 1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hIcc, ← Finset.sum_Ico_consecutive _ ham (Nat.le_succ_of_le hmb),
      Finset.sum_Ico_succ_top hmb]
    ring
  rw [hS, hsplit, abs_le]
  constructor <;> linarith


/-! ## Elementary inequalities (H §4 table) -/

/-- `b e^{-bs} ≤ 1/(e s)` for `b, s > 0` (`section.tex` l.230). -/
theorem mul_exp_neg_le_inv_exp_one_mul {b s : ℝ} (hb : 0 < b) (hs : 0 < s) :
    b * Real.exp (-(b * s)) ≤ 1 / (Real.exp 1 * s) := by
  have h1 := Real.mul_exp_neg_le_exp_neg_one (b * s)
  have hexp : Real.exp (-1) = 1 / Real.exp 1 := by rw [Real.exp_neg, one_div]
  rw [hexp] at h1
  calc b * Real.exp (-(b * s)) = (b * s * Real.exp (-(b * s))) / s := by field_simp
    _ ≤ (1 / Real.exp 1) / s := div_le_div_of_nonneg_right h1 hs.le
    _ = 1 / (Real.exp 1 * s) := by rw [div_div]

/-- `√(1+x) ≤ 1 + x/2` for `x ≥ 0` (`section.tex` l.494). -/
theorem sqrt_one_add_le {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (1 + x) ≤ 1 + x / 2 := by
  rw [Real.sqrt_le_iff]
  exact ⟨by linarith, by nlinarith [sq_nonneg x]⟩

private theorem sqrt_add_le_sqrt_add_sqrt_aux {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy,
    mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

/-- `√x - √y ≤ √(x - y)` for `x ≥ y ≥ 0` (`section.tex` l.1980). -/
theorem sqrt_sub_sqrt_le {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) :
    Real.sqrt x - Real.sqrt y ≤ Real.sqrt (x - y) := by
  have h := sqrt_add_le_sqrt_add_sqrt_aux (x := y) (y := x - y) hy (by linarith)
  rw [show y + (x - y) = x by ring] at h
  linarith

/-- `√(x + y) ≤ √x + √y` for `x, y ≥ 0` (`section.tex` l.1985, 2158). -/
theorem sqrt_add_le_sqrt_add_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y :=
  sqrt_add_le_sqrt_add_sqrt_aux hx hy

/-- `√(max_i x_i) ≤ ∑_i √(x_i)` for a finite nonempty family of nonnegative reals
(card H §4, elementary square-root row). -/
theorem sqrt_sup'_le_sum_sqrt {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) :
    Real.sqrt (s.sup' hs x) ≤ ∑ i ∈ s, Real.sqrt (x i) := by
  obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup' hs x
  rw [hjeq]
  exact Finset.single_le_sum (f := fun i => Real.sqrt (x i))
    (fun i _ => Real.sqrt_nonneg _) hj

/-- `|log(1-x)| ≤ 2x` for `0 < x ≤ 1/2` (`section.tex` l.633). -/
theorem abs_log_one_sub_le {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 2) :
    |Real.log (1 - x)| ≤ 2 * x := by
  have hpos : 0 < 1 - x := by linarith
  have hlog_le : Real.log (1 - x) ≤ 0 := Real.log_nonpos hpos.le (by linarith)
  have hlow : 1 - (1 - x)⁻¹ ≤ Real.log (1 - x) := Real.one_sub_inv_le_log_of_pos hpos
  have hinv_le : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    nlinarith
  rw [abs_of_nonpos hlog_le]
  linarith

/-- `√z · log(1/z) ≤ 2/e` for `0 < z ≤ 1` (`section.tex` l.2458, 2965). -/
theorem sqrt_mul_log_inv_le {z : ℝ} (hz0 : 0 < z) (hz : z ≤ 1) :
    Real.sqrt z * Real.log (1 / z) ≤ 2 / Real.exp 1 := by
  have htpos : 0 < Real.sqrt z := Real.sqrt_pos.2 hz0
  have hsq : Real.sqrt z ^ 2 = z := Real.sq_sqrt hz0.le
  have hdiv : 1 / z = (1 / Real.sqrt z) ^ 2 := by rw [div_pow, one_pow, hsq]
  have hlog : Real.log (1 / z) = 2 * Real.log (1 / Real.sqrt z) := by
    rw [hdiv, Real.log_pow]; norm_num
  have hkey : ∀ u : ℝ, 0 < u → Real.log u ≤ u / Real.exp 1 := by
    intro u hu
    have h := Real.log_le_sub_one_of_pos (show 0 < u / Real.exp 1 by positivity)
    rw [Real.log_div hu.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
    linarith
  have hu := hkey (1 / Real.sqrt z) (by positivity)
  have hmul : Real.sqrt z * (1 / Real.sqrt z / Real.exp 1) = 1 / Real.exp 1 := by
    field_simp
  have hm := mul_le_mul_of_nonneg_left hu htpos.le
  have hfin : Real.sqrt z * Real.log (1 / Real.sqrt z) ≤ 1 / Real.exp 1 := by
    linarith [hm, hmul]
  rw [hlog]
  calc Real.sqrt z * (2 * Real.log (1 / Real.sqrt z))
      = 2 * (Real.sqrt z * Real.log (1 / Real.sqrt z)) := by ring
    _ ≤ 2 * (1 / Real.exp 1) := by linarith [hfin]
    _ = 2 / Real.exp 1 := by ring

/-- `(cx)^n / n! ≤ e^{cx}` for `c > 0`, `x ≥ 0`, `n : ℕ` (`section.tex` l.2731).
Stated on `x ≥ 0` only, the range where H applies it. -/
theorem exp_pow_div_factorial_le {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) (n : ℕ) :
    (c * x) ^ n / (n.factorial : ℝ) ≤ Real.exp (c * x) :=
  Real.pow_div_factorial_le_exp (c * x) (mul_nonneg hc.le hx) n

/-- `sup_{x ≥ 1} x^{-a} log x = 1/(e a)` for `a > 0`, stated as a greatest element
(attained at `x = e^{1/a}`) (`section.tex` l.2290). -/
theorem rpow_neg_mul_log_isGreatest {a : ℝ} (ha : 0 < a) :
    IsGreatest ((fun x : ℝ => x ^ (-a) * Real.log x) '' Ici 1) (1 / (Real.exp 1 * a)) := by
  constructor
  · refine ⟨Real.exp (1 / a), ?_, ?_⟩
    · show (1:ℝ) ≤ Real.exp (1 / a)
      exact Real.one_le_exp (by positivity)
    · show Real.exp (1 / a) ^ (-a) * Real.log (Real.exp (1 / a)) = 1 / (Real.exp 1 * a)
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      have h1 : 1 / a * -a = -1 := by field_simp
      rw [h1, Real.exp_neg]
      field_simp
  · rintro y ⟨x, hx, rfl⟩
    show x ^ (-a) * Real.log x ≤ 1 / (Real.exp 1 * a)
    have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
    have hL : 0 ≤ Real.log x := Real.log_nonneg hx
    rw [Real.rpow_def_of_pos hx0]
    have hu : Real.log x * -a = -(a * Real.log x) := by ring
    rw [hu]
    have h1 : a * Real.log x ≤ Real.exp (a * Real.log x - 1) := by
      have := Real.add_one_le_exp (a * Real.log x - 1)
      linarith
    have hexp : Real.exp (a * Real.log x - 1) * Real.exp (-(a * Real.log x)) = (Real.exp 1)⁻¹ := by
      rw [← Real.exp_add, ← Real.exp_neg]
      congr 1
      ring
    have h2 : (a * Real.log x) * Real.exp (-(a * Real.log x)) ≤ (Real.exp 1)⁻¹ := by
      rw [← hexp]
      exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    rw [le_div_iff₀ (mul_pos (Real.exp_pos 1) ha)]
    have h3 : Real.exp (-(a * Real.log x)) * Real.log x * (Real.exp 1 * a)
        = Real.exp 1 * ((a * Real.log x) * Real.exp (-(a * Real.log x))) := by ring
    have h4 : Real.exp 1 * (Real.exp 1)⁻¹ = 1 := mul_inv_cancel₀ (Real.exp_pos 1).ne'
    rw [h3]
    calc _ ≤ Real.exp 1 * (Real.exp 1)⁻¹ := mul_le_mul_of_nonneg_left h2 (Real.exp_pos 1).le
      _ = 1 := h4

/-- `log(1 + c t) ≤ (1 + log max{1, c}) log(e + t)` for `c > 0`, `t ≥ 0`
(`section.tex` l.3500). -/
theorem log_one_add_mul_le {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) :
    Real.log (1 + c * t) ≤ (1 + Real.log (max 1 c)) * Real.log (Real.exp 1 + t) := by
  have hm1 : 1 ≤ max 1 c := le_max_left _ _
  have hcm : c ≤ max 1 c := le_max_right _ _
  have hm0 : 0 < max 1 c := by linarith
  have hLm : 0 ≤ Real.log (max 1 c) := Real.log_nonneg hm1
  have hE : 1 ≤ Real.log (Real.exp 1 + t) := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (le_add_of_nonneg_right ht : Real.exp 1 ≤ Real.exp 1 + t)
    rw [Real.log_exp] at h
    exact h
  have hlog1t : Real.log (1 + t) ≤ Real.log (Real.exp 1 + t) :=
    Real.log_le_log (by linarith) (by linarith [Real.add_one_le_exp (1:ℝ)])
  have hle : 1 + c * t ≤ max 1 c * (1 + t) := by
    nlinarith [mul_le_mul_of_nonneg_right hcm ht, hm1]
  have hmono : Real.log (1 + c * t) ≤ Real.log (max 1 c * (1 + t)) :=
    Real.log_le_log (by nlinarith [mul_nonneg hc.le ht]) hle
  rw [Real.log_mul hm0.ne' (by linarith)] at hmono
  nlinarith [mul_le_mul_of_nonneg_left hE hLm, hlog1t, hmono]

/-! ## Beta integral on the half line (DLMF 5.12.3) -/

/-- DLMF 5.12.3 on `(0,∞)`: for `a, b > 0`,
`∫_0^∞ t^{a-1} (1+t)^{-(a+b)} dt = Γ(a) Γ(b) / Γ(a+b)`.
Mathlib has only the `(0,1)` form `Complex.betaIntegral`
(`Analysis/SpecialFunctions/Gamma/Beta.lean`). Certificate `Muon.External.BetaHalfLine`
is replaced by this proved lemma. -/
private theorem betaUnit_real {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in Ioo (0:ℝ) 1, x ^ (a - 1) * (1 - x) ^ (b - 1) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  have h1 := ProbabilityTheory.beta_eq_betaIntegralReal a b ha hb
  have h2 : Complex.betaIntegral a b =
      ((∫ x in Ioo (0:ℝ) 1, x ^ (a - 1) * (1 - x) ^ (b - 1) : ℝ) : ℂ) := by
    unfold Complex.betaIntegral
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    refine (setIntegral_congr_fun measurableSet_Ioo (g := fun x : ℝ => ((x ^ (a - 1) * (1 - x) ^ (b - 1) : ℝ) : ℂ)) ?_).trans ?_
    · intro x hx
      have hx0 : 0 ≤ x := hx.1.le
      have hx1 : 0 ≤ 1 - x := by linarith [hx.2]
      have e1 : (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) := by push_cast; ring
      have e2 : ((a : ℂ) - 1) = ((a - 1 : ℝ) : ℂ) := by push_cast; ring
      have e3 : ((b : ℂ) - 1) = ((b - 1 : ℝ) : ℂ) := by push_cast; ring
      dsimp only
      rw [e1, e2, e3, ← Complex.ofReal_cpow hx0, ← Complex.ofReal_cpow hx1, Complex.ofReal_mul]
    · exact _root_.integral_ofReal (𝕜 := ℂ) (μ := volume.restrict (Ioo (0:ℝ) 1))
  have h3 : ProbabilityTheory.beta a b = ∫ x in Ioo (0:ℝ) 1, x ^ (a - 1) * (1 - x) ^ (b - 1) := by
    rw [h1, h2, Complex.ofReal_re]
  exact h3.symm

theorem betaHalfLine {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ t in Ioi (0 : ℝ), t ^ (a - 1) * (1 + t) ^ (-(a + b)) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  rw [← betaUnit_real ha hb]
  have himg : (fun t : ℝ => t / (1 + t)) '' Ioi 0 = Ioo 0 1 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht' : (0:ℝ) < t := ht
      exact ⟨div_pos ht' (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩
    · rintro ⟨h0, h1⟩
      have hne : (1 - x) ≠ 0 := by linarith
      refine ⟨x / (1 - x), div_pos h0 (by linarith), ?_⟩
      show x / (1 - x) / (1 + x / (1 - x)) = x
      field_simp
      ring
  have hinj : InjOn (fun t : ℝ => t / (1 + t)) (Ioi 0) := by
    intro s hs t ht h
    have hs' : (0:ℝ) < s := hs
    have ht' : (0:ℝ) < t := ht
    simp only at h
    rw [div_eq_div_iff (by linarith) (by linarith)] at h
    nlinarith
  have hderiv : ∀ t ∈ Ioi (0:ℝ),
      HasDerivWithinAt (fun t : ℝ => t / (1 + t)) (1 / (1 + t) ^ 2) (Ioi 0) t := by
    intro t ht
    have ht' : (0:ℝ) < t := ht
    have h1 : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id t
    have h2 : HasDerivAt (fun t : ℝ => 1 + t) 1 t := (hasDerivAt_id t).const_add 1
    have h3 := h1.div h2 (by linarith : (1 + t) ≠ 0)
    have h4 : HasDerivAt (fun t : ℝ => t / (1 + t)) (1 / (1 + t) ^ 2) t := by
      convert h3 using 1
      field_simp
      ring
    exact h4.hasDerivWithinAt
  have key : ∫ x in Ioo (0:ℝ) 1, x ^ (a - 1) * (1 - x) ^ (b - 1) =
      ∫ t in Ioi (0:ℝ), |1 / (1 + t) ^ 2| •
        ((t / (1 + t)) ^ (a - 1) * (1 - t / (1 + t)) ^ (b - 1)) := by
    rw [← himg]
    exact integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj _
  rw [key]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro t ht
  dsimp only
  have ht' : (0:ℝ) < t := ht
  have hu : (0:ℝ) < 1 + t := by linarith
  have hom : 1 - t / (1 + t) = 1 / (1 + t) := by field_simp; ring
  have hsplit : (1 + t) ^ (a + b) = (1 + t) ^ (a - 1) * (1 + t) ^ (b - 1) * (1 + t) ^ (2:ℝ) := by
    rw [← Real.rpow_add hu, ← Real.rpow_add hu]
    congr 1
    ring
  rw [Real.rpow_two] at hsplit
  rw [hom, smul_eq_mul, abs_of_pos (by positivity), Real.div_rpow ht'.le hu.le,
    Real.div_rpow zero_le_one hu.le, Real.one_rpow, Real.rpow_neg hu.le, hsplit]
  have p1 : (0:ℝ) < (1 + t) ^ (a - 1) := Real.rpow_pos_of_pos hu _
  have p2 : (0:ℝ) < (1 + t) ^ (b - 1) := Real.rpow_pos_of_pos hu _
  field_simp

/-- Instance `(a,b) = (1/2,1/2)`: `∫_0^∞ y^{-1/2} (1+y)^{-1} dy = π`. -/
theorem betaHalfLine_one_half_one_half :
    ∫ y in Ioi (0 : ℝ), y ^ (-(1/2:ℝ)) * (1 + y) ^ (-(1 : ℝ)) = Real.pi := by
  have h := betaHalfLine (a := 1/2) (b := 1/2) (by norm_num) (by norm_num)
  have e1 : (1/2:ℝ) - 1 = -(1/2:ℝ) := by norm_num
  have e2 : -((1/2:ℝ) + 1/2) = -(1:ℝ) := by norm_num
  rw [e1, e2] at h
  rw [h]
  have hsq : Real.Gamma (1/2:ℝ) * Real.Gamma (1/2:ℝ) = Real.pi := by
    rw [Real.Gamma_one_half_eq]
    exact Real.mul_self_sqrt Real.pi_pos.le
  have hsum : (1/2:ℝ) + 1/2 = 1 := by norm_num
  rw [hsum, Real.Gamma_one, div_one, hsq]

/-- Instance `(a,b) = (1/2,3/2)`: `∫_0^∞ y^{-1/2} (1+y)^{-2} dy = π/2`
(the ratio integral of `lem:app-phase-ratio-integral`). -/
theorem betaHalfLine_one_half_three_halves :
    ∫ y in Ioi (0 : ℝ), y ^ (-(1/2:ℝ)) * (1 + y) ^ (-(2 : ℝ)) = Real.pi / 2 := by
  have h := betaHalfLine (a := 1/2) (b := 3/2) (by norm_num) (by norm_num)
  have e1 : (1/2:ℝ) - 1 = -(1/2:ℝ) := by norm_num
  have e2 : -((1/2:ℝ) + 3/2) = -(2:ℝ) := by norm_num
  rw [e1, e2] at h
  rw [h]
  have hab : (1/2:ℝ) + 3/2 = 2 := by norm_num
  have hg32 : Real.Gamma (3/2:ℝ) = Real.sqrt Real.pi / 2 := by
    have h32 : (3/2:ℝ) = 1/2 + 1 := by norm_num
    rw [h32, Real.Gamma_add_one, Real.Gamma_one_half_eq]
    all_goals (try norm_num)
    all_goals ring
  have hs : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  rw [hab, Real.Gamma_two, hg32, Real.Gamma_one_half_eq, div_one,
    show Real.sqrt Real.pi * (Real.sqrt Real.pi / 2)
      = (Real.sqrt Real.pi * Real.sqrt Real.pi) / 2 by ring, hs]

end ProbabilityFoundations
