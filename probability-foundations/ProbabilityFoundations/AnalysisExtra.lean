import Mathlib

/-!
# Analysis helpers: cited results planned for proof (Foundations, work package L-0.6c)

Two cited results that the appendix uses without a Mathlib counterpart. Both are stated here
as theorems and proved later, not certified (`EXTERNAL-RESULTS.md`, policy "prove"):

* `ProbabilityFoundations.gronwall_integral`: integral Gronwall inequality (Teschl, Lemma 2.7).
  Consumers: `thm:app-dyn-main`(ii), `cor:app-dyn-continuum`(ii) (Cauchy bound, uniqueness).
* `ProbabilityFoundations.weak_implies_bl`: on a compact metric space, weak convergence of finite
  measures with bounded mass implies convergence in the bounded-Lipschitz distance
  (Dudley, Thm 11.3.3). Consumer: `cor:app-dyn-continuum`(ii).

Snapshot tag `cr-2026-10-23`. There is no paper label; the statements are the cited results as
the consuming card needs them. Proof bodies are `sorry`; the proof cards are in the result JSON.
-/

open MeasureTheory Set Filter Topology

namespace ProbabilityFoundations

/-- Integral Gronwall inequality (Teschl, *Ordinary Differential Equations and Dynamical Systems*,
Lemma 2.7), snapshot `cr-2026-10-23`.

Statement: for `c ≥ 0`, if `u` is bounded and measurable on `[0,T]` and
`u(t) ≤ a + c ∫_0^t u(s) ds` for all `t ∈ [0,T]`, then `u(t) ≤ a e^{c t}` for all `t ∈ [0,T]`.
No sign condition on `a` is needed. -/
private lemma gronwall_integral_pow (c t : ℝ) (k : ℕ) :
    c * ∫ s in (0:ℝ)..t, (c * s) ^ k / (k.factorial : ℝ)
      = (c * t) ^ (k + 1) / ((k + 1).factorial : ℝ) := by
  have h : ∀ s : ℝ, (c * s) ^ k / (k.factorial : ℝ) = (c ^ k / (k.factorial : ℝ)) * s ^ k :=
    fun s => by rw [mul_pow]; ring
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, integral_pow, zero_pow (Nat.succ_ne_zero k),
    sub_zero, Nat.factorial_succ]
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem gronwall_integral {T a c : ℝ} (hc : 0 ≤ c) (u : ℝ → ℝ)
    (hmeas : AEStronglyMeasurable u (volume.restrict (Icc (0:ℝ) T)))
    (hbdd : ∃ M : ℝ, ∀ t ∈ Icc (0:ℝ) T, |u t| ≤ M)
    (hineq : ∀ t ∈ Icc (0:ℝ) T, u t ≤ a + c * ∫ s in (0:ℝ)..t, u s) :
    ∀ t ∈ Icc (0:ℝ) T, u t ≤ a * Real.exp (c * t) := by
  obtain ⟨M, hM⟩ := hbdd
  have hIT : IntegrableOn u (Icc (0:ℝ) T) := by
    have hfin : (volume.restrict (Icc (0:ℝ) T)) univ ≠ ⊤ := by
      rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top.ne
    have hb : ∀ᵐ x ∂((volume.restrict (Icc (0:ℝ) T)).restrict univ), ‖u x‖ ≤ M := by
      rw [Measure.restrict_univ]
      exact ae_restrict_of_forall_mem measurableSet_Icc
        (fun x hx => by rw [Real.norm_eq_abs]; exact hM x hx)
    have h := Measure.integrableOn_of_bounded (μ := volume.restrict (Icc (0:ℝ) T))
      (s := univ) hfin hmeas hb
    simpa [IntegrableOn, Measure.restrict_univ] using h
  have hint : ∀ t ∈ Icc (0:ℝ) T, IntervalIntegrable u volume 0 t := by
    intro t ht
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).2
      (hIT.mono_set (Icc_subset_Icc le_rfl ht.2))
  -- Elementary iteration: u(t) ≤ a S_n(t) + M (ct)^n / n!
  have key : ∀ n : ℕ, ∀ t ∈ Icc (0:ℝ) T,
      u t ≤ a * (∑ k ∈ Finset.range n, (c * t) ^ k / (k.factorial : ℝ))
        + M * ((c * t) ^ n / (n.factorial : ℝ)) := by
    intro n
    induction n with
    | zero =>
      intro t ht
      have h1 := hM t ht
      have h2 := le_abs_self (u t)
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero, zero_add, pow_zero,
        Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
      linarith
    | succ n ih =>
      intro t ht
      have hG : Continuous fun s : ℝ => a * (∑ k ∈ Finset.range n, (c * s) ^ k / (k.factorial : ℝ))
          + M * ((c * s) ^ n / (n.factorial : ℝ)) := by fun_prop
      have hmono : ∫ s in (0:ℝ)..t, u s ≤ ∫ s in (0:ℝ)..t,
          (a * (∑ k ∈ Finset.range n, (c * s) ^ k / (k.factorial : ℝ))
            + M * ((c * s) ^ n / (n.factorial : ℝ))) :=
        intervalIntegral.integral_mono_on ht.1 (hint t ht) (hG.intervalIntegrable _ _)
          (fun s hs => ih s ⟨hs.1, hs.2.trans ht.2⟩)
      have hS_int : c * ∫ s in (0:ℝ)..t, ∑ k ∈ Finset.range n, (c * s) ^ k / (k.factorial : ℝ)
          = ∑ k ∈ Finset.range n, (c * t) ^ (k + 1) / ((k + 1).factorial : ℝ) := by
        rw [intervalIntegral.integral_finsetSum (fun k _ =>
          (by fun_prop : Continuous fun s : ℝ => (c * s) ^ k / (k.factorial : ℝ)).intervalIntegrable _ _),
          Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => gronwall_integral_pow c t k)
      have hH_int : c * ∫ s in (0:ℝ)..t, (c * s) ^ n / (n.factorial : ℝ)
          = (c * t) ^ (n + 1) / ((n + 1).factorial : ℝ) := gronwall_integral_pow c t n
      have hcalc : c * ∫ s in (0:ℝ)..t,
          (a * (∑ k ∈ Finset.range n, (c * s) ^ k / (k.factorial : ℝ))
            + M * ((c * s) ^ n / (n.factorial : ℝ)))
          = a * (∑ k ∈ Finset.range n, (c * t) ^ (k + 1) / ((k + 1).factorial : ℝ))
            + M * ((c * t) ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
        have hS : Continuous fun s : ℝ => ∑ k ∈ Finset.range n, (c * s) ^ k / (k.factorial : ℝ) := by
          fun_prop
        have hH : Continuous fun s : ℝ => (c * s) ^ n / (n.factorial : ℝ) := by fun_prop
        rw [intervalIntegral.integral_add ((hS.const_mul a).intervalIntegrable _ _)
          ((hH.const_mul M).intervalIntegrable _ _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        linear_combination a * hS_int + M * hH_int
      have hsum_eq : a * (∑ k ∈ Finset.range (n + 1), (c * t) ^ k / (k.factorial : ℝ))
          = a + a * (∑ k ∈ Finset.range n, (c * t) ^ (k + 1) / ((k + 1).factorial : ℝ)) := by
        rw [Finset.sum_range_succ']
        simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
        ring
      calc u t ≤ a + c * ∫ s in (0:ℝ)..t, u s := hineq t ht
        _ ≤ a + c * ∫ s in (0:ℝ)..t,
            (a * (∑ k ∈ Finset.range n, (c * s) ^ k / (k.factorial : ℝ))
              + M * ((c * s) ^ n / (n.factorial : ℝ))) :=
          by linarith [mul_le_mul_of_nonneg_left hmono hc]
        _ = a + (a * (∑ k ∈ Finset.range n, (c * t) ^ (k + 1) / ((k + 1).factorial : ℝ))
            + M * ((c * t) ^ (n + 1) / ((n + 1).factorial : ℝ))) := by rw [hcalc]
        _ = a * (∑ k ∈ Finset.range (n + 1), (c * t) ^ k / (k.factorial : ℝ))
            + M * ((c * t) ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
          rw [hsum_eq]; ring
  intro t ht
  have hexp : HasSum (fun k : ℕ => (c * t) ^ k / (k.factorial : ℝ)) (Real.exp (c * t)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (c * t)
  have hlim : Tendsto (fun n : ℕ => a * (∑ k ∈ Finset.range n, (c * t) ^ k / (k.factorial : ℝ))
      + M * ((c * t) ^ n / (n.factorial : ℝ))) atTop
      (𝓝 (a * Real.exp (c * t) + M * 0)) :=
    ((hexp.tendsto_sum_nat).const_mul a).add
      ((FloorSemiring.tendsto_pow_div_factorial_atTop (c * t)).const_mul M)
  have := ge_of_tendsto hlim (Eventually.of_forall fun n => key n t ht)
  simpa only [mul_zero, add_zero] using this

/-- Bounded-Lipschitz test class on a metric space `K`: the functions `f : K → ℝ` with
`|f x| ≤ 1` for all `x` and `|f x - f y| ≤ dist x y` for all `x, y`. -/
def blBall (K : Type*) [MetricSpace K] : Set (K → ℝ) :=
  {f | (∀ x, |f x| ≤ 1) ∧ ∀ x y, |f x - f y| ≤ dist x y}

/-- Bounded-Lipschitz distance between two finite measures `μ`, `ν` on `K`:
`sup_{f ∈ blBall K} |∫ f dμ - ∫ f dν|`. -/
noncomputable def blDist {K : Type*} [MetricSpace K] [MeasurableSpace K] (μ ν : Measure K) : ℝ :=
  sSup ((fun f : K → ℝ => |∫ x, f x ∂μ - ∫ x, f x ∂ν|) '' blBall K)

/-- Weak convergence implies bounded-Lipschitz convergence on a compact metric space (Dudley,
*Real Analysis and Probability*, Thm 11.3.3), snapshot `cr-2026-10-23`.

Statement: `K` compact metric with Borel σ-algebra; `μ n` and `ν` finite positive measures;
the masses `μ n univ` are bounded uniformly in `n`; and `∫ f dμ n → ∫ f dν` for every
continuous `f : K → ℝ` (weak convergence; every continuous function is bounded on compact `K`).
Then `blDist (μ n) ν → 0`. -/
theorem weak_implies_bl {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K]
    [BorelSpace K] (μ : ℕ → Measure K) (ν : Measure K)
    [∀ n, IsFiniteMeasure (μ n)] [IsFiniteMeasure ν]
    (hmass : ∃ C : ℝ, ∀ n, (μ n univ).toReal ≤ C)
    (hweak : ∀ f : K → ℝ, Continuous f →
      Tendsto (fun n => ∫ x, f x ∂(μ n)) atTop (𝓝 (∫ x, f x ∂ν))) :
    Tendsto (fun n => blDist (μ n) ν) atTop (𝓝 0) := by
  classical
  obtain ⟨C, hC⟩ := hmass
  obtain ⟨Cb, hCb_def⟩ : ∃ Cb : ℝ, Cb = max C 0 := ⟨_, rfl⟩
  have hCb : ∀ n, (μ n).real univ ≤ Cb := fun n => by
    rw [measureReal_def, hCb_def]; exact (hC n).trans (le_max_left _ _)
  have hCb0 : 0 ≤ Cb := by rw [hCb_def]; exact le_max_right _ _
  have hCn0 : 0 ≤ ν.real univ := measureReal_nonneg
  -- the test class as bounded continuous functions
  let T : Set (BoundedContinuousFunction K ℝ) :=
    {F | (∀ x, |F x| ≤ 1) ∧ ∀ x y, |F x - F y| ≤ dist x y}
  have hTcpt : IsCompact (closure T) := by
    refine BoundedContinuousFunction.arzela_ascoli (Icc (-1 : ℝ) 1) isCompact_Icc T ?_ ?_
    · intro F x hF
      have hF' := hF
      simp only [T, Set.mem_setOf_eq] at hF'
      exact abs_le.1 (hF'.1 x)
    · intro x0
      rw [Metric.equicontinuousAt_iff]
      intro ε hε
      refine ⟨ε, hε, fun x hx G => ?_⟩
      have hG' := G.2
      simp only [T, Set.mem_setOf_eq] at hG'
      rw [Real.dist_eq]
      exact lt_of_le_of_lt (hG'.2 x0 x) (by rw [dist_comm]; exact hx)
  have htb : TotallyBounded T := TotallyBounded.subset subset_closure hTcpt.totallyBounded
  -- the bounded-Lipschitz pointwise estimate
  have hdiff : ∀ (F y : BoundedContinuousFunction K ℝ) (ε : ℝ) (ρ : Measure K) [IsFiniteMeasure ρ],
      (∀ x, |F x - y x| ≤ ε) → |∫ x, F x ∂ρ - ∫ x, y x ∂ρ| ≤ ε * ρ.real univ := by
    intro F y ε ρ _ hpt
    rw [← integral_sub (BoundedContinuousFunction.integrable ρ F)
      (BoundedContinuousFunction.integrable ρ y), ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le_const (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact hpt x
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨ε, hε_def⟩ : ∃ ε : ℝ, ε = η / (2 * (Cb + ν.real univ + 1)) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hε_def]; positivity
  have hεS : ε * (Cb + ν.real univ) ≤ η / 2 := by
    have h1 : ε * (Cb + ν.real univ + 1) = η / 2 := by
      rw [hε_def]; field_simp
    have h2 : ε * (Cb + ν.real univ + 1) = ε * (Cb + ν.real univ) + ε := by ring
    linarith
  obtain ⟨t, htfin, hcov⟩ := Metric.totallyBounded_iff.1 htb ε hε
  set D : ℕ → ℝ := fun n => ∑ y ∈ htfin.toFinset, |∫ x, y x ∂(μ n) - ∫ x, y x ∂ν| with hD_def
  have hDlim : Tendsto D atTop (𝓝 0) := by
    have hterm : ∀ y ∈ htfin.toFinset,
        Tendsto (fun n => |∫ x, y x ∂(μ n) - ∫ x, y x ∂ν|) atTop (𝓝 0) := by
      intro y _
      have h1 : Tendsto (fun n => ∫ x, y x ∂(μ n) - ∫ x, y x ∂ν) atTop (𝓝 0) := by
        have := (hweak (⇑y) y.continuous).sub_const (∫ x, y x ∂ν)
        simpa using this
      have := (continuous_abs.tendsto 0).comp h1
      simpa [Function.comp_def] using this
    have := tendsto_finsetSum htfin.toFinset hterm
    simpa [hD_def] using this
  have hev : ∀ᶠ n in atTop, D n < η / 2 := by
    have := Metric.tendsto_nhds.1 hDlim (η / 2) (half_pos hη)
    filter_upwards [this] with n hn
    rw [Real.dist_eq, sub_zero] at hn
    exact (abs_lt.1 hn).2
  filter_upwards [hev] with n hn
  -- estimate for every test function in the class, uniformly in the class
  have hbound : ∀ F ∈ T, |∫ x, F x ∂(μ n) - ∫ x, F x ∂ν| ≤ ε * (Cb + ν.real univ) + D n := by
    intro F hF
    obtain ⟨y, hy, hd⟩ : ∃ y ∈ t, dist F y < ε := by
      have := hcov hF
      simpa [Metric.mem_ball] using this
    have hyF : y ∈ htfin.toFinset := (htfin.mem_toFinset).2 hy
    have hpt : ∀ x, |F x - y x| ≤ ε := fun x => by
      have := BoundedContinuousFunction.dist_coe_le_dist (f := F) (g := y) x
      rw [Real.dist_eq] at this
      exact this.trans hd.le
    have h1 := hdiff F y ε (μ n) hpt
    have h2 := hdiff F y ε ν hpt
    have h3 : |∫ x, y x ∂(μ n) - ∫ x, y x ∂ν| ≤ D n :=
      Finset.single_le_sum (f := fun y : BoundedContinuousFunction K ℝ =>
        |∫ x, y x ∂(μ n) - ∫ x, y x ∂ν|) (fun _ _ => abs_nonneg _) hyF
    have hsplit : ∫ x, F x ∂(μ n) - ∫ x, F x ∂ν
        = (∫ x, F x ∂(μ n) - ∫ x, y x ∂(μ n)) + (∫ x, y x ∂(μ n) - ∫ x, y x ∂ν)
          + (∫ x, y x ∂ν - ∫ x, F x ∂ν) := by ring
    rw [hsplit]
    have h5 := abs_add_le ((∫ x, F x ∂(μ n) - ∫ x, y x ∂(μ n)) + (∫ x, y x ∂(μ n) - ∫ x, y x ∂ν))
      (∫ x, y x ∂ν - ∫ x, F x ∂ν)
    have h6 := abs_add_le (∫ x, F x ∂(μ n) - ∫ x, y x ∂(μ n)) (∫ x, y x ∂(μ n) - ∫ x, y x ∂ν)
    have hm1 : ε * (μ n).real univ ≤ ε * Cb := mul_le_mul_of_nonneg_left (hCb n) hε.le
    have h7 : ε * (Cb + ν.real univ) = ε * Cb + ε * ν.real univ := by ring
    rw [abs_sub_comm (∫ x, y x ∂ν) (∫ x, F x ∂ν)] at h5
    linarith
  have hbl : blDist (μ n) ν ≤ ε * (Cb + ν.real univ) + D n := by
    unfold blDist
    apply csSup_le
    · have hz0 : (fun _ : K => (0 : ℝ)) ∈ blBall K :=
        ⟨fun _ => by simp, fun _ _ => by simp [dist_nonneg]⟩
      exact Set.Nonempty.image _ ⟨_, hz0⟩
    · rintro _ ⟨f, hf, rfl⟩
      have hfc : Continuous f := LipschitzWith.continuous
        (LipschitzWith.of_dist_le' (K := 1) (fun x y => by rw [Real.dist_eq, one_mul]; exact hf.2 x y))
      let F : BoundedContinuousFunction K ℝ := BoundedContinuousFunction.mkOfCompact ⟨f, hfc⟩
      have hFT : F ∈ T := by
        simp only [T, Set.mem_setOf_eq]
        exact ⟨fun x => hf.1 x, fun x y => hf.2 x y⟩
      exact hbound F hFT
  have hnn : 0 ≤ blDist (μ n) ν := by
    unfold blDist
    apply Real.sSup_nonneg
    rintro _ ⟨f, _, rfl⟩
    exact abs_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith

end ProbabilityFoundations
