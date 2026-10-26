import Mathlib

/-!
# Foundations: varying-space uniform integrability (task L-A.F5)

Helper for `lem:app-setup-residual`(iii) (snapshot `cr-2026-10-23`). The residual law is
asserted there for a sequence of matrices `A_B` whose dimensions and probability spaces may
vary with the index. Mathlib's uniform-integrability API lives on one fixed space, so the
transfer from weak convergence plus a uniform fourth-moment bound to convergence of
`E ψ(d_k)` is stated here in varying-space form.

Statement only (`sorry`). Proof route is in the interface JSON
`phases-of-muon/appendix-nodes/results/L-A.F5-interface.json`.

Mathlib used: `MeasureTheory.TendstoInDistribution` (`Function/ConvergenceInDistribution.lean`),
which allows varying `Ω k` and `P k`.
-/

open MeasureTheory Filter Topology

namespace ProbabilityFoundations

private theorem integrable_bcf_comp {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (f : α → ℝ) (hf : AEMeasurable f μ) (g : BoundedContinuousFunction ℝ ℝ) :
    Integrable (fun a => g (f a)) μ :=
  (integrable_const ‖g‖).mono' (g.continuous.measurable.comp_aemeasurable hf).aestronglyMeasurable
    (Eventually.of_forall fun a => g.norm_coe_le_norm (f a))

private theorem integrable_psi_comp {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (ψ : ℝ → ℝ) (hψc : Continuous ψ) (hψ4 : ∀ x, |ψ x| ≤ 2 + x ^ 4)
    (f : α → ℝ) (hf : AEMeasurable f μ) (hf4 : Integrable (fun a => f a ^ 4) μ) :
    Integrable (fun a => ψ (f a)) μ := by
  refine Integrable.mono' (g := fun a => 2 + f a ^ 4) ((integrable_const (2:ℝ)).add hf4) ?_ ?_
  · exact (hψc.measurable.comp_aemeasurable hf).aestronglyMeasurable
  · exact Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hψ4 (f a)

/-- Weak convergence of real random variables `d k` (on varying probability spaces) to a limit
`Z` (on a probability space `Ω'`), together with a uniform bound `sup_k E d_k^4 < ∞`, gives
`E ψ(d_k) → E ψ(Z)` for every continuous `ψ` with `|ψ x| ≤ 1 + x^2`. -/
theorem tendsto_integral_of_tendstoInDistribution_of_uniform_fourth_moment
    {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    {Ω' : Type*} [MeasurableSpace Ω']
    (P : (k : ℕ) → Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (d : (k : ℕ) → Ω k → ℝ) (Z : Ω' → ℝ)
    (hd : TendstoInDistribution d atTop Z P P')
    (hfour : ∀ k, Integrable (fun ω => d k ω ^ 4) (P k))
    (hbound : ∃ C : ℝ, ∀ k, ∫ ω, d k ω ^ 4 ∂(P k) ≤ C)
    (ψ : ℝ → ℝ) (hψc : Continuous ψ) (hψb : ∀ x, |ψ x| ≤ 1 + x ^ 2) :
    Tendsto (fun k => ∫ ω, ψ (d k ω) ∂(P k)) atTop (𝓝 (∫ ω, ψ (Z ω) ∂P')) := by
  obtain ⟨C, hC⟩ := hbound
  have hdm : ∀ k, AEMeasurable (d k) (P k) := hd.forall_aemeasurable
  have hZm : AEMeasurable Z P' := hd.aemeasurable_limit
  have hweak : ∀ g : BoundedContinuousFunction ℝ ℝ, Tendsto (fun k => ∫ ω, g (d k ω) ∂(P k)) atTop
      (𝓝 (∫ ω, g (Z ω) ∂P')) :=
    (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ hdm hZm).mp hd
  have hψ4 : ∀ x, |ψ x| ≤ 2 + x ^ 4 := fun x => by
    nlinarith [hψb x, sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2)]
  -- truncations of x^4 and of ψ
  have hGex : ∀ n : ℕ, ∃ g : BoundedContinuousFunction ℝ ℝ, ∀ x, g x = min (x ^ 4) (n : ℝ) := by
    intro n
    refine ⟨BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x : ℝ => min (x ^ 4) (n : ℝ)) (by fun_prop) (n : ℝ) (fun x => ?_), fun x => rfl⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by positivity) (Nat.cast_nonneg n))]
    exact min_le_right _ _
  choose G hG using hGex
  have hHex : ∀ N : ℕ, ∃ g : BoundedContinuousFunction ℝ ℝ,
      ∀ x, g x = ψ x * min 1 (max 0 ((N : ℝ) + 1 - |x|)) := by
    intro N
    refine ⟨BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x : ℝ => ψ x * min 1 (max 0 ((N : ℝ) + 1 - |x|))) (by fun_prop)
      (1 + ((N : ℝ) + 1) ^ 2) (fun x => ?_), fun x => rfl⟩
    rw [Real.norm_eq_abs, abs_mul]
    have hχ0 : 0 ≤ min 1 (max 0 ((N : ℝ) + 1 - |x|)) := le_min zero_le_one (le_max_left _ _)
    have hχ1 : min 1 (max 0 ((N : ℝ) + 1 - |x|)) ≤ 1 := min_le_left _ _
    rw [abs_of_nonneg hχ0]
    by_cases hx : |x| ≤ (N : ℝ) + 1
    · have hsq : x ^ 2 ≤ ((N : ℝ) + 1) ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
      calc |ψ x| * min 1 (max 0 ((N : ℝ) + 1 - |x|)) ≤ |ψ x| * 1 :=
            mul_le_mul_of_nonneg_left hχ1 (abs_nonneg _)
        _ ≤ 1 + ((N : ℝ) + 1) ^ 2 := by linarith [hψb x]
    · push_neg at hx
      have h0 : min 1 (max 0 ((N : ℝ) + 1 - |x|)) = 0 := by
        rw [max_eq_left (by linarith), min_eq_right zero_le_one]
      rw [h0, mul_zero]
      positivity
  choose H hH using hHex
  -- pointwise cutoff estimate
  have hcutpt : ∀ N : ℕ, 1 ≤ (N : ℝ) → ∀ x : ℝ, ‖ψ x - H N x‖ ≤ 2 / (N : ℝ) ^ 2 * x ^ 4 := by
    intro N hN x
    rw [hH N x, Real.norm_eq_abs]
    by_cases hx : |x| ≤ (N : ℝ)
    · have h1 : min 1 (max 0 ((N : ℝ) + 1 - |x|)) = 1 :=
        min_eq_left (le_max_of_le_right (by linarith))
      rw [h1, mul_one, sub_self, abs_zero]
      positivity
    · push_neg at hx
      have hM2 : 1 ≤ (N : ℝ) ^ 2 := by nlinarith
      have hx2 : (N : ℝ) ^ 2 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
      have hx1 : 1 ≤ x ^ 2 := by linarith
      have hχ0 : 0 ≤ min 1 (max 0 ((N : ℝ) + 1 - |x|)) := le_min zero_le_one (le_max_left _ _)
      have hχ1 : min 1 (max 0 ((N : ℝ) + 1 - |x|)) ≤ 1 := min_le_left _ _
      have h2 : |ψ x - ψ x * min 1 (max 0 ((N : ℝ) + 1 - |x|))| ≤ 1 + x ^ 2 := by
        rw [show ψ x - ψ x * min 1 (max 0 ((N : ℝ) + 1 - |x|))
            = ψ x * (1 - min 1 (max 0 ((N : ℝ) + 1 - |x|))) by ring, abs_mul]
        have h3 : |1 - min 1 (max 0 ((N : ℝ) + 1 - |x|))| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith
        calc |ψ x| * |1 - min 1 (max 0 ((N : ℝ) + 1 - |x|))| ≤ |ψ x| * 1 :=
              mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
          _ ≤ 1 + x ^ 2 := by linarith [hψb x]
      have h4 : 1 + x ^ 2 ≤ 2 / (N : ℝ) ^ 2 * x ^ 4 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.2 hx2),
          mul_nonneg (sq_nonneg x) (sub_nonneg.2 hx1)]
      exact h2.trans h4
  -- fourth moment of the limit
  have hZ4 : Integrable (fun ω => Z ω ^ 4) P' := by
    have hcut : ∀ n : ℕ, ∫ ω, min (Z ω ^ 4) (n : ℝ) ∂P' ≤ C := by
      intro n
      have hterm : ∀ k, ∫ ω, G n (d k ω) ∂(P k) ≤ C := fun k => by
        calc ∫ ω, G n (d k ω) ∂(P k) ≤ ∫ ω, d k ω ^ 4 ∂(P k) := by
              refine integral_mono (integrable_bcf_comp (P k) (d k) (hdm k) (G n))
                (hfour k) fun ω => ?_
              rw [hG n]
              exact min_le_left _ _
          _ ≤ C := hC k
      have hle : ∫ ω, G n (Z ω) ∂P' ≤ C := le_of_tendsto' (hweak (G n)) hterm
      simpa only [hG] using hle
    have hmeas : AEMeasurable (fun ω => Z ω ^ 4) P' := hZm.pow_const 4
    have hmin_int : ∀ n : ℕ, Integrable (fun ω => min (Z ω ^ 4) (n : ℝ)) P' := by
      intro n
      have := integrable_bcf_comp P' Z hZm (G n)
      simpa only [hG] using this
    have hiSup : ∀ ω, ⨆ n : ℕ, ENNReal.ofReal (min (Z ω ^ 4) (n : ℝ))
        = ENNReal.ofReal (Z ω ^ 4) := by
      intro ω
      apply le_antisymm
      · exact iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _)
      · refine le_iSup_of_le ⌈Z ω ^ 4⌉₊ (ENNReal.ofReal_le_ofReal ?_)
        exact le_min le_rfl (Nat.le_ceil _)
    have hlint : ∫⁻ ω, ENNReal.ofReal (Z ω ^ 4) ∂P' ≤ ENNReal.ofReal C := by
      calc ∫⁻ ω, ENNReal.ofReal (Z ω ^ 4) ∂P'
          = ∫⁻ ω, ⨆ n : ℕ, ENNReal.ofReal (min (Z ω ^ 4) (n : ℝ)) ∂P' :=
            lintegral_congr fun ω => (hiSup ω).symm
        _ = ⨆ n : ℕ, ∫⁻ ω, ENNReal.ofReal (min (Z ω ^ 4) (n : ℝ)) ∂P' := by
            refine lintegral_iSup' (fun n => ?_) (Eventually.of_forall fun ω m n hmn => ?_)
            · exact ((hmin_int n).aestronglyMeasurable.aemeasurable).ennreal_ofReal
            · exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.mpr hmn))
        _ ≤ ENNReal.ofReal C := by
            refine iSup_le fun n => ?_
            have hnn : 0 ≤ᵐ[P'] fun ω => min (Z ω ^ 4) (n : ℝ) :=
              Eventually.of_forall fun ω => le_min (by positivity) (Nat.cast_nonneg n)
            calc ∫⁻ ω, ENNReal.ofReal (min (Z ω ^ 4) (n : ℝ)) ∂P'
                = ENNReal.ofReal (∫ ω, min (Z ω ^ 4) (n : ℝ) ∂P') :=
                  (ofReal_integral_eq_lintegral_ofReal (hmin_int n) hnn).symm
              _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (hcut n)
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    calc ∫⁻ ω, ‖Z ω ^ 4‖ₑ ∂P' = ∫⁻ ω, ENNReal.ofReal (Z ω ^ 4) ∂P' :=
          lintegral_congr fun ω => by rw [Real.enorm_eq_ofReal (by positivity)]
      _ < ⊤ := lt_of_le_of_lt hlint ENNReal.ofReal_lt_top
  -- tail estimates for the truncation error
  have hdiff_d : ∀ N : ℕ, 1 ≤ (N : ℝ) → ∀ k,
      ‖∫ ω, ψ (d k ω) ∂(P k) - ∫ ω, H N (d k ω) ∂(P k)‖ ≤ 2 / (N : ℝ) ^ 2 * C := by
    intro N hN k
    have hi1 := integrable_psi_comp (P k) ψ hψc hψ4 (d k) (hdm k) (hfour k)
    have hi2 := integrable_bcf_comp (P k) (d k) (hdm k) (H N)
    rw [← integral_sub hi1 hi2]
    calc ‖∫ ω, (ψ (d k ω) - H N (d k ω)) ∂(P k)‖
        ≤ ∫ ω, 2 / (N : ℝ) ^ 2 * d k ω ^ 4 ∂(P k) :=
          norm_integral_le_of_norm_le ((hfour k).const_mul _)
            (Eventually.of_forall fun ω => hcutpt N hN (d k ω))
      _ = 2 / (N : ℝ) ^ 2 * ∫ ω, d k ω ^ 4 ∂(P k) := integral_const_mul _ _
      _ ≤ 2 / (N : ℝ) ^ 2 * C := mul_le_mul_of_nonneg_left (hC k) (by positivity)
  have hdiff_Z : ∀ N : ℕ, 1 ≤ (N : ℝ) →
      ‖∫ ω, ψ (Z ω) ∂P' - ∫ ω, H N (Z ω) ∂P'‖
        ≤ 2 / (N : ℝ) ^ 2 * ∫ ω, Z ω ^ 4 ∂P' := by
    intro N hN
    have hi1 := integrable_psi_comp P' ψ hψc hψ4 Z hZm hZ4
    have hi2 := integrable_bcf_comp P' Z hZm (H N)
    rw [← integral_sub hi1 hi2]
    calc ‖∫ ω, (ψ (Z ω) - H N (Z ω)) ∂P'‖
        ≤ ∫ ω, 2 / (N : ℝ) ^ 2 * Z ω ^ 4 ∂P' :=
          norm_integral_le_of_norm_le (hZ4.const_mul _)
            (Eventually.of_forall fun ω => hcutpt N hN (Z ω))
      _ = 2 / (N : ℝ) ^ 2 * ∫ ω, Z ω ^ 4 ∂P' := integral_const_mul _ _
  -- epsilon argument
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (4 * (|C| + |∫ ω, Z ω ^ 4 ∂P'|) / ε))
  have hN1 : (1 : ℝ) ≤ N := le_trans (le_max_left _ _) hN.le
  have hNgt : 4 * (|C| + |∫ ω, Z ω ^ 4 ∂P'|) / ε < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hev := Metric.tendsto_nhds.mp (hweak (H N)) (ε / 2) (half_pos hε)
  filter_upwards [hev] with k hk
  rw [dist_eq_norm] at hk ⊢
  have e1 := hdiff_d N hN1 k
  have e2 := hdiff_Z N hN1
  set K := |C| + |∫ ω, Z ω ^ 4 ∂P'| with hKdef
  have hsK : 2 / (N : ℝ) ^ 2 * K < ε / 2 := by
    have hN' : 4 * K < ε * N := by
      have := (div_lt_iff₀ hε).1 hNgt
      linarith
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hε.le (by linarith : (0 : ℝ) ≤ N)) (by linarith : (0 : ℝ) ≤ N - 1)]
  have hcomb : 2 / (N : ℝ) ^ 2 * C + 2 / (N : ℝ) ^ 2 * ∫ ω, Z ω ^ 4 ∂P'
      ≤ 2 / (N : ℝ) ^ 2 * K := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (by linarith [le_abs_self C, le_abs_self (∫ ω, Z ω ^ 4 ∂P')])
      (by positivity)
  have hsplit : ∫ ω, ψ (d k ω) ∂(P k) - ∫ ω, ψ (Z ω) ∂P'
      = (∫ ω, ψ (d k ω) ∂(P k) - ∫ ω, H N (d k ω) ∂(P k))
        + (∫ ω, H N (d k ω) ∂(P k) - ∫ ω, H N (Z ω) ∂P')
        - (∫ ω, ψ (Z ω) ∂P' - ∫ ω, H N (Z ω) ∂P') := by ring
  rw [hsplit]
  calc ‖(∫ ω, ψ (d k ω) ∂(P k) - ∫ ω, H N (d k ω) ∂(P k))
        + (∫ ω, H N (d k ω) ∂(P k) - ∫ ω, H N (Z ω) ∂P')
        - (∫ ω, ψ (Z ω) ∂P' - ∫ ω, H N (Z ω) ∂P')‖
      ≤ ‖(∫ ω, ψ (d k ω) ∂(P k) - ∫ ω, H N (d k ω) ∂(P k))
          + (∫ ω, H N (d k ω) ∂(P k) - ∫ ω, H N (Z ω) ∂P')‖
        + ‖∫ ω, ψ (Z ω) ∂P' - ∫ ω, H N (Z ω) ∂P'‖ := norm_sub_le _ _
    _ ≤ ‖∫ ω, ψ (d k ω) ∂(P k) - ∫ ω, H N (d k ω) ∂(P k)‖
          + ‖∫ ω, H N (d k ω) ∂(P k) - ∫ ω, H N (Z ω) ∂P'‖
        + ‖∫ ω, ψ (Z ω) ∂P' - ∫ ω, H N (Z ω) ∂P'‖ :=
          add_le_add (norm_add_le _ _) le_rfl
    _ < ε := by
          have h3 := hdiff_Z N hN1
          linarith
