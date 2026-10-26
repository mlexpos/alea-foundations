import GaussianFoundations.Defs
import SLT.HansonWright

/-!
# Gaussian quadratic forms: `‖zᵀFz − Tr F‖_{L^p} ≤ C_p ‖F‖_F` (from SLT's Hanson–Wright tail bound).
-/

namespace GaussianFoundations

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

private lemma stdGaussianVector_data {n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (z : Ω → Fin n → ℝ)
    (hz : IsStdGaussianVector μ z) :
    AEMeasurable z μ ∧
      iIndepFun (fun i ω => z ω i) μ ∧
      ∀ i, HasSubgaussianMGF (fun ω => z ω i) (1 : ℝ≥0) μ := by
  have hzmeas : AEMeasurable z μ := by
    by_cases hn : n = 0
    · subst n
      fun_prop
    · let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
      by_contra hzm
      have hdirac := Measure.map_of_not_aemeasurable_of_ne_zero hzm
        (IsProbabilityMeasure.ne_zero μ)
      have hpi_dirac : Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
          Measure.dirac (Classical.ofNonempty : Fin n → ℝ) := by
        rw [← hz]
        exact hdirac
      have heval := congrArg (fun ν : Measure (Fin n → ℝ) =>
        ν.map (Function.eval i)) hpi_dirac
      have hgauss_dirac : gaussianReal 0 1 =
          Measure.dirac ((Classical.ofNonempty : Fin n → ℝ) i) := by
        rw [(measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).map_eq] at heval
        simpa using heval
      letI : NullSingletonClass (gaussianReal 0 1) :=
        nullSingletonClass_gaussianReal (by norm_num)
      have hpoint := congrArg
        (fun ν : Measure ℝ => ν {((Classical.ofNonempty : Fin n → ℝ) i)}) hgauss_dirac
      simpa using hpoint
  have hcoord : ∀ i, μ.map (fun ω => z ω i) = gaussianReal 0 1 := by
    intro i
    calc
      μ.map (fun ω => z ω i) = (μ.map z).map (Function.eval i) := by
        rw [(measurable_pi_apply i).aemeasurable.map_map_of_aemeasurable hzmeas]
        rfl
      _ = (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map (Function.eval i) := by
        rw [hz]
      _ = gaussianReal 0 1 := (measurePreserving_eval _ i).map_eq
  have hindep : iIndepFun (fun i ω => z ω i) μ := by
    rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => hzmeas.eval i)]
    rw [show (fun ω i => z ω i) = z from rfl, hz]
    simp_rw [hcoord]
  refine ⟨hzmeas, hindep, ?_⟩
  intro i
  apply HasSubgaussianMGF.id_map_iff (hzmeas.eval i) |>.mp
  rw [hcoord i]
  exact HansonWright.hasSubgaussianMGF_id_gaussianReal_zero_one

private lemma centeredQuadraticForm_eq {n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (z : Ω → Fin n → ℝ)
    (hz : IsStdGaussianVector μ z) (F : Matrix (Fin n) (Fin n) ℝ) :
    HansonWright.centeredQuadraticForm μ F (fun i ω => z ω i) =
      fun ω => dotProduct (z ω) (Matrix.mulVec F (z ω)) - Matrix.trace F := by
  classical
  obtain ⟨hzmeas, hindep, hsubG⟩ := stdGaussianVector_data μ z hz
  have hcoord : ∀ i, μ.map (fun ω => z ω i) = gaussianReal 0 1 := by
    intro i
    calc
      μ.map (fun ω => z ω i) = (μ.map z).map (Function.eval i) := by
        rw [(measurable_pi_apply i).aemeasurable.map_map_of_aemeasurable hzmeas]
        rfl
      _ = (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map (Function.eval i) := by
        rw [hz]
      _ = gaussianReal 0 1 := (measurePreserving_eval _ i).map_eq
  have hsq_int (i : Fin n) : Integrable (fun ω => z ω i ^ 2) μ :=
    integrable_pow_of_integrable_exp_mul (t := 1) one_ne_zero
      (by simpa using (hsubG i).integrable_exp_mul 1)
      (by simpa using (hsubG i).integrable_exp_mul (-1)) 2
  have hsq (i : Fin n) : ∫ ω, z ω i ^ 2 ∂μ = 1 := by
    have hiLaw : HasLaw (fun ω => z ω i) (gaussianReal 0 1) μ :=
      ⟨hzmeas.eval i, hcoord i⟩
    have hi := hiLaw.integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
    change (∫ ω, z ω i ^ 2 ∂μ) = ∫ x, x ^ 2 ∂gaussianReal 0 1 at hi
    rw [hi]
    have hv := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
    rw [variance_eq_integral (X := fun x : ℝ => x) measurable_id.aemeasurable] at hv
    simpa using hv
  have hterm (i j : Fin n) :
      Integrable (fun ω => F i j * z ω i * z ω j) μ := by
    by_cases hij : i = j
    · subst j
      convert (hsq_int i).const_mul (F i i) using 1
      ext ω
      ring
    · have hm : Integrable ((fun ω => z ω i) * fun ω => z ω j) μ :=
        (hindep.indepFun hij).integrable_mul (hsubG i).integrable (hsubG j).integrable
      convert hm.const_mul (F i j) using 1
      ext ω
      simp only [Pi.mul_apply]
      ring
  have hint :
      ∫ ω, HansonWright.randomQuadraticForm F (fun i ω => z ω i) ω ∂μ =
        Matrix.trace F := by
    simp only [HansonWright.randomQuadraticForm, HansonWright.quadraticForm]
    change (∫ ω, ∑ i, ∑ j, F i j * z ω i * z ω j ∂μ) = ∑ i, F i i
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum]
      · rw [Finset.sum_eq_single i]
        · calc
            (∫ a, F i i * z a i * z a i ∂μ) =
                ∫ a, F i i * (z a i ^ 2) ∂μ := by
                  apply integral_congr_ae
                  filter_upwards with a
                  ring
            _ = F i i * ∫ a, z a i ^ 2 ∂μ := by
              simpa using integral_const_mul (μ := μ) (F i i) (fun a : Ω => z a i ^ 2)
            _ = F i i := by rw [hsq i, mul_one]
        · intro j _ hji
          have hprod := (hindep.indepFun hji.symm).integral_fun_mul_eq_mul_integral
            (hsubG i).aestronglyMeasurable (hsubG j).aestronglyMeasurable
          calc
            (∫ a, F i j * z a i * z a j ∂μ) =
                F i j * ∫ a, z a i * z a j ∂μ := by
                  calc
                    _ = ∫ a, F i j * (z a i * z a j) ∂μ := by
                      apply integral_congr_ae
                      filter_upwards with a
                      ring
                    _ = _ := by
                      simpa using integral_const_mul (μ := μ) (F i j)
                        (fun a : Ω => z a i * z a j)
            _ = F i j * ((∫ a, z a i ∂μ) * ∫ a, z a j ∂μ) := by rw [hprod]
            _ = 0 := by
              rw [HansonWright.hasSubgaussianMGF_integral_eq_zero (hsubG i)]
              ring
        · simp
      · intro j _
        exact hterm i j
    · intro i _
      exact integrable_finsetSum _ fun j _ => hterm i j
  ext ω
  unfold HansonWright.centeredQuadraticForm
  rw [hint]
  simp only [HansonWright.randomQuadraticForm, HansonWright.quadraticForm,
    dotProduct, Matrix.mulVec]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma matrix_norm_data {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) :
    HansonWright.frobeniusNorm F = frobNorm F ∧
      HansonWright.operatorNorm F ≤ frobNorm F ∧
      (0 < frobNorm F → 0 < HansonWright.operatorNorm F) ∧
      (frobNorm F = 0 → F = 0) := by
  have hop_le : HansonWright.operatorNorm F ≤ frobNorm F := by
    unfold HansonWright.operatorNorm frobNorm
    let T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
      Matrix.toEuclideanCLM (𝕜 := ℝ) F
    change ‖T‖ ≤ _
    refine ContinuousLinearMap.opNorm_le_bound T (Real.sqrt_nonneg _) fun x => ?_
    rw [← sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
    have hsum : 0 ≤ ∑ i, ∑ j, F i j ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [mul_pow, Real.sq_sqrt hsum]
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    change (∑ i, (∑ j, F i j * x.ofLp j) ^ 2) ≤
      (∑ i, ∑ j, F i j ^ 2) * ∑ j, x.ofLp j ^ 2
    calc
      (∑ i, (∑ j, F i j * x.ofLp j) ^ 2)
          ≤ ∑ i, (∑ j, F i j ^ 2) * ∑ j, x.ofLp j ^ 2 := by
            gcongr with i
            exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (F i) x.ofLp
      _ = (∑ i, ∑ j, F i j ^ 2) * ∑ j, x.ofLp j ^ 2 := by
        rw [Finset.sum_mul]
  have hzero_frob : frobNorm F = 0 → F = 0 := by
    intro h
    unfold frobNorm at h
    have hnonneg : 0 ≤ ∑ i, ∑ j, F i j ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hs : ∑ i, ∑ j, F i j ^ 2 = 0 := (Real.sqrt_eq_zero hnonneg).mp h
    ext i j
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)).mp hs i (Finset.mem_univ i)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => sq_nonneg _)).mp hi j (Finset.mem_univ j)
    exact (sq_eq_zero_iff).mp hij
  have hzero_op : HansonWright.operatorNorm F = 0 → F = 0 := by
    intro h
    have hT : Matrix.toEuclideanCLM (𝕜 := ℝ) F = 0 := by
      exact norm_eq_zero.mp h
    ext i j
    have happ := DFunLike.congr_fun hT (WithLp.toLp 2 (Pi.single j (1 : ℝ)))
    have hi := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x.ofLp i) happ
    simpa [Matrix.toEuclideanCLM_toLp, Matrix.mulVec_single_one] using hi
  refine ⟨rfl, hop_le, ?_, hzero_frob⟩
  intro hf
  have hop_ne : HansonWright.operatorNorm F ≠ 0 := by
    intro hop
    have hF := hzero_op hop
    subst F
    simp [frobNorm] at hf
  exact lt_of_le_of_ne (HansonWright.operatorNorm_nonneg F) (Ne.symm hop_ne)

private lemma eLpNorm_le_of_exp_tail (p : ℝ) (hp : 1 ≤ p) (B : ℝ) (hB : 0 ≤ B) :
    ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (Y : Ω → ℝ), AEMeasurable Y μ →
      (∀ t : ℝ, 0 ≤ t →
        (μ {ω | t ≤ |Y ω|}).toReal ≤ B * Real.exp (-t)) →
      eLpNorm Y (ENNReal.ofReal p) μ ≤ ENNReal.ofReal Cp := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hGamma : 0 ≤ Real.Gamma p := Real.Gamma_nonneg_of_nonneg hp0.le
  let M : ℝ := B * p * Real.Gamma p
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M ^ (1 / p), Real.rpow_nonneg hM _, ?_⟩
  intro Ω _ μ _ Y hY htail
  have hkernel_int :
      ∫ t : ℝ in Set.Ioi 0, t ^ (p - 1) * Real.exp (-t) = Real.Gamma p := by
    simpa using Real.integral_rpow_mul_exp_neg_mul_Ioi hp0 zero_lt_one
  have hkernel_integrable :
      IntegrableOn (fun t : ℝ => t ^ (p - 1) * Real.exp (-t)) (Set.Ioi 0) := by
    refine (Real.GammaIntegral_convergent hp0).congr_fun ?_ measurableSet_Ioi
    intro t ht
    ring
  have htailE (t : ℝ) (ht : 0 ≤ t) :
      μ {ω | t ≤ |Y ω|} ≤ ENNReal.ofReal (B * Real.exp (-t)) := by
    rw [← ENNReal.toReal_le_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top]
    rw [ENNReal.toReal_ofReal (mul_nonneg hB (Real.exp_pos _).le)]
    exact htail t ht
  have hlayer := lintegral_rpow_eq_lintegral_meas_le_mul μ
    (show 0 ≤ᵐ[μ] fun ω => |Y ω| from ae_of_all _ fun _ => abs_nonneg _)
    hY.abs hp0
  have htail_lintegral :
      ∫⁻ t : ℝ in Set.Ioi 0,
          μ {ω | t ≤ |Y ω|} * ENNReal.ofReal (t ^ (p - 1)) ≤
        ENNReal.ofReal (B * Real.Gamma p) := by
    calc
      _ ≤ ∫⁻ t : ℝ in Set.Ioi 0,
          ENNReal.ofReal (B * Real.exp (-t)) * ENNReal.ofReal (t ^ (p - 1)) := by
            apply lintegral_mono_ae
            filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
            gcongr
            exact htailE t ht.le
      _ = ∫⁻ t : ℝ in Set.Ioi 0,
          ENNReal.ofReal (B * (t ^ (p - 1) * Real.exp (-t))) := by
            apply lintegral_congr_ae
            filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
            rw [← ENNReal.ofReal_mul (mul_nonneg hB (Real.exp_pos _).le)]
            congr 1
            ring
      _ = ENNReal.ofReal (∫ t : ℝ in Set.Ioi 0,
          B * (t ^ (p - 1) * Real.exp (-t))) := by
            rw [ofReal_integral_eq_lintegral_ofReal]
            · exact hkernel_integrable.const_mul B
            · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
              exact mul_nonneg hB (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)
      _ = ENNReal.ofReal (B * Real.Gamma p) := by
            rw [integral_const_mul, hkernel_int]
  have hmoment :
      ∫⁻ ω, ‖Y ω‖ₑ ^ p ∂μ ≤ ENNReal.ofReal M := by
    have henorm : (∫⁻ ω, ‖Y ω‖ₑ ^ p ∂μ) =
        ∫⁻ ω, ENNReal.ofReal (|Y ω| ^ p) ∂μ := by
      apply lintegral_congr
      intro ω
      rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le]
      rw [← ofReal_norm, Real.norm_eq_abs]
    rw [henorm, hlayer]
    calc
      ENNReal.ofReal p * ∫⁻ t : ℝ in Set.Ioi 0,
          μ {a | t ≤ |Y a|} * ENNReal.ofReal (t ^ (p - 1))
          ≤ ENNReal.ofReal p * ENNReal.ofReal (B * Real.Gamma p) := by
          gcongr
      _ = ENNReal.ofReal M := by
          rw [← ENNReal.ofReal_mul hp0.le]
          congr 1
          dsimp [M]
          ring
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal]
  · rw [ENNReal.toReal_ofReal hp0.le]
    calc
      (∫⁻ ω, ‖Y ω‖ₑ ^ p ∂μ) ^ (1 / p)
          ≤ ENNReal.ofReal M ^ (1 / p) :=
            ENNReal.rpow_le_rpow hmoment (by positivity)
      _ = ENNReal.ofReal (M ^ (1 / p)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hM (by positivity)]
  · exact ENNReal.ofReal_pos.mpr hp0 |>.ne'
  · exact ENNReal.ofReal_ne_top
  · exact hY.aestronglyMeasurable

private lemma eLpNorm_le_of_two_scale_tail (p : ℝ) (hp : 1 ≤ p)
    (a : ℝ) (ha : 0 < a) :
    ∃ Cp : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (Y : Ω → ℝ) (σ : ℝ),
      AEMeasurable Y μ → 0 < σ →
      (∀ t : ℝ, 0 ≤ t →
        (μ {ω | t ≤ |Y ω|}).toReal ≤
          2 * Real.exp (-a * min (t ^ 2 / σ ^ 2) (t / σ))) →
      eLpNorm Y (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (Cp * σ) := by
  let B : ℝ := 2 * Real.exp a
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨D, hD, hExp⟩ := eLpNorm_le_of_exp_tail p hp B hB
  refine ⟨D / a, ?_⟩
  intro Ω _ μ _ Y σ hY hσ htail
  let W : Ω → ℝ := fun ω => a * (Y ω / σ)
  have hW : AEMeasurable W μ := by
    dsimp [W]
    fun_prop
  have hWtail : ∀ t : ℝ, 0 ≤ t →
      (μ {ω | t ≤ |W ω|}).toReal ≤ B * Real.exp (-t) := by
    intro t ht
    let s : ℝ := σ * t / a
    have hs : 0 ≤ s := by dsimp [s]; positivity
    have habsa : |a| = a := abs_of_pos ha
    have hsets : {ω | t ≤ |W ω|} = {ω | s ≤ |Y ω|} := by
      ext ω
      change t ≤ |a * (Y ω / σ)| ↔ s ≤ |Y ω|
      rw [abs_mul, abs_div, habsa, abs_of_pos hσ]
      constructor
      · intro h
        rw [← mul_div_assoc] at h
        apply (div_le_iff₀ ha).2
        have h' := (le_div_iff₀ hσ).1 h
        simpa [mul_comm, mul_left_comm, mul_assoc] using h'
      · intro h
        rw [← mul_div_assoc]
        apply (le_div_iff₀ hσ).2
        have h' := (div_le_iff₀ ha).1 h
        simpa [mul_comm, mul_left_comm, mul_assoc] using h'
    have hs_div : s / σ = t / a := by
      dsimp [s]
      field_simp
    have hs_sq_div : s ^ 2 / σ ^ 2 = (t / a) ^ 2 := by
      rw [← div_pow]
      exact congrArg (· ^ 2) hs_div
    have hx0 : 0 ≤ t / a := div_nonneg ht ha.le
    have hx_sq : t / a - 1 ≤ (t / a) ^ 2 := by
      nlinarith [sq_nonneg (t / a - 1 / 2)]
    have hmin : t / a - 1 ≤ min (s ^ 2 / σ ^ 2) (s / σ) := by
      rw [hs_sq_div, hs_div]
      exact le_min hx_sq (by linarith)
    have hat : a * (t / a) = t := by field_simp
    have harg : -a * min (s ^ 2 / σ ^ 2) (s / σ) ≤ -t + a := by
      calc
        -a * min (s ^ 2 / σ ^ 2) (s / σ) ≤ -a * (t / a - 1) :=
          mul_le_mul_of_nonpos_left hmin (by linarith)
        _ = -t + a := by field_simp; ring
    rw [hsets]
    calc
      (μ {ω | s ≤ |Y ω|}).toReal
          ≤ 2 * Real.exp (-a * min (s ^ 2 / σ ^ 2) (s / σ)) := by
            exact htail s hs
      _ ≤ 2 * Real.exp (-t + a) := by
            gcongr
      _ = B * Real.exp (-t) := by
            rw [show -t + a = a + -t by ring, Real.exp_add]
            dsimp [B]
            ring
  have hWnorm := hExp μ W hW hWtail
  have hYW : Y = (σ / a) • W := by
    funext ω
    dsimp [W]
    field_simp
  rw [hYW, eLpNorm_const_smul]
  calc
    ‖σ / a‖ₑ * eLpNorm W (ENNReal.ofReal p) μ
        ≤ ‖σ / a‖ₑ * ENNReal.ofReal D := by gcongr
    _ = ENNReal.ofReal ((D / a) * σ) := by
      rw [← ofReal_norm]
      have hc : 0 ≤ σ / a := div_nonneg hσ.le ha.le
      rw [Real.norm_of_nonneg hc, ← ENNReal.ofReal_mul hc]
      congr 1
      ring

private lemma eLpNorm_le_of_hansonWright_tail (p : ℝ) (hp : 1 ≤ p) :
    ∃ Cp : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (Y : Ω → ℝ) (σ : ℝ),
      AEMeasurable Y μ → 0 < σ →
      (∀ t : ℝ, 0 ≤ t →
        (μ {ω | t ≤ |Y ω|}).toReal ≤
          2 * Real.exp (-(1 / (4 * (64 * Real.exp 1 ^ 3))) *
            min (t ^ 2 / σ ^ 2) (t / σ))) →
      eLpNorm Y (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (Cp * σ) := by
  exact eLpNorm_le_of_two_scale_tail p hp
    (1 / (4 * (64 * Real.exp 1 ^ 3))) (by positivity)

/-- Statement of `Muon.External.GaussianQuadFormLp`. -/
theorem gaussianQuadFormLp :
    ∀ p : ℝ, 1 ≤ p → ∃ Cp : ℝ, ∀ n : ℕ,
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (z : Ω → Fin n → ℝ),
      IsStdGaussianVector μ z →
      ∀ F : Matrix (Fin n) (Fin n) ℝ,
        eLpNorm (fun ω => dotProduct (z ω) (Matrix.mulVec F (z ω)) - Matrix.trace F)
            (ENNReal.ofReal p) μ
          ≤ ENNReal.ofReal (Cp * frobNorm F) := by
  intro p hp
  obtain ⟨Cp, hCp⟩ := eLpNorm_le_of_hansonWright_tail p hp
  refine ⟨Cp, ?_⟩
  intro n Ω _ μ _ z hz F
  let X : Fin n → Ω → ℝ := fun i ω => z ω i
  let Y : Ω → ℝ := fun ω =>
    dotProduct (z ω) (Matrix.mulVec F (z ω)) - Matrix.trace F
  obtain ⟨hzmeas, hindep, hsubG⟩ := stdGaussianVector_data μ z hz
  obtain ⟨hFrob, hop_le, hop_pos, hF_zero⟩ := matrix_norm_data F
  by_cases hσ : frobNorm F = 0
  · have hF : F = 0 := hF_zero hσ
    subst F
    simp [frobNorm]
  · have hσpos : 0 < frobNorm F :=
      lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hσ)
    have hY : HansonWright.centeredQuadraticForm μ F X = Y := by
      simpa [X, Y] using centeredQuadraticForm_eq μ z hz F
    have hYmeas : AEMeasurable Y μ := by
      dsimp [Y]
      fun_prop
    apply hCp μ Y (frobNorm F) hYmeas hσpos
    intro t ht
    have hHW := HansonWright.hanson_wright_inequality
      (μ := μ) (A := F) (X := X) (K := (1 : ℝ))
      (C := 64 * Real.exp 1 ^ 3) (t := t)
      (by positivity) (by positivity)
      (by
        have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
        have hepow : Real.exp 1 ≤ Real.exp 1 ^ 3 := by
          calc
            Real.exp 1 = Real.exp 1 * 1 := by ring
            _ ≤ Real.exp 1 * Real.exp 1 ^ 2 := by
              gcongr
              exact one_le_pow₀ he
            _ = Real.exp 1 ^ 3 := by ring
        nlinarith)
      (by nlinarith [pow_pos (Real.exp_pos 1) 3])
      (by
        have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
        have h16 : 16 * Real.exp 1 ≤ 4096 * Real.exp 1 := by
          nlinarith [Real.exp_pos 1]
        have hepow : Real.exp 1 ≤ Real.exp 1 ^ 6 := by
          calc
            Real.exp 1 = Real.exp 1 * 1 := by ring
            _ ≤ Real.exp 1 * Real.exp 1 ^ 5 := by
              gcongr
              exact one_le_pow₀ he
            _ = Real.exp 1 ^ 6 := by ring
        nlinarith)
      (by
        have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
        nlinarith [mul_nonneg (sq_nonneg (Real.exp 1)) (sub_nonneg.mpr he)])
      (by simpa [hFrob] using hσpos) (hop_pos hσpos)
      hindep (fun i => by
        have hone : (⟨(1 : ℝ) ^ 2, sq_nonneg 1⟩ : ℝ≥0) = 1 := by
          ext
          norm_num
        rw [hone]
        exact hsubG i) ht
    rw [hY] at hHW
    calc
      (μ {ω | t ≤ |Y ω|}).toReal
          ≤ 2 * Real.exp (-(1 / (4 * (64 * Real.exp 1 ^ 3))) *
              min (t ^ 2 / (1 ^ 4 * HansonWright.frobeniusNorm F ^ 2))
                (t / (1 ^ 2 * HansonWright.operatorNorm F))) := hHW
      _ ≤ 2 * Real.exp (-(1 / (4 * (64 * Real.exp 1 ^ 3))) *
              min (t ^ 2 / frobNorm F ^ 2) (t / frobNorm F)) := by
        have hratio : t / frobNorm F ≤ t / HansonWright.operatorNorm F :=
          div_le_div_of_nonneg_left ht (hop_pos hσpos) hop_le
        have hmin :
            min (t ^ 2 / frobNorm F ^ 2) (t / frobNorm F) ≤
              min (t ^ 2 / frobNorm F ^ 2) (t / HansonWright.operatorNorm F) :=
          min_le_min_left _ hratio
        simp only [one_pow, one_mul]
        rw [hFrob]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonpos_left hmin (neg_nonpos.mpr (by positivity))

end GaussianFoundations
