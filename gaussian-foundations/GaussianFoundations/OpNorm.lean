import GaussianFoundations.Defs
import SLT.RMT.Basic
import SLT.GaussianLipConcen
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Rectangular Gaussian matrices: operator-norm tail and `L^6` bounds (Vershynin, HDP Thm 4.4.5, Gaussian case).
-/

namespace GaussianFoundations

open MeasureTheory ProbabilityTheory
open scoped ENNReal

private def vectorize {p q : ℕ} (Y : Matrix (Fin p) (Fin q) ℝ) : Fin p × Fin q → ℝ :=
  fun ij => Y ij.1 ij.2

private def unvectorize {p q : ℕ} (z : Fin p × Fin q → ℝ) : Matrix (Fin p) (Fin q) ℝ :=
  fun i j => z (i, j)

private lemma vectorize_aemeasurable_of_iid {p q : ℕ}
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → Matrix (Fin p) (Fin q) ℝ) (hY : IsIIDGaussianMatrix μ Y) :
    AEMeasurable (fun ω => vectorize (Y ω)) μ := by
  classical
  let I := Fin p × Fin q
  by_cases hI : Nonempty I
  · let i : I := Classical.choice hI
    by_contra h
    have hμ : μ ≠ 0 := by
      intro hz
      have hu : μ Set.univ = 1 := measure_univ
      rw [hz] at hu
      simp at hu
    have hdirac := Measure.map_of_not_aemeasurable_of_ne_zero h hμ
    let a : I → ℝ := Classical.ofNonempty
    have hlaw : μ.map (fun ω => vectorize (Y ω)) =
        Measure.pi (fun _ : I => gaussianReal 0 1) := by
      unfold vectorize
      exact hY
    have hpi : Measure.pi (fun _ : I => gaussianReal 0 1) = Measure.dirac a := by
      exact hlaw.symm.trans (by simpa [a, I] using hdirac)
    have heval := congrArg (fun m : Measure (I → ℝ) => m.map (fun z => z i)) hpi
    have hgauss : (Measure.pi (fun _ : I => gaussianReal 0 1)).map (fun z => z i) =
        gaussianReal 0 1 := (measurePreserving_eval (fun _ : I => gaussianReal 0 1) i).map_eq
    rw [hgauss, Measure.map_dirac' (measurable_pi_apply i)] at heval
    haveI : NullSingletonClass (gaussianReal 0 1) :=
      nullSingletonClass_gaussianReal (by norm_num)
    have hs := congrArg (fun m : Measure ℝ => m {a i}) heval
    simpa using hs
  · haveI : IsEmpty I := not_nonempty_iff.mp hI
    exact (measurable_of_subsingleton_codomain _).aemeasurable

private lemma measurable_matOpNorm_unvectorize (p q : ℕ) :
    Measurable (fun z : Fin p × Fin q → ℝ => matOpNorm (unvectorize z)) := by
  let Φ : (Fin p × Fin q → ℝ) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin p)) :=
    { toFun := fun z => LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (unvectorize z))
      map_add' := by
        intro x y
        ext v i
        change (∑ j, (x (i, j) + y (i, j)) * v.ofLp j) =
          (∑ j, x (i, j) * v.ofLp j) + ∑ j, y (i, j) * v.ofLp j
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      map_smul' := by
        intro c x
        ext v i
        simp [unvectorize, Matrix.mulVec, dotProduct, mul_assoc]
        rw [Finset.mul_sum] }
  have hΦ : Continuous Φ := Φ.continuous_of_finiteDimensional
  apply Continuous.measurable
  unfold matOpNorm
  exact continuous_norm.comp hΦ

private lemma canonical_gaussian_opNorm_tail (p q : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    let ν := Measure.pi (fun _ : Fin p × Fin q => gaussianReal 0 1)
    ν {z | 24 * (Real.sqrt p + Real.sqrt q + t) < matOpNorm (unvectorize z)}
      ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2))) := by
  classical
  let I := Fin p × Fin q
  let ν : Measure (I → ℝ) := Measure.pi (fun _ : I => gaussianReal 0 1)
  let A : Fin p → Fin q → (I → ℝ) → ℝ := fun i j z => z (i, j)
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  rcases eq_or_lt_of_le ht with rfl | ht
  · calc
      ν {z | 24 * (Real.sqrt p + Real.sqrt q + 0) < matOpNorm (unvectorize z)} ≤ 1 :=
        prob_le_one
      _ ≤ ENNReal.ofReal (2 * Real.exp (-(0 ^ 2))) := by norm_num
  · rcases p.eq_zero_or_pos with rfl | hp
    · have hz : ∀ z : Fin 0 × Fin q → ℝ, matOpNorm (unvectorize z) = 0 := by
        intro z
        unfold matOpNorm
        have hlin : Matrix.toEuclideanLin (unvectorize z) = 0 := by
          ext x i
          exact Fin.elim0 i
        rw [hlin]
        simp
      have hpos : 0 < 24 * (Real.sqrt q + t) := by positivity
      have hempty :
          {z : Fin 0 × Fin q → ℝ | 24 * (Real.sqrt q + t) < matOpNorm (unvectorize z)} = ∅ := by
        ext z
        constructor
        · intro h
          change 24 * (Real.sqrt q + t) < matOpNorm (unvectorize z) at h
          rw [hz] at h
          exact (not_lt_of_ge hpos.le h).elim
        · intro h
          simp at h
      have hle : ν {z | 24 * (Real.sqrt q + t) < matOpNorm (unvectorize z)} ≤
          ENNReal.ofReal (2 * Real.exp (-(t ^ 2))) := by
        rw [hempty, measure_empty]
        positivity
      simpa [ν] using hle
    rcases q.eq_zero_or_pos with rfl | hq
    · have hpos : 0 < 24 * (Real.sqrt p + t) := by positivity
      have hempty :
          {z : Fin p × Fin 0 → ℝ | 24 * (Real.sqrt p + t) < matOpNorm (unvectorize z)} = ∅ := by
        ext z
        constructor
        · intro h
          change 24 * (Real.sqrt p + t) < matOpNorm (unvectorize z) at h
          have hz : matOpNorm (unvectorize z) = 0 := by simp [matOpNorm]
          rw [hz] at h
          exact (not_lt_of_ge hpos.le h).elim
        · intro h
          simp at h
      have hle : ν {z | 24 * (Real.sqrt p + t) < matOpNorm (unvectorize z)} ≤
          ENNReal.ofReal (2 * Real.exp (-(t ^ 2))) := by
        rw [hempty, measure_empty]
        positivity
      simpa [ν] using hle
    have hind : iIndepFun (fun x : I => A x.1 x.2) ν := by
      dsimp [A, ν]
      exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)
    have hsub : ∀ i j, HasSubgaussianMGF (A i j) (1 : NNReal) ν := by
      intro i j
      have hmap : ν.map (fun z : I → ℝ => z (i, j)) = gaussianReal 0 1 :=
        (measurePreserving_eval (fun _ : I => gaussianReal 0 1) (i, j)).map_eq
      have h := HansonWright.hasSubgaussianMGF_id_gaussianReal_zero_one
      rw [← hmap] at h
      have hof := HasSubgaussianMGF.of_map (X := id)
        (measurable_pi_apply (i, j)).aemeasurable h
      simpa [A, Function.comp_def] using hof
    let S : ℝ := Real.sqrt p + Real.sqrt q + t
    have hS : 0 < S := by
      dsimp [S]
      positivity
    have hu : 0 < 12 * S := mul_pos (by norm_num) hS
    have htail := RMT.matrixOperatorNorm_tail_le_of_entrywise_subgaussian
      (m := p) (n := q) hp hq (A := A) (μ := ν) (K := 1) (u := 12 * S)
      one_pos hind (fun i j => by
        have heq : (⟨(1 : ℝ) ^ 2, sq_nonneg 1⟩ : NNReal) = 1 := by ext; norm_num
        rw [heq]
        exact hsub i j) hu
    have hpref := RMT.rectangular_net_tail_prefactor_le
      (m := p) (n := q) (K := 1) (t := t) one_pos ht
    have hweak :
        2 * 17 ^ (p + q) * Real.exp (-(12 * S) ^ 2 / (2 * 1 ^ 2)) ≤
          2 * 17 ^ (p + q) * Real.exp (-(12 * S) ^ 2 / (8 * 1 ^ 2)) := by
      apply mul_le_mul_of_nonneg_left
      · apply Real.exp_le_exp.mpr
        nlinarith [sq_nonneg (12 * S)]
      · positivity
    have hreal :
        (ν {z | 24 * S < matOpNorm (unvectorize z)}).toReal ≤
          2 * Real.exp (-(t ^ 2)) := by
      have h := htail.trans (hweak.trans (by simpa [S] using hpref))
      have hmat : ∀ z, RMT.randomMatrix A z = unvectorize z := by
        intro z
        rfl
      simp_rw [hmat] at h
      have hthr : 2 * (12 * S) = 24 * S := by ring
      rw [hthr] at h
      simpa [S, RMT.matrixOperatorNorm, matOpNorm] using h
    change ν {z | 24 * S < matOpNorm (unvectorize z)} ≤ _
    rw [← ENNReal.ofReal_toReal (measure_ne_top ν _)]
    exact ENNReal.ofReal_le_ofReal hreal

private lemma eLpNorm_six_le_two_of_gaussian_tail {A : Type} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (Z : A → ℝ) (hZ : Measurable Z)
    (hZ0 : ∀ a, 0 ≤ Z a)
    (htail : ∀ t : ℝ, 0 ≤ t →
      μ {a | t < Z a} ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2)))) :
    eLpNorm Z 6 μ ≤ 2 := by
  let g : ℝ → ℝ := fun t => 6 * t ^ 5
  have hgint : ∀ t > 0, IntervalIntegrable g volume 0 t := by
    intro t ht
    apply Continuous.intervalIntegrable
    dsimp [g]
    fun_prop
  have hgnn : ∀ᵐ t ∂volume.restrict (Set.Ioi 0), 0 ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    dsimp [g]
    exact mul_nonneg (by norm_num) (pow_nonneg ht.le _)
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul μ
    (ae_of_all μ hZ0) hZ.aemeasurable hgint hgnn
  have hintpow : ∀ a, (∫ t in 0..Z a, g t) = (Z a) ^ 6 := by
    intro a
    dsimp [g]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    ring
  simp_rw [hintpow] at hlayer
  have hright :
      ∫⁻ t in Set.Ioi (0 : ℝ), μ {a | t < Z a} * ENNReal.ofReal (g t)
        ≤ ENNReal.ofReal 12 := by
    calc
      ∫⁻ t in Set.Ioi (0 : ℝ), μ {a | t < Z a} * ENNReal.ofReal (g t)
          ≤ ∫⁻ t in Set.Ioi (0 : ℝ),
              ENNReal.ofReal (12 * t ^ 5 * Real.exp (-t ^ 2)) := by
            apply setLIntegral_mono' measurableSet_Ioi
            intro t ht
            have ht0 : 0 ≤ t := (Set.mem_Ioi.mp ht).le
            calc
              μ {a | t < Z a} * ENNReal.ofReal (g t)
                  ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2))) * ENNReal.ofReal (g t) :=
                    by
                      gcongr
                      exact htail t ht0
              _ = ENNReal.ofReal (12 * t ^ 5 * Real.exp (-t ^ 2)) := by
                rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.exp (-(t ^ 2)))]
                congr 1
                dsimp [g]
                ring
      _ = ENNReal.ofReal 12 := by
        have hint : IntegrableOn
            (fun t : ℝ => 12 * t ^ 5 * Real.exp (-t ^ 2)) (Set.Ioi 0) := by
          have hbase := integrableOn_rpow_mul_exp_neg_rpow
            (p := (2 : ℝ)) (s := (5 : ℝ)) (by norm_num) (by norm_num)
          apply (hbase.const_mul 12).congr
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          change 12 * (Real.rpow t 5 * Real.exp (-Real.rpow t 2)) =
            12 * t ^ 5 * Real.exp (-t ^ 2)
          have h5 : Real.rpow t (5 : ℝ) = t ^ 5 := by
            convert Real.rpow_natCast t 5 using 1 <;> norm_num
          have h2 : Real.rpow t (2 : ℝ) = t ^ 2 := by
            convert Real.rpow_natCast t 2 using 1 <;> norm_num
          rw [h5, h2]
          ring
        rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
          ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => by
            exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ht.le _))
              (Real.exp_pos _).le)]
        congr 1
        have h := integral_rpow_mul_exp_neg_rpow (p := (2 : ℝ)) (q := (5 : ℝ))
          (by norm_num) (by norm_num)
        have hnat : ∫ x in Set.Ioi (0 : ℝ), x ^ 5 * Real.exp (-x ^ 2) =
            (1 / 2 : ℝ) * Real.Gamma ((5 + 1) / 2) := by
          convert h using 1
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          have h5 : Real.rpow x (5 : ℝ) = x ^ 5 := by
            convert Real.rpow_natCast x 5 using 1 <;> norm_num
          have h2 : Real.rpow x (2 : ℝ) = x ^ 2 := by
            convert Real.rpow_natCast x 2 using 1 <;> norm_num
          change x ^ (5 : ℕ) * Real.exp (-(x ^ (2 : ℕ))) =
            Real.rpow x 5 * Real.exp (-Real.rpow x 2)
          rw [h5, h2]
        calc
          ∫ x in Set.Ioi (0 : ℝ), 12 * x ^ 5 * Real.exp (-x ^ 2) =
              ∫ x in Set.Ioi (0 : ℝ), 12 * (x ^ 5 * Real.exp (-x ^ 2)) := by
                congr 1
                funext x
                ring
          _ = 12 * ∫ x in Set.Ioi (0 : ℝ), x ^ 5 * Real.exp (-x ^ 2) := by
            rw [MeasureTheory.integral_const_mul]
          _ = 12 := by
            rw [hnat]
            norm_num [Real.Gamma_nat_eq_factorial]
  have hpows : eLpNorm Z 6 μ ^ (6 : ℝ) ≤ (2 : ENNReal) ^ (6 : ℝ) := by
    have heq := eLpNorm_nnreal_pow_eq_lintegral
      (f := Z) (p := (6 : NNReal)) (μ := μ) (by norm_num) hZ.aestronglyMeasurable
    have hleft : (∫⁻ a, ‖Z a‖ₑ ^ (6 : ℝ) ∂μ) =
        ∫⁻ a, ENNReal.ofReal (Z a ^ 6) ∂μ := by
      apply lintegral_congr
      intro a
      rw [← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (Z a)) (by norm_num : (0 : ℝ) ≤ 6)]
      congr 1
      rw [Real.norm_eq_abs, abs_of_nonneg (hZ0 a)]
      convert Real.rpow_natCast (Z a) 6 using 1 <;> norm_num
    calc
      eLpNorm Z 6 μ ^ (6 : ℝ) = ∫⁻ a, ‖Z a‖ₑ ^ (6 : ℝ) ∂μ := by
        simpa using heq
      _ = ∫⁻ a, ENNReal.ofReal (Z a ^ 6) ∂μ := hleft
      _ = ∫⁻ t in Set.Ioi (0 : ℝ),
          μ {a | t < Z a} * ENNReal.ofReal (g t) := hlayer
      _ ≤ ENNReal.ofReal 12 := hright
      _ ≤ ENNReal.ofReal (2 ^ 6) := ENNReal.ofReal_le_ofReal (by norm_num)
      _ = (2 : ENNReal) ^ (6 : ℝ) := by norm_num
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 6)).mp hpows

private lemma canonical_gaussian_opNorm_L6 (p q : ℕ) :
    let ν := Measure.pi (fun _ : Fin p × Fin q => gaussianReal 0 1)
    eLpNorm (fun z => matOpNorm (unvectorize z)) 6 ν
      ≤ ENNReal.ofReal (100 * (Real.sqrt p + Real.sqrt q)) := by
  classical
  let I := Fin p × Fin q
  let ν : Measure (I → ℝ) := Measure.pi (fun _ : I => gaussianReal 0 1)
  let X : (I → ℝ) → ℝ := fun z => matOpNorm (unvectorize z)
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  change eLpNorm X 6 ν ≤ ENNReal.ofReal (100 * (Real.sqrt p + Real.sqrt q))
  rcases p.eq_zero_or_pos with rfl | hp
  · have hX : ∀ z : Fin 0 × Fin q → ℝ, X z = 0 := by
      intro z
      dsimp [X]
      unfold matOpNorm
      have hlin : Matrix.toEuclideanLin (unvectorize z) = 0 := by
        ext x i
        exact Fin.elim0 i
      rw [hlin]
      simp
    have hXfun : X = 0 := funext hX
    rw [hXfun]
    simp
  rcases q.eq_zero_or_pos with rfl | hq
  · have hX : ∀ z : Fin p × Fin 0 → ℝ, X z = 0 := by
      intro z
      dsimp [X]
      simp [matOpNorm]
    have hXfun : X = 0 := funext hX
    rw [hXfun]
    simp
  let S : ℝ := Real.sqrt p + Real.sqrt q
  let Z : (I → ℝ) → ℝ := fun z => max ((X z - 24 * S) / 24) 0
  have hS : 0 < S := by
    dsimp [S]
    positivity
  have hXmeas : Measurable X := by
    dsimp [X, I]
    exact measurable_matOpNorm_unvectorize p q
  have hZmeas : Measurable Z := by
    dsimp [Z]
    fun_prop
  have hZ0 : ∀ z, 0 ≤ Z z := by
    intro z
    exact le_max_right _ _
  have htailZ : ∀ t : ℝ, 0 ≤ t →
      ν {z | t < Z z} ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2))) := by
    intro t ht
    have hset : {z | t < Z z} = {z | 24 * (S + t) < X z} := by
      ext z
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h
        have h' : t < (X z - 24 * S) / 24 := by
          rcases (lt_max_iff.mp h) with hleft | hright
          · exact hleft
          · exact (not_lt_of_ge ht hright).elim
        nlinarith
      · intro h
        apply lt_max_of_lt_left
        nlinarith
    rw [hset]
    have h := canonical_gaussian_opNorm_tail p q t ht
    simpa [ν, I, X, S] using h
  have hZLp : eLpNorm Z 6 ν ≤ 2 :=
    eLpNorm_six_le_two_of_gaussian_tail ν Z hZmeas hZ0 htailZ
  let B : (I → ℝ) → ℝ := fun z => 24 * S + 24 * Z z
  have hXB : ∀ z, ‖X z‖ ≤ ‖B z‖ := by
    intro z
    have hX0 : 0 ≤ X z := norm_nonneg _
    have hle : X z ≤ B z := by
      have hm := le_max_left ((X z - 24 * S) / 24) 0
      dsimp [B, Z]
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg hX0, Real.norm_eq_abs,
      abs_of_nonneg (le_trans hX0 hle)]
    exact hle
  have hmono : eLpNorm X 6 ν ≤ eLpNorm B 6 ν :=
    eLpNorm_mono hXmeas.aestronglyMeasurable hXB
  have htri : eLpNorm B 6 ν ≤
      eLpNorm (fun _ : I → ℝ => 24 * S) 6 ν +
        eLpNorm (fun z => 24 * Z z) 6 ν := by
    have hB : B = (fun _ : I → ℝ => 24 * S) + (fun z => 24 * Z z) := by
      funext z
      rfl
    rw [hB]
    exact eLpNorm_add_le (p := (6 : ENNReal)) (μ := ν)
      (f := fun _ : I → ℝ => 24 * S) (g := fun z => 24 * Z z) (by norm_num)
  have hconst : eLpNorm (fun _ : I → ℝ => 24 * S) 6 ν =
      ENNReal.ofReal (24 * S) := by
    rw [eLpNorm_const (24 * S) (by norm_num) (NeZero.ne ν)]
    simp only [measure_univ, ENNReal.one_rpow, mul_one]
    rw [← ofReal_norm]
    congr 1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hS.le)]
  have hsmul : eLpNorm (fun z => 24 * Z z) 6 ν =
      (24 : ENNReal) * eLpNorm Z 6 ν := by
    change eLpNorm ((24 : ℝ) • Z) 6 ν = _
    rw [eLpNorm_const_smul]
    congr 1
    rw [← ofReal_norm]
    norm_num
  have hbound : eLpNorm B 6 ν ≤ ENNReal.ofReal (100 * S) := by
    calc
      eLpNorm B 6 ν ≤
          eLpNorm (fun _ : I → ℝ => 24 * S) 6 ν +
            eLpNorm (fun z => 24 * Z z) 6 ν := htri
      _ = ENNReal.ofReal (24 * S) + (24 : ENNReal) * eLpNorm Z 6 ν := by
        rw [hconst, hsmul]
      _ ≤ ENNReal.ofReal (24 * S) + (24 : ENNReal) * 2 := by
        gcongr
      _ ≤ ENNReal.ofReal (100 * S) := by
        rw [← ENNReal.ofReal_ofNat 24, ← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 24),
          ← ENNReal.ofReal_add (mul_nonneg (by norm_num) hS.le) (by norm_num)]
        apply ENNReal.ofReal_le_ofReal
        nlinarith [show (2 : ℝ) ≤ S by
          have hp1 : (1 : ℝ) ≤ Real.sqrt p := by
            have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
            nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ p),
              Real.sqrt_nonneg (p : ℝ)]
          have hq1 : (1 : ℝ) ≤ Real.sqrt q := by
            have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
            nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ q),
              Real.sqrt_nonneg (q : ℝ)]
          dsimp [S]
          linarith]
  exact hmono.trans hbound

/-- Statement of `Muon.External.GaussianOpNorm`. -/
theorem gaussianOpNorm :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ p q : ℕ, ∀ t : ℝ, 0 ≤ t →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Y : Ω → Matrix (Fin p) (Fin q) ℝ),
      IsIIDGaussianMatrix μ Y →
        μ {ω | C₀ * (Real.sqrt p + Real.sqrt q + t) < matOpNorm (Y ω)}
          ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2))) := by
  refine ⟨24, by norm_num, ?_⟩
  intro p q t ht Ω _ μ _ Y hY
  let f : Ω → (Fin p × Fin q → ℝ) := fun ω => vectorize (Y ω)
  let s : Set (Fin p × Fin q → ℝ) :=
    {z | 24 * (Real.sqrt p + Real.sqrt q + t) < matOpNorm (unvectorize z)}
  have hf : AEMeasurable f μ := vectorize_aemeasurable_of_iid μ Y hY
  have hs : MeasurableSet s := by
    exact measurableSet_lt measurable_const (measurable_matOpNorm_unvectorize p q)
  have hpre : f ⁻¹' s =
      {ω | 24 * (Real.sqrt p + Real.sqrt q + t) < matOpNorm (Y ω)} := by
    ext ω
    rfl
  have hlaw : μ.map f = Measure.pi (fun _ : Fin p × Fin q => gaussianReal 0 1) := by
    change μ.map (fun ω => vectorize (Y ω)) = _
    unfold vectorize
    exact hY
  rw [← hpre, ← Measure.map_apply_of_aemeasurable hf hs, hlaw]
  exact canonical_gaussian_opNorm_tail p q t ht

/-- Statement of `Muon.External.GaussianOpNormL6`. -/
theorem gaussianOpNormL6 :
    ∃ C : ℝ, 0 < C ∧ ∀ p q : ℕ,
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Y : Ω → Matrix (Fin p) (Fin q) ℝ),
      IsIIDGaussianMatrix μ Y →
        eLpNorm (fun ω => matOpNorm (Y ω)) 6 μ
          ≤ ENNReal.ofReal (C * (Real.sqrt p + Real.sqrt q)) := by
  refine ⟨100, by norm_num, ?_⟩
  intro p q Ω _ μ _ Y hY
  let f : Ω → (Fin p × Fin q → ℝ) := fun ω => vectorize (Y ω)
  let g : (Fin p × Fin q → ℝ) → ℝ := fun z => matOpNorm (unvectorize z)
  have hf : AEMeasurable f μ := vectorize_aemeasurable_of_iid μ Y hY
  have hg : AEStronglyMeasurable g (μ.map f) :=
    (measurable_matOpNorm_unvectorize p q).aestronglyMeasurable
  have hcomp : g ∘ f = fun ω => matOpNorm (Y ω) := by
    funext ω
    rfl
  have hlaw : μ.map f = Measure.pi (fun _ : Fin p × Fin q => gaussianReal 0 1) := by
    change μ.map (fun ω => vectorize (Y ω)) = _
    unfold vectorize
    exact hY
  rw [← hcomp, ← eLpNorm_map_measure hg hf, hlaw]
  exact canonical_gaussian_opNorm_L6 p q

end GaussianFoundations
