import SLT.RMT.Lieb
import Mathlib

/-!
# Matrix martingale trace-MGF bound, Golden–Thompson free

For a martingale-difference sequence of `d × d` real symmetric matrices `Z_b` with `‖Z_b‖ ≤ c`
(adapted: `Z_b` is `ℱ (b+1)`-measurable, conditional mean zero given `ℱ b`),
`E tr exp(u ∑_{b<j} Z_b) ≤ d · exp(j u² c² / 2)`.

This is the statement of the private helper `mm_trace_mgf` of `Muon/Dynamics/Diffuse.lean` without its
Golden–Thompson certificate argument. Route (Tropp, *An Introduction to Matrix Concentration
Inequalities*, §3–4 and Ch. 7): Lieb's concavity theorem (proved in SLT, `SLT/RMT/Lieb.lean`) applied
conditionally on `ℱ b`, plus the matrix Hoeffding step `E[e^{uZ} | ℱ b] ⪯ cosh(uc) · I`.
-/

namespace MatrixConcentration

open MeasureTheory Set Matrix Topology Filter
open scoped MatrixOrder Matrix.Norms.L2Operator

/-- Operator norm of a real matrix as a map between Euclidean spaces; verbatim `Muon.opNorm`
(`Muon/Foundations/Conventions.lean`), specialised to `ℝ`. -/
noncomputable def opNorm {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin K)‖

private theorem opNorm_eq_norm {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ) :
    opNorm K = ‖K‖ := by
  rw [Matrix.l2_opNorm_def]
  rfl

private lemma mm_abs_entry_le_opNorm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (i j : Fin d) : |A i j| ≤ opNorm A := by
  have h₁ := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single j (1 : ℝ))
  have h₂ := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin d) ℝ).symm
    (A *ᵥ ⇑(EuclideanSpace.single j (1 : ℝ)))) i
  have h₃ : ((EuclideanSpace.equiv (Fin d) ℝ).symm
      (A *ᵥ ⇑(EuclideanSpace.single j (1 : ℝ)))) i = A i j := by
    simp
  simp only [PiLp.norm_single, norm_one, mul_one] at h₁
  rw [h₃, Real.norm_eq_abs] at h₂
  rw [opNorm_eq_norm]
  linarith

private lemma mm_partial_sum_measurable {Ω : Type*}
    (d : ℕ) (ℱ : ℕ → MeasurableSpace Ω) (hmono : Monotone ℱ)
    (Z : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
    (hmeas : ∀ b i j, Measurable[ℱ (b + 1)] (fun ω => Z b ω i j))
    (j : ℕ) : Measurable[ℱ j] (fun ω => ∑ b ∈ Finset.range j, Z b ω) := by
  let : MeasurableSpace Ω := ℱ j
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro k
  simpa only [Matrix.sum_apply] using Finset.measurable_sum (Finset.range j) (fun b hb =>
    (hmeas b i k).mono (hmono (Nat.succ_le_of_lt (Finset.mem_range.mp hb))) le_rfl)

private lemma mm_partial_sum_isHermitian {Ω : Type*} (d : ℕ)
    (Z : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
    (hsa : ∀ b ω, (Z b ω).IsHermitian) (j : ℕ) (ω : Ω) :
    (∑ b ∈ Finset.range j, Z b ω).IsHermitian := by
  exact (isSelfAdjoint_sum _ fun b _ => (hsa b ω).isSelfAdjoint).isHermitian

private lemma mm_exp_chord {c y : ℝ} (hc : 0 < c) (hy : |y| ≤ c) (u : ℝ) :
    Real.exp (u * y) ≤ Real.cosh (u * c) + (y / c) * Real.sinh (u * c) := by
  have ha : 0 ≤ (c - y) / (2 * c) := div_nonneg (sub_nonneg.mpr (abs_le.mp hy).2)
    (by positivity)
  have hb : 0 ≤ (c + y) / (2 * c) := div_nonneg (by linarith [(abs_le.mp hy).1])
    (by positivity)
  have hab : (c - y) / (2 * c) + (c + y) / (2 * c) = 1 := by
    field_simp
    ring
  have harg : (c - y) / (2 * c) * (-(u * c)) +
      (c + y) / (2 * c) * (u * c) = u * y := by
    field_simp
    ring
  have h := convexOn_exp.2 (mem_univ (-(u * c))) (mem_univ (u * c)) ha hb hab
  simp only [smul_eq_mul, harg] at h
  calc
    Real.exp (u * y) ≤ (c - y) / (2 * c) * Real.exp (-(u * c)) +
        (c + y) / (2 * c) * Real.exp (u * c) := h
    _ = Real.cosh (u * c) + (y / c) * Real.sinh (u * c) := by
      rw [Real.cosh_eq, Real.sinh_eq]
      field_simp
      ring

private lemma mm_exp_matrix_chord {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.IsHermitian) {c : ℝ} (hc : 0 < c) (hbd : opNorm A ≤ c) (u : ℝ) :
    NormedSpace.exp (u • A) ≤
      Real.cosh (u * c) • (1 : Matrix (Fin d) (Fin d) ℝ) +
        (Real.sinh (u * c) / c) • A := by
  by_cases hd : d = 0
  · subst d
    apply le_of_eq
    ext i
    exact Fin.elim0 i
  have : NeZero d := ⟨hd⟩
  have hsa : IsSelfAdjoint A := hA.isSelfAdjoint
  have hsau : IsSelfAdjoint (u • A) := (hA.smul (IsSelfAdjoint.all u)).isSelfAdjoint
  have h := cfc_mono (a := A) (f := fun y : ℝ => Real.exp (u * y))
    (g := fun y : ℝ => Real.cosh (u * c) + (Real.sinh (u * c) / c) * y)
    (fun y hy => by
      have hybd : |y| ≤ c := by
        rw [← Real.norm_eq_abs]
        exact (spectrum.norm_le_norm_of_mem hy).trans ((opNorm_eq_norm A) ▸ hbd)
      convert mm_exp_chord hc hybd u using 1
      ring)
  rw [cfc_comp_const_mul u Real.exp A (ha := hsa),
    CFC.real_exp_eq_normedSpace_exp hsau] at h
  simpa only [cfc_const_add (Real.cosh (u * c)) (fun y : ℝ => (Real.sinh (u * c) / c) * y)
      A (ha := hsa), cfc_const_mul_id _ A hsa,
    Algebra.algebraMap_eq_smul_one] using h

private lemma mm_matrix_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (Z : Ω → Matrix (Fin d) (Fin d) ℝ) (hmeas : Measurable Z)
    (c : ℝ) (hbd : ∀ ω, opNorm (Z ω) ≤ c) : Integrable Z P := by
  refine Integrable.mono' (integrable_const c) hmeas.aestronglyMeasurable ?_
  exact ae_of_all P fun ω => (opNorm_eq_norm (Z ω)) ▸ hbd ω

private lemma mm_condExp_matrix_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (m : MeasurableSpace Ω) {d : ℕ}
    (Z : Ω → Matrix (Fin d) (Fin d) ℝ) (hZ : Integrable Z P)
    (hmean : ∀ i j, MeasureTheory.condExp m P (fun ω => Z ω i j) =ᵐ[P] 0) :
    MeasureTheory.condExp m P Z =ᵐ[P] 0 := by
  have hentry : ∀ i j, (fun ω => (MeasureTheory.condExp m P Z) ω i j) =ᵐ[P] 0 := by
    intro i j
    let T := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
    exact (T.comp_condExp_comm hZ).trans (hmean i j)
  filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr (hentry i)] with ω hω
  ext i j
  exact hω i j

private lemma mm_exp_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (Z : Ω → Matrix (Fin d) (Fin d) ℝ) (hmeas : Measurable Z)
    (hsa : ∀ ω, (Z ω).IsHermitian) (c : ℝ) (hbd : ∀ ω, opNorm (Z ω) ≤ c)
    (u : ℝ) : Integrable (fun ω => NormedSpace.exp (u • Z ω)) P := by
  by_cases hd : d = 0
  · subst d
    have heq : (fun ω => NormedSpace.exp (u • Z ω)) = 0 := by
      funext ω
      ext i
      exact Fin.elim0 i
    rw [heq]
    exact integrable_zero _ _ _
  have : NeZero d := ⟨hd⟩
  let : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℝ) :=
    .restrictScalars ℚ ℝ (Matrix (Fin d) (Fin d) ℝ)
  refine Integrable.mono' (integrable_const (Real.exp (|u| * c)))
    (NormedSpace.exp_continuous.measurable.comp
      (hmeas.const_smul u)).aestronglyMeasurable ?_
  refine ae_of_all P fun ω => ?_
  rw [← CFC.real_exp_eq_normedSpace_exp ((hsa ω).smul (IsSelfAdjoint.all u)).isSelfAdjoint,
    ← cfc_comp_const_mul u Real.exp (Z ω) (ha := (hsa ω).isSelfAdjoint)]
  apply norm_cfc_le (Real.exp_nonneg _)
  intro y hy
  have hybd : |y| ≤ opNorm (Z ω) := by
    simpa only [Real.norm_eq_abs, ← opNorm_eq_norm] using spectrum.norm_le_norm_of_mem hy
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    u * y ≤ |u * y| := le_abs_self _
    _ = |u| * |y| := abs_mul _ _
    _ ≤ |u| * c := mul_le_mul_of_nonneg_left (hybd.trans (hbd ω)) (abs_nonneg _)

private lemma mm_condExp_exp_le {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {d : ℕ} (Z : Ω → Matrix (Fin d) (Fin d) ℝ) (hsa : ∀ ω, (Z ω).IsHermitian)
    (hZ : Integrable Z P) (hmean : MeasureTheory.condExp m P Z =ᵐ[P] 0)
    {c : ℝ} (hc : 0 < c) (hbd : ∀ ω, opNorm (Z ω) ≤ c) (u : ℝ)
    (hexp : Integrable (fun ω => NormedSpace.exp (u • Z ω)) P) :
    MeasureTheory.condExp m P (fun ω => NormedSpace.exp (u • Z ω)) ≤ᵐ[P]
      fun _ => Real.exp (u ^ 2 * c ^ 2 / 2) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  let a := Real.cosh (u * c) • (1 : Matrix (Fin d) (Fin d) ℝ)
  let r := Real.sinh (u * c) / c
  have hmono := condExp_mono (m := m) hexp
    ((integrable_const a).add (hZ.smul r))
    (ae_of_all P fun ω => mm_exp_matrix_chord (Z ω) (hsa ω) hc (hbd ω) u)
  have hadd := condExp_add (integrable_const a) (hZ.smul r) m
  have hsmul := condExp_smul r Z m (μ := P)
  filter_upwards [hmono, hadd, hsmul, hmean] with ω hω hsum hmul hzero
  have hle : (MeasureTheory.condExp m P (fun ω => NormedSpace.exp (u • Z ω))) ω ≤ a := by
    simpa only [hsum, Pi.add_apply, condExp_const hm, hmul, Pi.smul_apply,
      hzero, Pi.zero_apply, smul_zero, add_zero] using hω
  refine hle.trans ?_
  apply smul_le_smul_of_nonneg_right _
    (show (0 : Matrix (Fin d) (Fin d) ℝ) ≤ 1 from zero_le_one)
  simpa only [mul_pow] using Real.cosh_le_exp_half_sq (u * c)

private lemma mm_block_mgf {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ)
    (ℱ : ℕ → MeasurableSpace Ω) (hle : ∀ b, ℱ b ≤ mΩ)
    (Z : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (hsa : ∀ b ω, (Z b ω).IsHermitian)
    (hmeas : ∀ b i j, Measurable[ℱ (b + 1)] (fun ω => Z b ω i j))
    (hmean : ∀ b i j, MeasureTheory.condExp (ℱ b) P (fun ω => Z b ω i j) =ᵐ[P] 0)
    {c : ℝ} (hc : 0 < c) (hbd : ∀ b ω, opNorm (Z b ω) ≤ c) (b : ℕ) (u : ℝ) :
    MeasureTheory.condExp (ℱ b) P (fun ω => NormedSpace.exp (u • Z b ω)) ≤ᵐ[P]
      fun _ => Real.exp (u ^ 2 * c ^ 2 / 2) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  have hm : Measurable (Z b) := Measurable.of_eval fun i => Measurable.of_eval fun j =>
    (hmeas b i j).mono (hle (b + 1)) le_rfl
  have hi := mm_matrix_integrable P (Z b) hm c (hbd b)
  exact mm_condExp_exp_le P (ℱ b) (hle b) (Z b) (hsa b) hi
    (mm_condExp_matrix_zero P (ℱ b) (Z b) hi (hmean b)) hc (hbd b) u
    (mm_exp_integrable P (Z b) hm (hsa b) c (hbd b) u)

private lemma mm_partial_sum_norm_le {Ω : Type*} {d : ℕ}
    (Z : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (c : ℝ)
    (hbd : ∀ b ω, opNorm (Z b ω) ≤ c) (j : ℕ) (ω : Ω) :
    opNorm (∑ b ∈ Finset.range j, Z b ω) ≤ (j : ℝ) * c := by
  rw [opNorm_eq_norm]
  calc
    ‖∑ b ∈ Finset.range j, Z b ω‖ ≤ ∑ b ∈ Finset.range j, ‖Z b ω‖ := norm_sum_le _ _
    _ ≤ ∑ _b ∈ Finset.range j, c := Finset.sum_le_sum fun b _ =>
      (opNorm_eq_norm (Z b ω)) ▸ hbd b ω
    _ = (j : ℝ) * c := by simp

private lemma mm_trace_exp_add_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (H Z : Ω → Matrix (Fin d) (Fin d) ℝ) (hHm : Measurable H) (hZm : Measurable Z)
    (hHsa : ∀ ω, (H ω).IsHermitian) (hZsa : ∀ ω, (Z ω).IsHermitian)
    (a z : ℝ) (hHbd : ∀ ω, opNorm (H ω) ≤ a) (hZbd : ∀ ω, opNorm (Z ω) ≤ z) :
    Integrable (fun ω => Matrix.trace (NormedSpace.exp (H ω + Z ω))) P := by
  let T := (Matrix.traceLinearMap (Fin d) ℝ ℝ).toContinuousLinearMap
  apply T.integrable_comp
  simpa only [one_smul] using mm_exp_integrable P (fun ω => H ω + Z ω)
    (hHm.add hZm) (fun ω => (hHsa ω).add (hZsa ω)) (a + z)
    (fun ω => by
      rw [opNorm_eq_norm]
      exact (norm_add_le _ _).trans (add_le_add
        ((opNorm_eq_norm (H ω)) ▸ hHbd ω) ((opNorm_eq_norm (Z ω)) ▸ hZbd ω))) 1

private lemma mm_exp_norm_bound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.IsHermitian) :
    ‖NormedSpace.exp A‖ ≤ Real.exp (opNorm A) := by
  by_cases hd : d = 0
  · subst d
    have hz : NormedSpace.exp A = 0 := by ext i; exact Fin.elim0 i
    rw [hz, norm_zero]
    positivity
  have : NeZero d := ⟨hd⟩
  rw [← CFC.real_exp_eq_normedSpace_exp hA.isSelfAdjoint]
  apply norm_cfc_le (Real.exp_nonneg _)
  intro y hy
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact le_trans (le_abs_self y) (by
    simpa only [Real.norm_eq_abs, ← opNorm_eq_norm] using spectrum.norm_le_norm_of_mem hy)

private lemma mm_simple_partition {Ω E F : Type*} [MeasurableSpace Ω]
    [AddCommMonoid F] (f : SimpleFunc Ω E) (g : E → Ω → F) (ω : Ω) :
    (∑ x ∈ f.range, (f ⁻¹' {x}).indicator (g x) ω) = g (f ω) ω := by
  classical
  rw [Finset.sum_eq_single (f ω)]
  · simp
  · intro b hb hne
    simp [Ne.symm hne]
  · exact fun h => (h (f.mem_range_self ω)).elim

private lemma mm_lieb_constant_step {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] {d : ℕ}
    (H : Matrix (Fin d) (Fin d) ℝ) (Z : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hH : H.IsHermitian) (hZ : ∀ᵐ ω ∂Q, (Z ω).IsHermitian)
    (htrace : Integrable (fun ω => Matrix.trace (NormedSpace.exp (H + Z ω))) Q)
    (hexp : Integrable (fun ω => NormedSpace.exp (Z ω)) Q)
    (k : ℝ) (hk : 0 < k)
    (hmgf : (∫ ω, NormedSpace.exp (Z ω) ∂Q) ≤
      k • (1 : Matrix (Fin d) (Fin d) ℝ)) :
    (∫ ω, Matrix.trace (NormedSpace.exp (H + Z ω)) ∂Q) ≤
      k * Matrix.trace (NormedSpace.exp H) := by
  let M : Matrix (Fin d) (Fin d) ℝ := ∫ ω, NormedSpace.exp (Z ω) ∂Q
  have hMpos : M.PosDef := RMT.integral_exp_posDef_of_ae_isHermitian hZ hexp
  have hlog : CFC.log M ≤ CFC.log (k • (1 : Matrix (Fin d) (Fin d) ℝ)) :=
    Matrix.cfc_log_le_log_of_le_posDef hMpos hmgf
  have hHlogM : (H + CFC.log M).IsHermitian :=
    hH.add (show IsSelfAdjoint (CFC.log M) from IsSelfAdjoint.log).isHermitian
  have hHlogk : (H + CFC.log (k • (1 : Matrix (Fin d) (Fin d) ℝ))).IsHermitian :=
    hH.add (show IsSelfAdjoint (CFC.log (k • (1 : Matrix (Fin d) (Fin d) ℝ))) from
      IsSelfAdjoint.log).isHermitian
  have hmono : Matrix.trace (NormedSpace.exp (H + CFC.log M)) ≤
      Matrix.trace (NormedSpace.exp (H + CFC.log (k • (1 : Matrix (Fin d) (Fin d) ℝ)))) :=
    Matrix.trace_exp_monotone_of_le hHlogM hHlogk
      (by simpa [add_comm] using add_le_add_left hlog H)
  calc
    _ ≤ Matrix.trace (NormedSpace.exp (H + CFC.log M)) :=
      RMT.lieb_inequality_random_matrices_hdp_5_4_9 Q H Z hH hZ htrace hexp
    _ ≤ Matrix.trace
        (NormedSpace.exp (H + CFC.log (k • (1 : Matrix (Fin d) (Fin d) ℝ)))) := hmono
    _ = k * Matrix.trace (NormedSpace.exp H) := by
      rw [← Algebra.algebraMap_eq_smul_one, CFC.log_algebraMap]
      rw [Algebra.algebraMap_eq_smul_one]
      let : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℝ) :=
        .restrictScalars ℚ ℝ (Matrix (Fin d) (Fin d) ℝ)
      rw [← Algebra.algebraMap_eq_smul_one]
      have hc : Commute H
          ((algebraMap ℝ (Matrix (Fin d) (Fin d) ℝ)) (Real.log k)) :=
        (Algebra.commutes _ _).symm
      rw [NormedSpace.exp_add_of_commute hc]
      rw [← NormedSpace.map_exp (algebraMap ℝ (Matrix (Fin d) (Fin d) ℝ))
        (continuous_algebraMap ℝ (Matrix (Fin d) (Fin d) ℝ))]
      rw [← Real.exp_eq_exp_ℝ, Real.exp_log hk, Algebra.algebraMap_eq_smul_one]
      simp

private lemma mm_lieb_fiber_step {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ) (Z : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hH : H.IsHermitian)
    (hZm : @Measurable Ω (Matrix (Fin d) (Fin d) ℝ) mΩ _ Z)
    (hZsa : ∀ ω, (Z ω).IsHermitian)
    (z : ℝ) (hZbd : ∀ ω, opNorm (Z ω) ≤ z) (k : ℝ) (hk : 0 < k)
    (hcond : MeasureTheory.condExp m P (fun ω => NormedSpace.exp (Z ω)) ≤ᵐ[P]
      fun _ => k • (1 : Matrix (Fin d) (Fin d) ℝ))
    (s : Set Ω) (hs : MeasurableSet[m] s) :
    (∫ ω in s, Matrix.trace (NormedSpace.exp (H + Z ω)) ∂P) ≤
      k * P.real s * Matrix.trace (NormedSpace.exp H) := by
  by_cases hs0 : P s = 0
  · have hrs : P.restrict s = 0 := Measure.restrict_eq_zero.mpr hs0
    rw [show (∫ ω in s, Matrix.trace (NormedSpace.exp (H + Z ω)) ∂P) = 0 by
      rw [hrs, integral_zero_measure]]
    simp [measureReal_def, hs0]
  let Q : @Measure Ω mΩ := @ProbabilityTheory.cond Ω mΩ P s
  letI : IsProbabilityMeasure Q := ProbabilityTheory.cond_isProbabilityMeasure hs0
  let X : Ω → Matrix (Fin d) (Fin d) ℝ := fun ω => NormedSpace.exp (Z ω)
  have hXP : Integrable X P := by
    simpa [X] using @mm_exp_integrable Ω mΩ P _ d Z hZm hZsa z hZbd 1
  have htraceP : Integrable (fun ω => Matrix.trace (NormedSpace.exp (H + Z ω))) P :=
    @mm_trace_exp_add_integrable Ω mΩ P _ d (fun _ => H) Z measurable_const hZm
      (fun _ => hH) hZsa (opNorm H) z (fun _ => le_rfl) hZbd
  have hinvtop : (P s)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hs0
  have hXQ : Integrable X Q := by
    exact hXP.restrict.smul_measure hinvtop
  have htraceQ : Integrable (fun ω => Matrix.trace (NormedSpace.exp (H + Z ω))) Q := by
    exact htraceP.restrict.smul_measure hinvtop
  let Y : Ω → Matrix (Fin d) (Fin d) ℝ := MeasureTheory.condExp m P X
  have hseteq : (∫ ω in s, Y ω ∂P) = ∫ ω in s, X ω ∂P := by
    exact setIntegral_condExp hm hXP hs
  have hYint : Integrable Y P := integrable_condExp
  have hsetle : (∫ ω in s, Y ω ∂P) ≤
      ∫ _ω in s, k • (1 : Matrix (Fin d) (Fin d) ℝ) ∂P := by
    exact integral_mono_ae hYint.restrict (integrable_const _)
      (ae_restrict_of_ae hcond)
  have hXsetle : (∫ ω in s, X ω ∂P) ≤
      P.real s • (k • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
    calc
      _ = ∫ ω in s, Y ω ∂P := hseteq.symm
      _ ≤ ∫ _ω in s, k • (1 : Matrix (Fin d) (Fin d) ℝ) ∂P := hsetle
      _ = P.real s • (k • (1 : Matrix (Fin d) (Fin d) ℝ)) := setIntegral_const _
  have hq : 0 < P.real s := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hs0 (measure_ne_top P s)
  have hmgf : (∫ ω, NormedSpace.exp (Z ω) ∂Q) ≤
      k • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [show (fun ω => NormedSpace.exp (Z ω)) = X from rfl]
    change (∫ ω, X ω ∂Q) ≤ _
    simp only [Q, ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv]
    have hscaled := smul_le_smul_of_nonneg_left hXsetle (inv_nonneg.mpr (le_of_lt hq))
    rw [← measureReal_def]
    exact hscaled.trans_eq (inv_smul_smul₀ hq.ne' _)
  have hlieb := @mm_lieb_constant_step Ω mΩ Q _ d H Z hH
    (ae_of_all Q hZsa) htraceQ
    (by simpa [X] using hXQ) k hk hmgf
  simp only [Q, ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv] at hlieb
  change (∫ ω in s, Matrix.trace (NormedSpace.exp (H + Z ω)) ∂P) ≤ _
  have hqne : (P.real s)⁻¹ ≠ 0 := inv_ne_zero hq.ne'
  calc
    _ = P.real s * ((P.real s)⁻¹ •
        ∫ ω in s, Matrix.trace (NormedSpace.exp (H + Z ω)) ∂P) := by
      rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul]
    _ ≤ P.real s * (k * Matrix.trace (NormedSpace.exp H)) :=
      mul_le_mul_of_nonneg_left (by simpa [measureReal_def] using hlieb) hq.le
    _ = _ := by ring

/-- The adapted one-step Lieb recursion.  Its proof uses finite-valued approximation of `H` and
applies SLT's unconditional Lieb inequality on each atom of the approximation. -/
private lemma mm_lieb_adapted_step {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {d : ℕ} (H Z : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hHm : Measurable[m] H) (hHsa : ∀ ω, (H ω).IsHermitian)
    (hZm : @Measurable Ω (Matrix (Fin d) (Fin d) ℝ) mΩ _ Z)
    (hZsa : ∀ ω, (Z ω).IsHermitian)
    (a z : ℝ) (hHbd : ∀ ω, opNorm (H ω) ≤ a) (hZbd : ∀ ω, opNorm (Z ω) ≤ z)
    (hcond : MeasureTheory.condExp m P (fun ω => NormedSpace.exp (Z ω)) ≤ᵐ[P]
      fun _ => Real.exp (z ^ 2 / 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) :
    (∫ ω, Matrix.trace (NormedSpace.exp (H ω + Z ω)) ∂P) ≤
      Real.exp (z ^ 2 / 2) *
        ∫ ω, Matrix.trace (NormedSpace.exp (H ω)) ∂P := by
  let Mat := Matrix (Fin d) (Fin d) ℝ
  letI : NormedAlgebra ℚ Mat := .restrictScalars ℚ ℝ Mat
  let k := Real.exp (z ^ 2 / 2)
  have hk : 0 < k := Real.exp_pos _
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure P
  have ha : 0 ≤ a := (norm_nonneg (H ω₀)).trans (by
    simpa only [← opNorm_eq_norm] using hHbd ω₀)
  have hz : 0 ≤ z := (norm_nonneg (Z ω₀)).trans (by
    simpa only [← opNorm_eq_norm] using hZbd ω₀)
  let Hs : ℕ → @SimpleFunc Ω m Mat := fun n =>
    SimpleFunc.approxOn H hHm (Set.range H ∪ {0}) 0 (by simp) n
  have hHs_mem (n : ℕ) (ω : Ω) : Hs n ω ∈ Set.range H ∪ {0} := by
    simpa [Hs] using SimpleFunc.approxOn_mem hHm (by simp : (0 : Mat) ∈ Set.range H ∪ {0}) n ω
  have hHs_sa (n : ℕ) (ω : Ω) : (Hs n ω).IsHermitian := by
    rcases hHs_mem n ω with ⟨ω', hω'⟩ | hzero
    · rw [← hω']
      exact hHsa ω'
    · rw [hzero]
      simp
  have hHs_bd (n : ℕ) (ω : Ω) : opNorm (Hs n ω) ≤ a := by
    rcases hHs_mem n ω with ⟨ω', hω'⟩ | hzero
    · rw [← hω']
      exact hHbd ω'
    · rw [hzero, opNorm_eq_norm, norm_zero]
      exact ha
  have hHs_meas (n : ℕ) : @Measurable Ω Mat mΩ _ (Hs n) :=
    (Hs n).measurable.mono hm le_rfl
  have hHs_tendsto (ω : Ω) : Filter.Tendsto (fun n => Hs n ω) Filter.atTop (𝓝 (H ω)) := by
    exact SimpleFunc.tendsto_approxOn hHm (by simp : (0 : Mat) ∈ Set.range H ∪ {0})
      (subset_closure (Or.inl ⟨ω, rfl⟩))
  have hsimple (n : ℕ) :
      (∫ ω, Matrix.trace (NormedSpace.exp (Hs n ω + Z ω)) ∂P) ≤
        k * ∫ ω, Matrix.trace (NormedSpace.exp (Hs n ω)) ∂P := by
    classical
    let f := Hs n
    have hf_sa (h : Mat) (hh : h ∈ f.range) : h.IsHermitian := by
      rw [SimpleFunc.mem_range] at hh
      obtain ⟨ω, rfl⟩ := hh
      exact hHs_sa n ω
    have hf_bd (h : Mat) (hh : h ∈ f.range) : opNorm h ≤ a := by
      rw [SimpleFunc.mem_range] at hh
      obtain ⟨ω, rfl⟩ := hh
      exact hHs_bd n ω
    have hleft_int (h : Mat) (hh : h ∈ f.range) :
        Integrable (fun ω => Matrix.trace (NormedSpace.exp (h + Z ω))) P :=
      @mm_trace_exp_add_integrable Ω mΩ P _ d (fun _ => h) Z measurable_const hZm
        (fun _ => hf_sa h hh) hZsa a z (fun _ => hf_bd h hh) hZbd
    have hright_int (h : Mat) (hh : h ∈ f.range) :
        Integrable (fun _ω : Ω => Matrix.trace (NormedSpace.exp h)) P := integrable_const _
    have hleft_decomp :
        (∫ ω, Matrix.trace (NormedSpace.exp (f ω + Z ω)) ∂P) =
          ∑ h ∈ f.range,
            ∫ ω in (f ⁻¹' {h}), Matrix.trace (NormedSpace.exp (h + Z ω)) ∂P := by
      calc
        _ = ∫ ω, ∑ h ∈ f.range,
            (f ⁻¹' {h}).indicator
              (fun ω => Matrix.trace (NormedSpace.exp (h + Z ω))) ω ∂P := by
          apply integral_congr_ae
          exact ae_of_all P fun ω => (mm_simple_partition f
            (fun h ω => Matrix.trace (NormedSpace.exp (h + Z ω))) ω).symm
        _ = ∑ h ∈ f.range, ∫ ω,
            (f ⁻¹' {h}).indicator
              (fun ω => Matrix.trace (NormedSpace.exp (h + Z ω))) ω ∂P := by
          apply integral_finsetSum
          intro h hh
          exact (hleft_int h hh).indicator (hm _ (f.measurableSet_preimage {h}))
        _ = _ := by
          apply Finset.sum_congr rfl
          intro h hh
          rw [integral_indicator (hm _ (f.measurableSet_preimage {h}))]
    have hright_decomp :
        (∫ ω, Matrix.trace (NormedSpace.exp (f ω)) ∂P) =
          ∑ h ∈ f.range,
            ∫ ω in (f ⁻¹' {h}), Matrix.trace (NormedSpace.exp h) ∂P := by
      calc
        _ = ∫ ω, ∑ h ∈ f.range,
            (f ⁻¹' {h}).indicator
              (fun _ω => Matrix.trace (NormedSpace.exp h)) ω ∂P := by
          apply integral_congr_ae
          exact ae_of_all P fun ω => (mm_simple_partition f
            (fun h _ω => Matrix.trace (NormedSpace.exp h)) ω).symm
        _ = ∑ h ∈ f.range, ∫ ω,
            (f ⁻¹' {h}).indicator
              (fun _ω => Matrix.trace (NormedSpace.exp h)) ω ∂P := by
          apply integral_finsetSum
          intro h hh
          exact (hright_int h hh).indicator (hm _ (f.measurableSet_preimage {h}))
        _ = _ := by
          apply Finset.sum_congr rfl
          intro h hh
          rw [integral_indicator (hm _ (f.measurableSet_preimage {h}))]
    rw [hleft_decomp, hright_decomp, Finset.mul_sum]
    exact Finset.sum_le_sum fun h hh => by
      rw [setIntegral_const, smul_eq_mul]
      convert @mm_lieb_fiber_step Ω mΩ P _ m hm d h Z (hf_sa h hh) hZm hZsa z hZbd k hk
          (by simpa [k] using hcond) (f ⁻¹' {h}) (f.measurableSet_preimage {h}) using 1 <;>
        ring
  let T := (Matrix.traceLinearMap (Fin d) ℝ ℝ).toContinuousLinearMap
  have htrace_norm_bound (A : Mat) (hA : A.IsHermitian) (r : ℝ)
      (hAr : opNorm A ≤ r) :
      ‖Matrix.trace (NormedSpace.exp A)‖ ≤ ‖T‖ * Real.exp r := by
    calc
      ‖Matrix.trace (NormedSpace.exp A)‖ = ‖T (NormedSpace.exp A)‖ := rfl
      _ ≤ ‖T‖ * ‖NormedSpace.exp A‖ := T.le_opNorm _
      _ ≤ ‖T‖ * Real.exp (opNorm A) :=
        mul_le_mul_of_nonneg_left (mm_exp_norm_bound A hA) (norm_nonneg T)
      _ ≤ ‖T‖ * Real.exp r := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hAr) (norm_nonneg T)
  have hleft_int (n : ℕ) :
      Integrable (fun ω => Matrix.trace (NormedSpace.exp (Hs n ω + Z ω))) P :=
    @mm_trace_exp_add_integrable Ω mΩ P _ d (Hs n) Z (hHs_meas n) hZm
      (hHs_sa n) hZsa a z (hHs_bd n) hZbd
  have hright_int (n : ℕ) :
      Integrable (fun ω => Matrix.trace (NormedSpace.exp (Hs n ω))) P := by
    let Z0 : Ω → Mat := fun _ => 0
    simpa [Z0] using @mm_trace_exp_add_integrable Ω mΩ P _ d (Hs n) Z0
      (hHs_meas n) measurable_const (hHs_sa n)
      (fun _ => (IsSelfAdjoint.zero Mat).isHermitian) a 0
      (hHs_bd n) (fun _ => by rw [opNorm_eq_norm, norm_zero])
  have hleft_tendsto : Filter.Tendsto
      (fun n => ∫ ω, Matrix.trace (NormedSpace.exp (Hs n ω + Z ω)) ∂P)
      Filter.atTop
      (𝓝 (∫ ω, Matrix.trace (NormedSpace.exp (H ω + Z ω)) ∂P)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun _ => ‖T‖ * Real.exp (a + z))
    · exact Eventually.of_forall fun n => (hleft_int n).aestronglyMeasurable
    · exact Eventually.of_forall fun n => ae_of_all P fun ω =>
        htrace_norm_bound (Hs n ω + Z ω) ((hHs_sa n ω).add (hZsa ω)) (a + z)
          (by
            rw [opNorm_eq_norm]
            exact (norm_add_le _ _).trans (add_le_add
              ((opNorm_eq_norm (Hs n ω)) ▸ hHs_bd n ω)
              ((opNorm_eq_norm (Z ω)) ▸ hZbd ω)))
    · exact integrable_const _
    · exact ae_of_all P fun ω => by
        have hc : Continuous (fun A : Mat =>
            Matrix.trace (NormedSpace.exp (A + Z ω))) := by fun_prop
        exact (hc.tendsto (H ω)).comp (hHs_tendsto ω)
  have hright_tendsto : Filter.Tendsto
      (fun n => ∫ ω, Matrix.trace (NormedSpace.exp (Hs n ω)) ∂P)
      Filter.atTop
      (𝓝 (∫ ω, Matrix.trace (NormedSpace.exp (H ω)) ∂P)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun _ => ‖T‖ * Real.exp a)
    · exact Eventually.of_forall fun n => (hright_int n).aestronglyMeasurable
    · exact Eventually.of_forall fun n => ae_of_all P fun ω =>
        htrace_norm_bound (Hs n ω) (hHs_sa n ω) a (hHs_bd n ω)
    · exact integrable_const _
    · exact ae_of_all P fun ω => by
        have hc : Continuous (fun A : Mat => Matrix.trace (NormedSpace.exp A)) := by fun_prop
        exact (hc.tendsto (H ω)).comp (hHs_tendsto ω)
  exact le_of_tendsto_of_tendsto hleft_tendsto (hright_tendsto.const_mul k)
    (Eventually.of_forall hsimple)

theorem matrixMartingale_trace_mgf {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ) (ℱ : ℕ → MeasurableSpace Ω) (hmono : Monotone ℱ) (hle : ∀ b, ℱ b ≤ mΩ)
    (Z : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (hsa : ∀ b ω, (Z b ω).IsHermitian)
    (hmeas : ∀ b i j, Measurable[ℱ (b + 1)] (fun ω => Z b ω i j))
    (hmean : ∀ b i j, MeasureTheory.condExp (ℱ b) P (fun ω => Z b ω i j) =ᵐ[P] 0)
    {c : ℝ} (hc : 0 < c) (hbd : ∀ b ω, opNorm (Z b ω) ≤ c) (j : ℕ) (u : ℝ) :
    (∫ ω, Matrix.trace (NormedSpace.exp (u • ∑ b ∈ Finset.range j, Z b ω)) ∂P) ≤
      (d : ℝ) * Real.exp ((j : ℝ) * u ^ 2 * c ^ 2 / 2) := by
  let : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℝ) :=
    .restrictScalars ℚ ℝ (Matrix (Fin d) (Fin d) ℝ)
  have hSm (j : ℕ) := mm_partial_sum_measurable d ℱ hmono Z hmeas j
  have hSmeas (j : ℕ) := (hSm j).mono (hle j) le_rfl
  induction j with
  | zero => simp [NormedSpace.exp_zero, Matrix.trace_one]
  | succ j ih =>
    have hZm : Measurable (fun ω => u • Z j ω) :=
      (Measurable.of_eval fun i => Measurable.of_eval fun k =>
        (hmeas j i k).mono (hle (j + 1)) le_rfl).const_smul u
    have hstep := mm_lieb_adapted_step P (ℱ j) (hle j)
      (fun ω => u • ∑ b ∈ Finset.range j, Z b ω) (fun ω => u • Z j ω)
      ((hSm j).const_smul u)
      (fun ω => (mm_partial_sum_isHermitian d Z hsa j ω).smul (IsSelfAdjoint.all u))
      hZm (fun ω => (hsa j ω).smul (IsSelfAdjoint.all u))
      (|u| * ((j : ℝ) * c)) (|u| * c)
      (fun ω => by
        rw [opNorm_eq_norm, norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (mm_partial_sum_norm_le Z c hbd j ω) (abs_nonneg u))
      (fun ω => by
        rw [opNorm_eq_norm, norm_smul, Real.norm_eq_abs, ← opNorm_eq_norm]
        exact mul_le_mul_of_nonneg_left (hbd j ω) (abs_nonneg u))
      (by
        simpa only [mul_pow, sq_abs] using
          mm_block_mgf P d ℱ hle Z hsa hmeas hmean hc hbd j u)
    calc
      _ = ∫ ω, Matrix.trace
          (NormedSpace.exp
            (u • ∑ b ∈ Finset.range j, Z b ω + u • Z j ω)) ∂P := by
        congr 1
        funext ω
        rw [Finset.sum_range_succ, smul_add]
      _ ≤ Real.exp ((|u| * c) ^ 2 / 2) *
          ∫ ω, Matrix.trace
            (NormedSpace.exp (u • ∑ b ∈ Finset.range j, Z b ω)) ∂P := hstep
      _ ≤ Real.exp ((|u| * c) ^ 2 / 2) *
          ((d : ℝ) * Real.exp ((j : ℝ) * u ^ 2 * c ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left ih (Real.exp_nonneg _)
      _ = _ := by
        rw [mul_left_comm, ← Real.exp_add, Nat.cast_add, Nat.cast_one]
        congr 2
        rw [mul_pow, sq_abs]
        ring

end MatrixConcentration
