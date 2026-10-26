import GaussianFoundations.IBP
import GaussianFoundations.Poincare

/-!
# I.i.d. Gaussian matrices: measurability, entry moments, Poincaré

Facts about a random matrix `Y : Ω → Matrix (Fin p) (Fin q) ℝ` with `IsIIDGaussianMatrix μ Y` (entries i.i.d.
`N(0,1)`), requested downstream by `rmt-foundations` (Wishart moments, variance of linear spectral statistics).

* `IsIIDGaussianMatrix.aemeasurable`: `Y` is a.e.-measurable (the pushforward is a probability measure, hence
  nonzero; the argument is the private `aemeasurable_of_map_eq_pi_gaussian` of `IBP.lean`).
* `isserlis_wick` (ported from Muon's proved `Muon.Foundations.isserlis_wick`, general `k`, any finite index type) and
  its matrix form `IsIIDGaussianMatrix.isserlis_wick`.
* `IsIIDGaussianMatrix.integral_entry_sq`, `…_entry_four`, `…_isserlis`: second and fourth entry moments, and
  Isserlis' formula for four entries, `E[Y_a Y_b Y_c Y_d] = δ_ab δ_cd + δ_ac δ_bd + δ_ad δ_bc`.
* `gaussianPoincare_matrix`: `Var F(Y) ≤ E ∑_{ij} (∂F/∂Y_ij)²` (`matPartial`), transported from
  `gaussianPoincare` along `Fin p × Fin q ≃ Fin (p*q)` and `EuclideanSpace`; real-variance form with an
  integrable energy, and `evariance` form.
-/

namespace GaussianFoundations

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {p q : ℕ}
  {Y : Ω → Matrix (Fin p) (Fin q) ℝ}

private lemma aemeasurable_of_map_eq_pi_gaussian_matrix {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] {P : Measure Ω} {ξ : Ω → ι → ℝ}
    (hξ : P.map ξ = Measure.pi (fun _ : ι => gaussianReal 0 1)) :
    AEMeasurable ξ P := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      exact aemeasurable_of_subsingleton_codomain
  | inr hι =>
      let _ := hι
      let i : ι := Classical.choice hι
      have hP : P ≠ 0 := by
        intro hP
        subst P
        rw [Measure.map_zero] at hξ
        exact IsProbabilityMeasure.ne_zero
          (Measure.pi (fun _ : ι => gaussianReal 0 1)) hξ.symm
      by_contra hmeas
      rw [Measure.map_of_not_aemeasurable_of_ne_zero hmeas hP] at hξ
      have heval := congrArg (fun Q : Measure (ι → ℝ) => Q.map (fun x => x i)) hξ
      rw [(measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).map_eq] at heval
      simp only [Measure.map_dirac] at heval
      let a : ℝ := (Classical.ofNonempty : ι → ℝ) i
      have ha := congrArg (fun Q : Measure ℝ => Q {a}) heval
      let : NullSingletonClass (gaussianReal 0 1) :=
        nullSingletonClass_gaussianReal one_ne_zero
      simp [a] at ha

/-- An i.i.d. Gaussian matrix is a.e.-measurable. Route: `μ.map Y'` (vectorised) is a probability measure, so it
is nonzero, and `Measure.map` of a non-a.e.-measurable map is `0`; transport back along the measurable
equivalence `vecOfMat`/`matOfVec` (copy the private `aemeasurable_of_map_eq_pi_gaussian'` of `IBP.lean`). -/
theorem IsIIDGaussianMatrix.aemeasurable (hY : IsIIDGaussianMatrix μ Y) : AEMeasurable Y μ := by
  have hvec : AEMeasurable (fun ω => vecOfMat (Y ω)) μ :=
    aemeasurable_of_map_eq_pi_gaussian_matrix hY
  have hmat : Continuous (matOfVec : (Fin p × Fin q → ℝ) → Matrix (Fin p) (Fin q) ℝ) :=
    continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)
  have hcomp := hmat.measurable.comp_aemeasurable hvec
  convert hcomp using 1
  ext ω i j
  rfl

private lemma pi_gaussian_coord_pow {ι : Type*} [Fintype ι] (i : ι) (k : ℕ) :
    ∫ z, z i ^ k ∂(Measure.pi fun _ : ι => gaussianReal 0 1) =
      ∫ x, x ^ k ∂(gaussianReal 0 1) := by
  have hf : Measurable (fun x : ℝ => x ^ k) := measurable_id.pow_const k
  have hmap := (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).map_eq
  have h := integral_map (μ := Measure.pi fun _ : ι => gaussianReal 0 1)
    (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable
  rw [hmap] at h
  exact h.symm

private lemma gaussian_pow_integrable_matrix (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 1) := by
  have h := (memLp_id_gaussianReal' (μ := 0) (v := 1) (n : ℝ≥0∞)
    (ENNReal.natCast_ne_top n)).integrable_norm_pow'
  refine h.mono' (measurable_id.pow_const n).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  simp [norm_pow]

private lemma gaussian_half_line_matrix (k : ℕ) :
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
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx'.le]
      congr 1
      push_cast
      ring
    have e2 : x ^ ((2 : ℝ) - 1) * x ^ ((k : ℝ) * 2 - 1) = x ^ (2 * k) := by
      rw [← Real.rpow_add hx']
      rw [show ((2 : ℝ) - 1) + ((k : ℝ) * 2 - 1) = ((2 * k : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    rw [smul_eq_mul, Real.rpow_two x, e1]
    rw [← e2]
    ring
  have hG : ∫ y in Set.Ioi (0 : ℝ), (1 / 2 : ℝ) * y ^ ((k : ℝ) + 1 / 2 - 1)
        * Real.exp (-((1 / 2 : ℝ) * y))
      = (1 / 2 : ℝ) * ∫ y in Set.Ioi (0 : ℝ), y ^ ((k : ℝ) + 1 / 2 - 1)
        * Real.exp (-((1 / 2 : ℝ) * y)) := by
    rw [← integral_const_mul]
    congr 1
    ext y
    ring
  rw [hL, hsub, hG]
  have ha : 0 < (k : ℝ) + 1 / 2 :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) (by norm_num)
  have hr : (0 : ℝ) < 1 / 2 := by norm_num
  exact congrArg (fun x : ℝ => (1 / 2 : ℝ) * x)
    (Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1 / 2) (r := 1 / 2) ha hr)

private lemma gaussian_moment_even_matrix (k : ℕ) :
    ∫ x, x ^ (2 * k) ∂(gaussianReal 0 1) = (((2 * k - 1).doubleFactorial : ℕ) : ℝ) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have hpt : (fun x : ℝ => gaussianPDFReal 0 1 x • x ^ (2 * k))
      = fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹
          * (fun y : ℝ => y ^ (2 * k) * Real.exp (-((1 / 2 : ℝ) * y ^ 2))) |x| := by
    funext x
    rw [gaussianPDFReal_def, smul_eq_mul, ← Even.pow_abs (even_two_mul k) x]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    rw [sq_abs]
    ring
  rw [hpt, integral_const_mul, integral_comp_abs
    (f := fun y : ℝ => y ^ (2 * k) * Real.exp (-((1 / 2 : ℝ) * y ^ 2))),
    gaussian_half_line_matrix k, Real.Gamma_nat_add_half k]
  have h2 : (1 / (1 / 2 : ℝ)) ^ ((k : ℝ) + 1 / 2) = 2 ^ k * Real.sqrt 2 := by
    rw [show (1 / (1 / 2 : ℝ)) = (2 : ℝ) by norm_num, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_natCast, Real.sqrt_eq_rpow]
  rw [h2, Real.sqrt_mul (by norm_num) Real.pi]
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have h2k : (2 : ℝ) ^ k ≠ 0 := by positivity
  have hs2ne : Real.sqrt 2 ≠ 0 := by positivity
  let D : ℝ := ((2 * k - 1).doubleFactorial : ℕ)
  change (Real.sqrt 2 * Real.sqrt Real.pi)⁻¹ *
    (2 * (1 / 2 * ((2 : ℝ) ^ k * Real.sqrt 2 *
      (D * Real.sqrt Real.pi / (2 : ℝ) ^ k)))) = D
  have hcancel : (2 : ℝ) ^ k * Real.sqrt 2 *
      (D * Real.sqrt Real.pi / (2 : ℝ) ^ k) =
        Real.sqrt 2 * (D * Real.sqrt Real.pi) := by
    calc
      (2 : ℝ) ^ k * Real.sqrt 2 * (D * Real.sqrt Real.pi / (2 : ℝ) ^ k) =
          (2 : ℝ) ^ k * (Real.sqrt 2 * (D * Real.sqrt Real.pi)) / (2 : ℝ) ^ k := by ring
      _ = Real.sqrt 2 * (D * Real.sqrt Real.pi) := mul_div_cancel_left₀ _ h2k
  rw [hcancel]
  calc
    (Real.sqrt 2 * Real.sqrt Real.pi)⁻¹ *
        (2 * (1 / 2 * (Real.sqrt 2 * (D * Real.sqrt Real.pi)))) =
      (Real.sqrt 2 * Real.sqrt Real.pi)⁻¹ *
        ((Real.sqrt 2 * Real.sqrt Real.pi) * D) := by ring
    _ = D := by
      rw [← mul_assoc, inv_mul_cancel₀ (mul_ne_zero hs2ne hpi), one_mul]

private lemma gaussian_moment_odd_matrix (k : ℕ) :
    ∫ x, x ^ (2 * k + 1) ∂(gaussianReal 0 1) = 0 := by
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg]
    simp
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

/-- `E Y_ij² = 1`. Route: `integral_map` to the product Gaussian, the coordinate marginal is `gaussianReal 0 1`
(`Measure.pi` marginal), second moment `= variance = 1`. -/
theorem IsIIDGaussianMatrix.integral_entry_sq (hY : IsIIDGaussianMatrix μ Y) (i : Fin p) (j : Fin q) :
    ∫ ω, Y ω i j ^ 2 ∂μ = 1 := by
  let Z : Ω → Fin p × Fin q → ℝ := fun ω => vecOfMat (Y ω)
  have hZ : μ.map Z = Measure.pi (fun _ : Fin p × Fin q => gaussianReal 0 1) := hY
  have hm : AEMeasurable Z μ := aemeasurable_of_map_eq_pi_gaussian_matrix hZ
  calc
    ∫ ω, Y ω i j ^ 2 ∂μ = ∫ z, z (i, j) ^ 2 ∂(μ.map Z) := by
      rw [integral_map hm ((measurable_pi_apply (i, j)).pow_const 2).aestronglyMeasurable]
      rfl
    _ = ∫ z, z (i, j) ^ 2 ∂(Measure.pi fun _ : Fin p × Fin q => gaussianReal 0 1) := by
      rw [hZ]
    _ = 1 := by
      rw [pi_gaussian_coord_pow]
      simpa using gaussian_moment_even_matrix 1

/-- `E Y_ij⁴ = 3`. Route: as `integral_entry_sq`, with the Gaussian fourth moment (Mathlib's central moments of
`gaussianReal`, or the Muon `gaussian_moment_four` proof). -/
theorem IsIIDGaussianMatrix.integral_entry_four (hY : IsIIDGaussianMatrix μ Y) (i : Fin p) (j : Fin q) :
    ∫ ω, Y ω i j ^ 4 ∂μ = 3 := by
  let Z : Ω → Fin p × Fin q → ℝ := fun ω => vecOfMat (Y ω)
  have hZ : μ.map Z = Measure.pi (fun _ : Fin p × Fin q => gaussianReal 0 1) := hY
  have hm : AEMeasurable Z μ := aemeasurable_of_map_eq_pi_gaussian_matrix hZ
  calc
    ∫ ω, Y ω i j ^ 4 ∂μ = ∫ z, z (i, j) ^ 4 ∂(μ.map Z) := by
      rw [integral_map hm ((measurable_pi_apply (i, j)).pow_const 4).aestronglyMeasurable]
      rfl
    _ = ∫ z, z (i, j) ^ 4 ∂(Measure.pi fun _ : Fin p × Fin q => gaussianReal 0 1) := by
      rw [hZ]
    _ = 3 := by
      rw [pi_gaussian_coord_pow]
      simpa using gaussian_moment_even_matrix 2

/-- Fixed-point-free involutions of `Fin k` encode the perfect matchings of `[k]` (as in Muon's
`Muon.Foundations.IsPerfectMatchingInv`). -/
def IsPerfectMatchingInv {k : ℕ} (σ : Equiv.Perm (Fin k)) : Prop :=
  (∀ r, σ (σ r) = r) ∧ ∀ r, σ r ≠ r

private lemma fpf_cycleType_matrix {β : Type*} [Fintype β] [DecidableEq β]
    (σ : Equiv.Perm β)
    (h : (∀ q₀, σ (σ q₀) = q₀) ∧ ∀ q₀, σ q₀ ≠ q₀) :
    σ.cycleType = Multiset.replicate (Fintype.card β / 2) 2 ∧ Even (Fintype.card β) := by
  have hsq : σ ^ 2 = 1 := by
    ext i
    simp [pow_two, h.1 i]
  have hord : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have hall : ∀ n ∈ σ.cycleType, n = 2 := by
    intro n hn
    have h1 : n ∣ 2 := (Equiv.Perm.dvd_of_mem_cycleType hn).trans hord
    have h2 := Equiv.Perm.two_le_of_mem_cycleType hn
    exact le_antisymm (Nat.le_of_dvd (by norm_num) h1) h2
  have hsupp : σ.support = Finset.univ := by
    ext x
    simp [Equiv.Perm.mem_support, h.2 x]
  have hsum : σ.cycleType.sum = Fintype.card β := by
    rw [Equiv.Perm.sum_cycleType, hsupp, Finset.card_univ]
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
    Multiset.eq_replicate.2 ⟨rfl, hall⟩
  have hs2 : σ.cycleType.sum = 2 * Multiset.card σ.cycleType := by
    conv_lhs => rw [hrep]
    simp [mul_comm]
  have hev : Fintype.card β = 2 * Multiset.card σ.cycleType := by rw [← hsum, hs2]
  refine ⟨?_, ⟨Multiset.card σ.cycleType, by omega⟩⟩
  rw [hrep]
  congr 1
  omega

private lemma cycleType_fpf_matrix {β : Type*} [Fintype β] [DecidableEq β]
    (σ : Equiv.Perm β) (j : ℕ) (h : σ.cycleType = Multiset.replicate j 2)
    (hj : 2 * j = Fintype.card β) :
    (∀ q₀, σ (σ q₀) = q₀) ∧ ∀ q₀, σ q₀ ≠ q₀ := by
  have hsum : σ.cycleType.sum = Fintype.card β := by
    rw [h]
    simp [Multiset.sum_replicate]
    omega
  have hsupp : σ.support = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← Equiv.Perm.sum_cycleType, hsum]
  have hord : orderOf σ ∣ 2 := by
    rw [← Equiv.Perm.lcm_cycleType, h]
    apply Multiset.lcm_dvd.2
    intro a ha
    rw [Multiset.eq_of_mem_replicate ha]
  have hsq : σ ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 hord
  refine ⟨fun i => ?_, fun i hi => ?_⟩
  · have := congrArg (fun τ : Equiv.Perm β => τ i) hsq
    simpa [pow_two] using this
  · have : i ∈ σ.support := by rw [hsupp]; exact Finset.mem_univ _
    exact (Equiv.Perm.mem_support.1 this) hi

private lemma fpf_card_matrix {β : Type*} [Fintype β] [DecidableEq β] :
    Nat.card {σ : Equiv.Perm β // (∀ q₀, σ (σ q₀) = q₀) ∧ ∀ q₀, σ q₀ ≠ q₀}
      = if Even (Fintype.card β) then (Fintype.card β - 1).doubleFactorial else 0 := by
  classical
  split_ifs with hev
  · obtain ⟨j, hj⟩ := hev
    have hj' : Fintype.card β = 2 * j := by omega
    have hset : Nat.card {σ : Equiv.Perm β // (∀ q₀, σ (σ q₀) = q₀) ∧ ∀ q₀, σ q₀ ≠ q₀}
        = Finset.card ({g | g.cycleType = Multiset.replicate j 2} : Finset (Equiv.Perm β)) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        have hc := (fpf_cycleType_matrix σ h).1
        rw [hc]
        congr 2
        omega
      · intro h
        exact cycleType_fpf_matrix σ j h hj'.symm
    rw [hset, Equiv.Perm.card_of_cycleType]
    have hc : 2 * j ≤ Fintype.card β ∧ ∀ a ∈ Multiset.replicate j 2, 2 ≤ a := by
      refine ⟨by omega, fun a ha => ?_⟩
      rw [Multiset.eq_of_mem_replicate ha]
    rw [ite_eq_left (by simpa [Multiset.sum_replicate, mul_comm] using hc)]
    have hden : Nat.factorial (Fintype.card β - (Multiset.replicate j 2).sum) *
        (Multiset.replicate j 2).prod *
          (∏ n ∈ (Multiset.replicate j 2).toFinset,
            Nat.factorial ((Multiset.replicate j 2).count n))
        = 2 ^ j * Nat.factorial j := by
      have e1 : Fintype.card β - (Multiset.replicate j 2).sum = 0 := by
        simp [Multiset.sum_replicate]
        omega
      rw [e1]
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · subst h0
        simp
      · have : (Multiset.replicate j 2).toFinset = {2} := by
          rw [Multiset.toFinset_replicate]
          simp [h0.ne']
        rw [this]
        simp
    rw [hden, hj']
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0
      simp
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have e2 : 2 * (i + 1) = (2 * i + 1) + 1 := by ring
      have e3 : 2 * (i + 1) - 1 = 2 * i + 1 := by omega
      rw [e3, e2, Nat.factorial_eq_mul_doubleFactorial, ← e2, Nat.doubleFactorial_two_mul]
      ring
  · rw [Nat.card_eq_zero]
    left
    exact ⟨fun ⟨σ, hσ⟩ => hev (fpf_cycleType_matrix σ hσ).2⟩

private lemma stab_equiv_matrix {α ι : Type*} [DecidableEq ι] (c : α → ι) :
    ∃ e : {g : Equiv.Perm α // c ∘ g = c} ≃ ∀ i, Equiv.Perm {a // c a = i},
      ∀ g i a (h : c a = i), e g i ⟨a, h⟩ = g.1 a := by
  classical
  refine ⟨{ toFun := fun g i => Equiv.Perm.subtypePerm g.1 (fun a => by
                have h := congrFun g.2 a
                simp only [Function.comp_apply] at h
                rw [h])
            invFun := fun h => ⟨DomMulAct.stabilizerEquiv_invFun_aux h, by
                funext a
                exact DomMulAct.comp_stabilizerEquiv_invFun h a⟩
            left_inv := ?_
            right_inv := ?_ }, ?_⟩
  · intro g
    apply Subtype.ext
    ext a
    rfl
  · intro h
    ext i ⟨a, ha⟩
    exact DomMulAct.stabilizerEquiv_invFun_eq h ha
  · intro g i a h
    rfl

private lemma fpf_count_matrix {α ι : Type*} [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι] (c : α → ι) :
    Nat.card {σ : Equiv.Perm α // ((∀ q₀, σ (σ q₀) = q₀) ∧ ∀ q₀, σ q₀ ≠ q₀) ∧
        ∀ i, c (σ i) = c i}
      = ∏ i, Nat.card {σ : Equiv.Perm {a // c a = i} //
          (∀ q₀, σ (σ q₀) = q₀) ∧ ∀ q₀, σ q₀ ≠ q₀} := by
  obtain ⟨e, he⟩ := stab_equiv_matrix c
  have h1 : Nat.card {σ : Equiv.Perm α // ((∀ q₀, σ (σ q₀) = q₀) ∧
        ∀ q₀, σ q₀ ≠ q₀) ∧ ∀ i, c (σ i) = c i}
      = Nat.card {g : {g : Equiv.Perm α // c ∘ g = c} //
          (∀ q₀, g.1 (g.1 q₀) = q₀) ∧ ∀ q₀, g.1 q₀ ≠ q₀} := by
    refine Nat.card_congr ?_
    exact
      { toFun := fun σ => ⟨⟨σ.1, funext σ.2.2⟩, σ.2.1⟩
        invFun := fun g => ⟨g.1.1, g.2, fun i => congrFun g.1.2 i⟩
        left_inv := fun σ => rfl
        right_inv := fun g => rfl }
  have h2 : Nat.card {g : {g : Equiv.Perm α // c ∘ g = c} //
        (∀ q₀, g.1 (g.1 q₀) = q₀) ∧ ∀ q₀, g.1 q₀ ≠ q₀}
      = Nat.card {f : ∀ i, Equiv.Perm {a // c a = i} //
          ∀ i, (∀ q₀, (f i) ((f i) q₀) = q₀) ∧ ∀ q₀, (f i) q₀ ≠ q₀} := by
    refine Nat.card_congr (Equiv.subtypeEquiv e ?_)
    intro g
    have he' : ∀ i (x : {a // c a = i}), ((e g i) x).1 = g.1 x.1 :=
      fun i x => he g i x.1 x.2
    constructor
    · rintro ⟨h1, h2⟩ i
      refine ⟨fun x => ?_, fun x => ?_⟩
      · apply Subtype.ext
        rw [he', he']
        exact h1 _
      · intro hx
        apply h2 x.1
        have hx' := congrArg Subtype.val hx
        rw [he'] at hx'
        exact hx'
    · intro h
      refine ⟨fun a => ?_, fun a ha => ?_⟩
      · have hh := (h (c a)).1 ⟨a, rfl⟩
        have hh' := congrArg Subtype.val hh
        rw [he', he'] at hh'
        exact hh'
      · refine (h (c a)).2 ⟨a, rfl⟩ (Subtype.ext ?_)
        rw [he']
        exact ha
  rw [h1, h2, Nat.card_congr (Equiv.subtypePiEquivPi
    (β := fun i => Equiv.Perm {a // c a = i})
    (p := fun i σ => (∀ q₀, σ (σ q₀) = q₀) ∧ ∀ q₀, σ q₀ ≠ q₀)), Nat.card_pi]

private lemma gauss_moment_ite_matrix (m : ℕ) :
    ∫ x, x ^ m ∂(gaussianReal 0 1)
      = (((if Even m then (m - 1).doubleFactorial else 0 : ℕ)) : ℝ) := by
  rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
  · rw [gaussian_moment_even_matrix]
    simp
  · rw [gaussian_moment_odd_matrix]
    have h : ¬ Even (2 * j + 1) := by simp
    simp [h]

private lemma isserlis_wick_aux_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (c : Fin k → ι) :
    ∫ z, (∏ r : Fin k, z (c r)) ∂(Measure.pi fun _ : ι => gaussianReal 0 1) =
      (Nat.card {σ : Equiv.Perm (Fin k) // IsPerfectMatchingInv σ ∧
        ∀ i, c (σ i) = c i} : ℝ) := by
  have hprod : ∀ z : ι → ℝ, ∏ r : Fin k, z (c r)
      = ∏ i : ι, z i ^ Fintype.card {r // c r = i} := by
    intro z
    rw [← Fintype.prod_fiberwise c (fun r => z (c r))]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_congr rfl (fun (r : {r // c r = i}) _ => by rw [r.2]),
      Finset.prod_const, Finset.card_univ]
  simp_rw [hprod]
  rw [integral_fintype_prod_eq_prod
    (fun (i : ι) (x : ℝ) => x ^ Fintype.card {r // c r = i})]
  have key : Nat.card {σ : Equiv.Perm (Fin k) // IsPerfectMatchingInv σ ∧
      ∀ i, c (σ i) = c i}
      = ∏ i, Nat.card {σ : Equiv.Perm {a // c a = i} //
        (∀ q₀, σ (σ q₀) = q₀) ∧ ∀ q₀, σ q₀ ≠ q₀} := fpf_count_matrix c
  rw [key]
  push_cast
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gauss_moment_ite_matrix, fpf_card_matrix]

/-- Isserlis / Wick formula, coordinate form, for the product Gaussian `Measure.pi (fun _ : ι => gaussianReal 0 1)`
on a finite index type `ι`: `E ∏_{r<k} g_{c r} = #{perfect matchings π of [k] with c constant on each pair of π}`.
Route: PORT the proved `Muon.Foundations.isserlis_wick` (`muon/lean/Muon/Foundations/GaussianCombinatorics.lean:234`,
`isserlis_wick_aux` and its helpers `fpf_count`, `fpf_card`, `gauss_moment_ite`, …; read only, copy privately), which is
stated for `stdGaussianPi d = Measure.pi (fun _ : Fin d => gaussianReal 0 1)`. Generalise `Fin d` to `ι` by the
same argument, or transport along `Fintype.equivFin ι`. -/
theorem isserlis_wick {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (c : Fin k → ι) :
    ∫ z, (∏ r : Fin k, z (c r)) ∂(Measure.pi fun _ : ι => gaussianReal 0 1) =
      (Nat.card {σ : Equiv.Perm (Fin k) // IsPerfectMatchingInv σ ∧ ∀ r, c (σ r) = c r} : ℝ) := by
  exact isserlis_wick_aux_matrix k c

/-- Isserlis–Wick for the entries of an i.i.d. Gaussian matrix: `E ∏_{r<k} Y_{c r} = #{compatible perfect
matchings}`. Route: `integral_map` (`IsIIDGaussianMatrix.aemeasurable`) and `isserlis_wick` on `ι = Fin p × Fin q`. -/
theorem IsIIDGaussianMatrix.isserlis_wick (hY : IsIIDGaussianMatrix μ Y) (k : ℕ) (c : Fin k → Fin p × Fin q) :
    ∫ ω, (∏ r : Fin k, Y ω (c r).1 (c r).2) ∂μ =
      (Nat.card {σ : Equiv.Perm (Fin k) // IsPerfectMatchingInv σ ∧ ∀ r, c (σ r) = c r} : ℝ) := by
  let Z : Ω → Fin p × Fin q → ℝ := fun ω => vecOfMat (Y ω)
  have hZ : μ.map Z = Measure.pi (fun _ : Fin p × Fin q => gaussianReal 0 1) := hY
  have hm : AEMeasurable Z μ := aemeasurable_of_map_eq_pi_gaussian_matrix hZ
  have hp : AEStronglyMeasurable (fun z : Fin p × Fin q → ℝ => ∏ r : Fin k, z (c r))
      (μ.map Z) := (by fun_prop : Measurable fun z : Fin p × Fin q → ℝ =>
        ∏ r : Fin k, z (c r)).aestronglyMeasurable
  calc
    ∫ ω, (∏ r : Fin k, Y ω (c r).1 (c r).2) ∂μ =
        ∫ z, (∏ r : Fin k, z (c r)) ∂(μ.map Z) := by
      rw [integral_map hm hp]
      rfl
    _ = ∫ z, (∏ r : Fin k, z (c r))
        ∂(Measure.pi fun _ : Fin p × Fin q => gaussianReal 0 1) := by rw [hZ]
    _ = _ := GaussianFoundations.isserlis_wick k c

private lemma perm4_fpf_matrix (σ : Equiv.Perm (Fin 4)) :
    IsPerfectMatchingInv σ ↔
      (σ = Equiv.swap 0 1 * Equiv.swap 2 3 ∨
       σ = Equiv.swap 0 2 * Equiv.swap 1 3 ∨
       σ = Equiv.swap 0 3 * Equiv.swap 1 2) := by
  have h : ∀ σ : Equiv.Perm (Fin 4), IsPerfectMatchingInv σ ↔
      (σ = Equiv.swap 0 1 * Equiv.swap 2 3 ∨
       σ = Equiv.swap 0 2 * Equiv.swap 1 3 ∨
       σ = Equiv.swap 0 3 * Equiv.swap 1 2) := by
    unfold IsPerfectMatchingInv
    decide
  exact h σ

private lemma forall_fin4_matrix {P : Fin 4 → Prop} :
    (∀ i, P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩
  · rintro ⟨h0, h1, h2, h3⟩ i
    fin_cases i <;> assumption

private lemma card4_match_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : Fin 4 → ι) :
    Nat.card {σ : Equiv.Perm (Fin 4) // IsPerfectMatchingInv σ ∧
        ∀ i, c (σ i) = c i}
      = (if c 0 = c 1 ∧ c 2 = c 3 then 1 else 0) +
        (if c 0 = c 2 ∧ c 1 = c 3 then 1 else 0) +
        (if c 0 = c 3 ∧ c 1 = c 2 then 1 else 0) := by
  classical
  have hS : Finset.univ.filter (fun σ : Equiv.Perm (Fin 4) =>
      IsPerfectMatchingInv σ ∧ ∀ i, c (σ i) = c i)
      = ({Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
          Equiv.swap 0 3 * Equiv.swap 1 2} : Finset (Equiv.Perm (Fin 4))).filter
          (fun σ => ∀ i, c (σ i) = c i) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, perm4_fpf_matrix,
      Finset.mem_insert, Finset.mem_singleton]
  have hQ1 : (∀ i, c ((Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) i) = c i) ↔
      c 0 = c 1 ∧ c 2 = c 3 := by
    rw [forall_fin4_matrix]
    have v0 : (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) 0 = 1 := by decide
    have v1 : (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) 1 = 0 := by decide
    have v2 : (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) 2 = 3 := by decide
    have v3 : (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) 3 = 2 := by decide
    rw [v0, v1, v2, v3]
    constructor
    · rintro ⟨h0, -, h2, -⟩
      exact ⟨h0.symm, h2.symm⟩
    · rintro ⟨h0, h2⟩
      exact ⟨h0.symm, h0, h2.symm, h2⟩
  have hQ2 : (∀ i, c ((Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) i) = c i) ↔
      c 0 = c 2 ∧ c 1 = c 3 := by
    rw [forall_fin4_matrix]
    have v0 : (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) 0 = 2 := by decide
    have v1 : (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) 1 = 3 := by decide
    have v2 : (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) 2 = 0 := by decide
    have v3 : (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) 3 = 1 := by decide
    rw [v0, v1, v2, v3]
    constructor
    · rintro ⟨h0, h1, -, -⟩
      exact ⟨h0.symm, h1.symm⟩
    · rintro ⟨h0, h1⟩
      exact ⟨h0.symm, h1.symm, h0, h1⟩
  have hQ3 : (∀ i, c ((Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) i) = c i) ↔
      c 0 = c 3 ∧ c 1 = c 2 := by
    rw [forall_fin4_matrix]
    have v0 : (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) 0 = 3 := by decide
    have v1 : (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) 1 = 2 := by decide
    have v2 : (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) 2 = 1 := by decide
    have v3 : (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) 3 = 0 := by decide
    rw [v0, v1, v2, v3]
    constructor
    · rintro ⟨h0, h1, -, -⟩
      exact ⟨h0.symm, h1.symm⟩
    · rintro ⟨h0, h1⟩
      exact ⟨h0.symm, h1.symm, h1, h0⟩
  have d12 : (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) ∉
      ({Equiv.swap 0 2 * Equiv.swap 1 3,
        Equiv.swap 0 3 * Equiv.swap 1 2} : Finset (Equiv.Perm (Fin 4))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    decide
  have d23 : (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) ≠
      Equiv.swap 0 3 * Equiv.swap 1 2 := by decide
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hS, Finset.card_filter,
    Finset.sum_insert d12, Finset.sum_pair d23]
  simp only [hQ1, hQ2, hQ3]
  ring

/-- Isserlis (Wick) for four entries `a b c d : Fin p × Fin q`:
`E[Y_a Y_b Y_c Y_d] = δ_ab δ_cd + δ_ac δ_bd + δ_ad δ_bc`. Route: push forward to `Measure.pi`; split by the
the `k = 4` case of `IsIIDGaussianMatrix.isserlis_wick` (count the three perfect matchings of `Fin 4`), or directly
by coincidence patterns. -/
theorem IsIIDGaussianMatrix.isserlis (hY : IsIIDGaussianMatrix μ Y) (a b c d : Fin p × Fin q) :
    ∫ ω, Y ω a.1 a.2 * Y ω b.1 b.2 * Y ω c.1 c.2 * Y ω d.1 d.2 ∂μ =
      (if a = b ∧ c = d then 1 else 0) + (if a = c ∧ b = d then 1 else 0) +
        (if a = d ∧ b = c then 1 else 0) := by
  classical
  let e : Fin 4 → Fin p × Fin q := ![a, b, c, d]
  have h := hY.isserlis_wick 4 e
  rw [card4_match_matrix e] at h
  push_cast at h
  by_cases h1 : a = b ∧ c = d <;>
    by_cases h2 : a = c ∧ b = d <;>
      by_cases h3 : a = d ∧ b = c <;>
        simp [e, Fin.prod_univ_four, h1, h2, h3] at h ⊢ <;> exact h

/-- Gaussian Poincaré for a function of an i.i.d. Gaussian matrix, `evariance` form:
`Var F(Y) ≤ E ∑_{ij} (∂F/∂Y_ij)²`. Hypotheses on the vectorisation `F ∘ matOfVec` (as in `stein_matrix`).
Route: `μ.map (vecOfMat ∘ Y)` is the product Gaussian on `Fin p × Fin q → ℝ`; transport to
`EuclideanSpace ℝ (Fin (p*q))` via `finProdFinEquiv` and `EuclideanSpace.equiv` (the product Gaussian is
`stdGaussian` there, `map_pi_eq_stdGaussian`), apply `gaussianPoincare`, and identify
`‖fderiv f x‖² = ∑ (partial derivatives)²` (orthonormal basis expansion of the dual norm) with the
`matPartial`s (`matPartial_matOfVec`). -/
theorem gaussianPoincare_matrix (hY : IsIIDGaussianMatrix μ Y) {F : Matrix (Fin p) (Fin q) ℝ → ℝ}
    (hF : ContDiff ℝ 1 (fun x => F (matOfVec x)))
    (henergy : ∫⁻ ω, ENNReal.ofReal (∑ i, ∑ j, matPartial F i j (Y ω) ^ 2) ∂μ < ⊤) :
    evariance (fun ω => F (Y ω)) μ ≤ ∫⁻ ω, ENNReal.ofReal (∑ i, ∑ j, matPartial F i j (Y ω) ^ 2) ∂μ := by
  let Z : Ω → Fin p × Fin q → ℝ := fun ω => vecOfMat (Y ω)
  let ν : Measure (Fin p × Fin q → ℝ) :=
    Measure.pi fun _ : Fin p × Fin q => gaussianReal 0 1
  let ν' : Measure (Fin (p * q) → ℝ) :=
    Measure.pi fun _ : Fin (p * q) => gaussianReal 0 1
  let R : (Fin p × Fin q → ℝ) ≃L[ℝ] (Fin (p * q) → ℝ) :=
    ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (p * q) => ℝ) finProdFinEquiv
  let T : (Fin p × Fin q → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (p * q)) :=
    R.trans (EuclideanSpace.equiv (Fin (p * q)) ℝ).symm
  let g : (Fin p × Fin q → ℝ) → ℝ := fun z => F (matOfVec z)
  let f : EuclideanSpace ℝ (Fin (p * q)) → ℝ := fun x => g (T.symm x)
  have hZ : μ.map Z = ν := hY
  have hmZ : AEMeasurable Z μ := aemeasurable_of_map_eq_pi_gaussian_matrix hY
  have hR : MeasurePreserving R ν ν' := by
    let h := measurePreserving_piCongrLeft
      (fun _ : Fin (p * q) => gaussianReal 0 1) finProdFinEquiv
    refine ⟨R.continuous.measurable, ?_⟩
    have heq : (R : (Fin p × Fin q → ℝ) → (Fin (p * q) → ℝ)) =
        MeasurableEquiv.piCongrLeft (fun _ : Fin (p * q) => ℝ) finProdFinEquiv := by
      funext z k
      rfl
    rw [heq]
    simpa [ν, ν'] using h.map_eq
  have hE : MeasurePreserving (EuclideanSpace.equiv (Fin (p * q)) ℝ).symm ν'
      (stdGaussian (EuclideanSpace ℝ (Fin (p * q)))) := by
    refine ⟨(EuclideanSpace.equiv (Fin (p * q)) ℝ).symm.continuous.measurable, ?_⟩
    change Measure.map (WithLp.toLp 2) ν' =
      stdGaussian (EuclideanSpace ℝ (Fin (p * q)))
    simpa [ν'] using (ProbabilityTheory.map_pi_eq_stdGaussian (ι := Fin (p * q)))
  have hT : MeasurePreserving T ν
      (stdGaussian (EuclideanSpace ℝ (Fin (p * q)))) := by
    convert hE.comp hR using 1
    rfl
  have hf : ContDiff ℝ 1 f := hF.comp T.symm.contDiff
  have hgdiff (z : Fin p × Fin q → ℝ) : DifferentiableAt ℝ g z :=
    hF.differentiable one_ne_zero z
  have hbasis (ij : Fin p × Fin q) :
      T.symm (EuclideanSpace.basisFun (Fin (p * q)) ℝ (finProdFinEquiv ij)) =
        Pi.single ij 1 := by
    ext kl
    classical
    change R.symm (EuclideanSpace.equiv (Fin (p * q)) ℝ
      (EuclideanSpace.basisFun (Fin (p * q)) ℝ (finProdFinEquiv ij))) kl =
        (Pi.single ij (1 : ℝ) : Fin p × Fin q → ℝ) kl
    have hRsymm (w : Fin (p * q) → ℝ) (kl : Fin p × Fin q) :
        R.symm w kl = w (finProdFinEquiv kl) := by rfl
    rw [hRsymm]
    simp [EuclideanSpace.basisFun_apply, Pi.single_apply, eq_comm]
  have hpartial (z : Fin p × Fin q → ℝ) (i : Fin p) (j : Fin q) :
      fderiv ℝ f (T z) (EuclideanSpace.basisFun (Fin (p * q)) ℝ
        (finProdFinEquiv (i, j))) = matPartial F i j (matOfVec z) := by
    have hfd : fderiv ℝ f (T z) =
        (fderiv ℝ g z).comp T.symm.toContinuousLinearMap := by
      change fderiv ℝ (g ∘ T.symm) (T z) = _
      simpa using
        ((hgdiff (T.symm (T z))).hasFDerivAt.comp (T z) T.symm.hasFDerivAt).fderiv
    rw [hfd, ContinuousLinearMap.comp_apply]
    change fderiv ℝ g z (T.symm
      (EuclideanSpace.basisFun (Fin (p * q)) ℝ (finProdFinEquiv (i, j)))) = _
    rw [hbasis]
    change fderiv ℝ g z (Pi.single (i, j) 1) = _
    exact (matPartial_matOfVec i j (hgdiff z)).symm
  have hnorm (z : Fin p × Fin q → ℝ) :
      ‖fderiv ℝ f (T z)‖ ^ 2 =
        ∑ i : Fin p, ∑ j : Fin q, matPartial F i j (matOfVec z) ^ 2 := by
    rw [(EuclideanSpace.basisFun (Fin (p * q)) ℝ).norm_dual
      (fderiv ℝ f (T z))]
    rw [← Equiv.sum_comp finProdFinEquiv]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hpartial]
  have henergy_euclid :
      ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2
          ∂(stdGaussian (EuclideanSpace ℝ (Fin (p * q)))) =
        ∫⁻ z, ENNReal.ofReal
          (∑ i : Fin p, ∑ j : Fin q, matPartial F i j (matOfVec z) ^ 2) ∂ν := by
    rw [hT.lintegral_map_equiv
      (fun x => ‖fderiv ℝ f x‖ₑ ^ 2) T.toHomeomorph.toMeasurableEquiv]
    apply lintegral_congr
    intro z
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _) 2]
    change ENNReal.ofReal (‖fderiv ℝ f (T z)‖ ^ 2) = _
    rw [hnorm]
  have hraw_meas : Measurable (fun z : Fin p × Fin q → ℝ =>
      ENNReal.ofReal (∑ i : Fin p, ∑ j : Fin q,
        matPartial F i j (matOfVec z) ^ 2)) := by
    have hfun : (fun z : Fin p × Fin q → ℝ =>
        ∑ i : Fin p, ∑ j : Fin q, matPartial F i j (matOfVec z) ^ 2) =
        fun z => ∑ i : Fin p, ∑ j : Fin q,
          (fderiv ℝ g z (Pi.single (i, j) 1)) ^ 2 := by
      funext z
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [matPartial_matOfVec i j (hgdiff z)]
    rw [show (fun z => ENNReal.ofReal (∑ i : Fin p, ∑ j : Fin q,
        matPartial F i j (matOfVec z) ^ 2)) =
        fun z => ENNReal.ofReal (∑ i : Fin p, ∑ j : Fin q,
          (fderiv ℝ g z (Pi.single (i, j) 1)) ^ 2) by
      funext z
      rw [congrFun hfun z]]
    fun_prop
  have henergy_Y :
      (∫⁻ ω, ENNReal.ofReal (∑ i, ∑ j, matPartial F i j (Y ω) ^ 2) ∂μ) =
        ∫⁻ z, ENNReal.ofReal
          (∑ i : Fin p, ∑ j : Fin q, matPartial F i j (matOfVec z) ^ 2) ∂ν := by
    rw [← hZ, lintegral_map' hraw_meas.aemeasurable hmZ]
    rfl
  have hfenergy :
      ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2
          ∂(stdGaussian (EuclideanSpace ℝ (Fin (p * q)))) < ⊤ := by
    rw [henergy_euclid, ← henergy_Y]
    exact henergy
  have hvarYZ : IdentDistrib (fun ω => F (Y ω)) g μ ν := by
    have hident : IdentDistrib Z id μ ν := by
      refine ⟨hmZ, measurable_id.aemeasurable, ?_⟩
      simpa using hZ
    convert hident.comp hF.continuous.measurable using 1
    · ext ω
      rfl
    · ext z
      rfl
  have hvarT : IdentDistrib g f ν
      (stdGaussian (EuclideanSpace ℝ (Fin (p * q)))) := by
    have hident : IdentDistrib T id ν
        (stdGaussian (EuclideanSpace ℝ (Fin (p * q)))) := by
      refine ⟨T.continuous.measurable.aemeasurable, measurable_id.aemeasurable, ?_⟩
      simpa using hT.map_eq
    convert hident.comp hf.continuous.measurable using 1
    · ext z
      simp [f]
    · ext x
      rfl
  calc
    evariance (fun ω => F (Y ω)) μ = evariance g ν := hvarYZ.evariance_eq
    _ = evariance f (stdGaussian (EuclideanSpace ℝ (Fin (p * q)))) := hvarT.evariance_eq
    _ ≤ ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (Fin (p * q)))) :=
      gaussianPoincare (p * q) f hf hfenergy
    _ = ∫⁻ ω, ENNReal.ofReal
        (∑ i, ∑ j, matPartial F i j (Y ω) ^ 2) ∂μ := by
      rw [henergy_euclid, ← henergy_Y]

/-- Real-variance form of `gaussianPoincare_matrix`: with an integrable energy, `F(Y)` is in `L²` and
`Var F(Y) ≤ E ∑_{ij} (∂F/∂Y_ij)²`. Route: `gaussianPoincare_matrix`, then `evariance < ⊤` gives `MemLp 2`
(`evariance_lt_top_iff_memLp`) and `ENNReal.toReal` of both sides (`variance` is `(evariance).toReal`;
`ofReal_integral_eq_lintegral_ofReal` for the nonnegative energy). -/
theorem gaussianPoincare_matrix_real (hY : IsIIDGaussianMatrix μ Y) [IsProbabilityMeasure μ]
    {F : Matrix (Fin p) (Fin q) ℝ → ℝ}
    (hF : ContDiff ℝ 1 (fun x => F (matOfVec x)))
    (henergy : Integrable (fun ω => ∑ i, ∑ j, matPartial F i j (Y ω) ^ 2) μ) :
    MemLp (fun ω => F (Y ω)) 2 μ ∧
      variance (fun ω => F (Y ω)) μ ≤ ∫ ω, ∑ i, ∑ j, matPartial F i j (Y ω) ^ 2 ∂μ := by
  let E : Ω → ℝ := fun ω => ∑ i, ∑ j, matPartial F i j (Y ω) ^ 2
  have hnonneg : 0 ≤ᵐ[μ] E := ae_of_all μ fun ω => by
    dsimp [E]
    positivity
  have hlin : (∫⁻ ω, ENNReal.ofReal (E ω) ∂μ) < ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal henergy hnonneg]
    exact ENNReal.ofReal_lt_top
  have hpoincare := gaussianPoincare_matrix hY hF hlin
  have hmZ : AEMeasurable (fun ω => vecOfMat (Y ω)) μ :=
    aemeasurable_of_map_eq_pi_gaussian_matrix hY
  have hmeas : AEStronglyMeasurable (fun ω => F (Y ω)) μ := by
    have hcomp := hF.continuous.measurable.comp_aemeasurable hmZ
    have haemeas : AEMeasurable (fun ω => F (Y ω)) μ := by
      convert hcomp using 1
      ext ω
      rfl
    exact haemeas.aestronglyMeasurable
  have hvar_lt : evariance (fun ω => F (Y ω)) μ < ⊤ :=
    lt_of_le_of_lt hpoincare hlin
  have hmem : MemLp (fun ω => F (Y ω)) 2 μ :=
    (evariance_lt_top_iff_memLp hmeas).mp hvar_lt
  refine ⟨hmem, ?_⟩
  have hreal := (ENNReal.toReal_le_toReal hvar_lt.ne hlin.ne).2 hpoincare
  change variance (fun ω => F (Y ω)) μ ≤
    (∫⁻ ω, ENNReal.ofReal (E ω) ∂μ).toReal at hreal
  rw [← ofReal_integral_eq_lintegral_ofReal henergy hnonneg,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hnonneg)] at hreal
  exact hreal

end GaussianFoundations
