import Mathlib

/-!
# Foundations: cited probability results (task L-0.6a)

Three standard results that the appendix sections cite and that Mathlib does not contain in the
form the consumers need. Per `EXTERNAL-RESULTS.md` they are proved in Foundations, not certified;
every theorem below is a statement only (`sorry`). Proof routes are in the interface JSON
`phases-of-muon/appendix-nodes/results/L-0.6a-interface.json`.

* `efron_stein`: Boucheron–Lugosi–Massart, Thm 3.1. Consumers: A `lem:app-setup-truncation`(iii),
  B `lem:app-de-variance`.
* `levy_upward_L2`: Williams, Thm 14.2 (L² form). Consumers: C `lem:app-drift-covariance`
  (bounded case), E `lem:app-dyn-covariance`.
* `doob_L2`: Williams, Thm 14.11 (Doob L²). Consumer: E `lem:app-dyn-martingale`.

Mathlib has the weak-type `MeasureTheory.maximal_ineq`, the a.e. and L¹ forms of Lévy upward
(`MeasureTheory.Integrable.tendsto_ae_condExp`, `MeasureTheory.Integrable.tendsto_eLpNorm_condExp`),
and no Efron–Stein inequality and no L² forms of Lévy or Doob.

Snapshot tag: `cr-2026-10-23`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ProbabilityFoundations

private lemma es_mix_mp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)] (T : Finset ι) :
    MeasurePreserving
      (fun q : (∀ i, X i) × (∀ i, X i) => fun i => if i ∈ T then q.1 i else q.2 i)
      ((Measure.pi μ).prod (Measure.pi μ)) (Measure.pi μ) := by
  have hm : Measurable
      (fun q : (∀ i, X i) × (∀ i, X i) => fun i => if i ∈ T then q.1 i else q.2 i) := by
    refine measurable_pi_iff.2 fun i => ?_
    by_cases h : i ∈ T <;> simp only [h, if_true, if_false] <;> fun_prop
  refine ⟨hm, ?_⟩
  refine (Measure.pi_eq ?_).symm
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have : (fun q : (∀ i, X i) × (∀ i, X i) => fun i => if i ∈ T then q.1 i else q.2 i) ⁻¹'
      (Set.univ.pi s) =
      (Set.univ.pi fun i => if i ∈ T then s i else Set.univ) ×ˢ
      (Set.univ.pi fun i => if i ∈ T then Set.univ else s i) := by
    ext q
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun i => ?_⟩
      · by_cases hi : i ∈ T
        · simpa [hi] using h i
        · simp [hi]
      · by_cases hi : i ∈ T
        · simp [hi]
        · simpa [hi] using h i
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i ∈ T
      · simpa [hi] using h1 i
      · simpa [hi] using h2 i
  rw [this, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ T <;> simp [hi]



private lemma es_mp_integral {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {g : α → β} (hg : MeasurePreserving g μ ν)
    {φ : β → ℝ} (hφ : AEStronglyMeasurable φ ν) :
    ∫ a, φ (g a) ∂μ = ∫ b, φ b ∂ν := by
  rw [← hg.map_eq, integral_map hg.aemeasurable]
  rwa [hg.map_eq]

private lemma es_sq_integral_le {β : Type*} [MeasurableSpace β] (π : Measure β)
    [IsProbabilityMeasure π] {u : β → ℝ} (hu : MemLp u 2 π) :
    (∫ b, u b ∂π) ^ 2 ≤ ∫ b, u b ^ 2 ∂π := by
  have h := variance_nonneg u π
  rw [variance_eq_sub hu] at h
  simp only [Pi.pow_apply] at h
  linarith

private lemma es_jensen {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) [SFinite ν] (π : Measure β) [IsProbabilityMeasure π]
    {Φ : α × β → ℝ} (hΦ : MemLp Φ 2 (ν.prod π)) :
    MemLp (fun a => ∫ b, Φ (a, b) ∂π) 2 ν ∧
    ∫ a, (∫ b, Φ (a, b) ∂π) ^ 2 ∂ν ≤ ∫ z, Φ z ^ 2 ∂(ν.prod π) := by
  have hΦ2 : Integrable (fun z => Φ z ^ 2) (ν.prod π) := hΦ.integrable_sq
  have hae : ∀ᵐ a ∂ν, Integrable (fun b => Φ (a, b) ^ 2) π := hΦ2.prod_right_ae
  have hmem : ∀ᵐ a ∂ν, MemLp (fun b => Φ (a, b)) 2 π := by
    filter_upwards [hae, hΦ.aestronglyMeasurable.prodMk_left] with a ha1 ha2
    exact (memLp_two_iff_integrable_sq ha2).2 ha1
  have hint : Integrable (fun a => ∫ b, Φ (a, b) ^ 2 ∂π) ν := hΦ2.integral_prod_left
  have hle : ∀ᵐ a ∂ν, (∫ b, Φ (a, b) ∂π) ^ 2 ≤ ∫ b, Φ (a, b) ^ 2 ∂π := by
    filter_upwards [hmem] with a ha using es_sq_integral_le π ha
  have hmeas : AEStronglyMeasurable (fun a => ∫ b, Φ (a, b) ∂π) ν :=
    hΦ.aestronglyMeasurable.integral_prod_right'
  have hsq : Integrable (fun a => (∫ b, Φ (a, b) ∂π) ^ 2) ν := by
    refine hint.mono' (hmeas.pow 2) ?_
    filter_upwards [hle] with a ha
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact ha
  refine ⟨(memLp_two_iff_integrable_sq hmeas).2 hsq, ?_⟩
  rw [integral_prod _ hΦ2]
  exact integral_mono_ae hsq hint hle

private lemma es_mem_P {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (π : Measure (∀ i, X i)) [IsProbabilityMeasure π]
    (hmix : ∀ T : Finset ι, MeasurePreserving
      (fun q : (∀ i, X i) × (∀ i, X i) => fun i => if i ∈ T then q.1 i else q.2 i)
      (π.prod π) π) (T : Finset ι) {f : (∀ i, X i) → ℝ} (hf : MemLp f 2 π) :
    MemLp (fun x => ∫ y, f (fun i => if i ∈ T then x i else y i) ∂π) 2 π := by
  have := hf.comp_measurePreserving (hmix T)
  exact (es_jensen π π this).1

private lemma es_P_idem {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (π : Measure (∀ i, X i)) [IsProbabilityMeasure π]
    (hmix : ∀ T : Finset ι, MeasurePreserving
      (fun q : (∀ i, X i) × (∀ i, X i) => fun i => if i ∈ T then q.1 i else q.2 i)
      (π.prod π) π) (T : Finset ι) (h : (∀ i, X i) → ℝ) (x y : ∀ i, X i) :
    (∫ y', h (fun i => if i ∈ T then (fun i => if i ∈ T then x i else y i) i else y' i) ∂π)
      = ∫ y', h (fun i => if i ∈ T then x i else y' i) ∂π := by
  congr 1
  funext y'
  congr 1
  funext i
  by_cases hi : i ∈ T <;> simp [hi]

private lemma es_decomp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (π : Measure (∀ i, X i)) [IsProbabilityMeasure π]
    (hmix : ∀ T : Finset ι, MeasurePreserving
      (fun q : (∀ i, X i) × (∀ i, X i) => fun i => if i ∈ T then q.1 i else q.2 i)
      (π.prod π) π) (j : ι) {h : (∀ i, X i) → ℝ} (hh : MemLp h 2 π) :
    variance h π =
      (1 / 2) * ∫ p, (h p.1 - h (Function.update p.1 j (p.2 j))) ^ 2 ∂(π.prod π)
      + variance (fun x => ∫ y, h (fun i => if i ∈ Finset.univ.erase j then x i else y i) ∂π) π := by
  set C : Finset ι := Finset.univ.erase j with hC
  have hupd : ∀ x y : ∀ i, X i, Function.update x j (y j) =
      (fun i => if i ∈ C then x i else y i) := by
    intro x y
    funext i
    by_cases hi : i = j
    · subst hi; simp [hC]
    · simp [hC, hi, Function.update_of_ne hi]
  simp_rw [hupd]
  set u : (∀ i, X i) → ℝ := fun x => ∫ y, h (fun i => if i ∈ C then x i else y i) ∂π with hu_def
  have hu : MemLp u 2 π := es_mem_P π hmix C hh
  have hhm : MemLp (fun q : (∀ i, X i) × (∀ i, X i) => h (fun i => if i ∈ C then q.1 i else q.2 i))
      2 (π.prod π) := hh.comp_measurePreserving (hmix C)
  have hh1 : MemLp (fun q : (∀ i, X i) × (∀ i, X i) => h q.1) 2 (π.prod π) :=
    hh.comp_measurePreserving (measurePreserving_fst (μ := π) (ν := π))
  have hu1 : MemLp (fun q : (∀ i, X i) × (∀ i, X i) => u q.1) 2 (π.prod π) :=
    hu.comp_measurePreserving (measurePreserving_fst (μ := π) (ν := π))
  -- F1
  have F1 : ∫ x, u x ∂π = ∫ x, h x ∂π := by
    have := integral_prod (fun q : (∀ i, X i) × (∀ i, X i) =>
      h (fun i => if i ∈ C then q.1 i else q.2 i)) (hhm.integrable (by norm_num))
    rw [es_mp_integral (hmix C) hh.aestronglyMeasurable] at this
    exact this.symm
  -- idempotence
  have hidem : ∀ x y : ∀ i, X i, u (fun i => if i ∈ C then x i else y i) = u x := by
    intro x y
    exact es_P_idem π hmix C h x y
  -- F2
  have F2 : ∫ x, h x * u x ∂π = ∫ x, u x ^ 2 ∂π := by
    have hint : Integrable (fun q : (∀ i, X i) × (∀ i, X i) =>
        h (fun i => if i ∈ C then q.1 i else q.2 i) * u q.1) (π.prod π) := hhm.integrable_mul hu1
    have e1 : ∫ x, h x * u x ∂π = ∫ q : (∀ i, X i) × (∀ i, X i),
        (fun w => h w * u w) (fun i => if i ∈ C then q.1 i else q.2 i) ∂(π.prod π) := by
      exact (es_mp_integral (hmix C) (φ := fun w => h w * u w)
        (hh.aestronglyMeasurable.mul hu.aestronglyMeasurable)).symm
    rw [e1]
    simp_rw [hidem]
    rw [integral_prod _ hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [integral_mul_const, sq]
  -- F3
  have F3 : ∫ q, (h q.1 - h (fun i => if i ∈ C then q.1 i else q.2 i)) ^ 2 ∂(π.prod π)
      = 2 * ∫ x, h x ^ 2 ∂π - 2 * ∫ x, u x ^ 2 ∂π := by
    have i1 : Integrable (fun q : (∀ i, X i) × (∀ i, X i) => h q.1 ^ 2) (π.prod π) :=
      hh1.integrable_sq
    have i2 : Integrable (fun q : (∀ i, X i) × (∀ i, X i) =>
        h (fun i => if i ∈ C then q.1 i else q.2 i) ^ 2) (π.prod π) := hhm.integrable_sq
    have i3 : Integrable (fun q : (∀ i, X i) × (∀ i, X i) =>
        h q.1 * h (fun i => if i ∈ C then q.1 i else q.2 i)) (π.prod π) := hh1.integrable_mul hhm
    have e : ∀ q : (∀ i, X i) × (∀ i, X i),
        (h q.1 - h (fun i => if i ∈ C then q.1 i else q.2 i)) ^ 2 =
        h q.1 ^ 2 + h (fun i => if i ∈ C then q.1 i else q.2 i) ^ 2
          - 2 * (h q.1 * h (fun i => if i ∈ C then q.1 i else q.2 i)) := by
      intro q; ring
    simp_rw [e]
    have k1 : Integrable (fun q : (∀ i, X i) × (∀ i, X i) => h q.1 ^ 2 +
        h (fun i => if i ∈ C then q.1 i else q.2 i) ^ 2) (π.prod π) := i1.add i2
    have k2 : Integrable (fun q : (∀ i, X i) × (∀ i, X i) => 2 * (h q.1 *
        h (fun i => if i ∈ C then q.1 i else q.2 i))) (π.prod π) := i3.const_mul 2
    rw [integral_sub k1 k2, integral_add i1 i2, integral_const_mul]
    have j1 : ∫ q : (∀ i, X i) × (∀ i, X i), h q.1 ^ 2 ∂(π.prod π) = ∫ x, h x ^ 2 ∂π := by
      rw [integral_prod _ i1]; simp
    have j2 : ∫ q : (∀ i, X i) × (∀ i, X i),
        h (fun i => if i ∈ C then q.1 i else q.2 i) ^ 2 ∂(π.prod π) = ∫ x, h x ^ 2 ∂π := by
      have := es_mp_integral (hmix C) (φ := fun w => h w ^ 2)
        (hh.aestronglyMeasurable.pow 2)
      exact this
    have j3 : ∫ q : (∀ i, X i) × (∀ i, X i),
        h q.1 * h (fun i => if i ∈ C then q.1 i else q.2 i) ∂(π.prod π) = ∫ x, u x ^ 2 ∂π := by
      rw [integral_prod _ i3, ← F2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      rw [integral_const_mul]
    rw [j1, j2, j3]; ring
  rw [F3]
  rw [variance_eq_sub hh, variance_eq_sub hu]
  simp only [Pi.pow_apply]
  rw [F1]
  ring

private lemma es_tower {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (π : Measure (∀ i, X i)) [IsProbabilityMeasure π]
    (hmix : ∀ T : Finset ι, MeasurePreserving
      (fun q : (∀ i, X i) × (∀ i, X i) => fun i => if i ∈ T then q.1 i else q.2 i)
      (π.prod π) π) (A B : Finset ι) {h : (∀ i, X i) → ℝ} (hh : MemLp h 2 π) :
    ∀ᵐ x ∂π, (∫ y', (∫ y, h (fun i => if i ∈ B then
        (fun i => if i ∈ A then x i else y' i) i else y i) ∂π) ∂π)
      = ∫ w, h (fun i => if i ∈ A ∩ B then x i else w i) ∂π := by
  have hint : Integrable (fun q : (∀ i, X i) × (∀ i, X i) =>
      h (fun i => if i ∈ A ∩ B then q.1 i else q.2 i)) (π.prod π) :=
    (hh.comp_measurePreserving (hmix (A ∩ B))).integrable (by norm_num)
  filter_upwards [hint.prod_right_ae] with x hx
  have e : ∀ y' y : ∀ i, X i, h (fun i => if i ∈ B then
        (fun i => if i ∈ A then x i else y' i) i else y i)
      = (fun w => h (fun i => if i ∈ A ∩ B then x i else w i))
          (fun i => if i ∈ B then y' i else y i) := by
    intro y' y
    congr 1
    funext i
    by_cases hB : i ∈ B <;> by_cases hA : i ∈ A <;> simp [hB, hA]
  simp_rw [e]
  have hx' : Integrable (fun q : (∀ i, X i) × (∀ i, X i) =>
      (fun w => h (fun i => if i ∈ A ∩ B then x i else w i))
        (fun i => if i ∈ B then q.1 i else q.2 i)) (π.prod π) :=
    (hmix B).integrable_comp_of_integrable hx
  rw [← integral_prod _ hx']
  exact es_mp_integral (hmix B) (φ := fun w => h (fun i => if i ∈ A ∩ B then x i else w i))
    hx.aestronglyMeasurable

private lemma es_upd_eq_mix {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} (j : ι)
    (x y : ∀ i, X i) :
    Function.update x j (y j) = (fun i => if i ∈ Finset.univ.erase j then x i else y i) := by
  classical
  funext i
  by_cases hi : i = j
  · subst hi; simp
  · simp [hi, Function.update_of_ne hi]

private lemma es_mix_upd {ι : Type*} [DecidableEq ι] {X : ι → Type*} (j : ι) (T : Finset ι)
    (hj : j ∈ T) (x y : ∀ i, X i) (s : X j) :
    (fun i => if i ∈ T then Function.update x j s i else y i) =
      Function.update (fun i => if i ∈ T then x i else y i) j s := by
  funext i
  by_cases hi : i = j
  · subst hi; simp [hj]
  · simp [hi, Function.update_of_ne hi]

private lemma es_contract {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (π : Measure (∀ i, X i)) [IsProbabilityMeasure π]
    (hmix : ∀ T : Finset ι, MeasurePreserving
      (fun q : (∀ i, X i) × (∀ i, X i) => fun i => if i ∈ T then q.1 i else q.2 i)
      (π.prod π) π) (j : ι) (T : Finset ι) (hj : j ∈ T)
    {f : (∀ i, X i) → ℝ} (hf : MemLp f 2 π) :
    ∫ p, ((∫ y, f (fun i => if i ∈ T then p.1 i else y i) ∂π)
        - (∫ y, f (fun i => if i ∈ T then (Function.update p.1 j (p.2 j)) i else y i) ∂π)) ^ 2
        ∂(π.prod π)
      ≤ ∫ p, (f p.1 - f (Function.update p.1 j (p.2 j))) ^ 2 ∂(π.prod π) := by
  set C : Finset ι := Finset.univ.erase j with hC
  -- measure preserving maps on the triple space
  have hid : MeasurePreserving (Prod.map (fun q : (∀ i, X i) × (∀ i, X i) => q.1) (id : (∀ i, X i) → (∀ i, X i)))
      (((π.prod π)).prod π) (π.prod π) :=
    (measurePreserving_fst (μ := π) (ν := π)).prod (MeasurePreserving.id π)
  have hg1 : MeasurePreserving
      (fun r : ((∀ i, X i) × (∀ i, X i)) × (∀ i, X i) => fun i => if i ∈ T then r.1.1 i else r.2 i)
      ((π.prod π).prod π) π := (hmix T).comp hid
  have hid2 : MeasurePreserving
      (Prod.map (fun q : (∀ i, X i) × (∀ i, X i) => fun i => if i ∈ C then q.1 i else q.2 i)
        (id : (∀ i, X i) → (∀ i, X i)))
      (((π.prod π)).prod π) (π.prod π) :=
    (hmix C).prod (MeasurePreserving.id π)
  have hg2 : MeasurePreserving
      (fun r : ((∀ i, X i) × (∀ i, X i)) × (∀ i, X i) =>
        fun i => if i ∈ T then (fun i => if i ∈ C then r.1.1 i else r.1.2 i) i else r.2 i)
      ((π.prod π).prod π) π := (hmix T).comp hid2
  have h1 := hf.comp_measurePreserving hg1
  have h2 := hf.comp_measurePreserving hg2
  have hΦ : MemLp (fun r : ((∀ i, X i) × (∀ i, X i)) × (∀ i, X i) =>
      f (fun i => if i ∈ T then r.1.1 i else r.2 i) -
      f (fun i => if i ∈ T then (fun i => if i ∈ C then r.1.1 i else r.1.2 i) i else r.2 i))
      2 ((π.prod π).prod π) := h1.sub h2
  obtain ⟨-, hJ⟩ := es_jensen (π.prod π) π hΦ
  -- sections integrable a.e.
  have s1 := (h1.integrable (by norm_num)).prod_right_ae
  have s2 := (h2.integrable (by norm_num)).prod_right_ae
  have hpt : ∀ᵐ z ∂(π.prod π),
      ((∫ y, f (fun i => if i ∈ T then z.1 i else y i) ∂π)
        - (∫ y, f (fun i => if i ∈ T then (Function.update z.1 j (z.2 j)) i else y i) ∂π))
      = ∫ y, (f (fun i => if i ∈ T then z.1 i else y i) -
      f (fun i => if i ∈ T then (fun i => if i ∈ C then z.1 i else z.2 i) i else y i)) ∂π := by
    filter_upwards [s1, s2] with z hz1 hz2
    rw [es_upd_eq_mix j z.1 z.2]
    exact (integral_sub hz1 hz2).symm
  have hlhs : ∫ p, ((∫ y, f (fun i => if i ∈ T then p.1 i else y i) ∂π)
        - (∫ y, f (fun i => if i ∈ T then (Function.update p.1 j (p.2 j)) i else y i) ∂π)) ^ 2
        ∂(π.prod π) = ∫ z, (∫ y, (f (fun i => if i ∈ T then z.1 i else y i) -
      f (fun i => if i ∈ T then (fun i => if i ∈ C then z.1 i else z.2 i) i else y i)) ∂π) ^ 2
        ∂(π.prod π) := by
    refine integral_congr_ae ?_
    filter_upwards [hpt] with z hz
    simp only [hz]
  rw [hlhs]
  refine hJ.trans (le_of_eq ?_)
  -- change variables on the triple space
  have hσ : MeasurePreserving
      (fun r : ((∀ i, X i) × (∀ i, X i)) × (∀ i, X i) =>
        ((fun i => if i ∈ T then r.1.1 i else r.2 i), r.1.2))
      ((π.prod π).prod π) (π.prod π) := by
    have e1 := measurePreserving_prodAssoc π π π
    have e2 : MeasurePreserving (Prod.map (id : (∀ i, X i) → (∀ i, X i)) Prod.swap)
        (π.prod (π.prod π)) (π.prod (π.prod π)) :=
      (MeasurePreserving.id π).prod Measure.measurePreserving_swap
    have e3 := (measurePreserving_prodAssoc π π π).symm
    have e4 := (e3.comp e2).comp e1
    have e5 := ((hmix T).prod (MeasurePreserving.id π)).comp e4
    convert e5 using 1
    funext r
    rfl
  have hf1 : MemLp (fun w : (∀ i, X i) × (∀ i, X i) => f w.1) 2 (π.prod π) :=
    hf.comp_measurePreserving (measurePreserving_fst (μ := π) (ν := π))
  have hfm : MemLp (fun w : (∀ i, X i) × (∀ i, X i) => f (Function.update w.1 j (w.2 j))) 2
      (π.prod π) := by
    simp_rw [es_upd_eq_mix]
    exact hf.comp_measurePreserving (hmix C)
  have hφm : AEStronglyMeasurable (fun w : (∀ i, X i) × (∀ i, X i) =>
      (f w.1 - f (Function.update w.1 j (w.2 j))) ^ 2) (π.prod π) :=
    (hf1.sub hfm).aestronglyMeasurable.pow 2
  have hψ := es_mp_integral hσ
    (φ := fun w : (∀ i, X i) × (∀ i, X i) => (f w.1 - f (Function.update w.1 j (w.2 j))) ^ 2) hφm
  rw [← hψ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp only [Function.comp]
  have hupdC : Function.update r.1.1 j (r.1.2 j) = (fun i => if i ∈ C then r.1.1 i else r.1.2 i) :=
    es_upd_eq_mix j r.1.1 r.1.2
  have key : (fun i => if i ∈ T then (if i ∈ C then r.1.1 i else r.1.2 i) else r.2 i) =
      Function.update (fun i => if i ∈ T then r.1.1 i else r.2 i) j (r.1.2 j) := by
    rw [← es_mix_upd j T hj r.1.1 r.2 (r.1.2 j), hupdC]
  rw [key]

private lemma es_main {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (π : Measure (∀ i, X i)) [IsProbabilityMeasure π]
    (hmix : ∀ T : Finset ι, MeasurePreserving
      (fun q : (∀ i, X i) × (∀ i, X i) => fun i => if i ∈ T then q.1 i else q.2 i)
      (π.prod π) π) {f : (∀ i, X i) → ℝ} (hf : MemLp f 2 π) (T : Finset ι) :
    variance (fun x => ∫ y, f (fun i => if i ∈ T then x i else y i) ∂π) π ≤
      ∑ j ∈ T, (1 / 2) * ∫ p, (f p.1 - f (Function.update p.1 j (p.2 j))) ^ 2 ∂(π.prod π) := by
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, if_false, Finset.sum_empty]
    have : variance (fun _ : (∀ i, X i) => ∫ y, f (fun i => y i) ∂π) π = 0 := by
      rw [variance_eq_sub (memLp_const _)]
      simp
    exact this.le
  | insert j S hjS ih =>
    set T : Finset ι := insert j S with hT
    have hh := es_mem_P π hmix T hf
    have dec := es_decomp π hmix j hh
    have hc := es_contract π hmix j T (Finset.mem_insert_self j S) hf
    have htow := es_tower π hmix (Finset.univ.erase j) T hf
    have hCT : Finset.univ.erase j ∩ T = S := by
      ext i
      by_cases hi : i = j
      · subst hi; simp [hjS]
      · simp [hT, hi]
    rw [hCT] at htow
    have hv : variance (fun x => ∫ y, (fun x => ∫ y, f (fun i => if i ∈ T then x i else y i) ∂π)
        (fun i => if i ∈ Finset.univ.erase j then x i else y i) ∂π) π =
        variance (fun x => ∫ y, f (fun i => if i ∈ S then x i else y i) ∂π) π := by
      refine variance_congr ?_
      filter_upwards [htow] with x hx
      exact hx
    rw [Finset.sum_insert hjS, dec, hv]
    have := ih
    linarith

/-- Efron–Stein inequality for a finite product of probability spaces.

Source: Boucheron, Lugosi, Massart, *Concentration Inequalities* (2013), Thm 3.1 (Efron–Stein).
Here `ι` is a finite index set, `X i` carry probability measures `μ i`, and the product measure
is `Measure.pi μ`. The right-hand side uses an independent copy of the sample: the second factor
of `(Measure.pi μ).prod (Measure.pi μ)` is the copy `p.2`, and `Function.update p.1 i (p.2 i)`
replaces the `i`-th coordinate of `p.1` by the `i`-th coordinate of the copy.

Consumers (EXTERNAL-RESULTS.md): A `lem:app-setup-truncation`(iii), B `lem:app-de-variance`.
The hypothesis `MemLp f 2` is the square-integrability needed for the variance to be finite. -/
theorem efron_stein {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, X i) → ℝ) (hf : MemLp f 2 (Measure.pi μ)) :
    variance f (Measure.pi μ) ≤
      (1 / 2) * ∑ i, ∫ p, (f p.1 - f (Function.update p.1 i (p.2 i))) ^ 2
        ∂((Measure.pi μ).prod (Measure.pi μ)) := by
  have h := es_main (Measure.pi μ) (es_mix_mp μ) hf Finset.univ
  have e : (fun x => ∫ y, f (fun i => if i ∈ (Finset.univ : Finset ι) then x i else y i)
      ∂(Measure.pi μ)) = f := by
    funext x
    simp
  rw [e, ← Finset.mul_sum] at h
  exact h

private lemma levy_clamp_abs (x N : ℝ) (hN : 0 ≤ N) :
    |x - max (-N) (min N x)| ≤ |x| := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    rcases le_total N x with h1 | h1
    · rw [min_eq_left h1, max_eq_right (by linarith)]
      rw [abs_le]; constructor <;> linarith
    · rw [min_eq_right h1, max_eq_right (by linarith)]
      rw [abs_le]; constructor <;> linarith
  · rw [abs_of_nonpos hx, min_eq_right (by linarith : x ≤ N)]
    rcases le_total (-N) x with h1 | h1
    · rw [max_eq_right h1, sub_self, abs_zero]
      linarith
    · rw [max_eq_left h1]
      rw [abs_le]; constructor <;> linarith

private lemma levy_clamp_fix (x N : ℝ) (h : |x| < N) :
    x - max (-N) (min N x) = 0 := by
  have h' := abs_lt.1 h
  rw [min_eq_right h'.2.le, max_eq_right h'.1.le, sub_self]

/-- Truncation step of the `L²` Lévy theorem (private helper). -/
private theorem levy_trunc_L2 {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    (F : Ω → ℝ) (hF : MemLp F 2 μ) (hFm : StronglyMeasurable F) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ N : ℕ, eLpNorm (fun ω => F ω - max (-(N : ℝ)) (min (N : ℝ) (F ω))) 2 μ ≤ ε := by
  obtain ⟨M, hM⟩ := hF.eLpNorm_indicator_norm_ge_le hFm hε
  refine ⟨⌈M⌉₊, ?_⟩
  have hNle : M ≤ ((⌈M⌉₊ : ℕ) : ℝ) := Nat.le_ceil M
  have hT : StronglyMeasurable
      (fun ω => max (-((⌈M⌉₊ : ℕ) : ℝ)) (min ((⌈M⌉₊ : ℕ) : ℝ) (F ω))) :=
    (by fun_prop : Continuous fun y : ℝ =>
      max (-((⌈M⌉₊ : ℕ) : ℝ)) (min ((⌈M⌉₊ : ℕ) : ℝ) y)).comp_stronglyMeasurable hFm
  refine le_trans (eLpNorm_mono (hFm.sub hT).aestronglyMeasurable ?_) hM
  intro ω
  by_cases h : M ≤ ((‖F ω‖₊ : NNReal) : ℝ)
  · rw [Set.indicator_of_mem (show ω ∈ {x | M ≤ ((‖F x‖₊ : NNReal) : ℝ)} from h)]
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact levy_clamp_abs _ _ (Nat.cast_nonneg _)
  · rw [Set.indicator_of_notMem (show ω ∉ {x | M ≤ ((‖F x‖₊ : NNReal) : ℝ)} from h)]
    have h' : |F ω| < ((⌈M⌉₊ : ℕ) : ℝ) := by
      have := not_le.1 h
      simp only [coe_nnnorm, Real.norm_eq_abs] at this
      linarith
    rw [levy_clamp_fix _ _ h']

/-- Bounded case of the `L²` Lévy theorem (private helper): a bounded `ℱ∞`-measurable `G`
has `𝔼[G | ℱ n] → G` in `L²`, by Lévy a.e. convergence and uniform integrability. -/
private theorem levy_bdd_L2 {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (G : Ω → ℝ) (R : NNReal)
    (hG : StronglyMeasurable[⨆ n, ℱ n] G) (hR : ∀ ω, |G ω| ≤ (R : ℝ)) :
    Tendsto (fun n => eLpNorm (μ[G | ℱ n] - G) 2 μ) atTop (𝓝 0) := by
  have hle : ⨆ n, ℱ n ≤ m0 := iSup_le fun n => ℱ.le n
  have hGm : StronglyMeasurable G := hG.mono hle
  have hGL2 : MemLp G 2 μ :=
    MemLp.of_bound hGm.aestronglyMeasurable (R : ℝ)
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hR ω)
  have hae : ∀ᵐ ω ∂μ, Tendsto (fun n => μ[G | ℱ n] ω) atTop (𝓝 (G ω)) :=
    (hGL2.integrable one_le_two).tendsto_ae_condExp hG
  have hbd : ∀ n, ∀ᵐ ω ∂μ, |μ[G | ℱ n] ω| ≤ (R : ℝ) := fun n =>
    ae_bdd_abs_condExp_of_ae_bdd_abs (ae_of_all _ hR)
  have hunif : UnifIntegrable (fun n => μ[G | ℱ n]) 2 μ := by
    refine unifIntegrable_of one_le_two (by norm_num)
      (fun n => (stronglyMeasurable_condExp.mono (ℱ.le n)).aestronglyMeasurable) ?_
    intro ε hε
    refine ⟨R + 1, fun n => ?_⟩
    have hz : ({x | R + 1 ≤ ‖μ[G | ℱ n] x‖₊}.indicator (μ[G | ℱ n])) =ᵐ[μ] (0 : Ω → ℝ) := by
      filter_upwards [hbd n] with ω hω
      have hlt : ¬ (R + 1 ≤ ‖μ[G | ℱ n] ω‖₊) := by
        intro h
        have h' := NNReal.coe_le_coe.2 h
        rw [coe_nnnorm, Real.norm_eq_abs] at h'
        push_cast at h'
        linarith
      rw [Set.indicator_of_notMem (show ω ∉ {x | R + 1 ≤ ‖μ[G | ℱ n] x‖₊} from hlt)]
      rfl
    rw [eLpNorm_congr_ae hz, eLpNorm_zero]
    exact zero_le
  exact tendsto_Lp_finite_of_tendsto_ae one_le_two (by norm_num)
    (fun n => (stronglyMeasurable_condExp.mono (ℱ.le n)).aestronglyMeasurable) hGL2 hunif hae

/-- Lévy's upward theorem, `L²` form.

Source: Williams, *Probability with Martingales* (1991), Thm 14.2 (Lévy upward), `L²` case.
Let `ℱ` be a filtration on a probability space `(Ω, m0, μ)` and let `F ∈ L²` be measurable with
respect to `⨆ n, ℱ n`. Then `𝔼[F | ℱ n] → F` in `L²(μ)`.

Consumers (EXTERNAL-RESULTS.md): C `lem:app-drift-covariance` (bounded case, where `F` is bounded),
E `lem:app-dyn-covariance`. -/
theorem levy_upward_L2 {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    (F : Ω → ℝ) (hF : MemLp F 2 μ) (hFmeas : StronglyMeasurable[⨆ n, ℱ n] F) :
    Tendsto (fun n => eLpNorm (μ[F | ℱ n] - F) 2 μ) atTop (𝓝 0) := by
  have hle : ⨆ n, ℱ n ≤ m0 := iSup_le fun n => ℱ.le n
  have hFm : StronglyMeasurable F := hFmeas.mono hle
  have hFint : Integrable F μ := hF.integrable one_le_two
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3 : (0 : ℝ≥0∞) < ε / 3 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨N, hN⟩ := levy_trunc_L2 F hF hFm hε3
  set G : Ω → ℝ := fun ω => max (-(N : ℝ)) (min (N : ℝ) (F ω)) with hGdef
  have hGm : StronglyMeasurable[⨆ n, ℱ n] G :=
    (by fun_prop : Continuous fun y : ℝ => max (-(N : ℝ)) (min (N : ℝ) y)).comp_stronglyMeasurable
      hFmeas
  have hGm0 : StronglyMeasurable G := hGm.mono hle
  have hR : ∀ ω, |G ω| ≤ (((N : NNReal)) : ℝ) := fun ω => by
    rw [NNReal.coe_natCast]
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    refine abs_le.2 ⟨le_trans (by linarith) (le_max_left _ _), max_le (by linarith) ?_⟩
    exact min_le_left _ _
  have hGL2 : MemLp G 2 μ :=
    MemLp.of_bound hGm0.aestronglyMeasurable ((N : ℝ))
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        have := hR ω
        rwa [NNReal.coe_natCast] at this)
  have hGint : Integrable G μ := hGL2.integrable one_le_two
  have hB := levy_bdd_L2 (μ := μ) ℱ G (N : NNReal) hGm hR
  have hBev := (ENNReal.tendsto_nhds_zero.1 hB) (ε / 3) hε3
  filter_upwards [hBev] with n hn
  have hcond := condExp_sub hFint hGint (ℱ n)
  have hid : (fun ω => μ[F | ℱ n] ω - F ω) =ᵐ[μ]
      (fun ω => μ[F - G | ℱ n] ω + (μ[G | ℱ n] ω - G ω) + (-(F ω - G ω))) := by
    filter_upwards [hcond] with ω hω
    simp only [Pi.sub_apply] at hω
    rw [hω]
    ring
  have hsplit : eLpNorm (fun ω => μ[F | ℱ n] ω - F ω) 2 μ ≤
      eLpNorm (μ[F - G | ℱ n]) 2 μ + eLpNorm (fun ω => μ[G | ℱ n] ω - G ω) 2 μ +
        eLpNorm (fun ω => -(F ω - G ω)) 2 μ := by
    rw [eLpNorm_congr_ae hid]
    have e1 := eLpNorm_add_le (μ := μ) (f := μ[F - G | ℱ n] + fun ω => μ[G | ℱ n] ω - G ω)
      (g := fun ω => -(F ω - G ω)) one_le_two
    have e2 := eLpNorm_add_le (μ := μ) (f := μ[F - G | ℱ n])
      (g := fun ω => μ[G | ℱ n] ω - G ω) one_le_two
    exact e1.trans (add_le_add e2 le_rfl)
  have h1 : eLpNorm (μ[F - G | ℱ n]) 2 μ ≤ ε / 3 :=
    (eLpNorm_condExp_le_eLpNorm (m := ℱ n) (F - G) one_le_two).trans hN
  have h3 : eLpNorm (fun ω => -(F ω - G ω)) 2 μ ≤ ε / 3 := by
    have e : eLpNorm (fun ω => -(F ω - G ω)) 2 μ = eLpNorm (fun ω => F ω - G ω) 2 μ :=
      eLpNorm_neg _ _ _
    rw [e]
    exact hN
  calc eLpNorm (fun ω => μ[F | ℱ n] ω - F ω) 2 μ
      ≤ eLpNorm (μ[F - G | ℱ n]) 2 μ + eLpNorm (fun ω => μ[G | ℱ n] ω - G ω) 2 μ +
        eLpNorm (fun ω => -(F ω - G ω)) 2 μ := hsplit
    _ ≤ ε / 3 + ε / 3 + ε / 3 := add_le_add (add_le_add h1 hn) h3
    _ = ε := ENNReal.add_thirds ε

private theorem doob_abs_submart {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ)
    (hM : Martingale M ℱ μ) (hL2 : ∀ j, MemLp (M j) 2 μ) :
    Submartingale (fun j ω => |M j ω|) ℱ μ := by
  refine ⟨fun j => by simpa [Real.norm_eq_abs] using (hM.1 j).norm, ?_, ?_⟩
  · intro i j hij
    have h1 : (fun ω => |M i ω|) =ᵐ[μ] |μ[M j | ℱ i]| := by
      filter_upwards [hM.2 i j hij] with ω hω
      simp [hω]
    exact h1.trans_le (abs_condExp_ae_le_condExp_abs (m := ℱ i) (μ := μ) (M j))
  · intro j
    exact (hL2 j).integrable one_le_two |>.abs

/-- Doob's `L²` maximal inequality for a square-integrable martingale indexed by `ℕ`.

Source: Williams, *Probability with Martingales* (1991), Thm 14.11 (Doob `L^p`, `p = 2`):
for a martingale `(M j)` with `M j ∈ L²` for every `j`,
`𝔼 max_{j ≤ n} M_j² ≤ 4 𝔼 M_n²`.
Both sides are written as lower Lebesgue integrals of `ℝ≥0∞`-valued functions, so no
integrability of the maximum is assumed.

Consumer (EXTERNAL-RESULTS.md): E `lem:app-dyn-martingale`. -/
theorem doob_L2 {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ)
    (hM : Martingale M ℱ μ) (hL2 : ∀ j, MemLp (M j) 2 μ) (n : ℕ) :
    ∫⁻ ω, ⨆ j ∈ Finset.range (n + 1), ENNReal.ofReal ((M j ω) ^ 2) ∂μ ≤
      4 * ∫⁻ ω, ENNReal.ofReal ((M n ω) ^ 2) ∂μ := by
  classical
  have hsub := doob_abs_submart ℱ M hM hL2
  set S : Ω → ℝ := fun ω => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    (fun k => |M k ω|) with hS
  have hSmeas : Measurable S :=
    Finset.measurable_range_sup'' (f := fun k ω => |M k ω|) (n := n) fun k _ =>
      continuous_abs.measurable.comp ((hM.1 k).measurable.mono (ℱ.le k) le_rfl)
  have hSnn : ∀ ω, 0 ≤ S ω := fun ω =>
    le_trans (abs_nonneg _) (Finset.le_sup' (f := fun k => |M k ω|) (b := 0) (by simp))
  have hnonneg : (0 : ℕ → Ω → ℝ) ≤ (fun j ω => |M j ω|) := fun j ω => abs_nonneg _
  have hint : Integrable (fun ω => |M n ω|) μ := (hsub.integrable n)
  -- weak-type bound
  have hweak : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * μ {ω | t ≤ S ω} ≤
        ∫⁻ ω in {ω | t ≤ S ω}, ENNReal.ofReal |M n ω| ∂μ := by
    intro t ht
    have h := maximal_ineq hsub hnonneg (ε := ⟨t, ht.le⟩) n
    rw [ofReal_integral_eq_lintegral_ofReal hint.integrableOn
      (ae_of_all _ fun ω => abs_nonneg _)] at h
    have hc : ((NNReal.mk t ht.le : NNReal) : ENNReal) = ENNReal.ofReal t := by
      rw [ENNReal.ofReal, Real.toNNReal_of_nonneg ht.le]
    rw [← hc]
    exact h

  have hMn : Measurable (M n) := ((hM.1 n).measurable).mono (ℱ.le n) le_rfl
  -- layer cake for S^2
  have hA1 : ∫⁻ ω, ENNReal.ofReal (S ω ^ 2) ∂μ =
      ∫⁻ t in Set.Ioi 0, μ {ω | t < S ω} * ENNReal.ofReal (2 * t) := by
    have h := lintegral_comp_eq_lintegral_meas_lt_mul (μ := μ) (f := S) (g := fun t => 2 * t)
      (ae_of_all _ hSnn) hSmeas.aemeasurable
      (fun t _ => (by fun_prop : Continuous fun t : ℝ => 2 * t).intervalIntegrable _ _)
      ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => by
        have : (0:ℝ) < t := ht
        linarith)
    rw [← h]
    refine lintegral_congr fun ω => ?_
    congr 1
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  -- Fubini + pointwise Doob bound
  have hkey : ∫⁻ ω, ENNReal.ofReal (S ω ^ 2) ∂μ ≤
      2 * ∫⁻ ω, ENNReal.ofReal |M n ω| * ENNReal.ofReal (S ω) ∂μ := by
    set G : ℝ → Ω → ENNReal := fun t ω =>
      {ω | t ≤ S ω}.indicator (fun ω => ENNReal.ofReal |M n ω|) ω with hGdef
    have hpt : ∀ t : ℝ, 0 < t → μ {ω | t < S ω} * ENNReal.ofReal (2 * t) ≤
        2 * ∫⁻ ω, G t ω ∂μ := by
      intro t ht
      have hmeas : MeasurableSet {ω | t ≤ S ω} := measurableSet_le measurable_const hSmeas
      simp only [hGdef]
      rw [lintegral_indicator hmeas]
      have h1 : μ {ω | t < S ω} ≤ μ {ω | t ≤ S ω} := measure_mono fun ω (h : t < S ω) => le_of_lt h
      have h2 : ENNReal.ofReal (2 * t) = 2 * ENNReal.ofReal t := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      calc μ {ω | t < S ω} * ENNReal.ofReal (2 * t)
          ≤ μ {ω | t ≤ S ω} * (2 * ENNReal.ofReal t) := by
            rw [h2]; gcongr
        _ = 2 * (ENNReal.ofReal t * μ {ω | t ≤ S ω}) := by ring
        _ ≤ 2 * ∫⁻ ω in {ω | t ≤ S ω}, ENNReal.ofReal |M n ω| ∂μ := by
          gcongr; exact hweak t ht
    have hG : Measurable (Function.uncurry G) := by
      have hfun : Function.uncurry G =
          {p : ℝ × Ω | p.1 ≤ S p.2}.indicator (fun p => ENNReal.ofReal |M n p.2|) := by
        funext p
        simp only [Function.uncurry, hGdef, Set.indicator_apply, Set.mem_ofPred_eq]
      rw [hfun]
      exact Measurable.indicator
        (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (hMn.comp measurable_snd)))
        (measurableSet_le measurable_fst (hSmeas.comp measurable_snd))
    have hswap := lintegral_lintegral_swap (μ := volume.restrict (Set.Ioi (0:ℝ))) (ν := μ)
      (f := G) hG.aemeasurable
    have hinner : ∀ ω, ∫⁻ t in Set.Ioi (0:ℝ), G t ω = ENNReal.ofReal |M n ω| * ENNReal.ofReal (S ω) := by
      intro ω
      have hfn : (fun t => G t ω) = (Set.Iic (S ω)).indicator (fun _ => ENNReal.ofReal |M n ω|) := by
        funext t
        simp only [hGdef, Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Iic]
      rw [hfn, lintegral_indicator_const measurableSet_Iic, Measure.restrict_apply measurableSet_Iic,
        Set.Iic_inter_Ioi, Real.volume_Ioc, sub_zero]
    calc ∫⁻ ω, ENNReal.ofReal (S ω ^ 2) ∂μ
        = ∫⁻ t in Set.Ioi 0, μ {ω | t < S ω} * ENNReal.ofReal (2 * t) := hA1
      _ ≤ ∫⁻ t in Set.Ioi 0, 2 * ∫⁻ ω, G t ω ∂μ :=
          setLIntegral_mono' measurableSet_Ioi (fun t ht => hpt t ht)
      _ = 2 * ∫⁻ t in Set.Ioi 0, ∫⁻ ω, G t ω ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofNat_ne_top
      _ = 2 * ∫⁻ ω, (∫⁻ t in Set.Ioi 0, G t ω) ∂μ := by rw [hswap]
      _ = 2 * ∫⁻ ω, ENNReal.ofReal |M n ω| * ENNReal.ofReal (S ω) ∂μ := by
          congr 1
          exact lintegral_congr fun ω => hinner ω
  -- Cauchy-Schwarz
  have e1 : ∀ ω, (ENNReal.ofReal |M n ω|) ^ (2:ℝ) = ENNReal.ofReal (M n ω ^ 2) := fun ω => by
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have e2 : ∀ ω, (ENNReal.ofReal (S ω)) ^ (2:ℝ) = ENNReal.ofReal (S ω ^ 2) := fun ω => by
    rw [ENNReal.rpow_two, ENNReal.ofReal_pow (hSnn ω)]
  have hCS : ∫⁻ ω, ENNReal.ofReal |M n ω| * ENNReal.ofReal (S ω) ∂μ ≤
      (∫⁻ ω, ENNReal.ofReal (M n ω ^ 2) ∂μ) ^ (1 / (2:ℝ)) *
        (∫⁻ ω, ENNReal.ofReal (S ω ^ 2) ∂μ) ^ (1 / (2:ℝ)) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (p := 2) (q := 2) Real.HolderConjugate.two_two
      (f := fun ω => ENNReal.ofReal |M n ω|) (g := fun ω => ENNReal.ofReal (S ω))
      (by fun_prop) (by fun_prop)
    simp only [e1, e2] at h
    exact h
  -- finiteness
  have hBfin : ∫⁻ ω, ENNReal.ofReal (M n ω ^ 2) ∂μ ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hL2 n).integrable_sq
      (ae_of_all _ fun ω => sq_nonneg _)]
    exact ENNReal.ofReal_ne_top
  have hS2 : ∀ ω, S ω ^ 2 ≤ ∑ k ∈ Finset.range (n + 1), M k ω ^ 2 := by
    intro ω
    obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup' (s := Finset.range (n + 1))
      Finset.nonempty_range_add_one (fun k => |M k ω|)
    have hSk : S ω = |M k ω| := hkeq
    rw [hSk, sq_abs]
    exact Finset.single_le_sum (f := fun k => M k ω ^ 2) (fun j _ => sq_nonneg _) hk
  have hsumint : Integrable (fun ω => ∑ k ∈ Finset.range (n + 1), M k ω ^ 2) μ :=
    integrable_finsetSum _ fun k _ => (hL2 k).integrable_sq
  have hAfin : ∫⁻ ω, ENNReal.ofReal (S ω ^ 2) ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (le_trans (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hS2 ω)) le_rfl)
    rw [← ofReal_integral_eq_lintegral_ofReal hsumint
      (ae_of_all _ fun ω => Finset.sum_nonneg fun k _ => sq_nonneg _)]
    exact ENNReal.ofReal_ne_top
  -- pointwise reduction of the left side
  have hLE : ∫⁻ ω, ⨆ j ∈ Finset.range (n + 1), ENNReal.ofReal ((M j ω) ^ 2) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal (S ω ^ 2) ∂μ := by
    refine lintegral_mono fun ω => iSup₂_le fun j hj => ENNReal.ofReal_le_ofReal ?_
    have hjS : |M j ω| ≤ S ω := Finset.le_sup' (fun k => |M k ω|) hj
    rw [← sq_abs (M j ω)]
    exact pow_le_pow_left₀ (abs_nonneg _) hjS 2
  -- algebra
  have hsq : ∀ x : ENNReal, x ≠ ⊤ → x ^ (1 / (2:ℝ)) * x ^ (1 / (2:ℝ)) = x := by
    intro x hx
    rcases eq_or_ne x 0 with rfl | h0
    · simp
    · rw [← ENNReal.rpow_add _ _ h0 hx]; norm_num
  refine hLE.trans ?_
  set A := ∫⁻ ω, ENNReal.ofReal (S ω ^ 2) ∂μ with hAdef
  set B := ∫⁻ ω, ENNReal.ofReal (M n ω ^ 2) ∂μ with hBdef
  set X := B ^ (1 / (2:ℝ)) with hXdef
  set Y := A ^ (1 / (2:ℝ)) with hYdef
  have hA0 : A = 0 ∨ A ≠ 0 := eq_or_ne A 0
  rcases hA0 with hA0 | hA0
  · rw [hA0]; exact zero_le
  have hY0 : Y ≠ 0 := by
    rw [hYdef]; exact (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.mpr hA0) (by norm_num)).ne'
  have hYt : Y ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hAfin
  have hYY : Y * Y = A := hsq A hAfin
  have hXX : X * X = B := hsq B hBfin
  have hmain : A ≤ 2 * (X * Y) := by
    calc A ≤ 2 * ∫⁻ ω, ENNReal.ofReal |M n ω| * ENNReal.ofReal (S ω) ∂μ := hkey
      _ ≤ 2 * (X * Y) := by gcongr
  have hY2 : Y ≤ 2 * X := by
    have h3 : Y * Y ≤ Y * (2 * X) := by
      calc Y * Y = A := hYY
        _ ≤ 2 * (X * Y) := hmain
        _ = Y * (2 * X) := by ring
    exact (ENNReal.mul_le_mul_iff_right hY0 hYt).mp h3
  calc A = Y * Y := hYY.symm
    _ ≤ (2 * X) * (2 * X) := mul_le_mul' hY2 hY2
    _ = 4 * (X * X) := by ring
    _ = 4 * B := by rw [hXX]

end ProbabilityFoundations
