import Mathlib

/-!
# Freezing lemma and entrywise matrix conditional expectation

The freezing lemma (`X` 𝒢-measurable, `Y` independent of 𝒢 ⇒ `E[f(X,Y) | 𝒢] = g(X)` with
`g(x) = E f(x,Y)`) and the entrywise matrix conditional expectation `condExpMat`
(expectations of matrices are entrywise).

Relocated from Muon `Foundations/Freezing`; statements unchanged in content. Muon's `Mat m n` is
written `Matrix (Fin m) (Fin n) ℝ`, and Muon's entrywise mean `Muon.mean P X` is written out as
`Matrix.of fun i j => ∫ ω, X ω i j ∂P` (definitionally equal, so the Muon wrappers close by `exact`).

Mathlib reuse: `MeasureTheory.condExp`, `MeasureTheory.condExp_indep_eq`,
`MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq`, `ProbabilityTheory.indep_of_indep_of_le_left`.
Mathlib has no freezing lemma in this form (only the `condDistrib` representation
`condExp_prod_ae_eq_integral_condDistrib`, which conditions on `X` rather than on 𝒢).
-/

open scoped Matrix MatrixOrder
open MeasureTheory ProbabilityTheory

noncomputable section

namespace ProbabilityFoundations

variable {Ω α β : Type*}

/-! ## Entrywise matrix conditional expectation -/

/-- Entrywise conditional expectation `E[X | 𝒢]` of a random matrix `X : Ω → Matrix (Fin m) (Fin n) ℝ`: the
`(i, j)` entry is the scalar conditional expectation of `X_{ij}`. The result is a random matrix
(defined almost everywhere, as `condExp` is). -/
def condExpMat {m n : ℕ} (𝒢 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    (X : Ω → Matrix (Fin m) (Fin n) ℝ) : Ω → Matrix (Fin m) (Fin n) ℝ :=
  fun ω => Matrix.of fun i j => condExp 𝒢 μ (fun ω' => X ω' i j) ω

/-- Entrywise reading of `condExpMat`. -/
theorem condExpMat_apply {m n : ℕ} (𝒢 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) (X : Ω → Matrix (Fin m) (Fin n) ℝ) (ω : Ω) (i : Fin m) (j : Fin n) :
    condExpMat 𝒢 μ X ω i j = condExp 𝒢 μ (fun ω' => X ω' i j) ω :=
  rfl

/-- `condExpMat` respects almost-everywhere equality of matrix-valued random variables. -/
theorem condExpMat_congr_ae {m n : ℕ} (𝒢 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {X X' : Ω → Matrix (Fin m) (Fin n) ℝ} (h : X =ᵐ[μ] X') :
    condExpMat 𝒢 μ X =ᵐ[μ] condExpMat 𝒢 μ X' := by
  have hents : ∀ i j, ∀ᵐ ω ∂μ,
      condExp 𝒢 μ (fun ω' => X ω' i j) ω = condExp 𝒢 μ (fun ω' => X' ω' i j) ω := by
    intro i j
    exact condExp_congr_ae (h.mono fun ω hω => by simp only [hω])
  have hall : ∀ᵐ ω ∂μ, ∀ i j,
      condExp 𝒢 μ (fun ω' => X ω' i j) ω = condExp 𝒢 μ (fun ω' => X' ω' i j) ω :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun j => hents i j
  filter_upwards [hall] with ω hω
  ext i j
  change condExp 𝒢 μ (fun ω' => X ω' i j) ω = condExp 𝒢 μ (fun ω' => X' ω' i j) ω
  exact hω i j

/-- Independence: if the entries of `X` are measurable for a σ-algebra `𝒢'` independent of
𝒢, then `E[X | 𝒢]` is almost everywhere the entrywise mean `Matrix.of fun i j => ∫ ω, X ω i j ∂μ`. -/
theorem condExpMat_indep_eq {m n : ℕ} (𝒢 𝒢' : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h𝒢 : 𝒢 ≤ mΩ) (h𝒢' : 𝒢' ≤ mΩ)
    {X : Ω → Matrix (Fin m) (Fin n) ℝ} (hX : ∀ i j, Measurable[𝒢'] fun ω => X ω i j)
    (hind : Indep 𝒢' 𝒢 μ) :
    condExpMat 𝒢 μ X =ᵐ[μ] fun _ => Matrix.of fun i j => ∫ ω, X ω i j ∂μ := by
  have hents : ∀ i j, ∀ᵐ ω ∂μ,
      condExp 𝒢 μ (fun ω' => X ω' i j) ω = ∫ ω', X ω' i j ∂μ :=
    fun i j => condExp_indep_eq h𝒢' h𝒢 (hX i j).stronglyMeasurable hind
  have hall : ∀ᵐ ω ∂μ, ∀ i j,
      condExp 𝒢 μ (fun ω' => X ω' i j) ω = ∫ ω', X ω' i j ∂μ :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun j => hents i j
  filter_upwards [hall] with ω hω
  ext i j
  change condExp 𝒢 μ (fun ω' => X ω' i j) ω = ∫ ω', X ω' i j ∂μ
  exact hω i j

/-! ## Freezing lemma -/

/-- Joint law of `(X, Y)` restricted to a 𝒢-measurable set `s`: the restricted law of `X`
times the law of `Y`. -/
private theorem freezing_joint_restrict (𝒢 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    (h𝒢 : 𝒢 ≤ mΩ) {X : Ω → α} {Y : Ω → β} (hX : Measurable[𝒢] X) (hY : Measurable Y)
    (hind : Indep 𝒢 (MeasurableSpace.comap Y mβ) μ) {s : Set Ω} (hs : MeasurableSet[𝒢] s) :
    (μ.restrict s).map (fun ω => (X ω, Y ω)) = ((μ.restrict s).map X).prod (μ.map Y) := by
  have hXm : Measurable X := hX.mono h𝒢 le_rfl
  have hs' : MeasurableSet s := h𝒢 _ hs
  symm
  apply Measure.prod_eq
  intro A B hA hB
  have hYB : MeasurableSet (Y ⁻¹' B) := hY hB
  have hYB' : MeasurableSet[MeasurableSpace.comap Y mβ] (Y ⁻¹' B) :=
    MeasurableSpace.measurableSet_comap.2 ⟨B, hB, rfl⟩
  have hXA : MeasurableSet[𝒢] (X ⁻¹' A) := hX hA
  have hI := (Indep_iff _ _ μ).1 hind
  rw [Measure.map_apply hXm hA, Measure.map_apply hY hB,
    Measure.map_apply (hXm.prodMk hY) (hA.prod hB), Set.mk_preimage_prod,
    Measure.restrict_apply ((hXm hA).inter (hY hB)), Measure.restrict_apply (hXm hA),
    Set.inter_right_comm]
  exact hI _ _ (hXA.inter hs) hYB'

/-- Conditional expectation of a function of `(X, Y)` against a 𝒢-measurable set, freezing
form. -/
private theorem freezing_setIntegral (𝒢 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    (h𝒢 : 𝒢 ≤ mΩ) {X : Ω → α} {Y : Ω → β} (hX : Measurable[𝒢] X) (hY : Measurable Y)
    (hind : Indep 𝒢 (MeasurableSpace.comap Y mβ) μ)
    {f : α → β → ℝ} (hf : Measurable (Function.uncurry f))
    (hfint : Integrable (fun ω => f (X ω) (Y ω)) μ) {s : Set Ω} (hs : MeasurableSet[𝒢] s) :
    ∫ ω in s, f (X ω) (Y ω) ∂μ = ∫ ω in s, ∫ y, f (X ω) y ∂(μ.map Y) ∂μ := by
  have hXm : Measurable X := hX.mono h𝒢 le_rfl
  have hpair : Measurable (fun ω => (X ω, Y ω)) := hXm.prodMk hY
  have hgm : Measurable (fun x => ∫ y, f x y ∂(μ.map Y)) :=
    (hf.stronglyMeasurable.integral_prod_right' (ν := μ.map Y)).measurable
  have hkey := freezing_joint_restrict 𝒢 h𝒢 hX hY hind hs
  have hFs : Integrable (fun ω => f (X ω) (Y ω)) (μ.restrict s) := hfint.restrict
  have hint : Integrable (Function.uncurry f) (((μ.restrict s).map X).prod (μ.map Y)) := by
    rw [← hkey]
    exact (integrable_map_measure hf.aestronglyMeasurable hpair.aemeasurable).2 hFs
  calc ∫ ω in s, f (X ω) (Y ω) ∂μ
      = ∫ p, Function.uncurry f p ∂((μ.restrict s).map (fun ω => (X ω, Y ω))) := by
        rw [integral_map hpair.aemeasurable hf.aestronglyMeasurable]
        rfl
    _ = ∫ p, Function.uncurry f p ∂(((μ.restrict s).map X).prod (μ.map Y)) := by rw [hkey]
    _ = ∫ x, ∫ y, f x y ∂(μ.map Y) ∂((μ.restrict s).map X) := integral_prod _ hint
    _ = ∫ ω in s, ∫ y, f (X ω) y ∂(μ.map Y) ∂μ := by
        rw [integral_map hXm.aemeasurable hgm.aestronglyMeasurable]

/-- Freezing lemma, scalar form. Let `X` be 𝒢-measurable and `Y` independent of 𝒢, and let
`f(x, y)` be jointly measurable with `f(X, Y)` integrable. Then `E[f(X,Y) | 𝒢]` equals, almost
everywhere, `ω ↦ ∫ f(X ω, y) dP_Y(y)`, where `P_Y = μ.map Y` is the law of `Y`. -/
theorem freezing_condExp (𝒢 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] [mα : MeasurableSpace α] [mβ : MeasurableSpace β] (h𝒢 : 𝒢 ≤ mΩ)
    {X : Ω → α} {Y : Ω → β} (hX : Measurable[𝒢] X) (hY : Measurable Y)
    (hind : Indep 𝒢 (MeasurableSpace.comap Y mβ) μ)
    {f : α → β → ℝ} (hf : Measurable (Function.uncurry f))
    (hfint : Integrable (fun ω => f (X ω) (Y ω)) μ) :
    condExp 𝒢 μ (fun ω => f (X ω) (Y ω)) =ᵐ[μ] fun ω => ∫ y, f (X ω) y ∂(μ.map Y) := by
  have hXm : Measurable X := hX.mono h𝒢 le_rfl
  have hpair : Measurable (fun ω => (X ω, Y ω)) := hXm.prodMk hY
  have hgm : Measurable (fun x => ∫ y, f x y ∂(μ.map Y)) :=
    (hf.stronglyMeasurable.integral_prod_right' (ν := μ.map Y)).measurable
  have hGm : Measurable[𝒢] (fun ω => ∫ y, f (X ω) y ∂(μ.map Y)) := hgm.comp hX
  -- joint law of (X, Y) on the whole space: product of the marginals
  have huniv := freezing_joint_restrict 𝒢 h𝒢 hX hY hind MeasurableSet.univ
  rw [Measure.restrict_univ] at huniv
  have hint : Integrable (Function.uncurry f) ((μ.map X).prod (μ.map Y)) := by
    rw [← huniv]
    exact (integrable_map_measure hf.aestronglyMeasurable hpair.aemeasurable).2 hfint
  have hGint : Integrable (fun ω => ∫ y, f (X ω) y ∂(μ.map Y)) μ := by
    have h1 := hint.integral_prod_left
    exact (integrable_map_measure hgm.aestronglyMeasurable hXm.aemeasurable).1 h1
  refine (ae_eq_condExp_of_forall_setIntegral_eq h𝒢 hfint
    (fun s _ _ => hGint.integrableOn) (fun s hs _ => ?_)
      hGm.stronglyMeasurable.aestronglyMeasurable).symm
  exact (freezing_setIntegral 𝒢 h𝒢 hX hY hind hf hfint hs).symm

/-- Freezing lemma, matrix form. The entrywise version of `freezing_condExp`: for a family
`F x y : Matrix (Fin m) (Fin n) ℝ` with jointly measurable entries and integrable `F(X,Y)` entries, the entrywise
conditional expectation `condExpMat 𝒢 μ (F(X,Y))` is almost everywhere the entrywise mean
the matrix of entries `∫ y, F (X ω) y i j ∂(μ.map Y)` of `y ↦ F (X ω) y` under the law of `Y`. -/
theorem freezing_condExpMat {m n : ℕ} (𝒢 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    (h𝒢 : 𝒢 ≤ mΩ)
    {X : Ω → α} {Y : Ω → β} (hX : Measurable[𝒢] X) (hY : Measurable Y)
    (hind : Indep 𝒢 (MeasurableSpace.comap Y mβ) μ)
    {F : α → β → Matrix (Fin m) (Fin n) ℝ} (hF : ∀ i j, Measurable (Function.uncurry fun x y => F x y i j))
    (hfint : ∀ i j, Integrable (fun ω => F (X ω) (Y ω) i j) μ) :
    condExpMat 𝒢 μ (fun ω => F (X ω) (Y ω)) =ᵐ[μ]
      fun ω => Matrix.of fun i j => ∫ y, F (X ω) y i j ∂(μ.map Y) := by
  have hents : ∀ i j, ∀ᵐ ω ∂μ,
      condExp 𝒢 μ (fun ω' => F (X ω') (Y ω') i j) ω = ∫ y, F (X ω) y i j ∂(μ.map Y) :=
    fun i j => freezing_condExp 𝒢 h𝒢 hX hY hind (hF i j) (hfint i j)
  have hall : ∀ᵐ ω ∂μ, ∀ i j,
      condExp 𝒢 μ (fun ω' => F (X ω') (Y ω') i j) ω = ∫ y, F (X ω) y i j ∂(μ.map Y) :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun j => hents i j
  filter_upwards [hall] with ω hω
  ext i j
  change condExp 𝒢 μ (fun ω' => F (X ω') (Y ω') i j) ω = ∫ y, F (X ω) y i j ∂(μ.map Y)
  exact hω i j

end ProbabilityFoundations

end
