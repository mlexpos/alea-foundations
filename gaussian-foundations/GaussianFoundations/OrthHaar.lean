import Mathlib
import GaussianFoundations.Rotation

/-!
# Foundations: Haar probability measures on `O(n)` (task L-I.0b)

Ruling (coordinator, 2026-10-24, Q1 option (b)): downstream statements take a probability
measure `ν` on `O(n)` together with the hypothesis `IsOrthHaar ν`, which says that `ν` is a
probability measure invariant under left and right translation. Existence of such a measure is
stated separately (`orthHaar_exists`), and the constructed instance `haarO` from
`GaussianFoundations.Rotation` is shown to satisfy the predicate (`haarO_isOrthHaar`), so the
hypothesis is not vacuous.

Statement only (`sorry`) except for the definition. Proof routes are in
`muon/phases-of-muon/appendix-nodes/results/L-I.0b-interface.json`.

Reused, not restated: `Matrix.orthogonalGroup`, its compactness instance
`orthogonalGroup_compactSpace_inst` and the constructed Haar probability `haarO`, all from
`GaussianFoundations.Rotation`.
-/

open MeasureTheory

namespace GaussianFoundations

/-- `IsOrthHaar ν`: `ν` is a probability measure on `O(n)` that is invariant under left and
right translation by every orthogonal matrix. (task L-I.0b; no paper label; snapshot
cr-2026-10-23). Consumer: Appendix I, `def:app-sgd-state-law` (the Haar state law, l. 605–618),
through the sphere and sign lemmas of `GaussianFoundations.Sphere`. -/
def IsOrthHaar {n : ℕ} (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)) : Prop :=
  IsProbabilityMeasure ν ∧
    (∀ g : Matrix.orthogonalGroup (Fin n) ℝ, ν.map (fun h => g * h) = ν) ∧
    (∀ g : Matrix.orthogonalGroup (Fin n) ℝ, ν.map (fun h => h * g) = ν)

/-- Private re-proof (of `haarO_map_mul_right_eq_self` in `GaussianExtra`, which is private
there): right translation by `g` fixes `haarO n`. The modular character is `1` since both sides
are probability measures. -/
private lemma haarO_map_mul_right_eq_self' (n : ℕ) (g : Matrix.orthogonalGroup (Fin n) ℝ) :
    (haarO n).map (fun h => h * g) = haarO n := by
  have hH : (haarO n).IsHaarMeasure := by
    unfold haarO
    infer_instance
  have h := Measure.map_right_mul_eq_modularCharacterFun_smul (haarO n) g
  have hu := congrArg (fun m : Measure (Matrix.orthogonalGroup (Fin n) ℝ) => m Set.univ) h
  simp only [Measure.map_apply (continuous_mul_const g).measurable MeasurableSet.univ,
    Set.preimage_univ, Measure.smul_apply, ENNReal.smul_def, measure_univ] at hu
  have hc : Measure.modularCharacterFun g = 1 := by
    have h1 : ((Measure.modularCharacterFun g : NNReal) : ENNReal) = 1 := by
      simpa using hu.symm
    exact_mod_cast h1
  rw [hc, one_smul] at h
  exact h

/-- The constructed Haar probability `haarO n` satisfies `IsOrthHaar`. -/
private lemma haarO_isOrthHaar_aux (n : ℕ) : IsOrthHaar (haarO n) :=
  ⟨inferInstance, fun g => map_mul_left_eq_self (haarO n) g,
    fun g => haarO_map_mul_right_eq_self' n g⟩

/-- Existence of a Haar probability measure on `O(n)`: some probability measure on `O(n)` is
left and right invariant. (task L-I.0b; no paper label; snapshot cr-2026-10-23). Consumer:
non-vacuity of the hypothesis `IsOrthHaar ν` in Appendix I, `def:app-sgd-state-law`. Proof to
come (the witness `haarO n` from `GaussianExtra` is available; see `haarO_isOrthHaar`). -/
theorem orthHaar_exists (n : ℕ) :
    ∃ ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ), IsOrthHaar ν :=
  ⟨haarO n, haarO_isOrthHaar_aux n⟩

/-- Uniqueness of the Haar probability measure on `O(n)`: two left- and right-invariant
probability measures on `O(n)` coincide. (task L-I.0b; no paper label; snapshot
cr-2026-10-23). Consumer: `orthHaar_map_mulVec_eq_sphereGauss` and the Haar sign lemmas of
Appendix I (l. 614, 718–719, 1130), which are stated for an arbitrary `ν` with `IsOrthHaar ν`. -/
theorem isOrthHaar_unique {n : ℕ} {ν ν' : Measure (Matrix.orthogonalGroup (Fin n) ℝ)}
    (hν : IsOrthHaar ν) (hν' : IsOrthHaar ν') : ν = ν' := by
  obtain ⟨hP, hL, _⟩ := hν
  obtain ⟨hP', hL', _⟩ := hν'
  have : IsProbabilityMeasure ν := hP
  have : IsProbabilityMeasure ν' := hP'
  have : ν.IsMulLeftInvariant := ⟨hL⟩
  have : ν'.IsMulLeftInvariant := ⟨hL'⟩
  have : ν.IsOpenPosMeasure :=
    isOpenPosMeasure_of_mulLeftInvariant_of_compact Set.univ isCompact_univ
      (by simp [measure_univ])
  have : ν'.IsOpenPosMeasure :=
    isOpenPosMeasure_of_mulLeftInvariant_of_compact Set.univ isCompact_univ
      (by simp [measure_univ])
  have : ν.IsHaarMeasure := {}
  have : ν'.IsHaarMeasure := {}
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure ν ν'

/-- The constructed Haar probability `haarO n` of `GaussianExtra` satisfies `IsOrthHaar`. Shows
that the hypothesis of `IsOrthHaar` is satisfiable. (task L-I.0b; no paper label; snapshot
cr-2026-10-23). Consumer: as for `orthHaar_exists`. -/
theorem haarO_isOrthHaar (n : ℕ) : IsOrthHaar (haarO n) :=
  haarO_isOrthHaar_aux n

end GaussianFoundations
