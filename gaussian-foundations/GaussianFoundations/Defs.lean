import Mathlib

/-!
# Shared definitions

Verbatim copies of the definitions in `Muon.External.Certificates` (muon/lean), so that the theorems of
this package have exactly the statements of the Muon certificates and discharge them by unfolding.
-/

namespace GaussianFoundations

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Operator norm of a real `p × q` matrix, as the operator norm of the induced linear map
`EuclideanSpace ℝ (Fin q) → EuclideanSpace ℝ (Fin p)`. -/
noncomputable def matOpNorm {p q : ℕ} (Y : Matrix (Fin p) (Fin q) ℝ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Y)‖

/-- Frobenius norm `‖F‖_F = (∑ᵢⱼ |Fᵢⱼ|²)^{1/2}` of a real square matrix. -/
noncomputable def frobNorm {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, F i j ^ 2)

/-- `Y` is an i.i.d. `N(0,1)` matrix under `μ`: the law of its entries, vectorised, is the
product of `p * q` copies of `gaussianReal 0 1`. -/
def IsIIDGaussianMatrix {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {p q : ℕ}
    (Y : Ω → Matrix (Fin p) (Fin q) ℝ) : Prop :=
  μ.map (fun ω (ij : Fin p × Fin q) => Y ω ij.1 ij.2) =
    Measure.pi (fun _ : Fin p × Fin q => gaussianReal 0 1)

/-- `z` is a standard Gaussian vector `N(0, Id_n)` under `μ`: its law is the product of `n`
copies of `gaussianReal 0 1`. -/
def IsStdGaussianVector {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {n : ℕ}
    (z : Ω → Fin n → ℝ) : Prop :=
  μ.map z = Measure.pi (fun _ : Fin n => gaussianReal 0 1)

end GaussianFoundations
