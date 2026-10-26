# Relocation map: `Muon.Foundations.*` -> `ProbabilityFoundations.*`

Statements unchanged in mathematical content. `Mat m n` is written `Matrix (Fin m) (Fin n) ℝ`; indices stay `Fin`. `Muon.mean P X` is written out as `Matrix.of fun i j => ∫ ω, X ω i j ∂P` (defeq).

## `Muon/Foundations/Freezing.lean` -> `ProbabilityFoundations/Freezing.lean`

| Muon.Foundations name | ProbabilityFoundations name | Note |
|---|---|---|
| `condExpMat` | `condExpMat` | retyped |
| `condExpMat_apply` | `condExpMat_apply` | retyped |
| `condExpMat_congr_ae` | `condExpMat_congr_ae` | retyped |
| `condExpMat_indep_eq` | `condExpMat_indep_eq` | RHS `Muon.mean μ X` unfolded |
| `freezing_condExp` | `freezing_condExp` | unchanged |
| `freezing_condExpMat` | `freezing_condExpMat` | retyped; RHS `Muon.mean (μ.map Y) (F (X ω))` unfolded |
