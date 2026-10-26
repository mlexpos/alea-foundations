# Relocation map: `Muon.Foundations.*` -> `SpectralFoundations.*`

Statements unchanged in mathematical content. `Mat m n` is written `Matrix (Fin m) (Fin n) ℝ`, `Vec m` as `Fin m → ℝ`.

## `Muon/Foundations/SVD.lean` -> `SpectralFoundations/SVD.lean`

| Muon.Foundations name | SpectralFoundations name | Note |
|---|---|---|
| `rank_eq_finrank_range_toEuclideanLin` | `rank_eq_finrank_range_toEuclideanLin` | retyped (`Mat` unfolded) |
| `singularValues_pos_of_lt_rank` | `singularValues_pos_of_lt_rank` | retyped |
| `svd_rect_exists` | `svd_rect_exists` | retyped; `outer` unfolded to `Matrix.vecMulVec`, `Vec` to `Fin m → ℝ` |
| `cfc_intertwine_rect` | `cfc_intertwine_rect` | retyped; now carries the proof of `Muon.cfc_mul_transpose_mul_intertwine` (copied from Muon `Conventions`, which stays in Muon) |

## `Muon/Foundations/OperatorLipschitz.lean` -> `SpectralFoundations/OperatorLipschitz.lean`

`fro` is a local definition with Muon's exact body (`Real.sqrt (∑ i, ∑ j, ‖K i j‖ ^ 2)`, generic over `RCLike`), so `Muon.fro` is defeq to `SpectralFoundations.fro` (wrappers close by `exact`/`unfold`).

| Muon.Foundations name | SpectralFoundations name | Note |
|---|---|---|
| `Muon.fro` (Conventions; new copy) | `fro` | new local def, same body |
| `hermDilation` | `hermDilation` | retyped |
| `upperRight` | `upperRight` | retyped |
| `hermDilation_isHermitian` | `hermDilation_isHermitian` | retyped |
| `fro_hermDilation` | `fro_hermDilation` | retyped |
| `fro_upperRight_sq_le` | `fro_upperRight_sq_le` | retyped |
| `upperRight_cfc_hermDilation` | `upperRight_cfc_hermDilation` | RHS `Q ϱ K` written out as `K * cfc (fun x => (x + ϱ) ^ (-(1/2))) (Kᵀ * K)` (defeq by unfolding `Muon.Q`) |
| `lipschitz_filter_fun` | `lipschitz_filter_fun` | unchanged |
| `fro_cfc_sub_cfc_le` | `fro_cfc_sub_cfc_le` | retyped |
| private `fro_sq_aux` | `fro_sq_eq_sum` | now public, renamed |
| private `fro_nonneg_aux` | `fro_nonneg` | now public, renamed |
| private `hermDilation_sub_aux` | `hermDilation_sub` | now public, renamed |
| private `upperRight_sub_aux` | `upperRight_sub` | now public, renamed |
| private `herm_cfc_isHerm_aux` | `isHermitian_cfc` | now public, renamed (needed by Muon's `fro_Q_sub_Q_le`) |
| `fro_Q_sub_Q_le` | (stays in Muon) | Q-specific; will cite `fro_cfc_sub_cfc_le`, `lipschitz_filter_fun`, `upperRight_cfc_hermDilation` |
