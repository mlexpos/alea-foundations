# Alea foundations

Lean 4 libraries supporting the formalization of *Phases of Muon: When Muon
Eclipses SignSGD*.

The repository contains four Lake packages:

- `probability-foundations/`
- `gaussian-foundations/`
- `spectral-foundations/`
- `matrix-concentration/`

Each package uses Lean 4 and Mathlib v4.34.1. Build a package from its own
directory; for example:

```sh
cd gaussian-foundations
lake update
lake exe cache get
lake build
```

The two concentration packages use a v4.34.1 port of
[`lean-stat-learning-theory`](https://github.com/YuanheZ/lean-stat-learning-theory),
included under `vendor/slt/`. That vendored component retains its Apache-2.0
license in `vendor/slt/LICENSE`.
