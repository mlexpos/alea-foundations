import GaussianFoundations.Defs
import GaussianFoundations.OpNorm
import GaussianFoundations.QuadFormLp
import GaussianFoundations.Poincare
import GaussianFoundations.IBP
import GaussianFoundations.GaussianMatrix
import GaussianFoundations.Moments
import GaussianFoundations.Combinatorics
import GaussianFoundations.Rotation
import GaussianFoundations.OrthHaar
import GaussianFoundations.Sphere
open Lean in
#eval show Lean.Elab.Command.CommandElabM Unit from do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let mut n := 0
  for (nm, ci) in env.constants.toList do
    if nm.getRoot == `GaussianFoundations && !nm.isInternal then
      if ci matches .thmInfo _ then
        n := n + 1
        let axs ← Lean.collectAxioms nm
        if axs.any (fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound) then
          bad := bad.push nm
  logInfo m!"theorems checked: {n}; nonstandard-axiom theorems: {bad}"
