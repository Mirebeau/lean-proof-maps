/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.TolProof

/-!
# Frozen statement: rescaling into a sub-solution, sub-multiplicative case

Analogue of Prop. prop:pertSubSuper with sub-multiplicativity in place of sub-additivity, from the
proof of Corol. corol:tol (Complexity.tex, second point): if `Λ` is `ν`-sub-multiplicative with
`ν > 0`, `ε ≥ 0` and `u x - ε ≤ Λ u`, then `(1 - η) u` with `η := ε / (ν + ε)`, i.e.
`ν / (ν + ε) • u`, satisfies the sub-solution inequality at `x`. Scalar form: `Λ : (X → ℝ) → ℝ`
stands for `(Λ · x)`.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem subSolution_of_subMultiplicative {X : Type*} {Λ : (X → ℝ) → ℝ} {ν : ℝ} (hν : 0 < ν)
    (hmul : SubMultiplicative ν Λ) {u : X → ℝ} {x : X} {ε : ℝ} (hε : 0 ≤ ε)
    (hu : u x - ε ≤ Λ u) :
    ν / (ν + ε) * u x ≤ Λ (fun y => ν / (ν + ε) * u y) := by
  exact TolProof.subSolution_of_subMultiplicative hν hmul hε hu

end GuaranteedSubsol
