/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.TolProof

/-!
# Frozen statement: rescaling into a super-solution, sub-multiplicative case

Analogue of Prop. prop:pertSubSuper with sub-multiplicativity in place of sub-additivity, from the
proof of Corol. corol:tol (Complexity.tex, second point): if `Λ` is `ν`-sub-multiplicative,
`0 ≤ ε < ν` and `Λ u ≤ u x + ε`, then `(1 + η) u` with `η := ε / (ν - ε)`, i.e.
`ν / (ν - ε) • u`, satisfies the super-solution inequality at `x`. Scalar form:
`Λ : (X → ℝ) → ℝ` stands for `(Λ · x)`.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem superSolution_of_subMultiplicative {X : Type*} {Λ : (X → ℝ) → ℝ} {ν : ℝ}
    (hmul : SubMultiplicative ν Λ) {u : X → ℝ} {x : X} {ε : ℝ} (hε : 0 ≤ ε) (hεν : ε < ν)
    (hu : Λ u ≤ u x + ε) :
    Λ (fun y => ν / (ν - ε) * u y) ≤ ν / (ν - ε) * u x := by
  exact TolProof.superSolution_of_subMultiplicative hmul hε hεν hu

end GuaranteedSubsol
