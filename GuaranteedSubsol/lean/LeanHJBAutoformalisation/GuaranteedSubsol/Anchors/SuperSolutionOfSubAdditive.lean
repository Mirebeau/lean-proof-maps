/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.PertSubSuperProof

/-!
# Frozen statement: perturbation into a super-solution

Source: Prop. prop:pertSubSuper (Complexity.tex), super-solution part, in scalar form at a point
`x`: if `Λ` is `ρ`-sub-additive with `ρ < 1`, `c ≥ 0` and `Λ u ≤ u x + c`, then
`u̲ := u + c/(1-ρ)` satisfies `Λ u̲ ≤ u̲ x`. The scalar operator `Λ : (X → ℝ) → ℝ` stands for
`(Λ · x)`; the paper's global statement follows by applying this at every point.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem superSolution_of_subAdditive {X : Type*} {Λ : (X → ℝ) → ℝ} {ρ : ℝ} (hρ : ρ < 1)
    (hsub : SubAdditive ρ Λ) {u : X → ℝ} {x : X} {c : ℝ} (hc : 0 ≤ c) (hu : Λ u ≤ u x + c) :
    Λ (fun y => u y + c / (1 - ρ)) ≤ u x + c / (1 - ρ) := by
  exact PertSubSuperProof.superSolution_of_subAdditive hρ hsub hc hu

end GuaranteedSubsol
