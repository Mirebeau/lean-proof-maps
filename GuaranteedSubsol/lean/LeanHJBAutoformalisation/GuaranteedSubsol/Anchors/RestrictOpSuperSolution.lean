/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.RestrictionProof

/-!
# Frozen statement: partial application preserves super-solutions

Source: Prop. prop:partialMonotone (Complexity.tex): if `Λ` is monotone and `Λ u ≤ u`, then
`u' := Λ_B u` satisfies `Λ u' ≤ u'`.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem restrictOp_superSolution {X : Type*} {Λ : (X → ℝ) → X → ℝ} (hΛ : Monotone Λ)
    (B : Set X) {u : X → ℝ} (hu : Λ u ≤ u) :
    Λ (restrictOp Λ B u) ≤ restrictOp Λ B u := by
  exact RestrictionProof.restrictOp_superSolution hΛ B hu

end GuaranteedSubsol
