/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ComparisonLambdaProof

/-!
# Frozen statement: unique fixed point of `Λ`, below any super-solution

Source: Prop. prop:comparison_Lambda (Complexity.tex), second part: if `Λ` is monotone, `Φ_α` is
`ρ`-sub-additive with `α > 0`, `ρ < 1`, and `Λ u̲ ≤ u̲` for some `u̲`, then `Λ` admits a unique
fixed point `u_*`, and `u_* ≤ u̲`. `Φ_α` at `x` is `kruzkovOp α (Λ · x)`; the fixed point is shared
by the three conclusions.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem existsUnique_fixedPoint_of_kruzkov {X : Type*} [Finite X] {Λ : (X → ℝ) → X → ℝ}
    {α ρ : ℝ} (hα : 0 < α) (hρ : ρ < 1) (hmono : ∀ x, Monotone (Λ · x))
    (hsub : ∀ x, SubAdditive ρ (kruzkovOp α (Λ · x))) {uSup : X → ℝ} (huSup : Λ uSup ≤ uSup) :
    ∃ uFix : X → ℝ, Λ uFix = uFix ∧ (∀ w, Λ w = w → w = uFix) ∧ uFix ≤ uSup := by
  exact ComparisonLambdaProof.existsUnique_fixedPoint_of_kruzkov hα hρ hmono hsub huSup

end GuaranteedSubsol
