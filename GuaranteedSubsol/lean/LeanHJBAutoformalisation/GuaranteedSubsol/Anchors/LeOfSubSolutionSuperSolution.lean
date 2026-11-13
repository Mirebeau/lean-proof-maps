/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.ComparisonLambdaProof

/-!
# Frozen statement: comparison of a sub-solution with a super-solution

Source: Prop. prop:comparison_Lambda (Complexity.tex), eq. eq:comparison_Lambda, in the sub- vs.
super-solution form of the paper: if `Λ` is
monotone and `Φ_α` is `ρ`-sub-additive with `α > 0`, `ρ < 1`, then for any partition
`X = Int Y ⊔ ∂Y`, `(u ≤ Λ u and Λ v ≤ v on Int Y, u ≤ v on ∂Y) ⇒ u ≤ v`.

`Int Y` is the set `I`, `∂Y` its complement, and `Φ_α` at `x` is `kruzkovOp α (Λ · x)`.
Monotonicity and sub-additivity are only assumed at the points of `I`.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem le_of_subSolution_superSolution {X : Type*} [Finite X] {Λ : (X → ℝ) → X → ℝ}
    {α ρ : ℝ} (hα : 0 < α) (hρ : ρ < 1) {I : Set X} (hmono : ∀ x ∈ I, Monotone (Λ · x))
    (hsub : ∀ x ∈ I, SubAdditive ρ (kruzkovOp α (Λ · x))) {u v : X → ℝ}
    (hu : ∀ x ∈ I, u x ≤ Λ u x) (hv : ∀ x ∈ I, Λ v x ≤ v x) (hbd : ∀ x ∉ I, u x ≤ v x) :
    u ≤ v := by
  exact ComparisonLambdaProof.le_of_subSolution_superSolution hα hρ hmono hsub hu hv hbd

end GuaranteedSubsol
