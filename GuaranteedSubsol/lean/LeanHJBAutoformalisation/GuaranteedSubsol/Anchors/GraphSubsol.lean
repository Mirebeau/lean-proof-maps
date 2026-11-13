/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.GraphSubsolProof

/-!
# Frozen statement: extension of a sub-solution by a graph operator

Source: Lemma lem:graph_subsol (Complexity.tex): let `Λ, Γ : ℝ^X → ℝ^X` with `Λ` monotone and
`Γ ≤ Λ`. If `ū ≤ Λ ū` and `û = max {ū, Γ û}`, then `û ≤ Λ û`. Global operators
`(X → ℝ) → X → ℝ`, with the pointwise order on `X → ℝ` and on operators.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem subsol_extension {X : Type*} {Λ Γ : (X → ℝ) → X → ℝ} (hmono : Monotone Λ)
    (hΓ : Γ ≤ Λ) {uSub uHat : X → ℝ} (hsub : uSub ≤ Λ uSub)
    (hhat : uHat = fun x => max (uSub x) (Γ uHat x)) :
    uHat ≤ Λ uHat := by
  exact GraphSubsolProof.subsol_extension hmono hΓ hsub hhat

end GuaranteedSubsol
