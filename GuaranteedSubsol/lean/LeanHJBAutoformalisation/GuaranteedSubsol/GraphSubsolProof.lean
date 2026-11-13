/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.Axioms

/-!
# Extension of a sub-solution by a graph operator: proof

Provider proof for the frozen anchor `GuaranteedSubsol.subsol_extension` (see `ANCHORS.md`):
Lemma lem:graph_subsol (Complexity.tex). One has `ū ≤ û` by construction, hence `Λ ū ≤ Λ û`, and
`û = max {ū, Γ û} ≤ max {Λ ū, Λ û} = Λ û`.
-/

@[expose] public section

namespace GuaranteedSubsol.GraphSubsolProof

theorem subsol_extension {X : Type*} {Λ Γ : (X → ℝ) → X → ℝ} (hmono : Monotone Λ)
    (hΓ : Γ ≤ Λ) {uSub uHat : X → ℝ} (hsub : uSub ≤ Λ uSub)
    (hhat : uHat = fun x => max (uSub x) (Γ uHat x)) :
    uHat ≤ Λ uHat := by
  have hle : uSub ≤ uHat := fun x => by
    rw [congrFun hhat x]
    exact le_max_left _ _
  intro x
  rw [congrFun hhat x]
  exact max_le ((hsub x).trans (hmono hle x)) (hΓ uHat x)

end GuaranteedSubsol.GraphSubsolProof
