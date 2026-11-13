/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.MonotoneExtension

/-!
# Frozen statement: `Λ_∞ = Λ` on finite values

Source: Prop. prop:monotonic_Phi (Complexity.tex), "`Λ_∞ u = Λ u` for all `u ∈ ℝ^X`".
Agreement of the generalized `monotoneExtension` with the paper for monotone `Λ`.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem monotoneExtension_coe {X : Type*} {Λ : (X → ℝ) → ℝ} (hΛ : Monotone Λ) (u : X → ℝ) :
    monotoneExtension Λ (fun y => (u y : WithTop ℝ)) = (Λ u : WithTop ℝ) := by
  exact MonotoneExtension.coe_eq hΛ u

end GuaranteedSubsol
