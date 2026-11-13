/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.KruzkovProof

/-!
# Frozen statement: `Λ_∞` is monotone

Source: Prop. prop:monotonic_Phi (Complexity.tex), "`Λ_∞` and `Φ_α` are monotone", scalar form
(`Λ : (X → ℝ) → ℝ` stands for `(Λ · x)`).

The paper assumes `Λ` monotone. With the generalized `monotoneExtension` (supremum over finite
minorants) this hypothesis is not needed, so it is omitted.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem monotone_monotoneExtension {X : Type*} (Λ : (X → ℝ) → ℝ) :
    Monotone (monotoneExtension Λ) := by
  exact KruzkovProof.monotone_monotoneExtension Λ

end GuaranteedSubsol
