/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.KruzkovProof

/-!
# Frozen statement: `Φ_α` is monotone

Source: Prop. prop:monotonic_Phi (Complexity.tex), "`Λ_∞` and `Φ_α` are monotone", scalar form
(`Λ : (X → ℝ) → ℝ` stands for `(Λ · x)`), with `α > 0`.

The paper assumes `Λ` monotone. With the generalized `monotoneExtension` (supremum over finite
minorants) this hypothesis is not needed, so it is omitted.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem monotone_kruzkovOp {X : Type*} {α : ℝ} (hα : 0 < α) (Λ : (X → ℝ) → ℝ) :
    Monotone (kruzkovOp α Λ) := by
  exact KruzkovProof.monotone_kruzkovOp hα Λ

end GuaranteedSubsol
