/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.RestrictionProof

/-!
# Frozen statement: restriction preserves monotonicity

Source: Lemma lem:monDom (Complexity.tex), first claim: if `Λ` is monotone, so is `Λ_B`.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem monotone_restrictOp {X : Type*} {Λ : (X → ℝ) → X → ℝ} (hΛ : Monotone Λ)
    (B : Set X) : Monotone (restrictOp Λ B) := by
  exact RestrictionProof.monotone_restrictOp hΛ B

end GuaranteedSubsol
