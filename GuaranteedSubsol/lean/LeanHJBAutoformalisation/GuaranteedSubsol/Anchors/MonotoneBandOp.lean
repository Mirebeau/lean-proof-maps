/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.BandProof

/-!
# Frozen statement: the operator on a band, with frozen exterior values, is monotone

Source: Lemma lem:monDom (Complexity.tex), first claim, for `Λ_B^v` (eq. eqdef:Lambda_B,
right): if `Λ` is monotone, so is `Λ_B^v` (`bandOp Λ B v`, acting on `ℝ^B`, the values outside `B`
being frozen to `v`).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem monotone_bandOp {X : Type*} {Λ : (X → ℝ) → X → ℝ} (hΛ : Monotone Λ) (B : Set X)
    (v : X → ℝ) : Monotone (bandOp Λ B v) := by
  exact BandProof.monotone_bandOp fun x _ _ _ h => hΛ h x

end GuaranteedSubsol
