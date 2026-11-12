/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ContractivityProof

/-!
# Frozen statement: fixed point of a monotone `ρ`-sub-additive operator, `ρ < 1`

Source: Prop. prop:contractivity (Complexity.tex), second part: if moreover `ρ < 1`, then `Φ`
admits a unique fixed point `v*`, and `‖Φⁿ v - v*‖_∞ ≤ ρⁿ ‖Φ v - v‖_∞ / (1 - ρ)` for all `v`.
The fixed point is shared by the three conclusions. For finite `X`, Mathlib's norm on `X → ℝ` is
the sup norm.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem existsUnique_fixedPoint_of_subAdditive {X : Type*} [Fintype X] {Φ : (X → ℝ) → X → ℝ}
    {ρ : ℝ} (hρ : ρ < 1) (hmono : Monotone Φ) (hsub : ∀ x, SubAdditive ρ (Φ · x)) :
    ∃ vFix : X → ℝ, Φ vFix = vFix ∧ (∀ w, Φ w = w → w = vFix) ∧
      ∀ (v : X → ℝ) (n : ℕ), ‖Φ^[n] v - vFix‖ ≤ ρ ^ n * ‖Φ v - v‖ / (1 - ρ) := by
  exact ContractivityProof.existsUnique_fixedPoint_of_subAdditive hρ hmono hsub

end GuaranteedSubsol
