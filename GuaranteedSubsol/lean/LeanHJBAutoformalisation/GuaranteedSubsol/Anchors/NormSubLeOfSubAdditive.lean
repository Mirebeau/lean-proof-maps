/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.ContractivityProof

/-!
# Frozen statement: a monotone `ρ`-sub-additive operator is a `ρ`-contraction

Source: Prop. prop:contractivity (Complexity.tex), first part: if `Φ : ℝ^X → ℝ^X` is monotone
and `ρ`-sub-additive, then `‖Φ u - Φ v‖_∞ ≤ ρ ‖u - v‖_∞`. The operator is global, sub-additive at
every point; for finite `X`, Mathlib's norm on `X → ℝ` is the sup norm.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem norm_sub_le_of_subAdditive {X : Type*} [Fintype X] {Φ : (X → ℝ) → X → ℝ} {ρ : ℝ}
    (hmono : Monotone Φ) (hsub : ∀ x, SubAdditive ρ (Φ · x)) (u v : X → ℝ) :
    ‖Φ u - Φ v‖ ≤ ρ * ‖u - v‖ := by
  exact ContractivityProof.norm_sub_le_of_subAdditive hmono hsub u v

end GuaranteedSubsol
