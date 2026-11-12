/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ExtCausalMixProof

/-!
# Frozen statement: `min` of two SubAdditive operators on `ℝ_∞`

Source: Lemma lem:causal_mix (Complexity.tex), scalar form on `ℝ_∞ = WithTop ℝ`:
if `Γ` and `Λ` satisfy `Ext.SubAdditive`, then so does `min {Γ, Λ}`.
Monotonicity is Mathlib's `Monotone.min`.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol.Ext

theorem SubAdditive.min {X : Type*} {Λ Γ : (X → WithTop ℝ) → WithTop ℝ} {ρ : ℝ}
    (hΛ : SubAdditive ρ Λ) (hΓ : SubAdditive ρ Γ) :
    SubAdditive ρ fun u => min (Λ u) (Γ u) := by
  exact GuaranteedSubsol.ExtCausalMixProof.subAdditive_min hΛ hΓ

end GuaranteedSubsol.Ext
