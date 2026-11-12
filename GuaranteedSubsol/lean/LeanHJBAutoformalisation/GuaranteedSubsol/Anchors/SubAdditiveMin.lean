/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.CausalMixProof

/-!
# Frozen statement: `min` of two SubAdditive operators

Source: Lemma lem:causal_mix (Complexity.tex), scalar form:
if `Γ` and `Λ` satisfy `SubAdditive`, then so does `min {Γ, Λ}`.
Monotonicity is Mathlib's `Monotone.min`.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem SubAdditive.min {X : Type*} {Λ Γ : (X → ℝ) → ℝ} {ρ : ℝ} (hΛ : SubAdditive ρ Λ)
    (hΓ : SubAdditive ρ Γ) :
    SubAdditive ρ fun u => min (Λ u) (Γ u) := by
  exact CausalMixProof.subAdditive_min hΛ hΓ

end GuaranteedSubsol
