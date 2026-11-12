/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.CausalMixProof

/-!
# Frozen statement: `max` of two Causal operators

Source: Lemma lem:causal_mix (Complexity.tex), scalar form:
if `Γ` and `Λ` satisfy `Causal`, then so does `max {Γ, Λ}`.
Monotonicity is Mathlib's `Monotone.max`.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem Causal.max {X : Type*} {Λ Γ : (X → ℝ) → ℝ} (hΛ : Causal Λ)
    (hΓ : Causal Γ) :
    Causal fun u => max (Λ u) (Γ u) := by
  exact CausalMixProof.causal_max hΛ hΓ

end GuaranteedSubsol
