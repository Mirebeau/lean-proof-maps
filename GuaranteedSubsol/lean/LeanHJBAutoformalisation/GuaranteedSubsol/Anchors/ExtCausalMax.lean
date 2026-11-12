/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ExtCausalMixProof

/-!
# Frozen statement: `max` of two Causal operators on `ℝ_∞`

Source: Lemma lem:causal_mix (Complexity.tex), scalar form on `ℝ_∞ = WithTop ℝ`:
if `Γ` and `Λ` satisfy `Ext.Causal`, then so does `max {Γ, Λ}`.
Monotonicity is Mathlib's `Monotone.max`.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol.Ext

theorem Causal.max {X : Type*} {Λ Γ : (X → WithTop ℝ) → WithTop ℝ}
    (hΛ : Causal Λ) (hΓ : Causal Γ) :
    Causal fun u => max (Λ u) (Γ u) := by
  exact GuaranteedSubsol.ExtCausalMixProof.causal_max hΛ hΓ

end GuaranteedSubsol.Ext
