/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.ExtCausalMixProof

/-!
# Frozen statement: `min` of two Causal operators on `ℝ_∞`

Source: Lemma lem:causal_mix (Complexity.tex), scalar form on `ℝ_∞ = WithTop ℝ`:
if `Γ` and `Λ` satisfy `Ext.Causal`, then so does `min {Γ, Λ}`.
Monotonicity is Mathlib's `Monotone.min`.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol.Ext

theorem Causal.min {X : Type*} {Λ Γ : (X → WithTop ℝ) → WithTop ℝ}
    (hΛ : Causal Λ) (hΓ : Causal Γ) :
    Causal fun u => min (Λ u) (Γ u) := by
  exact GuaranteedSubsol.ExtCausalMixProof.causal_min hΛ hΓ

end GuaranteedSubsol.Ext
