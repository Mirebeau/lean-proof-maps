/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ExtCausalMixProof

/-!
# Frozen statement: `max` of two SubMultiplicative operators on `ℝ_∞`

Source: Lemma lem:causal_mix (Complexity.tex), scalar form on `ℝ_∞ = WithTop ℝ`:
if `Γ` and `Λ` satisfy `Ext.SubMultiplicative`, then so does `max {Γ, Λ}`.
Monotonicity is Mathlib's `Monotone.max`.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol.Ext

theorem SubMultiplicative.max {X : Type*} {Λ Γ : (X → WithTop ℝ) → WithTop ℝ} {ν : ℝ}
    (hΛ : SubMultiplicative ν Λ) (hΓ : SubMultiplicative ν Γ) :
    SubMultiplicative ν fun u => max (Λ u) (Γ u) := by
  exact GuaranteedSubsol.ExtCausalMixProof.subMultiplicative_max hΛ hΓ

end GuaranteedSubsol.Ext
