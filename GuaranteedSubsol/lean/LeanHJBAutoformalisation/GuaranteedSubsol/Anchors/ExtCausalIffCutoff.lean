/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ExtCausalCutoffProof

/-!
# Frozen statement: causality on `ℝ_∞` in terms of cutoffs

Source: Prop. prop:causal_formulation (Complexity.tex), eq. (causal_old), scalar form on
`ℝ_∞ = WithTop ℝ`: `Ext.Causal Γ` is equivalent to
`∀ u v t, u^{<t} = v^{<t} ⇒ (Γ u)^{≤t} = (Γ v)^{≤t}`, for `Γ : (X → ℝ_∞) → ℝ_∞`.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol.Ext

theorem causal_iff_cutoff {X : Type*} (Γ : (X → WithTop ℝ) → WithTop ℝ) :
    Causal Γ ↔ ∀ (u v : X → WithTop ℝ) (t : ℝ),
      (∀ y, cutoffLt t (u y) = cutoffLt t (v y)) → cutoffLe t (Γ u) = cutoffLe t (Γ v) := by
  exact GuaranteedSubsol.ExtCausalCutoffProof.causal_iff_cutoff Γ

end GuaranteedSubsol.Ext
