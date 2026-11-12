/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.CausalCutoffProof

/-!
# Frozen statement: causality in terms of cutoffs

Source: Prop. prop:causal_formulation (Complexity.tex), eq. (causal_old), scalar form: causality is
equivalent to `∀ u v t, u^{<t} = v^{<t} ⇒ (Γ u)^{≤t} = (Γ v)^{≤t}`. The scalar operator
`Γ : (X → ℝ) → ℝ` stands for `(Γ · x)`; values are compared in `ℝ_∞ = WithTop ℝ` through the
cutoffs `cutoffLt`, `cutoffLe`.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem causal_iff_cutoff {X : Type*} (Γ : (X → ℝ) → ℝ) :
    Causal Γ ↔ ∀ (u v : X → ℝ) (t : ℝ),
      (∀ y, cutoffLt t (u y) = cutoffLt t (v y)) → cutoffLe t (Γ u) = cutoffLe t (Γ v) := by
  exact CausalCutoffProof.causal_iff_cutoff Γ

end GuaranteedSubsol
