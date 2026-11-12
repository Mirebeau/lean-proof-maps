/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.CstSubsolProof

/-!
# Frozen statement: a `δ`-strictly causal operator is `≥ δ` on `0`

Source: Prop. prop:cst_subsol (Intro.tex, V1), item enum:Lambda0_delta, strictly causal case: if
`Γ` is `δ`-strictly causal (and additively invariant), then `Γ[0] ≥ δ` (scalar form, at a point of
`Int X`; no sign condition on `δ` is needed).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem le_apply_zero_of_strictlyCausal {X : Type*} {Γ : (X → ℝ) → ℝ} {δ : ℝ}
    (hcaus : StrictlyCausal δ Γ) (hadd : AdditivelyInvariant Γ) : δ ≤ Γ 0 := by
  exact CstSubsolProof.le_apply_zero_of_strictlyCausal hcaus hadd

end GuaranteedSubsol
