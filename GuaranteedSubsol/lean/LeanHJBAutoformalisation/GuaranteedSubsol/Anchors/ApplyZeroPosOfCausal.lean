/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ApplyZeroNonnegProof

/-!
# Frozen statement: a causal operator is positive on `0`

Source: Prop. prop:cst_subsol (Intro.tex, V1), item enum:Lambda0_delta, causal case: if `Γ` is
causal (and additively invariant), then `Γ[0] > 0` (scalar form, at a point of `Int X`).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem apply_zero_pos_of_causal {X : Type*} {Γ : (X → ℝ) → ℝ} (hcaus : Causal Γ)
    (hadd : AdditivelyInvariant Γ) : 0 < Γ 0 := by
  exact ApplyZeroNonnegProof.apply_zero_pos_of_causal hcaus hadd

end GuaranteedSubsol
