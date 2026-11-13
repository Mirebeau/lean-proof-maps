/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.CstSubsolProof

/-!
# Frozen statement: an operator with `C_past`-memory is `≤ C_past` on `0`

Source: the remark following Prop. prop:cst_subsol (Intro.tex): `C_past`-memory and additive
invariance together imply `Λ[0] ≤ C_past` (scalar form, at a point of `Int X`).

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem apply_zero_le_of_hasMemory {X : Type*} {Λ : (X → ℝ) → ℝ} {C : ℝ}
    (hmem : HasMemory C Λ) (hadd : AdditivelyInvariant Λ) : Λ 0 ≤ C := by
  exact CstSubsolProof.apply_zero_le_of_hasMemory hmem hadd

end GuaranteedSubsol
