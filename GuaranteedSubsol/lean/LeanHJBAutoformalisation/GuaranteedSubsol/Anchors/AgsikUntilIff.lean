/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.AgsikCriterion

/-!
# Frozen statement: reformulation of the intermediate stopping criterion of the AGSIK

Source: Algorithm algo:agsik (AGSI2.tex), line agsik:until, and the displayed reformulation in the
paragraph before the algorithm (with the convention `ln t = -∞` for `t ≤ 0`), at a point with
`u = b` and `Λ u = a` real, level `n`, timescale `α > 0`: the criterion
`exp(-a/α) < exp((ε-b)/α) + 2^{-n}` holds iff `a ≥ n α ln 2` or
`b < a + ε - α ln(1 - exp((a - n α ln 2)/α))`, with a strict second inequality as in the paper.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem agsik_until_iff {α : ℝ} (hα : 0 < α) (a b ε : ℝ) (n : ℕ) :
    Real.exp (-a / α) < Real.exp ((ε - b) / α) + (2 : ℝ)⁻¹ ^ n ↔
      (n * α * Real.log 2 ≤ a ∨
        b < a + ε - α * Real.log (1 - Real.exp ((a - n * α * Real.log 2) / α))) := by
  exact AgsikCriterionProof.agsik_until_iff hα a b ε n

end GuaranteedSubsol
