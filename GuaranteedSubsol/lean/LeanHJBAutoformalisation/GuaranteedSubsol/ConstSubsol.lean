/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.Axioms
import Mathlib.Tactic.Linarith

/-!
# Constant sub-solutions

Provider proofs for Prop. prop:cst_subsol (Intro.tex), see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

/-- A `ν`-sub-multiplicative operator satisfies `Λ[0] ≥ ν` (sub-multiplicativity with `u = 0`,
`t = 1`). -/
theorem SubMultiplicative.le_apply_zero {X : Type*} {Λ : (X → ℝ) → ℝ} {ν : ℝ}
    (hmul : SubMultiplicative ν Λ) : ν ≤ Λ 0 := by
  have h := hmul 1 zero_le_one 0
  have h0 : (fun y : X => (1 + 1 : ℝ) * (0 : X → ℝ) y) = 0 := by
    funext y; simp
  rw [h0] at h
  linarith

end GuaranteedSubsol
