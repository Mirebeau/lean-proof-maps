/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ConstSubsol

/-!
# Frozen statement: `Λ[0] ≥ ν` for a `ν`-sub-multiplicative operator

Source: Prop. prop:cst_subsol (Intro.tex), first branch, and its proof (sub-multiplicativity with
`u = 0`, `t = 1`). Scalar operator `Λ : (X → ℝ) → ℝ`, standing for `(Λ · x)` at `x ∈ Int X`.
Author ruling: the paper's additive invariance and `ν > 0` are dropped, being unused for this
conclusion (they are only needed for `t ≤ Λ[t]`, not formalized here).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem le_apply_zero_of_subMultiplicative {X : Type*} {Λ : (X → ℝ) → ℝ} {ν : ℝ}
    (hmul : SubMultiplicative ν Λ) : ν ≤ Λ 0 := by
  exact SubMultiplicative.le_apply_zero hmul

end GuaranteedSubsol
