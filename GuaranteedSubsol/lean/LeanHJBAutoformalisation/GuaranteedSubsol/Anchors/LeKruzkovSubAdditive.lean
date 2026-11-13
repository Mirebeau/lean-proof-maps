/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.Lambda0SubaddProof

/-!
# Frozen statement: `Λ[0] ≥ -α ln ρ` when `Φ_α` is `ρ`-sub-additive

Source: Prop. prop:cst_subsol (Intro.tex), item enum:Lambda0_alpha. Scalar operator
`Λ : (X → ℝ) → ℝ`, standing for `(Λ · x)` at `x ∈ Int X`; `Φ_α` is `kruzkovOp α Λ`.

Additive invariance is assumed, as in Prop. prop:cst_subsol: without it the statement fails
(a constant operator `Λ = K` is monotone and `Φ_α` is then constant, hence `ρ`-sub-additive, for
any `K`). The paper's `ρ < 1` is not needed, and `ρ > 0` follows from the other assumptions
(author ruling: dropped). A version with weaker assumptions (`α ≥ 0`, and `Λ w ≤ Λ 0` for `w ≤ 0`
instead of monotonicity) is `Lambda0SubaddProof.le_apply_zero_of_kruzkov_subAdditive'`.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem le_apply_zero_of_kruzkov_subAdditive {X : Type*} {Λ : (X → ℝ) → ℝ} {α ρ : ℝ}
    (hα : 0 < α) (hmono : Monotone Λ)
    (hadd : AdditivelyInvariant Λ) (hsub : SubAdditive ρ (kruzkovOp α Λ)) :
    -α * Real.log ρ ≤ Λ 0 := by
  exact Lambda0SubaddProof.le_apply_zero_of_kruzkov_subAdditive hα hmono hadd hsub

end GuaranteedSubsol
