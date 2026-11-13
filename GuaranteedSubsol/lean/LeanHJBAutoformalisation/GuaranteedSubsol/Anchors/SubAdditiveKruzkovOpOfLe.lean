/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.SubaddConcaveProof

/-!
# Frozen statement: sub-additivity in Kruzkov coordinates at a larger timescale

Source: Prop. prop:subadd_alpha_beta (Subadd.tex), scalar form: if `Λ` is monotone and
`1`-sub-additive and `Φ_α` is `ρ`-sub-additive, with `α > 0` and `ρ ≥ 0`, then `Φ_β` is
`σ`-sub-additive for every `β ≥ α` and `σ ≥ (1 - α/β) + ρ α/β`, without restrictions `ρ < 1`,
`σ < 1`, as in the paper (author ruling). `X` is finite (standing assumption).

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem subAdditive_kruzkovOp_of_le {X : Type*} [Finite X] {Λ : (X → ℝ) → ℝ}
    (hmono : Monotone Λ) (hsub1 : SubAdditive 1 Λ) {α β ρ σ : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hρ : 0 ≤ ρ) (hσ : (1 - α / β) + ρ * (α / β) ≤ σ) (h : SubAdditive ρ (kruzkovOp α Λ)) :
    SubAdditive σ (kruzkovOp β Λ) := by
  exact SubaddConcaveProof.subAdditive_kruzkovOp_of_le hmono hsub1 hα hαβ hρ hσ h

end GuaranteedSubsol
