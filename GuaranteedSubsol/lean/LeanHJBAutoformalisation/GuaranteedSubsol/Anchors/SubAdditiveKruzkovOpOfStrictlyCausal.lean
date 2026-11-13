/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.StrictCausalSubaddProof

/-!
# Frozen statement: strict causality implies sub-additivity in Kruzkov coordinates

Source: Prop. prop:strict_causal_implies_subadd (Subadd.tex), scalar form: if `Λ` is
`δ`-strictly-causal, monotone and `1`-sub-additive, with `δ > 0`, then `Φ_α` is
`exp(-δ/α)`-sub-additive for any `α > 0`. Author ruling: the assumption `δ > 0` is dropped,
being unneeded. `X` is finite (standing assumption).

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem subAdditive_kruzkovOp_of_strictlyCausal {X : Type*} [Finite X] {Λ : (X → ℝ) → ℝ}
    (hmono : Monotone Λ) (hsub1 : SubAdditive 1 Λ) {δ α : ℝ}
    (hcaus : StrictlyCausal δ Λ) (hα : 0 < α) :
    SubAdditive (Real.exp (-δ / α)) (kruzkovOp α Λ) := by
  exact StrictCausalSubaddProof.subAdditive_kruzkovOp_of_strictlyCausal hmono hsub1 hcaus hα

end GuaranteedSubsol
