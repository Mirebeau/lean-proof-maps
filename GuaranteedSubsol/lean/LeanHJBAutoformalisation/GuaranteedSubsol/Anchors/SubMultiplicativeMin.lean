/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.CausalMixProof

/-!
# Frozen statement: `min` of two SubMultiplicative operators

Source: Lemma lem:causal_mix (Complexity.tex), scalar form:
if `Γ` and `Λ` satisfy `SubMultiplicative`, then so does `min {Γ, Λ}`.
Monotonicity is Mathlib's `Monotone.min`.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem SubMultiplicative.min {X : Type*} {Λ Γ : (X → ℝ) → ℝ} {ν : ℝ} (hΛ : SubMultiplicative ν Λ)
    (hΓ : SubMultiplicative ν Γ) :
    SubMultiplicative ν fun u => min (Λ u) (Γ u) := by
  exact CausalMixProof.subMultiplicative_min hΛ hΓ

end GuaranteedSubsol
