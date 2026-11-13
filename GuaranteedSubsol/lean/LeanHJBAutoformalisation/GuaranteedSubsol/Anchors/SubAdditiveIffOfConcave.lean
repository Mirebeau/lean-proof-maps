/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.SubaddConcaveProof

/-!
# Frozen statement: sub-additivity of `Φ_α` for a concave operator

Source: Corol. corol:subadd_concave (Subadd.tex), scalar form: if `Λ` is monotone and concave,
then `Φ_α = kruzkovOp α Λ` is `ρ`-sub-additive iff
`Λ [u + t exp(u/α)] ≤ Λ u + ρ t exp(Λ u / α)` for all `u` and all `t ≥ 0`. Here `α * αinv = 1`
and `X` is finite (standing assumption).

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem subAdditive_kruzkovOp_iff_of_concave {X : Type*} [Finite X] {Λ : (X → ℝ) → ℝ}
    (hmono : Monotone Λ) (hconc : ConcaveOn ℝ Set.univ Λ) {α αinv ρ : ℝ} (hα : 0 < α)
    (hααinv : α * αinv = 1) (hρ : 0 ≤ ρ) :
    SubAdditive ρ (kruzkovOp α Λ) ↔
      ∀ (u : X → ℝ) (t : ℝ), 0 ≤ t →
        Λ (fun y => u y + t * Real.exp (αinv * u y)) ≤ Λ u + ρ * t * Real.exp (αinv * Λ u) := by
  exact SubaddConcaveProof.subAdditive_kruzkovOp_iff_of_concave hmono hconc hα hααinv hρ

end GuaranteedSubsol
