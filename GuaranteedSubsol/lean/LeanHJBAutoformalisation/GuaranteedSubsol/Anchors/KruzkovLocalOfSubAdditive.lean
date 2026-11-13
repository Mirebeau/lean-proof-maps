/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.SubaddLocalFwdProof

/-!
# Frozen statement: sub-additivity of `Φ_α` implies the local expansion, with `O(t²)`

Source: Prop. prop:subadd_local (Subadd.tex), direct implication, scalar form, with the strongest
conclusion (the `O(t²)` variant): if `Λ` is monotone and
`Φ_α = kruzkovOp α Λ` is `ρ`-sub-additive, then for every `u`,
`Λ [u + t exp(u/α)] ≤ Λ u + ρ t exp(Λ u / α) + O(t²)` as `t → 0⁺`. Here `α * αinv = 1`.
Author ruling: the continuity assumption of the paper and the finiteness of `X` are dropped, being
unused in this direction; `0 ≤ ρ` in place of the paper's `ρ > 0`.

State: see `ANCHORS.md`.
-/

@[expose] public section

open Filter Topology

namespace GuaranteedSubsol

theorem kruzkov_local_of_subAdditive {X : Type*} {Λ : (X → ℝ) → ℝ} (hmono : Monotone Λ)
    {α αinv ρ : ℝ} (hα : 0 < α) (hααinv : α * αinv = 1) (hρ : 0 ≤ ρ)
    (h : SubAdditive ρ (kruzkovOp α Λ)) (u : X → ℝ) :
    ∃ K : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Λ (fun y => u y + t * Real.exp (αinv * u y)) ≤
        Λ u + ρ * t * Real.exp (αinv * Λ u) + K * t ^ 2 := by
  exact SubaddLocalFwdProof.kruzkov_local_of_subAdditive hmono hα hααinv hρ h u

end GuaranteedSubsol
