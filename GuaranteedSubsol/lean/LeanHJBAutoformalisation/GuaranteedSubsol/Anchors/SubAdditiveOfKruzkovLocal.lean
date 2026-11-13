/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.SubaddLocalBwdProof

/-!
# Frozen statement: the local expansion implies sub-additivity of `Φ_α`

Source: Prop. prop:subadd_local (Subadd.tex), converse implication, scalar form, with the weakest
hypothesis (the `o(t)` variant): if `Λ` is monotone and continuous and, for every `u`,
`Λ [u + t exp(u/α)] ≤ Λ u + ρ t exp(Λ u / α) + o(t)` as `t → 0⁺`, then `Φ_α = kruzkovOp α Λ`
is `ρ`-sub-additive. The `o(t)` is written `∀ η > 0, ∀ᶠ t in 𝓝[>] 0, … + η t`;
`α * αinv = 1`.
As in the paper, `Λ` is continuous; `X` is `Finite`
(only continuity and finiteness are used); `0 ≤ ρ` in place of the paper's `ρ > 0`.

State: see `ANCHORS.md`.
-/

@[expose] public section

open Filter Topology

namespace GuaranteedSubsol

theorem subAdditive_of_kruzkov_local {X : Type*} [Finite X] {Λ : (X → ℝ) → ℝ}
    (hmono : Monotone Λ) (hcont : Continuous Λ) {α αinv ρ : ℝ} (hα : 0 < α)
    (hααinv : α * αinv = 1) (hρ : 0 ≤ ρ)
    (h : ∀ (u : X → ℝ), ∀ η > (0 : ℝ), ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Λ (fun y => u y + t * Real.exp (αinv * u y)) ≤
        Λ u + ρ * t * Real.exp (αinv * Λ u) + η * t) :
    SubAdditive ρ (kruzkovOp α Λ) := by
  exact SubaddLocalBwdProof.subAdditive_of_kruzkov_local hmono hcont hα hααinv hρ h

end GuaranteedSubsol
