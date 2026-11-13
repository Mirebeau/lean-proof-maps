/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.LocalXProof

/-!
# Frozen statement: the two local formulations of sub-additivity, with `O(t²)` remainders

Source: Prop. prop:subadd_local (Subadd.tex), equivalence of (subadd_local) and (subadd_local_x)
in the variant where `o(t)` is replaced with `O(t²)` ("The equivalence also holds if the
remainder `o(t)` is replaced with `O(t²)`"), scalar form. `O(t²)` is written
`∃ K, ∀ᶠ t in 𝓝[>] 0, … + K t²`. It is the change of variable `t' = t exp(-Λ u / α)`, valid for
any operator `Λ`; `αinv = 1/α`. Together with `kruzkov_local_of_subAdditive`, it gives
(subadd_local_x) with `O(t²)` from the `ρ`-sub-additivity of `Φ_α`.

State: see `ANCHORS.md`.
-/

@[expose] public section

open Filter Topology

namespace GuaranteedSubsol

theorem local_iff_local_x_sq {X : Type*} (Λ : (X → ℝ) → ℝ) {αinv ρ : ℝ} :
    (∀ (u : X → ℝ), ∃ K : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ),
        Λ (fun y => u y + t * Real.exp (αinv * u y)) ≤
          Λ u + ρ * t * Real.exp (αinv * Λ u) + K * t ^ 2) ↔
      ∀ (u : X → ℝ), ∃ K : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ),
        Λ (fun y => u y + t * Real.exp (αinv * (u y - Λ u))) ≤ Λ u + ρ * t + K * t ^ 2 := by
  exact LocalXProof.local_iff_local_x_sq Λ

end GuaranteedSubsol
