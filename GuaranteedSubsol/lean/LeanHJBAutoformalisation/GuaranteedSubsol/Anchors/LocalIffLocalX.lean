/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.LocalXProof

/-!
# Frozen statement: the two local formulations of sub-additivity in Kruzkov coordinates

Source: Prop. prop:subadd_local (Subadd.tex), equivalence of (subadd_local) and (subadd_local_x),
scalar form, with `o(t)` remainders written `∀ η > 0, ∀ᶠ t in 𝓝[>] 0, … + η t`. It is the change
of variable `t' = t exp(-Λ u / α)`, valid for any operator `Λ`; `αinv = 1/α`.

State: see `ANCHORS.md`.
-/

open Filter Topology

namespace GuaranteedSubsol

theorem local_iff_local_x {X : Type*} (Λ : (X → ℝ) → ℝ) {αinv ρ : ℝ} :
    (∀ (u : X → ℝ), ∀ η > (0 : ℝ), ∀ᶠ t in 𝓝[>] (0 : ℝ),
        Λ (fun y => u y + t * Real.exp (αinv * u y)) ≤
          Λ u + ρ * t * Real.exp (αinv * Λ u) + η * t) ↔
      ∀ (u : X → ℝ), ∀ η > (0 : ℝ), ∀ᶠ t in 𝓝[>] (0 : ℝ),
        Λ (fun y => u y + t * Real.exp (αinv * (u y - Λ u))) ≤ Λ u + ρ * t + η * t := by
  exact LocalXProof.local_iff_local_x Λ

end GuaranteedSubsol
