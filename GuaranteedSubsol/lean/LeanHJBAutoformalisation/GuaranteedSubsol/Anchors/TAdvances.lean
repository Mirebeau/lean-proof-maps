/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.TAdvancesProof

/-!
# Frozen statement: the tolerance criterion advances in the narrow band

Source: Prop. prop:t_advances (Complexity.tex). Global operator `Λ : (X → ℝ) → X → ℝ` with
Dirichlet data `ubd` outside `I = Int X`; `Φ` at `x` is `kruzkovOp α (Λ · x)`. The Kruzkov
transform of `ū` is `v̄ = kruzkov αinv ū`, with `α * αinv = 1`. Author rulings: the monotonicity
of `Λ` is not needed (the generalized `monotoneExtension` makes `Φ` monotone), and the
assumptions `v̄ - Φ v̄ ≤ 0` and `0 ≤ v̲ - Φ v̲` of (a) are dropped, being unused. The assumption
`T⁻ < T⁺` is dropped as well: it follows from the constraint on `Δ`.
`t = (T⁺ + T⁻)/2` and `Δ = (T⁺ - T⁻)/2` are given by their definitions.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem t_advances {X : Type*} [Finite X] {Λ : (X → ℝ) → X → ℝ} {I : Set X} {ubd : X → ℝ}
    (hΛbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) {α αinv ρ : ℝ} (hα : 0 < α) (hααinv : α * αinv = 1)
    (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) (hadd : ∀ x ∈ I, AdditivelyInvariant (Λ · x))
    (hsub : ∀ x ∈ I, SubAdditive ρ (kruzkovOp α (Λ · x)))
    {uSub vsub vsup : X → ℝ} (hvsub : ∀ x, vsub x = kruzkov αinv (uSub x))
    (hvsup : ∀ x, vsup x ≤ 0) {Tm Tp ξ ε C t Δ : ℝ} (hTm : 0 ≤ Tm) (hξ : 0 ≤ ξ)
    (hε : 0 < ε) (hC : 1 ≤ C) (ht : t = (Tp + Tm) / 2) (hΔ : Δ = (Tp - Tm) / 2)
    (ha₁ : ∀ x, Tm ≤ uSub x → uSub x < Tp → -((1 - ρ) * ξ) ≤ vsub x - kruzkovOp α (Λ · x) vsub)
    (ha₂ : ∀ x, Tm ≤ uSub x → uSub x < Tp → vsup x - kruzkovOp α (Λ · x) vsup ≤ (1 - ρ) * ξ)
    (hb : ∀ x, Tp ≤ uSub x → -ξ ≤ vsub x)
    (hc : ∀ x, uSub x < Tm → vsup x ≤ vsub x * Real.exp (-ε * αinv * uSub x))
    (hξC : ξ ≤ C * Real.exp (-αinv * Tp)) (hεT : ε * Tp ≤ α)
    (hΔlarge : 2 * α * max 1 (Real.log (2 * Real.exp 1 * C / ε)) ≤ Δ) :
    ∀ x, t - Δ / 2 ≤ uSub x → uSub x ≤ t + Δ / 2 →
      vsup x ≤ vsub x * Real.exp (-ε * αinv * uSub x) := by
  exact TAdvancesProof.t_advances hΛbd hα hααinv hρ₀ hρ₁ hadd hsub hvsub hvsup hTm hξ hε hC
    ht hΔ ha₁ ha₂ hb hc hξC hεT hΔlarge

end GuaranteedSubsol
