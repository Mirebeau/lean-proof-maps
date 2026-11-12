/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.TAdvancesWithUnknownProof

/-!
# Frozen statement: the tolerance criterion advances, unknown parameters

Source: Prop. prop:t_advances_withUnknown (Complexity.tex). Same conventions as `t_advances`:
global operator `Λ` with Dirichlet data `ubd` outside `I = Int X`; `Φ_α` (resp. `Φ_β`) at `x` is
`kruzkovOp α (Λ · x)` (resp. `kruzkovOp β (Λ · x)`); `v̄ = kruzkov αinv ū`; `α * αinv = 1`;
`r = α / β`, `C = (1-ρ)^r / (1-σ)`, `t` and `Δ` given by their definitions.
Author rulings: the monotonicity of `Λ`, the assumptions `v̄ - Φ_α v̄ ≤ 0` and `0 ≤ v̲ - Φ_α v̲`
of (a), `T⁻ < T⁺` and `0 < ρ` are dropped, being unused (V1 assumes `ρ, σ ∈ ]0,1[`; here
`0 ≤ σ < 1`). Renamed from `t_advances_small_alpha`
(author ruling, 2026-10-14: `WithUnknown` in place of `small_alpha`; statement unchanged).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem t_advances_withUnknown {X : Type*} [Finite X] {Λ : (X → ℝ) → X → ℝ} {I : Set X}
    {ubd : X → ℝ} (hΛbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) {α β αinv ρ σ r C : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hααinv : α * αinv = 1)
    (hρ₁ : ρ < 1) (hσ₀ : 0 ≤ σ) (hσ₁ : σ < 1) (hr : r = α / β) (hr₁ : r ≤ 1)
    (hCdef : C = (1 - ρ) ^ r / (1 - σ)) (hC : 1 ≤ C)
    (hadd : ∀ x ∈ I, AdditivelyInvariant (Λ · x))
    (hsub : ∀ x ∈ I, SubAdditive σ (kruzkovOp β (Λ · x)))
    {uSub vsub vsup : X → ℝ} (hvsub : ∀ x, vsub x = kruzkov αinv (uSub x))
    (hvsup : ∀ x, vsup x ≤ 0) {Tm Tp ξ ε t Δ : ℝ} (hTm : 0 ≤ Tm) (hξ : 0 ≤ ξ) (hε : 0 < ε)
    (ht : t = (Tp + Tm) / 2) (hΔ : Δ = (Tp - Tm) / 2)
    (ha₁ : ∀ x, Tm ≤ uSub x → uSub x < Tp → -((1 - ρ) * ξ) ≤ vsub x - kruzkovOp α (Λ · x) vsub)
    (ha₂ : ∀ x, Tm ≤ uSub x → uSub x < Tp → vsup x - kruzkovOp α (Λ · x) vsup ≤ (1 - ρ) * ξ)
    (hb : ∀ x, Tp ≤ uSub x → -ξ ≤ vsub x)
    (hc : ∀ x, uSub x < Tm → vsup x ≤ vsub x * Real.exp (-ε * αinv * uSub x))
    (hξT : ξ ≤ Real.exp (-αinv * Tp)) (hεT : ε * Tp ≤ α)
    (hΔlarge : 2 * β * max 1 (Real.log (2 * Real.exp 1 * C / ε)) ≤ Δ) :
    ∀ x, t - Δ / 2 ≤ uSub x → uSub x ≤ t + Δ / 2 →
      vsup x ≤ vsub x * Real.exp (-ε * αinv * uSub x) := by
  exact TAdvancesWithUnknownProof.t_advances_withUnknown hΛbd hα hβ hααinv hρ₁ hσ₀
    hσ₁ hr hr₁ hCdef hC hadd hsub hvsub hvsup hTm hξ hε ht hΔ ha₁ ha₂ hb hc hξT hεT hΔlarge

end GuaranteedSubsol
