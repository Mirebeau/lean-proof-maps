/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AnbWithUnknownProof

/-!
# Frozen statement: corol:NGamma with the modified `Δ_max`, unknown parameters

Source: Corollary corol:max_width_withUnknown (Complexity.tex), last sentence: the statement of
Corollary corol:NGamma holds with the modified `Δ_max` (author's request: one packaged anchor).
Namely: `B_n ⊂ {nτ - 2Δ_max ≤ u_* < nτ + Δ⁺_max}`, `B'_{n+1} ⊂ {nτ - 2Δ_max ≤ u_* <
(n+1)τ + Δ⁺_max}`, and for any point `x` and any finite set `S` of iterations whose band `B_n`
(resp. `B'_{n+1}`) contains `x`, `#S ≤ N'_Λ` (resp. `#S ≤ N_Γ`), as in the anchors
`anbRunData_band_subset`, `anbRunData_dijkstraBand_subset`, `anbRunData_card_band_le`,
`anbRunData_card_dijkstraBand_le`, with `Δ_max := 2β ln(2eC/ε) + 2τ` and the constants
`AnbParams.WithUnknown.ΔplusMax`, `NΛ'`, `NΓ` built from it.
Hypotheses: those of `anbRunData_Δ_lt_Δmax_withUnknown`, plus the `C_past`-memory of `Λ` on
`Int X`, `C_past ≥ 0` and `C'_Γ ≥ 0`. `X` is finite and linearly ordered (tie-breaking).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem anbRunData_band_bounds_withUnknown {X : Type*} [Fintype X] [LinearOrder X]
    {q : AnbParams.WithUnknown X} {I : Set X} {ubd : X → ℝ}
    (hΛbd : ∀ u, ∀ x ∉ I, q.p.Λ u x = ubd x) (hΓbd : ∀ u, ∀ x ∉ I, q.p.Γ u x = ubd x)
    {Cpast CΓ CΓ' : ℝ} (hCpast : 0 ≤ Cpast) (hCΓ : 1 ≤ CΓ) (hCΓ' : 0 ≤ CΓ')
    (hΛmono : ∀ x, Monotone (q.p.Λ · x)) (hadd : ∀ x ∈ I, AdditivelyInvariant (q.p.Λ · x))
    (hmem : ∀ x ∈ I, HasMemory Cpast (q.p.Λ · x))
    (hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (q.p.Λ · x) (q.p.Γ · x))
    (hΓmono : ∀ x, Monotone (q.p.Γ · x)) (hΓcaus : ∀ x, Causal (q.p.Γ · x))
    (hΓadd : ∀ x ∈ I, AdditivelyInvariant (q.p.Γ · x)) (hΓΛ : ∀ u, q.p.Γ u ≤ q.p.Λ u)
    (hsub : ∀ x ∈ I, SubAdditive q.σ (kruzkovOp q.β (q.p.Λ · x))) (hα : 0 < q.p.α)
    (hαβ : q.p.α ≤ q.β) (hσ0 : 0 < q.σ) (hσ1 : q.σ < 1) (hρ1 : q.p.ρ < 1)
    (hρσ : (1 - q.σ) ^ q.β ≤ (1 - q.p.ρ) ^ q.p.α) (hτ : 0 < q.p.τ) {uFix : X → ℝ}
    (hfix : q.p.Λ uFix = uFix) (hε : 0 < q.p.ε) (hεmax : q.p.ε ≤ q.εmax uFix)
    (hbd : ∀ x ∉ I, 2 * q.Δmax ≤ ubd x) :
    (∀ (k : ℕ) (x : X), x ∈ (anbRunData q.p k).band →
      (k : ℝ) * q.p.τ - 2 * q.Δmax ≤ uFix x ∧
        uFix x < (k : ℝ) * q.p.τ + q.ΔplusMax Cpast CΓ CΓ' uFix) ∧
    (∀ (k : ℕ) (x : X), x ∈ anbDijkstraBand (anbRunData q.p k).tMinus
        (((k + 1 : ℕ) : ℝ) * q.p.τ) (anbRunData q.p k).uHat (anbRunData q.p (k + 1)).uHat →
      (k : ℝ) * q.p.τ - 2 * q.Δmax ≤ uFix x ∧
        uFix x < ((k + 1 : ℕ) : ℝ) * q.p.τ + q.ΔplusMax Cpast CΓ CΓ' uFix) ∧
    (∀ (x : X) (S : Finset ℕ), (∀ k ∈ S, x ∈ (anbRunData q.p k).band) →
      S.card ≤ q.NΛ' Cpast CΓ CΓ' uFix) ∧
    (∀ (x : X) (S : Finset ℕ), (∀ k ∈ S, x ∈ anbDijkstraBand (anbRunData q.p k).tMinus
        (((k + 1 : ℕ) : ℝ) * q.p.τ) (anbRunData q.p k).uHat (anbRunData q.p (k + 1)).uHat) →
      S.card ≤ q.NΓ Cpast CΓ CΓ' uFix) := by
  exact AnbWithUnknownProof.nGamma
    ⟨hΛbd, hΓbd, hCΓ, hΛmono, hadd, hcmp, hΓmono, hΓcaus, hΓadd, hΓΛ, hsub, hα, hαβ, hσ0, hσ1,
      hρ1, hρσ, hτ, hfix, hε, hεmax, hbd⟩ hCpast hCΓ' hmem

end GuaranteedSubsol
