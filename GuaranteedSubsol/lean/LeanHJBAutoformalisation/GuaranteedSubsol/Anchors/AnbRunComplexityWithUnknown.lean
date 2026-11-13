/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.AnbWithUnknownProof

/-!
# Frozen statement: complexity of the ANB with unknown constants (th:complexity_withUnknown)

Source: Theorem th:complexity_withUnknown (Intro.tex), packaged as `anbRun_complexity`
(author's request): the conclusions of Theorem th:complexity hold when `Φ_β` (rather than `Φ_α`)
is `σ`-sub-additive, for unknown constants `β`, `σ` (`AnbParams.WithUnknown`; the algorithm only
uses `q.p`), with the modified constants `Δ_max := 2β ln(2eC/ε) + 2τ`,
`C := (1 - ρ)^(α/β)/(1 - σ)`, `N''_Λ := ⌈(2Δ_max/α + ln(β/α) - ln(1 - ρ))/(-ln σ)⌉` (the
constant of Prop. prop:niter_while_withUnknown), and
`n_max`, `ε_max`, `Δ⁺_max`, `N'_Λ`, `N_Γ` built from this `Δ_max`
(`AnbParams.WithUnknown.*`). As in the paper: `n_max` with a ceiling; the bound `N_Λ` for each of
the two counters. Departure from the paper (author ruling): `ρ > 0` is not assumed (unlike
`anbRun_complexity`; the paper assumes `ρ ∈ ]0,1[`). `X` is finite and linearly ordered
(tie-breaking).

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem anbRun_complexity_withUnknown {X : Type*} [Fintype X] [LinearOrder X]
    {q : AnbParams.WithUnknown X} {I : Set X} {ubd : X → ℝ}
    (hΛbd : ∀ u, ∀ x ∉ I, q.p.Λ u x = ubd x) (hΓbd : ∀ u, ∀ x ∉ I, q.p.Γ u x = ubd x)
    {Cpast CΓ CΓ' : ℝ} (hCpast : 0 ≤ Cpast) (hCΓ : 1 ≤ CΓ) (hCΓ' : 0 ≤ CΓ')
    (hΛmono : ∀ x, Monotone (q.p.Λ · x)) (hadd : ∀ x ∈ I, AdditivelyInvariant (q.p.Λ · x))
    (hmem : ∀ x ∈ I, HasMemory Cpast (q.p.Λ · x)) {w : X → ℝ} (hw : q.p.Λ w ≤ w)
    (hΓmono : ∀ x, Monotone (q.p.Γ · x)) (hΓcaus : ∀ x, Causal (q.p.Γ · x))
    (hΓadd : ∀ x ∈ I, AdditivelyInvariant (q.p.Γ · x)) (hΓΛ : ∀ u, q.p.Γ u ≤ q.p.Λ u)
    (hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (q.p.Λ · x) (q.p.Γ · x))
    (hsub : ∀ x ∈ I, SubAdditive q.σ (kruzkovOp q.β (q.p.Λ · x))) (hα : 0 < q.p.α)
    (hαβ : q.p.α ≤ q.β) (hσ0 : 0 < q.σ) (hσ1 : q.σ < 1) (hρ1 : q.p.ρ < 1)
    (hρσ : (1 - q.σ) ^ q.β ≤ (1 - q.p.ρ) ^ q.p.α) (hτ : 0 < q.p.τ) (hε : 0 < q.p.ε)
    (hbd : ∀ x ∉ I, 2 * q.Δmax ≤ ubd x) :
    ∃ uFix : X → ℝ, q.p.Λ uFix = uFix ∧ (∀ v, q.p.Λ v = v → v = uFix) ∧
      (∀ J : Set X, HasComparisonPrinciple J q.p.Λ) ∧
      (q.p.ε ≤ q.εmax uFix →
        anbStopIndex q.p ≤ ((⌈q.nMax uFix⌉₊ + 1 : ℕ) : ℕ∞) ∧
        ((anbRun q.p (anbStopIndex q.p).toNat).uSub ≤
            q.p.Λ (anbRun q.p (anbStopIndex q.p).toNat).uSub ∧
          Global.monotoneExtension q.p.Λ (anbRun q.p (anbStopIndex q.p).toNat).uSup ≤
            (anbRun q.p (anbStopIndex q.p).toNat).uSup ∧
          anbDone q.p (anbRun q.p (anbStopIndex q.p).toNat)) ∧
        (∀ k, (anbRunData q.p k).Δ < q.Δmax) ∧
        (∀ k, (anbRunData q.p k).passesSub ≤ (q.NΛ'' : ℕ∞) ∧
          (anbRunData q.p k).passesSup ≤ (q.NΛ'' : ℕ∞)) ∧
        (∀ (x : X) (S : Finset ℕ), (∀ k ∈ S, x ∈ (anbRunData q.p k).band) →
          S.card ≤ q.NΛ' Cpast CΓ CΓ' uFix) ∧
        (∀ (k : ℕ) (x : X),
          (anbRun q.p k).countSub x ≤ ((q.NΛ' Cpast CΓ CΓ' uFix * q.NΛ'' : ℕ) : ℕ∞) ∧
          (anbRun q.p k).countSup x ≤ ((q.NΛ' Cpast CΓ CΓ' uFix * q.NΛ'' : ℕ) : ℕ∞) ∧
          (anbRun q.p k).countHat x ≤ q.NΓ Cpast CΓ CΓ' uFix)) := by
  exact AnbWithUnknownProof.complexity hΛbd hΓbd hCpast hCΓ hCΓ' hΛmono hadd hmem hw hΓmono
    hΓcaus hΓadd hΓΛ hcmp hsub hα hαβ hσ0 hσ1 hρ1 hρσ hτ hε hbd

end GuaranteedSubsol
