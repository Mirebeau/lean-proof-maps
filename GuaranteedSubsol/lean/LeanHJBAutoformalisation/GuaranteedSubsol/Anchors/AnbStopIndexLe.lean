/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AnbMaxWidthProof

/-!
# Frozen statement: the ANB terminates within `⌈n_max⌉ + 1` iterations

Source: Corollary corol:max_width (Complexity.tex), first claim, author's request: the stopping
index `anbStopIndex` of the ANB (the first iteration at whose start the stopping test
`(1 + ε) ū ≥ u̲` holds, `⊤` in `ℕ∞` if it never holds) is at most `⌈n_max⌉₊ + 1`, i.e. the ANB
terminates after at most `⌈n_max⌉₊` iterations of the paper (the iteration `0` of the Lean version
is vacuous); `⌈n_max⌉₊` is V1's `n_max`, which has a ceiling. Same hypotheses as
`anbRun_done_of_maxWidth` (with `Δ_max := 2α ln(2e/ε) + 2τ`, as in V1). `X` is finite and linearly
ordered (tie-breaking). Constants renamed with Greek letters (`Δmax`, `ΔplusMax`, `εmax`, `NΛ'`,
`NΛ''`, `NΓ`) and inner-loop pass counts written `passesSub`, `passesSup` (author ruling,
2026-10-14; statements equal by definition).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem anbStopIndex_le {X : Type*} [Fintype X] [LinearOrder X] {p : AnbParams X}
    {I : Set X} {ubd : X → ℝ} (hΛbd : ∀ u, ∀ x ∉ I, p.Λ u x = ubd x)
    (hΓbd : ∀ u, ∀ x ∉ I, p.Γ u x = ubd x) {CΓ CΓ' : ℝ} (hCΓ : 1 ≤ CΓ)
    (hΛmono : ∀ x, Monotone (p.Λ · x)) (hadd : ∀ x ∈ I, AdditivelyInvariant (p.Λ · x))
    (hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (p.Λ · x) (p.Γ · x))
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x))
    (hΓadd : ∀ x ∈ I, AdditivelyInvariant (p.Γ · x)) (hΓΛ : ∀ u, p.Γ u ≤ p.Λ u)
    (hsub : ∀ x ∈ I, SubAdditive p.ρ (kruzkovOp p.α (p.Λ · x))) (hα : 0 < p.α)
    (hρ0 : 0 ≤ p.ρ) (hρ1 : p.ρ < 1) (hτ : 0 < p.τ) {uFix : X → ℝ} (hfix : p.Λ uFix = uFix)
    (hε : 0 < p.ε) (hεmax : p.ε ≤ p.εmax uFix) (hbd : ∀ x ∉ I, 2 * p.Δmax ≤ ubd x) :
    anbStopIndex p ≤ ((⌈p.nMax uFix⌉₊ + 1 : ℕ) : ℕ∞) := by
  exact AnbMaxWidthProof.stopIndex_le
    ⟨hΛbd, hΓbd, hCΓ, hΛmono, hadd, hcmp, hΓmono, hΓcaus, hΓadd, hΓΛ, hsub, hα, hρ0, hρ1, hτ,
      hfix, hε, hεmax, hbd⟩

end GuaranteedSubsol
