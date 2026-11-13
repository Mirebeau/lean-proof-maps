/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.AnbNGammaProof

/-!
# Frozen statement: at most `N_Γ` updates of `û` at each point in the ANB

Source: author's request, Theorem th:complexity (Intro.tex), the bound `N_Γ` on the updates
`û(x) ← Γ û(x)` when line anb:hatu uses Dijkstra's method as in Prop. prop:Dijkstra_band: over
the whole run, the counter `countHat` of the updates of `û` is at most `N_Γ` at every point
(Corollary corol:NGamma, Prop. prop:Dijkstra_band and Prop. prop:Dijkstra_correct: at most one
update per iteration, at the points of `B'_n`).
Hypotheses: those of Corollary corol:max_width (see `anbRunData_Δ_lt_Δmax`, with
`Δ_max := 2α ln(2e/ε) + 2τ`, as in the paper), together with the `C_past`-memory of `Λ` on `Int X`,
`C_past ≥ 0` and `C'_Γ ≥ 0`, used through Corollary corol:Bn_comp. `Δ⁺_max`, `N'_Λ` and `N_Γ` are
`AnbParams.ΔplusMax`, `AnbParams.NΛ'` and `AnbParams.NΓ`. `X` is finite and
linearly ordered (tie-breaking).
Constants renamed with Greek letters (`Δmax`, `ΔplusMax`, `εmax`, `NΛ'`, `NΛ''`, `NΓ`) and
inner-loop pass counts written `passesSub`, `passesSup` (author ruling, 2026-10-14; statements
equal by definition).

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem anbRun_countHat_le {X : Type*} [Fintype X] [LinearOrder X] {p : AnbParams X}
    {I : Set X} {ubd : X → ℝ} (hΛbd : ∀ u, ∀ x ∉ I, p.Λ u x = ubd x)
    (hΓbd : ∀ u, ∀ x ∉ I, p.Γ u x = ubd x) {CΓ CΓ' : ℝ} (hCΓ : 1 ≤ CΓ)
    (hΛmono : ∀ x, Monotone (p.Λ · x)) (hadd : ∀ x ∈ I, AdditivelyInvariant (p.Λ · x))
    (hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (p.Λ · x) (p.Γ · x))
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x))
    (hΓadd : ∀ x ∈ I, AdditivelyInvariant (p.Γ · x)) (hΓΛ : ∀ u, p.Γ u ≤ p.Λ u)
    (hsub : ∀ x ∈ I, SubAdditive p.ρ (kruzkovOp p.α (p.Λ · x))) (hα : 0 < p.α)
    (hρ0 : 0 ≤ p.ρ) (hρ1 : p.ρ < 1) (hτ : 0 < p.τ) {uFix : X → ℝ} (hfix : p.Λ uFix = uFix)
    (hε : 0 < p.ε) (hεmax : p.ε ≤ p.εmax uFix) (hbd : ∀ x ∉ I, 2 * p.Δmax ≤ ubd x)
    {Cpast : ℝ} (hCpast : 0 ≤ Cpast) (hCΓ' : 0 ≤ CΓ')
    (hmem : ∀ x ∈ I, HasMemory Cpast (p.Λ · x))
    (k : ℕ) (x : X) : (anbRun p k).countHat x ≤ p.NΓ Cpast CΓ CΓ' uFix := by
  exact AnbNGammaProof.countHat_le
    ⟨hΛbd, hΓbd, hCΓ, hΛmono, hadd, hcmp, hΓmono, hΓcaus, hΓadd, hΓΛ, hsub, hα, hρ0, hρ1, hτ,
      hfix, hε, hεmax, hbd⟩ hCpast hCΓ' hmem k x

end GuaranteedSubsol
