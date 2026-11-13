/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.AnbComplexityProof

/-!
# Frozen statement: complexity of the ANB (Theorem th:complexity)

Source: Theorem th:complexity (Intro.tex), packaged (author's request). Under Assumption assum:all
(Dirichlet data `ubd` outside `I = Int X`; `Λ` monotone, additively invariant, with
`C_past`-memory and a finite super-solution `w`; `Γ` monotone, additively invariant, causal,
`Γ ≤ Λ`, `C_Γ, C'_Γ`-comparable with `Λ`), assuming that `Φ_α` is `ρ`-sub-additive (with the
parameters `α`, `ρ` of algo:anb), `τ > 0`, `ε > 0` and `2 Δ_max ≤ min u_bd`: `Λ` has a unique
fixed point `u_*` and satisfies the comparison principle (eq. eq:comparison_Lambda); and if
`ε ≤ ε_max`, then the ANB stops within `n_max` iterations (the iteration `0` of the Lean version
is vacuous), producing a sub-solution `ū` and a super-solution `u̲` with `(1 + ε) ū ≥ u̲`; in every
iteration `Δ_n < Δ_max` and each inner loop performs at most `N''_Λ` passes; any `x` lies in at
most `N'_Λ` narrow bands; and at every point there are at most `N_Λ = N'_Λ N''_Λ` updates of `ū`,
at most `N_Λ` updates of `u̲`, and at most `N_Γ` updates of `û`. The bounds in `ℕ∞` also express
termination. As in the paper: `Δ_max := 2α ln(2e/ε) + 2τ`;
`n_max := ⌈(‖u_*‖_∞ + Δ_max)/τ⌉`; `2 Δ_max ≤ min u_bd`; `0 < ρ`; `Δ_max` in `N''_Λ`; the bound
`N_Λ` for each of the two counters. The positivity of the boundary data `u_bd` is not assumed: it
follows from `2 Δ_max ≤ min u_bd` when `ε ≤ ε_max`. `X` is finite and linearly ordered
(tie-breaking).

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem anbRun_complexity {X : Type*} [Fintype X] [LinearOrder X] {p : AnbParams X}
    {I : Set X} {ubd : X → ℝ} (hΛbd : ∀ u, ∀ x ∉ I, p.Λ u x = ubd x)
    (hΓbd : ∀ u, ∀ x ∉ I, p.Γ u x = ubd x) {Cpast CΓ CΓ' : ℝ} (hCpast : 0 ≤ Cpast)
    (hCΓ : 1 ≤ CΓ) (hCΓ' : 0 ≤ CΓ') (hΛmono : ∀ x, Monotone (p.Λ · x))
    (hadd : ∀ x ∈ I, AdditivelyInvariant (p.Λ · x)) (hmem : ∀ x ∈ I, HasMemory Cpast (p.Λ · x))
    {w : X → ℝ} (hw : p.Λ w ≤ w) (hΓmono : ∀ x, Monotone (p.Γ · x))
    (hΓcaus : ∀ x, Causal (p.Γ · x)) (hΓadd : ∀ x ∈ I, AdditivelyInvariant (p.Γ · x))
    (hΓΛ : ∀ u, p.Γ u ≤ p.Λ u) (hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (p.Λ · x) (p.Γ · x))
    (hsub : ∀ x ∈ I, SubAdditive p.ρ (kruzkovOp p.α (p.Λ · x))) (hα : 0 < p.α)
    (hρ0 : 0 < p.ρ) (hρ1 : p.ρ < 1) (hτ : 0 < p.τ) (hε : 0 < p.ε)
    (hbd : ∀ x ∉ I, 2 * p.Δmax ≤ ubd x) :
    ∃ uFix : X → ℝ, p.Λ uFix = uFix ∧ (∀ v, p.Λ v = v → v = uFix) ∧
      (∀ J : Set X, HasComparisonPrinciple J p.Λ) ∧
      (p.ε ≤ p.εmax uFix →
        anbStopIndex p ≤ ((⌈p.nMax uFix⌉₊ + 1 : ℕ) : ℕ∞) ∧
        ((anbRun p (anbStopIndex p).toNat).uSub ≤ p.Λ (anbRun p (anbStopIndex p).toNat).uSub ∧
          Global.monotoneExtension p.Λ (anbRun p (anbStopIndex p).toNat).uSup ≤
            (anbRun p (anbStopIndex p).toNat).uSup ∧
          anbDone p (anbRun p (anbStopIndex p).toNat)) ∧
        (∀ k, (anbRunData p k).Δ < p.Δmax) ∧
        (∀ k, (anbRunData p k).passesSub ≤ (p.NΛ'' : ℕ∞) ∧
          (anbRunData p k).passesSup ≤ (p.NΛ'' : ℕ∞)) ∧
        (∀ (x : X) (S : Finset ℕ), (∀ k ∈ S, x ∈ (anbRunData p k).band) →
          S.card ≤ p.NΛ' Cpast CΓ CΓ' uFix) ∧
        (∀ (k : ℕ) (x : X),
          (anbRun p k).countSub x ≤ ((p.NΛ' Cpast CΓ CΓ' uFix * p.NΛ'' : ℕ) : ℕ∞) ∧
          (anbRun p k).countSup x ≤ ((p.NΛ' Cpast CΓ CΓ' uFix * p.NΛ'' : ℕ) : ℕ∞) ∧
          (anbRun p k).countHat x ≤ p.NΓ Cpast CΓ CΓ' uFix)) := by
  exact AnbComplexityProof.complexity hΛbd hΓbd hCpast hCΓ hCΓ' hΛmono hadd hmem hw hΓmono
    hΓcaus hΓadd hΓΛ hcmp hsub hα hρ0 hρ1 hτ hε hbd

end GuaranteedSubsol
