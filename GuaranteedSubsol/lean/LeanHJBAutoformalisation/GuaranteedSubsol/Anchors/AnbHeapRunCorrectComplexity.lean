/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AnbHeapCorrectComplexityProof

/-!
# Frozen statement: correctness and complexity of the ANB with sorted lists (algo:anb_lazy)

Source: Theorem th:complexity and Prop. prop:complexity_lazy (Complexity.tex), combined as in
eq. eq:ln_N_eps (Intro.tex): the complexity of algo:anb implemented as algo:anb_lazy (author's
request, for the Palomar submission). Under the assumptions of `anbRun_complexity`, with stencils
`𝒱` of `Γ_∞` (`hst`, eq. eqdef:stencil): `Λ` has a unique fixed point `u_*` and satisfies the
comparison principle; and if `ε ≤ ε_max`, the ANB with sorted lists `L`, `M`, `S`, `Sc`
(`anbHeapRunWith anbGlobalIter`) stops within `⌈n_max⌉₊` iterations (the iteration `0` is vacuous,
hence the bound `⌈n_max⌉₊ + 1` on the stopping index), producing a sub-solution
`ū := ũ^{⋄→(n-1)τ}` (`uSub τ`) and a super-solution `u̲` with `u̲ ≤ (1 + ε) ū`; in every iteration
`Δ_n < Δ_max`; any point lies in at most `N'_Λ` narrow bands; at every point there are at most
`N'_Λ N''_Λ` updates of `ū` and of `u̲` and at most `N_Γ` acceptances by Dijkstra's method; and at
termination, with `N := #X` and `Ñ := ∑ₓ #𝒱̃(x)` (eq. eqdef:stencil_card), at most
`N + Ñ N_Γ + (N + Ñ) N'_Λ` evaluations of `Γ` and at most
`2N + 4(⌈n_max⌉₊ + 1) + N_Γ (5N + Ñ) + N'_Λ (12N + Ñ)` operations on the lists (eq. eq:anb_cost).
`X` is finite and linearly ordered (tie-breaking).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem anbHeapRun_correct_complexity {X : Type*} [Fintype X] [LinearOrder X] {p : AnbParams X}
    {𝒱 : X → Set X} {I : Set X} {ubd : X → ℝ} (hΛbd : ∀ u, ∀ x ∉ I, p.Λ u x = ubd x)
    (hΓbd : ∀ u, ∀ x ∉ I, p.Γ u x = ubd x) {Cpast CΓ CΓ' : ℝ} (hCpast : 0 ≤ Cpast)
    (hCΓ : 1 ≤ CΓ) (hCΓ' : 0 ≤ CΓ') (hΛmono : ∀ x, Monotone (p.Λ · x))
    (hadd : ∀ x ∈ I, AdditivelyInvariant (p.Λ · x)) (hmem : ∀ x ∈ I, HasMemory Cpast (p.Λ · x))
    {w : X → ℝ} (hw : p.Λ w ≤ w) (hΓmono : ∀ x, Monotone (p.Γ · x))
    (hΓcaus : ∀ x, Causal (p.Γ · x)) (hΓadd : ∀ x ∈ I, AdditivelyInvariant (p.Γ · x))
    (hΓΛ : ∀ u, p.Γ u ≤ p.Λ u) (hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (p.Λ · x) (p.Γ · x))
    (hst : Global.Ext.HasStencil 𝒱 (Global.monotoneExtension p.Γ))
    (hsub : ∀ x ∈ I, SubAdditive p.ρ (kruzkovOp p.α (p.Λ · x))) (hα : 0 < p.α)
    (hρ0 : 0 < p.ρ) (hρ1 : p.ρ < 1) (hτ : 0 < p.τ) (hε : 0 < p.ε)
    (hbd : ∀ x ∉ I, 2 * p.Δmax ≤ ubd x) :
    ∃ uFix : X → ℝ, p.Λ uFix = uFix ∧ (∀ v, p.Λ v = v → v = uFix) ∧
      (∀ J : Set X, HasComparisonPrinciple J p.Λ) ∧
      (p.ε ≤ p.εmax uFix →
        let run := anbHeapRunWith anbGlobalIter p 𝒱
        let data := anbHeapRunDataWith anbGlobalIter p 𝒱
        let K := anbHeapStopIndexWith anbGlobalIter p 𝒱
        let s := run K.toNat
        let nmax := ⌈p.nMax uFix⌉₊
        let NΛ' := p.NΛ' Cpast CΓ CΓ' uFix
        let NΓ := p.NΓ Cpast CΓ CΓ' uFix
        let card𝒱 := ∑ x, (Global.Ext.revStencil 𝒱 x).card
        K ≤ ((nmax + 1 : ℕ) : ℕ∞) ∧
        (s.uSub p.τ ≤ p.Λ (s.uSub p.τ) ∧ Global.monotoneExtension p.Λ s.uSup ≤ s.uSup ∧
          ∀ x, s.uSup x ≤ (((1 + p.ε) * s.uSub p.τ x : ℝ) : WithTop ℝ)) ∧
        (∀ k, (data k).Δ < p.Δmax) ∧
        (∀ (x : X) (S : Finset ℕ), (∀ k ∈ S, x ∈ (data k).band) → S.card ≤ NΛ') ∧
        (∀ (k : ℕ) (x : X),
          (run k).countSub x ≤ ((NΛ' * p.NΛ'' : ℕ) : ℕ∞) ∧
          (run k).countSup x ≤ ((NΛ' * p.NΛ'' : ℕ) : ℕ∞) ∧
          (run k).dij.count x ≤ NΓ) ∧
        s.dij.evalCount ≤ Fintype.card X + card𝒱 * NΓ + (Fintype.card X + card𝒱) * NΛ' ∧
        s.dij.L.count + s.M.count + s.S.count + s.Sc.count ≤
          2 * Fintype.card X + 4 * (nmax + 1) + NΓ * (5 * Fintype.card X + card𝒱) +
            NΛ' * (12 * Fintype.card X + card𝒱)) := by
  exact AnbHeapCorrectComplexityProof.correct_complexity hΛbd hΓbd hCpast hCΓ hCΓ' hΛmono hadd hmem
    hw hΓmono hΓcaus hΓadd hΓΛ hcmp hst hsub hα hρ0 hρ1 hτ hε hbd

end GuaranteedSubsol
