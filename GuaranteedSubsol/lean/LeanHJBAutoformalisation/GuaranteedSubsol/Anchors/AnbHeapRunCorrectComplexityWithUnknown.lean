/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AnbHeapCorrectComplexityProof

/-!
# Frozen statement: correctness and complexity of the ANB with sorted lists, unknown constants

Source: Theorem th:complexity_withUnknown and Prop. prop:complexity_lazy (Complexity.tex), combined
as in eq. eq:ln_N_eps (Intro.tex) (author's request, for the Palomar submission): the conclusions of
`anbHeapRun_correct_complexity` hold under the assumptions of `anbRun_complexity_withUnknown`
(`Φ_β` is `σ`-sub-additive for unknown constants `β ≥ α`, `0 < σ < 1` with
`(1 - σ)^β ≤ (1 - ρ)^α`; `ρ > 0` is not assumed), with the constants of `AnbParams.WithUnknown`.
The algorithm only uses the parameters `q.p`. `X` is finite and linearly ordered (tie-breaking).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem anbHeapRun_correct_complexity_withUnknown {X : Type*} [Fintype X] [LinearOrder X]
    {q : AnbParams.WithUnknown X} {𝒱 : X → Set X} {I : Set X} {ubd : X → ℝ}
    (hΛbd : ∀ u, ∀ x ∉ I, q.p.Λ u x = ubd x) (hΓbd : ∀ u, ∀ x ∉ I, q.p.Γ u x = ubd x)
    {Cpast CΓ CΓ' : ℝ} (hCpast : 0 ≤ Cpast) (hCΓ : 1 ≤ CΓ) (hCΓ' : 0 ≤ CΓ')
    (hΛmono : ∀ x, Monotone (q.p.Λ · x)) (hadd : ∀ x ∈ I, AdditivelyInvariant (q.p.Λ · x))
    (hmem : ∀ x ∈ I, HasMemory Cpast (q.p.Λ · x)) {w : X → ℝ} (hw : q.p.Λ w ≤ w)
    (hΓmono : ∀ x, Monotone (q.p.Γ · x)) (hΓcaus : ∀ x, Causal (q.p.Γ · x))
    (hΓadd : ∀ x ∈ I, AdditivelyInvariant (q.p.Γ · x)) (hΓΛ : ∀ u, q.p.Γ u ≤ q.p.Λ u)
    (hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (q.p.Λ · x) (q.p.Γ · x))
    (hst : Global.Ext.HasStencil 𝒱 (Global.monotoneExtension q.p.Γ))
    (hsub : ∀ x ∈ I, SubAdditive q.σ (kruzkovOp q.β (q.p.Λ · x))) (hα : 0 < q.p.α)
    (hαβ : q.p.α ≤ q.β) (hσ0 : 0 < q.σ) (hσ1 : q.σ < 1) (hρ1 : q.p.ρ < 1)
    (hρσ : (1 - q.σ) ^ q.β ≤ (1 - q.p.ρ) ^ q.p.α) (hτ : 0 < q.p.τ) (hε : 0 < q.p.ε)
    (hbd : ∀ x ∉ I, 2 * q.Δmax ≤ ubd x) :
    ∃ uFix : X → ℝ, q.p.Λ uFix = uFix ∧ (∀ v, q.p.Λ v = v → v = uFix) ∧
      (∀ J : Set X, HasComparisonPrinciple J q.p.Λ) ∧
      (q.p.ε ≤ q.εmax uFix →
        let run := anbHeapRunWith anbGlobalIter q.p 𝒱
        let data := anbHeapRunDataWith anbGlobalIter q.p 𝒱
        let K := anbHeapStopIndexWith anbGlobalIter q.p 𝒱
        let s := run K.toNat
        let nmax := ⌈q.nMax uFix⌉₊
        let NΛ' := q.NΛ' Cpast CΓ CΓ' uFix
        let NΓ := q.NΓ Cpast CΓ CΓ' uFix
        let card𝒱 := ∑ x, (Global.Ext.revStencil 𝒱 x).card
        K ≤ ((nmax + 1 : ℕ) : ℕ∞) ∧
        (s.uSub q.p.τ ≤ q.p.Λ (s.uSub q.p.τ) ∧
          Global.monotoneExtension q.p.Λ s.uSup ≤ s.uSup ∧
          ∀ x, s.uSup x ≤ (((1 + q.p.ε) * s.uSub q.p.τ x : ℝ) : WithTop ℝ)) ∧
        (∀ k, (data k).Δ < q.Δmax) ∧
        (∀ (x : X) (S : Finset ℕ), (∀ k ∈ S, x ∈ (data k).band) → S.card ≤ NΛ') ∧
        (∀ (k : ℕ) (x : X),
          (run k).countSub x ≤ ((NΛ' * q.NΛ'' : ℕ) : ℕ∞) ∧
          (run k).countSup x ≤ ((NΛ' * q.NΛ'' : ℕ) : ℕ∞) ∧
          (run k).dij.count x ≤ NΓ) ∧
        s.dij.evalCount ≤ Fintype.card X + card𝒱 * NΓ + (Fintype.card X + card𝒱) * NΛ' ∧
        s.dij.L.count + s.M.count + s.S.count + s.Sc.count ≤
          2 * Fintype.card X + 4 * (nmax + 1) + NΓ * (5 * Fintype.card X + card𝒱) +
            NΛ' * (12 * Fintype.card X + card𝒱)) := by
  exact AnbHeapCorrectComplexityProof.correct_complexity_withUnknown hΛbd hΓbd hCpast hCΓ hCΓ'
    hΛmono hadd hmem hw hΓmono hΓcaus hΓadd hΓΛ hcmp hst hsub hα hαβ hσ0 hσ1 hρ1 hρσ hτ hε hbd

end GuaranteedSubsol
