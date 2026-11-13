/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.AnbHeapCostProof

/-!
# Frozen statement: complexity of the ANB with sorted lists under uniform bounds

Source: Prop. prop:complexity_lazy (Complexity.tex), eq. eq:anb_cost, from uniform bounds
(author's request; the instances for Theorems th:complexity, th:complexity_withUnknown and
th:complexity_with_agsi are in `AnbHeapComplexity.lean`). For algo:anb_lazy with sorted lists and
any inner solver `S`: if `countB' ≤ N_Γ` (selections by Dijkstra's method, `anbHeapCountB'`),
`countB ≤ N'_Λ` (iterations in the band, `anbHeapCountB`), each point is updated at most `N_Λ`
times by each of the two inner loops (in total, `N_Λ = N'_Λ N''_Λ` in the instances), and the method
stops within `Kmax` iterations (`⌈n_max⌉ + 1`), then at termination, with `N := #X` and
`Ñ := ∑ₓ #𝒱̃(x)` (eq. eqdef:stencil_card): at most `2 N N_Λ` updates by the inner loops (evaluations
of `Λ`), at most `N + Ñ N_Γ + (N + Ñ) N'_Λ` evaluations of `Γ`, and at most
`2N + 4 Kmax + N_Γ (5N + Ñ) + N'_Λ (12N + Ñ)` operations on the lists `L`, `M`, `S`, `Sc`, each of
cost `O(ln N)`. The cost `O(Ñ ln Ñ)` of the reversed stencils is not modelled. Names chosen by the
author.
Hypotheses: those of `anbHeapRun_equiv`. `X` is finite and linearly ordered (tie-breaking).

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem anbHeapRun_cost_le {X : Type*} [Fintype X] [LinearOrder X] (S : AnbInnerSolver X)
    {p : AnbParams X} {𝒱 : X → Set X}
    (hst : Global.Ext.HasStencil 𝒱 (Global.monotoneExtension p.Γ))
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x)) (hα : 0 < p.α)
    (hτ : 0 < p.τ) (NΓ NΛ' NΛ Kmax : ℕ) (hcountB' : ∀ K x, anbHeapCountB' S p 𝒱 K x ≤ NΓ)
    (hcountB : ∀ K x, anbHeapCountB S p 𝒱 K x ≤ NΛ')
    (hcountΛ : ∀ K x, (anbHeapRunWith S p 𝒱 K).countSub x ≤ NΛ ∧
      (anbHeapRunWith S p 𝒱 K).countSup x ≤ NΛ)
    (hstop : anbHeapStopIndexWith S p 𝒱 ≤ Kmax) :
    ∑ x, ((anbHeapRunWith S p 𝒱 (anbHeapStopIndexWith S p 𝒱).toNat).countSub x +
        (anbHeapRunWith S p 𝒱 (anbHeapStopIndexWith S p 𝒱).toNat).countSup x) ≤
      ((2 * Fintype.card X * NΛ : ℕ) : ℕ∞) ∧
    (anbHeapRunWith S p 𝒱 (anbHeapStopIndexWith S p 𝒱).toNat).dij.evalCount ≤
      Fintype.card X + (∑ x, (Global.Ext.revStencil 𝒱 x).card) * NΓ +
        (Fintype.card X + ∑ x, (Global.Ext.revStencil 𝒱 x).card) * NΛ' ∧
    (anbHeapRunWith S p 𝒱 (anbHeapStopIndexWith S p 𝒱).toNat).dij.L.count +
      (anbHeapRunWith S p 𝒱 (anbHeapStopIndexWith S p 𝒱).toNat).M.count +
      (anbHeapRunWith S p 𝒱 (anbHeapStopIndexWith S p 𝒱).toNat).S.count +
      (anbHeapRunWith S p 𝒱 (anbHeapStopIndexWith S p 𝒱).toNat).Sc.count ≤
      2 * Fintype.card X + 4 * Kmax +
        NΓ * (5 * Fintype.card X + ∑ x, (Global.Ext.revStencil 𝒱 x).card) +
        NΛ' * (12 * Fintype.card X + ∑ x, (Global.Ext.revStencil 𝒱 x).card) := by
  exact AnbHeapCostProof.cost_le S hst hΓmono hΓcaus hα hτ NΓ NΛ' NΛ Kmax hcountB' hcountB
    hcountΛ hstop

end GuaranteedSubsol
