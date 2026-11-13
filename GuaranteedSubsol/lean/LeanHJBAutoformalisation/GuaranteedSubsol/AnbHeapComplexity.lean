/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.AnbHeapCostProof
public import LeanHJBAutoformalisation.GuaranteedSubsol.AnbComplexityProof
public import LeanHJBAutoformalisation.GuaranteedSubsol.AnbWithUnknownProof
public import LeanHJBAutoformalisation.GuaranteedSubsol.AnbAgsiProof

/-!
# Complexity of the ANB with sorted lists (prop:complexity_lazy): the three instances

Prop. prop:complexity_lazy (Complexity.tex) under the assumptions of Theorems th:complexity,
th:complexity_withUnknown and th:complexity_with_agsi (author's decision: ordinary theorems, not
frozen anchors). Each instance is the frozen `anbHeapRun_cost_le` (`AnbHeapCostProof.cost_le`) with
the uniform bounds of the corresponding complexity theorem: `countB' ≤ N_Γ` selections by
Dijkstra's method and `countB ≤ N'_Λ` iterations in the band per point, `N_Λ = N'_Λ N''_Λ` updates
per point by each inner loop, and `Kmax = ⌈n_max⌉ + 1` iterations. These bounds are transported
from the ANB to the ANB with sorted lists by `anbLazyRun_equiv` and `anbHeapRun_equiv`.

At termination (`AnbHeapCostBound`), with `N := #X` and `Ñ := ∑ₓ #𝒱̃(x)` (eq. eqdef:stencil_card):
* at most `2 N N'_Λ N''_Λ = 2 N N_Λ` evaluations of `Λ`;
* at most `N + Ñ N_Γ + (N + Ñ) N'_Λ` evaluations of `Γ` (`N` of them to build `L`);
* at most `2N + 4(⌈n_max⌉ + 1) + N_Γ (5N + Ñ) + N'_Λ (12N + Ñ)` operations on the lists `L`, `M`,
  `S`, `Sc` (`2N` of them to build `L` and `Sc`);
which is eq. eq:anb_cost, each operation on a list having cost `O(ln N)`. Not counted: the cost
`O(Ñ ln Ñ)` of the computation of the reversed stencils; the stopping test (`M` empty and `bot` of
`Sc`, two operations per iteration, covered by the term `O(n_max)`); the evaluations of `Λ` in the
final test of each inner loop (`countSub`, `countSup` count the updates, as in the paper).
-/

@[expose] public section

namespace GuaranteedSubsol

variable {X : Type*} [Fintype X] [LinearOrder X]

/-- The bounds of Prop. prop:complexity_lazy at termination of the ANB with sorted lists, with inner
solver `S`: at most `2 #X N_Λ` updates by the inner loops, `#X + Ñ N_Γ + (#X + Ñ) N'_Λ`
evaluations of `Γ`, and `2 #X + 4 Kmax + N_Γ (5 #X + Ñ) + N'_Λ (12 #X + Ñ)` operations on the
lists, `Ñ := ∑ₓ #𝒱̃(x)`. -/
def AnbHeapCostBound (S : AnbInnerSolver X) (p : AnbParams X) (𝒱 : X → Set X)
    (NΓ NΛ' NΛ Kmax : ℕ) : Prop :=
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
      NΛ' * (12 * Fintype.card X + ∑ x, (Global.Ext.revStencil 𝒱 x).card)

namespace AnbHeapComplexity

/-- The bounds of prop:complexity_lazy from uniform bounds on the ANB (`anbRunWith`). -/
theorem costBound_of_anb (S : AnbInnerSolver X) {p : AnbParams X} {𝒱 : X → Set X}
    (hst : Global.Ext.HasStencil 𝒱 (Global.monotoneExtension p.Γ))
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x)) (hα : 0 < p.α)
    (hτ : 0 < p.τ) (NΓ NΛ' NΛ Kmax : ℕ) (hacc : ∀ k x, (anbRunWith S p k).countHat x ≤ NΓ)
    (hband : ∀ (x : X) (T : Finset ℕ), (∀ k ∈ T, x ∈ (anbRunDataWith S p k).band) →
      T.card ≤ NΛ')
    (hsub : ∀ k x, (anbRunWith S p k).countSub x ≤ NΛ ∧ (anbRunWith S p k).countSup x ≤ NΛ)
    (hstop : anbStopIndexWith S p ≤ Kmax) :
    AnbHeapCostBound S p 𝒱 NΓ NΛ' NΛ Kmax := by
  obtain ⟨hH, hHstop⟩ := AnbHeapProof.equiv S hst hΓmono hΓcaus hα hτ
  obtain ⟨hL, hLstop⟩ := AnbLazyProof.equiv S hΓmono hΓcaus hα hτ.le
  refine AnbHeapCostProof.cost_le S hst hΓmono hΓcaus hα hτ NΓ NΛ' NΛ Kmax (fun k x => ?_)
    (fun K x => hband x _ fun k hk => ?_) (fun k x => ?_) (by rw [hHstop, hLstop]; exact hstop)
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hc, -⟩ := hH k
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hc'⟩ := hL k
    unfold anbHeapCountB'
    rw [hc, hc']
    exact hacc k x
  · obtain ⟨-, -, -, -, -, -, -, -, hb, -⟩ := hH k
    obtain ⟨-, -, -, -, -, -, -, -, -, hb', -⟩ := hL k
    have := (Finset.mem_filter.1 hk).2
    rw [← Finset.mem_coe, hb, hb'] at this
    exact this
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, hs, hs', -⟩ := hH k
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, ht, ht', -⟩ := hL k
    rw [hs, hs', ht, ht']
    exact hsub k x

end AnbHeapComplexity

/-- Prop. prop:complexity_lazy under the assumptions of Theorem th:complexity (the inner loops are
global iterations): `a = N_Γ`, `c = N'_Λ`, `d = N'_Λ N''_Λ`, `K₀ = ⌈n_max⌉ + 1`. -/
theorem anbHeapRun_complexity {p : AnbParams X} {𝒱 : X → Set X}
    (hst : Global.Ext.HasStencil 𝒱 (Global.monotoneExtension p.Γ))
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
      (p.ε ≤ p.εmax uFix →
        anbHeapStopIndexWith anbGlobalIter p 𝒱 ≤ ((⌈p.nMax uFix⌉₊ + 1 : ℕ) : ℕ∞) ∧
        AnbHeapCostBound anbGlobalIter p 𝒱 (p.NΓ Cpast CΓ CΓ' uFix) (p.NΛ' Cpast CΓ CΓ' uFix)
          (p.NΛ' Cpast CΓ CΓ' uFix * p.NΛ'') (⌈p.nMax uFix⌉₊ + 1)) := by
  obtain ⟨uFix, hfix, huniq, -, hcplx⟩ := AnbComplexityProof.complexity hΛbd hΓbd hCpast hCΓ hCΓ'
    hΛmono hadd hmem hw hΓmono hΓcaus hΓadd hΓΛ hcmp hsub hα hρ0 hρ1 hτ hε hbd
  refine ⟨uFix, hfix, huniq, fun hεmax => ?_⟩
  obtain ⟨hstop, -, -, -, hband, hcount⟩ := hcplx hεmax
  have hHstop := (AnbHeapProof.equiv anbGlobalIter hst hΓmono hΓcaus hα hτ).2
  have hLstop := (AnbLazyProof.equiv anbGlobalIter hΓmono hΓcaus hα hτ.le).2
  refine ⟨by rw [hHstop, hLstop]; exact hstop, ?_⟩
  exact AnbHeapComplexity.costBound_of_anb anbGlobalIter hst hΓmono hΓcaus hα hτ _ _ _ _
    (fun k x => (hcount k x).2.2) hband (fun k x => ⟨(hcount k x).1, (hcount k x).2.1⟩) hstop

/-- Prop. prop:complexity_lazy under the assumptions of Theorem th:complexity_withUnknown (unknown
`β`, `σ`; the constants of `AnbParams.WithUnknown`). -/
theorem anbHeapRun_complexity_withUnknown {q : AnbParams.WithUnknown X} {𝒱 : X → Set X}
    (hst : Global.Ext.HasStencil 𝒱 (Global.monotoneExtension q.p.Γ))
    {I : Set X} {ubd : X → ℝ}
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
      (q.p.ε ≤ q.εmax uFix →
        anbHeapStopIndexWith anbGlobalIter q.p 𝒱 ≤ ((⌈q.nMax uFix⌉₊ + 1 : ℕ) : ℕ∞) ∧
        AnbHeapCostBound anbGlobalIter q.p 𝒱 (q.NΓ Cpast CΓ CΓ' uFix) (q.NΛ' Cpast CΓ CΓ' uFix)
          (q.NΛ' Cpast CΓ CΓ' uFix * q.NΛ'') (⌈q.nMax uFix⌉₊ + 1)) := by
  obtain ⟨uFix, hfix, huniq, -, hcplx⟩ := AnbWithUnknownProof.complexity hΛbd hΓbd hCpast hCΓ
    hCΓ' hΛmono hadd hmem hw hΓmono hΓcaus hΓadd hΓΛ hcmp hsub hα hαβ hσ0 hσ1 hρ1 hρσ hτ hε hbd
  refine ⟨uFix, hfix, huniq, fun hεmax => ?_⟩
  obtain ⟨hstop, -, -, -, hband, hcount⟩ := hcplx hεmax
  have hHstop := (AnbHeapProof.equiv anbGlobalIter hst hΓmono hΓcaus hα hτ).2
  have hLstop := (AnbLazyProof.equiv anbGlobalIter hΓmono hΓcaus hα hτ.le).2
  refine ⟨by rw [hHstop, hLstop]; exact hstop, ?_⟩
  exact AnbHeapComplexity.costBound_of_anb anbGlobalIter hst hΓmono hΓcaus hα hτ _ _ _ _
    (fun k x => (hcount k x).2.2) hband (fun k x => ⟨(hcount k x).1, (hcount k x).2.1⟩) hstop

/-- Prop. prop:complexity_lazy under the assumptions of Theorem th:complexity_with_agsi (the inner
loops are parallel AGSI): `N''_Λ` is replaced by `AnbParams.NΛ''agsi`. -/
theorem anbHeapAgsiRun_complexity {p : AnbParams X} {𝒱 : X → Set X}
    (hst : Global.Ext.HasStencil 𝒱 (Global.monotoneExtension p.Γ))
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
      (p.ε ≤ p.εmax uFix →
        anbHeapStopIndexWith anbAgsi p 𝒱 ≤ ((⌈p.nMax uFix⌉₊ + 1 : ℕ) : ℕ∞) ∧
        AnbHeapCostBound anbAgsi p 𝒱 (p.NΓ Cpast CΓ CΓ' uFix) (p.NΛ' Cpast CΓ CΓ' uFix)
          (p.NΛ' Cpast CΓ CΓ' uFix * p.NΛ''agsi) (⌈p.nMax uFix⌉₊ + 1)) := by
  obtain ⟨uFix, hfix, huniq, -, hcplx⟩ := AnbAgsiProof.complexity hΛbd hΓbd hCpast hCΓ hCΓ'
    hΛmono hadd hmem hw hΓmono hΓcaus hΓadd hΓΛ hcmp hsub hα hρ0 hρ1 hτ hε hbd
  refine ⟨uFix, hfix, huniq, fun hεmax => ?_⟩
  obtain ⟨hstop, -, -, -, hband, hcount⟩ := hcplx hεmax
  have hHstop := (AnbHeapProof.equiv anbAgsi hst hΓmono hΓcaus hα hτ).2
  have hLstop := (AnbLazyProof.equiv anbAgsi hΓmono hΓcaus hα hτ.le).2
  refine ⟨by rw [hHstop, hLstop]; exact hstop, ?_⟩
  exact AnbHeapComplexity.costBound_of_anb anbAgsi hst hΓmono hΓcaus hα hτ _ _ _ _
    (fun k x => (hcount k x).2.2) hband (fun k x => ⟨(hcount k x).1, (hcount k x).2.1⟩) hstop

end GuaranteedSubsol
