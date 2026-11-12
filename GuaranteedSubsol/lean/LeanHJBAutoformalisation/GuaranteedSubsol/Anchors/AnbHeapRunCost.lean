/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AnbHeapCostProof

/-!
# Frozen statement: cost accounting of the ANB with sorted lists

Source: Prop. prop:complexity_lazy (Complexity.tex), generic part (author's request), for
algo:anb_lazy with sorted lists (`anbHeapRunWith`, `AnbHeap.lean`) and any inner solver `S`. After
`K` iterations, with `N := #X`, `𝒱̃` the reversed stencils, `countB'(x)` the number of selections of
`x` in line anb_lazy:Dijkstra (line Dijkstra:accept; updates by Dijkstra's method, which only occur
in the bands `B'_n`; `anbHeapCountB'`) and `countB(x)` the number of iterations `k < K` with
`x ∈ B_k` (`anbHeapCountB`; names chosen by the author):
* the number of evaluations of `Γ` is at most `N + ∑ₓ countB'(x) #𝒱̃(x) + ∑ₓ countB(x) (1 + #𝒱̃(x))`
  (`N` evaluations to build `L`);
* the number of operations on the lists `L`, `M`, `S`, `Sc` is at most
  `2N + 4K + ∑ₓ countB'(x) (5 + #𝒱̃(x)) + ∑ₓ countB(x) (12 + #𝒱̃(x))` (`2N` to build `L` and
  `Sc`).
Hypotheses: those of `anbHeapRun_equiv` (`Γ` monotone, causal, with stencils `𝒱`, `α > 0`,
`τ > 0`). `X` is finite and linearly ordered (tie-breaking).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem anbHeapRun_cost {X : Type*} [Fintype X] [LinearOrder X] (S : AnbInnerSolver X)
    {p : AnbParams X} {𝒱 : X → Set X}
    (hst : Global.Ext.HasStencil 𝒱 (Global.monotoneExtension p.Γ))
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x)) (hα : 0 < p.α)
    (hτ : 0 < p.τ) (K : ℕ) :
    (anbHeapRunWith S p 𝒱 K).dij.evalCount ≤ Fintype.card X +
      ∑ x, anbHeapCountB' S p 𝒱 K x * (Global.Ext.revStencil 𝒱 x).card +
      ∑ x, anbHeapCountB S p 𝒱 K x * (1 + (Global.Ext.revStencil 𝒱 x).card) ∧
    (anbHeapRunWith S p 𝒱 K).dij.L.count + (anbHeapRunWith S p 𝒱 K).M.count +
      (anbHeapRunWith S p 𝒱 K).S.count + (anbHeapRunWith S p 𝒱 K).Sc.count ≤
      2 * Fintype.card X + 4 * K +
      ∑ x, anbHeapCountB' S p 𝒱 K x * (5 + (Global.Ext.revStencil 𝒱 x).card) +
      ∑ x, anbHeapCountB S p 𝒱 K x * (12 + (Global.Ext.revStencil 𝒱 x).card) := by
  exact AnbHeapCostProof.cost S hst hΓmono hΓcaus hα hτ K

end GuaranteedSubsol
