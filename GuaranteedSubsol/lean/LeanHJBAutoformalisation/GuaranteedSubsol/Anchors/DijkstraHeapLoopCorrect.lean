/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.DijkstraHeapCorrectProof

/-!
# Frozen statement: Dijkstra's method with a sorted list and a stopping time

Source: Prop. prop:Dijkstra_correct and algo:Dijkstra (Complexity.tex), for the while loop
with the sorted list `L` and the stopping time `T ∈ ℝ_∞` (`dijkstraHeapLoop`; author's request
2026-10-20). Hypotheses: `Γ : ℝ_∞^X → ℝ_∞^X` monotone and causal, with stencils `𝒱`; the initial
`u` satisfies `(Γ u)^{<T} ≤ u`; `L` holds the keys of the active points,
`L = {(Γ u(x), x) | Γ u(x) < u(x)}` (eq. eq:Dijkstra_prop). Conclusions: the loop stops (the stop
index, in `ℕ∞`, is finite) after at most `#X` acceptances, one per point where `u` decreased
(re-frozen 2026-10-20, author's approval: stop index in `ℕ∞`); `u` is then a fixed point of
`Γ^{<T}` (`dijkstraCutOp`); `L` still holds the keys of the active points, and all of them are
`≥ T`; each point is accepted at most once, exactly where `u` decreased; the evaluations of `Γ`
and the operations on `L`. This is the form used in the ANB with sorted lists
(`anbHeapRun_equiv`). `X` is finite and linearly ordered (tie-breaking).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem dijkstraHeapLoop_correct {X : Type*} [Fintype X] [LinearOrder X]
    {Γ : (X → WithTop ℝ) → X → WithTop ℝ} {𝒱 : X → Set X} (hst : Global.Ext.HasStencil 𝒱 Γ)
    (hmono : Monotone Γ) (hcaus : ∀ x, Ext.Causal (Γ · x)) (T : WithTop ℝ)
    (s₀ : DijkstraHeapState X) (hL : s₀.L.v = dijkstraKey Γ s₀.u)
    (hsup : dijkstraCutOp T Γ s₀.u ≤ s₀.u) :
    dijkstraHeapStopIndex Γ 𝒱 T s₀ ≤ Fintype.card X ∧
    dijkstraHeapStopIndex Γ 𝒱 T s₀ =
      ((∑ x, ((dijkstraHeapLoop Γ 𝒱 T s₀).count x - s₀.count x) : ℕ) : ℕ∞) ∧
    dijkstraCutOp T Γ (dijkstraHeapLoop Γ 𝒱 T s₀).u = (dijkstraHeapLoop Γ 𝒱 T s₀).u ∧
    (dijkstraHeapLoop Γ 𝒱 T s₀).L.v = dijkstraKey Γ (dijkstraHeapLoop Γ 𝒱 T s₀).u ∧
    (∀ y t, (dijkstraHeapLoop Γ 𝒱 T s₀).L.v y = some t → T ≤ t) ∧
    (∀ x, (dijkstraHeapLoop Γ 𝒱 T s₀).count x ≤ s₀.count x + 1 ∧
      ((dijkstraHeapLoop Γ 𝒱 T s₀).count x = s₀.count x + 1 ↔
        (dijkstraHeapLoop Γ 𝒱 T s₀).u x < s₀.u x)) ∧
    (dijkstraHeapLoop Γ 𝒱 T s₀).evalCount = s₀.evalCount +
      ∑ x, ((dijkstraHeapLoop Γ 𝒱 T s₀).count x - s₀.count x) * (Global.Ext.revStencil 𝒱 x).card ∧
    (dijkstraHeapLoop Γ 𝒱 T s₀).L.count = s₀.L.count + 1 +
      ∑ x, ((dijkstraHeapLoop Γ 𝒱 T s₀).count x - s₀.count x) *
        (2 + (Global.Ext.revStencil 𝒱 x).card) := by
  exact DijkstraHeapCorrectProof.loop_correct hst hmono hcaus T s₀ hL hsup

end GuaranteedSubsol
