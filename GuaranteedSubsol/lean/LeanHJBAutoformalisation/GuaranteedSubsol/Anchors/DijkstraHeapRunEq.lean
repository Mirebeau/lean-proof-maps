/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.DijkstraHeapProof

/-!
# Frozen statement: Dijkstra's method with a sorted list and a threshold

Source: algo:Dijkstra (Complexity.tex) with the sorted list `L` (its invariant is eq.
eq:Dijkstra_prop, right) stored in an ordered partial map (Papers/OrderedPartialMap, author's
request; `dijkstraHeapRun`), with the stencils `𝒱` of eq. eqdef:stencil and the stopping time `T`
of algo:Dijkstra (V1: the method stops when the smallest key is `≥ T`, as needed in the ANB).
Starting from any state whose list holds the keys of the active points (`L.v = dijkstraKey Γ u`, as
in the ANB where `L` is given), after `n` iterations: the map `u` and the acceptance counts coincide
with those of algo:Dijkstra without stopping time (`dijkstraRun`) applied to `Γ^{<T}`
(`dijkstraCutOp`; `Γ^{<⊤} = Γ`), as in the proof of Prop. prop:Dijkstra_correct; the list still
holds the keys of the active points; the number of evaluations of `Γ` has increased by
`∑ₓ count(x) · #𝒱̃(x)`, and the number of operations on `L` by `n + ∑ₓ count(x) · (1 + #𝒱̃(x))`,
where `count` is the number of acceptances in algo:Dijkstra and `𝒱̃` the reversed stencil (author's
ruling: two separate counters). The only hypothesis is the stencil property of `Γ`. `X` is finite
and linearly ordered (tie-breaking).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem dijkstraHeapRun_eq {X : Type*} [Fintype X] [LinearOrder X]
    {Γ : (X → WithTop ℝ) → X → WithTop ℝ} {𝒱 : X → Set X} (hst : Global.Ext.HasStencil 𝒱 Γ)
    (T : WithTop ℝ) (s₀ : DijkstraHeapState X) (hL : s₀.L.v = dijkstraKey Γ s₀.u) (n : ℕ) :
    (dijkstraHeapRun Γ 𝒱 T s₀ n).u = (dijkstraRun (dijkstraCutOp T Γ) s₀.u n).u ∧
    (dijkstraHeapRun Γ 𝒱 T s₀ n).count =
      s₀.count + (dijkstraRun (dijkstraCutOp T Γ) s₀.u n).count ∧
    (dijkstraHeapRun Γ 𝒱 T s₀ n).L.v = dijkstraKey Γ (dijkstraHeapRun Γ 𝒱 T s₀ n).u ∧
    (dijkstraHeapRun Γ 𝒱 T s₀ n).evalCount = s₀.evalCount +
      ∑ x, (dijkstraRun (dijkstraCutOp T Γ) s₀.u n).count x * (Global.Ext.revStencil 𝒱 x).card ∧
    (dijkstraHeapRun Γ 𝒱 T s₀ n).L.count = s₀.L.count + n +
      ∑ x, (dijkstraRun (dijkstraCutOp T Γ) s₀.u n).count x *
        (1 + (Global.Ext.revStencil 𝒱 x).card) := by
  exact DijkstraHeapProof.run_spec hst T s₀ hL n

end GuaranteedSubsol
