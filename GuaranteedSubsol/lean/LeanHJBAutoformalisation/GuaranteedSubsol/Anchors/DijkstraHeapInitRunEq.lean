/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.DijkstraHeapProof

/-!
# Frozen statement: Dijkstra's method with a sorted list, from scratch

Source: algo:Dijkstra (Complexity.tex) with the sorted list `L` (its invariant is eq.
eq:Dijkstra_prop, right) stored in an ordered partial map (Papers/OrderedPartialMap, author's
request), started from scratch (`dijkstraHeapInit`: `L` filled with the keys of all the points)
and with the stopping time `T = ∞` (`⊤`) of algo:Dijkstra:
after `n` iterations, the map `u` and the acceptance counts coincide with those of algo:Dijkstra
(`dijkstraRun`), the list holds the keys of the active points, the number of evaluations of `Γ` is
`#X + ∑ₓ count(x) · #𝒱̃(x)` and the number of operations on `L` is
`#X + n + ∑ₓ count(x) · (1 + #𝒱̃(x))`, where `𝒱̃` is the reversed stencil. The only hypothesis is
the stencil property of `Γ`. `X` is finite and linearly ordered (tie-breaking).

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem dijkstraHeapInit_run_eq {X : Type*} [Fintype X] [LinearOrder X]
    {Γ : (X → WithTop ℝ) → X → WithTop ℝ} {𝒱 : X → Set X} (hst : Global.Ext.HasStencil 𝒱 Γ)
    (u₀ : X → WithTop ℝ) (n : ℕ) :
    (dijkstraHeapRun Γ 𝒱 ⊤ (dijkstraHeapInit Γ u₀) n).u = (dijkstraRun Γ u₀ n).u ∧
    (dijkstraHeapRun Γ 𝒱 ⊤ (dijkstraHeapInit Γ u₀) n).count = (dijkstraRun Γ u₀ n).count ∧
    (dijkstraHeapRun Γ 𝒱 ⊤ (dijkstraHeapInit Γ u₀) n).L.v =
      dijkstraKey Γ (dijkstraHeapRun Γ 𝒱 ⊤ (dijkstraHeapInit Γ u₀) n).u ∧
    (dijkstraHeapRun Γ 𝒱 ⊤ (dijkstraHeapInit Γ u₀) n).evalCount = Fintype.card X +
      ∑ x, (dijkstraRun Γ u₀ n).count x * (Global.Ext.revStencil 𝒱 x).card ∧
    (dijkstraHeapRun Γ 𝒱 ⊤ (dijkstraHeapInit Γ u₀) n).L.count = Fintype.card X + n +
      ∑ x, (dijkstraRun Γ u₀ n).count x * (1 + (Global.Ext.revStencil 𝒱 x).card) := by
  exact DijkstraHeapProof.init_run_spec hst u₀ n

end GuaranteedSubsol
