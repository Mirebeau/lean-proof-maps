/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.DijkstraProof

/-!
# Frozen statement: termination of the generalized Dijkstra algorithm at a fixed point

Source: Prop. prop:Dijkstra_correct (Complexity.tex): the algorithm terminates (`L_N = ∅`), here
within `N ≤ card X` iterations, and `u_* := u_N` is a fixed point of `Γ`. `X` is finite and
linearly ordered (tie-breaking). prop:Dijkstra_correct adds a stopping time `T`; these statements
are the case `T = ∞`, and imply the general case applied to `Γ^{<T}` (`dijkstraCutOp`).

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem dijkstraRun_fixedPoint {X : Type*} [LinearOrder X] [Finite X]
    {Γ : (X → WithTop ℝ) → X → WithTop ℝ} (hmono : Monotone Γ) (hcaus : ∀ x, Ext.Causal (Γ · x))
    {u₀ : X → WithTop ℝ} (hu₀ : Γ u₀ ≤ u₀) :
    ∃ N ≤ Nat.card X, Γ (dijkstraRun Γ u₀ N).u = (dijkstraRun Γ u₀ N).u := by
  exact DijkstraProof.fixedPoint hmono hcaus hu₀

end GuaranteedSubsol
