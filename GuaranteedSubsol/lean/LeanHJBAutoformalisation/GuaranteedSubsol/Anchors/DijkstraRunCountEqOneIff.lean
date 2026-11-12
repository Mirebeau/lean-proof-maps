/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.DijkstraProof

/-!
# Frozen statement: the points updated by the generalized Dijkstra algorithm

Source: Prop. prop:Dijkstra_correct (Complexity.tex), last statement
`{x_0, …, x_{N-1}} = {x | u_*(x) < u_0(x)}`, stated at every iteration `n`: a point has been
updated iff its value has decreased. `X` is linearly ordered (tie-breaking).
Author ruling: the paper's assumptions that `Γ` is monotone, that `Γ u_0 ≤ u_0` and that `X` is
finite are dropped, being unneeded here (they are used for termination at a fixed point).
V1 prop:Dijkstra_correct adds a stopping time `T`; these statements are the case `T = ∞`, and
imply the general case applied to `Γ^{<T}` (`dijkstraCutOp`).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem dijkstraRun_count_eq_one_iff {X : Type*} [LinearOrder X]
    {Γ : (X → WithTop ℝ) → X → WithTop ℝ} (hcaus : ∀ x, Ext.Causal (Γ · x))
    (u₀ : X → WithTop ℝ) (n : ℕ) (x : X) :
    (dijkstraRun Γ u₀ n).count x = 1 ↔
      (dijkstraRun Γ u₀ n).u x < u₀ x := by
  exact DijkstraProof.count_eq_one_iff hcaus u₀ n x

end GuaranteedSubsol
