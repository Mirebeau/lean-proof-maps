/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.DijkstraProof

/-!
# Frozen statement: each point is updated at most once by the generalized Dijkstra algorithm

Source: Prop. prop:Dijkstra_correct (Complexity.tex): for `Γ` causal on `ℝ_∞`, the selected
points `(x_n)` are pairwise distinct, i.e. each point is updated at most once. `X` is linearly
ordered (tie-breaking).
Author ruling: the paper's assumptions that `Γ` is monotone, that `Γ u_0 ≤ u_0` and that `X` is
finite are dropped, being unneeded here (they are used for termination at a fixed point).
prop:Dijkstra_correct adds a stopping time `T`; these statements are the case `T = ∞`, and
imply the general case applied to `Γ^{<T}` (`dijkstraCutOp`).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem dijkstraRun_count_le_one {X : Type*} [LinearOrder X]
    {Γ : (X → WithTop ℝ) → X → WithTop ℝ} (hcaus : ∀ x, Ext.Causal (Γ · x))
    (u₀ : X → WithTop ℝ) (n : ℕ) (x : X) :
    (dijkstraRun Γ u₀ n).count x ≤ 1 := by
  exact DijkstraProof.count_le_one hcaus u₀ n x

end GuaranteedSubsol
