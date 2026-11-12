/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.DijkstraProof

/-!
# Frozen statement: the generalized Dijkstra algorithm preserves super-solutions

Source: Prop. prop:Dijkstra_correct (Complexity.tex), eq. (Dijkstra_prop), first part:
`Γ u_n ≤ u_n` at each iteration, from `Γ u_0 ≤ u_0`. Only the monotonicity of `Γ` is needed.
prop:Dijkstra_correct adds a stopping time `T`; these statements are the case `T = ∞`, and
imply the general case applied to `Γ^{<T}` (`dijkstraCutOp`).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem dijkstraStep_superSolution {X : Type*} [LinearOrder X]
    {Γ : (X → WithTop ℝ) → X → WithTop ℝ} (hmono : Monotone Γ) {s : DijkstraState X}
    (hs : Γ s.u ≤ s.u) (n : ℕ) :
    Γ ((dijkstraStep Γ)^[n] s).u ≤ ((dijkstraStep Γ)^[n] s).u := by
  exact DijkstraProof.superSolution hmono hs n

end GuaranteedSubsol
