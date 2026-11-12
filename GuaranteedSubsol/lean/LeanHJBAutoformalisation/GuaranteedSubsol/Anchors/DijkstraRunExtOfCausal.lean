/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.DijkstraExtProof

/-!
# Frozen statement: generalized Dijkstra for the extension of a real causal scheme

Source: Prop. prop:Dijkstra_correct (Complexity.tex), for the extension
`Γ_∞ = Global.monotoneExtension Γ` of a real operator `Γ` that is monotone and causal at each point
(author's request): if `Γ_∞ u₀ ≤ u₀`, then each point is updated at most once, the updated points
are those whose value has decreased, and the algorithm reaches a fixed point of `Γ_∞` within
`card X` iterations. `X` is finite and linearly ordered (tie-breaking). prop:Dijkstra_correct
adds a stopping time `T`; these statements are the case `T = ∞`, and imply the general case applied
to `Γ^{<T}` (`dijkstraCutOp`).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem dijkstraRun_ext_of_causal {X : Type*} [LinearOrder X] [Finite X]
    {Γ : (X → ℝ) → X → ℝ} (hmono : ∀ x, Monotone (Γ · x)) (hcaus : ∀ x, Causal (Γ · x))
    {u₀ : X → WithTop ℝ} (hu₀ : Global.monotoneExtension Γ u₀ ≤ u₀) :
    (∀ n x, (dijkstraRun (Global.monotoneExtension Γ) u₀ n).count x ≤ 1 ∧
      ((dijkstraRun (Global.monotoneExtension Γ) u₀ n).count x = 1 ↔
        (dijkstraRun (Global.monotoneExtension Γ) u₀ n).u x < u₀ x)) ∧
    ∃ N ≤ Nat.card X, Global.monotoneExtension Γ (dijkstraRun (Global.monotoneExtension Γ) u₀ N).u =
      (dijkstraRun (Global.monotoneExtension Γ) u₀ N).u := by
  exact DijkstraExtProof.dijkstraRun_ext_of_causal hmono hcaus hu₀

end GuaranteedSubsol
