/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.CausalFixedPointProof

/-!
# Frozen statement: fixed point of a monotone causal operator with a super-solution

Source: Prop. prop:comp_of_causal (Complexity.tex), last claims (author's request):
Dijkstra's method started from a super-solution computes the unique fixed point
(Prop. prop:Dijkstra_correct), by the comparison principle for causal operators with `Int Y = X`:
if `Γ` is monotone and
causal (at every point) and `Γ w ≤ w` for some finite `w`, then `Γ` has a fixed point `u` which
lies above every sub-solution and below every super-solution; in particular `u` is the unique
fixed point, and `u ≤ w`. `X` is finite; no order on `X` is assumed.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem exists_fixedPoint_of_causal {X : Type*} [Finite X] {Γ : (X → ℝ) → X → ℝ}
    (hmono : ∀ x, Monotone (Γ · x)) (hcaus : ∀ x, Causal (Γ · x)) {w : X → ℝ} (hw : Γ w ≤ w) :
    ∃ u : X → ℝ, Γ u = u ∧ (∀ v, v ≤ Γ v → v ≤ u) ∧ (∀ v, Γ v ≤ v → u ≤ v) := by
  exact CausalFixedPointProof.exists_fixedPoint_of_causal hmono hcaus hw

end GuaranteedSubsol
