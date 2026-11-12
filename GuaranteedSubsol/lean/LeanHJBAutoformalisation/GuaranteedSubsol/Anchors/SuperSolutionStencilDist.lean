/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.StencilDistProof

/-!
# Frozen statement: an explicit super-solution, from the distance to the boundary

Source: proof of Prop. prop:constr_Gamma (Effective.tex), "Construction of a super-solution to
`Λ`", global form with Dirichlet data `Λ u = u_bd` outside the interior `I`: if
`Λ u(x) ≤ C_past + u(y)` for all `y ∈ V(x)` at interior points (`C_past`-dependency, with
`C_past ≥ 0`) and the stencils are connected to the boundary (footnote of prop:constr_Gamma),
then `C_past d_V(x, ∂X) + M` is a super-solution for any `M ≥ u_bd`. The paper's other
assumptions (monotonicity, additive invariance, `Λ[0] ≥ δ`) are not needed.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem superSolution_stencilDist {X : Type*} {Λ : (X → ℝ) → X → ℝ} {I : Set X} {ubd : X → ℝ}
    (hbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) {V : X → Set X} {Cpast M : ℝ} (hCpast : 0 ≤ Cpast)
    (hM : ∀ x ∉ I, ubd x ≤ M) (hdep : ∀ x ∈ I, HasDependency Cpast (V x) (Λ · x))
    (hconn : ∀ x ∈ I, ∃ z ∉ I, Relation.TransGen (fun a b => a ∈ I ∧ b ∈ V a) x z) :
    Λ (fun x => Cpast * stencilDist I V x + M) ≤ fun x => Cpast * stencilDist I V x + M := by
  exact StencilDistProof.superSolution_stencilDist hbd hCpast hM hdep hconn

end GuaranteedSubsol
