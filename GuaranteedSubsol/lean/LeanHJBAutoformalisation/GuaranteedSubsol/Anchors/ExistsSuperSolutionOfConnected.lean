/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.StencilDistProof

/-!
# Frozen statement: existence of a super-solution when the stencils reach the boundary

Source: Prop. prop:constr_Gamma (Intro.tex), "admits a super-solution if the stencils are
connected to the boundary" (footnote), global form with Dirichlet data `Λ u = u_bd` outside the
interior `I`, under `C_past`-dependency with `C_past ≥ 0`. The paper's other assumptions
(monotonicity, additive invariance, `Λ[0] ≥ δ`) are not needed. `X` is finite.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem exists_superSolution_of_connected {X : Type*} [Finite X] {Λ : (X → ℝ) → X → ℝ}
    {I : Set X} {ubd : X → ℝ} (hbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) {V : X → Set X} {Cpast : ℝ}
    (hCpast : 0 ≤ Cpast) (hdep : ∀ x ∈ I, HasDependency Cpast (V x) (Λ · x))
    (hconn : ∀ x ∈ I, ∃ z ∉ I, Relation.TransGen (fun a b => a ∈ I ∧ b ∈ V a) x z) :
    ∃ u : X → ℝ, Λ u ≤ u := by
  exact StencilDistProof.exists_superSolution_of_connected hbd hCpast hdep hconn

end GuaranteedSubsol
