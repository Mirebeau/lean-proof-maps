/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.Axioms
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Construction of `Γ` from `Λ`

The underestimating operator of Prop. prop:constr_Gamma (Intro.tex, eq. (constr_Gamma)),
in scalar form at an interior point `x ∈ Int X`.
-/

namespace GuaranteedSubsol

variable {X : Type*}

/-- The operator `Γ u := c + min_V u`, with `c := Λ[0]`, built from a scalar operator `Λ` and a
nonempty finite stencil `V` (Intro.tex eq. (constr_Gamma), at an interior point). -/
noncomputable def constrGamma (Λ : (X → ℝ) → ℝ) (V : Finset X) (hV : V.Nonempty)
    (u : X → ℝ) : ℝ :=
  Λ 0 + V.inf' hV u

end GuaranteedSubsol
