/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.ConstrGammaProof

/-!
# Frozen statement: the constructed underestimating operator is monotone

Source: Prop. prop:constr_Gamma (Intro.tex), monotonicity of `Γ u := Λ[0] + min_V u`
(eq. eqdef:constr_Gamma, at an interior point; the other properties are `constrGammaLoc`).

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem monotone_constrGamma {X : Type*} {Λ : (X → ℝ) → ℝ} {V : Finset X} (hV : V.Nonempty) :
    Monotone (constrGamma Λ V hV) := by
  exact ConstrGamma.monotone hV

end GuaranteedSubsol
