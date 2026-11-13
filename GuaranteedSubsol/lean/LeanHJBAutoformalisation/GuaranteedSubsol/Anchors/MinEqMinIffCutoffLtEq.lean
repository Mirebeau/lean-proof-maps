/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.CutoffProof

/-!
# Frozen statement: `min {u,t} = min {v,t} ⇔ u^{<t} = v^{<t}`, scalar form

Source: Prop. prop:causal_formulation (Complexity.tex), first equivalence, with the cutoffs of
eq. eqdef:u_less_t, for scalar values
`a, b ∈ ℝ_∞` and a level `t ∈ ℝ`. The paper's statement for `u, v ∈ ℝ^X` follows by applying it
at every point.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem min_eq_min_iff_cutoffLt_eq (a b : WithTop ℝ) (t : ℝ) :
    min a t = min b t ↔ cutoffLt t a = cutoffLt t b := by
  exact CutoffProof.min_eq_min_iff_cutoffLt_eq a b t

end GuaranteedSubsol
