/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.CutoffLeProof

/-!
# Frozen statement: `(∃ δ > 0, min {u,t+δ} = min {v,t+δ}) ⇔ u^{≤t} = v^{≤t}`, scalar form

Source: Prop. prop:causal_formulation (Complexity.tex), second equivalence ("Likewise ..."), for
scalar values `a, b ∈ ℝ_∞` and a level `t ∈ ℝ`. In the scalar form `δ` may depend on `a, b`; the
paper's statement for `u, v ∈ ℝ^X` (a single `δ` for all points) additionally needs `X` finite.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem exists_min_eq_min_iff_cutoffLe_eq (a b : WithTop ℝ) (t : ℝ) :
    (∃ δ > (0 : ℝ), min a ((t + δ : ℝ) : WithTop ℝ) = min b ((t + δ : ℝ) : WithTop ℝ)) ↔
      cutoffLe t a = cutoffLe t b := by
  exact CutoffLeProof.exists_min_eq_min_iff_cutoffLe_eq a b t

end GuaranteedSubsol
