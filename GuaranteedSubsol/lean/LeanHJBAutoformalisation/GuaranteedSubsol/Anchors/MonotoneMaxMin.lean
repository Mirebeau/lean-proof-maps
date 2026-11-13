/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.MaxMinMonCausalProof

/-!
# Frozen statement: monotonicity of `max {ū, min {T, Γ}}`

Source: Lemma lem:max_min_mon_causal (Complexity.tex), monotone part, scalar form: if `Γ` is
monotone, so is `u ↦ max {c, min {T, Γ u}}`, where `c` stands for `ū (x)`. The scalar operator
`Γ : (X → ℝ) → ℝ` stands for `(Γ · x)`.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem monotone_max_min {X : Type*} {Γ : (X → ℝ) → ℝ} (hmono : Monotone Γ) (c T : ℝ) :
    Monotone (fun u => max c (min T (Γ u))) := by
  exact MaxMinMonCausalProof.monotone_max_min hmono c T

end GuaranteedSubsol
