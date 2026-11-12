/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.MaxMinMonCausalProof

/-!
# Frozen statement: causality of `max {ū, min {T, Γ}}`

Source: Lemma lem:max_min_mon_causal (Complexity.tex), causal part, scalar form: if `Γ` is causal,
so is `u ↦ max {c, min {T, Γ u}}`, where `c` stands for `ū (x)`. The scalar operator
`Γ : (X → ℝ) → ℝ` stands for `(Γ · x)`.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem Causal.max_min {X : Type*} {Γ : (X → ℝ) → ℝ} (hcaus : Causal Γ) (c T : ℝ) :
    Causal (fun u => max c (min T (Γ u))) := by
  exact MaxMinMonCausalProof.causal_max_min hcaus c T

end GuaranteedSubsol
