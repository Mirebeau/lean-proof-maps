/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.CpastFormulationProof

/-!
# Frozen statement: `C_past`-memory implies eq. (Lambda_max_u_t)

Source: Prop. prop:Cpast_formulation (Complexity.tex), direct implication, scalar form: if `Λ` is
monotone, additively invariant and has `C_past`-memory, then `Λ u = Λ max {u,t}` for all
`t ≤ Λ u - C_past`. The scalar operator `Λ : (X → ℝ) → ℝ` stands for `(Λ · x)`.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem HasMemory.apply_eq_apply_max {X : Type*} {Λ : (X → ℝ) → ℝ} {C : ℝ}
    (hmono : Monotone Λ) (hadd : AdditivelyInvariant Λ) (h : HasMemory C Λ)
    (u : X → ℝ) {t : ℝ} (ht : t ≤ Λ u - C) :
    Λ u = Λ (fun y => max (u y) t) := by
  exact CpastFormulationProof.apply_eq_apply_max hmono hadd h u ht

end GuaranteedSubsol
