/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.CpastFormulationProof

/-!
# Frozen statement: eq. (Lambda_max_u_t) implies `C_past`-memory

Source: Prop. prop:Cpast_formulation (Complexity.tex), converse implication, scalar form: if `Λ` is
monotone, additively invariant, and `Λ u = Λ max {u,t}` for all `u` and `t ≤ Λ u - C_past`, then
`Λ` has `C_past`-memory. `X` is finite (the proof needs `u - n ε 1_{u ≤ t} ≤ v` for some `n`).
The scalar operator `Λ : (X → ℝ) → ℝ` stands for `(Λ · x)`.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem hasMemory_of_apply_eq_apply_max {X : Type*} [Finite X] {Λ : (X → ℝ) → ℝ} {C : ℝ}
    (hmono : Monotone Λ) (hadd : AdditivelyInvariant Λ)
    (h : ∀ (u : X → ℝ) (t : ℝ), t ≤ Λ u - C → Λ u = Λ (fun y => max (u y) t)) :
    HasMemory C Λ := by
  exact CpastFormulationProof.hasMemory_of_apply_eq_apply_max hmono hadd h

end GuaranteedSubsol
