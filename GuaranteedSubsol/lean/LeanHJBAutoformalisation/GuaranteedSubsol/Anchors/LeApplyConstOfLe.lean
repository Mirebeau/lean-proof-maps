/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.CstSubsolProof

/-!
# Frozen statement: constants below the boundary data are sub-solutions (`Γ ≤ Λ` case)

Source: Prop. prop:cst_subsol (Intro.tex), eq. eq:cst_subsol, second case: if `Γ[0] ≥ 0` and
`Γ ≤ Λ`, then `t ≤ Λ[t]` and `t ≤ Γ[t]` for all `t ≤ min u_bd`. `Γ` is additively invariant on
`Int X = I` and equal to `u_bd` on `∂X` (the additive invariance of `Λ` is not used).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem le_apply_const_of_le {X : Type*} {Λ Γ : (X → ℝ) → X → ℝ} {I : Set X} {ubd : X → ℝ}
    (hΓbd : ∀ u, ∀ x ∉ I, Γ u x = ubd x) (hΓadd : ∀ x ∈ I, AdditivelyInvariant (Γ · x))
    (hΓΛ : ∀ u, Γ u ≤ Λ u) (hΓ0 : ∀ x ∈ I, 0 ≤ Γ 0 x) {t : ℝ} (ht : ∀ x ∉ I, t ≤ ubd x)
    (x : X) : t ≤ Λ (fun _ => t) x ∧ t ≤ Γ (fun _ => t) x := by
  exact CstSubsolProof.le_apply_const_of_le hΓbd hΓadd hΓΛ hΓ0 ht x

end GuaranteedSubsol
