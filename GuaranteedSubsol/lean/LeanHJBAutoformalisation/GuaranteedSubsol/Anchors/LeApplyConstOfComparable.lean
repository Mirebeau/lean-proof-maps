/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.CstSubsolProof

/-!
# Frozen statement: constants below the boundary data are sub-solutions (comparison case)

Source: Prop. prop:cst_subsol (Intro.tex, V1), eq. eq:cst_subsol, first case: if `Λ[0] ≥ 0` and
`C_Γ, C'_Γ`-comparison holds (only its upper inequality is used), then `t ≤ Λ[t]` and `t ≤ Γ[t]`
for all `t ≤ min u_bd`. The operators are additively invariant on `Int X = I` and equal to `u_bd`
on `∂X`; `C_Γ > 0`.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem le_apply_const_of_comparable {X : Type*} {Λ Γ : (X → ℝ) → X → ℝ} {I : Set X}
    {ubd : X → ℝ} (hΛbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) (hΓbd : ∀ u, ∀ x ∉ I, Γ u x = ubd x)
    (hΛadd : ∀ x ∈ I, AdditivelyInvariant (Λ · x)) (hΓadd : ∀ x ∈ I, AdditivelyInvariant (Γ · x))
    {CΓ CΓ' : ℝ} (hCΓ : 0 < CΓ) (hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (Λ · x) (Γ · x))
    (hΛ0 : ∀ x ∈ I, 0 ≤ Λ 0 x) {t : ℝ} (ht : ∀ x ∉ I, t ≤ ubd x) (x : X) :
    t ≤ Λ (fun _ => t) x ∧ t ≤ Γ (fun _ => t) x := by
  exact CstSubsolProof.le_apply_const_of_comparable hΛbd hΓbd hΛadd hΓadd hCΓ hcmp hΛ0 ht x

end GuaranteedSubsol
