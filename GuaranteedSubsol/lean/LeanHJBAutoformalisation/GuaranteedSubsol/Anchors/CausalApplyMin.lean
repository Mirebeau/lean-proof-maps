/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.CausalApplyMinProof

/-!
# Frozen statement: a causal operator ignores values above its output

Source: Corol. corol:G_min_u_t (Complexity.tex), scalar form: if `Γ` is causal, then
`Γ u = Γ min {u,t}` for all `t ≥ Γ u`. The scalar operator `Γ : (X → ℝ) → ℝ` stands for `(Γ · x)`.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem Causal.apply_eq_apply_min {X : Type*} {Γ : (X → ℝ) → ℝ} (hΓ : Causal Γ) (u : X → ℝ)
    {t : ℝ} (ht : Γ u ≤ t) :
    Γ u = Γ (fun y => min (u y) t) := by
  exact CausalApplyMinProof.apply_eq_apply_min hΓ u ht

end GuaranteedSubsol
