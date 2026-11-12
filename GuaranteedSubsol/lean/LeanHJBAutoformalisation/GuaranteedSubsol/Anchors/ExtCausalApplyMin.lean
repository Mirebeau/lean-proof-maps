/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.CausalApplyMinProof

/-!
# Frozen statement: a causal operator on `ℝ_∞` ignores values above its output

Source: Corol. corol:G_min_u_t (Complexity.tex), scalar form on `ℝ_∞ = WithTop ℝ`: if `Γ` is
causal (`Ext.Causal`), then `Γ u = Γ min {u,t}` for all real `t ≥ Γ u`. The scalar operator
`Γ : (X → ℝ_∞) → ℝ_∞` stands for `(Γ · x)`.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol.Ext

theorem Causal.apply_eq_apply_min {X : Type*} {Γ : (X → WithTop ℝ) → WithTop ℝ}
    (hΓ : Causal Γ) (u : X → WithTop ℝ) {t : ℝ} (ht : Γ u ≤ t) :
    Γ u = Γ (fun y => min (u y) t) := by
  exact GuaranteedSubsol.CausalApplyMinProof.ext_apply_eq_apply_min hΓ u ht

end GuaranteedSubsol.Ext
