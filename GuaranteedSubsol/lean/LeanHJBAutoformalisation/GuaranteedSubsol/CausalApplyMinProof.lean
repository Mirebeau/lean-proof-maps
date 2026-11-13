/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.Axioms
public import LeanHJBAutoformalisation.GuaranteedSubsol.AxiomsExt
public import Mathlib.Tactic.Linarith

/-!
# A causal operator ignores values above its output: proofs

Provider proofs for the frozen anchors `GuaranteedSubsol.Causal.apply_eq_apply_min` and
`GuaranteedSubsol.Ext.Causal.apply_eq_apply_min` (see `ANCHORS.md`): Corol. corol:G_min_u_t
(Complexity.tex), scalar form, on `ℝ` and on `ℝ_∞`. Causality applied to `u` and `min {u,t}`
gives `δ > 0` with `min (Γ u) (t+δ) = min (Γ min {u,t}) (t+δ)`; since `Γ u ≤ t < t + δ`, the left
side is `Γ u`, which forces `Γ min {u,t} < t + δ` and the equality.
-/

@[expose] public section

namespace GuaranteedSubsol.CausalApplyMinProof

theorem apply_eq_apply_min {X : Type*} {Γ : (X → ℝ) → ℝ} (hΓ : Causal Γ) (u : X → ℝ)
    {t : ℝ} (ht : Γ u ≤ t) :
    Γ u = Γ (fun y => min (u y) t) := by
  obtain ⟨δ, hδ, h⟩ := hΓ u (fun y => min (u y) t) t fun y => by rw [min_assoc, min_self]
  rw [min_eq_left (by linarith : Γ u ≤ t + δ)] at h
  rcases le_or_gt (t + δ) (Γ fun y => min (u y) t) with hle | hlt
  · rw [min_eq_right hle] at h
    linarith
  · rwa [min_eq_left hlt.le] at h

theorem ext_apply_eq_apply_min {X : Type*} {Γ : (X → WithTop ℝ) → WithTop ℝ}
    (hΓ : Ext.Causal Γ) (u : X → WithTop ℝ) {t : ℝ} (ht : Γ u ≤ t) :
    Γ u = Γ (fun y => min (u y) t) := by
  obtain ⟨δ, hδ, h⟩ := hΓ u (fun y => min (u y) t) t fun y => by rw [min_assoc, min_self]
  have hlt : ((t : ℝ) : WithTop ℝ) < ((t + δ : ℝ) : WithTop ℝ) :=
    WithTop.coe_lt_coe.2 (by linarith)
  rw [min_eq_left (ht.trans hlt.le)] at h
  rcases le_or_gt ((t + δ : ℝ) : WithTop ℝ) (Γ fun y => min (u y) t) with hle | hgt
  · rw [min_eq_right hle] at h
    exact absurd (h ▸ ht) (not_le.2 hlt)
  · rwa [min_eq_left hgt.le] at h

end GuaranteedSubsol.CausalApplyMinProof
