/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.CausalMixProof

/-!
# Monotonicity and causality of `max {ū, min {T, Γ}}`: proofs

Provider proofs for the frozen anchors `GuaranteedSubsol.monotone_max_min` and
`GuaranteedSubsol.Causal.max_min` (see `ANCHORS.md`): Lemma lem:max_min_mon_causal
(Complexity.tex), scalar form, from lem:causal_mix and the fact that constant operators are
monotone and causal.
-/

namespace GuaranteedSubsol.MaxMinMonCausalProof

/-- A constant operator is causal. -/
theorem causal_const {X : Type*} (c : ℝ) : Causal (fun _ : X → ℝ => c) :=
  fun _ _ _ _ => ⟨1, one_pos, rfl⟩

theorem monotone_max_min {X : Type*} {Γ : (X → ℝ) → ℝ} (hmono : Monotone Γ) (c T : ℝ) :
    Monotone (fun u => max c (min T (Γ u))) :=
  monotone_const.max (monotone_const.min hmono)

theorem causal_max_min {X : Type*} {Γ : (X → ℝ) → ℝ} (hcaus : Causal Γ) (c T : ℝ) :
    Causal (fun u => max c (min T (Γ u))) :=
  CausalMixProof.causal_max (causal_const c) (CausalMixProof.causal_min (causal_const T) hcaus)

end GuaranteedSubsol.MaxMinMonCausalProof
