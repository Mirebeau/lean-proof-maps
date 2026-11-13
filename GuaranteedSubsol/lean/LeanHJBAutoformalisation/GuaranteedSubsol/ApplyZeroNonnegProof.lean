/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.Axioms
public import Mathlib.Tactic.Linarith

/-!
# `Λ[0] ≥ 0` from the causality of `Γ`: proofs

Provider proof for the frozen anchor `GuaranteedSubsol.apply_zero_nonneg_of_causal`, see
`ANCHORS.md`. A causal and additively invariant scalar operator satisfies `Γ[0] > 0`: causality
applied to `u = 0`, `v = 1` at the level `t = 0` gives `min {Γ[0], δ} = min {Γ[0] + 1, δ}` for some
`δ > 0`, which forces `Γ[0] ≥ δ`. Hence `Λ[0] ≥ Γ[0] > 0` on `Int X`, while `Λ[0] = u_bd ≥ 0` on
`∂X`.
-/

@[expose] public section

namespace GuaranteedSubsol.ApplyZeroNonnegProof

variable {X : Type*}

/-- A causal and additively invariant scalar operator satisfies `Γ[0] > 0`. -/
theorem apply_zero_pos_of_causal {Γ : (X → ℝ) → ℝ} (hcaus : Causal Γ)
    (hadd : AdditivelyInvariant Γ) : 0 < Γ 0 := by
  obtain ⟨δ, hδ, h⟩ := hcaus 0 (fun _ => 1) 0 (fun y => by simp)
  have h1 : Γ (fun _ => (1 : ℝ)) = Γ 0 + 1 := by simpa using hadd 0 1
  rw [h1, zero_add] at h
  by_contra hneg
  rw [min_eq_left ((not_lt.1 hneg).trans hδ.le)] at h
  rcases le_total (Γ 0 + 1) δ with h2 | h2
  · rw [min_eq_left h2] at h; linarith
  · rw [min_eq_right h2] at h; linarith [not_lt.1 hneg]

theorem apply_zero_nonneg_of_causal {Λ Γ : (X → ℝ) → X → ℝ} {I : Set X} {ubd : X → ℝ}
    (hΛbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) (hubd : ∀ x ∉ I, 0 ≤ ubd x)
    (hΓadd : ∀ x ∈ I, AdditivelyInvariant (Γ · x)) (hΓcaus : ∀ x ∈ I, Causal (Γ · x))
    (hΓΛ : ∀ u, Γ u ≤ Λ u) : 0 ≤ Λ 0 := fun x => by
  by_cases hx : x ∈ I
  · exact (apply_zero_pos_of_causal (hΓcaus x hx) (hΓadd x hx)).le.trans (hΓΛ 0 x)
  · rw [Pi.zero_apply, hΛbd 0 x hx]
    exact hubd x hx

end GuaranteedSubsol.ApplyZeroNonnegProof
