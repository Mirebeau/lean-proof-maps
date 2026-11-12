/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.Axioms
import Mathlib.Tactic.Linarith

/-!
# Prop. prop:cst_subsol: the values of the operators on constants

Provider proofs for the frozen anchors on Prop. prop:cst_subsol (Intro.tex) and the remark
below it, see `ANCHORS.md`:
* item enum:Lambda0_delta, strictly causal case: `Γ[0] ≥ δ` (`le_apply_zero_of_strictlyCausal`);
  the causal case `Γ[0] > 0` is `ApplyZeroNonnegProof.apply_zero_pos_of_causal`;
* the remark below the proposition: `C_past`-memory and additive invariance give `Λ[0] ≤ C_past`
  (`apply_zero_le_of_hasMemory`);
* eq. eq:cst_subsol: `t ≤ Λ[t]` and `t ≤ Γ[t]` for `t ≤ min u_bd`, under `Λ[0] ≥ 0` and
  comparison (`le_apply_const_of_comparable`), or under `Γ[0] ≥ 0` and `Γ ≤ Λ`
  (`le_apply_const_of_le`).
-/

namespace GuaranteedSubsol.CstSubsolProof

variable {X : Type*}

/-- A `δ`-strictly causal and additively invariant scalar operator satisfies `Γ[0] ≥ δ`. -/
theorem le_apply_zero_of_strictlyCausal {Γ : (X → ℝ) → ℝ} {δ : ℝ} (hcaus : StrictlyCausal δ Γ)
    (hadd : AdditivelyInvariant Γ) : δ ≤ Γ 0 := by
  have h := hcaus 0 (fun _ => 1) 0 (fun y => by simp)
  have h1 : Γ (fun _ => (1 : ℝ)) = Γ 0 + 1 := by simpa using hadd 0 1
  rw [h1, zero_add] at h
  by_contra hlt
  push Not at hlt
  rw [min_eq_left hlt.le] at h
  rcases le_total (Γ 0 + 1) δ with h2 | h2
  · rw [min_eq_left h2] at h; linarith
  · rw [min_eq_right h2] at h; linarith

/-- `C_past`-memory and additive invariance give `Λ[0] ≤ C_past`. -/
theorem apply_zero_le_of_hasMemory {Λ : (X → ℝ) → ℝ} {C : ℝ} (hmem : HasMemory C Λ)
    (hadd : AdditivelyInvariant Λ) : Λ 0 ≤ C := by
  have h := hmem 0 (fun _ => -1) 0 (fun y => by simp)
  have h1 : Λ (fun _ => (-1 : ℝ)) = Λ 0 - 1 := by
    have := hadd 0 (-1)
    simp only [Pi.zero_apply, zero_add] at this
    rw [this, sub_eq_add_neg]
  rw [h1, zero_add] at h
  by_contra hlt
  push Not at hlt
  rw [max_eq_left hlt.le] at h
  rcases le_total (Λ 0 - 1) C with h2 | h2
  · rw [max_eq_right h2] at h; linarith
  · rw [max_eq_left h2] at h; linarith

/-- On `Int X`, `t ≤ Λ[t]` follows from `Λ[0] ≥ 0` and additive invariance. -/
theorem le_apply_const_of_nonneg {Λ : (X → ℝ) → X → ℝ} {I : Set X} {ubd : X → ℝ}
    (hΛbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) (hΛadd : ∀ x ∈ I, AdditivelyInvariant (Λ · x))
    (hΛ0 : ∀ x ∈ I, 0 ≤ Λ 0 x) {t : ℝ} (ht : ∀ x ∉ I, t ≤ ubd x) (x : X) :
    t ≤ Λ (fun _ => t) x := by
  by_cases hx : x ∈ I
  · have h2 := hΛadd x hx 0 t
    change Λ (fun y => (0 : X → ℝ) y + t) x = Λ 0 x + t at h2
    have h3 : (fun y => (0 : X → ℝ) y + t) = fun _ => t := funext fun y => by simp
    rw [h3] at h2
    rw [h2]
    linarith [hΛ0 x hx]
  · rw [hΛbd _ x hx]
    exact ht x hx

/-- Eq. eq:cst_subsol under `Λ[0] ≥ 0` and `C_Γ, C'_Γ`-comparison (only its upper inequality is
used). -/
theorem le_apply_const_of_comparable {Λ Γ : (X → ℝ) → X → ℝ} {I : Set X} {ubd : X → ℝ}
    (hΛbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) (hΓbd : ∀ u, ∀ x ∉ I, Γ u x = ubd x)
    (hΛadd : ∀ x ∈ I, AdditivelyInvariant (Λ · x)) (hΓadd : ∀ x ∈ I, AdditivelyInvariant (Γ · x))
    {CΓ CΓ' : ℝ} (hCΓ : 0 < CΓ) (hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (Λ · x) (Γ · x))
    (hΛ0 : ∀ x ∈ I, 0 ≤ Λ 0 x) {t : ℝ} (ht : ∀ x ∉ I, t ≤ ubd x) (x : X) :
    t ≤ Λ (fun _ => t) x ∧ t ≤ Γ (fun _ => t) x := by
  refine ⟨le_apply_const_of_nonneg hΛbd hΛadd hΛ0 ht x, ?_⟩
  refine le_apply_const_of_nonneg hΓbd hΓadd (fun y hy => ?_) ht x
  have h1 := (hcmp y hy 0).2
  change Λ (fun z => CΓ * (0 : X → ℝ) z) y ≤ CΓ * Γ 0 y at h1
  have h0 : (fun z => CΓ * (0 : X → ℝ) z) = 0 := funext fun z => by simp
  rw [h0] at h1
  by_contra hneg
  have : CΓ * Γ 0 y < 0 := mul_neg_of_pos_of_neg hCΓ (not_le.1 hneg)
  linarith [hΛ0 y hy]

/-- Eq. eq:cst_subsol under `Γ[0] ≥ 0` and `Γ ≤ Λ`. -/
theorem le_apply_const_of_le {Λ Γ : (X → ℝ) → X → ℝ} {I : Set X} {ubd : X → ℝ}
    (hΓbd : ∀ u, ∀ x ∉ I, Γ u x = ubd x) (hΓadd : ∀ x ∈ I, AdditivelyInvariant (Γ · x))
    (hΓΛ : ∀ u, Γ u ≤ Λ u) (hΓ0 : ∀ x ∈ I, 0 ≤ Γ 0 x) {t : ℝ} (ht : ∀ x ∉ I, t ≤ ubd x)
    (x : X) : t ≤ Λ (fun _ => t) x ∧ t ≤ Γ (fun _ => t) x := by
  have h := le_apply_const_of_nonneg hΓbd hΓadd hΓ0 ht x
  exact ⟨h.trans (hΓΛ _ x), h⟩

end GuaranteedSubsol.CstSubsolProof
