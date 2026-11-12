/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.CausalApplyMinProof
import LeanHJBAutoformalisation.GuaranteedSubsol.CpastFormulationProof
import Mathlib.Data.Fintype.Lattice

/-!
# Monotonicity restricted to a window of values: proofs

Provider proofs for the frozen anchors `GuaranteedSubsol.apply_le_apply_of_causal_memory_of_lt`
and `GuaranteedSubsol.apply_le_apply_of_causal_memory` (see `ANCHORS.md`): Corol.
corol:mon_min_max (Complexity.tex), scalar form.

* Strict case `t₀ < Λ u - C`: with `ũ = min {u,t₁}` and `ṽ = min {v,t₁}`, causality gives
  `Λ u = Λ ũ`, memory gives `Λ ũ = Λ max {ũ,t₀}`, monotonicity gives
  `Λ max {ũ,t₀} ≤ Λ max {ṽ,t₀}`, memory at level `t₀` gives `Λ max {ṽ,t₀} = Λ ṽ` since the former
  exceeds `t₀ + C`, and `Λ ṽ ≤ Λ v` by monotonicity.
* Boundary case `t₀ = Λ u - C`: since `X` is finite, some `t₀' < t₀` leaves no value of `u` in
  `[t₀', t₀[`, and the strict case applies at `t₀'`.
-/

namespace GuaranteedSubsol.MonMinMaxProof

/-- Pointwise comparison behind Corol. corol:mon_min_max:
`max {min {u,t₁}, t₀} ≤ max {min {v,t₁}, t₀}` under the window hypotheses. -/
theorem max_min_le_max_min {a b t₀ t₁ : ℝ} (hmid : t₀ ≤ a → a < t₁ → a ≤ b)
    (htop : t₁ ≤ a → t₁ ≤ b) : max (min a t₁) t₀ ≤ max (min b t₁) t₀ := by
  rcases lt_or_ge a t₀ with h0 | h0
  · exact max_le ((min_le_left _ _).trans (h0.le.trans (le_max_right _ _))) (le_max_right _ _)
  rcases lt_or_ge a t₁ with h1 | h1
  · rw [min_eq_left h1.le]
    exact max_le (le_max_of_le_left (le_min (hmid h0 h1) h1.le)) (le_max_right _ _)
  · rw [min_eq_right h1]
    exact max_le (le_max_of_le_left (le_min (htop h1) le_rfl)) (le_max_right _ _)

theorem apply_le_apply_of_causal_memory_of_lt {X : Type*} {Λ : (X → ℝ) → ℝ} {C : ℝ}
    (hmono : Monotone Λ) (hcaus : Causal Λ) (hadd : AdditivelyInvariant Λ)
    (hmem : HasMemory C Λ) {u v : X → ℝ} {t₀ t₁ : ℝ} (ht₀ : t₀ < Λ u - C) (ht₁ : Λ u ≤ t₁)
    (hmid : ∀ y, t₀ ≤ u y → u y < t₁ → u y ≤ v y) (htop : ∀ y, t₁ ≤ u y → t₁ ≤ v y) :
    Λ u ≤ Λ v := by
  have h1 := CausalApplyMinProof.apply_eq_apply_min hcaus u ht₁
  have h2 := CpastFormulationProof.apply_eq_apply_max hmono hadd hmem
    (fun y => min (u y) t₁) (t := t₀) (by rw [← h1]; exact ht₀.le)
  have h3 : Λ (fun y => max (min (u y) t₁) t₀) ≤ Λ (fun y => max (min (v y) t₁) t₀) :=
    hmono fun y => max_min_le_max_min (hmid y) (htop y)
  have hw : Λ u ≤ Λ (fun y => max (min (v y) t₁) t₀) := by
    rw [h1, h2]; exact h3
  have hm := hmem (fun y => max (min (v y) t₁) t₀) (fun y => min (v y) t₁) t₀
    fun y => by rw [max_assoc, max_self]
  rw [max_eq_left (by linarith : t₀ + C ≤ Λ fun y => max (min (v y) t₁) t₀)] at hm
  have h4 : Λ (fun y => min (v y) t₁) ≤ Λ v := hmono fun y => min_le_left _ _
  rcases le_or_gt (t₀ + C) (Λ fun y => min (v y) t₁) with hle | hlt
  · rw [max_eq_left hle] at hm
    linarith
  · rw [max_eq_right hlt.le] at hm
    linarith

/-- For `X` finite, some `ε > 0` separates the values of `u` below `t₀` from `t₀`:
`u y < t₀ → u y ≤ t₀ - ε`. -/
theorem exists_pos_gap {X : Type*} [Finite X] (u : X → ℝ) (t₀ : ℝ) :
    ∃ ε > 0, ∀ y, u y < t₀ → u y ≤ t₀ - ε := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨1, one_pos, fun y => isEmptyElim y⟩
  let f : X → ℝ := fun y => if u y < t₀ then t₀ - u y else 1
  have hf : ∀ y, 0 < f y := fun y => by
    simp only [f]; split_ifs with h
    · linarith
    · exact one_pos
  obtain ⟨y₀, hy₀⟩ := Finite.exists_min f
  refine ⟨f y₀, hf y₀, fun y hy => ?_⟩
  have := hy₀ y
  simp only [f, hy, ↓reduceIte] at this
  linarith

theorem apply_le_apply_of_causal_memory {X : Type*} [Finite X] {Λ : (X → ℝ) → ℝ} {C : ℝ}
    (hmono : Monotone Λ) (hcaus : Causal Λ) (hadd : AdditivelyInvariant Λ)
    (hmem : HasMemory C Λ) {u v : X → ℝ} {t₀ t₁ : ℝ} (ht₀ : t₀ ≤ Λ u - C) (ht₁ : Λ u ≤ t₁)
    (hmid : ∀ y, t₀ ≤ u y → u y < t₁ → u y ≤ v y) (htop : ∀ y, t₁ ≤ u y → t₁ ≤ v y) :
    Λ u ≤ Λ v := by
  obtain ⟨ε, hε, hgap⟩ := exists_pos_gap u t₀
  refine apply_le_apply_of_causal_memory_of_lt hmono hcaus hadd hmem (t₀ := t₀ - ε / 2)
    (by linarith) ht₁ (fun y hy hy₁ => hmid y ?_ hy₁) htop
  by_contra h
  have := hgap y (not_le.1 h)
  linarith

end GuaranteedSubsol.MonMinMaxProof
