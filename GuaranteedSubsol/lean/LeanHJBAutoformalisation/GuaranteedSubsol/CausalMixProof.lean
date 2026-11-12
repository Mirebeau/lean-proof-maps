/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.Axioms
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Tactic.Linarith

/-!
# Max and min of causal, sub-additive and sub-multiplicative operators

Provider proofs for the frozen anchors `GuaranteedSubsol.Causal.max`, `Causal.min`,
`SubAdditive.max`, `SubAdditive.min`, `SubMultiplicative.max` and `SubMultiplicative.min`
(see `ANCHORS.md`), Lemma lem:causal_mix of Complexity.tex in scalar form: the pointwise
maximum and minimum of two operators satisfying one of these axioms satisfy it again.

For causality, the two delays `δ₁, δ₂` are replaced by `min δ₁ δ₂`, using that agreement of
truncations at level `t + δ₁` implies agreement at any lower level `t + δ`, and that truncation
at a level commutes with `max` and `min`. The other two axioms follow from the monotonicity of
`max` and `min` and their compatibility with translation and nonnegative scaling.
-/

namespace GuaranteedSubsol.CausalMixProof

/-- Agreement of truncations at a level `s` implies agreement at every lower level `r ≤ s`. -/
theorem min_eq_min_of_le {a b r s : ℝ} (h : min a s = min b s) (hrs : r ≤ s) :
    min a r = min b r := by
  rw [← min_eq_right hrs, ← min_assoc, h, min_assoc]

/-- Truncation at a level commutes with `max`: `min (max a b) s = max (min a s) (min b s)`. -/
theorem min_max_trunc (a b s : ℝ) : min (max a b) s = max (min a s) (min b s) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (min_le_min_right s h)]
  · rw [max_eq_left h, max_eq_left (min_le_min_right s h)]

/-- Truncation at a level commutes with `min`: `min (min a b) s = min (min a s) (min b s)`. -/
theorem min_min_trunc (a b s : ℝ) : min (min a b) s = min (min a s) (min b s) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (min_le_min_right s h)]
  · rw [min_eq_right h, min_eq_right (min_le_min_right s h)]

/-- Common delay for two causal operators: if the truncations of `Λ u, Λ v` and of `Γ u, Γ v`
agree above `t` with delays `δ₁` and `δ₂`, they both agree with delay `min δ₁ δ₂ > 0`. -/
theorem common_delay {X : Type*} {Λ Γ : (X → ℝ) → ℝ} (hΛ : Causal Λ) (hΓ : Causal Γ)
    (u v : X → ℝ) (t : ℝ) (h : ∀ y, min (u y) t = min (v y) t) :
    ∃ δ > 0, min (Λ u) (t + δ) = min (Λ v) (t + δ) ∧
      min (Γ u) (t + δ) = min (Γ v) (t + δ) := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := hΛ u v t h
  obtain ⟨δ₂, hδ₂, h₂⟩ := hΓ u v t h
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_, ?_⟩
  · exact min_eq_min_of_le h₁ (by linarith [min_le_left δ₁ δ₂])
  · exact min_eq_min_of_le h₂ (by linarith [min_le_right δ₁ δ₂])

theorem causal_max {X : Type*} {Λ Γ : (X → ℝ) → ℝ} (hΛ : Causal Λ)
    (hΓ : Causal Γ) :
    Causal fun u => max (Λ u) (Γ u) := by
  intro u v t h
  obtain ⟨δ, hδ, h₁, h₂⟩ := common_delay hΛ hΓ u v t h
  exact ⟨δ, hδ, by beta_reduce; rw [min_max_trunc (Λ u), min_max_trunc (Λ v), h₁, h₂]⟩

theorem causal_min {X : Type*} {Λ Γ : (X → ℝ) → ℝ} (hΛ : Causal Λ)
    (hΓ : Causal Γ) :
    Causal fun u => min (Λ u) (Γ u) := by
  intro u v t h
  obtain ⟨δ, hδ, h₁, h₂⟩ := common_delay hΛ hΓ u v t h
  exact ⟨δ, hδ, by beta_reduce; rw [min_min_trunc (Λ u), min_min_trunc (Λ v), h₁, h₂]⟩

theorem subAdditive_max {X : Type*} {Λ Γ : (X → ℝ) → ℝ} {ρ : ℝ} (hΛ : SubAdditive ρ Λ)
    (hΓ : SubAdditive ρ Γ) :
    SubAdditive ρ fun u => max (Λ u) (Γ u) := by
  intro v t ht
  beta_reduce
  rw [← max_add_add_right]
  exact max_le_max (hΛ v t ht) (hΓ v t ht)

theorem subAdditive_min {X : Type*} {Λ Γ : (X → ℝ) → ℝ} {ρ : ℝ} (hΛ : SubAdditive ρ Λ)
    (hΓ : SubAdditive ρ Γ) :
    SubAdditive ρ fun u => min (Λ u) (Γ u) := by
  intro v t ht
  beta_reduce
  rw [← min_add_add_right]
  exact min_le_min (hΛ v t ht) (hΓ v t ht)

theorem subMultiplicative_max {X : Type*} {Λ Γ : (X → ℝ) → ℝ} {ν : ℝ}
    (hΛ : SubMultiplicative ν Λ)
    (hΓ : SubMultiplicative ν Γ) :
    SubMultiplicative ν fun u => max (Λ u) (Γ u) := by
  intro t ht u
  have hc : (0 : ℝ) ≤ 1 + t := by linarith
  rw [mul_max_of_nonneg _ _ hc, ← max_sub_sub_right]
  exact max_le_max (hΛ t ht u) (hΓ t ht u)

theorem subMultiplicative_min {X : Type*} {Λ Γ : (X → ℝ) → ℝ} {ν : ℝ}
    (hΛ : SubMultiplicative ν Λ)
    (hΓ : SubMultiplicative ν Γ) :
    SubMultiplicative ν fun u => min (Λ u) (Γ u) := by
  intro t ht u
  have hc : (0 : ℝ) ≤ 1 + t := by linarith
  rw [mul_min_of_nonneg _ _ hc, ← min_sub_sub_right]
  exact min_le_min (hΛ t ht u) (hΓ t ht u)

end GuaranteedSubsol.CausalMixProof
