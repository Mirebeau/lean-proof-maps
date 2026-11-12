/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AxiomsExt
import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax
import Mathlib.Tactic.Linarith

/-!
# Max and min of causal, sub-additive and sub-multiplicative operators on `ℝ_∞`

Provider proofs for the frozen anchors `GuaranteedSubsol.Ext.Causal.max`, `Ext.Causal.min`,
`Ext.SubAdditive.max`, `Ext.SubAdditive.min`, `Ext.SubMultiplicative.max` and
`Ext.SubMultiplicative.min` (see `ANCHORS.md`), Lemma lem:causal_mix of Complexity.tex in
scalar form on `ℝ_∞ = WithTop ℝ`: the pointwise maximum and minimum of two operators
satisfying one of these axioms satisfy it again.

For causality, the two delays `δ₁, δ₂` are replaced by `min δ₁ δ₂`, using that agreement of
truncations at level `t + δ₁` implies agreement at any lower level `t + δ`, and that truncation
at a level commutes with `max` and `min` in any linear order. The other two axioms follow from
the monotonicity of `max` and `min`, of translation `x ↦ x + c`, and of multiplication
`x ↦ ↑k * x` by a positive real `k` on `WithTop ℝ`.
-/

namespace GuaranteedSubsol.ExtCausalMixProof

/-- Agreement of truncations at a level `s` implies agreement at every lower level `r ≤ s`. -/
theorem min_eq_min_of_le {α : Type*} [LinearOrder α] {a b r s : α}
    (h : min a s = min b s) (hrs : r ≤ s) : min a r = min b r := by
  rw [← min_eq_right hrs, ← min_assoc, h, min_assoc]

/-- Truncation at a level commutes with `max`: `min (max a b) s = max (min a s) (min b s)`. -/
theorem min_max_trunc {α : Type*} [LinearOrder α] (a b s : α) :
    min (max a b) s = max (min a s) (min b s) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (min_le_min_right s h)]
  · rw [max_eq_left h, max_eq_left (min_le_min_right s h)]

/-- Truncation at a level commutes with `min`: `min (min a b) s = min (min a s) (min b s)`. -/
theorem min_min_trunc {α : Type*} [LinearOrder α] (a b s : α) :
    min (min a b) s = min (min a s) (min b s) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (min_le_min_right s h)]
  · rw [min_eq_right h, min_eq_right (min_le_min_right s h)]

/-- Common delay for two causal operators on `ℝ_∞`: if the truncations of `Λ u, Λ v` and of
`Γ u, Γ v` agree above `t` with delays `δ₁` and `δ₂`, they both agree with delay
`min δ₁ δ₂ > 0`. -/
theorem common_delay {X : Type*} {Λ Γ : (X → WithTop ℝ) → WithTop ℝ} (hΛ : Ext.Causal Λ)
    (hΓ : Ext.Causal Γ) (u v : X → WithTop ℝ) (t : ℝ)
    (h : ∀ y, min (u y) (t : WithTop ℝ) = min (v y) t) :
    ∃ δ > (0 : ℝ), min (Λ u) ((t + δ : ℝ) : WithTop ℝ) = min (Λ v) ((t + δ : ℝ) : WithTop ℝ) ∧
      min (Γ u) ((t + δ : ℝ) : WithTop ℝ) = min (Γ v) ((t + δ : ℝ) : WithTop ℝ) := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := hΛ u v t h
  obtain ⟨δ₂, hδ₂, h₂⟩ := hΓ u v t h
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_, ?_⟩
  · exact min_eq_min_of_le h₁ (WithTop.coe_le_coe.2 (by linarith [min_le_left δ₁ δ₂]))
  · exact min_eq_min_of_le h₂ (WithTop.coe_le_coe.2 (by linarith [min_le_right δ₁ δ₂]))

/-- Multiplication by a positive real `↑k` is monotone on `ℝ_∞ = WithTop ℝ`. -/
theorem mul_left_monotone {k : ℝ} (hk : 0 < k) :
    Monotone fun x : WithTop ℝ => (k : WithTop ℝ) * x := by
  have htop : (k : WithTop ℝ) * ⊤ = ⊤ := WithTop.mul_top (by exact_mod_cast hk.ne')
  intro x y hxy
  induction y using WithTop.recTopCoe with
  | top => exact (le_top : _ ≤ (⊤ : WithTop ℝ)).trans_eq htop.symm
  | coe b =>
    induction x using WithTop.recTopCoe with
    | top => exact absurd hxy (by simp)
    | coe a =>
      change (k : WithTop ℝ) * a ≤ (k : WithTop ℝ) * b
      rw [← WithTop.coe_mul, ← WithTop.coe_mul, WithTop.coe_le_coe]
      exact mul_le_mul_of_nonneg_left (WithTop.coe_le_coe.1 hxy) hk.le

theorem causal_max {X : Type*} {Λ Γ : (X → WithTop ℝ) → WithTop ℝ}
    (hΛ : Ext.Causal Λ) (hΓ : Ext.Causal Γ) :
    Ext.Causal fun u => max (Λ u) (Γ u) := by
  intro u v t h
  obtain ⟨δ, hδ, h₁, h₂⟩ := common_delay hΛ hΓ u v t h
  exact ⟨δ, hδ, by beta_reduce; rw [min_max_trunc (Λ u), min_max_trunc (Λ v), h₁, h₂]⟩

theorem causal_min {X : Type*} {Λ Γ : (X → WithTop ℝ) → WithTop ℝ}
    (hΛ : Ext.Causal Λ) (hΓ : Ext.Causal Γ) :
    Ext.Causal fun u => min (Λ u) (Γ u) := by
  intro u v t h
  obtain ⟨δ, hδ, h₁, h₂⟩ := common_delay hΛ hΓ u v t h
  exact ⟨δ, hδ, by beta_reduce; rw [min_min_trunc (Λ u), min_min_trunc (Λ v), h₁, h₂]⟩

theorem subAdditive_max {X : Type*} {Λ Γ : (X → WithTop ℝ) → WithTop ℝ} {ρ : ℝ}
    (hΛ : Ext.SubAdditive ρ Λ) (hΓ : Ext.SubAdditive ρ Γ) :
    Ext.SubAdditive ρ fun u => max (Λ u) (Γ u) := by
  intro v t ht
  beta_reduce
  rw [← max_add_add_right]
  exact max_le_max (hΛ v t ht) (hΓ v t ht)

theorem subAdditive_min {X : Type*} {Λ Γ : (X → WithTop ℝ) → WithTop ℝ} {ρ : ℝ}
    (hΛ : Ext.SubAdditive ρ Λ) (hΓ : Ext.SubAdditive ρ Γ) :
    Ext.SubAdditive ρ fun u => min (Λ u) (Γ u) := by
  intro v t ht
  beta_reduce
  rw [← min_add_add_right]
  exact min_le_min (hΛ v t ht) (hΓ v t ht)

theorem subMultiplicative_max {X : Type*} {Λ Γ : (X → WithTop ℝ) → WithTop ℝ} {ν : ℝ}
    (hΛ : Ext.SubMultiplicative ν Λ) (hΓ : Ext.SubMultiplicative ν Γ) :
    Ext.SubMultiplicative ν fun u => max (Λ u) (Γ u) := by
  intro t ht u
  beta_reduce
  rw [(mul_left_monotone (by linarith : (0 : ℝ) < 1 + t)).map_max, ← max_add_add_right]
  exact max_le_max (hΛ t ht u) (hΓ t ht u)

theorem subMultiplicative_min {X : Type*} {Λ Γ : (X → WithTop ℝ) → WithTop ℝ} {ν : ℝ}
    (hΛ : Ext.SubMultiplicative ν Λ) (hΓ : Ext.SubMultiplicative ν Γ) :
    Ext.SubMultiplicative ν fun u => min (Λ u) (Γ u) := by
  intro t ht u
  beta_reduce
  rw [(mul_left_monotone (by linarith : (0 : ℝ) < 1 + t)).map_min, ← min_add_add_right]
  exact min_le_min (hΛ t ht u) (hΓ t ht u)

end GuaranteedSubsol.ExtCausalMixProof
