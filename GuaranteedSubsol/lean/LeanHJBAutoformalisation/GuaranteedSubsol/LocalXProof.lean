/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.Axioms
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.Basic

/-!
# The two local formulations of sub-additivity in Kruzkov coordinates: proof

Provider proof for the frozen anchor `GuaranteedSubsol.local_iff_local_x` (see `ANCHORS.md`):
Prop. prop:subadd_local (Subadd.tex), (subadd_local) ⇔ (subadd_local_x). It is the change of
variable `t' = c t` with `c = exp(-αinv Λ u) > 0`, together with `η' = η / c` (resp. `η c`).
-/

@[expose] public section

open Filter Topology

namespace GuaranteedSubsol.LocalXProof

/-- Rescaling by a positive constant preserves `∀ᶠ t in 𝓝[>] 0`. -/
theorem eventually_mul {c : ℝ} (hc : 0 < c) {P : ℝ → Prop} (h : ∀ᶠ t in 𝓝[>] (0 : ℝ), P t) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), P (c * t) := by
  have ht : Tendsto (fun t : ℝ => c * t) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => c * t) (𝓝 0) (𝓝 (c * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos hc ht
  exact ht.eventually h

/-- The perturbation in (subadd_local_x) is a rescaled perturbation of (subadd_local). -/
theorem pert_eq {X : Type*} (u : X → ℝ) (αinv L t : ℝ) :
    (fun y => u y + t * Real.exp (αinv * (u y - L))) =
      fun y => u y + (Real.exp (-αinv * L) * t) * Real.exp (αinv * u y) := by
  funext y
  rw [mul_sub, sub_eq_add_neg, Real.exp_add, neg_mul]
  ring

theorem local_iff_local_x {X : Type*} (Λ : (X → ℝ) → ℝ) {αinv ρ : ℝ} :
    (∀ (u : X → ℝ), ∀ η > (0 : ℝ), ∀ᶠ t in 𝓝[>] (0 : ℝ),
        Λ (fun y => u y + t * Real.exp (αinv * u y)) ≤
          Λ u + ρ * t * Real.exp (αinv * Λ u) + η * t) ↔
      ∀ (u : X → ℝ), ∀ η > (0 : ℝ), ∀ᶠ t in 𝓝[>] (0 : ℝ),
        Λ (fun y => u y + t * Real.exp (αinv * (u y - Λ u))) ≤ Λ u + ρ * t + η * t := by
  constructor
  · intro h u η hη
    set c := Real.exp (-αinv * Λ u) with hc_def
    have hc : 0 < c := Real.exp_pos _
    have hcinv : c * Real.exp (αinv * Λ u) = 1 := by
      rw [hc_def, ← Real.exp_add]; simp
    filter_upwards [eventually_mul hc (h u (η / c) (div_pos hη hc))] with t ht
    rw [pert_eq]
    calc Λ (fun y => u y + c * t * Real.exp (αinv * u y))
        ≤ Λ u + ρ * (c * t) * Real.exp (αinv * Λ u) + η / c * (c * t) := ht
      _ = Λ u + ρ * t * (c * Real.exp (αinv * Λ u)) + η * t := by
          rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_left₀ t hc.ne']; ring
      _ = Λ u + ρ * t + η * t := by rw [hcinv, mul_one]
  · intro h u η hη
    set c := Real.exp (-αinv * Λ u) with hc_def
    have hc : 0 < c := Real.exp_pos _
    have hcinv : c * Real.exp (αinv * Λ u) = 1 := by
      rw [hc_def, ← Real.exp_add]; simp
    have hc' : 0 < c⁻¹ := inv_pos.2 hc
    filter_upwards [eventually_mul hc' (h u (η * c) (mul_pos hη hc))] with t ht
    rw [pert_eq] at ht
    have hct : c * (c⁻¹ * t) = t := by field_simp
    rw [hct] at ht
    calc Λ (fun y => u y + t * Real.exp (αinv * u y))
        ≤ Λ u + ρ * (c⁻¹ * t) + η * c * (c⁻¹ * t) := ht
      _ = Λ u + ρ * t * Real.exp (αinv * Λ u) + η * t * (c * Real.exp (αinv * Λ u)) := by
          have : c⁻¹ = Real.exp (αinv * Λ u) := by
            rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ hc.ne', mul_comm]; exact hcinv
          rw [this]; ring
      _ = Λ u + ρ * t * Real.exp (αinv * Λ u) + η * t := by rw [hcinv, mul_one]


/-- The rescaling of `local_iff_local_x`, with `O(t²)` remainders. -/
theorem local_iff_local_x_sq {X : Type*} (Λ : (X → ℝ) → ℝ) {αinv ρ : ℝ} :
    (∀ (u : X → ℝ), ∃ K : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ),
        Λ (fun y => u y + t * Real.exp (αinv * u y)) ≤
          Λ u + ρ * t * Real.exp (αinv * Λ u) + K * t ^ 2) ↔
      ∀ (u : X → ℝ), ∃ K : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ),
        Λ (fun y => u y + t * Real.exp (αinv * (u y - Λ u))) ≤ Λ u + ρ * t + K * t ^ 2 := by
  constructor
  · intro h u
    obtain ⟨K, hK⟩ := h u
    set c := Real.exp (-αinv * Λ u) with hc_def
    have hc : 0 < c := Real.exp_pos _
    have hcinv : c * Real.exp (αinv * Λ u) = 1 := by
      rw [hc_def, ← Real.exp_add]; simp
    refine ⟨K * c ^ 2, ?_⟩
    filter_upwards [eventually_mul hc hK] with t ht
    rw [pert_eq]
    calc Λ (fun y => u y + c * t * Real.exp (αinv * u y))
        ≤ Λ u + ρ * (c * t) * Real.exp (αinv * Λ u) + K * (c * t) ^ 2 := ht
      _ = Λ u + ρ * t * (c * Real.exp (αinv * Λ u)) + K * c ^ 2 * t ^ 2 := by ring
      _ = Λ u + ρ * t + K * c ^ 2 * t ^ 2 := by rw [hcinv, mul_one]
  · intro h u
    obtain ⟨K, hK⟩ := h u
    set c := Real.exp (-αinv * Λ u) with hc_def
    have hc : 0 < c := Real.exp_pos _
    have hcinv : c * Real.exp (αinv * Λ u) = 1 := by
      rw [hc_def, ← Real.exp_add]; simp
    have hc' : 0 < c⁻¹ := inv_pos.2 hc
    have hE : c⁻¹ = Real.exp (αinv * Λ u) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ hc.ne', mul_comm]; exact hcinv
    refine ⟨K * Real.exp (αinv * Λ u) ^ 2, ?_⟩
    filter_upwards [eventually_mul hc' hK] with t ht
    rw [pert_eq] at ht
    have hct : c * (c⁻¹ * t) = t := by field_simp
    rw [hct, hE] at ht
    calc Λ (fun y => u y + t * Real.exp (αinv * u y))
        ≤ Λ u + ρ * (Real.exp (αinv * Λ u) * t) + K * (Real.exp (αinv * Λ u) * t) ^ 2 := ht
      _ = Λ u + ρ * t * Real.exp (αinv * Λ u) + K * Real.exp (αinv * Λ u) ^ 2 * t ^ 2 := by
          ring

end GuaranteedSubsol.LocalXProof
