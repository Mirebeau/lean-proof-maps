/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Reformulation of the intermediate stopping criterion of the AGSIK: proof

Provider proof for the frozen anchor `GuaranteedSubsol.agsik_until_iff`, see `ANCHORS.md`.

The criterion of line agsik:until of Algorithm algo:agsik (AGSI2.tex), at a point with `u = b`
and `Λ u = a` (real scalars), at level `n` and with timescale `α > 0`:
`exp(-a/α) < exp((ε-b)/α) + 2^{-n}`. The paragraph before the algorithm reformulates it as
`b ≤ a + ε - α ln(1 - exp((a - n α ln 2)/α))`, with the convention `ln t = -∞` for `t ≤ 0`.

The (strict) criterion of line agsik:until is equivalent to the reformulation with a *strict*
inequality (`agsik_until_iff`), not with `≤` as written in the paper. The convention `ln t = -∞` is
encoded by the alternative `a ≥ n α ln 2 ∨ …`: indeed `t := 1 - exp((a - n α ln 2)/α) ≤ 0` iff
`a ≥ n α ln 2`.
-/

namespace GuaranteedSubsol.AgsikCriterionProof

/-- `exp(-a/α) - 2^{-n} = exp(-a/α) (1 - exp((a - n α ln 2)/α))`. -/
theorem exp_sub_inv_two_pow {α : ℝ} (hα : 0 < α) (a : ℝ) (n : ℕ) :
    Real.exp (-a / α) - (2 : ℝ)⁻¹ ^ n =
      Real.exp (-a / α) * (1 - Real.exp ((a - n * α * Real.log 2) / α)) := by
  have h2 : (2 : ℝ)⁻¹ ^ n = Real.exp (-a / α) * Real.exp ((a - n * α * Real.log 2) / α) := by
    rw [← Real.exp_add, show -a / α + (a - n * α * Real.log 2) / α = -(n * Real.log 2) by
      field_simp; ring, Real.exp_neg, Real.exp_nat_mul, Real.exp_log two_pos, inv_pow]
  rw [h2]; ring

/-- Line agsik:until (strict) is the reformulated criterion with a strict inequality. -/
theorem agsik_until_iff {α : ℝ} (hα : 0 < α) (a b ε : ℝ) (n : ℕ) :
    Real.exp (-a / α) < Real.exp ((ε - b) / α) + (2 : ℝ)⁻¹ ^ n ↔
      (n * α * Real.log 2 ≤ a ∨
        b < a + ε - α * Real.log (1 - Real.exp ((a - n * α * Real.log 2) / α))) := by
  set t := 1 - Real.exp ((a - n * α * Real.log 2) / α) with ht
  have key := exp_sub_inv_two_pow hα a n
  rw [← ht] at key
  have hE := Real.exp_pos (-a / α)
  have hF := Real.exp_pos ((ε - b) / α)
  have ht0 : t ≤ 0 ↔ n * α * Real.log 2 ≤ a := by
    rw [ht, sub_nonpos, Real.one_le_exp_iff, le_div_iff₀ hα, zero_mul, sub_nonneg]
  rcases le_or_gt t 0 with h | h
  · simp only [ht0.1 h, true_or, iff_true]
    nlinarith
  · simp only [show ¬n * α * Real.log 2 ≤ a from fun h' => (not_le.2 h) (ht0.2 h'), false_or]
    rw [← sub_lt_iff_lt_add, key, ← Real.exp_log h, ← Real.exp_add, Real.exp_lt_exp,
      div_add' _ _ _ hα.ne', div_lt_div_iff_of_pos_right hα]
    simp only [Real.log_exp]
    constructor <;> intro h' <;> linarith

end GuaranteedSubsol.AgsikCriterionProof
