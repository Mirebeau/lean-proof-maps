/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Lemma lem:pow_cvx: proof

Lemma lem:pow_cvx (Complexity.tex, V1): for `0 ≤ a ≤ b` and `s ≥ 1`,
`b^s ≤ a^s + s b^{s-1} (b - a)`, the tangent inequality of the convex function `t ↦ t^s` at `b`.
The proof uses Bernoulli's inequality `1 + s x ≤ (1 + x)^s` (`x ≥ -1`) with `x = a/b - 1`.
-/

namespace GuaranteedSubsol.PowCvxProof

theorem rpow_le_rpow_add_mul_sub {a b s : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hs : 1 ≤ s) :
    b ^ s ≤ a ^ s + s * b ^ (s - 1) * (b - a) := by
  rcases (ha.trans hab).eq_or_lt with hb | hb
  · -- `b = 0`, hence `a = 0`
    have ha0 : a = 0 := le_antisymm (hb ▸ hab) ha
    rw [← hb, ha0, Real.zero_rpow (by linarith)]
    simp
  · have hx : -1 ≤ a / b - 1 := by
      have : 0 ≤ a / b := div_nonneg ha hb.le
      linarith
    have hbern := one_add_mul_self_le_rpow_one_add hx hs
    rw [add_sub_cancel, Real.div_rpow ha hb.le] at hbern
    have hbs : 0 < b ^ s := Real.rpow_pos_of_pos hb s
    rw [le_div_iff₀ hbs] at hbern
    have hsplit : b ^ s = b * b ^ (s - 1) := by
      rw [← Real.rpow_one_add' hb.le (by linarith)]
      congr 1
      ring
    have e : (1 + s * (a / b - 1)) * b ^ s = b ^ s - s * b ^ (s - 1) * (b - a) := by
      rw [hsplit]
      field_simp
      ring
    linarith

end GuaranteedSubsol.PowCvxProof
