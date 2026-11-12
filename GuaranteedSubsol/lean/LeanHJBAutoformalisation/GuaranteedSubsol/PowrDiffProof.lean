/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith

/-!
# Difference of powers: proof

Provider proof for the frozen anchor `GuaranteedSubsol.abs_rpow_sub_rpow_le` (see `ANCHORS.md`):
Lemma lem:powr_diff (Complexity.tex). Assuming `b ≤ a`, Mathlib's `Real.rpow_add_le_add_rpow`
gives `a ^ r = (b + (a - b)) ^ r ≤ b ^ r + (a - b) ^ r`, and `b ^ r ≤ a ^ r` by monotonicity.
-/

namespace GuaranteedSubsol.PowrDiffProof

/-- The case `b ≤ a`. -/
theorem abs_rpow_sub_rpow_le_of_le {a b r : ℝ} (hb : 0 ≤ b) (h : b ≤ a) (hr₀ : 0 ≤ r)
    (hr₁ : r ≤ 1) : |a ^ r - b ^ r| ≤ |a - b| ^ r := by
  have key : a ^ r ≤ b ^ r + (a - b) ^ r := by
    have := Real.rpow_add_le_add_rpow hb (sub_nonneg.2 h) hr₀ hr₁
    rwa [add_sub_cancel] at this
  have hmono : b ^ r ≤ a ^ r := Real.rpow_le_rpow hb h hr₀
  rw [abs_of_nonneg (sub_nonneg.2 hmono), abs_of_nonneg (sub_nonneg.2 h)]
  linarith

theorem abs_rpow_sub_rpow_le {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    |a ^ r - b ^ r| ≤ |a - b| ^ r := by
  rcases le_total b a with h | h
  · exact abs_rpow_sub_rpow_le_of_le hb h hr₀ hr₁
  · rw [abs_sub_comm, abs_sub_comm a b]
    exact abs_rpow_sub_rpow_le_of_le ha h hr₀ hr₁

end GuaranteedSubsol.PowrDiffProof
