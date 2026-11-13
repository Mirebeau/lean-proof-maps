/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.Kruzkov
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The tolerance criterion in Kruzkov coordinates: proof

Provider proof for the frozen anchor `GuaranteedSubsol.le_mul_iff_kruzkov` (see `ANCHORS.md`):
Complexity.tex, eq. (tol_as_Kruzkov). One has `v̄ exp(-ε αinv ū) = E((1+ε) ū)`, and the Kruzkov
transform `E = kruzkov αinv` is an order embedding of `ℝ_∞` for `αinv > 0`.
-/

@[expose] public section

namespace GuaranteedSubsol.TolKruzkovProof

/-- `E (ū) exp(-ε αinv ū) = E ((1+ε) ū)`. -/
theorem kruzkov_mul_exp (αinv ε a : ℝ) :
    kruzkov αinv a * Real.exp (-ε * αinv * a) = kruzkov αinv (((1 + ε) * a : ℝ) : WithTop ℝ) := by
  simp only [kruzkov]
  rw [neg_mul, ← Real.exp_add]
  congr 2
  ring

/-- For `αinv > 0`, `b ≤ c ↔ E b ≤ E c`, for `b ∈ ℝ_∞` and `c ∈ ℝ`. -/
theorem le_coe_iff_kruzkov {αinv : ℝ} (hα : 0 < αinv) (b : WithTop ℝ) (c : ℝ) :
    b ≤ (c : WithTop ℝ) ↔ kruzkov αinv b ≤ kruzkov αinv c := by
  cases b with
  | top =>
    simp only [top_le_iff, WithTop.coe_ne_top, false_iff, not_le, kruzkov]
    exact neg_neg_of_pos (Real.exp_pos _)
  | coe r =>
    simp only [WithTop.coe_le_coe, kruzkov, neg_le_neg_iff, Real.exp_le_exp]
    constructor <;> intro h <;> nlinarith

theorem le_mul_iff_kruzkov {αinv ε : ℝ} (hα : 0 < αinv) (uSub : ℝ) (uSup : WithTop ℝ) :
    uSup ≤ (((1 + ε) * uSub : ℝ) : WithTop ℝ) ↔
      kruzkov αinv uSup ≤ kruzkov αinv uSub * Real.exp (-ε * αinv * uSub) := by
  rw [kruzkov_mul_exp, ← le_coe_iff_kruzkov hα]

end GuaranteedSubsol.TolKruzkovProof
