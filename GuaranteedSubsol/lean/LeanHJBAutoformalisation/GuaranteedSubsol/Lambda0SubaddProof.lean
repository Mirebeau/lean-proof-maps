/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.KruzkovProof
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# `Λ[0] ≥ -α ln ρ` when `Φ_α` is `ρ`-sub-additive: proof

Provider proof for the frozen anchor `GuaranteedSubsol.le_apply_zero_of_kruzkov_subAdditive`
(see `ANCHORS.md`): Prop. prop:cst_subsol, item enum:Lambda0_alpha (Intro.tex). Direct proof, not
following the paper's local expansion. By additive invariance, `Φ_α` maps the constant `r < 0` to
the constant `r exp(-Λ[0]/α)`. Sub-additivity between the constants `-1` and `-1/2` gives
`exp(-Λ[0]/α) ≤ ρ`, i.e. `Λ[0] ≥ -α ln ρ`.

The general version `le_apply_zero_of_kruzkov_subAdditive'` only assumes `0 ≤ α` (for `α = 0`
the sub-additivity is contradictory), drops `0 < ρ` (it follows), and replaces monotonicity of
`Λ` by `Λ w ≤ Λ 0` for all `w ≤ 0`, which is exactly `Λ_∞ 0 = Λ 0`.
-/

namespace GuaranteedSubsol.Lambda0SubaddProof

open KruzkovProof

variable {X : Type*}

/-- If `Λ w ≤ Λ 0` for all `w ≤ 0`, then `Λ_∞` takes the value `Λ 0` at the constant `0`. -/
theorem monotoneExtension_zero {Λ : (X → ℝ) → ℝ} (hmax : ∀ w : X → ℝ, w ≤ 0 → Λ w ≤ Λ 0) :
    monotoneExtension Λ (fun _ => ((0 : ℝ) : WithTop ℝ)) = ((Λ 0 : ℝ) : WithTop ℝ) := by
  have := nonempty_minorant (X := X) fun _ => ((0 : ℝ) : WithTop ℝ)
  refine le_antisymm (ciSup_le fun w => WithTop.coe_le_coe.2 (hmax w.1 fun y => ?_)) ?_
  · exact WithTop.coe_le_coe.1 (w.2 y)
  · exact le_monotoneExtension Λ 0 fun _ => le_rfl

/-- Under the same assumption and additive invariance, `Λ_∞ c = Λ 0 + c` for constant `c`. -/
theorem monotoneExtension_const {Λ : (X → ℝ) → ℝ} (hmax : ∀ w : X → ℝ, w ≤ 0 → Λ w ≤ Λ 0)
    (hadd : AdditivelyInvariant Λ) (c : ℝ) :
    monotoneExtension Λ (fun _ => (c : WithTop ℝ)) = ((Λ 0 + c : ℝ) : WithTop ℝ) := by
  have h := monotoneExtension_add_const hadd (fun _ => ((0 : ℝ) : WithTop ℝ)) c
  rw [monotoneExtension_zero hmax] at h
  simpa [← WithTop.coe_add] using h

/-- For `α ≠ 0`, `Φ_α` maps the constant `r < 0` to the constant `r exp(-Λ[0]/α)`. -/
theorem kruzkovOp_const_neg {Λ : (X → ℝ) → ℝ} {α : ℝ} (hα : α ≠ 0)
    (hmax : ∀ w : X → ℝ, w ≤ 0 → Λ w ≤ Λ 0) (hadd : AdditivelyInvariant Λ) {r : ℝ}
    (hr : r < 0) :
    kruzkovOp α Λ (fun _ => r) = r * Real.exp (-(1 / α) * Λ 0) := by
  unfold kruzkovOp
  simp only [kruzkovInv, hr, ↓reduceIte]
  rw [monotoneExtension_const hmax hadd]
  change -Real.exp (-(1 / α) * (Λ 0 + -α * Real.log (-r))) = _
  rw [show -(1 / α) * (Λ 0 + -α * Real.log (-r)) = -(1 / α) * Λ 0 + Real.log (-r) by
    field_simp; ring, Real.exp_add, Real.exp_log (by linarith)]
  ring

/-- For `α = 0`, `Φ_α` is never sub-additive (under the same assumptions): it jumps from `-1`
to `0` when a constant crosses `0`. -/
theorem not_subAdditive_zero {Λ : (X → ℝ) → ℝ} (hmax : ∀ w : X → ℝ, w ≤ 0 → Λ w ≤ Λ 0)
    (hadd : AdditivelyInvariant Λ) (ρ : ℝ) : ¬ SubAdditive ρ (kruzkovOp 0 Λ) := by
  intro hsub
  set ε : ℝ := 1 / (2 * (|ρ| + 1)) with hε
  have hε0 : 0 < ε := by positivity
  have h := hsub (fun _ => -ε) (2 * ε) (by linarith)
  have hl : kruzkovOp 0 Λ (fun _ => -ε + 2 * ε) = 0 := by
    unfold kruzkovOp
    have hneg : ¬ (-ε + 2 * ε < 0) := by linarith
    simp only [kruzkovInv, hneg, ↓reduceIte]
    suffices hT : monotoneExtension Λ (fun _ : X => (⊤ : WithTop ℝ)) = ⊤ by
      rw [hT]; rfl
    refine WithTop.eq_top_iff_forall_gt.2 fun m => ?_
    have h1 := le_monotoneExtension Λ (u := fun _ : X => (⊤ : WithTop ℝ))
      (fun _ => m + 1 - Λ 0) fun _ => le_top
    have h2 : Λ (fun _ => m + 1 - Λ 0) = m + 1 := by
      have := hadd 0 (m + 1 - Λ 0)
      simp only [Pi.zero_apply, zero_add] at this
      rw [this]; ring
    rw [h2] at h1
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.2 (by linarith)) h1
  have hr : kruzkovOp 0 Λ (fun _ => -ε) = -1 := by
    unfold kruzkovOp
    have hneg : -ε < 0 := by linarith
    simp only [kruzkovInv, hneg, ↓reduceIte, neg_zero, zero_mul]
    rw [monotoneExtension_const hmax hadd]
    simp [kruzkov]
  rw [hl, hr] at h
  have : ρ * (2 * ε) < 1 := by
    rw [hε]
    have h3 : ρ ≤ |ρ| := le_abs_self ρ
    have h4 : 0 < |ρ| + 1 := by positivity
    rw [show ρ * (2 * (1 / (2 * (|ρ| + 1)))) = ρ / (|ρ| + 1) by field_simp,
      div_lt_one h4]
    linarith
  linarith

theorem le_apply_zero_of_kruzkov_subAdditive' {X : Type*} {Λ : (X → ℝ) → ℝ} {α ρ : ℝ}
    (hα : 0 ≤ α) (hmax : ∀ w : X → ℝ, w ≤ 0 → Λ w ≤ Λ 0)
    (hadd : AdditivelyInvariant Λ) (hsub : SubAdditive ρ (kruzkovOp α Λ)) :
    -α * Real.log ρ ≤ Λ 0 := by
  rcases hα.eq_or_lt with rfl | hα
  · exact absurd hsub (not_subAdditive_zero hmax hadd ρ)
  have h := hsub (fun _ => -1) (1 / 2) (by norm_num)
  rw [kruzkovOp_const_neg hα.ne' hmax hadd (by norm_num),
    kruzkovOp_const_neg hα.ne' hmax hadd (by norm_num)] at h
  set e := Real.exp (-(1 / α) * Λ 0) with he
  have hle : e ≤ ρ := by linarith
  have hlog : -(1 / α) * Λ 0 ≤ Real.log ρ := by
    rw [← Real.log_exp (-(1 / α) * Λ 0)]
    exact Real.log_le_log (Real.exp_pos _) hle
  have : -(1 / α) * Λ 0 * α = -Λ 0 := by field_simp
  nlinarith

theorem le_apply_zero_of_kruzkov_subAdditive {X : Type*} {Λ : (X → ℝ) → ℝ} {α ρ : ℝ}
    (hα : 0 < α) (hmono : Monotone Λ)
    (hadd : AdditivelyInvariant Λ) (hsub : SubAdditive ρ (kruzkovOp α Λ)) :
    -α * Real.log ρ ≤ Λ 0 :=
  le_apply_zero_of_kruzkov_subAdditive' hα.le (fun _ hw => hmono hw) hadd hsub

end GuaranteedSubsol.Lambda0SubaddProof
