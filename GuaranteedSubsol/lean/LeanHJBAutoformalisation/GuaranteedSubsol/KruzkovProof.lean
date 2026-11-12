/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.Axioms
import LeanHJBAutoformalisation.GuaranteedSubsol.Kruzkov
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Kruzkov operator: monotonicity and multiplicative invariance

Provider proofs for the frozen anchors `GuaranteedSubsol.monotone_monotoneExtension`,
`GuaranteedSubsol.monotone_kruzkovOp` and `GuaranteedSubsol.kruzkovOp_mul` (see `ANCHORS.md`),
from Prop. prop:monotonic_Phi (Complexity.tex). No monotonicity of `Λ` is needed, thanks to the
generalized `monotoneExtension` (supremum over finite minorants).
-/

namespace GuaranteedSubsol.KruzkovProof

variable {X : Type*}

/-- The index type of `monotoneExtension Λ u` (finite minorants of `u`) is nonempty. -/
theorem nonempty_minorant (u : X → WithTop ℝ) :
    Nonempty {w : X → ℝ // ∀ y, (w y : WithTop ℝ) ≤ u y} := by
  refine ⟨⟨fun y => min ((u y).untopD 0) 0, fun y => ?_⟩⟩
  cases h : u y with
  | top => exact le_top
  | coe r => exact WithTop.coe_le_coe.2 (by simp [h])

/-- `Λ w ≤ monotoneExtension Λ u` for every finite minorant `w` of `u`. -/
theorem le_monotoneExtension (Λ : (X → ℝ) → ℝ) {u : X → WithTop ℝ} (w : X → ℝ)
    (hw : ∀ y, (w y : WithTop ℝ) ≤ u y) :
    ((Λ w : ℝ) : WithTop ℝ) ≤ monotoneExtension Λ u :=
  le_ciSup (f := fun w : {w : X → ℝ // ∀ y, (w y : WithTop ℝ) ≤ u y} =>
    ((Λ w : ℝ) : WithTop ℝ)) (OrderTop.bddAbove _) ⟨w, hw⟩

theorem monotone_monotoneExtension {X : Type*} (Λ : (X → ℝ) → ℝ) :
    Monotone (monotoneExtension Λ) := by
  intro u u' huu'
  have := nonempty_minorant u
  exact ciSup_le fun w => le_monotoneExtension Λ w.1 fun y => (w.2 y).trans (huu' y)

/-- For `α > 0`, the inverse Kruzkov transform `E_α⁻¹` is monotone. -/
theorem monotone_kruzkovInv {α : ℝ} (hα : 0 < α) : Monotone (kruzkovInv α) := by
  intro v v' hvv'
  unfold kruzkovInv
  by_cases hv' : v' < 0
  · have hv : v < 0 := lt_of_le_of_lt hvv' hv'
    simp only [hv, hv', ↓reduceIte]
    refine WithTop.coe_le_coe.2 ?_
    have : Real.log (-v') ≤ Real.log (-v) := Real.log_le_log (by linarith) (by linarith)
    nlinarith
  · simp only [hv', ↓reduceIte]
    exact le_top

/-- For `α > 0`, the Kruzkov transform `E_α` is monotone. -/
theorem monotone_kruzkov {α : ℝ} (hα : 0 < α) : Monotone (kruzkov (1 / α)) := by
  intro z z' hzz'
  cases z' with
  | top =>
    cases z with
    | top => exact le_rfl
    | coe r => exact (neg_nonpos.2 (Real.exp_pos _).le)
  | coe r' =>
    cases z with
    | top => exact absurd hzz' (by simp)
    | coe r =>
      have hr : r ≤ r' := WithTop.coe_le_coe.1 hzz'
      have hα' : 0 < 1 / α := by positivity
      change -Real.exp (-(1 / α) * r) ≤ -Real.exp (-(1 / α) * r')
      refine neg_le_neg (Real.exp_le_exp.2 ?_)
      nlinarith

theorem monotone_kruzkovOp {X : Type*} {α : ℝ} (hα : 0 < α) (Λ : (X → ℝ) → ℝ) :
    Monotone (kruzkovOp α Λ) := fun _ _ hvv' =>
  monotone_kruzkov hα (monotone_monotoneExtension Λ fun y => monotone_kruzkovInv hα (hvv' y))

/-- `E_α⁻¹ (γ v) = E_α⁻¹ v - α log γ` for `γ > 0`. -/
theorem kruzkovInv_mul (α : ℝ) {γ : ℝ} (hγ : 0 < γ) (v : ℝ) :
    kruzkovInv α (γ * v) = kruzkovInv α v + ((-α * Real.log γ : ℝ) : WithTop ℝ) := by
  unfold kruzkovInv
  by_cases hv : v < 0
  · have hγv : γ * v < 0 := mul_neg_of_pos_of_neg hγ hv
    simp only [hv, hγv, ↓reduceIte]
    rw [← WithTop.coe_add, neg_mul_eq_mul_neg,
      Real.log_mul hγ.ne' (by linarith)]
    congr 1
    ring
  · have hγv : ¬ γ * v < 0 := fun h => hv (by nlinarith)
    simp only [hv, hγv, ↓reduceIte, WithTop.top_add]

/-- One inequality of `monotoneExtension Λ (u + c) = monotoneExtension Λ u + c`, for
additively invariant `Λ`. -/
theorem monotoneExtension_add_const_le {Λ : (X → ℝ) → ℝ} (hadd : AdditivelyInvariant Λ)
    (u : X → WithTop ℝ) (c : ℝ) :
    monotoneExtension Λ (fun y => u y + c) ≤ monotoneExtension Λ u + c := by
  have := nonempty_minorant fun y => u y + c
  refine ciSup_le fun w => ?_
  have hw : ∀ y, ((w.1 y - c : ℝ) : WithTop ℝ) ≤ u y := by
    intro y
    have h : (w.1 y : WithTop ℝ) ≤ u y + c := w.2 y
    cases hu : u y with
    | top => exact le_top
    | coe r =>
      rw [hu, ← WithTop.coe_add] at h
      exact WithTop.coe_le_coe.2 (by linarith [WithTop.coe_le_coe.1 h])
  have hΛ : Λ w.1 = Λ (fun y => w.1 y - c) + c := by
    rw [← hadd]
    simp
  rw [hΛ, WithTop.coe_add]
  exact add_le_add_left (le_monotoneExtension Λ _ hw) _

/-- For additively invariant `Λ`, `monotoneExtension Λ (u + c) = monotoneExtension Λ u + c`. -/
theorem monotoneExtension_add_const {Λ : (X → ℝ) → ℝ} (hadd : AdditivelyInvariant Λ)
    (u : X → WithTop ℝ) (c : ℝ) :
    monotoneExtension Λ (fun y => u y + c) = monotoneExtension Λ u + c := by
  refine le_antisymm (monotoneExtension_add_const_le hadd u c) ?_
  have h := monotoneExtension_add_const_le hadd (fun y => u y + c) (-c)
  have hu : (fun y => u y + (c : WithTop ℝ) + ((-c : ℝ) : WithTop ℝ)) = u := by
    funext y
    rw [add_assoc, ← WithTop.coe_add, add_neg_cancel, WithTop.coe_zero, add_zero]
  rw [hu] at h
  calc monotoneExtension Λ u + c
      ≤ monotoneExtension Λ (fun y => u y + c) + ((-c : ℝ) : WithTop ℝ) + c :=
        add_le_add_left h _
    _ = monotoneExtension Λ (fun y => u y + c) := by
        rw [add_assoc, ← WithTop.coe_add, neg_add_cancel, WithTop.coe_zero, add_zero]

/-- `E_α (z + c) = exp (-(1/α) c) E_α z`. -/
theorem kruzkov_add_const (αinv : ℝ) (z : WithTop ℝ) (c : ℝ) :
    kruzkov αinv (z + c) = Real.exp (-αinv * c) * kruzkov αinv z := by
  cases z with
  | top => simp [kruzkov]
  | coe r =>
    rw [← WithTop.coe_add]
    change -Real.exp (-αinv * (r + c)) = Real.exp (-αinv * c) * -Real.exp (-αinv * r)
    rw [mul_neg, ← Real.exp_add]
    ring_nf

theorem kruzkovOp_mul {X : Type*} {α : ℝ} (hα : 0 < α) {Λ : (X → ℝ) → ℝ}
    (hadd : AdditivelyInvariant Λ) {γ : ℝ} (hγ : 0 < γ) (v : X → ℝ) :
    kruzkovOp α Λ (fun y => γ * v y) = γ * kruzkovOp α Λ v := by
  unfold kruzkovOp
  simp_rw [kruzkovInv_mul α hγ]
  rw [monotoneExtension_add_const hadd, kruzkov_add_const]
  congr 1
  rw [show -(1 / α) * (-α * Real.log γ) = Real.log γ by field_simp, Real.exp_log hγ]

end GuaranteedSubsol.KruzkovProof
