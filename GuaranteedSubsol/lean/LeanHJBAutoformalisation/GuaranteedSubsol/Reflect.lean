/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.Rescale

/-!
# Reflection of an operator

The reflected operator `Λ' u := -Λ[-u]`, for a scalar operator `Λ : (X → ℝ) → ℝ` or a global one
`Φ : (X → ℝ) → X → ℝ` (pointwise negation). For scalar operators it is `rescaleOp (-1) Λ`.
Reflection is an involution, and exchanges sub-solutions and super-solutions.

Monotonicity, additive invariance, `ρ`-sub-additivity (same `ρ`), the stencil and the comparison
principle are preserved (each an equivalence, by involutivity).

Not from the paper: introduced at the author's request.
-/

namespace GuaranteedSubsol

variable {X : Type*}

/-- Reflected operator `Λ' u := -Λ[-u]`, for `Λ` valued in `ℝ` (scalar operator) or in `X → ℝ`
(global operator). -/
def reflectOp {β : Type*} [Neg β] (Λ : (X → ℝ) → β) (u : X → ℝ) : β :=
  -Λ (-u)

theorem reflectOp_apply {β : Type*} [Neg β] (Λ : (X → ℝ) → β) (u : X → ℝ) :
    reflectOp Λ u = -Λ (-u) := rfl

/-- Global form, pointwise. -/
theorem reflectOp_apply_apply (Φ : (X → ℝ) → X → ℝ) (u : X → ℝ) (x : X) :
    reflectOp Φ u x = -Φ (-u) x := rfl

/-- The scalar form at `x` of the reflected global operator is the reflected scalar form. -/
theorem reflectOp_comp_eval (Φ : (X → ℝ) → X → ℝ) (x : X) :
    (reflectOp Φ · x) = reflectOp (Φ · x) := rfl

theorem reflectOp_reflectOp {β : Type*} [InvolutiveNeg β] (Λ : (X → ℝ) → β) :
    reflectOp (reflectOp Λ) = Λ := by
  funext u
  simp [reflectOp]

/-- Reflection is the rescaling with `α = -1`. -/
theorem reflectOp_eq_rescaleOp (Λ : (X → ℝ) → ℝ) : reflectOp Λ = rescaleOp (-1) Λ := by
  funext u
  simp only [reflectOp, rescaleOp, neg_one_mul, div_neg, div_one]
  rfl

section Order

variable {β : Type*} [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]

theorem Monotone.reflectOp {Λ : (X → ℝ) → β} (h : Monotone Λ) : Monotone (reflectOp Λ) :=
  fun _ _ huv => neg_le_neg (h (neg_le_neg huv))

theorem monotone_reflectOp_iff {Λ : (X → ℝ) → β} : Monotone (reflectOp Λ) ↔ Monotone Λ :=
  ⟨fun h => reflectOp_reflectOp Λ ▸ GuaranteedSubsol.Monotone.reflectOp h,
    GuaranteedSubsol.Monotone.reflectOp⟩

end Order

variable {Λ : (X → ℝ) → ℝ}

theorem AdditivelyInvariant.reflectOp (h : AdditivelyInvariant Λ) :
    AdditivelyInvariant (reflectOp Λ) := by
  intro u t
  have e : -(fun y => u y + t) = fun y => (-u) y + -t := by
    funext y; simp only [Pi.neg_apply]; ring
  simp only [GuaranteedSubsol.reflectOp]
  rw [e, h]
  ring

theorem additivelyInvariant_reflectOp_iff :
    AdditivelyInvariant (reflectOp Λ) ↔ AdditivelyInvariant Λ :=
  ⟨fun h => reflectOp_reflectOp Λ ▸ h.reflectOp, fun h => h.reflectOp⟩

theorem SubAdditive.reflectOp {ρ : ℝ} (h : SubAdditive ρ Λ) : SubAdditive ρ (reflectOp Λ) := by
  intro v t ht
  have key := h (fun y => -v y - t) t ht
  have e1 : (fun y => -v y - t + t) = -v := by funext y; simp
  have e2 : (fun y => -v y - t) = -(fun y => v y + t) := by funext y; simp only [Pi.neg_apply]; ring
  rw [e1, e2] at key
  simp only [GuaranteedSubsol.reflectOp]
  linarith

theorem subAdditive_reflectOp_iff {ρ : ℝ} : SubAdditive ρ (reflectOp Λ) ↔ SubAdditive ρ Λ :=
  ⟨fun h => reflectOp_reflectOp Λ ▸ h.reflectOp, fun h => h.reflectOp⟩

theorem HasStencil.reflectOp {V : Set X} (h : HasStencil V Λ) : HasStencil V (reflectOp Λ) := by
  intro u v huv
  simp only [GuaranteedSubsol.reflectOp]
  rw [h (-u) (-v) fun y hy => by simp [huv y hy]]

theorem hasStencil_reflectOp_iff {V : Set X} : HasStencil V (reflectOp Λ) ↔ HasStencil V Λ :=
  ⟨fun h => reflectOp_reflectOp Λ ▸ h.reflectOp, fun h => h.reflectOp⟩

section Global

variable {Φ : (X → ℝ) → X → ℝ}

/-- Sub-solutions of the reflection are the negatives of super-solutions. -/
theorem le_reflectOp_iff {u : X → ℝ} : u ≤ reflectOp Φ u ↔ Φ (-u) ≤ -u := by
  constructor <;> intro h x <;> have := h x <;> simp only [reflectOp_apply_apply,
    Pi.neg_apply] at this ⊢ <;> linarith

/-- Super-solutions of the reflection are the negatives of sub-solutions. -/
theorem reflectOp_le_iff {u : X → ℝ} : reflectOp Φ u ≤ u ↔ -u ≤ Φ (-u) := by
  constructor <;> intro h x <;> have := h x <;> simp only [reflectOp_apply_apply,
    Pi.neg_apply] at this ⊢ <;> linarith

/-- Fixed points of the reflection are the negatives of fixed points. -/
theorem reflectOp_eq_iff {u : X → ℝ} : reflectOp Φ u = u ↔ Φ (-u) = -u := by
  rw [le_antisymm_iff, le_antisymm_iff, reflectOp_le_iff, le_reflectOp_iff, and_comm]

theorem HasComparisonPrinciple.reflectOp {I : Set X} (h : HasComparisonPrinciple I Φ) :
    HasComparisonPrinciple I (reflectOp Φ) := by
  intro u v hu hv hout
  have key := h (-v) (-u) (fun x hx => by
      have := hv x hx; simp only [reflectOp_apply_apply, Pi.neg_apply] at this ⊢; linarith)
    (fun x hx => by
      have := hu x hx; simp only [reflectOp_apply_apply, Pi.neg_apply] at this ⊢; linarith)
    (fun x hx => by have := hout x hx; simp only [Pi.neg_apply]; linarith)
  exact fun x => by have := key x; simp only [Pi.neg_apply] at this; linarith

theorem hasComparisonPrinciple_reflectOp_iff {I : Set X} :
    HasComparisonPrinciple I (reflectOp Φ) ↔ HasComparisonPrinciple I Φ :=
  ⟨fun h => reflectOp_reflectOp Φ ▸ h.reflectOp, fun h => h.reflectOp⟩

end Global

end GuaranteedSubsol
