/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.Axioms
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Perturbation into sub- and super-solutions

Provider proofs for the frozen anchors `GuaranteedSubsol.subSolution_of_subAdditive` and
`GuaranteedSubsol.superSolution_of_subAdditive` (see `ANCHORS.md`), i.e. Prop. prop:pertSubSuper
(Complexity.tex) in scalar form: for a `ρ`-sub-additive `Λ` with `ρ < 1`, shifting `u` by
`t := c / (1 - ρ)` absorbs a residual `c ≥ 0`, using the identity `c + ρ t = t`.
-/

@[expose] public section

namespace GuaranteedSubsol.PertSubSuperProof

/-- The shift `c / (1 - ρ)` is nonnegative when `c ≥ 0` and `ρ < 1`. -/
theorem shift_nonneg {ρ c : ℝ} (hρ : ρ < 1) (hc : 0 ≤ c) : 0 ≤ c / (1 - ρ) :=
  div_nonneg hc (by linarith)

/-- The key identity `c + ρ t = t` for the shift `t = c / (1 - ρ)`. -/
theorem shift_identity {ρ c : ℝ} (hρ : ρ < 1) : c + ρ * (c / (1 - ρ)) = c / (1 - ρ) := by
  have h : (1 - ρ) ≠ 0 := by linarith
  field_simp
  ring

theorem subSolution_of_subAdditive {X : Type*} {Λ : (X → ℝ) → ℝ} {ρ : ℝ} (hρ : ρ < 1)
    (hsub : SubAdditive ρ Λ) {u : X → ℝ} {x : X} {c : ℝ} (hc : 0 ≤ c) (hu : u x - c ≤ Λ u) :
    u x - c / (1 - ρ) ≤ Λ (fun y => u y - c / (1 - ρ)) := by
  have key := hsub (fun y => u y - c / (1 - ρ)) (c / (1 - ρ)) (shift_nonneg hρ hc)
  have hfun : (fun y => (fun y => u y - c / (1 - ρ)) y + c / (1 - ρ)) = u := by
    funext y
    ring
  rw [hfun] at key
  linarith [shift_identity (c := c) hρ]

theorem superSolution_of_subAdditive {X : Type*} {Λ : (X → ℝ) → ℝ} {ρ : ℝ} (hρ : ρ < 1)
    (hsub : SubAdditive ρ Λ) {u : X → ℝ} {x : X} {c : ℝ} (hc : 0 ≤ c) (hu : Λ u ≤ u x + c) :
    Λ (fun y => u y + c / (1 - ρ)) ≤ u x + c / (1 - ρ) := by
  have key := hsub u (c / (1 - ρ)) (shift_nonneg hρ hc)
  linarith [shift_identity (c := c) hρ]

end GuaranteedSubsol.PertSubSuperProof
