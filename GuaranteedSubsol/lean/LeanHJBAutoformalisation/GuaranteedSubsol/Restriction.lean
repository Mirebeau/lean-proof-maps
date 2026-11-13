/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Piecewise

/-!
# Restriction of an operator to a subdomain

The restriction `Λ_B` of an operator `Λ : ℝ^X → ℝ^X` to a subdomain `B ⊆ X`, defined after
Prop. prop:monotonic_Phi (Complexity.tex): `Λ_B u (x) = Λ u (x)` if `x ∈ B`, and `u (x)` otherwise.

This is a global operator `(X → ℝ) → X → ℝ`; at a point `x ∈ B` its scalar form is `(Λ · x)`, and
at `x ∉ B` it is the evaluation `u ↦ u x`.
-/

@[expose] public section

namespace GuaranteedSubsol

variable {X : Type*}

open Classical in
/-- Restriction `Λ_B` of an operator `Λ` to a subdomain `B` (Complexity.tex, after
Prop. prop:monotonic_Phi): `Λ_B u (x) := Λ u (x)` if `x ∈ B`, and `u (x)` otherwise. -/
noncomputable def restrictOp (Λ : (X → ℝ) → X → ℝ) (B : Set X) (u : X → ℝ) : X → ℝ :=
  B.piecewise (Λ u) u

theorem restrictOp_of_mem {Λ : (X → ℝ) → X → ℝ} {B : Set X} (u : X → ℝ) {x : X} (hx : x ∈ B) :
    restrictOp Λ B u x = Λ u x := by
  classical
  simp [restrictOp, hx]

theorem restrictOp_of_notMem {Λ : (X → ℝ) → X → ℝ} {B : Set X} (u : X → ℝ) {x : X}
    (hx : x ∉ B) : restrictOp Λ B u x = u x := by
  classical
  simp [restrictOp, hx]

end GuaranteedSubsol
