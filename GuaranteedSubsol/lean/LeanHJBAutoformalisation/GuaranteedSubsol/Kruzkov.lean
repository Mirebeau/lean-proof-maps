/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Kruzkov transform of GuaranteedSubsolutions (Introduction)

Kruzkov change of variables `E_α : ℝ_∞ → ℝ` and its left inverse `E_α⁻¹ : ℝ → ℝ_∞`, from the
Introduction (`Include/Intro.tex`, eq. (Kruzkov)) of the preprint GuaranteedSubsolutions.

`ℝ_∞ = ]-∞,∞]` is modelled as `WithTop ℝ`.

REVIEW: `kruzkov` takes the inverse timescale `αinv = 1/α`, while `kruzkovInv` takes `α`. The
paper's `E_α` and `E_α⁻¹` correspond to `kruzkov (1/α)` and `kruzkovInv α`,
with `α > 0` to be stated as a theorem hypothesis.
-/

@[expose] public section

namespace GuaranteedSubsol

/-- Kruzkov transform `E_α : ℝ_∞ → ℝ` (Intro.tex eq. (Kruzkov)), with `αinv = 1/α`:
`E_α u = -exp(-αinv * u)` if `u < ∞`, and `0` otherwise. -/
noncomputable def kruzkov (αinv : ℝ) : WithTop ℝ → ℝ
  | ⊤ => 0
  | (u : ℝ) => -Real.exp (-αinv * u)

/-- Left inverse `E_α⁻¹ : ℝ → ℝ_∞` of the Kruzkov transform (Intro.tex eq. (Kruzkov)):
`E_α⁻¹ v = -α ln(-v)` if `v < 0`, and `∞` otherwise. -/
noncomputable def kruzkovInv (α : ℝ) (v : ℝ) : WithTop ℝ :=
  if v < 0 then ((-α * Real.log (-v) : ℝ) : WithTop ℝ) else ⊤

variable {X : Type*}

/-- Extension `Λ_∞ : ℝ_∞^X → ℝ_∞` of an operator to positively infinite values
(Intro.tex eq. eqdef:monotone_extension), defined as the supremum of `Λ w` over all finite
minorants `w ≤ u`.

REVIEW: this generalizes the paper, which defines `Λ_∞ u := lim_{t→∞} Λ min {u,t}` only for
monotone `Λ`. Here `Λ` is arbitrary; agreement with the paper's limit for monotone `Λ` is proved
in `MonotoneExtension.lean`. The supremum is taken over a subtype (never empty) rather than with a
`Prop` binder, because in `WithTop ℝ` the supremum of the empty set is `0`, not `⊥`. -/
noncomputable def monotoneExtension (Λ : (X → ℝ) → ℝ) (u : X → WithTop ℝ) : WithTop ℝ :=
  ⨆ w : {w : X → ℝ // ∀ y, (w y : WithTop ℝ) ≤ u y}, ((Λ w : ℝ) : WithTop ℝ)

/-- Operator in Kruzkov coordinates `Φ_α := E_α Λ_∞ E_α⁻¹` (Intro.tex eq. (Phi)), scalar form. -/
noncomputable def kruzkovOp (α : ℝ) (Λ : (X → ℝ) → ℝ) (v : X → ℝ) : ℝ :=
  kruzkov (1 / α) (monotoneExtension Λ fun y => kruzkovInv α (v y))

namespace Global

/-- Global form of `monotoneExtension`: the extension `Λ_∞ : ℝ_∞^X → ℝ_∞^X` of a global operator
`Λ : ℝ^X → ℝ^X`, applied pointwise, `Λ_∞ u (x) := (Λ · x)_∞ u` (Intro.tex
eq. eqdef:monotone_extension). It agrees with the paper's limit when `Λ` is monotone, see the
REVIEW note of `monotoneExtension`. -/
noncomputable def monotoneExtension (Λ : (X → ℝ) → X → ℝ) (u : X → WithTop ℝ) : X → WithTop ℝ :=
  fun x => _root_.GuaranteedSubsol.monotoneExtension (Λ · x) u

/-- Global form of `kruzkovOp`: the operator in Kruzkov coordinates `Φ_α := E_α Λ_∞ E_α⁻¹` of a
global operator `Λ : ℝ^X → ℝ^X` (Intro.tex eq. (Phi)), `Φ_α v x := kruzkovOp α (Λ · x) v`. -/
noncomputable def kruzkovOp (α : ℝ) (Λ : (X → ℝ) → X → ℝ) (v : X → ℝ) : X → ℝ :=
  fun x => _root_.GuaranteedSubsol.kruzkovOp α (Λ · x) v

end Global

end GuaranteedSubsol
