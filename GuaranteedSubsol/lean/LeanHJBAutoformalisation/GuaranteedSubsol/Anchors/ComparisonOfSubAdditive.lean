/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ComparisonProof

/-!
# Frozen statement: comparison principle for a monotone `ρ`-sub-additive operator

Source: Prop. prop:comparison_Phi (Complexity.tex): if `Φ : ℝ^X → ℝ^X` is monotone and
`ρ`-sub-additive with `ρ < 1`, then for any partition `X = Int Y ⊔ ∂Y` and `u, v ∈ ℝ^X`,
`(u - Φ u ≤ v - Φ v on Int Y, and u ≤ v on ∂Y) ⇒ u ≤ v`.

`Int Y` is the set `I`, and `∂Y` its complement. Monotonicity and sub-additivity are only
assumed at the points of `I` (the paper assumes them everywhere; the proof only uses them at a
point of `Int Y`). `X` is finite, as throughout the paper.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem le_of_comparison {X : Type*} [Finite X] {Φ : (X → ℝ) → X → ℝ} {ρ : ℝ} (hρ : ρ < 1)
    {I : Set X} (hmono : ∀ x ∈ I, Monotone (Φ · x)) (hsub : ∀ x ∈ I, SubAdditive ρ (Φ · x))
    {u v : X → ℝ} (hI : ∀ x ∈ I, u x - Φ u x ≤ v x - Φ v x) (hbd : ∀ x ∉ I, u x ≤ v x) :
    u ≤ v := by
  exact ComparisonProof.le_of_comparison hρ hmono hsub hI hbd

end GuaranteedSubsol
