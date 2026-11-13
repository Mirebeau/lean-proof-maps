/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.Axioms
public import LeanHJBAutoformalisation.GuaranteedSubsol.Restriction

/-!
# Restriction of an operator: monotonicity and partial application

Provider proofs for the frozen anchors `GuaranteedSubsol.monotone_restrictOp`,
`GuaranteedSubsol.restrictOp_superSolution` and `GuaranteedSubsol.restrictOp_subSolution`
(see `ANCHORS.md`): Lemma lem:monDom (monotone case) and Prop. prop:partialMonotone
(Complexity.tex). If `Λ` is monotonic then so is `Λ_B`, and `Λ_B` maps super-solutions
(resp. sub-solutions) of `Λ` to super-solutions (resp. sub-solutions).
-/

@[expose] public section

namespace GuaranteedSubsol.RestrictionProof

/-- Super-solution sandwich: if `Λ u ≤ u` then `Λ u ≤ Λ_B u`. -/
theorem le_restrictOp_of_le {X : Type*} {Λ : (X → ℝ) → X → ℝ} (B : Set X) {u : X → ℝ}
    (hu : Λ u ≤ u) : Λ u ≤ restrictOp Λ B u := fun x => by
  by_cases hx : x ∈ B
  · rw [restrictOp_of_mem u hx]
  · rw [restrictOp_of_notMem u hx]; exact hu x

/-- Super-solution sandwich: if `Λ u ≤ u` then `Λ_B u ≤ u`. -/
theorem restrictOp_le_of_le {X : Type*} {Λ : (X → ℝ) → X → ℝ} (B : Set X) {u : X → ℝ}
    (hu : Λ u ≤ u) : restrictOp Λ B u ≤ u := fun x => by
  by_cases hx : x ∈ B
  · rw [restrictOp_of_mem u hx]; exact hu x
  · rw [restrictOp_of_notMem u hx]

/-- Sub-solution sandwich: if `u ≤ Λ u` then `u ≤ Λ_B u`. -/
theorem le_restrictOp_of_ge {X : Type*} {Λ : (X → ℝ) → X → ℝ} (B : Set X) {u : X → ℝ}
    (hu : u ≤ Λ u) : u ≤ restrictOp Λ B u := fun x => by
  by_cases hx : x ∈ B
  · rw [restrictOp_of_mem u hx]; exact hu x
  · rw [restrictOp_of_notMem u hx]

/-- Sub-solution sandwich: if `u ≤ Λ u` then `Λ_B u ≤ Λ u`. -/
theorem restrictOp_le_of_ge {X : Type*} {Λ : (X → ℝ) → X → ℝ} (B : Set X) {u : X → ℝ}
    (hu : u ≤ Λ u) : restrictOp Λ B u ≤ Λ u := fun x => by
  by_cases hx : x ∈ B
  · rw [restrictOp_of_mem u hx]
  · rw [restrictOp_of_notMem u hx]; exact hu x

/-- Lemma lem:monDom (Complexity.tex), monotone case: `Λ_B` is monotonic if `Λ` is. -/
theorem monotone_restrictOp {X : Type*} {Λ : (X → ℝ) → X → ℝ} (hΛ : Monotone Λ)
    (B : Set X) : Monotone (restrictOp Λ B) := fun u v huv x => by
  by_cases hx : x ∈ B
  · rw [restrictOp_of_mem u hx, restrictOp_of_mem v hx]; exact hΛ huv x
  · rw [restrictOp_of_notMem u hx, restrictOp_of_notMem v hx]; exact huv x

/-- Prop. prop:partialMonotone (Complexity.tex): `Λ_B` preserves super-solutions. -/
theorem restrictOp_superSolution {X : Type*} {Λ : (X → ℝ) → X → ℝ} (hΛ : Monotone Λ)
    (B : Set X) {u : X → ℝ} (hu : Λ u ≤ u) :
    Λ (restrictOp Λ B u) ≤ restrictOp Λ B u :=
  (hΛ (restrictOp_le_of_le B hu)).trans (le_restrictOp_of_le B hu)

/-- Prop. prop:partialMonotone (Complexity.tex): `Λ_B` preserves sub-solutions. -/
theorem restrictOp_subSolution {X : Type*} {Λ : (X → ℝ) → X → ℝ} (hΛ : Monotone Λ)
    (B : Set X) {u : X → ℝ} (hu : u ≤ Λ u) :
    restrictOp Λ B u ≤ Λ (restrictOp Λ B u) :=
  (restrictOp_le_of_ge B hu).trans (hΛ (le_restrictOp_of_ge B hu))

end GuaranteedSubsol.RestrictionProof
