/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.Axioms
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Tactic.Linarith

/-!
# Comparison principle for a monotone `ρ`-sub-additive operator

Provider proof for the frozen anchor `GuaranteedSubsol.le_of_comparison` (see `ANCHORS.md`),
following Prop. prop:comparison_Phi (Complexity.tex): at a point `x` maximizing `u - v`, with
`t := u x - v x > 0`, one has `x ∈ I`, and monotonicity and sub-additivity at `x` give
`t ≤ Φ u x - Φ v x ≤ ρ t`, which contradicts `ρ < 1`.
-/

@[expose] public section

namespace GuaranteedSubsol.ComparisonProof

/-- At a point `x ∈ I` where `u - v` is maximal with value `t > 0`, the hypotheses force
`t ≤ ρ * t`. -/
theorem max_le_mul {X : Type*} {Φ : (X → ℝ) → X → ℝ} {ρ : ℝ} {I : Set X}
    (hmono : ∀ x ∈ I, Monotone (Φ · x)) (hsub : ∀ x ∈ I, SubAdditive ρ (Φ · x))
    {u v : X → ℝ} (hI : ∀ x ∈ I, u x - Φ u x ≤ v x - Φ v x) {x : X} (hx : x ∈ I)
    (hmax : ∀ y, u y - v y ≤ u x - v x) (ht : 0 ≤ u x - v x) :
    u x - v x ≤ ρ * (u x - v x) := by
  have hle : u ≤ fun y => v y + (u x - v x) := fun y => by linarith [hmax y]
  have h1 : Φ u x ≤ Φ (fun y => v y + (u x - v x)) x := hmono x hx hle
  have h2 := hsub x hx v (u x - v x) ht
  have h3 := hI x hx
  simp only at h2
  linarith

theorem le_of_comparison {X : Type*} [Finite X] {Φ : (X → ℝ) → X → ℝ} {ρ : ℝ} (hρ : ρ < 1)
    {I : Set X} (hmono : ∀ x ∈ I, Monotone (Φ · x)) (hsub : ∀ x ∈ I, SubAdditive ρ (Φ · x))
    {u v : X → ℝ} (hI : ∀ x ∈ I, u x - Φ u x ≤ v x - Φ v x) (hbd : ∀ x ∉ I, u x ≤ v x) :
    u ≤ v := by
  intro y
  have : Nonempty X := ⟨y⟩
  obtain ⟨x, hmax⟩ := Finite.exists_max fun z => u z - v z
  by_contra hyv
  have ht : 0 < u x - v x := by linarith [hmax y, not_le.1 hyv]
  have hx : x ∈ I := by
    by_contra hx
    linarith [hbd x hx]
  have := max_le_mul hmono hsub hI hx hmax ht.le
  nlinarith

end GuaranteedSubsol.ComparisonProof
