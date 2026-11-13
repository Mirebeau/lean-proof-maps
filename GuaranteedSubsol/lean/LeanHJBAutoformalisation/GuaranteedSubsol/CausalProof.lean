/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.Axioms
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Tactic.Linarith

/-!
# Comparison principle for a monotone causal operator

Provider proof for the frozen anchor `GuaranteedSubsol.le_of_causal_real` (see `ANCHORS.md`),
Prop. prop:comp_of_causal of Complexity.tex on finite values: if `Γ` is monotone and causal on
`I`, then a subsolution `u` and a supersolution `v` on `I`, ordered on the complement of `I`,
are ordered everywhere.

The proof is by contradiction: at a point `x` minimizing `v` among the points where `v < u`,
with `t := v x`, the truncations `min u t ≤ min v t` are ordered, and causality at `x` transfers
the resulting inequality `Γ (min u t) x ≤ Γ (min v t) x` to `Γ u x` and `Γ v x` above level `t`.
-/

@[expose] public section

namespace GuaranteedSubsol.CausalProof

/-- If every point with `v y < u y` satisfies `t ≤ v y`, then the truncations at level `t`
are ordered: `min u t ≤ min v t`. -/
theorem min_le_min_of_forall {X : Type*} {u v : X → ℝ} {t : ℝ}
    (h : ∀ y, v y < u y → t ≤ v y) : (fun y => min (u y) t) ≤ fun y => min (v y) t := by
  intro y
  by_cases hy : u y ≤ v y
  · exact min_le_min_right t hy
  · change min (u y) t ≤ min (v y) t
    rw [min_eq_right (h y (not_le.1 hy))]
    exact min_le_right _ _

theorem le_of_causal_real {X : Type*} [Finite X] {Γ : (X → ℝ) → X → ℝ} {I : Set X}
    (hmono : ∀ x ∈ I, Monotone (Γ · x)) (hcaus : ∀ x ∈ I, Causal (Γ · x)) {u v : X → ℝ}
    (hu : ∀ x ∈ I, u x ≤ Γ u x) (hv : ∀ x ∈ I, Γ v x ≤ v x) (hbd : ∀ x ∉ I, u x ≤ v x) :
    u ≤ v := by
  intro y₀
  by_contra h₀
  obtain ⟨x, hxS, hxmin⟩ := Set.exists_min_image {y | v y < u y} v (Set.toFinite _)
    ⟨y₀, not_le.1 h₀⟩
  simp only [Set.mem_ofPred_eq] at hxS hxmin
  have hxI : x ∈ I := by
    by_contra hx
    exact absurd (hbd x hx) (not_le.2 hxS)
  have hΓ : Γ (fun y => min (u y) (v x)) x ≤ Γ (fun y => min (v y) (v x)) x :=
    hmono x hxI (min_le_min_of_forall hxmin)
  obtain ⟨δ₁, hδ₁, h₁⟩ := hcaus x hxI u (fun y => min (u y) (v x)) (v x) (fun y => by simp)
  obtain ⟨δ₂, hδ₂, h₂⟩ := hcaus x hxI v (fun y => min (v y) (v x)) (v x) (fun y => by simp)
  have k₁ : v x < min (Γ u x) (v x + δ₁) := lt_min (by linarith [hu x hxI]) (by linarith)
  have k₂ : v x < Γ (fun y => min (u y) (v x)) x := (lt_min_iff.1 (k₁.trans_eq h₁)).1
  have k₃ : v x < min (Γ (fun y => min (v y) (v x)) x) (v x + δ₂) :=
    lt_min (by linarith) (by linarith)
  have k₄ : v x < Γ v x := (lt_min_iff.1 (k₃.trans_eq h₂.symm)).1
  linarith [hv x hxI]

end GuaranteedSubsol.CausalProof
