/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AxiomsExt
import Mathlib.Basic.Finite.Defs
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Comparison principle for a monotone causal operator on `ℝ_∞`

Provider proof for the frozen anchor `GuaranteedSubsol.le_of_causal_ext` (see `ANCHORS.md`),
Prop. prop:comp_of_causal of Complexity.tex with values in `ℝ_∞ = WithTop ℝ`: if `Γ` is monotone
and causal (`Ext.Causal`) on `I`, then a subsolution `u` and a supersolution `v` on `I`, ordered
on the complement of `I`, are ordered everywhere.

The proof follows `CausalProof.le_of_causal_real`: at a point `x` minimizing `v` among the points
where `v < u`, the value `v x` is finite, say `v x = t`; the truncations `min u t ≤ min v t` are
ordered, and causality at `x` transfers `Γ (min u t) x ≤ Γ (min v t) x` to `Γ u x` and `Γ v x`
above level `t`.
-/

namespace GuaranteedSubsol.CausalExtProof

/-- If every point with `v y < u y` satisfies `t ≤ v y`, then the truncations at level `t`
are ordered: `min u t ≤ min v t` (in `ℝ_∞`). -/
theorem min_le_min_of_forall {X : Type*} {u v : X → WithTop ℝ} {t : WithTop ℝ}
    (h : ∀ y, v y < u y → t ≤ v y) : (fun y => min (u y) t) ≤ fun y => min (v y) t := by
  intro y
  by_cases hy : u y ≤ v y
  · exact min_le_min_right t hy
  · change min (u y) t ≤ min (v y) t
    rw [min_eq_right (h y (not_le.1 hy))]
    exact min_le_right _ _

theorem le_of_causal_ext {X : Type*} [Finite X] {Γ : (X → WithTop ℝ) → X → WithTop ℝ}
    {I : Set X} (hmono : ∀ x ∈ I, Monotone (Γ · x)) (hcaus : ∀ x ∈ I, Ext.Causal (Γ · x))
    {u v : X → WithTop ℝ} (hu : ∀ x ∈ I, u x ≤ Γ u x) (hv : ∀ x ∈ I, Γ v x ≤ v x)
    (hbd : ∀ x ∉ I, u x ≤ v x) :
    u ≤ v := by
  intro y₀
  by_contra h₀
  obtain ⟨x, hxS, hxmin⟩ := Set.exists_min_image {y | v y < u y} v (Set.toFinite _)
    ⟨y₀, not_le.1 h₀⟩
  simp only [Set.mem_ofPred_eq] at hxS hxmin
  have hxI : x ∈ I := by
    by_contra hx
    exact absurd (hbd x hx) (not_le.2 hxS)
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 (hxS.trans_le le_top).ne
  rw [← ht] at hxS hxmin
  have hΓ : Γ (fun y => min (u y) (t : WithTop ℝ)) x ≤ Γ (fun y => min (v y) (t : WithTop ℝ)) x :=
    hmono x hxI (min_le_min_of_forall hxmin)
  obtain ⟨δ₁, hδ₁, h₁⟩ := hcaus x hxI u (fun y => min (u y) (t : WithTop ℝ)) t (fun y => by simp)
  obtain ⟨δ₂, hδ₂, h₂⟩ := hcaus x hxI v (fun y => min (v y) (t : WithTop ℝ)) t (fun y => by simp)
  have k₁ : (t : WithTop ℝ) < min (Γ u x) ((t + δ₁ : ℝ) : WithTop ℝ) :=
    lt_min (hxS.trans_le (hu x hxI)) (WithTop.coe_lt_coe.2 (by linarith))
  have k₂ : (t : WithTop ℝ) < Γ (fun y => min (u y) (t : WithTop ℝ)) x :=
    (lt_min_iff.1 (k₁.trans_eq h₁)).1
  have k₃ : (t : WithTop ℝ) < min (Γ (fun y => min (v y) (t : WithTop ℝ)) x)
      ((t + δ₂ : ℝ) : WithTop ℝ) :=
    lt_min (k₂.trans_le hΓ) (WithTop.coe_lt_coe.2 (by linarith))
  have k₄ : (t : WithTop ℝ) < Γ v x := (lt_min_iff.1 (k₃.trans_eq h₂.symm)).1
  exact absurd (hv x hxI) (not_le.2 (ht ▸ k₄))

end GuaranteedSubsol.CausalExtProof
