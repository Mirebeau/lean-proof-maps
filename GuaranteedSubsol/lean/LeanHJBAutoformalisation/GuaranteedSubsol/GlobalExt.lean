/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AxiomsExt
import Mathlib.Basic.Finite.Defs
import Mathlib.Data.Fintype.Lattice

/-!
# Global scheme axioms for operators on `ℝ_∞`

Global forms of the `Ext` axioms of `AxiomsExt.lean`, for operators `Λ : (X → ℝ_∞) → X → ℝ_∞`,
where `ℝ_∞ = WithTop ℝ`. The paper (`Include/Intro.tex`) states the axioms on `ℝ^X` only; their
version on `ℝ_∞` is the `Ext` ruling of the formalization. In the global form, the local
property is required at every `x : X`, with a single `δ` for all `x` in the case of causality.

Under Dirichlet data `ubd : X → ℝ_∞` outside `I` (`Λ u x = ubd x` for `x ∉ I`), each global
axiom is equivalent to the local axiom of `Λ · x` for all `x ∈ I`. For causality this uses the
finiteness of `X` (to take the minimum of the `δ`'s); for sub-additivity, `ρ ≥ 0` and `Φ`
constant off `I`. This mirrors the real-valued module `Global.lean`.
-/

namespace GuaranteedSubsol.Global.Ext

variable {X : Type*}

/-- (Global `C_past`-memory on `ℝ_∞`) `max {u,t} = max {v,t} ⇒ max {Λ u, t + C} = max {Λ v, t + C}`
at every point `x`. -/
def HasMemory (C : ℝ) (Λ : (X → WithTop ℝ) → X → WithTop ℝ) : Prop :=
  ∀ (u v : X → WithTop ℝ) (t : ℝ), (∀ y, max (u y) t = max (v y) t) →
    ∀ x, max (Λ u x) ((t + C : ℝ) : WithTop ℝ) = max (Λ v x) ((t + C : ℝ) : WithTop ℝ)

/-- (Global causality on `ℝ_∞`) `min {u,t} = min {v,t} ⇒ ∃ δ > 0, min {Λ u, t + δ} =
min {Λ v, t + δ}` at every point `x`, with `δ` independent of `x`. -/
def Causal (Λ : (X → WithTop ℝ) → X → WithTop ℝ) : Prop :=
  ∀ (u v : X → WithTop ℝ) (t : ℝ), (∀ y, min (u y) t = min (v y) t) →
    ∃ δ > (0 : ℝ), ∀ x,
      min (Λ u x) ((t + δ : ℝ) : WithTop ℝ) = min (Λ v x) ((t + δ : ℝ) : WithTop ℝ)

/-- (Global `δ`-strict causality on `ℝ_∞`) Like causality, with `δ` independent of `u`, `v`,
`t`. -/
def StrictlyCausal (δ : ℝ) (Λ : (X → WithTop ℝ) → X → WithTop ℝ) : Prop :=
  ∀ (u v : X → WithTop ℝ) (t : ℝ), (∀ y, min (u y) t = min (v y) t) →
    ∀ x, min (Λ u x) ((t + δ : ℝ) : WithTop ℝ) = min (Λ v x) ((t + δ : ℝ) : WithTop ℝ)

/-- (Global `ρ`-sub-additivity on `ℝ_∞`) `Φ (v + t) ≤ Φ v + ρ t` pointwise, for real `t ≥ 0`. -/
def SubAdditive (ρ : ℝ) (Φ : (X → WithTop ℝ) → X → WithTop ℝ) : Prop :=
  ∀ (v : X → WithTop ℝ) (t : ℝ), 0 ≤ t →
    ∀ x, Φ (fun y => v y + t) x ≤ Φ v x + ((ρ * t : ℝ) : WithTop ℝ)

/-- (Stencil, Intro.tex eq. (Cpast_dependency), left, global form on `ℝ_∞`) `Γ u x` only depends
on the restriction of `u` to the stencil `𝒱 x`. -/
def HasStencil (𝒱 : X → Set X) (Γ : (X → WithTop ℝ) → X → WithTop ℝ) : Prop :=
  ∀ x, GuaranteedSubsol.Ext.HasStencil (𝒱 x) (Γ · x)

open Classical in
/-- The reversed stencil `𝒱̃ y := {x | y ∈ 𝒱 x}` (Complexity.tex, eq. eqdef:stencil, without the
restriction to `Int X`): the points whose value `Γ u x` may change when `u y` changes. It is a
`Finset`, since its cardinality is the cost of updating the corresponding values. -/
noncomputable def revStencil [Fintype X] (𝒱 : X → Set X) (y : X) : Finset X :=
  Finset.univ.filter fun x => y ∈ 𝒱 x

variable {Λ Φ : (X → WithTop ℝ) → X → WithTop ℝ} {I : Set X} {ubd : X → WithTop ℝ}

/-- Under Dirichlet data off `I`, `Λ` is monotone iff each `Λ · x`, `x ∈ I`, is. -/
theorem monotone_iff (hbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) :
    Monotone Λ ↔ ∀ x ∈ I, Monotone (Λ · x) := by
  refine ⟨fun h x _ u v huv => h huv x, fun h u v huv x => ?_⟩
  by_cases hx : x ∈ I
  · exact h x hx huv
  · rw [hbd u x hx, hbd v x hx]

/-- Under Dirichlet data off `I`, global memory iff memory of each `Λ · x`, `x ∈ I`. -/
theorem hasMemory_iff (hbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) {C : ℝ} :
    HasMemory C Λ ↔ ∀ x ∈ I, GuaranteedSubsol.Ext.HasMemory C (Λ · x) := by
  refine ⟨fun h x _ u v t huv => h u v t huv x, fun h u v t huv x => ?_⟩
  by_cases hx : x ∈ I
  · exact h x hx u v t huv
  · rw [hbd u x hx, hbd v x hx]

/-- Under Dirichlet data off `I` and for finite `X`, global causality iff causality of each
`Λ · x`, `x ∈ I`: the global `δ` is the minimum of the local ones. -/
theorem causal_iff [Finite X] (hbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) :
    Causal Λ ↔ ∀ x ∈ I, GuaranteedSubsol.Ext.Causal (Λ · x) := by
  classical
  refine ⟨fun h x _ u v t huv => ?_, fun h u v t huv => ?_⟩
  · obtain ⟨δ, hδ, hx⟩ := h u v t huv
    exact ⟨δ, hδ, hx x⟩
  · -- local `δ`'s, set to `1` off `I`
    let d : X → ℝ := fun x =>
      if hx : x ∈ I then Classical.choose (h x hx u v t huv) else 1
    have hd_pos : ∀ x, 0 < d x := by
      intro x
      by_cases hx : x ∈ I
      · simp only [d, hx, dite_true]
        exact (Classical.choose_spec (h x hx u v t huv)).1
      · simp only [d, hx, dite_false]
        exact one_pos
    have hd_eq : ∀ x ∈ I, min (Λ u x) ((t + d x : ℝ) : WithTop ℝ) =
        min (Λ v x) ((t + d x : ℝ) : WithTop ℝ) := by
      intro x hx
      simp only [d, hx, dite_true]
      exact (Classical.choose_spec (h x hx u v t huv)).2
    -- lowering the truncation level
    have lower : ∀ (a b : WithTop ℝ) (δ δ' : ℝ), δ ≤ δ' →
        min a ((t + δ' : ℝ) : WithTop ℝ) = min b ((t + δ' : ℝ) : WithTop ℝ) →
        min a ((t + δ : ℝ) : WithTop ℝ) = min b ((t + δ : ℝ) : WithTop ℝ) := by
      intro a b δ δ' hle hab
      have hc : ((t + δ : ℝ) : WithTop ℝ) ≤ ((t + δ' : ℝ) : WithTop ℝ) :=
        WithTop.coe_le_coe.2 (add_le_add le_rfl hle)
      calc min a ((t + δ : ℝ) : WithTop ℝ)
          = min (min a ((t + δ' : ℝ) : WithTop ℝ)) ((t + δ : ℝ) : WithTop ℝ) := by
            rw [min_assoc, min_eq_right hc]
        _ = min (min b ((t + δ' : ℝ) : WithTop ℝ)) ((t + δ : ℝ) : WithTop ℝ) := by rw [hab]
        _ = min b ((t + δ : ℝ) : WithTop ℝ) := by rw [min_assoc, min_eq_right hc]
    rcases isEmpty_or_nonempty X with hX | hX
    · exact ⟨1, one_pos, fun x => isEmptyElim x⟩
    · obtain ⟨x₀, hx₀⟩ := Finite.exists_min d
      refine ⟨d x₀, hd_pos x₀, fun x => ?_⟩
      by_cases hx : x ∈ I
      · exact lower _ _ _ _ (hx₀ x) (hd_eq x hx)
      · rw [hbd u x hx, hbd v x hx]

/-- Under Dirichlet data off `I`, global `δ`-strict causality iff that of each `Λ · x`,
`x ∈ I`. -/
theorem strictlyCausal_iff (hbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) {δ : ℝ} :
    StrictlyCausal δ Λ ↔ ∀ x ∈ I, GuaranteedSubsol.Ext.StrictlyCausal δ (Λ · x) := by
  refine ⟨fun h x _ u v t huv => h u v t huv x, fun h u v t huv x => ?_⟩
  by_cases hx : x ∈ I
  · exact h x hx u v t huv
  · rw [hbd u x hx, hbd v x hx]

/-- For `Φ` constant off `I` and `ρ ≥ 0`, global `ρ`-sub-additivity iff that of each `Φ · x`,
`x ∈ I`. -/
theorem subAdditive_iff {c : X → WithTop ℝ} (hbd : ∀ v, ∀ x ∉ I, Φ v x = c x) {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    SubAdditive ρ Φ ↔ ∀ x ∈ I, GuaranteedSubsol.Ext.SubAdditive ρ (Φ · x) := by
  refine ⟨fun h x _ v t ht => h v t ht x, fun h v t ht x => ?_⟩
  by_cases hx : x ∈ I
  · exact h x hx v t ht
  · rw [hbd _ x hx, hbd v x hx]
    exact le_add_of_nonneg_right (WithTop.coe_nonneg.2 (mul_nonneg hρ ht))

end GuaranteedSubsol.Global.Ext
