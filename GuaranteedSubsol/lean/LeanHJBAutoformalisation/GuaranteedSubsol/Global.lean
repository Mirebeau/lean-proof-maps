/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.Axioms
import Mathlib.Basic.Finite.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith

/-!
# Global form of the scheme axioms

The Introduction (`Include/Intro.tex`) of the preprint GuaranteedSubsolutions states the scheme
axioms for *global* operators `Λ : ℝ^X → ℝ^X`, which satisfy the Dirichlet boundary condition
`Λ u = u_bd` on `∂X`. At the author's request, the
formalization (`Axioms.lean`) uses *scalar* (local) forms of the axioms, for the operator
`u ↦ Λ u x` at a fixed interior point `x ∈ Int X`.

This module transcribes the paper's global definitions (namespace `GuaranteedSubsol.Global`) and
proves their equivalence with "for all `x ∈ Int X`, the local axiom holds", under the
Dirichlet condition. Here `Int X` is a set `I`, and the Dirichlet condition reads
`Λ u x = ubd x` for `x ∉ I`. Causality additionally requires `X` finite (the global `δ` is the
minimum of the local ones), and sub-additivity requires `ρ ≥ 0` and `Φ` constant off `I`.
The latter applies in particular to the Kruzkov transform `Φ_α` of a Dirichlet operator `Λ`,
which is constant off `I`.

Axioms already stated "on `Int X`" in the paper (additive invariance, sub-multiplicativity,
comparison) need no lemma, and `C_past`-dependency is pointwise by nature.
-/

namespace GuaranteedSubsol.Global

variable {X : Type*}

/-- (`C_past`-memory, Intro.tex eq. (Cpast_memory), global form)
`max {u,t} = max {v,t} ⇒ max {Λ u, t + C} = max {Λ v, t + C}` on `X`. -/
def HasMemory (C : ℝ) (Λ : (X → ℝ) → X → ℝ) : Prop :=
  ∀ (u v : X → ℝ) (t : ℝ), (∀ y, max (u y) t = max (v y) t) →
    ∀ x, max (Λ u x) (t + C) = max (Λ v x) (t + C)

/-- (Causality, Intro.tex eq. (causality), global form)
`min {u,t} = min {v,t} ⇒ ∃ δ > 0, min {Λ u, t + δ} = min {Λ v, t + δ}` on `X`. -/
def Causal (Λ : (X → ℝ) → X → ℝ) : Prop :=
  ∀ (u v : X → ℝ) (t : ℝ), (∀ y, min (u y) t = min (v y) t) →
    ∃ δ > 0, ∀ x, min (Λ u x) (t + δ) = min (Λ v x) (t + δ)

/-- (`δ`-strict causality, Intro.tex Remark rem:submult_strictcaus, global form)
Like causality, but `δ` is independent of `u`, `v` and `t`. -/
def StrictlyCausal (δ : ℝ) (Λ : (X → ℝ) → X → ℝ) : Prop :=
  ∀ (u v : X → ℝ) (t : ℝ), (∀ y, min (u y) t = min (v y) t) →
    ∀ x, min (Λ u x) (t + δ) = min (Λ v x) (t + δ)

/-- (`ρ`-sub-additivity, Intro.tex, axiom after eq. eqdef:Phi, global form)
`Φ (v + t) ≤ Φ v + ρ t` on `X`, for all `t ≥ 0`. -/
def SubAdditive (ρ : ℝ) (Φ : (X → ℝ) → X → ℝ) : Prop :=
  ∀ (v : X → ℝ) (t : ℝ), 0 ≤ t → ∀ x, Φ (fun y => v y + t) x ≤ Φ v x + ρ * t

variable {Λ Φ : (X → ℝ) → X → ℝ} {I : Set X} {ubd : X → ℝ}

/-- (Monotonicity, Intro.tex) Under the Dirichlet condition, `Λ` is monotone iff each
`(Λ · x)`, `x ∈ Int X`, is monotone. -/
theorem monotone_iff (hbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) :
    Monotone Λ ↔ ∀ x ∈ I, Monotone (Λ · x) := by
  refine ⟨fun h x _ u v huv => h huv x, fun h u v huv x => ?_⟩
  by_cases hx : x ∈ I
  · exact h x hx huv
  · exact le_of_eq (by rw [hbd u x hx, hbd v x hx])

/-- (`C_past`-memory, Intro.tex eq. (Cpast_memory)) Under the Dirichlet condition, the global
memory property is equivalent to the local one at each `x ∈ Int X`. -/
theorem hasMemory_iff (hbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) {C : ℝ} :
    HasMemory C Λ ↔ ∀ x ∈ I, GuaranteedSubsol.HasMemory C (Λ · x) := by
  refine ⟨fun h x _ u v t huv => h u v t huv x, fun h u v t huv x => ?_⟩
  by_cases hx : x ∈ I
  · exact h x hx u v t huv
  · rw [hbd u x hx, hbd v x hx]

/-- (Causality, Intro.tex eq. (causality)) For `X` finite, under the Dirichlet condition, global
causality is equivalent to local causality at each `x ∈ Int X`. -/
theorem causal_iff [Finite X] (hbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) :
    Causal Λ ↔ ∀ x ∈ I, GuaranteedSubsol.Causal (Λ · x) := by
  constructor
  · intro h x _ u v t huv
    obtain ⟨δ, hδ, h'⟩ := h u v t huv
    exact ⟨δ, hδ, h' x⟩
  · intro h u v t huv
    have : Fintype X := Fintype.ofFinite X
    have hx : ∀ x, ∃ δ > 0, min (Λ u x) (t + δ) = min (Λ v x) (t + δ) := by
      intro x
      by_cases hxI : x ∈ I
      · exact h x hxI u v t huv
      · exact ⟨1, one_pos, by rw [hbd u x hxI, hbd v x hxI]⟩
    choose f hf0 hf using hx
    rcases isEmpty_or_nonempty X with hX | hX
    · exact ⟨1, one_pos, fun x => isEmptyElim x⟩
    · refine ⟨Finset.univ.inf' Finset.univ_nonempty f,
        (Finset.lt_inf'_iff _).2 fun x _ => hf0 x, fun x => ?_⟩
      have hle : Finset.univ.inf' Finset.univ_nonempty f ≤ f x :=
        Finset.inf'_le _ (Finset.mem_univ x)
      have key : ∀ a : ℝ, min a (t + Finset.univ.inf' Finset.univ_nonempty f) =
          min (min a (t + f x)) (t + Finset.univ.inf' Finset.univ_nonempty f) := by
        intro a
        rw [min_assoc, min_eq_right (a := t + f x) (by linarith)]
      rw [key (Λ u x), key (Λ v x), hf x]

/-- (`δ`-strict causality, Intro.tex Remark rem:submult_strictcaus) Under the Dirichlet
condition, global `δ`-strict causality is equivalent to the local one at each `x ∈ Int X`. -/
theorem strictlyCausal_iff (hbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) {δ : ℝ} :
    StrictlyCausal δ Λ ↔ ∀ x ∈ I, GuaranteedSubsol.StrictlyCausal δ (Λ · x) := by
  refine ⟨fun h x _ u v t huv => h u v t huv x, fun h u v t huv x => ?_⟩
  by_cases hx : x ∈ I
  · exact h x hx u v t huv
  · rw [hbd u x hx, hbd v x hx]

/-- (`ρ`-sub-additivity, Intro.tex, axiom after eq. eqdef:Phi) If `Φ` is constant off `Int X` and
`ρ ≥ 0`, global `ρ`-sub-additivity is equivalent to the local one at each `x ∈ Int X`. -/
theorem subAdditive_iff {c : X → ℝ} (hbd : ∀ v, ∀ x ∉ I, Φ v x = c x) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    SubAdditive ρ Φ ↔ ∀ x ∈ I, GuaranteedSubsol.SubAdditive ρ (Φ · x) := by
  refine ⟨fun h x _ v t ht => h v t ht x, fun h v t ht x => ?_⟩
  by_cases hx : x ∈ I
  · exact h x hx v t ht
  · rw [hbd _ x hx, hbd v x hx]
    linarith [mul_nonneg hρ ht]

end GuaranteedSubsol.Global
