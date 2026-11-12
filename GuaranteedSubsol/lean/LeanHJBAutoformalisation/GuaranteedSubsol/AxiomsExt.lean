/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Ring.WithTop

/-!
# Scheme axioms for operators on `ℝ_∞`

Variants of the axioms of `Axioms.lean` for scalar operators `Λ : (X → ℝ_∞) → ℝ_∞`, where
`ℝ_∞ = ]-∞,∞]` is `WithTop ℝ`. The statements are those of the Introduction (`Include/Intro.tex`),
with the constants and the variable `t` real, cast into `WithTop ℝ`.

In `WithTop ℝ`, `⊤ + a = ⊤`, and `↑c * ⊤ = ⊤` for `c ≠ 0`. To avoid subtraction, whose value at `⊤`
is a convention, the inequalities are written with additions only: `a ≤ b - c` becomes
`a + c ≤ b`. They agree with the real axioms on finite values.

REVIEW: as in `Axioms.lean`, the constraints on the constants (`C_past ≥ 0`, `δ > 0`, `ν > 0`,
`ρ < 1`, `C_Γ ≥ 1`, ...) are theorem hypotheses. In `Comparable`, `↑C * ⊤ = ⊤` has the intended
meaning only for `C > 0`.
-/

namespace GuaranteedSubsol.Ext

variable {X : Type*}

/-- (Additive invariance, Intro.tex, axioms of `Λ` and `Γ`, on `ℝ_∞`)
`Λ (u + t) = Λ u + t` for all `t : ℝ`. -/
def AdditivelyInvariant (Λ : (X → WithTop ℝ) → WithTop ℝ) : Prop :=
  ∀ (u : X → WithTop ℝ) (t : ℝ), Λ (fun y => u y + t) = Λ u + t

/-- (`C_past`-memory, Intro.tex eq. eqdef:Cpast_memory, on `ℝ_∞`)
`max {u,t} = max {v,t} ⇒ max {Λ u, t + C} = max {Λ v, t + C}`, for all `t : ℝ`. -/
def HasMemory (C : ℝ) (Λ : (X → WithTop ℝ) → WithTop ℝ) : Prop :=
  ∀ (u v : X → WithTop ℝ) (t : ℝ), (∀ y, max (u y) t = max (v y) t) →
    max (Λ u) ((t + C : ℝ) : WithTop ℝ) = max (Λ v) ((t + C : ℝ) : WithTop ℝ)

/-- (Causality, Intro.tex eq. eqdef:causality, on `ℝ_∞`)
`min {u,t} = min {v,t} ⇒ ∃ δ > 0, min {Λ u, t + δ} = min {Λ v, t + δ}`, for all `t : ℝ`. -/
def Causal (Λ : (X → WithTop ℝ) → WithTop ℝ) : Prop :=
  ∀ (u v : X → WithTop ℝ) (t : ℝ), (∀ y, min (u y) t = min (v y) t) →
    ∃ δ > (0 : ℝ),
      min (Λ u) ((t + δ : ℝ) : WithTop ℝ) = min (Λ v) ((t + δ : ℝ) : WithTop ℝ)

/-- (`δ`-strict causality, Intro.tex Remark rem:submult_strictcaus, on `ℝ_∞`)
Like causality, but `δ` is independent of `u`, `v` and `t`. -/
def StrictlyCausal (δ : ℝ) (Λ : (X → WithTop ℝ) → WithTop ℝ) : Prop :=
  ∀ (u v : X → WithTop ℝ) (t : ℝ), (∀ y, min (u y) t = min (v y) t) →
    min (Λ u) ((t + δ : ℝ) : WithTop ℝ) = min (Λ v) ((t + δ : ℝ) : WithTop ℝ)

/-- (`ν`-sub-multiplicativity, Intro.tex Remark rem:submult_strictcaus, on `ℝ_∞`)
`Λ [(1+t) u] ≤ (1+t) Λ u - ν t` for all real `t ≥ 0`, written `Λ [(1+t) u] + ν t ≤ (1+t) Λ u`. -/
def SubMultiplicative (ν : ℝ) (Λ : (X → WithTop ℝ) → WithTop ℝ) : Prop :=
  ∀ (t : ℝ), 0 ≤ t → ∀ (u : X → WithTop ℝ),
    Λ (fun y => ((1 + t : ℝ) : WithTop ℝ) * u y) + ((ν * t : ℝ) : WithTop ℝ) ≤
      ((1 + t : ℝ) : WithTop ℝ) * Λ u

/-- (`ρ`-sub-additivity, Intro.tex, axiom after eq. eqdef:Phi, on `ℝ_∞`)
`Φ (v + t) ≤ Φ v + ρ t` for all real `t ≥ 0`. -/
def SubAdditive (ρ : ℝ) (Φ : (X → WithTop ℝ) → WithTop ℝ) : Prop :=
  ∀ (v : X → WithTop ℝ) (t : ℝ), 0 ≤ t → Φ (fun y => v y + t) ≤ Φ v + ((ρ * t : ℝ) : WithTop ℝ)

/-- (Stencil, Intro.tex eq. eqdef:Cpast_dependency, left, on `ℝ_∞`)
`u_{|V} = v_{|V} ⇒ Λ u = Λ v`. -/
def HasStencil (V : Set X) (Λ : (X → WithTop ℝ) → WithTop ℝ) : Prop :=
  ∀ (u v : X → WithTop ℝ), (∀ y ∈ V, u y = v y) → Λ u = Λ v

/-- (`C_past`-dependency, Intro.tex eq. eqdef:Cpast_dependency, on `ℝ_∞`)
`Λ` has stencil `V`, and `Λ u ≤ C + u y` for all `y ∈ V`. -/
def HasDependency (C : ℝ) (V : Set X) (Λ : (X → WithTop ℝ) → WithTop ℝ) : Prop :=
  HasStencil V Λ ∧ ∀ (u : X → WithTop ℝ), ∀ y ∈ V, Λ u ≤ (C : WithTop ℝ) + u y

/-- (`C_Γ,C'_Γ`-comparison, Intro.tex, axioms of `Γ`, on `ℝ_∞`)
`C Λ u - C' ≤ Λ [C u] ≤ C Γ u`, written `C Λ u ≤ Λ [C u] + C'` and `Λ [C u] ≤ C Γ u`. -/
def Comparable (C C' : ℝ) (Λ Γ : (X → WithTop ℝ) → WithTop ℝ) : Prop :=
  ∀ u : X → WithTop ℝ,
    (C : WithTop ℝ) * Λ u ≤ Λ (fun y => (C : WithTop ℝ) * u y) + (C' : WithTop ℝ) ∧
      Λ (fun y => (C : WithTop ℝ) * u y) ≤ (C : WithTop ℝ) * Γ u


/-- (Comparison principle on `ℝ_∞`, Complexity.tex eq. eq:comparison_Lambda)
For the partition `X = I ⊔ Iᶜ`: `(u ≤ Λ u and Λ v ≤ v on I, u ≤ v outside I) ⇒ u ≤ v`, for the
global operator `Λ : (X → ℝ_∞) → X → ℝ_∞`. -/
def HasComparisonPrinciple (I : Set X) (Λ : (X → WithTop ℝ) → X → WithTop ℝ) : Prop :=
  ∀ (u v : X → WithTop ℝ), (∀ x ∈ I, u x ≤ Λ u x) → (∀ x ∈ I, Λ v x ≤ v x) →
    (∀ x ∉ I, u x ≤ v x) → u ≤ v

end GuaranteedSubsol.Ext
