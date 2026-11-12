/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Basic.Real.Basic

/-!
# Scheme axioms of GuaranteedSubsolutions (Introduction)

Axioms on a discretization scheme, from the Introduction (`Include/Intro.tex`) of the preprint
GuaranteedSubsolutions.

At the author's request, the axioms are
stated for a *scalar* operator `Λ : (X → ℝ) → ℝ`, which stands for `u ↦ Λ u x` at a fixed
interior point `x ∈ Int X`. Theorem statements will assume "for all `x ∈ Int X`, `(Λ · x)`
satisfies ...". On `∂X` the paper's global axioms hold trivially, by the Dirichlet boundary
conditions `Λ u = u_bd`, so the global axioms are recovered by asserting the scalar ones at every
interior point.

Monotonicity is Mathlib's `Monotone`, since the order on `X → ℝ` is the pointwise order of the
paper.

REVIEW: the constants are unconstrained reals in the definitions. The paper's constraints
(`C_past ≥ 0`, `δ > 0`, `ν > 0`, `0 ≤ ρ < 1`) are to be stated as theorem hypotheses.
-/

namespace GuaranteedSubsol

variable {X : Type*}

/-- (Additive invariance, Intro.tex, axioms of `Λ` and `Γ`, scalar form)
`Λ (u + t) = Λ u + t` for all `t : ℝ`, `u : X → ℝ`. -/
def AdditivelyInvariant (Λ : (X → ℝ) → ℝ) : Prop :=
  ∀ (u : X → ℝ) (t : ℝ), Λ (fun y => u y + t) = Λ u + t

/-- (`C_past`-memory, Intro.tex eq. eqdef:Cpast_memory, scalar form)
`max {u,t} = max {v,t} ⇒ max {Λ u, t + C} = max {Λ v, t + C}`,
for all `u v : X → ℝ` and `t : ℝ`. -/
def HasMemory (C : ℝ) (Λ : (X → ℝ) → ℝ) : Prop :=
  ∀ (u v : X → ℝ) (t : ℝ), (∀ y, max (u y) t = max (v y) t) →
    max (Λ u) (t + C) = max (Λ v) (t + C)

/-- (Causality, Intro.tex eq. eqdef:causality, scalar form)
`min {u,t} = min {v,t} ⇒ ∃ δ > 0, min {Λ u, t + δ} = min {Λ v, t + δ}`,
for all `u v : X → ℝ` and `t : ℝ`.

REVIEW: here `δ` may depend on the point `x`; this is equivalent to the paper's global
causality because `X` is finite (take the minimum of the `δ`'s). -/
def Causal (Λ : (X → ℝ) → ℝ) : Prop :=
  ∀ (u v : X → ℝ) (t : ℝ), (∀ y, min (u y) t = min (v y) t) →
    ∃ δ > 0, min (Λ u) (t + δ) = min (Λ v) (t + δ)

/-- (`δ`-strict causality, Intro.tex Remark rem:submult_strictcaus, scalar form)
Like causality, but `δ` is independent of `u`, `v` and `t`. -/
def StrictlyCausal (δ : ℝ) (Λ : (X → ℝ) → ℝ) : Prop :=
  ∀ (u v : X → ℝ) (t : ℝ), (∀ y, min (u y) t = min (v y) t) →
    min (Λ u) (t + δ) = min (Λ v) (t + δ)

/-- (`ν`-sub-multiplicativity, Intro.tex Remark rem:submult_strictcaus, scalar form)
`Λ [(1+t) u] ≤ (1+t) Λ u - ν t` for all `t ≥ 0`, `u : X → ℝ`. -/
def SubMultiplicative (ν : ℝ) (Λ : (X → ℝ) → ℝ) : Prop :=
  ∀ (t : ℝ), 0 ≤ t → ∀ (u : X → ℝ), Λ (fun y => (1 + t) * u y) ≤ (1 + t) * Λ u - ν * t

/-- (`ρ`-sub-additivity, Intro.tex, axiom after eq. eqdef:Phi, scalar form)
`Φ (v + t) ≤ Φ v + ρ t` for all `t ≥ 0`, `v : X → ℝ`.

Stated for an arbitrary operator `Φ`, as in Complexity.tex (Prop. prop:contractivity,
Lemma lem:monDom). The paper's assumption "`Φ_α` is `ρ`-sub-additive" is this property
applied to the Kruzkov-transformed operator `Φ_α = E_α Λ_∞ E_α⁻¹`.

REVIEW: on `∂X` the paper's global property reduces to `0 ≤ ρ t`, so the scalar form recovers
the global one only when `ρ ≥ 0`. -/
def SubAdditive (ρ : ℝ) (Φ : (X → ℝ) → ℝ) : Prop :=
  ∀ (v : X → ℝ) (t : ℝ), 0 ≤ t → Φ (fun y => v y + t) ≤ Φ v + ρ * t

/-- (Stencil, Intro.tex eq. eqdef:Cpast_dependency, left, scalar form)
`Λ u` only depends on the restriction of `u` to the stencil `V`:
`u_{|V} = v_{|V} ⇒ Λ u = Λ v`. -/
def HasStencil (V : Set X) (Λ : (X → ℝ) → ℝ) : Prop :=
  ∀ (u v : X → ℝ), (∀ y ∈ V, u y = v y) → Λ u = Λ v

/-- (`C_past`-dependency, Intro.tex eq. eqdef:Cpast_dependency, scalar form)
`Λ` has stencil `V`, and `Λ u ≤ C + min_V u` for all `u : X → ℝ`.

REVIEW: `Λ u ≤ C + min_V u` is written `∀ y ∈ V, Λ u ≤ C + u y`. This is the same inequality
when `V` is finite and nonempty, and avoids an infimum over `V`, which in `ℝ` would take a
junk value when `V` is empty or `u` is unbounded below on `V`. -/
def HasDependency (C : ℝ) (V : Set X) (Λ : (X → ℝ) → ℝ) : Prop :=
  HasStencil V Λ ∧ ∀ (u : X → ℝ), ∀ y ∈ V, Λ u ≤ C + u y

/-- (`C_Γ,C'_Γ`-comparison, Intro.tex, axioms of `Γ`, scalar form)
`C Λ u - C' ≤ Λ [C u] ≤ C Γ u` for all `u : X → ℝ`. -/
def Comparable (C C' : ℝ) (Λ Γ : (X → ℝ) → ℝ) : Prop :=
  ∀ u : X → ℝ, C * Λ u - C' ≤ Λ (fun y => C * u y) ∧ Λ (fun y => C * u y) ≤ C * Γ u


/-- (Comparison principle, Complexity.tex, eq. eq:comparison_Lambda of Prop.
prop:comparison_Lambda) For the partition `X = I ⊔ Iᶜ`, a sub-solution on `I` lies below a
super-solution on `I` as soon as it does on the complement:
`(u ≤ Λ u and Λ v ≤ v on I, u ≤ v outside I) ⇒ u ≤ v`. The paper's "for any partition" is
`∀ I, HasComparisonPrinciple I Λ`. Unlike the other axioms, this is a property of the global
operator `Λ : (X → ℝ) → X → ℝ`. -/
def HasComparisonPrinciple (I : Set X) (Λ : (X → ℝ) → X → ℝ) : Prop :=
  ∀ (u v : X → ℝ), (∀ x ∈ I, u x ≤ Λ u x) → (∀ x ∈ I, Λ v x ≤ v x) →
    (∀ x ∉ I, u x ≤ v x) → u ≤ v

end GuaranteedSubsol
