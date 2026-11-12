/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ConstrGammaProof

/-!
# Frozen statement: construction of `Γ` from `Λ` (pointwise)

Source: Prop. prop:constr_Gamma (Intro.tex), and its proof (Effective.tex), at one interior point
`x ∈ Int X`. The scalar operator `Λ : (X → ℝ) → ℝ` stands for `(Λ · x)`, the finite nonempty
stencil `V` for `V(x)`, and `Γ := constrGamma Λ V hV` for `(Γ · x)`.

Conclusions: `Λ` has `C_past`-memory; `Γ` is additively invariant, `δ`-strictly causal,
underestimates `Λ`, and is `C_Γ, C'_Γ`-comparable with `C_Γ = C_past / δ` and
`C'_Γ = C_past C_Γ - δ`. The existence of a super-solution is a global property, not stated here.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem constrGammaLoc {X : Type*} {Λ : (X → ℝ) → ℝ} {V : Finset X} (hV : V.Nonempty)
    {Cpast δ : ℝ} (hCpast : 0 ≤ Cpast) (hδ : 0 < δ) (hmono : Monotone Λ)
    (hadd : AdditivelyInvariant Λ) (hΛ0 : δ ≤ Λ 0) (hdep : HasDependency Cpast V Λ) :
    HasMemory Cpast Λ ∧ AdditivelyInvariant (constrGamma Λ V hV) ∧
      StrictlyCausal δ (constrGamma Λ V hV) ∧ (∀ u, constrGamma Λ V hV u ≤ Λ u) ∧
      Comparable (Cpast / δ) (Cpast * (Cpast / δ) - δ) Λ (constrGamma Λ V hV) := by
  exact ConstrGamma.loc hV hCpast hδ hmono hadd hΛ0 hdep

end GuaranteedSubsol
