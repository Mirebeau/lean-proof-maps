/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.SubsolGrowthProof

/-!
# Frozen statement: growth of a sub-solution above a level

Source: Prop. prop:olu_ge_ustar (Complexity.tex). Global operators `Λ, Γ : (X → ℝ) → X → ℝ` with
the same Dirichlet data `ubd` outside `I = Int X` (the "implicit additional assumption" of the
paper's proof). `Λ` is monotone, additively invariant, has `C_past`-memory and is
`C_Γ, C'_Γ`-comparable with `Γ` on `Int X`. The comparison principle is assumed in the form of
eq:comparison_Lambda (`hcomp`: sub-solution vs. super-solution, on any partition `J ⊔ Jᶜ`). The
paper's `u_*` is only a sub-solution, named `uSub`. The assumption `Γ ≤ Λ` is not used, hence
omitted. Conclusion: `u ≥ t + (u_* - (1+ε) t - C_past - C'_Γ) / C_Γ` on `{u ≥ t}`.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem subsol_growth {X : Type*} {Λ Γ : (X → ℝ) → X → ℝ} {I : Set X} {ubd : X → ℝ}
    (hΛbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) (hΓbd : ∀ u, ∀ x ∉ I, Γ u x = ubd x)
    {Cpast CΓ CΓ' : ℝ} (hCpast : 0 ≤ Cpast) (hCΓ : 1 ≤ CΓ) (hCΓ' : 0 ≤ CΓ')
    (hmono : ∀ x ∈ I, Monotone (Λ · x)) (hadd : ∀ x ∈ I, AdditivelyInvariant (Λ · x))
    (hmem : ∀ x ∈ I, HasMemory Cpast (Λ · x))
    (hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (Λ · x) (Γ · x))
    (hcomp : ∀ J : Set X, HasComparisonPrinciple J Λ)
    {uSub : X → ℝ} (huSub : uSub ≤ Λ uSub) {u : X → ℝ} {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε)
    (hlow : ∀ x, u x < t → uSub x ≤ (1 + ε) * u x) (hΓu : ∀ x, Γ u x ≤ u x)
    (huΛ : ∀ x, u x ≤ Λ u x) :
    ∀ x, t ≤ u x → t + (uSub x - (1 + ε) * t - Cpast - CΓ') / CΓ ≤ u x := by
  exact SubsolGrowthProof.subsol_growth hΛbd hΓbd hCpast hCΓ hCΓ' hmono hadd hmem hcmp hcomp huSub
    ht hε hlow hΓu huΛ

end GuaranteedSubsol
