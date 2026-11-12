/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.TolProof

/-!
# Frozen statement: tolerance from a super-solution, sub-multiplicative case

Source: Corol. corol:tol (Complexity.tex), second point, super-solution case. `Λ` obeys the
comparison principle (sub-solution vs. super-solution form of eq:comparison_Lambda, `hcomp`), has
a fixed point `u_*`, Dirichlet boundary conditions `ubd ≥ 0` on `∂X` (complement of `I = Int X`),
and is `ν`-sub-multiplicative on `Int X` with `ν > 0`. If `0 ≤ u̲ - Λ u̲ ≤ ε` and `u̲ = ubd` on
`∂X`, then `u_* ≤ u̲ ≤ (1 + ε/ν) u_*`.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem tol_of_superSolution_subMultiplicative {X : Type*} {Λ : (X → ℝ) → X → ℝ} {I : Set X}
    {ubd : X → ℝ} (hbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) (hubd : ∀ x ∉ I, 0 ≤ ubd x)
    {ν : ℝ} (hν : 0 < ν) (hmul : ∀ x ∈ I, SubMultiplicative ν (Λ · x))
    (hcomp : HasComparisonPrinciple Set.univ Λ)
    {uFix : X → ℝ} (hfix : Λ uFix = uFix) {ε : ℝ} (hε : 0 ≤ ε) {uSup : X → ℝ}
    (hsup : Λ uSup ≤ uSup) (htol : ∀ x, uSup x - Λ uSup x ≤ ε)
    (hsupbd : ∀ x ∉ I, uSup x = ubd x) :
    ∀ x, uFix x ≤ uSup x ∧ uSup x ≤ (1 + ε / ν) * uFix x := by
  exact TolProof.tol_of_superSolution_subMultiplicative hbd hubd hν hmul hcomp hfix hε hsup htol
    hsupbd

end GuaranteedSubsol
