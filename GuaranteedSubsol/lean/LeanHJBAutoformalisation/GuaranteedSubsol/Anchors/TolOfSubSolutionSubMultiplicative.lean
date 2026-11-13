/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.TolProof

/-!
# Frozen statement: tolerance from a sub-solution, sub-multiplicative case

Source: Corol. corol:tol (Complexity.tex), second point, sub-solution case. `Λ` obeys the comparison
principle (sub-solution vs. super-solution form of eq:comparison_Lambda, `hcomp`), has a fixed
point `u_*`, Dirichlet boundary conditions `ubd ≥ 0` on `∂X` (complement of `I = Int X`), and is
`ν`-sub-multiplicative on `Int X`. If `0 ≤ Λ ū - ū ≤ ε` with `0 ≤ ε < ν`, and `ū = ubd` on `∂X`,
then `(1 - ε/ν) u_* ≤ ū ≤ u_*`.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem tol_of_subSolution_subMultiplicative {X : Type*} {Λ : (X → ℝ) → X → ℝ} {I : Set X}
    {ubd : X → ℝ} (hbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) (hubd : ∀ x ∉ I, 0 ≤ ubd x)
    {ν : ℝ} (hmul : ∀ x ∈ I, SubMultiplicative ν (Λ · x))
    (hcomp : HasComparisonPrinciple Set.univ Λ)
    {uFix : X → ℝ} (hfix : Λ uFix = uFix) {ε : ℝ} (hε : 0 ≤ ε) (hεν : ε < ν)
    {uSub : X → ℝ} (hsub : uSub ≤ Λ uSub) (htol : ∀ x, Λ uSub x - uSub x ≤ ε)
    (hsubbd : ∀ x ∉ I, uSub x = ubd x) :
    ∀ x, (1 - ε / ν) * uFix x ≤ uSub x ∧ uSub x ≤ uFix x := by
  exact TolProof.tol_of_subSolution_subMultiplicative hbd hubd hmul hcomp hfix hε hεν hsub htol
    hsubbd

end GuaranteedSubsol
