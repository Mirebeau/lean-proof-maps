/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.TolProof

/-!
# Frozen statement: tolerance from a sub- and a super-solution

Source: Corol. corol:tol (Complexity.tex), first point. `Λ` is monotone, obeys the comparison
principle (in the sub-solution vs. super-solution form of eq:comparison_Lambda, `hcomp`),
and has a fixed point `u_*`. If `ū ≤ Λ ū`, `Λ u̲ ≤ u̲` and `(1 + ε) ū ≥ u̲` with `ε ≥ 0`, then
`(1+ε)⁻¹ u_* ≤ ū ≤ u_*`, `u_* ≤ u̲ ≤ (1+ε) u_*`, `0 ≤ Λ ū - ū ≤ ε u_*`, `0 ≤ u̲ - Λ u̲ ≤ ε u_*`.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem tol_of_subSolution_superSolution {X : Type*} {Λ : (X → ℝ) → X → ℝ}
    (hmono : Monotone Λ) (hcomp : HasComparisonPrinciple Set.univ Λ)
    {uFix : X → ℝ} (hfix : Λ uFix = uFix) {ε : ℝ} (hε : 0 ≤ ε) {uSub uSup : X → ℝ}
    (hsub : uSub ≤ Λ uSub) (hsup : Λ uSup ≤ uSup) (htol : ∀ x, uSup x ≤ (1 + ε) * uSub x) :
    ∀ x, ((1 + ε)⁻¹ * uFix x ≤ uSub x ∧ uSub x ≤ uFix x) ∧
      (uFix x ≤ uSup x ∧ uSup x ≤ (1 + ε) * uFix x) ∧
      (0 ≤ Λ uSub x - uSub x ∧ Λ uSub x - uSub x ≤ ε * uFix x) ∧
      (0 ≤ uSup x - Λ uSup x ∧ uSup x - Λ uSup x ≤ ε * uFix x) := by
  exact TolProof.tol_of_subSolution_superSolution hmono hcomp hfix hε hsub hsup htol

end GuaranteedSubsol
