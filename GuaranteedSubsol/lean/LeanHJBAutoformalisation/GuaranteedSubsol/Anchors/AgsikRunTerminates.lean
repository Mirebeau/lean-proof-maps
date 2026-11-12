/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AgsikProof

/-!
# Frozen statement: termination of the AGSIK

Source: Algorithm algo:agsik (AGSI2.tex); termination claim (author's
request): if `Λ` is monotone on `ℝ_∞`,
satisfies the comparison principle and admits a finite sub-solution `w`, then the AGSIK started from
`u = +∞`, with `ε > 0` and `α > 0` (`αinv = 1/α`), reaches the stopping criterion `u ≤ Λ u + ε`
after finitely many steps (no a-priori bound). `X` is finite.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem agsikRun_terminates {X : Type*} [Finite X] {Λ : (X → WithTop ℝ) → X → WithTop ℝ}
    (hmono : Monotone Λ) (hcomp : Ext.HasComparisonPrinciple Set.univ Λ) {w : X → ℝ}
    (hw : ∀ x, (w x : WithTop ℝ) ≤ Λ (fun y => (w y : WithTop ℝ)) x) {αinv ε : ℝ}
    (hαinv : 0 < αinv) (hε : 0 < ε) :
    ∃ k, agsikDone Λ ε (agsikRun Λ αinv ε k).u := by
  exact AgsikProof.terminates hmono hcomp hw hαinv hε

end GuaranteedSubsol
