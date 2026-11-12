/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.GlobalIterationProof

/-!
# Frozen statement: the global iteration preserves sub-solutions

Source: Algorithm algo:global_iteration (Complexity.tex), sub-solution variant: for a monotone
`Φ`, if `v ≤ Φ v` then this holds at all iterations (ensures `0 ≤ Φ v - v` at termination).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem globalIterSubRun_subSolution {X : Type*} {Φ : (X → ℝ) → X → ℝ} (hmono : Monotone Φ)
    (η : ℝ) {v : X → ℝ} (hv : v ≤ Φ v) (n : ℕ) :
    globalIterSubRun Φ η v n ≤ Φ (globalIterSubRun Φ η v n) := by
  exact GlobalIterationProof.subSolution hmono η hv n

end GuaranteedSubsol
