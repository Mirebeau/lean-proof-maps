/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.GlobalIterationProof

/-!
# Frozen statement: the global iteration preserves super-solutions

Source: Algorithm algo:global_iteration (Complexity.tex), super-solution version: for a monotone
`Φ`, if `Φ v ≤ v` then this holds at all iterations (ensures `0 ≤ v - Φ v` at termination).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem globalIterRun_superSolution {X : Type*} {Φ : (X → ℝ) → X → ℝ} (hmono : Monotone Φ)
    (η : ℝ) {v : X → ℝ} (hv : Φ v ≤ v) (n : ℕ) :
    Φ (globalIterRun Φ η v n) ≤ globalIterRun Φ η v n := by
  exact GlobalIterationProof.superSolution hmono η hv n

end GuaranteedSubsol
