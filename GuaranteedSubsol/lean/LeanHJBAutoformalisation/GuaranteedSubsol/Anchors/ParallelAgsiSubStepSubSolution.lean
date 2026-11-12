/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ParallelAgsiSubProof

/-!
# Frozen statement: the sub-solution variant of the parallel AGSI preserves sub-solutions

Source: Algorithm algo:agsi_parallel (AGSI2.tex), sub-solution variant: for a monotone `Φ`, if
`v` is a sub-solution (`v ≤ Φ v`), it remains so at all times in the algorithm.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem parallelAgsiSubStep_subSolution {X : Type*} {Φ : (X → ℝ) → X → ℝ}
    (hmono : Monotone Φ) (η : ℝ) {s : ParallelAgsiState X} (hs : s.v ≤ Φ s.v) (n : ℕ) :
    ((parallelAgsiSubStep Φ η)^[n] s).v ≤ Φ ((parallelAgsiSubStep Φ η)^[n] s).v := by
  exact ParallelAgsiSubProof.subSolution hmono η hs n

end GuaranteedSubsol
