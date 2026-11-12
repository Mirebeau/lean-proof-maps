/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ParallelAgsiProof

/-!
# Frozen statement: the parallel AGSI preserves super-solutions

Source: Algorithm algo:agsi_parallel (AGSI2.tex) and the proof of Prop. prop:cplx_agsi_parallel:
for a monotone `Φ`, if `v` is a super-solution (`Φ v ≤ v`), it remains so at all times in the
algorithm (via Prop. prop:partialMonotone).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem parallelAgsiStep_superSolution {X : Type*} {Φ : (X → ℝ) → X → ℝ} (hmono : Monotone Φ)
    (η : ℝ) {s : ParallelAgsiState X} (hs : Φ s.v ≤ s.v) (n : ℕ) :
    Φ ((parallelAgsiStep Φ η)^[n] s).v ≤ ((parallelAgsiStep Φ η)^[n] s).v := by
  exact ParallelAgsiProof.superSolution hmono η hs n

end GuaranteedSubsol
