/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ParallelAgsiProof

/-!
# Frozen statement: termination of the parallel AGSI

Source: Algorithm algo:agsi_parallel (AGSI2.tex) and a V0 `\formalizationInstruction` below it,
removed in V1 (author's request): under the
assumptions of `parallelAgsiRun_count_le`, the while loop terminates, i.e. the stopping criterion
`v - Φ v ≤ η` holds after `n` passes, with the explicit bound `n ≤ ⌈∑_X (v - w) / η⌉₊`.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem parallelAgsiRun_terminates {X : Type*} [Fintype X] {Φ : (X → ℝ) → X → ℝ}
    (hmono : Monotone Φ) (hcomp : HasComparisonPrinciple Set.univ Φ) {w : X → ℝ}
    (hw : w ≤ Φ w) {η : ℝ} (hη : 0 < η) {v : X → ℝ} (hv : Φ v ≤ v) :
    ∃ n ≤ ⌈(∑ x, (v x - w x)) / η⌉₊, ∀ x,
      (parallelAgsiRun Φ η v n).v x - Φ (parallelAgsiRun Φ η v n).v x ≤ η := by
  exact ParallelAgsiProof.terminates hmono hcomp hw hη hv

end GuaranteedSubsol
