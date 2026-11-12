/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ParallelAgsiSubProof

/-!
# Frozen statement: termination of the sub-solution variant of the parallel AGSI

Source: Algorithm algo:agsi_parallel (AGSI2.tex), sub-solution variant, and a V0
`\formalizationInstruction`, removed in V1 (author's request): under the assumptions of
`parallelAgsiSubRun_count_le`, the stopping criterion `Φ v - v ≤ η` holds after `n` passes,
with `n ≤ ⌈∑_X (w - v) / η⌉₊`.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem parallelAgsiSubRun_terminates {X : Type*} [Fintype X] {Φ : (X → ℝ) → X → ℝ}
    (hmono : Monotone Φ) (hcomp : HasComparisonPrinciple Set.univ Φ) {w : X → ℝ}
    (hw : Φ w ≤ w) {η : ℝ} (hη : 0 < η) {v : X → ℝ} (hv : v ≤ Φ v) :
    ∃ n ≤ ⌈(∑ x, (w x - v x)) / η⌉₊, ∀ x,
      Φ (parallelAgsiSubRun Φ η v n).v x - (parallelAgsiSubRun Φ η v n).v x
        ≤ η := by
  exact ParallelAgsiSubProof.terminates hmono hcomp hw hη hv

end GuaranteedSubsol
