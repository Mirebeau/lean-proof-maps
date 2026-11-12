/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ParallelAgsiSubProof

/-!
# Frozen statement: the sub-solution parallel AGSI is the reflected super-solution one

Source: Algorithm algo:agsi_parallel (AGSI2.tex), sub-solution variant (`v - Φ v` replaced with
`Φ v - v`); author's request. After `n` passes, the sub-solution variant on `Φ` from the state `s`
is the super-solution version on the reflected operator `reflectOp Φ = (v ↦ -Φ (-v))` from the
negated state `s.neg`, negated back.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem parallelAgsiSubStep_iterate {X : Type*} {Φ : (X → ℝ) → X → ℝ} {η : ℝ}
    (s : ParallelAgsiState X) (n : ℕ) :
    (parallelAgsiSubStep Φ η)^[n] s = ((parallelAgsiStep (reflectOp Φ) η)^[n] s.neg).neg := by
  exact ParallelAgsiSubProof.parallelAgsiSubStep_iterate s n

end GuaranteedSubsol
