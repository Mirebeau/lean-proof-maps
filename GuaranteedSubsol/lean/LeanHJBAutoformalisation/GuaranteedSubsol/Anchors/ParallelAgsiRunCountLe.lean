/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ParallelAgsiProof

/-!
# Frozen statement: bound on the total number of updates of the parallel AGSI

Source: Algorithm algo:agsi_parallel (AGSI2.tex) (author's request): if `Φ` is
monotone, satisfies the comparison principle and admits a sub-solution `w`, and `v` is a
super-solution, then `v` stays above `w`, while `∑_X v` decreases by more than `η` at each update
`v(x) ← Φ v(x)`. Hence `η` times the total number of updates is at most `∑_X (v - w)`.
Author ruling: the assumption `η > 0` is dropped, being unneeded.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem parallelAgsiRun_count_le {X : Type*} [Fintype X] {Φ : (X → ℝ) → X → ℝ} (hmono : Monotone Φ)
    (hcomp : HasComparisonPrinciple Set.univ Φ) {w : X → ℝ} (hw : w ≤ Φ w) {η : ℝ}
    {v : X → ℝ} (hv : Φ v ≤ v) (n : ℕ) :
    η * ∑ x, ((parallelAgsiRun Φ η v n).count x : ℝ) ≤ ∑ x, (v x - w x) := by
  exact ParallelAgsiProof.count_le hmono hcomp hw hv n

end GuaranteedSubsol
