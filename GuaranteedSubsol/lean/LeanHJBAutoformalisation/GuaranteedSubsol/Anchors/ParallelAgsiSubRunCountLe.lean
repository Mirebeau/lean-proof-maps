/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.ParallelAgsiSubProof

/-!
# Frozen statement: total number of updates of the sub-solution variant of the parallel AGSI

Source: Algorithm algo:agsi_parallel (AGSI2.tex), sub-solution variant (author's
request), with sub- and
super-solutions exchanged: if `Φ` is monotone,
satisfies the comparison principle and admits a super-solution `w`, and `v` is a sub-solution,
then `η` times the total number of updates is at most `∑_X (w - v)`.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem parallelAgsiSubRun_count_le {X : Type*} [Fintype X] {Φ : (X → ℝ) → X → ℝ}
    (hmono : Monotone Φ) (hcomp : HasComparisonPrinciple Set.univ Φ) {w : X → ℝ}
    (hw : Φ w ≤ w) {η : ℝ} {v : X → ℝ} (hv : v ≤ Φ v) (n : ℕ) :
    η * ∑ x, ((parallelAgsiSubRun Φ η v n).count x : ℝ) ≤ ∑ x, (w x - v x) := by
  exact ParallelAgsiSubProof.count_le (η := η) hmono hcomp hw hv n

end GuaranteedSubsol
