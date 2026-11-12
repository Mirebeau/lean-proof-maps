/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ParallelAgsiTermProof

/-!
# Frozen statement: the parallel AGSI terminates (sub-solution version)

Source: Prop. prop:cplx_agsi_parallel (AGSI2.tex, V1), termination claim for the sub-solution
variant of Algorithm algo:agsi_parallel: if `Φ` is monotone and `ρ`-sub-additive with
`0 < ρ < 1`, started from `v` with `0 ≤ Φ v - v ≤ C`, the loop terminates. The bound on the number
of updates at each point is `parallelAgsiSubRun_count_le_of_subAdditive`.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem parallelAgsiSubPasses_lt_top_of_subAdditive {X : Type*} [Finite X]
    {Φ : (X → ℝ) → X → ℝ} (hmono : Monotone Φ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hsub : ∀ x, SubAdditive ρ (Φ · x)) {η C : ℝ} (hη : 0 < η) {v : X → ℝ}
    (hv : v ≤ Φ v) (hvC : ∀ x, Φ v x - v x ≤ C) : parallelAgsiSubPasses Φ η v < ⊤ := by
  exact ParallelAgsiTermProof.subPasses_lt_top hmono hρ0 hρ1 hsub hη hv hvC

end GuaranteedSubsol
