/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.ParallelAgsiTermProof

/-!
# Frozen statement: the parallel AGSI terminates (super-solution version)

Source: Prop. prop:cplx_agsi_parallel (AGSI2.tex), termination claim: if `Φ` is monotone and
`ρ`-sub-additive with `0 < ρ < 1`, Algorithm algo:agsi_parallel, started from `v` with
`0 ≤ v - Φ v ≤ C`, terminates (the number of passes is finite). The bound on the number of updates
at each point is `parallelAgsiRun_count_le_of_subAdditive`.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem parallelAgsiPasses_lt_top_of_subAdditive {X : Type*} [Finite X]
    {Φ : (X → ℝ) → X → ℝ} (hmono : Monotone Φ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hsub : ∀ x, SubAdditive ρ (Φ · x)) {η C : ℝ} (hη : 0 < η) {v : X → ℝ}
    (hv : Φ v ≤ v) (hvC : ∀ x, v x - Φ v x ≤ C) : parallelAgsiPasses Φ η v < ⊤ := by
  exact ParallelAgsiTermProof.passes_lt_top hmono hρ0 hρ1 hsub hη hv hvC

end GuaranteedSubsol
