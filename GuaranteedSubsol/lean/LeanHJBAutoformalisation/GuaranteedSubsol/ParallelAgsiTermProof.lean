/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ParallelAgsiCplxProof
import LeanHJBAutoformalisation.GuaranteedSubsol.ParallelAgsiSubProof
import LeanHJBAutoformalisation.GuaranteedSubsol.ParallelAgsiResultProof

/-!
# Prop. prop:cplx_agsi_parallel: termination

Provider proofs for the frozen anchors `GuaranteedSubsol.parallelAgsiPasses_lt_top_of_subAdditive`
and `…parallelAgsiSubPasses_lt_top_of_subAdditive`, see `ANCHORS.md`: under the assumptions of
Prop. prop:cplx_agsi_parallel (AGSI2.tex, V1), the number of updates at each point is bounded
uniformly along the loop (`ParallelAgsiCplxProof.count_le_of_subAdditive`), hence the loop stops
(`ParallelAgsiResultProof.passes_lt_top_of_count_le`).
-/

namespace GuaranteedSubsol.ParallelAgsiTermProof

variable {X : Type*} [Finite X] {Φ : (X → ℝ) → X → ℝ} {ρ η C : ℝ} {v : X → ℝ}

theorem passes_lt_top (hmono : Monotone Φ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hsub : ∀ x, SubAdditive ρ (Φ · x)) (hη : 0 < η) (hv : Φ v ≤ v)
    (hvC : ∀ x, v x - Φ v x ≤ C) : parallelAgsiPasses Φ η v < ⊤ :=
  ParallelAgsiResultProof.passes_lt_top_of_count_le fun n x =>
    ParallelAgsiCplxProof.count_le_of_subAdditive hmono hρ0 hρ1 hsub hη hv hvC n x

theorem subPasses_lt_top (hmono : Monotone Φ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hsub : ∀ x, SubAdditive ρ (Φ · x)) (hη : 0 < η) (hv : v ≤ Φ v)
    (hvC : ∀ x, Φ v x - v x ≤ C) : parallelAgsiSubPasses Φ η v < ⊤ :=
  ParallelAgsiResultProof.subPasses_lt_top_of_count_le fun n x =>
    ParallelAgsiSubProof.count_le_of_subAdditive hmono hρ0 hρ1 hsub hη hv hvC n x

end GuaranteedSubsol.ParallelAgsiTermProof
