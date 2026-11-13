/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.ParallelAgsiSubProof

/-!
# Frozen statement: number of updates per point of the sub-solution variant of the parallel AGSI

Source: Prop. prop:cplx_agsi_parallel (AGSI2.tex), sub-solution variant: if `Φ` is monotone and
`ρ`-sub-additive with `0 < ρ < 1`, and the input satisfies `0 ≤ Φ v - v ≤ C`, then at most
`N''_Φ := ⌈ln((1 - ρ) C/η) / (-ln ρ)⌉₊ + 2/(1 - ρ)²` updates occur at any given point. As in the
paper, `0 < ρ`. `X` is finite.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem parallelAgsiSubRun_count_le_of_subAdditive {X : Type*} [Finite X]
    {Φ : (X → ℝ) → X → ℝ} (hmono : Monotone Φ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hsub : ∀ x, SubAdditive ρ (Φ · x)) {η C : ℝ} (hη : 0 < η) {v : X → ℝ}
    (hv : v ≤ Φ v) (hvC : ∀ x, Φ v x - v x ≤ C) (n : ℕ) (x : X) :
    ((parallelAgsiSubRun Φ η v n).count x : ℝ) ≤
      ⌈Real.log ((1 - ρ) * C / η) / (-Real.log ρ)⌉₊ + 2 / (1 - ρ) ^ 2 := by
  exact ParallelAgsiSubProof.count_le_of_subAdditive hmono hρ0 hρ1 hsub hη hv hvC n x

end GuaranteedSubsol
