/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.ParallelAgsiKruzkovProof

/-!
# Frozen statement: number of updates per point of the parallel AGSI applied to `Φ_α`

Source: Prop. prop:cplx_agsi_parallel (AGSI2.tex), super-solution case, applied to the operator
`Φ := Φ_α = Global.kruzkovOp α Λ` in Kruzkov coordinates (author's request): if `Φ_α` is
`ρ`-sub-additive with `0 < ρ < 1` and the input satisfies `0 ≤ v - Φ_α v ≤ C`, then at most
`N''_Φ` updates occur at any point. No monotonicity of `Λ` is needed (`Φ_α` is monotone for
`α > 0`). `X` is finite.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem parallelAgsiRun_kruzkovOp_count_le {X : Type*} [Finite X] {Λ : (X → ℝ) → X → ℝ}
    {α ρ : ℝ} (hα : 0 < α) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hsub : ∀ x, SubAdditive ρ (kruzkovOp α (Λ · x))) {η C : ℝ} (hη : 0 < η) {v : X → ℝ}
    (hv : Global.kruzkovOp α Λ v ≤ v) (hvC : ∀ x, v x - Global.kruzkovOp α Λ v x ≤ C)
    (n : ℕ) (x : X) :
    ((parallelAgsiRun (Global.kruzkovOp α Λ) η v n).count x : ℝ) ≤
      ⌈Real.log ((1 - ρ) * C / η) / (-Real.log ρ)⌉₊ + 2 / (1 - ρ) ^ 2 := by
  exact ParallelAgsiKruzkovProof.parallelAgsiRun_kruzkovOp_count_le hα hρ0 hρ1 hsub hη hv hvC n x

end GuaranteedSubsol
