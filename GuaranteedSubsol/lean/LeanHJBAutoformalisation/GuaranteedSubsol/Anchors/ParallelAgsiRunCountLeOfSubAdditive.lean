/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ParallelAgsiCplxProof

/-!
# Frozen statement: number of updates per point of the parallel AGSI

Source: Prop. prop:cplx_agsi_parallel (AGSI2.tex), super-solution case: if `Φ` is monotone and
`ρ`-sub-additive with `ρ < 1`, and the input satisfies `0 ≤ v - Φ v ≤ C`, then the parallel
AGSI with tolerance `η > 0` performs at most
`N''_Φ := ⌈ln((1 - ρ) C/η) / (-ln ρ)⌉₊ + 2/(1 - ρ)²` updates `v(x) ← Φ v(x)` at any given point
`x`, whatever the number `n` of passes. The hypothesis `0 < ρ` (`ln ρ`) is as in the paper. It loses
no generality, since a `0`-sub-additive `Φ` is `ρ`-sub-additive for any `ρ > 0`. `X` is finite
(standing assumption).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem parallelAgsiRun_count_le_of_subAdditive {X : Type*} [Finite X]
    {Φ : (X → ℝ) → X → ℝ} (hmono : Monotone Φ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hsub : ∀ x, SubAdditive ρ (Φ · x)) {η C : ℝ} (hη : 0 < η) {v : X → ℝ}
    (hv : Φ v ≤ v) (hvC : ∀ x, v x - Φ v x ≤ C) (n : ℕ) (x : X) :
    ((parallelAgsiRun Φ η v n).count x : ℝ) ≤
      ⌈Real.log ((1 - ρ) * C / η) / (-Real.log ρ)⌉₊ + 2 / (1 - ρ) ^ 2 := by
  exact ParallelAgsiCplxProof.count_le_of_subAdditive hmono hρ0 hρ1 hsub hη hv hvC n x

end GuaranteedSubsol
