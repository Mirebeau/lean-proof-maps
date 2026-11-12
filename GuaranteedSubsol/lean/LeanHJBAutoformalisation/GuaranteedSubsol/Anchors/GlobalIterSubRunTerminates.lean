/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.GlobalIterationProof

/-!
# Frozen statement: termination of the sub-solution global iteration

Source: Lemma lem:cplx_global_iteration (Complexity.tex), for Algorithm
algo:global_iteration, sub-solution variant: for `Φ` monotone and `ρ`-sub-additive with `0 < ρ < 1`,
`η > 0`, and an input with `0 ≤ Φ v - v ≤ C`, the stopping criterion holds after at most
`⌈ln(C/η) / (-ln ρ)⌉₊` iterations. The hypothesis `0 < ρ` (`ln ρ`) is as in the paper.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem globalIterSubRun_terminates {X : Type*} {Φ : (X → ℝ) → X → ℝ} (hmono : Monotone Φ)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hsub : ∀ x, SubAdditive ρ (Φ · x)) {η C : ℝ}
    (hη : 0 < η) {v : X → ℝ} (hv : v ≤ Φ v) (hvC : ∀ x, Φ v x - v x ≤ C) :
    ∃ n ≤ ⌈Real.log (C / η) / (-Real.log ρ)⌉₊, ∀ x,
      Φ (globalIterSubRun Φ η v n) x - globalIterSubRun Φ η v n x ≤ η := by
  exact GlobalIterationProof.subRun_terminates hmono hρ0 hρ1 hsub hη hv hvC

end GuaranteedSubsol
