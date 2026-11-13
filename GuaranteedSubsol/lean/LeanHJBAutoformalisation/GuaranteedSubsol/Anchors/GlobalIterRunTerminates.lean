/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.GlobalIterationProof

/-!
# Frozen statement: termination of the global iteration

Source: Lemma lem:cplx_global_iteration (Complexity.tex), for Algorithm
algo:global_iteration, super-solution version: for `Φ` monotone and `ρ`-sub-additive with
`0 < ρ < 1`, `η > 0`, and an input with `0 ≤ v - Φ v ≤ C`, the stopping criterion holds after at
most `⌈ln(C/η) / (-ln ρ)⌉₊` iterations. The hypothesis `0 < ρ` (`ln ρ`) is as in the paper.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem globalIterRun_terminates {X : Type*} {Φ : (X → ℝ) → X → ℝ} (hmono : Monotone Φ)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hsub : ∀ x, SubAdditive ρ (Φ · x)) {η C : ℝ}
    (hη : 0 < η) {v : X → ℝ} (hv : Φ v ≤ v) (hvC : ∀ x, v x - Φ v x ≤ C) :
    ∃ n ≤ ⌈Real.log (C / η) / (-Real.log ρ)⌉₊, ∀ x,
      globalIterRun Φ η v n x - Φ (globalIterRun Φ η v n) x ≤ η := by
  exact GlobalIterationProof.terminates hmono hρ0 hρ1 hsub hη hv hvC

end GuaranteedSubsol
