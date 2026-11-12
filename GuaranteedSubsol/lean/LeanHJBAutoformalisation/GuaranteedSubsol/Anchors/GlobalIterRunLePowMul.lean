/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.GlobalIterationProof

/-!
# Frozen statement: contraction of the residual along the global iteration

Source: Algorithm algo:global_iteration (Complexity.tex) and the proof of Lemma
lem:cplx_global_iteration, super-solution version (author's request): for `Φ` monotone and
`ρ`-sub-additive, `ρ ≥ 0`, and an input with `0 ≤ v - Φ v ≤ C`, the residual after `n` iterations is
at most `max (ρ^n C) η` (it is at most `ρ^n C` until the stopping criterion holds, and at most `η`
afterwards).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem globalIterRun_le_pow_mul {X : Type*} {Φ : (X → ℝ) → X → ℝ} (hmono : Monotone Φ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hsub : ∀ x, SubAdditive ρ (Φ · x)) (η : ℝ) {C : ℝ} {v : X → ℝ}
    (hv : Φ v ≤ v) (hvC : ∀ x, v x - Φ v x ≤ C) (n : ℕ) (x : X) :
    globalIterRun Φ η v n x - Φ (globalIterRun Φ η v n) x ≤ max (ρ ^ n * C) η := by
  exact GlobalIterationProof.le_pow_mul hmono hρ hsub η hv hvC n x

end GuaranteedSubsol
