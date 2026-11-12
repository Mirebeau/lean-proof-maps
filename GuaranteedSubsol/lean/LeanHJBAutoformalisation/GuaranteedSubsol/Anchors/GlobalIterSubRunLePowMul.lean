/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.GlobalIterationProof

/-!
# Frozen statement: contraction of the residual along the sub-solution global iteration

Source: Algorithm algo:global_iteration (Complexity.tex) and the proof of Lemma
lem:cplx_global_iteration, sub-solution variant (author's request): for `Φ` monotone and
`ρ`-sub-additive, `ρ ≥ 0`, and an input with `0 ≤ Φ v - v ≤ C`, the residual after `n` iterations is
at most `max (ρ^n C) η`.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem globalIterSubRun_le_pow_mul {X : Type*} {Φ : (X → ℝ) → X → ℝ} (hmono : Monotone Φ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hsub : ∀ x, SubAdditive ρ (Φ · x)) (η : ℝ) {C : ℝ} {v : X → ℝ}
    (hv : v ≤ Φ v) (hvC : ∀ x, Φ v x - v x ≤ C) (n : ℕ) (x : X) :
    Φ (globalIterSubRun Φ η v n) x - globalIterSubRun Φ η v n x ≤ max (ρ ^ n * C) η := by
  exact GlobalIterationProof.subRun_le_pow_mul hmono hρ hsub η hv hvC n x

end GuaranteedSubsol
