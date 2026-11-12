/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.BandProof

/-!
# Frozen statement: the operator on a band, with frozen exterior values, is sub-additive

Source: Lemma lem:monDom (Complexity.tex), second claim: if `Λ` is monotone and
`ρ`-sub-additive, so is `Λ_B^v` (`bandOp Λ B v`; scalar form at each point of `B`).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem subAdditive_bandOp {X : Type*} {Λ : (X → ℝ) → X → ℝ} {ρ : ℝ} (hΛ : Monotone Λ)
    (hsub : ∀ x, SubAdditive ρ (Λ · x)) (B : Set X) (v : X → ℝ) (x : B) :
    SubAdditive ρ (bandOp Λ B v · x) := by
  exact BandProof.subAdditive_bandOp x.2 (fun _ _ h => hΛ h x) (hsub x)

end GuaranteedSubsol
