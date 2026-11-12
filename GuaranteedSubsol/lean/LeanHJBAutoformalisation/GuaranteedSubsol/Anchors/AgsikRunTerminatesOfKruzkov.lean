/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AgsikKruzkov

/-!
# Frozen statement: termination of the AGSIK for the extension of a real scheme

Source: Algorithm algo:agsik (AGSI2.tex); the termination claim is from a V0
`\formalizationInstruction`, removed in V1. Stated for the extension `Λ_∞` of a real operator `Λ`
(author's request): if `Λ` is monotone, its Kruzkov transform `Φ_β` is `ρ`-sub-additive with `β > 0`
and `ρ < 1`, and `Λ` admits a finite sub-solution `w`, then the AGSIK applied to `Λ_∞` (timescale
`α = 1/αinv > 0`, unrelated to `β`, tolerance `ε > 0`) reaches its stopping criterion after finitely
many steps. No causality is assumed. `X` is finite.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem agsikRun_terminates_of_kruzkov {X : Type*} [Finite X] {Λ : (X → ℝ) → X → ℝ}
    (hmono : ∀ x, Monotone (Λ · x)) {β ρ : ℝ} (hβ : 0 < β) (hρ : ρ < 1)
    (hsub : ∀ x, SubAdditive ρ (kruzkovOp β (Λ · x))) {w : X → ℝ} (hw : w ≤ Λ w)
    {αinv ε : ℝ} (hαinv : 0 < αinv) (hε : 0 < ε) :
    ∃ k, agsikDone (Global.monotoneExtension Λ) ε
      (agsikRun (Global.monotoneExtension Λ) αinv ε k).u := by
  exact AgsikKruzkovProof.agsikRun_terminates_of_kruzkov hmono hβ hρ hsub hw hαinv hε

end GuaranteedSubsol
