/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AgsikProof
import LeanHJBAutoformalisation.GuaranteedSubsol.ComparisonPrinciple

/-!
# Termination of the AGSIK for the extension of a real scheme: proof

Provider proof for the frozen anchor `GuaranteedSubsol.agsikRun_terminates_of_kruzkov`, see
`ANCHORS.md`.

For a monotone `Λ : (X → ℝ) → X → ℝ` whose Kruzkov transform `Φ_β` is `ρ`-sub-additive with
`ρ < 1`, the AGSIK applied to `Λ_∞` terminates as soon as `Λ` admits a (finite) sub-solution:
the comparison principle on `ℝ_∞` follows from `Ext.hasComparisonPrinciple_of_kruzkov`, and no
causality is needed. The Kruzkov timescale `β` is unrelated to the timescale `α = 1/αinv` of
the AGSIK.
-/

namespace GuaranteedSubsol.AgsikKruzkovProof

/-- Termination of the AGSIK for `Λ_∞`, when `Λ` is monotone, `Φ_β` is `ρ`-sub-additive with
`ρ < 1`, and `Λ` admits a finite sub-solution `w`. -/
theorem agsikRun_terminates_of_kruzkov {X : Type*} [Finite X] {Λ : (X → ℝ) → X → ℝ}
    (hmono : ∀ x, Monotone (Λ · x)) {β ρ : ℝ} (hβ : 0 < β) (hρ : ρ < 1)
    (hsub : ∀ x, SubAdditive ρ (kruzkovOp β (Λ · x))) {w : X → ℝ} (hw : w ≤ Λ w)
    {αinv ε : ℝ} (hαinv : 0 < αinv) (hε : 0 < ε) :
    ∃ k, agsikDone (Global.monotoneExtension Λ) ε
      ((agsikStep (Global.monotoneExtension Λ) αinv ε)^[k] agsikInit).u :=
  AgsikProof.terminates (Λ := Global.monotoneExtension Λ) (w := w)
    (fun _ _ h x => KruzkovProof.monotone_monotoneExtension _ h)
    (Ext.hasComparisonPrinciple_of_kruzkov hβ hρ fun x _ => hsub x)
    (fun x => by
      change (w x : WithTop ℝ) ≤ monotoneExtension (Λ · x) (fun y => (w y : WithTop ℝ))
      rw [MonotoneExtension.coe_eq (hmono x)]; exact WithTop.coe_le_coe.2 (hw x))
    hαinv hε

end GuaranteedSubsol.AgsikKruzkovProof
