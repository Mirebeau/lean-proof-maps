/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.AnbProof

/-!
# Frozen statement: line anb:hatu of the ANB computes the solution `û_n`

Source: Algorithm algo:anb, line anb:hatu (Intro.tex), and Prop. prop:Dijkstra_band
(Complexity.tex): if `Γ` is monotone and causal and the initial guess is a super-solution of
`Γ' := max (ū, min (nτ, Γ_∞))`, Dijkstra's method yields a finite `û_n` solving
`û_n = max {ū, min {nτ, Γ û_n}}`. `X` is finite and linearly ordered (tie-breaking).

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem anbStepData_uHat_eq {X : Type*} [Fintype X] [LinearOrder X] {p : AnbParams X}
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x)) {s : AnbState X}
    (hinit : anbHatOp p.Γ s.uSub (s.n * p.τ) s.uHatInit ≤ s.uHatInit) (x : X) :
    (anbStepData p s).hatRun.u x = ((anbStepData p s).uHat x : WithTop ℝ) ∧
      (anbStepData p s).uHat x =
        max (s.uSub x) (min (s.n * p.τ) (p.Γ (anbStepData p s).uHat x)) := by
  exact AnbProof.uHat_eq hΓmono hΓcaus hinit x

end GuaranteedSubsol
