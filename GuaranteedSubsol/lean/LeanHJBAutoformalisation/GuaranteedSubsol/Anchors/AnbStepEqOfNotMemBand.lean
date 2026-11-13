/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.AnbProof

/-!
# Frozen statement: the ANB only updates the band

Source: Algorithm algo:anb, lines anb:while_sub and anb:while_sup (Intro.tex): outside the band
`B_n`, one iteration sets `ū` to `û_n` and leaves `u̲` unchanged. Only `α > 0` is assumed.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem anbStep_eq_of_notMem_band {X : Type*} [Fintype X] [LinearOrder X] {p : AnbParams X}
    (hα : 0 < p.α) {s : AnbState X} {x : X} (hx : x ∉ (anbStepData p s).band) :
    (anbStep p s).uSub x = (anbStepData p s).uHat x ∧ (anbStep p s).uSup x = s.uSup x := by
  exact AnbProof.eq_of_notMem_band hα hx

end GuaranteedSubsol
