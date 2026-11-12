/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AnbProof

/-!
# Frozen statement: the iteration `n = 0` of the ANB is vacuous

Source: Remark rem:anb_npos (Complexity.tex), for the ANB started at `n = 0` (author's decision):
`û_0 = 0`, `t_0 = Δ_0 = 0`, the band `B_0` is empty, and the iteration `n = 0` changes neither
`ū`, `u̲` nor the update counters (only `n`). `X` is finite and linearly ordered. Author ruling:
the assumption that `X` is nonempty is dropped, being unneeded (the step is the loop body).
Restated with `anbRunData p k` in place of `anbStepData p (anbRun p k)`, equal by definition
(author ruling, 2026-10-14).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem anbRun_zero_vacuous {X : Type*} [Fintype X] [LinearOrder X] (p : AnbParams X) :
    (anbRunData p 0).uHat = 0 ∧ (anbRunData p 0).t = 0 ∧
    (anbRunData p 0).Δ = 0 ∧ (anbRunData p 0).band = ∅ ∧
    (anbRun p 1).n = 1 ∧ (anbRun p 1).uSub = (anbRun p 0).uSub ∧
    (anbRun p 1).uSup = (anbRun p 0).uSup ∧ (anbRun p 1).countSub = 0 ∧
    (anbRun p 1).countSup = 0 ∧ (anbRun p 1).countHat = 0 := by
  exact AnbProof.zero_vacuous p

end GuaranteedSubsol
