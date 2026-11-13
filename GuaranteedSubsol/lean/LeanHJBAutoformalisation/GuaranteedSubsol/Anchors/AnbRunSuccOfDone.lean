/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.AnbProof

/-!
# Frozen statement: the ANB after its stopping test holds

Source: Algorithm algo:anb, line anb:for (Intro.tex), author's request: once the stopping test
`(1 + ε) ū ≥ u̲` holds, the next iteration has an empty band, sets `ū` to `û_n`, leaves `u̲` and
the update counters of `ū` and `u̲` unchanged, and the test still holds. `Γ` is monotone and causal,
`α > 0`, `1 + ε ≥ 0`. `X` is finite and linearly ordered (tie-breaking).
`τ ≥ 0` added (author ruling, 2026-10-14): the initial guess of Dijkstra's method is now the map
of eq. eqdef:Dijkstra_supsol (Prop. prop:Dijkstra_band), whose super-solution property uses it.
Restated with `anbRunData p k` in place of `anbStepData p (anbRun p k)`, equal by definition
(author ruling, 2026-10-14).

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem anbRun_succ_of_done {X : Type*} [Fintype X] [LinearOrder X] {p : AnbParams X}
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x)) (hα : 0 < p.α)
    (hτ : 0 ≤ p.τ) (hε : 0 ≤ 1 + p.ε) {k : ℕ} (hk : anbDone p (anbRun p k)) :
    (anbRunData p k).band = ∅ ∧
    (anbRun p (k + 1)).uSub = (anbRunData p k).uHat ∧
    (anbRun p (k + 1)).uSup = (anbRun p k).uSup ∧
    (anbRun p (k + 1)).countSub = (anbRun p k).countSub ∧
    (anbRun p (k + 1)).countSup = (anbRun p k).countSup ∧
    anbDone p (anbRun p (k + 1)) := by
  exact AnbProof.succ_of_done hΓmono hΓcaus hα hτ hε hk

end GuaranteedSubsol
