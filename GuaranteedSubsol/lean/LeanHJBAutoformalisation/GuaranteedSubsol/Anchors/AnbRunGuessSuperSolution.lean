/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AnbProof

/-!
# Frozen statement: the initial guess of Dijkstra's method in the ANB is a super-solution

Source: Prop. prop:Dijkstra_band (Complexity.tex), first claim: along the run of the ANB, the
initial guess `uHatInit` of Dijkstra's method at line anb:hatu (the map `u` of
eq. eqdef:Dijkstra_supsol, `anbDijkstraGuess`; `0` at `n = 0`) is a super-solution of
`Γ' = max (ū_n, min (nτ, Γ_∞))`, so that Dijkstra's method computes `û_n`
(`anbStepData_uHat_eq`). `Γ` is monotone and causal, `α > 0`, `τ ≥ 0`; the hypotheses on `Λ` of
Prop. prop:always_subsol are not used. `X` is finite and linearly ordered (tie-breaking).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem anbRun_guess_superSolution {X : Type*} [Fintype X] [LinearOrder X] {p : AnbParams X}
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x)) (hα : 0 < p.α)
    (hτ : 0 ≤ p.τ) (k : ℕ) :
    anbHatOp p.Γ (anbRun p k).uSub ((anbRun p k).n * p.τ) (anbRun p k).uHatInit ≤
      (anbRun p k).uHatInit := by
  exact AnbProof.guess_run hΓmono hΓcaus hα hτ k

end GuaranteedSubsol
