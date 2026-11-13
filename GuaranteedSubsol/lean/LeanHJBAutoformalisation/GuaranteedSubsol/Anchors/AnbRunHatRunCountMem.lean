/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.AnbProof

/-!
# Frozen statement: Dijkstra's method in the ANB only updates points of `B'_n`

Source: Prop. prop:Dijkstra_band (Complexity.tex), last claim: the points updated by Dijkstra's
method at line anb:hatu of iteration `n = k + 1` belong to
`B'_n = {x | t⁻_{n-1} ≤ û_{n-1}(x) ∧ û_n(x) < nτ}` (eq. eqdef:Bpn, `anbDijkstraBand`), with
`t⁻_{n-1} = t_{n-1} - Δ_{n-1}` (`AnbStepData.tMinus`). Iteration `n = 0` updates no point
(`anbRun_zero_vacuous`). `Γ` is monotone and causal, `α > 0`, `τ ≥ 0`; the hypotheses on `Λ` of
Prop. prop:always_subsol are not used. `X` is finite and linearly ordered (tie-breaking).

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem anbRun_hatRun_count_mem {X : Type*} [Fintype X] [LinearOrder X] {p : AnbParams X}
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x)) (hα : 0 < p.α)
    (hτ : 0 ≤ p.τ) {k : ℕ} {x : X} (hx : (anbRunData p (k + 1)).hatRun.count x ≠ 0) :
    x ∈ anbDijkstraBand (anbRunData p k).tMinus (((k + 1 : ℕ) : ℝ) * p.τ)
      (anbRunData p k).uHat (anbRunData p (k + 1)).uHat := by
  exact AnbProof.hatRun_count_mem hΓmono hΓcaus hα hτ hx

end GuaranteedSubsol
