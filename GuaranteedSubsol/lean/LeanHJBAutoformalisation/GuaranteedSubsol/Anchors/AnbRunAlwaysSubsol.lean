/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AnbProof

/-!
# Frozen statement: the invariants of the ANB

Source: Prop. prop:always_subsol (Complexity.tex), for the ANB started at `n = 0`: if `Λ` is
monotone with `Λ[0] ≥ 0`, `Γ ≤ Λ`, and (for line anb:hatu) `Γ` is monotone and causal and
`α > 0`, then at every iteration `ū ≤ Λ ū`, `Λ u̲ ≤ u̲`, `û ≤ Λ û`, `ū ≤ û ≤ ū'` and
`u̲' ≤ u̲` (`AnbAlwaysSubsol`). `X` is finite and linearly ordered (tie-breaking).
`τ ≥ 0` added (author ruling, 2026-10-14): the initial guess of Dijkstra's method is now the map
of eq. eqdef:Dijkstra_supsol (Prop. prop:Dijkstra_band), whose super-solution property uses it.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem anbRun_always_subsol {X : Type*} [Fintype X] [LinearOrder X] {p : AnbParams X}
    (hΛmono : ∀ x, Monotone (p.Λ · x)) (hΛ0 : 0 ≤ p.Λ 0) (hΓmono : ∀ x, Monotone (p.Γ · x))
    (hΓcaus : ∀ x, Causal (p.Γ · x)) (hΓΛ : ∀ u, p.Γ u ≤ p.Λ u) (hα : 0 < p.α) (hτ : 0 ≤ p.τ)
    (k : ℕ) :
    AnbAlwaysSubsol p (anbRun p k) := by
  exact AnbProof.always_subsol hΛmono hΛ0 hΓmono hΓcaus hΓΛ hα hτ k

end GuaranteedSubsol
