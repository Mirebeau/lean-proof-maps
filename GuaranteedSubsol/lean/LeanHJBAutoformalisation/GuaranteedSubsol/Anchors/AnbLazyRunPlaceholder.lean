/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AnbLazyProof

/-!
# Frozen statement: where the placeholder of the ANB with a placeholder sits

Source: Papers/AnbEquivalence (`Claude_AnbEquivalence.tex`), the relation for `ũ_n` (author's
request, as an anchor separate from `anbLazyRun_equiv`): `ũ_n = ⋄` where `û_{n-1} = (n-1)τ` and
`ū_{n-1} < (n-1)τ`, and `ũ_n = ū_n` otherwise, with `ū`, `û` from the ANB (`anbRunWith`,
`anbRunDataWith`) and `ũ` from the ANB with a placeholder (`anbLazyRunWith`), for any inner solver
`S`. Written for `n = k + 1`; at `n = 0` there is no placeholder (`ũ_0 = ū_0`). Hypotheses as for
`anbLazyRun_equiv`. The placeholder `⋄` is `none` (`ũ` takes values in `Option ℝ`, author's
ruling 2026-10-17). `X` is finite and linearly ordered (tie-breaking).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

open Classical in
theorem anbLazyRun_placeholder {X : Type*} [Fintype X] [LinearOrder X] (S : AnbInnerSolver X)
    {p : AnbParams X} (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x))
    (hα : 0 < p.α) (hτ : 0 ≤ p.τ) :
    (∀ x, (anbLazyRunWith S p 0).uTilde x = some ((anbRunWith S p 0).uSub x)) ∧
      ∀ (k : ℕ) (x : X), (anbLazyRunWith S p (k + 1)).uTilde x =
        if (anbRunDataWith S p k).uHat x = k * p.τ ∧ (anbRunWith S p k).uSub x < k * p.τ then none
        else some ((anbRunWith S p (k + 1)).uSub x) := by
  exact AnbLazyProof.placeholder S hΓmono hΓcaus hα hτ

end GuaranteedSubsol
