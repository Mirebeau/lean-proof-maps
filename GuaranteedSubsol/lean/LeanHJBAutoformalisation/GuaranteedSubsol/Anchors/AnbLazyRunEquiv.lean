/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.AnbLazyProof

/-!
# Frozen statement: the ANB with a placeholder is equivalent to the ANB

Source: Papers/AnbEquivalence (`Claude_AnbEquivalence.tex`), the program with the `⋄` placeholder
(`anbLazyRunWith`, `AnbLazy.lean`), and the target of Prop. prop:correct_anb_lazy
(Complexity.tex) without the heaps (author's request). For any inner solver `S` (in particular the
global iteration of algo:anb and the parallel AGSI of th:complexity_with_agsi), at every iteration
`k`, with `T = kτ`: `u̲~_k = u̲_k`; `ū_k = ũ_k^{⋄→(k-1)τ}` (`AnbLazyState.uSub`); `ǔ_k^init =
(û_k^init)^{<T}` and `û_k^init = min {ǔ_k^init, max {ū_k, T}}` (`AnbLazyState.uHatInit`);
`ǔ_k = û_k^{<T}` and `û_k = max {ū_k, min {T, ǔ_k}}`; `(ũ^init)^{⋄→T} = û_k`; `t_k`, `Δ_k`, `B_k`,
`η_k` and the three counters are equal; and the two programs stop at the same iteration.
Hypotheses: `Γ` monotone and causal, `α > 0`, `τ ≥ 0` (those of Prop. prop:Dijkstra_band, used for
the initial guesses; no property of `Λ` nor of the inner solver is needed, since both programs
call the inner solver on the same data). The placeholder `⋄` is `none` (`ũ` in `Option ℝ`, author's
ruling 2026-10-17). `X` is finite and linearly ordered (tie-breaking).

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem anbLazyRun_equiv {X : Type*} [Fintype X] [LinearOrder X] (S : AnbInnerSolver X)
    {p : AnbParams X} (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x))
    (hα : 0 < p.α) (hτ : 0 ≤ p.τ) :
    (∀ k : ℕ,
      (anbLazyRunWith S p k).uSup = (anbRunWith S p k).uSup ∧
      (anbLazyRunWith S p k).uSub p.τ = (anbRunWith S p k).uSub ∧
      (anbLazyRunWith S p k).uCheckInit =
        (fun x => cutoffLt (k * p.τ) ((anbRunWith S p k).uHatInit x)) ∧
      (anbRunWith S p k).uHatInit = (anbLazyRunWith S p k).uHatInit p.τ ∧
      (anbLazyRunDataWith S p k).uCheck =
        (fun x => cutoffLt (k * p.τ) ((anbRunDataWith S p k).uHat x : WithTop ℝ)) ∧
      (∀ x, ((anbRunDataWith S p k).uHat x : WithTop ℝ) =
        max ((anbLazyRunWith S p k).uSub p.τ x : WithTop ℝ)
          (min ((k * p.τ : ℝ) : WithTop ℝ) ((anbLazyRunDataWith S p k).uCheck x))) ∧
      (anbLazyRunDataWith S p k).uHat = (anbRunDataWith S p k).uHat ∧
      (anbLazyRunDataWith S p k).t = (anbRunDataWith S p k).t ∧
      (anbLazyRunDataWith S p k).Δ = (anbRunDataWith S p k).Δ ∧
      (anbLazyRunDataWith S p k).band = (anbRunDataWith S p k).band ∧
      (anbLazyRunDataWith S p k).η = (anbRunDataWith S p k).η ∧
      (anbLazyRunWith S p k).countSub = (anbRunWith S p k).countSub ∧
      (anbLazyRunWith S p k).countSup = (anbRunWith S p k).countSup ∧
      (anbLazyRunWith S p k).countHat = (anbRunWith S p k).countHat) ∧
    anbLazyStopIndexWith S p = anbStopIndexWith S p := by
  exact AnbLazyProof.equiv S hΓmono hΓcaus hα hτ

end GuaranteedSubsol
