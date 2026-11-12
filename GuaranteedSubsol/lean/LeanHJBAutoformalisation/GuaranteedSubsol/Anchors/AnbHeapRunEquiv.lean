/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AnbHeapProof

/-!
# Frozen statement: the ANB with sorted lists is equivalent to the ANB with a placeholder

Source: Prop. prop:correct_anb_lazy (Complexity.tex, V1), for algo:anb_lazy with the sorted lists
`L`, `M`, `S` stored in ordered partial maps (`anbHeapRunWith`, `AnbHeap.lean`), compared with the
ANB with a placeholder (`anbLazyRunWith`; author's request), itself equivalent to algo:anb by
`anbLazyRun_equiv`. As in V1 (author's rulings 2026-10-16, fixes of V0, now in the paper): line
anb_lazy:olu_gets_hatu also updates the points of `S` with key in `[(n-1)τ, nτ[`; there, the
placeholder is set exactly when `nτ` is selected in `min {nτ, ǔ}`; a fourth list `Sc` (the keys
`u̲~` of the placeholders, eq. eqdef:Sc_heap) makes the stopping test exactly that of algo:anb. For
any inner solver `S`, at every iteration `k`: the super-solutions coincide; the sub-solutions
`ũ^{⋄→(k-1)τ}` coincide for `k ≥ 1`; the maps `ǔ` at the start of the iteration and after Dijkstra's
method coincide; after line anb_lazy:olu_gets_hatu, `ũ^{⋄→kτ} = û` and (for `k ≥ 1`) `ũ` coincides;
`t_k`, `Δ_k`, `B_k`, `η_k` and the three counters coincide; the lists hold the keys of eqs.
eqdef:L_heap, eqdef:M_heap, eqdef:S_heap (and of `Sc`); and the two programs stop at the same
iteration. Hypotheses: `Γ` monotone, causal, with stencils `𝒱` (eq. eqdef:stencil), `α > 0`,
`τ > 0`. The placeholder `⋄` is `none` (`ũ` in `Option ℝ`, author's ruling 2026-10-17). `X` is
finite and linearly ordered (tie-breaking).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem anbHeapRun_equiv {X : Type*} [Fintype X] [LinearOrder X] (S : AnbInnerSolver X)
    {p : AnbParams X} {𝒱 : X → Set X}
    (hst : Global.Ext.HasStencil 𝒱 (Global.monotoneExtension p.Γ))
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x)) (hα : 0 < p.α)
    (hτ : 0 < p.τ) :
    (∀ k : ℕ,
      (anbHeapRunWith S p 𝒱 k).uSup = (anbLazyRunWith S p k).uSup ∧
      (0 < k → (anbHeapRunWith S p 𝒱 k).uSub p.τ = (anbLazyRunWith S p k).uSub p.τ) ∧
      (anbHeapRunWith S p 𝒱 k).dij.u = (anbLazyRunWith S p k).uCheckInit ∧
      (anbHeapRunDataWith S p 𝒱 k).dij.u = (anbLazyRunDataWith S p k).uCheck ∧
      (fun x => ((anbHeapRunDataWith S p 𝒱 k).uTildeInit x).getD (k * p.τ)) =
        (anbLazyRunDataWith S p k).uHat ∧
      (0 < k → (anbHeapRunDataWith S p 𝒱 k).uTildeInit = (anbLazyRunDataWith S p k).uTildeInit) ∧
      (anbHeapRunDataWith S p 𝒱 k).t = (anbLazyRunDataWith S p k).t ∧
      (anbHeapRunDataWith S p 𝒱 k).Δ = (anbLazyRunDataWith S p k).Δ ∧
      ((anbHeapRunDataWith S p 𝒱 k).band : Set X) = (anbLazyRunDataWith S p k).band ∧
      (anbHeapRunDataWith S p 𝒱 k).η = (anbLazyRunDataWith S p k).η ∧
      (anbHeapRunWith S p 𝒱 k).countSub = (anbLazyRunWith S p k).countSub ∧
      (anbHeapRunWith S p 𝒱 k).countSup = (anbLazyRunWith S p k).countSup ∧
      (anbHeapRunWith S p 𝒱 k).dij.count = (anbLazyRunWith S p k).countHat ∧
      (anbHeapRunWith S p 𝒱 k).dij.L.v = dijkstraKey
        (anbHeapOp p.Γ ((anbLazyRunWith S p k).uSub p.τ)) (anbHeapRunWith S p 𝒱 k).dij.u ∧
      (anbHeapRunWith S p 𝒱 k).M.v =
        anbKeyM p.ε (anbHeapRunWith S p 𝒱 k).uTilde (anbHeapRunWith S p 𝒱 k).uSup ∧
      (anbHeapRunWith S p 𝒱 k).S.v = anbKeyS (anbHeapRunWith S p 𝒱 k).uTilde ∧
      (anbHeapRunWith S p 𝒱 k).Sc.v =
        anbKeySc (anbHeapRunWith S p 𝒱 k).uTilde (anbHeapRunWith S p 𝒱 k).uSup) ∧
    anbHeapStopIndexWith S p 𝒱 = anbLazyStopIndexWith S p := by
  exact AnbHeapProof.equiv S hst hΓmono hΓcaus hα hτ

end GuaranteedSubsol
