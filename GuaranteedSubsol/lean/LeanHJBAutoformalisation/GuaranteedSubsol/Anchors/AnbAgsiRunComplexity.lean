/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AnbAgsiProof

/-!
# Frozen statement: complexity of the ANB with the parallel AGSI (th:complexity_with_agsi)

Source: Theorem th:complexity_with_agsi (AGSI2.tex), packaged as `anbRun_complexity` (author's
request): the statement of Theorem th:complexity holds when lines anb:while_sub and anb:while_sup
of algo:anb are replaced with parallel AGSI on the band `B_n` (`anbAgsiRun`, the ANB with the inner
solver `anbAgsi`), with the modified constant `N''_Λ := ⌈2Δ_max/(-α ln ρ)⌉ + ⌊2/(1 - ρ)²⌋`
(`AnbParams.NΛ''agsi`). As in V1 (author rulings now in the paper): `Δ_max := 2α ln(2e/ε) + 2τ`,
`n_max` with a ceiling, `2 Δ_max ≤ min u_bd`, `0 < ρ < 1`, the bound `N_Λ` for each of the two
counters, and `Δ_max` in `N''_Λ`. Departures from V1: the second term `2/(1 - ρ)²` of `N''_Λ` is
rounded down since the update counts are integers; the joint "Until" loop of the paper is modelled
as two separate AGSI runs, for `ū` and for `u̲`, which is equivalent since the two updates do not
interact. The AGSI bounds the number of updates at each point of the band, not the number of passes
of the inner loops (a pass may update a single point): the bound on the passes of the inner loops in
`anbRun_complexity` is replaced with the bound `N''_Λ` on the number of updates at each point in
each iteration (the counters increase by at most `N''_Λ`). `X` is finite and linearly ordered
(tie-breaking).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem anbAgsiRun_complexity {X : Type*} [Fintype X] [LinearOrder X] {p : AnbParams X}
    {I : Set X} {ubd : X → ℝ} (hΛbd : ∀ u, ∀ x ∉ I, p.Λ u x = ubd x)
    (hΓbd : ∀ u, ∀ x ∉ I, p.Γ u x = ubd x) {Cpast CΓ CΓ' : ℝ} (hCpast : 0 ≤ Cpast)
    (hCΓ : 1 ≤ CΓ) (hCΓ' : 0 ≤ CΓ') (hΛmono : ∀ x, Monotone (p.Λ · x))
    (hadd : ∀ x ∈ I, AdditivelyInvariant (p.Λ · x)) (hmem : ∀ x ∈ I, HasMemory Cpast (p.Λ · x))
    {w : X → ℝ} (hw : p.Λ w ≤ w) (hΓmono : ∀ x, Monotone (p.Γ · x))
    (hΓcaus : ∀ x, Causal (p.Γ · x)) (hΓadd : ∀ x ∈ I, AdditivelyInvariant (p.Γ · x))
    (hΓΛ : ∀ u, p.Γ u ≤ p.Λ u) (hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (p.Λ · x) (p.Γ · x))
    (hsub : ∀ x ∈ I, SubAdditive p.ρ (kruzkovOp p.α (p.Λ · x))) (hα : 0 < p.α)
    (hρ0 : 0 < p.ρ) (hρ1 : p.ρ < 1) (hτ : 0 < p.τ) (hε : 0 < p.ε)
    (hbd : ∀ x ∉ I, 2 * p.Δmax ≤ ubd x) :
    ∃ uFix : X → ℝ, p.Λ uFix = uFix ∧ (∀ v, p.Λ v = v → v = uFix) ∧
      (∀ J : Set X, HasComparisonPrinciple J p.Λ) ∧
      (p.ε ≤ p.εmax uFix →
        anbAgsiStopIndex p ≤ ((⌈p.nMax uFix⌉₊ + 1 : ℕ) : ℕ∞) ∧
        ((anbAgsiRun p (anbAgsiStopIndex p).toNat).uSub ≤
            p.Λ (anbAgsiRun p (anbAgsiStopIndex p).toNat).uSub ∧
          Global.monotoneExtension p.Λ (anbAgsiRun p (anbAgsiStopIndex p).toNat).uSup ≤
            (anbAgsiRun p (anbAgsiStopIndex p).toNat).uSup ∧
          anbDone p (anbAgsiRun p (anbAgsiStopIndex p).toNat)) ∧
        (∀ k, (anbAgsiRunData p k).Δ < p.Δmax) ∧
        (∀ (k : ℕ) (x : X),
          (anbAgsiRun p (k + 1)).countSub x ≤ (anbAgsiRun p k).countSub x + (p.NΛ''agsi : ℕ∞) ∧
          (anbAgsiRun p (k + 1)).countSup x ≤ (anbAgsiRun p k).countSup x + (p.NΛ''agsi : ℕ∞)) ∧
        (∀ (x : X) (S : Finset ℕ), (∀ k ∈ S, x ∈ (anbAgsiRunData p k).band) →
          S.card ≤ p.NΛ' Cpast CΓ CΓ' uFix) ∧
        (∀ (k : ℕ) (x : X),
          (anbAgsiRun p k).countSub x ≤ ((p.NΛ' Cpast CΓ CΓ' uFix * p.NΛ''agsi : ℕ) : ℕ∞) ∧
          (anbAgsiRun p k).countSup x ≤ ((p.NΛ' Cpast CΓ CΓ' uFix * p.NΛ''agsi : ℕ) : ℕ∞) ∧
          (anbAgsiRun p k).countHat x ≤ p.NΓ Cpast CΓ CΓ' uFix)) := by
  exact AnbAgsiProof.complexity hΛbd hΓbd hCpast hCΓ hCΓ' hΛmono hadd hmem hw hΓmono hΓcaus
    hΓadd hΓΛ hcmp hsub hα hρ0 hρ1 hτ hε hbd

end GuaranteedSubsol
