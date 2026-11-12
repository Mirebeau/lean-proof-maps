/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AnbHeapComplexity

/-!
# Correctness and complexity of the ANB with sorted lists (provider proofs)

Provider proofs for the frozen anchors `anbHeapRun_correct_complexity` and
`anbHeapRun_correct_complexity_withUnknown` (algo:anb_lazy with sorted lists, under the assumptions
of Theorems th:complexity and th:complexity_withUnknown), see `ANCHORS.md`.

The conclusions of the complexity theorems for algo:anb (`AnbComplexityProof.complexity`,
`AnbWithUnknownProof.complexity`) are transported to the ANB with sorted lists by
`anbLazyRun_equiv` and `anbHeapRun_equiv` (`transfer`), and the cost bounds are those of
`anbHeapRun_complexity` and `anbHeapRun_complexity_withUnknown`.
-/

namespace GuaranteedSubsol.AnbHeapCorrectComplexityProof

variable {X : Type*} [Fintype X] [LinearOrder X]

/-- Transport of the conclusions of the complexity theorems from algo:anb (`anbRun`) to the ANB with
sorted lists (`anbHeapRunWith anbGlobalIter`): stopping index, correctness at termination, band
half-width, number of bands containing a point, and numbers of updates at each point. -/
theorem transfer {p : AnbParams X} {𝒱 : X → Set X}
    (hst : Global.Ext.HasStencil 𝒱 (Global.monotoneExtension p.Γ))
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x)) (hα : 0 < p.α)
    (hτ : 0 < p.τ) {Kmax NΛ' NΛ'' NΓ : ℕ} {Δmax : ℝ}
    (hstop : anbStopIndex p ≤ (Kmax : ℕ∞))
    (hcorr : (anbRun p (anbStopIndex p).toNat).uSub ≤ p.Λ (anbRun p (anbStopIndex p).toNat).uSub ∧
      Global.monotoneExtension p.Λ (anbRun p (anbStopIndex p).toNat).uSup ≤
        (anbRun p (anbStopIndex p).toNat).uSup ∧
      anbDone p (anbRun p (anbStopIndex p).toNat))
    (hΔ : ∀ k, (anbRunData p k).Δ < Δmax)
    (hband : ∀ (x : X) (S : Finset ℕ), (∀ k ∈ S, x ∈ (anbRunData p k).band) → S.card ≤ NΛ')
    (hcount : ∀ (k : ℕ) (x : X),
      (anbRun p k).countSub x ≤ ((NΛ' * NΛ'' : ℕ) : ℕ∞) ∧
      (anbRun p k).countSup x ≤ ((NΛ' * NΛ'' : ℕ) : ℕ∞) ∧
      (anbRun p k).countHat x ≤ NΓ) :
    let run := anbHeapRunWith anbGlobalIter p 𝒱
    let data := anbHeapRunDataWith anbGlobalIter p 𝒱
    let K := anbHeapStopIndexWith anbGlobalIter p 𝒱
    let s := run K.toNat
    K ≤ (Kmax : ℕ∞) ∧
    (s.uSub p.τ ≤ p.Λ (s.uSub p.τ) ∧ Global.monotoneExtension p.Λ s.uSup ≤ s.uSup ∧
      ∀ x, s.uSup x ≤ (((1 + p.ε) * s.uSub p.τ x : ℝ) : WithTop ℝ)) ∧
    (∀ k, (data k).Δ < Δmax) ∧
    (∀ (x : X) (S : Finset ℕ), (∀ k ∈ S, x ∈ (data k).band) → S.card ≤ NΛ') ∧
    (∀ (k : ℕ) (x : X),
      (run k).countSub x ≤ ((NΛ' * NΛ'' : ℕ) : ℕ∞) ∧
      (run k).countSup x ≤ ((NΛ' * NΛ'' : ℕ) : ℕ∞) ∧
      (run k).dij.count x ≤ NΓ) := by
  intro run data K s
  obtain ⟨hH, hHstop⟩ := AnbHeapProof.equiv anbGlobalIter hst hΓmono hΓcaus hα hτ
  obtain ⟨hL, hLstop⟩ := AnbLazyProof.equiv anbGlobalIter hΓmono hΓcaus hα hτ.le
  have hK : K = anbStopIndex p := by
    change anbHeapStopIndexWith anbGlobalIter p 𝒱 = _
    rw [hHstop, hLstop]; rfl
  -- the quantities of the heap version at iteration `k` are those of `anbRun`
  have hrun : ∀ k, (run k).uSup = (anbRun p k).uSup ∧
      (0 < k → (run k).uSub p.τ = (anbRun p k).uSub) ∧
      (run k).countSub = (anbRun p k).countSub ∧ (run k).countSup = (anbRun p k).countSup ∧
      (run k).dij.count = (anbRun p k).countHat := by
    intro k
    obtain ⟨h1, h2, -, -, -, -, -, -, -, -, h11, h12, h13, -⟩ := hH k
    obtain ⟨l1, l2, -, -, -, -, -, -, -, -, -, l12, l13, l14⟩ := hL k
    exact ⟨h1.trans l1, fun hk => (h2 hk).trans l2, h11.trans l12, h12.trans l13,
      h13.trans l14⟩
  have hdata : ∀ k, (data k).Δ = (anbRunData p k).Δ ∧
      ((data k).band : Set X) = (anbRunData p k).band := by
    intro k
    obtain ⟨-, -, -, -, -, -, -, h8, h9, -⟩ := hH k
    obtain ⟨-, -, -, -, -, -, -, -, l9, l10, -⟩ := hL k
    exact ⟨h8.trans l9, h9.trans l10⟩
  refine ⟨hK ▸ hstop, ?_, fun k => (hdata k).1 ▸ hΔ k, ?_, ?_⟩
  · obtain ⟨hsub, hsup, hdone⟩ := hcorr
    have hs : s = run (anbStopIndex p).toNat := by rw [← hK]
    rcases Nat.eq_zero_or_pos (anbStopIndex p).toNat with h0 | hpos
    · -- stopping at iteration `0` forces `X = ∅`, since `u̲ = ∞` there
      have hX : IsEmpty X := by
        refine ⟨fun x => ?_⟩
        have := hdone x
        rw [h0] at this
        simp [anbRun, anbRunWith, anbInit] at this
      exact ⟨fun x => isEmptyElim x, fun x => isEmptyElim x, fun x => isEmptyElim x⟩
    · obtain ⟨r1, r2, -, -, -⟩ := hrun (anbStopIndex p).toNat
      rw [hs, r1, r2 hpos]
      exact ⟨hsub, hsup, hdone⟩
  · intro x S hS
    exact hband x S fun k hk => by
      rw [← (hdata k).2]; exact Finset.mem_coe.2 (hS k hk)
  · intro k x
    obtain ⟨-, -, r3, r4, r5⟩ := hrun k
    rw [r3, r4, r5]
    exact hcount k x

/-- Provider of `anbHeapRun_correct_complexity`. -/
theorem correct_complexity {X : Type*} [Fintype X] [LinearOrder X] {p : AnbParams X}
    {𝒱 : X → Set X} {I : Set X} {ubd : X → ℝ} (hΛbd : ∀ u, ∀ x ∉ I, p.Λ u x = ubd x)
    (hΓbd : ∀ u, ∀ x ∉ I, p.Γ u x = ubd x) {Cpast CΓ CΓ' : ℝ} (hCpast : 0 ≤ Cpast)
    (hCΓ : 1 ≤ CΓ) (hCΓ' : 0 ≤ CΓ') (hΛmono : ∀ x, Monotone (p.Λ · x))
    (hadd : ∀ x ∈ I, AdditivelyInvariant (p.Λ · x)) (hmem : ∀ x ∈ I, HasMemory Cpast (p.Λ · x))
    {w : X → ℝ} (hw : p.Λ w ≤ w) (hΓmono : ∀ x, Monotone (p.Γ · x))
    (hΓcaus : ∀ x, Causal (p.Γ · x)) (hΓadd : ∀ x ∈ I, AdditivelyInvariant (p.Γ · x))
    (hΓΛ : ∀ u, p.Γ u ≤ p.Λ u) (hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (p.Λ · x) (p.Γ · x))
    (hst : Global.Ext.HasStencil 𝒱 (Global.monotoneExtension p.Γ))
    (hsub : ∀ x ∈ I, SubAdditive p.ρ (kruzkovOp p.α (p.Λ · x))) (hα : 0 < p.α)
    (hρ0 : 0 < p.ρ) (hρ1 : p.ρ < 1) (hτ : 0 < p.τ) (hε : 0 < p.ε)
    (hbd : ∀ x ∉ I, 2 * p.Δmax ≤ ubd x) :
    ∃ uFix : X → ℝ, p.Λ uFix = uFix ∧ (∀ v, p.Λ v = v → v = uFix) ∧
      (∀ J : Set X, HasComparisonPrinciple J p.Λ) ∧
      (p.ε ≤ p.εmax uFix →
        let run := anbHeapRunWith anbGlobalIter p 𝒱
        let data := anbHeapRunDataWith anbGlobalIter p 𝒱
        let K := anbHeapStopIndexWith anbGlobalIter p 𝒱
        let s := run K.toNat
        let nmax := ⌈p.nMax uFix⌉₊
        let NΛ' := p.NΛ' Cpast CΓ CΓ' uFix
        let NΓ := p.NΓ Cpast CΓ CΓ' uFix
        let card𝒱 := ∑ x, (Global.Ext.revStencil 𝒱 x).card
        K ≤ ((nmax + 1 : ℕ) : ℕ∞) ∧
        (s.uSub p.τ ≤ p.Λ (s.uSub p.τ) ∧ Global.monotoneExtension p.Λ s.uSup ≤ s.uSup ∧
          ∀ x, s.uSup x ≤ (((1 + p.ε) * s.uSub p.τ x : ℝ) : WithTop ℝ)) ∧
        (∀ k, (data k).Δ < p.Δmax) ∧
        (∀ (x : X) (S : Finset ℕ), (∀ k ∈ S, x ∈ (data k).band) → S.card ≤ NΛ') ∧
        (∀ (k : ℕ) (x : X),
          (run k).countSub x ≤ ((NΛ' * p.NΛ'' : ℕ) : ℕ∞) ∧
          (run k).countSup x ≤ ((NΛ' * p.NΛ'' : ℕ) : ℕ∞) ∧
          (run k).dij.count x ≤ NΓ) ∧
        s.dij.evalCount ≤ Fintype.card X + card𝒱 * NΓ + (Fintype.card X + card𝒱) * NΛ' ∧
        s.dij.L.count + s.M.count + s.S.count + s.Sc.count ≤
          2 * Fintype.card X + 4 * (nmax + 1) + NΓ * (5 * Fintype.card X + card𝒱) +
            NΛ' * (12 * Fintype.card X + card𝒱)) := by
  obtain ⟨uFix, hfix, huniq, hcomp, hcplx⟩ := AnbComplexityProof.complexity hΛbd hΓbd hCpast hCΓ
    hCΓ' hΛmono hadd hmem hw hΓmono hΓcaus hΓadd hΓΛ hcmp hsub hα hρ0 hρ1 hτ hε hbd
  obtain ⟨uFix', hfix', -, hcost⟩ := anbHeapRun_complexity hst hΛbd hΓbd hCpast hCΓ hCΓ' hΛmono
    hadd hmem hw hΓmono hΓcaus hΓadd hΓΛ hcmp hsub hα hρ0 hρ1 hτ hε hbd
  obtain rfl : uFix' = uFix := huniq _ hfix'
  refine ⟨uFix', hfix, huniq, hcomp, fun hεmax => ?_⟩
  obtain ⟨hstop, hcorr, hΔ, -, hband, hcount⟩ := hcplx hεmax
  obtain ⟨-, hev, hops⟩ := (hcost hεmax).2
  obtain ⟨t1, t2, t3, t4, t5⟩ := transfer hst hΓmono hΓcaus hα hτ hstop hcorr hΔ hband hcount
  exact ⟨t1, t2, t3, t4, t5, hev, hops⟩

/-- Provider of `anbHeapRun_correct_complexity_withUnknown`. -/
theorem correct_complexity_withUnknown {X : Type*} [Fintype X] [LinearOrder X]
    {q : AnbParams.WithUnknown X} {𝒱 : X → Set X} {I : Set X} {ubd : X → ℝ}
    (hΛbd : ∀ u, ∀ x ∉ I, q.p.Λ u x = ubd x) (hΓbd : ∀ u, ∀ x ∉ I, q.p.Γ u x = ubd x)
    {Cpast CΓ CΓ' : ℝ} (hCpast : 0 ≤ Cpast) (hCΓ : 1 ≤ CΓ) (hCΓ' : 0 ≤ CΓ')
    (hΛmono : ∀ x, Monotone (q.p.Λ · x)) (hadd : ∀ x ∈ I, AdditivelyInvariant (q.p.Λ · x))
    (hmem : ∀ x ∈ I, HasMemory Cpast (q.p.Λ · x)) {w : X → ℝ} (hw : q.p.Λ w ≤ w)
    (hΓmono : ∀ x, Monotone (q.p.Γ · x)) (hΓcaus : ∀ x, Causal (q.p.Γ · x))
    (hΓadd : ∀ x ∈ I, AdditivelyInvariant (q.p.Γ · x)) (hΓΛ : ∀ u, q.p.Γ u ≤ q.p.Λ u)
    (hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (q.p.Λ · x) (q.p.Γ · x))
    (hst : Global.Ext.HasStencil 𝒱 (Global.monotoneExtension q.p.Γ))
    (hsub : ∀ x ∈ I, SubAdditive q.σ (kruzkovOp q.β (q.p.Λ · x))) (hα : 0 < q.p.α)
    (hαβ : q.p.α ≤ q.β) (hσ0 : 0 < q.σ) (hσ1 : q.σ < 1) (hρ1 : q.p.ρ < 1)
    (hρσ : (1 - q.σ) ^ q.β ≤ (1 - q.p.ρ) ^ q.p.α) (hτ : 0 < q.p.τ) (hε : 0 < q.p.ε)
    (hbd : ∀ x ∉ I, 2 * q.Δmax ≤ ubd x) :
    ∃ uFix : X → ℝ, q.p.Λ uFix = uFix ∧ (∀ v, q.p.Λ v = v → v = uFix) ∧
      (∀ J : Set X, HasComparisonPrinciple J q.p.Λ) ∧
      (q.p.ε ≤ q.εmax uFix →
        let run := anbHeapRunWith anbGlobalIter q.p 𝒱
        let data := anbHeapRunDataWith anbGlobalIter q.p 𝒱
        let K := anbHeapStopIndexWith anbGlobalIter q.p 𝒱
        let s := run K.toNat
        let nmax := ⌈q.nMax uFix⌉₊
        let NΛ' := q.NΛ' Cpast CΓ CΓ' uFix
        let NΓ := q.NΓ Cpast CΓ CΓ' uFix
        let card𝒱 := ∑ x, (Global.Ext.revStencil 𝒱 x).card
        K ≤ ((nmax + 1 : ℕ) : ℕ∞) ∧
        (s.uSub q.p.τ ≤ q.p.Λ (s.uSub q.p.τ) ∧
          Global.monotoneExtension q.p.Λ s.uSup ≤ s.uSup ∧
          ∀ x, s.uSup x ≤ (((1 + q.p.ε) * s.uSub q.p.τ x : ℝ) : WithTop ℝ)) ∧
        (∀ k, (data k).Δ < q.Δmax) ∧
        (∀ (x : X) (S : Finset ℕ), (∀ k ∈ S, x ∈ (data k).band) → S.card ≤ NΛ') ∧
        (∀ (k : ℕ) (x : X),
          (run k).countSub x ≤ ((NΛ' * q.NΛ'' : ℕ) : ℕ∞) ∧
          (run k).countSup x ≤ ((NΛ' * q.NΛ'' : ℕ) : ℕ∞) ∧
          (run k).dij.count x ≤ NΓ) ∧
        s.dij.evalCount ≤ Fintype.card X + card𝒱 * NΓ + (Fintype.card X + card𝒱) * NΛ' ∧
        s.dij.L.count + s.M.count + s.S.count + s.Sc.count ≤
          2 * Fintype.card X + 4 * (nmax + 1) + NΓ * (5 * Fintype.card X + card𝒱) +
            NΛ' * (12 * Fintype.card X + card𝒱)) := by
  obtain ⟨uFix, hfix, huniq, hcomp, hcplx⟩ := AnbWithUnknownProof.complexity hΛbd hΓbd hCpast hCΓ
    hCΓ' hΛmono hadd hmem hw hΓmono hΓcaus hΓadd hΓΛ hcmp hsub hα hαβ hσ0 hσ1 hρ1 hρσ hτ hε hbd
  obtain ⟨uFix', hfix', -, hcost⟩ := anbHeapRun_complexity_withUnknown hst hΛbd hΓbd hCpast hCΓ
    hCΓ' hΛmono hadd hmem hw hΓmono hΓcaus hΓadd hΓΛ hcmp hsub hα hαβ hσ0 hσ1 hρ1 hρσ hτ hε hbd
  obtain rfl : uFix' = uFix := huniq _ hfix'
  refine ⟨uFix', hfix, huniq, hcomp, fun hεmax => ?_⟩
  obtain ⟨hstop, hcorr, hΔ, -, hband, hcount⟩ := hcplx hεmax
  obtain ⟨-, hev, hops⟩ := (hcost hεmax).2
  obtain ⟨t1, t2, t3, t4, t5⟩ := transfer hst hΓmono hΓcaus hα hτ hstop hcorr hΔ hband hcount
  exact ⟨t1, t2, t3, t4, t5, hev, hops⟩

end GuaranteedSubsol.AnbHeapCorrectComplexityProof
