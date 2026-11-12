/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AnbNiterProof

/-!
# ANB: Theorem th:complexity, proof

Provider proof for the frozen anchor `GuaranteedSubsol.anbRun_complexity`, see `ANCHORS.md`. The
proof assembles: the fixed point `u_*` (`existsUnique_fixedPoint_of_kruzkov`, with
`ρ`-sub-additivity at boundary points automatic since `Λ` is constant there), the comparison
principle (`AnbMaxWidthProof.hasComparisonPrinciple`), termination (`stopIndex_le`), the
properties of Prop. prop:always_subsol at the stopping index, the bound on `Δ_n` (`Δ_lt`), the
passes of the inner loops (`passes_le`), and the counts of Corollary corol:NGamma and
Theorem th:complexity (`card_band_le`, `countSub_countSup_le`, `countHat_le`).
-/

namespace GuaranteedSubsol.AnbComplexityProof

open AnbProof AnbBnCompProof AnbMaxWidthProof AnbNGammaProof AnbNiterProof

variable {X : Type*} [Fintype X] [LinearOrder X]

/-- At the stopping index, when it is finite, the stopping test holds. -/
theorem done_stopIndex {S : AnbInnerSolver X} {p : AnbParams X}
    (hex : ∃ k, anbDone p (anbRunWith S p k)) :
    anbDone p (anbRunWith S p (anbStopIndexWith S p).toNat) := by
  classical
  unfold anbStopIndexWith
  simp only [hex, ↓reduceDIte, ENat.toNat_natCast]
  convert Nat.find_spec hex

theorem complexity {p : AnbParams X}
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
        anbStopIndex p ≤ ((⌈p.nMax uFix⌉₊ + 1 : ℕ) : ℕ∞) ∧
        ((anbRun p (anbStopIndex p).toNat).uSub ≤ p.Λ (anbRun p (anbStopIndex p).toNat).uSub ∧
          Global.monotoneExtension p.Λ (anbRun p (anbStopIndex p).toNat).uSup ≤
            (anbRun p (anbStopIndex p).toNat).uSup ∧
          anbDone p (anbRun p (anbStopIndex p).toNat)) ∧
        (∀ k, (anbRunData p k).Δ < p.Δmax) ∧
        (∀ k, (anbRunData p k).passesSub ≤ (p.NΛ'' : ℕ∞) ∧
          (anbRunData p k).passesSup ≤ (p.NΛ'' : ℕ∞)) ∧
        (∀ (x : X) (S : Finset ℕ), (∀ k ∈ S, x ∈ (anbRunData p k).band) →
          S.card ≤ p.NΛ' Cpast CΓ CΓ' uFix) ∧
        (∀ (k : ℕ) (x : X),
          (anbRun p k).countSub x ≤ ((p.NΛ' Cpast CΓ CΓ' uFix * p.NΛ'' : ℕ) : ℕ∞) ∧
          (anbRun p k).countSup x ≤ ((p.NΛ' Cpast CΓ CΓ' uFix * p.NΛ'' : ℕ) : ℕ∞) ∧
          (anbRun p k).countHat x ≤ p.NΓ Cpast CΓ CΓ' uFix)) := by
  have hsubAll : ∀ x, SubAdditive p.ρ (kruzkovOp p.α (p.Λ · x)) := fun x => by
    by_cases hx : x ∈ I
    · exact hsub x hx
    · exact subAdditive_kruzkovOp_const (fun u => hΛbd u x hx) hρ0.le
  obtain ⟨uFix, hfix, huniq, -⟩ :=
    ComparisonLambdaProof.existsUnique_fixedPoint_of_kruzkov hα hρ1 hΛmono hsubAll hw
  refine ⟨uFix, hfix, huniq, hasComparisonPrinciple hΛbd hΛmono hα hρ1 hsub, fun hεmax => ?_⟩
  have h : Hyp p I ubd CΓ CΓ' uFix := ⟨hΛbd, hΓbd, hCΓ, hΛmono, hadd, hcmp, hΓmono, hΓcaus,
    hΓadd, hΓΛ, hsub, hα, hρ0.le, hρ1, hτ, hfix, hε, hεmax, hbd⟩
  have hAS := h.always (S := anbGlobalIter) (anbStopIndex p).toNat
  refine ⟨stopIndex_le h, ⟨hAS.uSub_le, hAS.uSup_ge, done_stopIndex ⟨_, done h⟩⟩, Δ_lt h,
    passes_le h hρ0, fun x S hS => card_band_le h hCpast hCΓ' hmem x hS, fun k x => ?_⟩
  obtain ⟨h1, h2⟩ := countSub_countSup_le h hρ0 hCpast hCΓ' hmem k x
  exact ⟨h1, h2, countHat_le h hCpast hCΓ' hmem k x⟩

end GuaranteedSubsol.AnbComplexityProof
