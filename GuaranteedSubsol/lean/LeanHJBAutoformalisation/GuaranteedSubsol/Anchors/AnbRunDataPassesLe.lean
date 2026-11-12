/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AnbNiterProof

/-!
# Frozen statement: the inner loops of the ANB stop after at most `N''_Λ` passes

Source: Prop. prop:niter_while (Complexity.tex): in each iteration of the ANB, the inner loops of
lines anb:while_sub and anb:while_sup (global iterations on the band `B_n`, `AnbStepData.ΦSub`,
`AnbStepData.ΦSup`) perform at most `N''_Λ := ⌈(2Δ_max/α - ln(1 - ρ))/(-ln ρ)⌉` passes
(`AnbParams.NΛ''`); in particular they stop, since the number of passes is `⊤` (in `ℕ∞`)
for a loop that never stops (author ruling, 2026-10-14: pass counts in `ℕ∞`). The proof uses the
termination of the global iteration (`globalIterSubRun_terminates`, `globalIterRun_terminates`)
applied on the band (author's request).
Hypotheses: those of Corollary corol:max_width (see `anbRunData_Δ_lt_Δmax`, with
`Δ_max := 2α ln(2e/ε) + 2τ`), and `ρ > 0` (`ln ρ` appears in `N''_Λ`), as in the paper. `X` is
finite and linearly ordered (tie-breaking). Constants renamed with Greek letters (`Δmax`,
`ΔplusMax`, `εmax`, `NΛ'`, `NΛ''`, `NΓ`) and inner-loop pass counts written `passesSub`, `passesSup`
(author ruling, 2026-10-14; statements equal by definition).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem anbRunData_passes_le {X : Type*} [Fintype X] [LinearOrder X] {p : AnbParams X}
    {I : Set X} {ubd : X → ℝ} (hΛbd : ∀ u, ∀ x ∉ I, p.Λ u x = ubd x)
    (hΓbd : ∀ u, ∀ x ∉ I, p.Γ u x = ubd x) {CΓ CΓ' : ℝ} (hCΓ : 1 ≤ CΓ)
    (hΛmono : ∀ x, Monotone (p.Λ · x)) (hadd : ∀ x ∈ I, AdditivelyInvariant (p.Λ · x))
    (hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (p.Λ · x) (p.Γ · x))
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x))
    (hΓadd : ∀ x ∈ I, AdditivelyInvariant (p.Γ · x)) (hΓΛ : ∀ u, p.Γ u ≤ p.Λ u)
    (hsub : ∀ x ∈ I, SubAdditive p.ρ (kruzkovOp p.α (p.Λ · x))) (hα : 0 < p.α)
    (hρ0 : 0 ≤ p.ρ) (hρ1 : p.ρ < 1) (hτ : 0 < p.τ) {uFix : X → ℝ} (hfix : p.Λ uFix = uFix)
    (hε : 0 < p.ε) (hεmax : p.ε ≤ p.εmax uFix) (hbd : ∀ x ∉ I, 2 * p.Δmax ≤ ubd x)
    (hρpos : 0 < p.ρ) (k : ℕ) :
    (anbRunData p k).passesSub ≤ (p.NΛ'' : ℕ∞) ∧
      (anbRunData p k).passesSup ≤ (p.NΛ'' : ℕ∞) := by
  exact AnbNiterProof.passes_le
    ⟨hΛbd, hΓbd, hCΓ, hΛmono, hadd, hcmp, hΓmono, hΓcaus, hΓadd, hΓΛ, hsub, hα, hρ0, hρ1, hτ,
      hfix, hε, hεmax, hbd⟩ hρpos k

end GuaranteedSubsol
