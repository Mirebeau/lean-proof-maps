/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.AnbWithUnknownProof

/-!
# Frozen statement: the inner loops of the ANB stop after at most `N''_Λ` passes, unknown parameters

Source: Prop. prop:niter_while_withUnknown (Complexity.tex): in each iteration of the ANB,
the inner loops of lines anb:while_sub and anb:while_sup (global iterations on the band `B_n`)
perform at most `N''_Λ := ⌈(2Δ_max/α + ln(β/α) - ln(1 - ρ))/(-ln σ)⌉` passes
(`AnbParams.WithUnknown.NΛ''`); in particular they stop (the
number of passes is `⊤` in `ℕ∞` for a loop that never stops).
Hypotheses: those of Corollary corol:max_width_withUnknown: the parts of assum:all used
(memory and finite super-solution unused, omitted), `Φ_β` `σ`-sub-additive on `Int X` with
`0 < α ≤ β`, `0 < σ < 1`, `ρ < 1` (the paper's `ρ > 0` is unused, omitted),
`(1 - σ)^β ≤ (1 - ρ)^α`, a fixed point `u_*`, `0 < ε ≤ ε_max` and `2Δ_max ≤ u_bd`. The constants
`β`, `σ` are unknown: they are not parameters of the algorithm, which only uses `q.p`
(`AnbParams.WithUnknown`, author's decision, 2026-10-14). `Δ_max := 2β ln(2eC/ε) + 2τ`
(`AnbParams.WithUnknown.Δmax`). `X` is finite and linearly ordered (tie-breaking).

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem anbRunData_passes_le_withUnknown {X : Type*} [Fintype X] [LinearOrder X]
    {q : AnbParams.WithUnknown X} {I : Set X} {ubd : X → ℝ} (hΛbd : ∀ u, ∀ x ∉ I, q.p.Λ u x = ubd x)
    (hΓbd : ∀ u, ∀ x ∉ I, q.p.Γ u x = ubd x) {CΓ CΓ' : ℝ} (hCΓ : 1 ≤ CΓ)
    (hΛmono : ∀ x, Monotone (q.p.Λ · x)) (hadd : ∀ x ∈ I, AdditivelyInvariant (q.p.Λ · x))
    (hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (q.p.Λ · x) (q.p.Γ · x))
    (hΓmono : ∀ x, Monotone (q.p.Γ · x)) (hΓcaus : ∀ x, Causal (q.p.Γ · x))
    (hΓadd : ∀ x ∈ I, AdditivelyInvariant (q.p.Γ · x)) (hΓΛ : ∀ u, q.p.Γ u ≤ q.p.Λ u)
    (hsub : ∀ x ∈ I, SubAdditive q.σ (kruzkovOp q.β (q.p.Λ · x))) (hα : 0 < q.p.α)
    (hαβ : q.p.α ≤ q.β) (hσ0 : 0 < q.σ) (hσ1 : q.σ < 1) (hρ1 : q.p.ρ < 1)
    (hρσ : (1 - q.σ) ^ q.β ≤ (1 - q.p.ρ) ^ q.p.α) (hτ : 0 < q.p.τ) {uFix : X → ℝ}
    (hfix : q.p.Λ uFix = uFix) (hε : 0 < q.p.ε) (hεmax : q.p.ε ≤ q.εmax uFix)
    (hbd : ∀ x ∉ I, 2 * q.Δmax ≤ ubd x) (k : ℕ) :
    (anbRunData q.p k).passesSub ≤ (q.NΛ'' : ℕ∞) ∧
      (anbRunData q.p k).passesSup ≤ (q.NΛ'' : ℕ∞) := by
  exact AnbWithUnknownProof.passes_le
    ⟨hΛbd, hΓbd, hCΓ, hΛmono, hadd, hcmp, hΓmono, hΓcaus, hΓadd, hΓΛ, hsub, hα, hαβ, hσ0, hσ1,
      hρ1, hρσ, hτ, hfix, hε, hεmax, hbd⟩ k

end GuaranteedSubsol
