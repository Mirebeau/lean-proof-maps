/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.AnbMaxWidthProof

/-!
# Frozen statement: the half-width of the narrow band of the ANB is bounded

Source: Corollary corol:max_width (Complexity.tex), second claim: in each iteration of the ANB,
`Δ_n < Δ_max`.
Hypotheses: the parts of Assumption assum:all used by the proof, in the form of
`subsol_growth` (`Λ` and `Γ` have the Dirichlet data `ubd` outside `I = Int X`; `Λ` monotone and
additively invariant on `Int X`; `Γ` monotone, causal, additively invariant on `Int X`, `Γ ≤ Λ`,
and `C_Γ, C'_Γ`-comparable with `Λ`, `C_Γ ≥ 1`); the `ρ`-sub-additivity of `Φ_α` on `Int X`
with `α > 0`, `0 ≤ ρ < 1` (the parameters `α`, `ρ` of algo:anb); a fixed point `u_*` (`uFix`) of
`Λ`; `τ > 0`, `0 < ε ≤ ε_max` (`AnbParams.εmax`) and `2 Δ_max ≤ min u_bd`. The memory property
and the finite super-solution of assum:all are not used, hence omitted; `Λ[0] ≥ 0` and the
comparison principle are derived from sub-additivity. `Δ_max := 2α ln(2e/ε) + 2τ`
(`AnbParams.Δmax`), as in the paper. `X` is finite and linearly ordered (tie-breaking).
Constants renamed with Greek letters (`Δmax`, `ΔplusMax`, `εmax`, `NΛ'`, `NΛ''`, `NΓ`) and
inner-loop pass counts written `passesSub`, `passesSup` (author ruling, 2026-10-14; statements
equal by definition).

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem anbRunData_Δ_lt_Δmax {X : Type*} [Fintype X] [LinearOrder X] {p : AnbParams X}
    {I : Set X} {ubd : X → ℝ} (hΛbd : ∀ u, ∀ x ∉ I, p.Λ u x = ubd x)
    (hΓbd : ∀ u, ∀ x ∉ I, p.Γ u x = ubd x) {CΓ CΓ' : ℝ} (hCΓ : 1 ≤ CΓ)
    (hΛmono : ∀ x, Monotone (p.Λ · x)) (hadd : ∀ x ∈ I, AdditivelyInvariant (p.Λ · x))
    (hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (p.Λ · x) (p.Γ · x))
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x))
    (hΓadd : ∀ x ∈ I, AdditivelyInvariant (p.Γ · x)) (hΓΛ : ∀ u, p.Γ u ≤ p.Λ u)
    (hsub : ∀ x ∈ I, SubAdditive p.ρ (kruzkovOp p.α (p.Λ · x))) (hα : 0 < p.α)
    (hρ0 : 0 ≤ p.ρ) (hρ1 : p.ρ < 1) (hτ : 0 < p.τ) {uFix : X → ℝ} (hfix : p.Λ uFix = uFix)
    (hε : 0 < p.ε) (hεmax : p.ε ≤ p.εmax uFix) (hbd : ∀ x ∉ I, 2 * p.Δmax ≤ ubd x)
    (k : ℕ) : (anbRunData p k).Δ < p.Δmax := by
  exact AnbMaxWidthProof.Δ_lt ⟨hΛbd, hΓbd, hCΓ, hΛmono, hadd, hcmp, hΓmono, hΓcaus,
    hΓadd, hΓΛ, hsub, hα, hρ0, hρ1, hτ, hfix, hε, hεmax, hbd⟩ k

end GuaranteedSubsol
