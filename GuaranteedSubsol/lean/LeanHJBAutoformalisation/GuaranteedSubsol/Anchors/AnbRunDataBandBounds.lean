/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AnbBnCompProof

/-!
# Frozen statement: the exact solution on the narrow band `B_n` of the ANB

Source: Corollary corol:Bn_comp (Complexity.tex), first inclusion: in iteration `n = k` of the
ANB, `B_n ⊂ {t⁻_n ≤ u_* < t⁺_n}`, with `t⁻_n = t_n - Δ_n` (`AnbStepData.tMinus`) and
`t⁺_n = (1 + ε) t_n + C_past + C'_Γ + C_Γ Δ_n` (`AnbStepData.tPlus`).
Hypotheses: the parts of Assumption assum:all used by the proof, in the form of
`subsol_growth` (shared Dirichlet data `ubd` outside `I = Int X`; `Λ` monotone with `Λ[0] ≥ 0`,
additively invariant, with `C_past`-memory and `C_Γ, C'_Γ`-comparable with `Γ` on `Int X`; `Γ`
monotone, causal, `Γ ≤ Λ`), the comparison principle (eq. eq:comparison_Lambda, as in V1; see
`le_of_subSolution_superSolution`), a fixed point `u_*` (`uFix`) of `Λ`, and `α > 0`, `τ ≥ 0`,
`ε > 0`. `Γ` additively invariant, the finite super-solution (`u_*` is one) and the positive
boundary conditions (beyond `Λ[0] ≥ 0`) are not used, hence omitted. `X` is finite and linearly
ordered (tie-breaking).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem anbRunData_band_bounds {X : Type*} [Fintype X] [LinearOrder X] {p : AnbParams X}
    {I : Set X} {ubd : X → ℝ} (hΛbd : ∀ u, ∀ x ∉ I, p.Λ u x = ubd x)
    (hΓbd : ∀ u, ∀ x ∉ I, p.Γ u x = ubd x) {Cpast CΓ CΓ' : ℝ} (hCpast : 0 ≤ Cpast)
    (hCΓ : 1 ≤ CΓ) (hCΓ' : 0 ≤ CΓ') (hΛmono : ∀ x, Monotone (p.Λ · x)) (hΛ0 : 0 ≤ p.Λ 0)
    (hadd : ∀ x ∈ I, AdditivelyInvariant (p.Λ · x)) (hmem : ∀ x ∈ I, HasMemory Cpast (p.Λ · x))
    (hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (p.Λ · x) (p.Γ · x))
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x))
    (hΓΛ : ∀ u, p.Γ u ≤ p.Λ u) (hcomp : ∀ J : Set X, HasComparisonPrinciple J p.Λ)
    {uFix : X → ℝ} (hfix : p.Λ uFix = uFix) (hα : 0 < p.α) (hτ : 0 ≤ p.τ) (hε : 0 < p.ε)
    (k : ℕ) {x : X} (hx : x ∈ (anbRunData p k).band) :
    (anbRunData p k).tMinus ≤ uFix x ∧ uFix x < (anbRunData p k).tPlus p.ε Cpast CΓ CΓ' := by
  exact AnbBnCompProof.band_bounds hΛbd hΓbd hCpast hCΓ hCΓ' hΛmono hΛ0 hadd hmem hcmp hΓmono
    hΓcaus hΓΛ hcomp hfix hα hτ hε k hx

end GuaranteedSubsol
