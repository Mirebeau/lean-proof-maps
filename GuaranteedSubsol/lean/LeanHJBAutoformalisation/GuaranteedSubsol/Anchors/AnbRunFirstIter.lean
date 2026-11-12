/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AnbFirstIterProof

/-!
# Frozen statement: the first iterations of the ANB are vacuous

Source: Lemma lem:first_iter (Complexity.tex): in an iteration `1 ≤ k` of the ANB with
`kτ ≤ min u_bd`, `ū_k = (k-1)τ`, `u̲_k = ∞`, `û_k = kτ`, `t_k = kτ`, `Δ_k = 0` and `B_k = ∅`.
In addition (author's request), no update of `ū`, `u̲` or `û` is made in the iterations
`0, …, k`: the three update counters vanish at the end of iteration `k`. The iterations are
numbered from `0` (Remark rem:anb_npos); iteration `0` is covered by `anbRun_zero_vacuous`.
Hypotheses: the parts of Assumption assum:all used by the proof, in the form of `subsol_growth`:
`Γ` has the Dirichlet data `ubd` outside `I = Int X`, is additively invariant and
`C_Γ, C'_Γ`-comparable with `Λ` on `Int X`, with `C_Γ ≥ 1`, and `Γ` is monotone; `α > 0`,
`τ ≥ 0`; and `Λ[0] ≥ 0`, a consequence of assum:all (causality and additive invariance of `Γ`
give `Γ[0] > 0` on `Int X`, and `Γ ≤ Λ`; see the remark after prop:always_subsol), used
here to get `t ≤ Γ[t]` by Prop. prop:cst_subsol, second part. Causality of `Γ` (approved in the
statement) is not used, hence omitted: the initial guess of Dijkstra's method is already the
fixed point `kτ`. `X` is finite and linearly ordered (tie-breaking).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem anbRun_first_iter {X : Type*} [Fintype X] [LinearOrder X] {p : AnbParams X}
    {I : Set X} {ubd : X → ℝ} (hΓbd : ∀ u, ∀ x ∉ I, p.Γ u x = ubd x) {CΓ CΓ' : ℝ}
    (hCΓ : 1 ≤ CΓ) (hΛ0 : 0 ≤ p.Λ 0) (hΓadd : ∀ x ∈ I, AdditivelyInvariant (p.Γ · x))
    (hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (p.Λ · x) (p.Γ · x))
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hα : 0 < p.α) (hτ : 0 ≤ p.τ) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : ∀ x ∉ I, (k : ℝ) * p.τ ≤ ubd x) :
    (anbRun p k).uSub = (fun _ => ((k : ℝ) - 1) * p.τ) ∧ (anbRun p k).uSup = (fun _ => ⊤) ∧
    (anbRunData p k).uHat = (fun _ => (k : ℝ) * p.τ) ∧ (anbRunData p k).t = k * p.τ ∧
    (anbRunData p k).Δ = 0 ∧ (anbRunData p k).band = ∅ ∧
    (anbRun p (k + 1)).countSub = 0 ∧ (anbRun p (k + 1)).countSup = 0 ∧
    (anbRun p (k + 1)).countHat = 0 := by
  exact AnbFirstIterProof.first_iter hΓbd hCΓ hΛ0 hΓadd hcmp hΓmono hα hτ hk1 hk

end GuaranteedSubsol
