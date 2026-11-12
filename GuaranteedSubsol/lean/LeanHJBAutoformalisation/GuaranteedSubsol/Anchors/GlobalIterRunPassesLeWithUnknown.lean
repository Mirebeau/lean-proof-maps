/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.GlobalIterKruzkovProof

/-!
# Frozen statement: the global iteration for `Φ_α` stops when `Φ_β` is `σ`-sub-additive (V1)

Source: Lemma lem:cplx_global_iteration_withUnknown (Complexity.tex, V1): if `Λ` is monotone and
`Φ_β` is `σ`-sub-additive, with `0 < α ≤ β` and `0 < σ < 1`, then the global iteration
(algo:global_iteration) for `Φ_α`, started from `E_α ū` (sub-solution variant) or from `E_α u̲`
(super-solution version), stops within `⌈(ln(C/η) + ln(β/α))/(-ln σ)⌉` passes, where `ū ≤ Λ ū`,
`Λ u̲ ≤ u̲` (`u̲` with values in `ℝ_∞`, `Λ_∞` its extension) and `E_α ū ≥ -C`. It replaces the
anchor `globalIterRun_passes_le_of_kruzkov`, which stated the weaker V0 bound
`⌈(ln(C/η) + (β/α) ln 2)/(-ln σ)⌉` (author's ruling 2026-10-16); the proof uses lem:pow_cvx.
The numbers of passes are in `ℕ∞` (`⊤` if a loop never stops), so the bound
expresses termination. The order `ū ≤ u̲`, used for the super-solution version, follows from the
comparison principle; the paper's `C ≥ 0` is not needed (`C` only enters through `max(C, 0)`).
`X` is finite.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem globalIterRun_passes_le_withUnknown {X : Type*} [Finite X] {Λ : (X → ℝ) → X → ℝ}
    (hΛmono : ∀ x, Monotone (Λ · x)) {α β σ : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hsub : ∀ x, SubAdditive σ (kruzkovOp β (Λ · x)))
    {uSub : X → ℝ} {uSup : X → WithTop ℝ} (huSub : uSub ≤ Λ uSub)
    (huSup : Global.monotoneExtension Λ uSup ≤ uSup)
    {C η : ℝ} (hC : ∀ x, -C ≤ kruzkov (1 / α) (uSub x)) (hη : 0 < η) :
    globalIterSubPasses (Global.kruzkovOp α Λ) η (fun x => kruzkov (1 / α) (uSub x)) ≤
        (⌈(Real.log (C / η) + Real.log (β / α)) / (-Real.log σ)⌉₊ : ℕ∞) ∧
      globalIterPasses (Global.kruzkovOp α Λ) η (fun x => kruzkov (1 / α) (uSup x)) ≤
        (⌈(Real.log (C / η) + Real.log (β / α)) / (-Real.log σ)⌉₊ : ℕ∞) := by
  exact GlobalIterKruzkovProof.passes_le hΛmono hα hαβ hσ0 hσ1 hsub huSub huSup hC hη

end GuaranteedSubsol
