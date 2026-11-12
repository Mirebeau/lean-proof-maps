/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ApplyZeroNonnegProof

/-!
# Frozen statement: `Λ[0] ≥ 0` under Assumption assum:all

Source: the remark after Prop. prop:always_subsol (Complexity.tex, V1), author's request:
the assumption `Λ[0] ≥ 0` of Prop. prop:always_subsol follows from Assumption assum:all. If `Λ` has
the Dirichlet data `ubd ≥ 0` outside `I = Int X` (non-negative boundary conditions), and `Γ` is
additively invariant and causal on `Int X` and underestimates `Λ`, then `Λ[0] ≥ 0` on `X` (in
fact `Λ[0] ≥ Γ[0] > 0` on `Int X`). Global operators `(X → ℝ) → X → ℝ`.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem apply_zero_nonneg_of_causal {X : Type*} {Λ Γ : (X → ℝ) → X → ℝ} {I : Set X}
    {ubd : X → ℝ} (hΛbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) (hubd : ∀ x ∉ I, 0 ≤ ubd x)
    (hΓadd : ∀ x ∈ I, AdditivelyInvariant (Γ · x)) (hΓcaus : ∀ x ∈ I, Causal (Γ · x))
    (hΓΛ : ∀ u, Γ u ≤ Λ u) : 0 ≤ Λ 0 := by
  exact ApplyZeroNonnegProof.apply_zero_nonneg_of_causal hΛbd hubd hΓadd hΓcaus hΓΛ

end GuaranteedSubsol
