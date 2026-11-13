/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.ExistsUniqueProof

/-!
# Frozen statement: the three fixed points of lem:u_less_t exist and are unique

Source: Lemma lem:u_less_t (Complexity.tex), first sentence (author's request 2026-10-20,
completing the anchor `u_less_t`): let `Γ : ℝ_∞^X → ℝ_∞^X` be monotone and causal (at every
point), `ū ∈ ℝ^X`, `T ∈ ℝ`. Then the operators `Γ' := max {ū, Γ}`, `Γ̌ := max {ū, Γ}^{<T}` and
`Γ̂ := max {ū, min {T, Γ}}` are monotone and causal, and each has a unique fixed point in `ℝ_∞^X`
(the fixed points `u`, `ǔ`, `û` of the lemma). The operators are written out pointwise; the fixed
points are stated in the form `u = fun x => …` of the hypotheses of `u_less_t`. Cutoffs are
`cutoffLt` (eq. eqdef:u_less_t). `X` is finite.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem u_less_t_existsUnique {X : Type*} [Finite X] {Γ : (X → WithTop ℝ) → X → WithTop ℝ}
    (hmono : ∀ x, Monotone (Γ · x)) (hcaus : ∀ x, Ext.Causal (Γ · x)) (uSub : X → ℝ) (T : ℝ) :
    (∀ x, Monotone (fun u => max (uSub x : WithTop ℝ) (Γ u x)) ∧
      Ext.Causal (fun u => max (uSub x : WithTop ℝ) (Γ u x))) ∧
    (∀ x, Monotone (fun u => cutoffLt T (max (uSub x : WithTop ℝ) (Γ u x))) ∧
      Ext.Causal (fun u => cutoffLt T (max (uSub x : WithTop ℝ) (Γ u x)))) ∧
    (∀ x, Monotone (fun u => max (uSub x : WithTop ℝ) (min (T : WithTop ℝ) (Γ u x))) ∧
      Ext.Causal (fun u => max (uSub x : WithTop ℝ) (min (T : WithTop ℝ) (Γ u x)))) ∧
    (∃! u : X → WithTop ℝ, u = fun x => max (uSub x : WithTop ℝ) (Γ u x)) ∧
    (∃! u : X → WithTop ℝ, u = fun x => cutoffLt T (max (uSub x : WithTop ℝ) (Γ u x))) ∧
    (∃! u : X → WithTop ℝ,
      u = fun x => max (uSub x : WithTop ℝ) (min (T : WithTop ℝ) (Γ u x))) := by
  exact ExistsUniqueProof.u_less_t_existsUnique hmono hcaus uSub T

end GuaranteedSubsol
