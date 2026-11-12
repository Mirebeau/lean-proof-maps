/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ULessTProof

/-!
# Frozen statement: cutting a fixed point of `max {ū, Γ}` at a level `T`

Source: Lemma lem:u_less_t (Complexity.tex): let `Γ : ℝ_∞^X → ℝ_∞^X` be causal (`Ext.Causal` at
every point), `ū ∈ ℝ^X`, `T ∈ ℝ`, and `u = max {ū, Γ u}`. Then `ǔ := u^{<T}` satisfies
`ǔ = max {ū, Γ ǔ}^{<T}`; `û := max {ū, min {T, ǔ}}` satisfies `û = max {ū, min {T, Γ û}}`; and
`ǔ = û^{<T}`. Cutoffs are `cutoffLt` pointwise. Author ruling: the monotonicity of `Γ` is
dropped, being unused.
Annotation (author's ruling 2026-10-20): V1 lem:u_less_t states that the three operators are
monotone and causal and have unique fixed points `u`, `ǔ`, `û`; the anchor proves the identities
`ǔ = u^{<T}`, `û = max {ū, min {T, ǔ}}`, `ǔ = û^{<T}` for a given fixed point `u` of
`Γ' = max {ū, Γ}`, under causality only. Existence and uniqueness are not part of the anchor; they
follow from the comparison principle for causal operators and Dijkstra's method.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem u_less_t {X : Type*} {Γ : (X → WithTop ℝ) → X → WithTop ℝ}
    (hcaus : ∀ x, Ext.Causal (Γ · x)) (uSub : X → ℝ) (T : ℝ) {u ucheck uHat : X → WithTop ℝ}
    (hu : u = fun x => max (uSub x : WithTop ℝ) (Γ u x))
    (hucheck : ucheck = fun x => cutoffLt T (u x))
    (huHat : uHat = fun x => max (uSub x : WithTop ℝ) (min (T : WithTop ℝ) (ucheck x))) :
    (ucheck = fun x => cutoffLt T (max (uSub x : WithTop ℝ) (Γ ucheck x))) ∧
      (uHat = fun x => max (uSub x : WithTop ℝ) (min (T : WithTop ℝ) (Γ uHat x))) ∧
      ucheck = fun x => cutoffLt T (uHat x) := by
  exact GuaranteedSubsol.ULessTProof.u_less_t hcaus uSub T hu hucheck huHat

end GuaranteedSubsol
