/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.MaxMinProof

/-!
# Frozen statement: fixed point of the truncated operator `max {ū, min {T, Γ}}`

Source: Lemma lem:max_min (Complexity.tex): let `Γ` be causal, `Γ' := max {ū, min {T, Γ}}`. If
`u = max {ū, Γ u}`, then `û := max {ū, min {T, u}}` satisfies `Γ' û = û`, and
`min {u,T} = min {û,T}`. (The paper's last consequence, `{u < t} = {û < t}` for `t ≤ T`, is
omitted as trivial; author ruling.) Global operator `Γ : (X → ℝ) → X → ℝ`, causal at every point;
`Γ'` and `û` are written out explicitly.
Annotation (author's ruling 2026-10-20): V1 lem:max_min assumes `Γ` monotone and causal and states
that `û` is the unique fixed point; the anchor proves the fixed-point identity under causality
only. Uniqueness is not part of the anchor; it follows from `le_of_causal_real`.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem max_min_fixedPoint {X : Type*} {Γ : (X → ℝ) → X → ℝ} (hcaus : ∀ x, Causal (Γ · x))
    (uSub : X → ℝ) (T : ℝ) {u uHat : X → ℝ} (hu : u = fun x => max (uSub x) (Γ u x))
    (huHat : uHat = fun x => max (uSub x) (min T (u x))) :
    ((fun x => max (uSub x) (min T (Γ uHat x))) = uHat) ∧ ∀ x, min (u x) T = min (uHat x) T := by
  exact MaxMinProof.max_min_fixedPoint hcaus uSub T hu huHat

end GuaranteedSubsol
