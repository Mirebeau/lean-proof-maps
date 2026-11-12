/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ULessTProof

/-!
# Frozen statement: fixed point of `max {ū, min {T, Γ}}` on `ℝ_∞`

Source: Lemma lem:max_min (Complexity.tex), on `ℝ_∞ = WithTop ℝ` (as used in the proof of
Lemma lem:u_less_t): let `Γ : (X → ℝ_∞) → X → ℝ_∞` be causal (`Ext.Causal` at every point). If
`u = max {ū, Γ u}`, then `û := max {ū, min {T, u}}` satisfies `max {ū, min {T, Γ û}} = û`, and
`min {u,T} = min {û,T}`. Here `ū` and `T` are real.
Annotation (author's ruling 2026-10-20): V1 lem:max_min assumes `Γ` monotone and causal and states
that `û` is the unique fixed point; the anchor proves the fixed-point identity under causality
only. Uniqueness is not part of the anchor; it follows from `le_of_causal_ext`.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol.Ext

theorem max_min_fixedPoint {X : Type*} {Γ : (X → WithTop ℝ) → X → WithTop ℝ}
    (hcaus : ∀ x, Causal (Γ · x)) (uSub : X → ℝ) (T : ℝ) {u uHat : X → WithTop ℝ}
    (hu : u = fun x => max (uSub x : WithTop ℝ) (Γ u x))
    (huHat : uHat = fun x => max (uSub x : WithTop ℝ) (min (T : WithTop ℝ) (u x))) :
    ((fun x => max (uSub x : WithTop ℝ) (min (T : WithTop ℝ) (Γ uHat x))) = uHat) ∧
      ∀ x, min (u x) T = min (uHat x) T := by
  exact GuaranteedSubsol.ULessTProof.ext_max_min_fixedPoint hcaus uSub T hu huHat

end GuaranteedSubsol.Ext
