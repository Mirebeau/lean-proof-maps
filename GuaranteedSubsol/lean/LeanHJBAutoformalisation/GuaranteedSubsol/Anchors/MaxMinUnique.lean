/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ExistsUniqueProof

/-!
# Frozen statement: uniqueness of the fixed point in lem:max_min

Source: Lemma lem:max_min (Complexity.tex, V1), uniqueness part (author's request 2026-10-20,
completing the anchor `max_min_fixedPoint`): let `Γ : ℝ^X → ℝ^X` be monotone and causal (at every
point), `ū ∈ ℝ^X`, `T ∈ ℝ`. If `u = max {ū, Γ u}` and `û := max {ū, min {T, u}}`, then every fixed
point `v` of `Γ' := max {ū, min {T, Γ}}` equals `û`. (That `û` is a fixed point is
`max_min_fixedPoint`.) `X` is finite.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem max_min_unique {X : Type*} [Finite X] {Γ : (X → ℝ) → X → ℝ}
    (hmono : ∀ x, Monotone (Γ · x)) (hcaus : ∀ x, Causal (Γ · x)) (uSub : X → ℝ) (T : ℝ)
    {u uHat v : X → ℝ} (hu : u = fun x => max (uSub x) (Γ u x))
    (huHat : uHat = fun x => max (uSub x) (min T (u x)))
    (hv : v = fun x => max (uSub x) (min T (Γ v x))) : v = uHat := by
  exact ExistsUniqueProof.max_min_unique hmono hcaus uSub T hu huHat hv

end GuaranteedSubsol
