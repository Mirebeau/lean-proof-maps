/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.KruzkovProof

/-!
# Frozen statement: `Φ_α` is multiplicatively invariant

Source: Prop. prop:monotonic_Phi (Complexity.tex): if `Λ` is additively invariant, then
`Φ_α (γ v) (x) = γ Φ_α v (x)` for all `γ > 0`, `v ∈ ℝ^X` and `x ∈ Int X`. Scalar form
(`Λ : (X → ℝ) → ℝ` stands for `(Λ · x)` at `x ∈ Int X`), with `α > 0`.

The paper assumes `Λ` monotone. With the generalized `monotoneExtension` (supremum over finite
minorants) this hypothesis is not needed, so it is omitted.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem kruzkovOp_mul {X : Type*} {α : ℝ} (hα : 0 < α) {Λ : (X → ℝ) → ℝ}
    (hadd : AdditivelyInvariant Λ) {γ : ℝ} (hγ : 0 < γ) (v : X → ℝ) :
    kruzkovOp α Λ (fun y => γ * v y) = γ * kruzkovOp α Λ v := by
  exact KruzkovProof.kruzkovOp_mul hα hadd hγ v

end GuaranteedSubsol
