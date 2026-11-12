/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.CausalProof

/-!
# Frozen statement: comparison principle for a monotone causal operator, real values

Source: Prop. prop:comp_of_causal (Complexity.tex), restricted to finite values `u, v ∈ ℝ^X`:
if `Γ` is monotone and causal, then for any partition `X = Int Y ⊔ ∂Y`,
`(u ≤ Γ u and Γ v ≤ v on Int Y, and u ≤ v on ∂Y) ⇒ u ≤ v`.

`Int Y` is the set `I`, `∂Y` its complement. Monotonicity and causality are only assumed at the
points of `I`.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem le_of_causal_real {X : Type*} [Finite X] {Γ : (X → ℝ) → X → ℝ} {I : Set X}
    (hmono : ∀ x ∈ I, Monotone (Γ · x)) (hcaus : ∀ x ∈ I, Causal (Γ · x)) {u v : X → ℝ}
    (hu : ∀ x ∈ I, u x ≤ Γ u x) (hv : ∀ x ∈ I, Γ v x ≤ v x) (hbd : ∀ x ∉ I, u x ≤ v x) :
    u ≤ v := by
  exact CausalProof.le_of_causal_real hmono hcaus hu hv hbd

end GuaranteedSubsol
