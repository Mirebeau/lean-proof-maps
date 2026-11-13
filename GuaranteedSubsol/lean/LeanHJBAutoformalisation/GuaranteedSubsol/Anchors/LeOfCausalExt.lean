/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.CausalExtProof

/-!
# Frozen statement: comparison principle for a monotone causal operator on `ℝ_∞`

Source: Prop. prop:comp_of_causal (Complexity.tex), with values in `ℝ_∞ = WithTop ℝ`: if `Γ` is
monotone and causal, then for any partition `X = Int Y ⊔ ∂Y` and `u, v ∈ ℝ_∞^X`,
`(u ≤ Γ u and Γ v ≤ v on Int Y, and u ≤ v on ∂Y) ⇒ u ≤ v`.

Here `Γ : (X → ℝ_∞) → X → ℝ_∞` acts directly on `ℝ_∞^X`, and causality is `Ext.Causal`
(`AxiomsExt.lean`). `Int Y` is the set `I`, `∂Y` its complement. Monotonicity and causality are
only assumed at the points of `I`.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem le_of_causal_ext {X : Type*} [Finite X] {Γ : (X → WithTop ℝ) → X → WithTop ℝ}
    {I : Set X} (hmono : ∀ x ∈ I, Monotone (Γ · x)) (hcaus : ∀ x ∈ I, Ext.Causal (Γ · x))
    {u v : X → WithTop ℝ} (hu : ∀ x ∈ I, u x ≤ Γ u x) (hv : ∀ x ∈ I, Γ v x ≤ v x)
    (hbd : ∀ x ∉ I, u x ≤ v x) :
    u ≤ v := by
  exact CausalExtProof.le_of_causal_ext hmono hcaus hu hv hbd

end GuaranteedSubsol
