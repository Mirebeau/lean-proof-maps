/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.MonMinMaxProof

/-!
# Frozen statement: monotonicity restricted to a window of values, strict lower level

Variant of Corol. corol:mon_min_max (Complexity.tex), scalar form, with the strict assumption
`t₀ < Λ u - C_past` and no finiteness assumption on `X`: let `Λ` be monotone, causal, additively
invariant, with `C_past`-memory; let `t₀ < Λ u - C_past` and `t₁ ≥ Λ u`. If `v ≥ u` on
`{t₀ ≤ u < t₁}` and `v ≥ t₁` on `{u ≥ t₁}`, then `Λ u ≤ Λ v`. The scalar operator
`Λ : (X → ℝ) → ℝ` stands for `(Λ · x)`.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem apply_le_apply_of_causal_memory_of_lt {X : Type*} {Λ : (X → ℝ) → ℝ} {C : ℝ}
    (hmono : Monotone Λ) (hcaus : Causal Λ) (hadd : AdditivelyInvariant Λ)
    (hmem : HasMemory C Λ) {u v : X → ℝ} {t₀ t₁ : ℝ} (ht₀ : t₀ < Λ u - C) (ht₁ : Λ u ≤ t₁)
    (hmid : ∀ y, t₀ ≤ u y → u y < t₁ → u y ≤ v y) (htop : ∀ y, t₁ ≤ u y → t₁ ≤ v y) :
    Λ u ≤ Λ v := by
  exact MonMinMaxProof.apply_le_apply_of_causal_memory_of_lt hmono hcaus hadd hmem ht₀ ht₁ hmid htop

end GuaranteedSubsol
