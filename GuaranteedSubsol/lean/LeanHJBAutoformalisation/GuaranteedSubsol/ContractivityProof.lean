/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.Axioms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Contractivity of monotone sub-additive operators

Provider proofs for the frozen anchors `GuaranteedSubsol.norm_sub_le_of_subAdditive` and
`GuaranteedSubsol.existsUnique_fixedPoint_of_subAdditive` (see `ANCHORS.md`), from
Prop. prop:contractivity (Complexity.tex): a monotone `ρ`-sub-additive operator
`Φ : ℝ^X → ℝ^X` is `ρ`-Lipschitz for the sup norm, and for `ρ < 1` it has a unique fixed point,
approached by the iterates at the a-priori Banach rate. The fixed point part is Mathlib's
`ContractingWith` (Banach fixed point theorem).
-/

@[expose] public section

namespace GuaranteedSubsol.ContractivityProof

/-- One-sided bound: `Φ u x ≤ Φ v x + ρ ‖u - v‖`, by monotonicity (`u ≤ v + ‖u - v‖`) and
sub-additivity at `x`. -/
theorem le_add_mul_norm_sub {X : Type*} [Fintype X] {Φ : (X → ℝ) → X → ℝ} {ρ : ℝ}
    (hmono : Monotone Φ) (hsub : ∀ x, SubAdditive ρ (Φ · x)) (u v : X → ℝ) (x : X) :
    Φ u x ≤ Φ v x + ρ * ‖u - v‖ := by
  have h1 : u ≤ fun y => v y + ‖u - v‖ := fun y => by
    have := norm_le_pi_norm (u - v) y
    rw [Pi.sub_apply, Real.norm_eq_abs] at this
    linarith [le_abs_self (u y - v y)]
  exact (hmono h1 x).trans (hsub x v _ (norm_nonneg _))

/-- If `X` is nonempty, a monotone `ρ`-sub-additive operator forces `0 ≤ ρ`. -/
theorem nonneg_of_subAdditive {X : Type*} [Nonempty X] {Φ : (X → ℝ) → X → ℝ} {ρ : ℝ}
    (hmono : Monotone Φ) (hsub : ∀ x, SubAdditive ρ (Φ · x)) : 0 ≤ ρ := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have h1 : (0 : X → ℝ) ≤ fun y => (0 : X → ℝ) y + 1 := fun y => by simp
  have h2 := (hmono h1 x).trans (hsub x 0 1 zero_le_one)
  linarith

theorem norm_sub_le_of_subAdditive {X : Type*} [Fintype X] {Φ : (X → ℝ) → X → ℝ} {ρ : ℝ}
    (hmono : Monotone Φ) (hsub : ∀ x, SubAdditive ρ (Φ · x)) (u v : X → ℝ) :
    ‖Φ u - Φ v‖ ≤ ρ * ‖u - v‖ := by
  rcases isEmpty_or_nonempty X with hX | hX
  · simp [Subsingleton.elim (Φ u - Φ v) 0, Subsingleton.elim (u - v) 0]
  have hρ := nonneg_of_subAdditive hmono hsub
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hρ (norm_nonneg _))).2 fun x => ?_
  have h1 := le_add_mul_norm_sub hmono hsub u v x
  have h2 := le_add_mul_norm_sub hmono hsub v u x
  rw [norm_sub_rev v u] at h2
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_le_iff]
  constructor <;> linarith

theorem existsUnique_fixedPoint_of_subAdditive {X : Type*} [Fintype X] {Φ : (X → ℝ) → X → ℝ}
    {ρ : ℝ} (hρ : ρ < 1) (hmono : Monotone Φ) (hsub : ∀ x, SubAdditive ρ (Φ · x)) :
    ∃ vFix : X → ℝ, Φ vFix = vFix ∧ (∀ w, Φ w = w → w = vFix) ∧
      ∀ (v : X → ℝ) (n : ℕ), ‖Φ^[n] v - vFix‖ ≤ ρ ^ n * ‖Φ v - v‖ / (1 - ρ) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · refine ⟨0, Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _, fun v n => ?_⟩
    simp [Subsingleton.elim (Φ^[n] v - 0) 0, Subsingleton.elim (Φ v - v) 0]
  have hρ0 := nonneg_of_subAdditive hmono hsub
  set K : NNReal := ⟨ρ, hρ0⟩ with hK
  have hKρ : (K : ℝ) = ρ := rfl
  have hf : ContractingWith K Φ := by
    refine ⟨by rw [← NNReal.coe_lt_coe]; exact hρ, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
    rw [dist_eq_norm, dist_eq_norm]
    exact norm_sub_le_of_subAdditive hmono hsub u v
  refine ⟨ContractingWith.fixedPoint Φ hf, ContractingWith.fixedPoint_isFixedPt hf,
    fun w hw => ContractingWith.fixedPoint_unique hf hw, fun v n => ?_⟩
  have := ContractingWith.apriori_dist_iterate_fixedPoint_le hf v n
  rw [dist_eq_norm, dist_comm, dist_eq_norm] at this
  rwa [hKρ, mul_comm] at this

end GuaranteedSubsol.ContractivityProof
