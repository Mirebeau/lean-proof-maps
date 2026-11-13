/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.Band
public import LeanHJBAutoformalisation.GuaranteedSubsol.Restriction
public import LeanHJBAutoformalisation.GuaranteedSubsol.Axioms
public import Mathlib.Tactic.Linarith

/-!
# An operator acting on a band: basic properties

The band operator `bandOp Φ B w` inherits monotonicity and `ρ`-sub-additivity from `Φ` at the
points of `B` (`monotone_bandOp`, `subAdditive_bandOp`), and is related to the restriction `Φ_B`
by `restrictOp_bandExtend`.
-/

@[expose] public section

namespace GuaranteedSubsol.BandProof

variable {X : Type*} {Φ : (X → ℝ) → X → ℝ} {B : Set X} {w : X → ℝ}

theorem bandExtend_mono {v v' : B → ℝ} (h : v ≤ v') : bandExtend B w v ≤ bandExtend B w v' :=
  fun y => by
    by_cases hy : y ∈ B
    · rw [bandExtend_of_mem _ _ _ hy, bandExtend_of_mem _ _ _ hy]; exact h _
    · rw [bandExtend_of_notMem _ _ _ hy, bandExtend_of_notMem _ _ _ hy]

theorem monotone_bandOp (hmono : ∀ x ∈ B, Monotone (Φ · x)) : Monotone (bandOp Φ B w) :=
  fun _ _ h x => hmono x x.2 (bandExtend_mono h)

/-- `Φ_B (v ⊔_B w) = (bandOp Φ B w v) ⊔_B w`. -/
theorem restrictOp_bandExtend (v : B → ℝ) :
    restrictOp Φ B (bandExtend B w v) = bandExtend B w (bandOp Φ B w v) := funext fun y => by
  by_cases hy : y ∈ B
  · rw [restrictOp_of_mem _ hy, bandExtend_of_mem _ _ _ hy]
    rfl
  · rw [restrictOp_of_notMem _ hy, bandExtend_of_notMem _ _ _ hy, bandExtend_of_notMem _ _ _ hy]

/-- `ρ`-sub-additivity of `Φ` at a point of `B` transfers to the band operator. -/
theorem subAdditive_bandOp {ρ : ℝ} {x : X} (hx : x ∈ B) (hmono : Monotone (Φ · x))
    (hsub : SubAdditive ρ (Φ · x)) : SubAdditive ρ (bandOp Φ B w · ⟨x, hx⟩) := by
  intro v t ht
  have hle : bandExtend B w (fun y => v y + t) ≤ fun y => bandExtend B w v y + t := fun y => by
    by_cases hy : y ∈ B
    · simp only [bandExtend_of_mem _ _ _ hy, le_refl]
    · simp only [bandExtend_of_notMem _ _ _ hy]
      linarith
  exact (hmono hle).trans (hsub _ t ht)

end GuaranteedSubsol.BandProof
