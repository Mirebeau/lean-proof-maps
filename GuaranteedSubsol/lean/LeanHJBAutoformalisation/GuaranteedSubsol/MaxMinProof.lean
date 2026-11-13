/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.Axioms
public import Mathlib.Tactic.Linarith

/-!
# Fixed point of the truncated operator `max {ū, min {T, Γ}}`: proof

Provider proof for the frozen anchor `GuaranteedSubsol.max_min_fixedPoint` (see `ANCHORS.md`):
Lemma lem:max_min (Complexity.tex). First `min {u,T} = min {û,T}`, since `ū ≤ u`; then causality
gives `min {T, Γ û} = min {T, Γ u}`, and a lattice identity concludes `Γ' û = û`.
-/

@[expose] public section

namespace GuaranteedSubsol.MaxMinProof

/-- Lattice identity: `max a (min T b) = max a (min T (max a b))`. -/
theorem max_min_max (a b T : ℝ) : max a (min T b) = max a (min T (max a b)) := by
  simp only [max_def, min_def]
  split_ifs <;> linarith

/-- Truncation at `T` only sees truncations at levels `s ≥ T`. -/
theorem min_min_of_le {a T s : ℝ} (h : T ≤ s) : min T (min a s) = min T a := by
  simp only [min_def]
  split_ifs <;> linarith

/-- `min {u,T} = min {û,T}` when `ū ≤ u`. -/
theorem min_max_min (a b T : ℝ) (h : a ≤ b) : min b T = min (max a (min T b)) T := by
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem max_min_fixedPoint {X : Type*} {Γ : (X → ℝ) → X → ℝ} (hcaus : ∀ x, Causal (Γ · x))
    (uSub : X → ℝ) (T : ℝ) {u uHat : X → ℝ} (hu : u = fun x => max (uSub x) (Γ u x))
    (huHat : uHat = fun x => max (uSub x) (min T (u x))) :
    ((fun x => max (uSub x) (min T (Γ uHat x))) = uHat) ∧ ∀ x, min (u x) T = min (uHat x) T := by
  have hux : ∀ x, u x = max (uSub x) (Γ u x) := fun x => congrFun hu x
  have hle : ∀ x, uSub x ≤ u x := fun x => (hux x).symm ▸ le_max_left _ _
  subst huHat
  have hmin : ∀ x, min (u x) T = min (max (uSub x) (min T (u x))) T :=
    fun x => min_max_min _ _ _ (hle x)
  refine ⟨funext fun x => ?_, hmin⟩
  obtain ⟨δ, hδ, h⟩ := hcaus x (fun y => max (uSub y) (min T (u y))) u T
    fun y => (hmin y).symm
  have hkey : min T (Γ (fun y => max (uSub y) (min T (u y))) x) = min T (Γ u x) := by
    rw [← min_min_of_le (le_of_lt (lt_add_of_pos_right T hδ)), h,
      min_min_of_le (le_of_lt (lt_add_of_pos_right T hδ))]
  change max (uSub x) (min T _) = max (uSub x) (min T (u x))
  rw [hkey, max_min_max, ← hux x]

end GuaranteedSubsol.MaxMinProof
