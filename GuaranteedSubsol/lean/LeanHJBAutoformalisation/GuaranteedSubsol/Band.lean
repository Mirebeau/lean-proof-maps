/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import Mathlib.Basic.Real.Basic

/-!
# An operator acting on a band, with frozen values outside

Given an operator `Φ : ℝ^X → ℝ^X`, a subdomain (band) `B ⊆ X` and frozen values `w ∈ ℝ^X`, the
operator `bandOp Φ B w : ℝ^B → ℝ^B` acts on the maps on the subtype `B`: a map `v` on `B` is
extended by `w` outside `B` (`bandExtend B w v`), and `Φ` is evaluated at the points of `B`.

This is how the inner loops (lines anb:while_sub and anb:while_sup) of Algorithm algo:anb act on
the narrow band `B_n`: any algorithm stated for an operator on a finite type (global iteration,
AGSI, ...) can be run on the band. Compared with the restriction `Φ_B` of `Restriction.lean` (the
identity outside `B`), the band operator inherits monotonicity and `ρ`-sub-additivity from `Φ` at
the points of `B`.
-/

@[expose] public section

namespace GuaranteedSubsol

variable {X : Type*}

open Classical in
/-- The map equal to `v` on `B` and to `w` outside `B` (in eq. eqdef:Lambda_B, the map on `X` made
of `w ∈ ℝ^B` and of the boundary data `v ∈ ℝ^{X∖B}`: the letters are swapped). -/
noncomputable def bandExtend (B : Set X) (w : X → ℝ) (v : B → ℝ) : X → ℝ :=
  fun y => if h : y ∈ B then v ⟨y, h⟩ else w y

/-- The operator `Φ` acting on the maps on the band `B`, the values outside `B` being frozen to
`w`: `bandOp Φ B w v x := Φ (bandExtend B w v) x` for `x ∈ B`. This is `Λ_B^v : ℝ^B → ℝ^B` of
eq. eqdef:Lambda_B (right), whose boundary data `v ∈ ℝ^{X∖B}` is here `w` (only its values outside
`B` are used), and whose argument `w ∈ ℝ^B` is here `v`. -/
noncomputable def bandOp (Φ : (X → ℝ) → X → ℝ) (B : Set X) (w : X → ℝ) : (B → ℝ) → B → ℝ :=
  fun v x => Φ (bandExtend B w v) x

theorem bandExtend_of_mem (B : Set X) (w : X → ℝ) (v : B → ℝ) {y : X} (hy : y ∈ B) :
    bandExtend B w v y = v ⟨y, hy⟩ := by
  classical
  simp only [bandExtend, hy, ↓reduceDIte]

theorem bandExtend_of_notMem (B : Set X) (w : X → ℝ) (v : B → ℝ) {y : X} (hy : y ∉ B) :
    bandExtend B w v y = w y := by
  classical
  simp only [bandExtend, hy, ↓reduceDIte]

/-- Extending the restriction of `w` by `w` gives back `w`. -/
theorem bandExtend_restrict (B : Set X) (w : X → ℝ) : bandExtend B w (fun x => w x) = w := by
  funext y
  by_cases hy : y ∈ B
  · rw [bandExtend_of_mem B w _ hy]
  · rw [bandExtend_of_notMem B w _ hy]

end GuaranteedSubsol
