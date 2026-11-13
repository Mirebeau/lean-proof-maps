/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Data.ENat.Basic

/-!
# Global iteration

Algorithm algo:global_iteration (Complexity.tex): while the stopping criterion fails, update
`v(x) ← Φ v(x)` at all points simultaneously, i.e. `v ← Φ v`. Super-solution version (criterion
`v - Φ v ≤ η`) and sub-solution variant (criterion `Φ v - v ≤ η`), modelled as step functions
which leave `v` unchanged once the criterion holds; termination of the while loop is the existence
of an `n` at which the criterion holds. Every point is updated at each pass, so the number of
updates at any point is the number of passes. The number of passes takes values in `ℕ∞`: it is
`⊤` when the while loop never exits, so that a bound `passes ≤ N` also expresses termination; the
output is then the junk value obtained after `0` passes.
-/

@[expose] public section

namespace GuaranteedSubsol

variable {X : Type*}

open Classical in
/-- One iteration of algo:global_iteration, super-solution version: `v ← Φ v`, unless the stopping
criterion `v - Φ v ≤ η` holds, in which case `v` is unchanged. -/
noncomputable def globalIterStep (Φ : (X → ℝ) → X → ℝ) (η : ℝ) (v : X → ℝ) : X → ℝ :=
  if ∀ x, v x - Φ v x ≤ η then v else Φ v

open Classical in
/-- One iteration of algo:global_iteration, sub-solution variant: `v ← Φ v`, unless the stopping
criterion `Φ v - v ≤ η` holds, in which case `v` is unchanged. -/
noncomputable def globalIterSubStep (Φ : (X → ℝ) → X → ℝ) (η : ℝ) (v : X → ℝ) : X → ℝ :=
  if ∀ x, Φ v x - v x ≤ η then v else Φ v

/-- The map of algo:global_iteration (super-solution version) after `n` iterations from `v`. -/
noncomputable def globalIterRun (Φ : (X → ℝ) → X → ℝ) (η : ℝ) (v : X → ℝ) (n : ℕ) : X → ℝ :=
  (globalIterStep Φ η)^[n] v

/-- The map of algo:global_iteration (sub-solution variant) after `n` iterations from `v`. -/
noncomputable def globalIterSubRun (Φ : (X → ℝ) → X → ℝ) (η : ℝ) (v : X → ℝ) (n : ℕ) : X → ℝ :=
  (globalIterSubStep Φ η)^[n] v

open Classical in
/-- Number of iterations of algo:global_iteration (super-solution version) until its stopping
criterion holds, i.e. when the while loop exits (`⊤` if it never holds). -/
noncomputable def globalIterPasses (Φ : (X → ℝ) → X → ℝ) (η : ℝ) (v : X → ℝ) : ℕ∞ :=
  if h : ∃ n, ∀ x, globalIterRun Φ η v n x - Φ (globalIterRun Φ η v n) x ≤ η then
    (Nat.find h : ℕ∞)
  else ⊤

/-- The output of algo:global_iteration (super-solution version), started from `v` (meaningful
when the loop exits, i.e. when `globalIterPasses Φ η v < ⊤`). -/
noncomputable def globalIterResult (Φ : (X → ℝ) → X → ℝ) (η : ℝ) (v : X → ℝ) : X → ℝ :=
  globalIterRun Φ η v (globalIterPasses Φ η v).toNat

open Classical in
/-- Number of iterations of algo:global_iteration (sub-solution variant) until its stopping
criterion holds (`⊤` if it never holds). -/
noncomputable def globalIterSubPasses (Φ : (X → ℝ) → X → ℝ) (η : ℝ) (v : X → ℝ) : ℕ∞ :=
  if h : ∃ n, ∀ x, Φ (globalIterSubRun Φ η v n) x - globalIterSubRun Φ η v n x ≤ η then
    (Nat.find h : ℕ∞)
  else ⊤

/-- The output of algo:global_iteration (sub-solution variant), started from `v` (meaningful when
the loop exits, i.e. when `globalIterSubPasses Φ η v < ⊤`). -/
noncomputable def globalIterSubResult (Φ : (X → ℝ) → X → ℝ) (η : ℝ) (v : X → ℝ) : X → ℝ :=
  globalIterSubRun Φ η v (globalIterSubPasses Φ η v).toNat

end GuaranteedSubsol
