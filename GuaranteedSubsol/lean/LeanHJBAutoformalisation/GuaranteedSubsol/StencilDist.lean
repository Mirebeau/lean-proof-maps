/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Nat.Find

/-!
# Distance to the boundary along the stencils

The graph distance `d_V(x, ∂X)` of the proof of Prop. prop:constr_Gamma (Effective.tex): the
number of edges from `x` to the boundary `∂X = Iᶜ` on the oriented graph defined by the stencils,
`x → y` for `x ∈ I` and `y ∈ V x`.
-/

@[expose] public section

namespace GuaranteedSubsol

variable {X : Type*}

/-- `stencilReach I V n x`: there is a path of `n` stencil edges from `x` to the boundary `Iᶜ`,
`x = x₀ → x₁ → … → xₙ ∉ I`, with `x_{i+1} ∈ V xᵢ` and `xᵢ ∈ I` for `i < n`. -/
def stencilReach (I : Set X) (V : X → Set X) : ℕ → X → Prop
  | 0, x => x ∉ I
  | n + 1, x => x ∈ I ∧ ∃ y ∈ V x, stencilReach I V n y

open Classical in
/-- Number of stencil edges `d_V(x, ∂X)` from `x` to the boundary (`0` if the boundary is
unreachable from `x`). -/
noncomputable def stencilDist (I : Set X) (V : X → Set X) (x : X) : ℕ :=
  if h : ∃ n, stencilReach I V n x then Nat.find h else 0

end GuaranteedSubsol
