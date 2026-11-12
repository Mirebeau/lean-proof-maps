/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.WithBot
import Mathlib.Logic.Function.Basic

/-!
# Generalized Dijkstra algorithm

Algorithm algo:Dijkstra (Complexity.tex), modelled as a step function on a state. The map `u` and
the operator `Γ` take values in `ℝ_∞ = WithTop ℝ`. The list `L` is not stored: by
Prop. prop:Dijkstra_correct (eq. eq:Dijkstra_prop) it equals `{(Γ u x, x) | Γ u x < u x}` at each
iteration. As in V1, ties are broken by a linear order on `X`: the selected pair `(t, x)` is
minimal for the lexicographic order. The state also records the number of Dijkstra updates at
each point. The model has no stopping time (the case `T = ∞` of algo:Dijkstra, V1); the stopping
time `T` corresponds to running it on `Γ^{<T}` (`dijkstraCutOp`, `DijkstraHeap.lean`), as in the
proof of Prop. prop:Dijkstra_correct.
-/

namespace GuaranteedSubsol

variable {X : Type*}

/-- State of the generalized Dijkstra algorithm (algo:Dijkstra): the map `u` and the number
`count x` of Dijkstra updates performed at each point. The list `L` is not stored: by
Prop. prop:Dijkstra_correct it equals `{(Γ u x, x) | Γ u x < u x}`. -/
structure DijkstraState (X : Type*) where
  u : X → WithTop ℝ
  count : X → ℕ

/-- Line Dijkstra:accept: `x` is the active point whose pair `(t, x) = (Γ u x, x)` is
minimal for the lexicographic order. -/
def dijkstraSelect [LinearOrder X] (Γ : (X → WithTop ℝ) → X → WithTop ℝ) (u : X → WithTop ℝ)
    (x : X) : Prop :=
  Γ u x < u x ∧ ∀ y, Γ u y < u y → Γ u x < Γ u y ∨ (Γ u x = Γ u y ∧ x ≤ y)

/-- Initialization with the initial guess `u₀` and no updates. -/
def dijkstraInit (u₀ : X → WithTop ℝ) : DijkstraState X := ⟨u₀, 0⟩

open Classical in
/-- One iteration of the while loop of algo:Dijkstra: the Dijkstra update `u(x) ← Γ u(x)` at the
selected point (and `count x ← count x + 1`); if `L` is empty, stay put. -/
noncomputable def dijkstraStep [LinearOrder X] (Γ : (X → WithTop ℝ) → X → WithTop ℝ)
    (s : DijkstraState X) : DijkstraState X :=
  if h : ∃ x, dijkstraSelect Γ s.u x then
    { u := Function.update s.u (Classical.choose h) (Γ s.u (Classical.choose h))
      count := Function.update s.count (Classical.choose h) (s.count (Classical.choose h) + 1) }
  else s

/-- The state of algo:Dijkstra after `n` iterations, started from the initial guess `u₀`. -/
noncomputable def dijkstraRun [LinearOrder X] (Γ : (X → WithTop ℝ) → X → WithTop ℝ)
    (u₀ : X → WithTop ℝ) (n : ℕ) : DijkstraState X :=
  (dijkstraStep Γ)^[n] (dijkstraInit u₀)

end GuaranteedSubsol
