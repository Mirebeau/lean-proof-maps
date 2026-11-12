/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.Dijkstra
import LeanHJBAutoformalisation.GuaranteedSubsol.OrderedPartialMap
import LeanHJBAutoformalisation.GuaranteedSubsol.GlobalExt
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ENat.Basic

/-!
# Dijkstra's method with a sorted list

A version of algo:Dijkstra closer to the paper: the list `L` of active pairs is stored in an
ordered partial map (`OrderedPartialMap`, a model of `std::set`), whose key at `y` is `Γ u y` when
`Γ u y < u y`, and absent otherwise (`dijkstraKey`; eq. eq:Dijkstra_prop, right). One iteration,
with the stopping time `T` of algo:Dijkstra (V1):
* `bot` gives the smallest active pair `(t, x)`; if there is none, or if `t ≥ T`, the method stops
  (the state is unchanged, except for the cost of `bot`);
* otherwise `x` is accepted: `u x := t`, the pair is erased, and the keys of the points of the
  reversed stencil `𝒱̃ x` are recomputed (`#𝒱̃ x` evaluations of `Γ`).
The state records the number of acceptances at each point (as `DijkstraState`), the number of
evaluations of `Γ` (`evalCount`), and the operations on `L` (`L.count`). The initial state is
arbitrary (in the ANB, `L` is given); `dijkstraHeapInit` builds `L` from scratch. With `T = ⊤`
this is `dijkstraRun` (algo:Dijkstra with `T = ∞`); with a finite `T`, it is `dijkstraRun` applied
to `Γ^{<T}` (`dijkstraCutOp`), as in the proof of Prop. prop:Dijkstra_correct. The while loop,
which stops at the first unsuccessful test, is `dijkstraHeapLoop`.
-/

namespace GuaranteedSubsol

variable {X : Type*}

/-- The key of `y` in the list `L`: `Γ u y` if `y` is active (`Γ u y < u y`), absent otherwise. -/
noncomputable def dijkstraKey (Γ : (X → WithTop ℝ) → X → WithTop ℝ) (u : X → WithTop ℝ) :
    X → Option (WithTop ℝ) :=
  fun y => if Γ u y < u y then some (Γ u y) else none

/-- The operator `Γ^{<T}`: `Γ u x` if `Γ u x < T`, and `∞` otherwise (for `T = ⊤`, this is `Γ`). -/
noncomputable def dijkstraCutOp (T : WithTop ℝ) (Γ : (X → WithTop ℝ) → X → WithTop ℝ) :
    (X → WithTop ℝ) → X → WithTop ℝ :=
  fun u x => if Γ u x < T then Γ u x else ⊤

/-- State of Dijkstra's method with a sorted list: the map `u`, the number of acceptances at each
point, the list `L` (with its operation counter), and the number of evaluations of `Γ`. -/
structure DijkstraHeapState (X : Type*) where
  u : X → WithTop ℝ
  count : X → ℕ
  L : OrderedPartialMap X (WithTop ℝ)
  evalCount : ℕ

variable [Fintype X] [LinearOrder X]

/-- One iteration of Dijkstra's method with a sorted list, stencil `𝒱` and threshold `T`. -/
noncomputable def dijkstraHeapStep (Γ : (X → WithTop ℝ) → X → WithTop ℝ) (𝒱 : X → Set X)
    (T : WithTop ℝ) (s : DijkstraHeapState X) : DijkstraHeapState X :=
  match s.L.bot with
  | (none, L₁) => { s with L := L₁ }
  | (some (t, x), L₁) =>
    if T ≤ t then { s with L := L₁ }
    else
      let u' := Function.update s.u x t
      { u := u'
        count := Function.update s.count x (s.count x + 1)
        L := (L₁.erase1 x).set (Global.Ext.revStencil 𝒱 x) (dijkstraKey Γ u')
        evalCount := s.evalCount + (Global.Ext.revStencil 𝒱 x).card }

/-- The state after `n` iterations, from the state `s₀`. -/
noncomputable def dijkstraHeapRun (Γ : (X → WithTop ℝ) → X → WithTop ℝ) (𝒱 : X → Set X)
    (T : WithTop ℝ) (s₀ : DijkstraHeapState X) (n : ℕ) : DijkstraHeapState X :=
  (dijkstraHeapStep Γ 𝒱 T)^[n] s₀

/-- Initial state built from scratch: `u₀`, no acceptance, `L` filled with the keys of all the
points (`#X` evaluations of `Γ` and `#X` operations on `L`). -/
noncomputable def dijkstraHeapInit (Γ : (X → WithTop ℝ) → X → WithTop ℝ) (u₀ : X → WithTop ℝ) :
    DijkstraHeapState X :=
  ⟨u₀, 0, (⟨fun _ => none, 0⟩ : OrderedPartialMap X (WithTop ℝ)).set Finset.univ
    (dijkstraKey Γ u₀), Fintype.card X⟩

/-- Whether Dijkstra's method with a sorted list and threshold `T` stops at the state `s`: the list
`L` is empty, or its smallest key is `≥ T`. -/
def DijkstraHeapState.Stopped (T : WithTop ℝ) (s : DijkstraHeapState X) : Prop :=
  ∀ t x, OrderedPartialMap.botVal s.L.v = some (t, x) → T ≤ t

open Classical in
/-- The number of acceptances before Dijkstra's method with a sorted list stops, from the state `s₀`
(`⊤` if it never stops). -/
noncomputable def dijkstraHeapStopIndex (Γ : (X → WithTop ℝ) → X → WithTop ℝ) (𝒱 : X → Set X)
    (T : WithTop ℝ) (s₀ : DijkstraHeapState X) : ℕ∞ :=
  if h : ∃ n, (dijkstraHeapRun Γ 𝒱 T s₀ n).Stopped T then Nat.find h else ⊤

/-- The while loop of algo:Dijkstra with a sorted list and threshold `T`, from the state `s₀`: the
acceptances, then the final test (one more call to `bot`, which finds the list empty or its
smallest key `≥ T`). Meaningful when the stop index is finite. -/
noncomputable def dijkstraHeapLoop (Γ : (X → WithTop ℝ) → X → WithTop ℝ) (𝒱 : X → Set X)
    (T : WithTop ℝ) (s₀ : DijkstraHeapState X) : DijkstraHeapState X :=
  dijkstraHeapRun Γ 𝒱 T s₀ ((dijkstraHeapStopIndex Γ 𝒱 T s₀).toNat + 1)

end GuaranteedSubsol
