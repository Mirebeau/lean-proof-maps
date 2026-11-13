/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.Restriction
public import Mathlib.Data.ENat.Basic

/-!
# Parallel AGSI

The parallel Adaptive Gauss-Seidel Iteration of Algorithm algo:agsi_parallel (AGSI2.tex),
super-solution version, modelled as a step function on a state; the state after `n` passes of
the while loop, started from `v`, is `parallelAgsiRun Φ η v n := (parallelAgsiStep Φ η)^[n] ⟨v, 0⟩`.
Once the stopping criterion `v - Φ v ≤ η` holds, `parallelAgsiStep` leaves `v` unchanged, so
termination of the while loop is the existence of an `n` at which the criterion holds.

The state also records, for each point, the number of updates performed there (author's request),
which is the quantity bounded in Prop. prop:cplx_agsi_parallel.

The sub-solution variant `parallelAgsiSubStep` replaces `v - Φ v` with `Φ v - v`. It is the
super-solution version applied to the reflected operator `v ↦ -Φ (-v)` and to `-v`, with the
resulting map negated back.
-/

@[expose] public section

namespace GuaranteedSubsol

variable {X : Type*}

/-- State of the parallel AGSI (algo:agsi_parallel): the current map `v` and, for each point,
the number `count x` of updates `v(x) ← Φ v(x)` performed so far. -/
structure ParallelAgsiState (X : Type*) where
  v : X → ℝ
  count : X → ℕ

open Classical in
/-- One pass of the parallel AGSI (algo:agsi_parallel, line algoline:agsi_parallel_for),
super-solution version: on `B := {x | v x - Φ v x > η}`, `v(x) ← Φ v(x)` and
`count x ← count x + 1`; elsewhere both are unchanged. -/
noncomputable def parallelAgsiStep (Φ : (X → ℝ) → X → ℝ) (η : ℝ) (s : ParallelAgsiState X) :
    ParallelAgsiState X where
  v := restrictOp Φ {x | η < s.v x - Φ s.v x} s.v
  count x := if η < s.v x - Φ s.v x then s.count x + 1 else s.count x

open Classical in
/-- One pass of the parallel AGSI, sub-solution variant (algo:agsi_parallel, with `v - Φ v`
replaced by `Φ v - v`): on `B := {x | Φ v x - v x > η}`, `v(x) ← Φ v(x)` and
`count x ← count x + 1`; elsewhere both are unchanged. -/
noncomputable def parallelAgsiSubStep (Φ : (X → ℝ) → X → ℝ) (η : ℝ) (s : ParallelAgsiState X) :
    ParallelAgsiState X where
  v := restrictOp Φ {x | η < Φ s.v x - s.v x} s.v
  count x := if η < Φ s.v x - s.v x then s.count x + 1 else s.count x

/-- The state with `v` replaced by `-v` (same counter). -/
def ParallelAgsiState.neg (s : ParallelAgsiState X) : ParallelAgsiState X :=
  ⟨-s.v, s.count⟩

/-- The state of algo:agsi_parallel (super-solution version) after `n` passes, started from `v`
with no updates. -/
noncomputable def parallelAgsiRun (Φ : (X → ℝ) → X → ℝ) (η : ℝ) (v : X → ℝ) (n : ℕ) :
    ParallelAgsiState X :=
  (parallelAgsiStep Φ η)^[n] ⟨v, 0⟩

/-- The state of the sub-solution variant of algo:agsi_parallel after `n` passes, started from `v`
with no updates. -/
noncomputable def parallelAgsiSubRun (Φ : (X → ℝ) → X → ℝ) (η : ℝ) (v : X → ℝ) (n : ℕ) :
    ParallelAgsiState X :=
  (parallelAgsiSubStep Φ η)^[n] ⟨v, 0⟩

open Classical in
/-- Number of passes of algo:agsi_parallel (super-solution version) until its stopping criterion
`v - Φ v ≤ η` holds (`⊤` if it never holds). -/
noncomputable def parallelAgsiPasses (Φ : (X → ℝ) → X → ℝ) (η : ℝ) (v : X → ℝ) : ℕ∞ :=
  if h : ∃ n, ∀ x, (parallelAgsiRun Φ η v n).v x - Φ (parallelAgsiRun Φ η v n).v x ≤ η then
    (Nat.find h : ℕ∞)
  else ⊤

/-- The output of algo:agsi_parallel (super-solution version), started from `v` (meaningful when
the loop exits, i.e. when `parallelAgsiPasses Φ η v < ⊤`). -/
noncomputable def parallelAgsiResult (Φ : (X → ℝ) → X → ℝ) (η : ℝ) (v : X → ℝ) : X → ℝ :=
  (parallelAgsiRun Φ η v (parallelAgsiPasses Φ η v).toNat).v

open Classical in
/-- The number of updates `v(x) ← Φ v(x)` performed at each point by algo:agsi_parallel
(super-solution version) until the loop stops (`⊤` if it never stops). -/
noncomputable def parallelAgsiCount (Φ : (X → ℝ) → X → ℝ) (η : ℝ) (v : X → ℝ) : X → ℕ∞ :=
  fun x => if parallelAgsiPasses Φ η v = ⊤ then ⊤
    else ((parallelAgsiRun Φ η v (parallelAgsiPasses Φ η v).toNat).count x : ℕ∞)

open Classical in
/-- Number of passes of the sub-solution variant of algo:agsi_parallel until its stopping
criterion `Φ v - v ≤ η` holds (`⊤` if it never holds). -/
noncomputable def parallelAgsiSubPasses (Φ : (X → ℝ) → X → ℝ) (η : ℝ) (v : X → ℝ) : ℕ∞ :=
  if h : ∃ n, ∀ x, Φ (parallelAgsiSubRun Φ η v n).v x - (parallelAgsiSubRun Φ η v n).v x ≤ η then
    (Nat.find h : ℕ∞)
  else ⊤

/-- The output of the sub-solution variant of algo:agsi_parallel, started from `v` (meaningful
when the loop exits, i.e. when `parallelAgsiSubPasses Φ η v < ⊤`). -/
noncomputable def parallelAgsiSubResult (Φ : (X → ℝ) → X → ℝ) (η : ℝ) (v : X → ℝ) : X → ℝ :=
  (parallelAgsiSubRun Φ η v (parallelAgsiSubPasses Φ η v).toNat).v

open Classical in
/-- The number of updates `v(x) ← Φ v(x)` performed at each point by the sub-solution variant of
algo:agsi_parallel until the loop stops (`⊤` if it never stops). -/
noncomputable def parallelAgsiSubCount (Φ : (X → ℝ) → X → ℝ) (η : ℝ) (v : X → ℝ) : X → ℕ∞ :=
  fun x => if parallelAgsiSubPasses Φ η v = ⊤ then ⊤
    else ((parallelAgsiSubRun Φ η v (parallelAgsiSubPasses Φ η v).toNat).count x : ℕ∞)

end GuaranteedSubsol
