/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.OrderedPartialMapProof

/-!
# Frozen statement: `entriesIco` of an ordered partial map returns the entries in `[Tm, Tp)`

Source: Papers/OrderedPartialMap (`OrderedPartialMap.tex`), operation range, named `entriesIco`
following Mathlib's naming of intervals (author's request): its output is the set of points `x`
with an entry `v x = t` such that `Tm ≤ t < Tp`. `X` is finite, `V` linearly ordered.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol.OrderedPartialMap

theorem entriesIco_fst {X V : Type*} [Fintype X] [LinearOrder V] (m : OrderedPartialMap X V)
    (Tm Tp : V) (x : X) :
    x ∈ (m.entriesIco Tm Tp).1 ↔ ∃ t, m.v x = some t ∧ Tm ≤ t ∧ t < Tp := by
  exact OrderedPartialMapProof.entriesIco_fst m Tm Tp x

end GuaranteedSubsol.OrderedPartialMap
