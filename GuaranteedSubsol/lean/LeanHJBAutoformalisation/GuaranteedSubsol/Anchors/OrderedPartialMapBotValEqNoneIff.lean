/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.OrderedPartialMapProof

/-!
# Frozen statement: `bot` of an ordered partial map returns nothing iff the map is empty

Source: Papers/OrderedPartialMap (`OrderedPartialMap.tex`), operation bot (author's request):
`botVal v` (the first component of `bot`) is `none` iff `v x = ⋄` (`none`) for all `x`. `X` is
finite and linearly ordered, `V` linearly ordered.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol.OrderedPartialMap

theorem botVal_eq_none_iff {X V : Type*} [Fintype X] [LinearOrder X] [LinearOrder V]
    {v : X → Option V} :
    botVal v = none ↔ ∀ x, v x = none := by
  exact OrderedPartialMapProof.botVal_eq_none_iff

end GuaranteedSubsol.OrderedPartialMap
