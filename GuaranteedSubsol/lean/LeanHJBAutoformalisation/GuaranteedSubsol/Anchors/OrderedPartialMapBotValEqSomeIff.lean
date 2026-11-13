/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.OrderedPartialMapProof

/-!
# Frozen statement: `bot` of an ordered partial map returns the smallest entry

Source: Papers/OrderedPartialMap (`OrderedPartialMap.tex`), operation bot (author's request):
`botVal v` (the first component of `bot`) is `(t, x)` iff `v x = t` and `(t, x)` is minimal among
the entries `(t', y)` (`v y = t'`) for the lexicographic order of `V ×ₗ X` (value first, ties
broken by the order of `X`). `X` is finite and linearly ordered, `V` linearly ordered.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol.OrderedPartialMap

theorem botVal_eq_some_iff {X V : Type*} [Fintype X] [LinearOrder X] [LinearOrder V]
    {v : X → Option V} {t : V} {x : X} :
    botVal v = some (t, x) ↔
      v x = some t ∧ ∀ y t', v y = some t' → toLex (t, x) ≤ toLex (t', y) := by
  exact OrderedPartialMapProof.botVal_eq_some_iff

end GuaranteedSubsol.OrderedPartialMap
