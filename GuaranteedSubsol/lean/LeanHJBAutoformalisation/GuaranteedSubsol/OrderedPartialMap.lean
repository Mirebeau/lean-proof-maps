/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Data.Fintype.Basic

/-!
# Ordered partial maps

A toy model of a sorted container of pairs `(v x, x)` with an operation counter (Papers/
OrderedPartialMap, `OrderedPartialMap.tex`; in C++, `std::set<std::pair<V, X>>`, whose operations
cost `O(ln #X)`): a partial map `v : X → Option V` (the value `none` is the absent value `⋄`) and
the number `count` of elementary operations performed so far. `X` is finite and linearly ordered
(the order only breaks ties), `V` is linearly ordered, and pairs are compared lexicographically,
the value first (`V ×ₗ X`).

Each operation returns its result (if any) together with the updated map:
* `empty`: whether there is no entry; cost `1`;
* `bot`: the smallest entry `(t, x)` (`none` if there is none); cost `1`;
* `set1 x t`: `v x := t` (`t = none` erases `x`); cost `1`;
* `set Y v'`: `v x := v' x` for `x ∈ Y`; cost `#Y`;
* `erase1 x`, `erase Y`: `set1 x none`, `set Y (fun _ => none)`;
* `pop`: the output of `bot`, and the erasure of that entry; cost `2` (`1` if there is no entry);
* `entriesIco Tm Tp`: the points `x` with `Tm ≤ v x < Tp`; cost `1 + #W`, where `W` is the output.
-/

@[expose] public section

namespace GuaranteedSubsol

variable {X V : Type*}

/-- An ordered partial map: the partial map `v` (`none` is absent) and an operation counter. -/
structure OrderedPartialMap (X V : Type*) where
  v : X → Option V
  count : ℕ

namespace OrderedPartialMap

variable [Fintype X] [LinearOrder X] [LinearOrder V]

/-- The entries `(v x, x)`, in the lexicographic order of `V ×ₗ X`. -/
def entries (v : X → Option V) : Finset (V ×ₗ X) :=
  Finset.univ.filterMap (fun x => (v x).map fun t => toLex (t, x)) (by
    intro x x' p hx hx'
    obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨t', -, h⟩ := Option.map_eq_some_iff.1 hx'
    exact (congrArg Prod.snd (toLex.injective h)).symm)

/-- The smallest entry `(t, x)` for the lexicographic order (`none` if there is no entry). -/
def botVal (v : X → Option V) : Option (V × X) := WithTop.map ofLex (entries v).min

/-- Whether there is no entry; cost `1`. -/
def empty (m : OrderedPartialMap X V) : Bool × OrderedPartialMap X V :=
  (decide (∀ x, m.v x = none), ⟨m.v, m.count + 1⟩)

/-- The smallest entry (`none` if there is none); cost `1`. -/
def bot (m : OrderedPartialMap X V) : Option (V × X) × OrderedPartialMap X V :=
  (botVal m.v, ⟨m.v, m.count + 1⟩)

/-- `v x := t` (`t = none` erases `x`); cost `1`. -/
def set1 (m : OrderedPartialMap X V) (x : X) (t : Option V) : OrderedPartialMap X V :=
  ⟨Function.update m.v x t, m.count + 1⟩

/-- `v x := v' x` for `x ∈ Y`; cost `#Y`. -/
def set (m : OrderedPartialMap X V) (Y : Finset X) (v' : X → Option V) :
    OrderedPartialMap X V :=
  ⟨fun x => if x ∈ Y then v' x else m.v x, m.count + Y.card⟩

/-- Erase the entry of `x`; cost `1`. -/
def erase1 (m : OrderedPartialMap X V) (x : X) : OrderedPartialMap X V := m.set1 x none

/-- Erase the entries of the points of `Y`; cost `#Y`. -/
def erase (m : OrderedPartialMap X V) (Y : Finset X) : OrderedPartialMap X V :=
  m.set Y fun _ => none

/-- The smallest entry (`none` if there is none), which is erased; cost `2` (`1` if there is no
entry). -/
def pop (m : OrderedPartialMap X V) : Option (V × X) × OrderedPartialMap X V :=
  match botVal m.v with
  | none => (none, ⟨m.v, m.count + 1⟩)
  | some (t, x) => (some (t, x), ⟨Function.update m.v x none, m.count + 2⟩)

open Classical in
/-- The points `x` whose value satisfies `Tm ≤ v x < Tp` (closed-open interval); cost `1 + #W`,
where `W` is the output. -/
noncomputable def entriesIco (m : OrderedPartialMap X V) (Tm Tp : V) :
    Finset X × OrderedPartialMap X V :=
  let W := Finset.univ.filter fun x => ∃ t, m.v x = some t ∧ Tm ≤ t ∧ t < Tp
  (W, ⟨m.v, m.count + 1 + W.card⟩)

end OrderedPartialMap

end GuaranteedSubsol
