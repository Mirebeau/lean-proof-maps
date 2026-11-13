/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.OrderedPartialMap

/-!
# Ordered partial maps: specification of the operations

For each operation of `OrderedPartialMap`, its result (or its effect on the partial map) and its
cost (the increase of the counter). Provider proofs for the frozen anchors
`GuaranteedSubsol.OrderedPartialMap.botVal_eq_none_iff`, `…botVal_eq_some_iff` and
`…entriesIco_fst`, see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol.OrderedPartialMapProof

open OrderedPartialMap

variable {X V : Type*}

theorem mem_entries [Fintype X] {v : X → Option V} {t : V} {x : X} :
    toLex (t, x) ∈ entries v ↔ v x = some t := by
  unfold entries
  rw [Finset.mem_filterMap]
  constructor
  · rintro ⟨y, -, hy⟩
    rw [Option.map_eq_some_iff] at hy
    obtain ⟨t', hy, h⟩ := hy
    have h' := toLex.injective h
    simp only [Prod.mk.injEq] at h'
    rw [← h'.2, hy, h'.1]
  · intro h
    exact ⟨x, Finset.mem_univ x, by rw [h]; rfl⟩

/-- `bot` returns `none` iff there is no entry. -/
theorem botVal_eq_none_iff [Fintype X] [LinearOrder X] [LinearOrder V] {v : X → Option V} :
    botVal v = none ↔ ∀ x, v x = none := by
  change WithTop.map ofLex (entries v).min = ⊤ ↔ _
  rw [WithTop.map_eq_top_iff, Finset.min_eq_top, Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h x
    by_contra hx
    obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.1 hx
    exact h _ (mem_entries.2 ht)
  · intro h p hp
    have hp' : toLex ((ofLex p).1, (ofLex p).2) ∈ entries v := hp
    rw [mem_entries, h] at hp'
    simp at hp'

/-- When `bot` returns `(t, x)`, then `v x = t` and `(t, x)` is lexicographically minimal. -/
theorem botVal_eq_some [Fintype X] [LinearOrder X] [LinearOrder V] {v : X → Option V} {t : V}
    {x : X} (h : botVal v = some (t, x)) :
    v x = some t ∧ ∀ y t', v y = some t' → toLex (t, x) ≤ toLex (t', y) := by
  change WithTop.map ofLex (entries v).min = (((t, x) : V × X) : WithTop (V × X)) at h
  rcases hm : (entries v).min with _ | p
  · rw [hm] at h
    exact absurd h WithTop.top_ne_coe
  have hmin : (entries v).min = (p : WithTop (V ×ₗ X)) := hm
  rw [hm] at h
  have hpx : ofLex p = (t, x) := WithTop.coe_inj.1 h
  have hmem : p ∈ entries v := Finset.mem_of_min hmin
  have hp' : p = toLex (t, x) := by rw [← hpx]; rfl
  rw [hp'] at hmem hmin
  refine ⟨mem_entries.1 hmem, fun y t' hy => ?_⟩
  exact Finset.min_le_of_eq (mem_entries.2 hy) hmin

/-- `bot` returns `(t, x)` iff `v x = t` and `(t, x)` is lexicographically minimal among the
entries. -/
theorem botVal_eq_some_iff [Fintype X] [LinearOrder X] [LinearOrder V] {v : X → Option V}
    {t : V} {x : X} :
    botVal v = some (t, x) ↔
      v x = some t ∧ ∀ y t', v y = some t' → toLex (t, x) ≤ toLex (t', y) := by
  refine ⟨botVal_eq_some, fun ⟨hx, hmin⟩ => ?_⟩
  rcases hb : botVal v with _ | ⟨t', x'⟩
  · rw [botVal_eq_none_iff.1 hb x] at hx
    exact absurd hx (by simp)
  · obtain ⟨hx', hmin'⟩ := botVal_eq_some hb
    have h := le_antisymm (hmin x' t' hx') (hmin' x t hx)
    rw [toLex.injective h]

variable (m : OrderedPartialMap X V)

theorem empty_fst [Fintype X] : m.empty.1 = decide (∀ x, m.v x = none) := rfl
theorem empty_snd [Fintype X] : m.empty.2 = ⟨m.v, m.count + 1⟩ := rfl
theorem bot_fst [Fintype X] [LinearOrder X] [LinearOrder V] : m.bot.1 = botVal m.v := rfl
theorem bot_snd [Fintype X] [LinearOrder X] [LinearOrder V] : m.bot.2 = ⟨m.v, m.count + 1⟩ :=
  rfl
theorem set1_v [LinearOrder X] (x : X) (t : Option V) :
    (m.set1 x t).v = Function.update m.v x t := rfl
theorem set1_count [LinearOrder X] (x : X) (t : Option V) : (m.set1 x t).count = m.count + 1 :=
  rfl
theorem set_v [LinearOrder X] (Y : Finset X) (v' : X → Option V) :
    (m.set Y v').v = fun x => if x ∈ Y then v' x else m.v x := rfl
theorem set_count [LinearOrder X] (Y : Finset X) (v' : X → Option V) :
    (m.set Y v').count = m.count + Y.card := rfl
theorem erase1_v [LinearOrder X] (x : X) : (m.erase1 x).v = Function.update m.v x none :=
  rfl
theorem erase1_count [LinearOrder X] (x : X) : (m.erase1 x).count = m.count + 1 := rfl
theorem erase_v [LinearOrder X] (Y : Finset X) :
    (m.erase Y).v = fun x => if x ∈ Y then none else m.v x := rfl
theorem erase_count [LinearOrder X] (Y : Finset X) : (m.erase Y).count = m.count + Y.card := rfl

theorem pop_of_none [Fintype X] [LinearOrder X] [LinearOrder V] (h : botVal m.v = none) :
    m.pop = (none, ⟨m.v, m.count + 1⟩) := by
  unfold pop
  rw [h]

theorem pop_of_some [Fintype X] [LinearOrder X] [LinearOrder V] {t : V} {x : X}
    (h : botVal m.v = some (t, x)) :
    m.pop = (some (t, x), ⟨Function.update m.v x none, m.count + 2⟩) := by
  unfold pop
  rw [h]

theorem entriesIco_fst [Fintype X] [LinearOrder V] (Tm Tp : V) (x : X) :
    x ∈ (m.entriesIco Tm Tp).1 ↔ ∃ t, m.v x = some t ∧ Tm ≤ t ∧ t < Tp := by
  simp [entriesIco]

theorem entriesIco_snd [Fintype X] [LinearOrder V] (Tm Tp : V) :
    (m.entriesIco Tm Tp).2 = ⟨m.v, m.count + 1 + (m.entriesIco Tm Tp).1.card⟩ := rfl

end GuaranteedSubsol.OrderedPartialMapProof
