/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.DijkstraHeap
public import LeanHJBAutoformalisation.GuaranteedSubsol.OrderedPartialMapProof
public import LeanHJBAutoformalisation.GuaranteedSubsol.DijkstraProof

/-!
# Dijkstra's method with a sorted list: proof

Provider proofs for the frozen anchors `GuaranteedSubsol.dijkstraHeapRun_eq` and
`GuaranteedSubsol.dijkstraHeapInit_run_eq`, see `ANCHORS.md`. As long as the list `L` holds the keys
of the active points (`L.v = dijkstraKey Γ u`), one iteration of the method with threshold `T`
coincides with one iteration of algo:Dijkstra applied to `Γ^{<T}` (`step_spec`):
* `bot` returns the lexicographically smallest active pair `(Γ u x, x)`; if there is none, or if
  `Γ u x ≥ T`, no point is active for `Γ^{<T}`;
* otherwise `x` is the point selected by algo:Dijkstra for `Γ^{<T}` (selection is unique), and the
  keys remain correct: they are recomputed on `𝒱̃ x`, and elsewhere they do not change, by the
  stencil property (the key of `x` itself becomes absent, since `Γ u' x = Γ u x = u' x`).
The costs follow: `1` for a step that stops, `2 + #𝒱̃ x` operations on `L` and `#𝒱̃ x`
evaluations of `Γ` for a step that accepts `x`.
-/

@[expose] public section

namespace GuaranteedSubsol.DijkstraHeapProof

open OrderedPartialMap OrderedPartialMapProof

variable {X : Type*}

/-- The selected point of algo:Dijkstra is unique. -/
theorem select_unique [LinearOrder X] {Γ : (X → WithTop ℝ) → X → WithTop ℝ}
    {u : X → WithTop ℝ} {x x' : X} (h : dijkstraSelect Γ u x) (h' : dijkstraSelect Γ u x') :
    x = x' := by
  rcases h.2 x' h'.1 with h1 | ⟨h1, h2⟩ <;> rcases h'.2 x h.1 with h3 | ⟨h3, h4⟩
  · exact absurd (h1.trans h3) (lt_irrefl _)
  · exact absurd h1 (h3 ▸ lt_irrefl _)
  · exact absurd h3 (h1 ▸ lt_irrefl _)
  · exact le_antisymm h2 h4

theorem dijkstraCutOp_top (Γ : (X → WithTop ℝ) → X → WithTop ℝ) : dijkstraCutOp ⊤ Γ = Γ := by
  funext u x
  unfold dijkstraCutOp
  split_ifs with h
  · rfl
  · exact (not_lt_top_iff.1 h).symm

theorem mem_revStencil [Fintype X] {𝒱 : X → Set X} {x y : X} :
    y ∈ Global.Ext.revStencil 𝒱 x ↔ x ∈ 𝒱 y := by
  classical
  simp [Global.Ext.revStencil]

/-- Weighted sum after one more acceptance at `x`. -/
theorem sum_update_mul [Fintype X] [DecidableEq X] (c w : X → ℕ) (x : X) :
    ∑ y, Function.update c x (c x + 1) y * w y = ∑ y, c y * w y + w x := by
  have h : ∀ y, Function.update c x (c x + 1) y * w y = c y * w y + if y = x then w y else 0 :=
    fun y => by
      by_cases hy : y = x
      · subst hy; simp [add_mul]
      · simp [hy]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

variable [Fintype X] [LinearOrder X] {Γ : (X → WithTop ℝ) → X → WithTop ℝ} {𝒱 : X → Set X}

/-- One iteration: either both methods stop, or both accept the same point `x`, with value
`Γ u x`. -/
theorem step_spec (hst : Global.Ext.HasStencil 𝒱 Γ) (T : WithTop ℝ) (s : DijkstraHeapState X)
    (hL : s.L.v = dijkstraKey Γ s.u) (c : X → ℕ) :
    (dijkstraStep (dijkstraCutOp T Γ) ⟨s.u, c⟩ = ⟨s.u, c⟩ ∧
      dijkstraHeapStep Γ 𝒱 T s = { s with L := ⟨s.L.v, s.L.count + 1⟩ }) ∨
    ∃ x, dijkstraStep (dijkstraCutOp T Γ) ⟨s.u, c⟩ =
        ⟨Function.update s.u x (Γ s.u x), Function.update c x (c x + 1)⟩ ∧
      (dijkstraHeapStep Γ 𝒱 T s).u = Function.update s.u x (Γ s.u x) ∧
      (dijkstraHeapStep Γ 𝒱 T s).count = Function.update s.count x (s.count x + 1) ∧
      (dijkstraHeapStep Γ 𝒱 T s).L.v = dijkstraKey Γ (dijkstraHeapStep Γ 𝒱 T s).u ∧
      (dijkstraHeapStep Γ 𝒱 T s).L.count =
        s.L.count + 2 + (Global.Ext.revStencil 𝒱 x).card ∧
      (dijkstraHeapStep Γ 𝒱 T s).evalCount =
        s.evalCount + (Global.Ext.revStencil 𝒱 x).card := by
  classical
  have hkey : ∀ y, s.L.v y = dijkstraKey Γ s.u y := fun y => congrFun hL y
  -- the active points of `Γ^{<T}` are those of `Γ` with key below `T`
  have hact : ∀ y, dijkstraCutOp T Γ s.u y < s.u y ↔ Γ s.u y < T ∧ Γ s.u y < s.u y := fun y => by
    unfold dijkstraCutOp
    split_ifs with h
    · exact ⟨fun h' => ⟨h, h'⟩, fun h' => h'.2⟩
    · exact ⟨fun h' => absurd h' (not_lt.2 le_top), fun h' => absurd h'.1 h⟩
  rcases hb : botVal s.L.v with _ | ⟨t, x⟩
  · -- no active point
    left
    have hnone := botVal_eq_none_iff.1 hb
    have hno : ¬∃ x, dijkstraSelect (dijkstraCutOp T Γ) s.u x := by
      rintro ⟨y, hy, -⟩
      have := hkey y
      rw [hnone y] at this
      unfold dijkstraKey at this
      simp only [((hact y).1 hy).2, ↓reduceIte] at this
      exact absurd this (by simp)
    refine ⟨DijkstraProof.step_of_not_select _ hno, ?_⟩
    unfold dijkstraHeapStep
    simp only [OrderedPartialMap.bot, hb]
  · obtain ⟨hx, hmin⟩ := botVal_eq_some hb
    have hkx := hkey x
    rw [hx] at hkx
    unfold dijkstraKey at hkx
    split_ifs at hkx with hxa
    have ht : Γ s.u x = t := (Option.some_injective _ hkx).symm
    by_cases hT : T ≤ t
    · -- the smallest key is above the threshold
      left
      have hno : ¬∃ x, dijkstraSelect (dijkstraCutOp T Γ) s.u x := by
        rintro ⟨y, hy, -⟩
        obtain ⟨hyT, hya⟩ := (hact y).1 hy
        have hky : s.L.v y = some (Γ s.u y) := by
          rw [hkey y]; unfold dijkstraKey; simp only [hya, ↓reduceIte]
        have hle := hmin y _ hky
        rw [Prod.Lex.toLex_le_toLex] at hle
        rcases hle with hlt | ⟨heq, -⟩
        · exact absurd (hT.trans hlt.le) (not_le.2 hyT)
        · have heq' : t = Γ s.u y := heq
          exact absurd (heq' ▸ hT) (not_le.2 hyT)
      refine ⟨DijkstraProof.step_of_not_select _ hno, ?_⟩
      unfold dijkstraHeapStep
      simp only [OrderedPartialMap.bot, hb, hT, ↓reduceIte]
    · -- `x` is accepted
      right
      have hxT : Γ s.u x < T := ht ▸ not_le.1 hT
      have hcx : dijkstraCutOp T Γ s.u x = Γ s.u x := by
        unfold dijkstraCutOp; simp only [hxT, ↓reduceIte]
      have hsel : dijkstraSelect (dijkstraCutOp T Γ) s.u x := by
        refine ⟨hcx ▸ hxa, fun y hy => ?_⟩
        obtain ⟨hyT, hya⟩ := (hact y).1 hy
        have hcy : dijkstraCutOp T Γ s.u y = Γ s.u y := by
          unfold dijkstraCutOp; simp only [hyT, ↓reduceIte]
        have hky : s.L.v y = some (Γ s.u y) := by
          rw [hkey y]; unfold dijkstraKey; simp only [hya, ↓reduceIte]
        have hle := hmin y _ hky
        rw [Prod.Lex.toLex_le_toLex, ← ht] at hle
        rw [hcx, hcy]
        exact hle
      obtain ⟨x', hx', hstep⟩ := DijkstraProof.step_of_select (Γ := dijkstraCutOp T Γ)
        ⟨s.u, c⟩ ⟨x, hsel⟩
      have hxx' : x' = x := select_unique hx' hsel
      subst hxx'
      have hstep' : dijkstraHeapStep Γ 𝒱 T s =
          { u := Function.update s.u x' t
            count := Function.update s.count x' (s.count x' + 1)
            L := ((⟨s.L.v, s.L.count + 1⟩ : OrderedPartialMap X (WithTop ℝ)).erase1 x').set
              (Global.Ext.revStencil 𝒱 x') (dijkstraKey Γ (Function.update s.u x' t))
            evalCount := s.evalCount + (Global.Ext.revStencil 𝒱 x').card } := by
        unfold dijkstraHeapStep
        simp only [OrderedPartialMap.bot, hb, hT, ↓reduceIte]
      refine ⟨x', by rw [hstep, hcx], by rw [hstep', ht], by rw [hstep'], ?_, ?_, by rw [hstep']⟩
      · rw [hstep']
        funext y
        simp only [set_v, erase1_v]
        by_cases hy : y ∈ Global.Ext.revStencil 𝒱 x'
        · simp only [hy, ↓reduceIte]
        · simp only [hy, ↓reduceIte]
          have hxy : x' ∉ 𝒱 y := fun h => hy (mem_revStencil.2 h)
          have hΓ : Γ (Function.update s.u x' t) y = Γ s.u y :=
            hst y _ _ fun z hz => Function.update_of_ne (fun h : z = x' => hxy (h ▸ hz)) _ _
          by_cases hyx : y = x'
          · subst hyx
            rw [Function.update_self]
            unfold dijkstraKey
            rw [hΓ, Function.update_self, ht]
            simp
          · rw [Function.update_of_ne hyx, hkey y]
            unfold dijkstraKey
            rw [hΓ, Function.update_of_ne hyx]
      · rw [hstep']
        simp only [set_count, erase1_count]

omit [Fintype X] in
theorem dijkstraRun_succ' (G : (X → WithTop ℝ) → X → WithTop ℝ) (u₀ : X → WithTop ℝ) (n : ℕ) :
    dijkstraRun G u₀ (n + 1) = dijkstraStep G (dijkstraRun G u₀ n) :=
  Function.iterate_succ_apply' _ _ _

theorem heapRun_succ (T : WithTop ℝ) (s₀ : DijkstraHeapState X) (n : ℕ) :
    dijkstraHeapRun Γ 𝒱 T s₀ (n + 1) = dijkstraHeapStep Γ 𝒱 T (dijkstraHeapRun Γ 𝒱 T s₀ n) :=
  Function.iterate_succ_apply' _ _ _

/-- The method with a sorted list follows algo:Dijkstra applied to `Γ^{<T}`, with the costs. -/
theorem run_spec (hst : Global.Ext.HasStencil 𝒱 Γ) (T : WithTop ℝ) (s₀ : DijkstraHeapState X)
    (hL : s₀.L.v = dijkstraKey Γ s₀.u) (n : ℕ) :
    (dijkstraHeapRun Γ 𝒱 T s₀ n).u = (dijkstraRun (dijkstraCutOp T Γ) s₀.u n).u ∧
    (dijkstraHeapRun Γ 𝒱 T s₀ n).count =
      s₀.count + (dijkstraRun (dijkstraCutOp T Γ) s₀.u n).count ∧
    (dijkstraHeapRun Γ 𝒱 T s₀ n).L.v = dijkstraKey Γ (dijkstraHeapRun Γ 𝒱 T s₀ n).u ∧
    (dijkstraHeapRun Γ 𝒱 T s₀ n).evalCount = s₀.evalCount +
      ∑ x, (dijkstraRun (dijkstraCutOp T Γ) s₀.u n).count x * (Global.Ext.revStencil 𝒱 x).card ∧
    (dijkstraHeapRun Γ 𝒱 T s₀ n).L.count = s₀.L.count + n +
      ∑ x, (dijkstraRun (dijkstraCutOp T Γ) s₀.u n).count x *
        (1 + (Global.Ext.revStencil 𝒱 x).card) := by
  classical
  induction n with
  | zero =>
    refine ⟨rfl, ?_, hL, ?_, ?_⟩
    · change s₀.count = s₀.count + 0
      rw [add_zero]
    · change s₀.evalCount = s₀.evalCount + ∑ x, (0 : X → ℕ) x * _
      simp
    · change s₀.L.count = s₀.L.count + 0 + ∑ x, (0 : X → ℕ) x * _
      simp
  | succ n ih =>
    obtain ⟨hu, hc, hLv, he, hLc⟩ := ih
    rw [heapRun_succ, dijkstraRun_succ']
    set s := dijkstraHeapRun Γ 𝒱 T s₀ n with hs
    set d := dijkstraRun (dijkstraCutOp T Γ) s₀.u n with hd
    have hd' : d = ⟨s.u, d.count⟩ := by rw [hu]
    rw [hd']
    rcases step_spec hst T s hLv d.count with ⟨h1, h2⟩ | ⟨x, h1, h2, h3, h4, h5, h6⟩
    · rw [h1, h2]
      dsimp only
      refine ⟨rfl, hc, hLv, he, ?_⟩
      rw [hLc]
      omega
    · rw [h1]
      dsimp only
      refine ⟨h2, ?_, h4, ?_, ?_⟩
      · rw [h3, hc]
        funext y
        by_cases hy : y = x
        · subst hy; simp only [Function.update_self, Pi.add_apply]; omega
        · simp [Function.update_of_ne hy]
      · change _ = s₀.evalCount + ∑ y, Function.update d.count x (d.count x + 1) y * _
        rw [h6, he, sum_update_mul]
        omega
      · change _ = s₀.L.count + (n + 1) +
          ∑ y, Function.update d.count x (d.count x + 1) y * _
        rw [h5, hLc, sum_update_mul]
        omega

/-- Built from scratch, with no threshold, the method with a sorted list follows algo:Dijkstra, with
`#X` initial evaluations of `Γ` and operations on `L`. -/
theorem init_run_spec (hst : Global.Ext.HasStencil 𝒱 Γ) (u₀ : X → WithTop ℝ) (n : ℕ) :
    (dijkstraHeapRun Γ 𝒱 ⊤ (dijkstraHeapInit Γ u₀) n).u = (dijkstraRun Γ u₀ n).u ∧
    (dijkstraHeapRun Γ 𝒱 ⊤ (dijkstraHeapInit Γ u₀) n).count = (dijkstraRun Γ u₀ n).count ∧
    (dijkstraHeapRun Γ 𝒱 ⊤ (dijkstraHeapInit Γ u₀) n).L.v =
      dijkstraKey Γ (dijkstraHeapRun Γ 𝒱 ⊤ (dijkstraHeapInit Γ u₀) n).u ∧
    (dijkstraHeapRun Γ 𝒱 ⊤ (dijkstraHeapInit Γ u₀) n).evalCount = Fintype.card X +
      ∑ x, (dijkstraRun Γ u₀ n).count x * (Global.Ext.revStencil 𝒱 x).card ∧
    (dijkstraHeapRun Γ 𝒱 ⊤ (dijkstraHeapInit Γ u₀) n).L.count = Fintype.card X + n +
      ∑ x, (dijkstraRun Γ u₀ n).count x * (1 + (Global.Ext.revStencil 𝒱 x).card) := by
  classical
  have hL : (dijkstraHeapInit Γ u₀).L.v = dijkstraKey Γ (dijkstraHeapInit Γ u₀).u := by
    change (fun x => if x ∈ Finset.univ then dijkstraKey Γ u₀ x else none) = dijkstraKey Γ u₀
    simp
  have h := run_spec hst ⊤ (dijkstraHeapInit Γ u₀) hL n
  rw [dijkstraCutOp_top] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, ?_, h3, h4, ?_⟩
  · rw [h2]
    change 0 + _ = _
    rw [zero_add]
    rfl
  · rw [h5]
    change 0 + Finset.univ.card + n + _ = _
    rw [zero_add, Finset.card_univ]
    rfl

/-! ### The while loop -/

omit [Fintype X] in
/-- A run of algo:Dijkstra without active point stays put. -/
theorem dijkstraRun_stay (G : (X → WithTop ℝ) → X → WithTop ℝ) (u₀ : X → WithTop ℝ) {m : ℕ}
    (h : ∀ y, ¬G (dijkstraRun G u₀ m).u y < (dijkstraRun G u₀ m).u y) (j : ℕ) :
    dijkstraRun G u₀ (m + j) = dijkstraRun G u₀ m := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← add_assoc, dijkstraRun_succ', ih]
    exact DijkstraProof.step_of_not_select _ fun ⟨y, hy⟩ => h y hy.1

omit [Fintype X] in
theorem dijkstraRun_stay_of_le (G : (X → WithTop ℝ) → X → WithTop ℝ) (u₀ : X → WithTop ℝ)
    {m n : ℕ} (h : ∀ y, ¬G (dijkstraRun G u₀ m).u y < (dijkstraRun G u₀ m).u y) (hmn : m ≤ n) :
    dijkstraRun G u₀ n = dijkstraRun G u₀ m := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact dijkstraRun_stay G u₀ h j

/-- With a correct list, the method stops iff algo:Dijkstra for `Γ^{<T}` has no active point. -/
theorem stopped_iff (T : WithTop ℝ) (s : DijkstraHeapState X) (hL : s.L.v = dijkstraKey Γ s.u) :
    s.Stopped T ↔ ∀ y, ¬dijkstraCutOp T Γ s.u y < s.u y := by
  have hact : ∀ y, dijkstraCutOp T Γ s.u y < s.u y ↔ Γ s.u y < T ∧ Γ s.u y < s.u y := fun y => by
    unfold dijkstraCutOp
    split_ifs with h
    · exact ⟨fun h' => ⟨h, h'⟩, fun h' => h'.2⟩
    · exact ⟨fun h' => absurd h' (not_lt.2 le_top), fun h' => absurd h'.1 h⟩
  have hkey : ∀ y, Γ s.u y < s.u y → s.L.v y = some (Γ s.u y) := fun y hy => by
    rw [hL]; unfold dijkstraKey; simp only [hy, ↓reduceIte]
  constructor
  · intro hs y hy
    obtain ⟨hyT, hya⟩ := (hact y).1 hy
    rcases hb : botVal s.L.v with _ | ⟨t, x⟩
    · have := (botVal_eq_none_iff.1 hb) y
      rw [hkey y hya] at this
      exact absurd this (by simp)
    · have hle := (botVal_eq_some hb).2 y _ (hkey y hya)
      rw [Prod.Lex.toLex_le_toLex] at hle
      have htT := hs t x hb
      rcases hle with hlt | ⟨heq, -⟩
      · exact absurd (htT.trans hlt.le) (not_le.2 hyT)
      · have heq' : t = Γ s.u y := heq
        exact absurd (heq' ▸ htT) (not_le.2 hyT)
  · intro h t x hb
    obtain ⟨hx, -⟩ := botVal_eq_some hb
    rw [hL] at hx
    unfold dijkstraKey at hx
    split_ifs at hx with hxa
    have ht : Γ s.u x = t := Option.some_injective _ hx
    by_contra hT
    exact h x ((hact x).2 ⟨ht ▸ not_le.1 hT, hxa⟩)

/-- If algo:Dijkstra for `Γ^{<T}` has no active point after `N` steps, the while loop stops after
`m ≤ N` acceptances, one per step of algo:Dijkstra (`m = ∑ₓ count(x)`), and then follows
algo:Dijkstra after `N` steps, with `m + 1` calls to `bot`. -/
theorem loop_spec (hst : Global.Ext.HasStencil 𝒱 Γ) (T : WithTop ℝ) (s₀ : DijkstraHeapState X)
    (hL : s₀.L.v = dijkstraKey Γ s₀.u) (N : ℕ)
    (hN : ∀ y, ¬dijkstraCutOp T Γ (dijkstraRun (dijkstraCutOp T Γ) s₀.u N).u y <
      (dijkstraRun (dijkstraCutOp T Γ) s₀.u N).u y) :
    dijkstraHeapStopIndex Γ 𝒱 T s₀ ≤ N ∧
    dijkstraHeapStopIndex Γ 𝒱 T s₀ =
      ((∑ x, (dijkstraRun (dijkstraCutOp T Γ) s₀.u N).count x : ℕ) : ℕ∞) ∧
    (dijkstraHeapLoop Γ 𝒱 T s₀).u = (dijkstraRun (dijkstraCutOp T Γ) s₀.u N).u ∧
    (dijkstraHeapLoop Γ 𝒱 T s₀).count =
      s₀.count + (dijkstraRun (dijkstraCutOp T Γ) s₀.u N).count ∧
    (dijkstraHeapLoop Γ 𝒱 T s₀).L.v = dijkstraKey Γ (dijkstraHeapLoop Γ 𝒱 T s₀).u ∧
    (dijkstraHeapLoop Γ 𝒱 T s₀).evalCount = s₀.evalCount +
      ∑ x, (dijkstraRun (dijkstraCutOp T Γ) s₀.u N).count x * (Global.Ext.revStencil 𝒱 x).card ∧
    (dijkstraHeapLoop Γ 𝒱 T s₀).L.count = s₀.L.count +
      ∑ x, (dijkstraRun (dijkstraCutOp T Γ) s₀.u N).count x + 1 +
      ∑ x, (dijkstraRun (dijkstraCutOp T Γ) s₀.u N).count x *
        (1 + (Global.Ext.revStencil 𝒱 x).card) := by
  classical
  set G := dijkstraCutOp T Γ with hG
  have hstop : ∀ n, (dijkstraHeapRun Γ 𝒱 T s₀ n).Stopped T ↔
      ∀ y, ¬G (dijkstraRun G s₀.u n).u y < (dijkstraRun G s₀.u n).u y := fun n => by
    obtain ⟨hu, -, hLv, -⟩ := run_spec hst T s₀ hL n
    rw [stopped_iff T _ hLv, hu]
  have hex : ∃ n, (dijkstraHeapRun Γ 𝒱 T s₀ n).Stopped T := ⟨N, (hstop N).2 hN⟩
  set m := Nat.find hex with hm'
  have hm : dijkstraHeapStopIndex Γ 𝒱 T s₀ = m := by
    unfold dijkstraHeapStopIndex; simp only [hex, ↓reduceDIte, hm']
  have hmN : m ≤ N := hm' ▸ Nat.find_min' hex ((hstop N).2 hN)
  have hmstop : ∀ y, ¬G (dijkstraRun G s₀.u m).u y < (dijkstraRun G s₀.u m).u y :=
    (hstop m).1 (hm' ▸ Nat.find_spec hex)
  have hNm : dijkstraRun G s₀.u N = dijkstraRun G s₀.u m := dijkstraRun_stay_of_le G _ hmstop hmN
  have hm1 : dijkstraRun G s₀.u (m + 1) = dijkstraRun G s₀.u m := dijkstraRun_stay G _ hmstop 1
  -- before `m`, each step accepts a point
  have hsum : ∀ j ≤ m, ∑ x, (dijkstraRun G s₀.u j).count x = j := by
    intro j hj
    induction j with
    | zero => simp [dijkstraRun, dijkstraInit]
    | succ j ih =>
      have hjm : j < m := hj
      have hnot : ¬(dijkstraHeapRun Γ 𝒱 T s₀ j).Stopped T := by
        rw [hm'] at hjm; exact Nat.find_min hex hjm
      rw [hstop j] at hnot
      simp only [not_forall, not_not] at hnot
      obtain ⟨x, hx, hstep⟩ := DijkstraProof.step_of_select _ (DijkstraProof.exists_select hnot)
      rw [dijkstraRun_succ', hstep]
      dsimp only
      rw [DijkstraProof.sum_update_succ, ih hjm.le]
  obtain ⟨hu, hc, hLv, he, hLc⟩ := run_spec hst T s₀ hL (m + 1)
  rw [hm1] at hu hc he hLc
  unfold dijkstraHeapLoop
  rw [hm, ENat.toNat_natCast, hNm]
  refine ⟨Nat.cast_le.2 hmN, by rw [hsum m le_rfl], hu, hc, hLv, he, ?_⟩
  rw [hLc, hsum m le_rfl]; omega

/-- If the method has stopped, the loop only calls `bot` once. -/
theorem loop_of_stopped (T : WithTop ℝ) (s₀ : DijkstraHeapState X) (h : s₀.Stopped T) :
    dijkstraHeapLoop Γ 𝒱 T s₀ = { s₀ with L := ⟨s₀.L.v, s₀.L.count + 1⟩ } := by
  classical
  have hex : ∃ n, (dijkstraHeapRun Γ 𝒱 T s₀ n).Stopped T := ⟨0, h⟩
  have h0 : (dijkstraHeapStopIndex Γ 𝒱 T s₀).toNat = 0 := by
    unfold dijkstraHeapStopIndex
    simp only [hex, ↓reduceDIte, ENat.toNat_natCast, Nat.find_eq_zero]
    exact h
  unfold dijkstraHeapLoop
  rw [h0]
  change dijkstraHeapStep Γ 𝒱 T s₀ = _
  unfold dijkstraHeapStep
  rcases hb : botVal s₀.L.v with _ | ⟨t, x⟩
  · simp only [OrderedPartialMap.bot, hb]
  · simp only [OrderedPartialMap.bot, hb, h t x hb, ↓reduceIte]

end GuaranteedSubsol.DijkstraHeapProof
