/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.Dijkstra
public import LeanHJBAutoformalisation.GuaranteedSubsol.AxiomsExt
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Lex
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Tactic.Linarith

/-!
# Generalized Dijkstra: proofs

Provider proofs for the frozen anchors `GuaranteedSubsol.dijkstraStep_superSolution`,
`dijkstraRun_count_le_one`, `dijkstraRun_count_eq_one_iff` and `dijkstraRun_fixedPoint`
(Prop. prop:Dijkstra_correct), see `ANCHORS.md`.

* `step_active_ge` (causality): after the update at the selected point `x`, with `t = Γ u(x)`,
  every active point `y` has `Γ u'(y) ≥ t`. Indeed `min(u', t) = min(u, t)`, so by causality
  `Γ u'(y) < t` would give `Γ u(y) = Γ u'(y) < t`, hence `y` inactive for `u` (minimality of
  `t`), and then `u'(y) = u(y) ≤ Γ u(y) = Γ u'(y)`.
* The invariant `Inv` (`u ≤ u₀`, `count ≤ 1`, `count = 1 ↔ u < u₀`, and updated values below the
  values `Γ u(y)` of the active points) is preserved by each step, using causality only. In
  particular an updated point is never active again. Monotonicity and `Γ u₀ ≤ u₀` are only used
  for the super-solution property, hence for the fixed point at termination.
* Termination: if all the first `card X` steps perform an update, all points have been updated,
  hence none is active.
-/

@[expose] public section

namespace GuaranteedSubsol.DijkstraProof

variable {X : Type*} [LinearOrder X] {Γ : (X → WithTop ℝ) → X → WithTop ℝ}

/-- An active point exists iff a selected point exists (for finite `X`). -/
theorem exists_select [Finite X] {u : X → WithTop ℝ} (h : ∃ x, Γ u x < u x) :
    ∃ x, dijkstraSelect Γ u x := by
  obtain ⟨x, hxA, hmin⟩ := Set.exists_min_image {x | Γ u x < u x}
    (fun x => toLex (Γ u x, x)) (Set.toFinite _) h
  refine ⟨x, hxA, fun y hy => ?_⟩
  have := hmin y hy
  rw [Prod.Lex.toLex_le_toLex] at this
  exact this

open Classical in
theorem step_of_select (s : DijkstraState X) (h : ∃ x, dijkstraSelect Γ s.u x) :
    ∃ x, dijkstraSelect Γ s.u x ∧ dijkstraStep Γ s =
      ⟨Function.update s.u x (Γ s.u x), Function.update s.count x (s.count x + 1)⟩ :=
  ⟨Classical.choose h, Classical.choose_spec h, by simp only [dijkstraStep, h, ↓reduceDIte]⟩

theorem step_of_not_select (s : DijkstraState X) (h : ¬∃ x, dijkstraSelect Γ s.u x) :
    dijkstraStep Γ s = s := by
  classical
  simp only [dijkstraStep, h, ↓reduceDIte]

theorem step_superSolution (hmono : Monotone Γ) {s : DijkstraState X} (hs : Γ s.u ≤ s.u) :
    Γ (dijkstraStep Γ s).u ≤ (dijkstraStep Γ s).u := by
  by_cases h : ∃ x, dijkstraSelect Γ s.u x
  · obtain ⟨x, -, hstep⟩ := step_of_select s h
    rw [hstep]
    dsimp only
    have hle : Function.update s.u x (Γ s.u x) ≤ s.u := fun y => by
      rcases eq_or_ne y x with rfl | hyx
      · rw [Function.update_self]; exact hs y
      · rw [Function.update_of_ne hyx]
    intro y
    refine (hmono hle y).trans ?_
    rcases eq_or_ne y x with rfl | hyx
    · rw [Function.update_self]
    · rw [Function.update_of_ne hyx]; exact hs y
  · rw [step_of_not_select s h]; exact hs

theorem superSolution (hmono : Monotone Γ) {s : DijkstraState X} (hs : Γ s.u ≤ s.u) (n : ℕ) :
    Γ ((dijkstraStep Γ)^[n] s).u ≤ ((dijkstraStep Γ)^[n] s).u := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact step_superSolution hmono ih

/-- Causality: after the update at the selected point, active values are `≥ Γ u(x)`. -/
theorem step_active_ge (hcaus : ∀ x, Ext.Causal (Γ · x)) {u : X → WithTop ℝ} {x : X}
    (hx : dijkstraSelect Γ u x) {y : X}
    (hy : Γ (Function.update u x (Γ u x)) y < Function.update u x (Γ u x) y) :
    Γ u x ≤ Γ (Function.update u x (Γ u x)) y := by
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hx.1)
  set u' := Function.update u x (Γ u x)
  by_contra hlt
  rw [not_le, ← ht] at hlt
  -- `min(u', t) = min(u, t)`
  have hmin : ∀ z, min (u' z) (t : WithTop ℝ) = min (u z) t := fun z => by
    rcases eq_or_ne z x with rfl | hzx
    · simp only [u', Function.update_self, ← ht, min_self]
      rw [min_eq_right (ht ▸ hx.1).le]
    · simp only [u', Function.update_of_ne hzx]
  obtain ⟨δ, hδ, hc⟩ := hcaus y u' u t hmin
  simp only at hc
  have htδ : (t : WithTop ℝ) < ((t + δ : ℝ) : WithTop ℝ) := WithTop.coe_lt_coe.2 (by linarith)
  rw [min_eq_left (hlt.trans htδ).le] at hc
  -- `Γ u y = Γ u' y < t`
  have hΓy : Γ u y = Γ u' y := by
    rcases le_total (Γ u y) ((t + δ : ℝ) : WithTop ℝ) with h | h
    · rw [min_eq_left h] at hc; exact hc.symm
    · rw [min_eq_right h] at hc; exact absurd hc (ne_of_lt (hlt.trans htδ))
  have hinact : ¬Γ u y < u y := fun hact => by
    rcases hx.2 y hact with h | ⟨h, -⟩
    · rw [← ht] at h; exact absurd (hΓy ▸ h) (not_lt.2 hlt.le)
    · rw [← ht] at h; rw [hΓy] at h; exact absurd h (ne_of_gt hlt)
  have hyx : y ≠ x := fun h => hinact (h ▸ hx.1)
  have : u' y = u y := Function.update_of_ne hyx _ _
  rw [this, ← hΓy] at hy
  exact hinact hy

/-- Incrementing one entry of a counter increments the total by one. -/
theorem sum_update_succ [Fintype X] (c : X → ℕ) (x : X) :
    ∑ y, Function.update c x (c x + 1) y = ∑ y, c y + 1 := by
  classical
  rw [Finset.sum_update_of_mem (Finset.mem_univ x), Finset.sdiff_singleton_eq_erase,
    ← Finset.add_sum_erase _ c (Finset.mem_univ x)]
  omega

/-- The invariant of the generalized Dijkstra algorithm (causality only): `u ≤ u₀`,
`count ≤ 1`, `count = 1 ↔ u < u₀`, and updated values below the values `Γ u(y)` of the active
points. -/
def Inv (Γ : (X → WithTop ℝ) → X → WithTop ℝ) (u₀ : X → WithTop ℝ) (s : DijkstraState X) :
    Prop :=
  s.u ≤ u₀ ∧ (∀ x, s.count x ≤ 1) ∧ (∀ x, s.count x = 1 ↔ s.u x < u₀ x) ∧
    ∀ z, s.count z = 1 → ∀ y, Γ s.u y < s.u y → s.u z ≤ Γ s.u y

omit [LinearOrder X] in
theorem inv_init (u₀ : X → WithTop ℝ) : Inv Γ u₀ (dijkstraInit u₀) := by
  refine ⟨le_rfl, fun x => by simp [dijkstraInit], fun x => ?_, fun z hz => ?_⟩
  · simp [dijkstraInit]
  · simp [dijkstraInit] at hz

theorem inv_step (hcaus : ∀ x, Ext.Causal (Γ · x)) {u₀ : X → WithTop ℝ} {s : DijkstraState X}
    (hs : Inv Γ u₀ s) : Inv Γ u₀ (dijkstraStep Γ s) := by
  obtain ⟨h2, h3, h4, h5⟩ := hs
  by_cases h : ∃ x, dijkstraSelect Γ s.u x
  · obtain ⟨x, hx, hstep⟩ := step_of_select s h
    rw [hstep]
    set u' := Function.update s.u x (Γ s.u x)
    -- the selected point has not been updated before
    have hcx : s.count x = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (h3 x) with h0 | h0
      · exact h0
      · exact absurd (h5 x h0 x hx.1) (not_le.2 hx.1)
    refine ⟨fun y => ?_, fun y => ?_, fun y => ?_, fun z hz y hy => ?_⟩
    · rcases eq_or_ne y x with rfl | hyx
      · simp only [u', Function.update_self]; exact hx.1.le.trans (h2 y)
      · simp only [u', Function.update_of_ne hyx]; exact h2 y
    · rcases eq_or_ne y x with rfl | hyx
      · simp [hcx]
      · simp only [Function.update_of_ne hyx]; exact h3 y
    · rcases eq_or_ne y x with rfl | hyx
      · simp only [u', Function.update_self, hcx, zero_add, true_iff]
        exact lt_of_lt_of_le hx.1 (h2 y)
      · simp only [u', Function.update_of_ne hyx]; exact h4 y
    · have hge := step_active_ge hcaus hx hy
      refine le_trans ?_ hge
      rcases eq_or_ne z x with rfl | hzx
      · simp [u']
      · simp only [Function.update_of_ne hzx] at hz
        simp only [u', Function.update_of_ne hzx]
        exact h5 z hz x hx.1
  · rw [step_of_not_select s h]; exact ⟨h2, h3, h4, h5⟩

theorem inv_iterate (hcaus : ∀ x, Ext.Causal (Γ · x)) (u₀ : X → WithTop ℝ) (n : ℕ) :
    Inv Γ u₀ ((dijkstraStep Γ)^[n] (dijkstraInit u₀)) := by
  induction n with
  | zero => exact inv_init u₀
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact inv_step hcaus ih

/-- Each point is updated at most once (causality only). -/
theorem count_le_one (hcaus : ∀ x, Ext.Causal (Γ · x)) (u₀ : X → WithTop ℝ) (n : ℕ) (x : X) :
    ((dijkstraStep Γ)^[n] (dijkstraInit u₀)).count x ≤ 1 :=
  (inv_iterate hcaus u₀ n).2.1 x

/-- The updated points are those whose value has decreased (causality only). -/
theorem count_eq_one_iff (hcaus : ∀ x, Ext.Causal (Γ · x)) (u₀ : X → WithTop ℝ) (n : ℕ)
    (x : X) :
    ((dijkstraStep Γ)^[n] (dijkstraInit u₀)).count x = 1 ↔
      ((dijkstraStep Γ)^[n] (dijkstraInit u₀)).u x < u₀ x :=
  (inv_iterate hcaus u₀ n).2.2.1 x

omit [LinearOrder X] in
/-- Without active point, a super-solution is a fixed point. -/
theorem fixed_of_not_active {u : X → WithTop ℝ} (hsup : Γ u ≤ u) (h : ¬∃ x, Γ u x < u x) :
    Γ u = u :=
  funext fun x => le_antisymm (hsup x) (not_lt.1 fun hx => h ⟨x, hx⟩)

theorem fixedPoint [Finite X] (hmono : Monotone Γ) (hcaus : ∀ x, Ext.Causal (Γ · x))
    {u₀ : X → WithTop ℝ} (hu₀ : Γ u₀ ≤ u₀) :
    ∃ N ≤ Nat.card X, Γ ((dijkstraStep Γ)^[N] (dijkstraInit u₀)).u =
      ((dijkstraStep Γ)^[N] (dijkstraInit u₀)).u := by
  classical
  have := Fintype.ofFinite X
  set s : ℕ → DijkstraState X := fun n => (dijkstraStep Γ)^[n] (dijkstraInit u₀) with hs_def
  have hsucc : ∀ n, s (n + 1) = dijkstraStep Γ (s n) := fun n =>
    Function.iterate_succ_apply' _ _ _
  have hinv := inv_iterate hcaus u₀ (Γ := Γ)
  have hsup := superSolution hmono (s := dijkstraInit u₀) hu₀
  by_cases hstop : ∃ m < Nat.card X, ¬∃ x, Γ (s m).u x < (s m).u x
  · obtain ⟨m, hm, hna⟩ := hstop
    exact ⟨m, hm.le, fixed_of_not_active (hsup m) hna⟩
  · push Not at hstop
    -- every step before `card X` updates a new point: `∑ count = n`
    have hsum : ∀ n ≤ Nat.card X, ∑ x, (s n).count x = n := by
      intro n
      induction n with
      | zero => intro _; simp [s, dijkstraInit]
      | succ n ih =>
        intro hn
        obtain ⟨x, hx, hstep⟩ := step_of_select (s n) (exists_select (hstop n (by omega)))
        rw [hsucc, hstep]
        dsimp only
        rw [sum_update_succ, ih (by omega)]
    refine ⟨Nat.card X, le_rfl, fixed_of_not_active (hsup _) ?_⟩
    rintro ⟨y, hy⟩
    -- all points have been updated
    have hall : ∀ x, (s (Nat.card X)).count x = 1 := by
      have h1 := hsum (Nat.card X) le_rfl
      have h2 : ∑ x : X, (s (Nat.card X)).count x ≤ ∑ _x : X, 1 :=
        Finset.sum_le_sum fun x _ => (hinv _).2.1 x
      have h3 : ∑ _x : X, (1 : ℕ) = Nat.card X := by simp [Nat.card_eq_fintype_card]
      have h4 := (Finset.sum_eq_sum_iff_of_le fun x _ => (hinv (Nat.card X)).2.1 x).1
        (by rw [h1, h3])
      exact fun x => h4 x (Finset.mem_univ x)
    exact absurd ((hinv _).2.2.2 y (hall y) y hy) (not_le.2 hy)

end GuaranteedSubsol.DijkstraProof
