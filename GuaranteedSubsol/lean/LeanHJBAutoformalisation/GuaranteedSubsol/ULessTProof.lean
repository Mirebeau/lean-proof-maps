/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ExtCausalCutoffProof
import LeanHJBAutoformalisation.GuaranteedSubsol.ExtCausalMixProof

/-!
# Cutting a fixed point of `max {ū, Γ}` at a level `T` on `ℝ_∞`: proof

Provider proofs for the frozen anchors `GuaranteedSubsol.Ext.max_min_fixedPoint` and
`GuaranteedSubsol.u_less_t` (see `ANCHORS.md`): Lemmas lem:max_min (on `ℝ_∞ = WithTop ℝ`) and
lem:u_less_t (Complexity.tex). The first follows the real-valued proof `MaxMinProof`, with the
lattice identities proved in any linear order. The second uses the cutoff formulation of
causality `ExtCausalCutoffProof.causal_iff_cutoff`, applied to the causal operator
`w ↦ max {ū x, Γ w x}`, and then the first lemma.
-/

namespace GuaranteedSubsol.ULessTProof

/-- Lattice identity: `max a (min T b) = max a (min T (max a b))`, in any linear order. -/
theorem max_min_max {α : Type*} [LinearOrder α] (a b T : α) :
    max a (min T b) = max a (min T (max a b)) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h]
    rcases le_total T b with h' | h'
    · rw [min_eq_left h', min_eq_left (h'.trans h)]
    · rw [min_eq_right h', max_eq_left h]
      rcases le_total T a with h'' | h''
      · rw [min_eq_left h'', max_eq_left h'']
      · rw [min_eq_right h'', max_self]

/-- Truncation at `T` only sees truncations at levels `s ≥ T`, in any linear order. -/
theorem min_min_of_le {α : Type*} [LinearOrder α] {a T s : α} (h : T ≤ s) :
    min T (min a s) = min T a := by
  rw [min_left_comm, min_eq_left h, min_comm]

/-- `min {b,T} = min {max {a, min {T,b}}, T}` when `a ≤ b`, in any linear order. -/
theorem min_max_min {α : Type*} [LinearOrder α] (a b T : α) (h : a ≤ b) :
    min b T = min (max a (min T b)) T := by
  rcases le_total T b with h' | h'
  · rw [min_eq_left h', min_eq_right h', min_eq_right (le_max_right _ _)]
  · rw [min_eq_right h', min_eq_left h', max_eq_right h, min_eq_left h']

theorem ext_max_min_fixedPoint {X : Type*} {Γ : (X → WithTop ℝ) → X → WithTop ℝ}
    (hcaus : ∀ x, Ext.Causal (Γ · x)) (uSub : X → ℝ) (T : ℝ) {u uHat : X → WithTop ℝ}
    (hu : u = fun x => max (uSub x : WithTop ℝ) (Γ u x))
    (huHat : uHat = fun x => max (uSub x : WithTop ℝ) (min (T : WithTop ℝ) (u x))) :
    ((fun x => max (uSub x : WithTop ℝ) (min (T : WithTop ℝ) (Γ uHat x))) = uHat) ∧
      ∀ x, min (u x) T = min (uHat x) T := by
  have hux : ∀ x, u x = max (uSub x : WithTop ℝ) (Γ u x) := fun x => congrFun hu x
  have hle : ∀ x, (uSub x : WithTop ℝ) ≤ u x := fun x => (hux x).symm ▸ le_max_left _ _
  subst huHat
  have hmin : ∀ x, min (u x) (T : WithTop ℝ) =
      min (max (uSub x : WithTop ℝ) (min (T : WithTop ℝ) (u x))) T :=
    fun x => min_max_min _ _ _ (hle x)
  refine ⟨funext fun x => ?_, hmin⟩
  obtain ⟨δ, hδ, h⟩ := hcaus x (fun y => max (uSub y : WithTop ℝ) (min (T : WithTop ℝ) (u y)))
    u T fun y => (hmin y).symm
  have hTs : (T : WithTop ℝ) ≤ ((T + δ : ℝ) : WithTop ℝ) :=
    WithTop.coe_le_coe.mpr (le_of_lt (lt_add_of_pos_right T hδ))
  have hkey : min (T : WithTop ℝ)
      (Γ (fun y => max (uSub y : WithTop ℝ) (min (T : WithTop ℝ) (u y))) x) =
      min (T : WithTop ℝ) (Γ u x) := by
    rw [← min_min_of_le hTs, h, min_min_of_le hTs]
  change max (uSub x : WithTop ℝ) (min (T : WithTop ℝ) _) =
    max (uSub x : WithTop ℝ) (min (T : WithTop ℝ) (u x))
  rw [hkey, max_min_max, ← hux x]

/-- A constant scalar operator on `ℝ_∞` is causal. -/
theorem causal_const {X : Type*} (c : WithTop ℝ) :
    Ext.Causal (fun _ : X → WithTop ℝ => c) :=
  fun _ _ _ _ => ⟨1, one_pos, rfl⟩

/-- The strict cutoff is idempotent: `(a^{<T})^{<T} = a^{<T}`. -/
theorem cutoffLt_cutoffLt (T : ℝ) (a : WithTop ℝ) :
    cutoffLt T (cutoffLt T a) = cutoffLt T a := by
  rcases lt_or_ge a T with h | h
  · rw [cutoffLt_of_lt h, cutoffLt_of_lt h]
  · rw [cutoffLt_of_le h, cutoffLt_of_le le_top]

/-- The strict cutoff absorbs the large cutoff: `(a^{≤T})^{<T} = a^{<T}`. -/
theorem cutoffLt_cutoffLe (T : ℝ) (a : WithTop ℝ) :
    cutoffLt T (cutoffLe T a) = cutoffLt T a := by
  rcases le_or_gt a T with h | h
  · rw [cutoffLe_of_le h]
  · rw [cutoffLe_of_lt h, cutoffLt_of_le le_top, cutoffLt_of_le h.le]

/-- `min {T, a^{<T}} = min {T, a}`. -/
theorem min_cutoffLt (T : ℝ) (a : WithTop ℝ) :
    min (T : WithTop ℝ) (cutoffLt T a) = min (T : WithTop ℝ) a := by
  rcases lt_or_ge a T with h | h
  · rw [cutoffLt_of_lt h]
  · rw [cutoffLt_of_le h, min_eq_left le_top, min_eq_left h]

/-- `(max {a, min {T, b}})^{<T} = b^{<T}` when `a ≤ b`. -/
theorem cutoffLt_max_min (T : ℝ) {a b : WithTop ℝ} (hab : a ≤ b) :
    cutoffLt T (max a (min (T : WithTop ℝ) b)) = cutoffLt T b := by
  rcases lt_or_ge b T with h | h
  · rw [min_eq_right h.le, max_eq_right hab]
  · rw [min_eq_left h, cutoffLt_of_le (le_max_right _ _), cutoffLt_of_le h]

theorem u_less_t {X : Type*} {Γ : (X → WithTop ℝ) → X → WithTop ℝ}
    (hcaus : ∀ x, Ext.Causal (Γ · x)) (uSub : X → ℝ) (T : ℝ) {u ucheck uHat : X → WithTop ℝ}
    (hu : u = fun x => max (uSub x : WithTop ℝ) (Γ u x))
    (hucheck : ucheck = fun x => cutoffLt T (u x))
    (huHat : uHat = fun x => max (uSub x : WithTop ℝ) (min (T : WithTop ℝ) (ucheck x))) :
    (ucheck = fun x => cutoffLt T (max (uSub x : WithTop ℝ) (Γ ucheck x))) ∧
      (uHat = fun x => max (uSub x : WithTop ℝ) (min (T : WithTop ℝ) (Γ uHat x))) ∧
      ucheck = fun x => cutoffLt T (uHat x) := by
  have hux : ∀ x, u x = max (uSub x : WithTop ℝ) (Γ u x) := fun x => congrFun hu x
  have hle : ∀ x, (uSub x : WithTop ℝ) ≤ u x := fun x => (hux x).symm ▸ le_max_left _ _
  have hcx : ∀ x, ucheck x = cutoffLt T (u x) := fun x => congrFun hucheck x
  have huHat' : uHat = fun x => max (uSub x : WithTop ℝ) (min (T : WithTop ℝ) (u x)) := by
    rw [huHat]
    funext x
    rw [hcx x, min_cutoffLt]
  refine ⟨funext fun x => ?_, (ext_max_min_fixedPoint hcaus uSub T hu huHat').1.symm,
    funext fun x => ?_⟩
  · have hΓ' : Ext.Causal fun w => max (uSub x : WithTop ℝ) (Γ w x) :=
      ExtCausalMixProof.causal_max (causal_const _) (hcaus x)
    have h := (ExtCausalCutoffProof.causal_iff_cutoff _).mp hΓ' ucheck u T
      fun y => by rw [hcx y, cutoffLt_cutoffLt]
    beta_reduce at h
    rw [← cutoffLt_cutoffLe, h, ← hux x, cutoffLt_cutoffLe, hcx x]
  · rw [hcx x, huHat', cutoffLt_max_min T (hle x)]

end GuaranteedSubsol.ULessTProof
