/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.Axioms
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# `C_past`-memory and eq. (Lambda_max_u_t): proofs

Provider proofs for the frozen anchors `GuaranteedSubsol.HasMemory.apply_eq_apply_max` and
`GuaranteedSubsol.hasMemory_of_apply_eq_apply_max` (see `ANCHORS.md`): Prop.
prop:Cpast_formulation (Complexity.tex), scalar form, both implications.

* Direct implication: for `t < Λ u - C`, memory applied to `u` and `max {u,t}` gives the equality;
  the boundary case `t = Λ u - C` follows by applying it at `t - ε` for every `ε > 0`.
* Converse: if `Λ u > t + C` and `max {u,t} = max {v,t}`, then `Λ u = Λ (u - k ε 1_{u ≤ t})`
  for every `k : ℕ`, where `ε = Λ u - (t + C)`; since `X` is finite, `u - k ε 1_{u ≤ t} ≤ v`
  for `k` large, hence `Λ u ≤ Λ v`. Symmetry concludes.
-/

namespace GuaranteedSubsol.CpastFormulationProof

variable {X : Type*} {Λ : (X → ℝ) → ℝ} {C : ℝ}

/-- Strict case of the direct implication: memory gives `Λ u = Λ max {u,t}` when
`t < Λ u - C`. -/
theorem apply_eq_apply_max_of_lt (h : HasMemory C Λ) (u : X → ℝ) {t : ℝ}
    (ht : t < Λ u - C) : Λ u = Λ (fun y => max (u y) t) := by
  have hm := h u (fun y => max (u y) t) t fun y => by rw [max_assoc, max_self]
  rw [max_eq_left (by linarith : t + C ≤ Λ u)] at hm
  rcases le_or_gt (t + C) (Λ fun y => max (u y) t) with hle | hlt
  · rwa [max_eq_left hle] at hm
  · rw [max_eq_right hlt.le] at hm
    linarith

theorem apply_eq_apply_max {X : Type*} {Λ : (X → ℝ) → ℝ} {C : ℝ}
    (hmono : Monotone Λ) (hadd : AdditivelyInvariant Λ) (h : HasMemory C Λ)
    (u : X → ℝ) {t : ℝ} (ht : t ≤ Λ u - C) :
    Λ u = Λ (fun y => max (u y) t) := by
  refine le_antisymm (hmono fun y => le_max_left _ _) ?_
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have h1 := apply_eq_apply_max_of_lt h u (t := t - ε) (by linarith)
  have h2 : Λ (fun y => max (u y) t + -ε) ≤ Λ (fun y => max (u y) (t - ε)) :=
    hmono fun y => by
      rcases le_total (u y) t with hy | hy
      · rw [max_eq_right hy]; exact (by linarith : t + -ε = t - ε) ▸ le_max_right _ _
      · rw [max_eq_left hy]; linarith [le_max_left (u y) (t - ε)]
  rw [hadd] at h2
  linarith

/-- The functions `u - k ε 1_{u ≤ t}` used in the converse implication. -/
noncomputable def lowered (u : X → ℝ) (t ε : ℝ) (k : ℕ) : X → ℝ :=
  fun y => if t < u y then u y else u y - k * ε

/-- Key induction of the converse: `Λ (u - k ε 1_{u ≤ t}) = Λ u` for all `k`, provided
`0 ≤ ε` and `t + ε + C ≤ Λ u`. -/
theorem apply_lowered (hmono : Monotone Λ) (hadd : AdditivelyInvariant Λ)
    (h : ∀ (u : X → ℝ) (t : ℝ), t ≤ Λ u - C → Λ u = Λ (fun y => max (u y) t))
    (u : X → ℝ) {t ε : ℝ} (hε : 0 ≤ ε) (hu : t + ε + C ≤ Λ u) (k : ℕ) :
    Λ (lowered u t ε k) = Λ u := by
  induction k with
  | zero => congr 1; funext y; simp [lowered]
  | succ k ih =>
    set w' : X → ℝ := fun y => lowered u t ε k y + if t < u y then ε else 0 with hw'
    have hw'_ge : Λ u ≤ Λ w' := ih ▸ hmono fun y => by
      simp only [hw']; split_ifs <;> linarith
    have hmax := h w' (t + ε) (by linarith)
    have hlow : Λ (fun y => lowered u t ε k y + ε) ≤ Λ (fun y => max (w' y) (t + ε)) :=
      hmono fun y => by
        simp only [hw', lowered]
        split_ifs with hy
        · exact le_max_left _ _
        · have : (0 : ℝ) ≤ k * ε := mul_nonneg (Nat.cast_nonneg k) hε
          have : u y ≤ t := not_lt.1 hy
          exact le_max_of_le_right (by linarith)
    rw [hadd, ih, ← hmax] at hlow
    have hnext : lowered u t ε (k + 1) = fun y => w' y + -ε := by
      funext y; simp only [hw', lowered]; split_ifs <;> push_cast <;> ring
    have hle : lowered u t ε (k + 1) ≤ lowered u t ε k := fun y => by
      simp only [lowered]; split_ifs
      · exact le_rfl
      · push_cast; nlinarith
    have h3 := hmono hle
    rw [ih] at h3
    rw [hnext, hadd] at h3 ⊢
    linarith

/-- One-sided converse: if `max {u,t} = max {v,t}` and `t + C < Λ u`, then `Λ u ≤ Λ v`. -/
theorem apply_le_of_max_eq [Finite X] (hmono : Monotone Λ) (hadd : AdditivelyInvariant Λ)
    (h : ∀ (u : X → ℝ) (t : ℝ), t ≤ Λ u - C → Λ u = Λ (fun y => max (u y) t))
    {u v : X → ℝ} {t : ℝ} (huv : ∀ y, max (u y) t = max (v y) t) (hu : t + C < Λ u) :
    Λ u ≤ Λ v := by
  set ε := Λ u - (t + C) with hε
  have hεpos : 0 < ε := by linarith
  obtain ⟨M, hM⟩ := (Set.toFinite (Set.range fun y => u y - v y)).bddAbove
  obtain ⟨k, hk⟩ := exists_nat_ge (M / ε)
  have hMk : M ≤ k * ε := (div_le_iff₀ hεpos).1 hk
  rw [← apply_lowered hmono hadd h u (t := t) hεpos.le (by linarith) k]
  refine hmono fun y => ?_
  simp only [lowered]
  split_ifs with hy
  · have hyv := huv y
    rw [max_eq_left hy.le] at hyv
    rcases le_total (v y) t with hv | hv
    · rw [max_eq_right hv] at hyv; linarith
    · rw [max_eq_left hv] at hyv; exact hyv.le
  · have : u y - v y ≤ M := hM ⟨y, rfl⟩
    linarith

/-- Symmetrizable inequality: `max (Λ u) (t + C) ≤ max (Λ v) (t + C)`. -/
theorem max_apply_le [Finite X] (hmono : Monotone Λ) (hadd : AdditivelyInvariant Λ)
    (h : ∀ (u : X → ℝ) (t : ℝ), t ≤ Λ u - C → Λ u = Λ (fun y => max (u y) t))
    {u v : X → ℝ} {t : ℝ} (huv : ∀ y, max (u y) t = max (v y) t) :
    max (Λ u) (t + C) ≤ max (Λ v) (t + C) := by
  rcases le_or_gt (Λ u) (t + C) with hu | hu
  · rw [max_eq_right hu]; exact le_max_right _ _
  · rw [max_eq_left hu.le]
    exact le_max_of_le_left (apply_le_of_max_eq hmono hadd h huv hu)

theorem hasMemory_of_apply_eq_apply_max {X : Type*} [Finite X] {Λ : (X → ℝ) → ℝ} {C : ℝ}
    (hmono : Monotone Λ) (hadd : AdditivelyInvariant Λ)
    (h : ∀ (u : X → ℝ) (t : ℝ), t ≤ Λ u - C → Λ u = Λ (fun y => max (u y) t)) :
    HasMemory C Λ := fun _ _ _ huv =>
  le_antisymm (max_apply_le hmono hadd h huv)
    (max_apply_le hmono hadd h fun y => (huv y).symm)

end GuaranteedSubsol.CpastFormulationProof
