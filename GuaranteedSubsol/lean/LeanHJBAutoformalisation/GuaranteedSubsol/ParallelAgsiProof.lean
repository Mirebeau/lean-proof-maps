/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ParallelAGSI
import LeanHJBAutoformalisation.GuaranteedSubsol.RestrictionProof
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Parallel AGSI: proofs

Provider proofs for the frozen anchors `GuaranteedSubsol.parallelAgsiStep_superSolution`,
`GuaranteedSubsol.parallelAgsiRun_count_le` and `GuaranteedSubsol.parallelAgsiRun_terminates`
(Algorithm algo:agsi_parallel and a V0 `\formalizationInstruction`, removed in V1), see
`ANCHORS.md`.

* Invariant: each pass is `v ← Φ_B v`, which preserves super-solutions by
  Prop. prop:partialMonotone (`restrictOp_superSolution`).
* Count: the potential `∑_X v + η ∑_X count` does not increase along the algorithm (an update at
  `x` lowers `v x` by more than `η` and raises `count x` by `1`), while `w ≤ v` by the comparison
  principle.
* Termination: each pass before termination performs at least one update, so after `n` such
  passes `∑_X count ≥ n`, which the count bound limits to `n ≤ ∑_X (v - w) / η`.
-/

namespace GuaranteedSubsol.ParallelAgsiProof

variable {X : Type*} {Φ : (X → ℝ) → X → ℝ} {η : ℝ}

/-- Pointwise form of a pass, for `v`. -/
theorem step_v (s : ParallelAgsiState X) (x : X) :
    (parallelAgsiStep Φ η s).v x = if η < s.v x - Φ s.v x then Φ s.v x else s.v x := by
  by_cases h : η < s.v x - Φ s.v x
  · simp only [h, ↓reduceIte]
    exact restrictOp_of_mem _ (show x ∈ {x | η < s.v x - Φ s.v x} from h)
  · simp only [h, ↓reduceIte]
    exact restrictOp_of_notMem _ (show x ∉ {x | η < s.v x - Φ s.v x} from h)

/-- Pointwise form of a pass, for the counter. -/
theorem step_count (s : ParallelAgsiState X) (x : X) :
    (parallelAgsiStep Φ η s).count x =
      if η < s.v x - Φ s.v x then s.count x + 1 else s.count x := by
  classical
  simp only [parallelAgsiStep]

theorem superSolution (hmono : Monotone Φ) (η : ℝ) {s : ParallelAgsiState X}
    (hs : Φ s.v ≤ s.v) (n : ℕ) :
    Φ ((parallelAgsiStep Φ η)^[n] s).v ≤ ((parallelAgsiStep Φ η)^[n] s).v := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact RestrictionProof.restrictOp_superSolution hmono _ ih

/-- One pass does not increase the potential `v x + η count x`, at every point. -/
theorem step_potential_le (s : ParallelAgsiState X) (x : X) :
    (parallelAgsiStep Φ η s).v x + η * ((parallelAgsiStep Φ η s).count x : ℝ) ≤
      s.v x + η * (s.count x : ℝ) := by
  rw [step_v, step_count]
  split_ifs with h
  · push_cast; linarith
  · exact le_rfl

theorem count_le [Fintype X] (hmono : Monotone Φ)
    (hcomp : HasComparisonPrinciple Set.univ Φ) {w : X → ℝ} (hw : w ≤ Φ w) {v : X → ℝ}
    (hv : Φ v ≤ v) (n : ℕ) :
    η * ∑ x, (((parallelAgsiStep Φ η)^[n] ⟨v, 0⟩).count x : ℝ) ≤ ∑ x, (v x - w x) := by
  set s := fun n => (parallelAgsiStep Φ η)^[n] (⟨v, 0⟩ : ParallelAgsiState X)
  -- the potential `∑ v + η ∑ count` does not increase
  have hpot : ∀ n, ∑ x, ((s n).v x + η * ((s n).count x : ℝ)) ≤ ∑ x, v x := by
    intro n
    induction n with
    | zero => simp [s]
    | succ n ih =>
      refine le_trans (Finset.sum_le_sum fun x _ => ?_) ih
      simp only [s, Function.iterate_succ_apply']
      exact step_potential_le _ x
  -- `w ≤ v` along the algorithm, by the comparison principle
  have hwv : w ≤ (s n).v := hcomp w (s n).v (fun x _ => hw x)
    (fun x _ => superSolution hmono η (s := ⟨v, 0⟩) hv n x) (fun x hx => absurd trivial hx)
  have h1 := hpot n
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h1
  have h2 : ∑ x, w x ≤ ∑ x, (s n).v x := Finset.sum_le_sum fun x _ => hwv x
  rw [Finset.sum_sub_distrib]
  simp only [s] at h1 h2
  linarith

theorem terminates [Fintype X] (hmono : Monotone Φ)
    (hcomp : HasComparisonPrinciple Set.univ Φ) {w : X → ℝ} (hw : w ≤ Φ w)
    (hη : 0 < η) {v : X → ℝ} (hv : Φ v ≤ v) :
    ∃ n ≤ ⌈(∑ x, (v x - w x)) / η⌉₊, ∀ x,
      ((parallelAgsiStep Φ η)^[n] ⟨v, 0⟩).v x - Φ ((parallelAgsiStep Φ η)^[n] ⟨v, 0⟩).v x ≤ η := by
  set s := fun n => (parallelAgsiStep Φ η)^[n] (⟨v, 0⟩ : ParallelAgsiState X)
  classical
  set N := ⌈(∑ x, (v x - w x)) / η⌉₊
  by_contra hcon
  push Not at hcon
  -- each pass up to `N` performs an update, so `∑ count ≥ n` for `n ≤ N + 1`
  have hcnt : ∀ n ≤ N + 1, (n : ℝ) ≤ ∑ x, ((s n).count x : ℝ) := by
    intro n
    induction n with
    | zero => intro _; simp [s]
    | succ n ih =>
      intro hn
      obtain ⟨y, hy⟩ := hcon n (by omega)
      have hle : ∀ x, ((s n).count x : ℝ) ≤ ((s (n + 1)).count x : ℝ) := fun x => by
        simp only [s, Function.iterate_succ_apply']
        rw [step_count]
        split_ifs <;> push_cast <;> linarith
      have hlt : ((s n).count y : ℝ) + 1 ≤ ((s (n + 1)).count y : ℝ) := by
        simp only [s, Function.iterate_succ_apply']
        rw [step_count]
        simp only [hy, ↓reduceIte]
        push_cast; exact le_rfl
      have hsum : ∑ x, ((s n).count x : ℝ) + 1 ≤ ∑ x, ((s (n + 1)).count x : ℝ) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ y),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ y)]
        have := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ.erase y) => hle x
        linarith
      push_cast
      linarith [ih (by omega)]
  have h1 := hcnt (N + 1) le_rfl
  have h2 := count_le (η := η) hmono hcomp hw hv (N + 1)
  have h3 : (∑ x, (v x - w x)) / η ≤ N := Nat.le_ceil _
  rw [div_le_iff₀ hη] at h3
  push_cast at h1
  nlinarith

end GuaranteedSubsol.ParallelAgsiProof
