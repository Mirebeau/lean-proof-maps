/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.ParallelAgsiCplxProof
public import LeanHJBAutoformalisation.GuaranteedSubsol.Reflect

/-!
# Parallel AGSI, sub-solution variant: proofs by reflection

The sub-solution variant on `Φ` started from `v` is the super-solution version on the reflected
operator `reflectOp Φ = (v ↦ -Φ (-v))` started from `-v`, up to the sign of `v`
(`parallelAgsiSubStep_iterate`). The reflection preserves monotonicity, `ρ`-sub-additivity and
the comparison principle, and exchanges sub- and super-solutions (`Reflect.lean`), so the
results for the sub-solution variant follow from those for the super-solution version.
-/

@[expose] public section

namespace GuaranteedSubsol.ParallelAgsiSubProof

variable {X : Type*} {Φ : (X → ℝ) → X → ℝ} {η : ℝ}

/-- One pass of the sub-solution variant is a pass of the super-solution version for the
reflected operator, on the negated state. -/
theorem parallelAgsiSubStep_eq (s : ParallelAgsiState X) :
    parallelAgsiSubStep Φ η s = (parallelAgsiStep (reflectOp Φ) η s.neg).neg := by
  have hc : ∀ x, (η < Φ s.v x - s.v x) ↔ (η < -s.v x - reflectOp Φ (-s.v) x) := fun x => by
    rw [reflectOp_apply_apply, neg_neg]; constructor <;> intro h <;> linarith
  cases s with
  | mk v c =>
    simp only [parallelAgsiSubStep, parallelAgsiStep, ParallelAgsiState.neg]
    congr 1
    · funext x
      by_cases h : η < Φ v x - v x
      · rw [restrictOp_of_mem _ (show x ∈ {x | η < Φ v x - v x} from h), Pi.neg_apply,
          restrictOp_of_mem _ (show x ∈ {x | η < (-v) x - reflectOp Φ (-v) x} from (hc x).1 h),
          reflectOp_apply_apply, neg_neg, neg_neg]
      · rw [restrictOp_of_notMem _ (show x ∉ {x | η < Φ v x - v x} from h), Pi.neg_apply,
          restrictOp_of_notMem _
            (show x ∉ {x | η < (-v) x - reflectOp Φ (-v) x} from fun h' => h ((hc x).2 h')),
          Pi.neg_apply, neg_neg]
    · funext x
      simp only [Pi.neg_apply] at hc ⊢
      by_cases h : η < Φ v x - v x
      · simp [h, (hc x).1 h]
      · have h' : ¬η < -v x - reflectOp Φ (-v) x := fun h' => h ((hc x).2 h')
        simp [h, h']

/-- The sub-solution variant after `n` passes, through the super-solution version for the
reflected operator. -/
theorem parallelAgsiSubStep_iterate (s : ParallelAgsiState X) (n : ℕ) :
    (parallelAgsiSubStep Φ η)^[n] s = ((parallelAgsiStep (reflectOp Φ) η)^[n] s.neg).neg := by
  induction n with
  | zero => cases s; simp [ParallelAgsiState.neg]
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      parallelAgsiSubStep_eq]
    congr 2
    cases ((parallelAgsiStep (reflectOp Φ) η)^[n] s.neg)
    simp [ParallelAgsiState.neg]

/-- Reading the iterates off the reflected run, from `⟨v, 0⟩`. -/
theorem iterate_v (v : X → ℝ) (n : ℕ) :
    ((parallelAgsiSubStep Φ η)^[n] ⟨v, 0⟩).v =
      -((parallelAgsiStep (reflectOp Φ) η)^[n] ⟨-v, 0⟩).v := by
  rw [parallelAgsiSubStep_iterate]; rfl

theorem iterate_count (v : X → ℝ) (n : ℕ) :
    ((parallelAgsiSubStep Φ η)^[n] ⟨v, 0⟩).count =
      ((parallelAgsiStep (reflectOp Φ) η)^[n] ⟨-v, 0⟩).count := by
  rw [parallelAgsiSubStep_iterate]; rfl

theorem subSolution (hmono : Monotone Φ) (η : ℝ) {s : ParallelAgsiState X}
    (hs : s.v ≤ Φ s.v) (n : ℕ) :
    ((parallelAgsiSubStep Φ η)^[n] s).v ≤ Φ ((parallelAgsiSubStep Φ η)^[n] s).v := by
  have hs' : reflectOp Φ s.neg.v ≤ s.neg.v := by
    rw [reflectOp_le_iff]; simpa [ParallelAgsiState.neg] using hs
  have key := ParallelAgsiProof.superSolution (Monotone.reflectOp hmono) η hs' n
  rw [parallelAgsiSubStep_iterate]
  rw [reflectOp_le_iff] at key
  simpa [ParallelAgsiState.neg] using key

theorem count_le [Fintype X] (hmono : Monotone Φ)
    (hcomp : HasComparisonPrinciple Set.univ Φ) {w : X → ℝ} (hw : Φ w ≤ w)
    {v : X → ℝ} (hv : v ≤ Φ v) (n : ℕ) :
    η * ∑ x, (((parallelAgsiSubStep Φ η)^[n] ⟨v, 0⟩).count x : ℝ) ≤ ∑ x, (w x - v x) := by
  have hw' : -w ≤ reflectOp Φ (-w) := by rw [le_reflectOp_iff, neg_neg]; exact hw
  have hv' : reflectOp Φ (-v) ≤ -v := by rw [reflectOp_le_iff, neg_neg]; exact hv
  have key := ParallelAgsiProof.count_le (η := η) (Monotone.reflectOp hmono) hcomp.reflectOp hw'
    hv' n
  rw [iterate_count]
  convert key using 2
  simp only [Pi.neg_apply]; ring

theorem terminates [Fintype X] (hmono : Monotone Φ)
    (hcomp : HasComparisonPrinciple Set.univ Φ) {w : X → ℝ} (hw : Φ w ≤ w)
    (hη : 0 < η) {v : X → ℝ} (hv : v ≤ Φ v) :
    ∃ n ≤ ⌈(∑ x, (w x - v x)) / η⌉₊, ∀ x,
      Φ ((parallelAgsiSubStep Φ η)^[n] ⟨v, 0⟩).v x - ((parallelAgsiSubStep Φ η)^[n] ⟨v, 0⟩).v x
        ≤ η := by
  have hw' : -w ≤ reflectOp Φ (-w) := by rw [le_reflectOp_iff, neg_neg]; exact hw
  have hv' : reflectOp Φ (-v) ≤ -v := by rw [reflectOp_le_iff, neg_neg]; exact hv
  obtain ⟨n, hn, h⟩ := ParallelAgsiProof.terminates (Monotone.reflectOp hmono) hcomp.reflectOp
    hw' hη hv'
  refine ⟨n, ?_, fun x => ?_⟩
  · convert hn using 4
    simp only [Pi.neg_apply]; ring
  · have := h x
    rw [iterate_v]
    simp only [reflectOp_apply_apply, Pi.neg_apply] at this ⊢
    linarith

theorem count_le_of_subAdditive [Finite X] (hmono : Monotone Φ) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hsub : ∀ x, SubAdditive ρ (Φ · x)) {C : ℝ} (hη : 0 < η) {v : X → ℝ}
    (hv : v ≤ Φ v) (hvC : ∀ x, Φ v x - v x ≤ C) (n : ℕ) (x : X) :
    (((parallelAgsiSubStep Φ η)^[n] ⟨v, 0⟩).count x : ℝ) ≤
      ⌈Real.log ((1 - ρ) * C / η) / (-Real.log ρ)⌉₊ + 2 / (1 - ρ) ^ 2 := by
  have hv' : reflectOp Φ (-v) ≤ -v := by rw [reflectOp_le_iff, neg_neg]; exact hv
  have hsub' : ∀ x, SubAdditive ρ (reflectOp Φ · x) := fun x => by
    rw [reflectOp_comp_eval]; exact (hsub x).reflectOp
  have hvC' : ∀ x, -v x - reflectOp Φ (-v) x ≤ C := fun x => by
    rw [reflectOp_apply_apply, neg_neg]; linarith [hvC x]
  rw [iterate_count]
  exact ParallelAgsiCplxProof.count_le_of_subAdditive (Monotone.reflectOp hmono) hρ0 hρ1 hsub'
    hη hv' hvC' n x

end GuaranteedSubsol.ParallelAgsiSubProof
