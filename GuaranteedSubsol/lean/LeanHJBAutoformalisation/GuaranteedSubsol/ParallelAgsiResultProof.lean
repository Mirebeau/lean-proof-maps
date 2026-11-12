/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ParallelAGSI
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Parallel AGSI: the output of the loop

Properties of `parallelAgsiPasses`, `parallelAgsiResult`, `parallelAgsiCount` and of their
sub-solution variants:
* when the loop stops, its output satisfies the stopping criterion (`result_crit`);
* every map produced along the loop is obtained from the previous one by replacing some of its
  values `v(x)` with `Φ v(x)`, so the output lies in any set of maps which contains the input and
  is closed under such partial updates (`result_mem`);
* a bound on the number of updates at each point, uniform along the loop, implies that the loop
  stops (`passes_lt_top_of_count_le`): each pass before the stop performs at least one update.
-/

namespace GuaranteedSubsol.ParallelAgsiResultProof

variable {X : Type*} {Φ : (X → ℝ) → X → ℝ} {η : ℝ} {v : X → ℝ}

/-! ### Super-solution version -/

theorem step_v (s : ParallelAgsiState X) (x : X) :
    (parallelAgsiStep Φ η s).v x = if η < s.v x - Φ s.v x then Φ s.v x else s.v x := by
  by_cases h : η < s.v x - Φ s.v x
  · simp only [h, ↓reduceIte]
    exact restrictOp_of_mem _ (show x ∈ {x | η < s.v x - Φ s.v x} from h)
  · simp only [h, ↓reduceIte]
    exact restrictOp_of_notMem _ (show x ∉ {x | η < s.v x - Φ s.v x} from h)

theorem step_count (s : ParallelAgsiState X) (x : X) :
    (parallelAgsiStep Φ η s).count x =
      if η < s.v x - Φ s.v x then s.count x + 1 else s.count x := by
  classical
  simp only [parallelAgsiStep]

theorem run_succ (n : ℕ) :
    parallelAgsiRun Φ η v (n + 1) = parallelAgsiStep Φ η (parallelAgsiRun Φ η v n) :=
  Function.iterate_succ_apply' _ _ _

/-- When the loop stops, its output satisfies the stopping criterion. -/
theorem result_crit (h : parallelAgsiPasses Φ η v < ⊤) (x : X) :
    parallelAgsiResult Φ η v x - Φ (parallelAgsiResult Φ η v) x ≤ η := by
  classical
  by_cases hex : ∃ n, ∀ x, (parallelAgsiRun Φ η v n).v x - Φ (parallelAgsiRun Φ η v n).v x ≤ η
  · unfold parallelAgsiResult parallelAgsiPasses
    simp only [hex, ↓reduceDIte, ENat.toNat_natCast]
    exact Nat.find_spec hex x
  · unfold parallelAgsiPasses at h
    simp only [hex, ↓reduceDIte, lt_self_iff_false] at h

/-- The maps produced along the loop lie in any set containing `v` and closed under partial
updates. -/
theorem run_mem {N : Set (X → ℝ)} (hv : v ∈ N)
    (hN : ∀ w ∈ N, ∀ w' : X → ℝ, (∀ y, w' y = w y ∨ w' y = Φ w y) → w' ∈ N) (n : ℕ) :
    (parallelAgsiRun Φ η v n).v ∈ N := by
  induction n with
  | zero => exact hv
  | succ n ih =>
    rw [run_succ]
    refine hN _ ih _ fun y => ?_
    rw [step_v]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem result_mem {N : Set (X → ℝ)} (hv : v ∈ N)
    (hN : ∀ w ∈ N, ∀ w' : X → ℝ, (∀ y, w' y = w y ∨ w' y = Φ w y) → w' ∈ N) :
    parallelAgsiResult Φ η v ∈ N :=
  run_mem hv hN _

/-- A uniform bound on the number of updates at each point implies that the loop stops. -/
theorem passes_lt_top_of_count_le [Finite X] {M : ℝ}
    (hb : ∀ n x, ((parallelAgsiRun Φ η v n).count x : ℝ) ≤ M) :
    parallelAgsiPasses Φ η v < ⊤ := by
  classical
  have := Fintype.ofFinite X
  have hex : ∃ n, ∀ x, (parallelAgsiRun Φ η v n).v x - Φ (parallelAgsiRun Φ η v n).v x ≤ η := by
    by_contra hcon
    push Not at hcon
    have hcnt : ∀ n : ℕ, (n : ℝ) ≤ ∑ x, ((parallelAgsiRun Φ η v n).count x : ℝ) := by
      intro n
      induction n with
      | zero =>
        simp only [Nat.cast_zero]
        exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
      | succ n ih =>
        obtain ⟨y, hy⟩ := hcon n
        have hle : ∀ x, ((parallelAgsiRun Φ η v n).count x : ℝ) ≤
            ((parallelAgsiRun Φ η v (n + 1)).count x : ℝ) := fun x => by
          rw [run_succ, step_count]
          split_ifs <;> push_cast <;> linarith
        have hlt : ((parallelAgsiRun Φ η v n).count y : ℝ) + 1 ≤
            ((parallelAgsiRun Φ η v (n + 1)).count y : ℝ) := by
          rw [run_succ, step_count]
          simp only [hy, ↓reduceIte]
          push_cast; linarith
        have := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hle x
        have hsplit := Finset.add_sum_erase Finset.univ
          (fun x => ((parallelAgsiRun Φ η v (n + 1)).count x : ℝ)) (Finset.mem_univ y)
        have hsplit' := Finset.add_sum_erase Finset.univ
          (fun x => ((parallelAgsiRun Φ η v n).count x : ℝ)) (Finset.mem_univ y)
        have hrest := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ.erase y) => hle x
        push_cast
        linarith
    obtain ⟨n, hn⟩ := exists_nat_gt ((Fintype.card X : ℝ) * M)
    have h1 := hcnt n
    have h2 : ∑ x, ((parallelAgsiRun Φ η v n).count x : ℝ) ≤ Fintype.card X * M := by
      have := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hb n x
      simpa [Finset.sum_const, nsmul_eq_mul] using this
    linarith
  unfold parallelAgsiPasses
  simp only [hex, ↓reduceDIte]
  exact ENat.natCast_lt_top _

/-- When the loop stops, the number of updates at each point is the counter of the output. -/
theorem count_eq (h : parallelAgsiPasses Φ η v < ⊤) (x : X) :
    parallelAgsiCount Φ η v x =
      ((parallelAgsiRun Φ η v (parallelAgsiPasses Φ η v).toNat).count x : ℕ∞) := by
  classical
  unfold parallelAgsiCount
  simp only [h.ne, ↓reduceIte]

theorem count_lt_top_iff (x : X) :
    parallelAgsiCount Φ η v x < ⊤ ↔ parallelAgsiPasses Φ η v < ⊤ := by
  classical
  unfold parallelAgsiCount
  by_cases h : parallelAgsiPasses Φ η v = ⊤
  · simp [h]
  · simp only [h, ↓reduceIte, ENat.natCast_lt_top, true_iff]
    exact lt_top_iff_ne_top.2 h

/-! ### Sub-solution variant -/

theorem subStep_v (s : ParallelAgsiState X) (x : X) :
    (parallelAgsiSubStep Φ η s).v x = if η < Φ s.v x - s.v x then Φ s.v x else s.v x := by
  by_cases h : η < Φ s.v x - s.v x
  · simp only [h, ↓reduceIte]
    exact restrictOp_of_mem _ (show x ∈ {x | η < Φ s.v x - s.v x} from h)
  · simp only [h, ↓reduceIte]
    exact restrictOp_of_notMem _ (show x ∉ {x | η < Φ s.v x - s.v x} from h)

theorem subStep_count (s : ParallelAgsiState X) (x : X) :
    (parallelAgsiSubStep Φ η s).count x =
      if η < Φ s.v x - s.v x then s.count x + 1 else s.count x := by
  classical
  simp only [parallelAgsiSubStep]

theorem subRun_succ (n : ℕ) :
    parallelAgsiSubRun Φ η v (n + 1) = parallelAgsiSubStep Φ η (parallelAgsiSubRun Φ η v n) :=
  Function.iterate_succ_apply' _ _ _

theorem subResult_crit (h : parallelAgsiSubPasses Φ η v < ⊤) (x : X) :
    Φ (parallelAgsiSubResult Φ η v) x - parallelAgsiSubResult Φ η v x ≤ η := by
  classical
  by_cases hex : ∃ n, ∀ x,
      Φ (parallelAgsiSubRun Φ η v n).v x - (parallelAgsiSubRun Φ η v n).v x ≤ η
  · unfold parallelAgsiSubResult parallelAgsiSubPasses
    simp only [hex, ↓reduceDIte, ENat.toNat_natCast]
    exact Nat.find_spec hex x
  · unfold parallelAgsiSubPasses at h
    simp only [hex, ↓reduceDIte, lt_self_iff_false] at h

theorem subRun_mem {N : Set (X → ℝ)} (hv : v ∈ N)
    (hN : ∀ w ∈ N, ∀ w' : X → ℝ, (∀ y, w' y = w y ∨ w' y = Φ w y) → w' ∈ N) (n : ℕ) :
    (parallelAgsiSubRun Φ η v n).v ∈ N := by
  induction n with
  | zero => exact hv
  | succ n ih =>
    rw [subRun_succ]
    refine hN _ ih _ fun y => ?_
    rw [subStep_v]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem subResult_mem {N : Set (X → ℝ)} (hv : v ∈ N)
    (hN : ∀ w ∈ N, ∀ w' : X → ℝ, (∀ y, w' y = w y ∨ w' y = Φ w y) → w' ∈ N) :
    parallelAgsiSubResult Φ η v ∈ N :=
  subRun_mem hv hN _

theorem subPasses_lt_top_of_count_le [Finite X] {M : ℝ}
    (hb : ∀ n x, ((parallelAgsiSubRun Φ η v n).count x : ℝ) ≤ M) :
    parallelAgsiSubPasses Φ η v < ⊤ := by
  classical
  have := Fintype.ofFinite X
  have hex : ∃ n, ∀ x,
      Φ (parallelAgsiSubRun Φ η v n).v x - (parallelAgsiSubRun Φ η v n).v x ≤ η := by
    by_contra hcon
    push Not at hcon
    have hcnt : ∀ n : ℕ, (n : ℝ) ≤ ∑ x, ((parallelAgsiSubRun Φ η v n).count x : ℝ) := by
      intro n
      induction n with
      | zero =>
        simp only [Nat.cast_zero]
        exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
      | succ n ih =>
        obtain ⟨y, hy⟩ := hcon n
        have hle : ∀ x, ((parallelAgsiSubRun Φ η v n).count x : ℝ) ≤
            ((parallelAgsiSubRun Φ η v (n + 1)).count x : ℝ) := fun x => by
          rw [subRun_succ, subStep_count]
          split_ifs <;> push_cast <;> linarith
        have hlt : ((parallelAgsiSubRun Φ η v n).count y : ℝ) + 1 ≤
            ((parallelAgsiSubRun Φ η v (n + 1)).count y : ℝ) := by
          rw [subRun_succ, subStep_count]
          simp only [hy, ↓reduceIte]
          push_cast; linarith
        have hsplit := Finset.add_sum_erase Finset.univ
          (fun x => ((parallelAgsiSubRun Φ η v (n + 1)).count x : ℝ)) (Finset.mem_univ y)
        have hsplit' := Finset.add_sum_erase Finset.univ
          (fun x => ((parallelAgsiSubRun Φ η v n).count x : ℝ)) (Finset.mem_univ y)
        have hrest := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ.erase y) => hle x
        push_cast
        linarith
    obtain ⟨n, hn⟩ := exists_nat_gt ((Fintype.card X : ℝ) * M)
    have h1 := hcnt n
    have h2 : ∑ x, ((parallelAgsiSubRun Φ η v n).count x : ℝ) ≤ Fintype.card X * M := by
      have := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hb n x
      simpa [Finset.sum_const, nsmul_eq_mul] using this
    linarith
  unfold parallelAgsiSubPasses
  simp only [hex, ↓reduceDIte]
  exact ENat.natCast_lt_top _

theorem subCount_eq (h : parallelAgsiSubPasses Φ η v < ⊤) (x : X) :
    parallelAgsiSubCount Φ η v x =
      ((parallelAgsiSubRun Φ η v (parallelAgsiSubPasses Φ η v).toNat).count x : ℕ∞) := by
  classical
  unfold parallelAgsiSubCount
  simp only [h.ne, ↓reduceIte]

theorem subCount_lt_top_iff (x : X) :
    parallelAgsiSubCount Φ η v x < ⊤ ↔ parallelAgsiSubPasses Φ η v < ⊤ := by
  classical
  unfold parallelAgsiSubCount
  by_cases h : parallelAgsiSubPasses Φ η v = ⊤
  · simp [h]
  · simp only [h, ↓reduceIte, ENat.natCast_lt_top, true_iff]
    exact lt_top_iff_ne_top.2 h

end GuaranteedSubsol.ParallelAgsiResultProof
