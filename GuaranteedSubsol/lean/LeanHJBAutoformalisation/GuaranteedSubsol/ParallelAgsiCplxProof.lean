/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ParallelAgsiProof
import LeanHJBAutoformalisation.GuaranteedSubsol.ContractivityProof
import LeanHJBAutoformalisation.GuaranteedSubsol.ComparisonProof
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Parallel AGSI: number of updates per point (proof)

Provider proof for the frozen anchor `GuaranteedSubsol.parallelAgsiRun_count_le_of_subAdditive`
(Prop. prop:cplx_agsi_parallel, super-solution case), see `ANCHORS.md` and AGSI2.tex. We follow
the paper's proof, with `v_n` the map after `n` passes.

* `v_n - Φ v_n ≤ B_n := ρ^n C + η/(1-ρ)` (from `C_{n+1} ≤ ρ C_n + η`, `step_bound`), and
  `ρ^N C ≤ η/(1-ρ)` for `N := ⌈ln((1-ρ)C/η)/(-ln ρ)⌉₊` (`pow_mul_le`).
* By the comparison principle (Prop. prop:comparison_Phi) and the fixed point `v_*` of `Φ`:
  `v_* ≤ v_n` for all `n`, and `v_N ≤ v_* + ξ` with `ξ := B_N/(1-ρ) ≤ 2η/(1-ρ)²`.
* Each update at `x` lowers `v(x)` by more than `η`, so at most `ξ/η ≤ 2/(1-ρ)²` updates occur
  at `x` after pass `N`, and at most `N` before (one per pass).
-/

namespace GuaranteedSubsol.ParallelAgsiCplxProof

open ParallelAgsiProof

variable {X : Type*} {Φ : (X → ℝ) → X → ℝ} {ρ η : ℝ}

/-- One pass: if `0 ≤ v - Φ v ≤ c` with `c ≥ 0`, then afterwards `v - Φ v ≤ ρ c + η`. -/
theorem step_bound (hmono : Monotone Φ) (hsub : ∀ x, SubAdditive ρ (Φ · x)) (hη : 0 ≤ η)
    {s : ParallelAgsiState X} (hs : Φ s.v ≤ s.v) {c : ℝ} (hc : 0 ≤ c)
    (hsc : ∀ x, s.v x - Φ s.v x ≤ c) (x : X) :
    (parallelAgsiStep Φ η s).v x - Φ (parallelAgsiStep Φ η s).v x ≤ ρ * c + η := by
  set u := s.v
  set u' := (parallelAgsiStep Φ η s).v
  have h1 : ∀ y, Φ u y ≤ u' y := fun y => by
    simp only [u', step_v]
    split_ifs
    · exact le_rfl
    · exact hs y
  have h2 : ∀ y, u' y ≤ Φ u y + η := fun y => by
    simp only [u', step_v]
    split_ifs with h
    · linarith
    · push Not at h; linarith
  have h3 : u ≤ fun y => u' y + c := fun y => by linarith [hsc y, h1 y]
  have h4 := hmono h3 x
  have h5 := hsub x u' c hc
  simp only at h5
  linarith [h2 x]

/-- `ρ^N C ≤ η/(1-ρ)` for `N := ⌈ln((1-ρ)C/η)/(-ln ρ)⌉₊`. -/
theorem pow_mul_le (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hη : 0 < η) {C : ℝ} (hC : 0 ≤ C) :
    ρ ^ ⌈Real.log ((1 - ρ) * C / η) / (-Real.log ρ)⌉₊ * C ≤ η / (1 - ρ) := by
  have h1ρ : 0 < 1 - ρ := by linarith
  rcases hC.eq_or_lt with hC0 | hC0
  · rw [← hC0, mul_zero]; positivity
  set N := ⌈Real.log ((1 - ρ) * C / η) / (-Real.log ρ)⌉₊
  set a := (1 - ρ) * C / η
  have ha : 0 < a := by positivity
  have hlog : 0 < -Real.log ρ := neg_pos.2 (Real.log_neg hρ0 hρ1)
  have hN : Real.log a ≤ N * -Real.log ρ :=
    (div_le_iff₀ hlog).1 (Nat.le_ceil _)
  have hpow : ρ ^ N ≤ a⁻¹ := by
    rw [← Real.exp_log (pow_pos hρ0 N), Real.log_pow, ← Real.exp_log (inv_pos.2 ha),
      Real.log_inv]
    exact Real.exp_le_exp.2 (by linarith)
  calc ρ ^ N * C ≤ a⁻¹ * C := mul_le_mul_of_nonneg_right hpow hC
    _ = η / (1 - ρ) := by simp only [a]; field_simp

/-- Prop. prop:cplx_agsi_parallel, super-solution case: at most `N''_Φ` updates at each point. -/
theorem count_le_of_subAdditive [Finite X] (hmono : Monotone Φ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hsub : ∀ x, SubAdditive ρ (Φ · x)) {C : ℝ} (hη : 0 < η) {v : X → ℝ}
    (hv : Φ v ≤ v) (hvC : ∀ x, v x - Φ v x ≤ C) (n : ℕ) (x : X) :
    (((parallelAgsiStep Φ η)^[n] ⟨v, 0⟩).count x : ℝ) ≤
      ⌈Real.log ((1 - ρ) * C / η) / (-Real.log ρ)⌉₊ + 2 / (1 - ρ) ^ 2 := by
  have := Fintype.ofFinite X
  have h1ρ : 0 < 1 - ρ := by linarith
  set s : ℕ → ParallelAgsiState X := fun n => (parallelAgsiStep Φ η)^[n] ⟨v, 0⟩ with hs_def
  have hsucc : ∀ n, s (n + 1) = parallelAgsiStep Φ η (s n) := fun n =>
    Function.iterate_succ_apply' _ _ _
  have hsup : ∀ n, Φ (s n).v ≤ (s n).v := fun n => superSolution hmono η (s := ⟨v, 0⟩) hv n
  have hC : 0 ≤ C := by linarith [hvC x, hv x]
  -- `v_n - Φ v_n ≤ B_n`
  set B : ℕ → ℝ := fun n => ρ ^ n * C + η / (1 - ρ) with hB
  have hB0 : ∀ n, 0 ≤ B n := fun n => by simp only [B]; positivity
  have hbound : ∀ n y, (s n).v y - Φ (s n).v y ≤ B n := by
    intro n
    induction n with
    | zero =>
      intro y
      have : 0 ≤ η / (1 - ρ) := by positivity
      simp only [s, B, Function.iterate_zero, id, pow_zero, one_mul]
      linarith [hvC y]
    | succ n ih =>
      intro y
      rw [hsucc]
      refine (step_bound hmono hsub hη.le (hsup n) (hB0 n) ih y).trans (le_of_eq ?_)
      simp only [B]; field_simp; ring
  set N := ⌈Real.log ((1 - ρ) * C / η) / (-Real.log ρ)⌉₊
  have hBN : B N ≤ 2 * η / (1 - ρ) := by
    have : ρ ^ N * C ≤ η / (1 - ρ) := pow_mul_le hρ0 hρ1 hη hC
    simp only [B]
    have e : 2 * η / (1 - ρ) = η / (1 - ρ) + η / (1 - ρ) := by ring
    rw [e]; linarith
  -- the fixed point `v_*` and the comparison principle
  obtain ⟨vFix, hfix, -, -⟩ :=
    ContractivityProof.existsUnique_fixedPoint_of_subAdditive hρ1 hmono hsub
  have hmono' : ∀ y ∈ (Set.univ : Set X), Monotone (Φ · y) := fun y _ _ _ h => hmono h y
  have hsub' : ∀ y ∈ (Set.univ : Set X), SubAdditive ρ (Φ · y) := fun y _ => hsub y
  have hlow : ∀ n, vFix ≤ (s n).v := fun n =>
    ComparisonProof.le_of_comparison hρ1 hmono' hsub'
      (fun y _ => by rw [hfix]; linarith [hsup n y]) (fun y hy => absurd trivial hy)
  set ξ := B N / (1 - ρ)
  have hξ : 0 ≤ ξ := div_nonneg (hB0 N) h1ρ.le
  have hup : (s N).v ≤ fun y => vFix y + ξ :=
    ComparisonProof.le_of_comparison hρ1 hmono' hsub' (fun y _ => by
      have h5 := hsub y vFix ξ hξ
      simp only at h5
      rw [hfix] at h5
      have : B N = (1 - ρ) * ξ := by simp only [ξ]; field_simp
      linarith [hbound N y]) (fun y hy => absurd trivial hy)
  -- the potential `v x + η count x` is non-increasing
  have hpot : ∀ m, (s (N + m)).v x + η * ((s (N + m)).count x : ℝ) ≤
      (s N).v x + η * ((s N).count x : ℝ) := by
    intro m
    induction m with
    | zero => exact le_rfl
    | succ m ih =>
      rw [← add_assoc, hsucc]
      exact (step_potential_le _ x).trans ih
  -- at most one update per pass
  have hcnt : ∀ n, ((s n).count x : ℝ) ≤ n := by
    intro n
    induction n with
    | zero => simp [s]
    | succ n ih =>
      rw [hsucc, step_count]
      split_ifs <;> push_cast <;> linarith
  have h2 : 0 ≤ 2 / (1 - ρ) ^ 2 := by positivity
  rcases le_or_gt n N with hn | hn
  · have := hcnt n
    have : (n : ℝ) ≤ N := by exact_mod_cast hn
    linarith
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn.le
    have hp := hpot m
    have hl := hlow (N + m) x
    have hu := hup x
    have hcN := hcnt N
    -- `η (count_{N+m} - count_N) ≤ ξ ≤ 2η/(1-ρ)²`
    have hξ2 : ξ ≤ η * (2 / (1 - ρ) ^ 2) := by
      simp only [ξ]
      rw [div_le_iff₀ h1ρ]
      have e : η * (2 / (1 - ρ) ^ 2) * (1 - ρ) = 2 * η / (1 - ρ) := by field_simp
      rw [e]; exact hBN
    have key : η * (((s (N + m)).count x : ℝ) - ((s N).count x : ℝ)) ≤
        η * (2 / (1 - ρ) ^ 2) := by
      simp only at hu; nlinarith
    have := le_of_mul_le_mul_left key hη
    simp only [s] at this hcN ⊢
    linarith

end GuaranteedSubsol.ParallelAgsiCplxProof
