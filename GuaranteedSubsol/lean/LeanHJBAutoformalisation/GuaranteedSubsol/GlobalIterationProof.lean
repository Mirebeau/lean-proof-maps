/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.GlobalIteration
import LeanHJBAutoformalisation.GuaranteedSubsol.Axioms
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Global iteration: proofs

Provider proofs for the frozen anchors on Algorithm algo:global_iteration, see `ANCHORS.md`.

* One step (`step_super`, `step_sub`): if `0 ≤ v - Φ v ≤ c` with `c ≥ 0`, then `w := Φ v`
  satisfies `0 ≤ w - Φ w ≤ ρ c`, by monotonicity and `ρ`-sub-additivity
  (`Φ v ≤ Φ (Φ v + c) ≤ Φ (Φ v) + ρ c`); likewise for the sub-solution variant.
* Along the run, the residual is at most `max (ρ^n C) η`: while the stopping criterion fails, the
  bound `η` is not attained, so the residual is at most `ρ^n C`, and one more step multiplies it by
  `ρ`; once the criterion holds, the run stops.
* Termination: `ρ^N C ≤ η` for `N := ⌈ln(C/η)/(-ln ρ)⌉₊` (`pow_mul_le`).
-/

namespace GuaranteedSubsol.GlobalIterationProof

variable {X : Type*} {Φ : (X → ℝ) → X → ℝ} {ρ η : ℝ}

theorem run_succ (v : X → ℝ) (n : ℕ) :
    globalIterRun Φ η v (n + 1) = globalIterStep Φ η (globalIterRun Φ η v n) :=
  Function.iterate_succ_apply' _ _ _

theorem subRun_succ (v : X → ℝ) (n : ℕ) :
    globalIterSubRun Φ η v (n + 1) = globalIterSubStep Φ η (globalIterSubRun Φ η v n) :=
  Function.iterate_succ_apply' _ _ _

theorem step_eq (v : X → ℝ) :
    globalIterStep Φ η v = v ∨ globalIterStep Φ η v = Φ v := by
  classical
  unfold globalIterStep; split_ifs <;> simp

theorem subStep_eq (v : X → ℝ) :
    globalIterSubStep Φ η v = v ∨ globalIterSubStep Φ η v = Φ v := by
  classical
  unfold globalIterSubStep; split_ifs <;> simp

theorem step_of_not (v : X → ℝ) (h : ¬∀ x, v x - Φ v x ≤ η) : globalIterStep Φ η v = Φ v := by
  classical
  simp only [globalIterStep, h, ↓reduceIte]

theorem subStep_of_not (v : X → ℝ) (h : ¬∀ x, Φ v x - v x ≤ η) :
    globalIterSubStep Φ η v = Φ v := by
  classical
  simp only [globalIterSubStep, h, ↓reduceIte]

theorem step_of_done (v : X → ℝ) (h : ∀ x, v x - Φ v x ≤ η) : globalIterStep Φ η v = v := by
  classical
  simp only [globalIterStep, h, implies_true, ↓reduceIte]

theorem subStep_of_done (v : X → ℝ) (h : ∀ x, Φ v x - v x ≤ η) : globalIterSubStep Φ η v = v := by
  classical
  simp only [globalIterSubStep, h, implies_true, ↓reduceIte]

/-- One contraction step, super-solution version. -/
theorem step_super (hmono : Monotone Φ) (hsub : ∀ x, SubAdditive ρ (Φ · x)) {v : X → ℝ}
    (hv : Φ v ≤ v) {c : ℝ} (hc : 0 ≤ c) (hvc : ∀ x, v x - Φ v x ≤ c) :
    Φ (Φ v) ≤ Φ v ∧ ∀ x, Φ v x - Φ (Φ v) x ≤ ρ * c := by
  refine ⟨hmono hv, fun x => ?_⟩
  have h1 : v ≤ fun y => Φ v y + c := fun y => by linarith [hvc y]
  have h2 := hmono h1 x
  have h3 := hsub x (Φ v) c hc
  simp only at h3
  linarith

/-- One contraction step, sub-solution variant. -/
theorem step_sub (hmono : Monotone Φ) (hsub : ∀ x, SubAdditive ρ (Φ · x)) {v : X → ℝ}
    (hv : v ≤ Φ v) {c : ℝ} (hc : 0 ≤ c) (hvc : ∀ x, Φ v x - v x ≤ c) :
    Φ v ≤ Φ (Φ v) ∧ ∀ x, Φ (Φ v) x - Φ v x ≤ ρ * c := by
  refine ⟨hmono hv, fun x => ?_⟩
  have h1 : Φ v ≤ fun y => v y + c := fun y => by linarith [hvc y]
  have h2 := hmono h1 x
  have h3 := hsub x v c hc
  simp only at h3
  linarith

theorem superSolution (hmono : Monotone Φ) (η : ℝ) {v : X → ℝ} (hv : Φ v ≤ v) (n : ℕ) :
    Φ (globalIterRun Φ η v n) ≤ globalIterRun Φ η v n := by
  induction n with
  | zero => exact hv
  | succ n ih =>
    rw [run_succ]
    rcases step_eq (Φ := Φ) (η := η) (globalIterRun Φ η v n) with h | h <;> rw [h]
    · exact ih
    · exact hmono ih

theorem subSolution (hmono : Monotone Φ) (η : ℝ) {v : X → ℝ} (hv : v ≤ Φ v) (n : ℕ) :
    globalIterSubRun Φ η v n ≤ Φ (globalIterSubRun Φ η v n) := by
  induction n with
  | zero => exact hv
  | succ n ih =>
    rw [subRun_succ]
    rcases subStep_eq (Φ := Φ) (η := η) (globalIterSubRun Φ η v n) with h | h <;> rw [h]
    · exact ih
    · exact hmono ih

theorem le_pow_mul (hmono : Monotone Φ) (hρ : 0 ≤ ρ) (hsub : ∀ x, SubAdditive ρ (Φ · x))
    (η : ℝ) {C : ℝ} {v : X → ℝ} (hv : Φ v ≤ v) (hvC : ∀ x, v x - Φ v x ≤ C) (n : ℕ) (x : X) :
    globalIterRun Φ η v n x - Φ (globalIterRun Φ η v n) x ≤ max (ρ ^ n * C) η := by
  have hC : 0 ≤ C := (sub_nonneg.2 (hv x)).trans (hvC x)
  revert x
  induction n with
  | zero => intro x; simp only [pow_zero, one_mul]; exact (hvC x).trans (le_max_left _ _)
  | succ n ih =>
    intro x
    set r := globalIterRun Φ η v n
    rw [run_succ]
    by_cases hdone : ∀ y, r y - Φ r y ≤ η
    · rw [step_of_done r hdone]; exact (hdone x).trans (le_max_right _ _)
    · rw [step_of_not r hdone]
      -- the bound `η` is not attained, so the residual is at most `ρ^n C`
      have hrn : ∀ y, r y - Φ r y ≤ ρ ^ n * C := by
        push Not at hdone
        obtain ⟨z, hz⟩ := hdone
        have hmax : max (ρ ^ n * C) η = ρ ^ n * C :=
          max_eq_left (by by_contra h; push Not at h; linarith [ih z, max_eq_right h.le])
        exact fun y => hmax ▸ ih y
      have := (step_super hmono hsub (superSolution hmono η hv n)
        (mul_nonneg (pow_nonneg hρ n) hC) hrn).2 x
      rw [pow_succ]
      refine this.trans (le_of_eq_of_le ?_ (le_max_left _ _))
      ring

theorem subRun_le_pow_mul (hmono : Monotone Φ) (hρ : 0 ≤ ρ) (hsub : ∀ x, SubAdditive ρ (Φ · x))
    (η : ℝ) {C : ℝ} {v : X → ℝ} (hv : v ≤ Φ v) (hvC : ∀ x, Φ v x - v x ≤ C) (n : ℕ) (x : X) :
    Φ (globalIterSubRun Φ η v n) x - globalIterSubRun Φ η v n x ≤ max (ρ ^ n * C) η := by
  have hC : 0 ≤ C := (sub_nonneg.2 (hv x)).trans (hvC x)
  revert x
  induction n with
  | zero => intro x; simp only [pow_zero, one_mul]; exact (hvC x).trans (le_max_left _ _)
  | succ n ih =>
    intro x
    set r := globalIterSubRun Φ η v n
    rw [subRun_succ]
    by_cases hdone : ∀ y, Φ r y - r y ≤ η
    · rw [subStep_of_done r hdone]; exact (hdone x).trans (le_max_right _ _)
    · rw [subStep_of_not r hdone]
      have hrn : ∀ y, Φ r y - r y ≤ ρ ^ n * C := by
        push Not at hdone
        obtain ⟨z, hz⟩ := hdone
        have hmax : max (ρ ^ n * C) η = ρ ^ n * C :=
          max_eq_left (by by_contra h; push Not at h; linarith [ih z, max_eq_right h.le])
        exact fun y => hmax ▸ ih y
      have := (step_sub hmono hsub (subSolution hmono η hv n)
        (mul_nonneg (pow_nonneg hρ n) hC) hrn).2 x
      rw [pow_succ]
      refine this.trans (le_of_eq_of_le ?_ (le_max_left _ _))
      ring

/-- `ρ^N C ≤ η` for `N := ⌈ln(C/η)/(-ln ρ)⌉₊`. -/
theorem pow_mul_le (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hη : 0 < η) (C : ℝ) :
    ρ ^ ⌈Real.log (C / η) / (-Real.log ρ)⌉₊ * C ≤ η := by
  set N := ⌈Real.log (C / η) / (-Real.log ρ)⌉₊
  rcases le_or_gt C 0 with hC | hC
  · nlinarith [pow_pos hρ0 N]
  set a := C / η
  have ha : 0 < a := div_pos hC hη
  have hlog : 0 < -Real.log ρ := neg_pos.2 (Real.log_neg hρ0 hρ1)
  have hN : Real.log a ≤ N * -Real.log ρ := (div_le_iff₀ hlog).1 (Nat.le_ceil _)
  have hpow : ρ ^ N ≤ a⁻¹ := by
    rw [← Real.exp_log (pow_pos hρ0 N), Real.log_pow, ← Real.exp_log (inv_pos.2 ha),
      Real.log_inv]
    exact Real.exp_le_exp.2 (by linarith)
  calc ρ ^ N * C ≤ a⁻¹ * C := mul_le_mul_of_nonneg_right hpow hC.le
    _ = η := by simp only [a]; field_simp

theorem terminates (hmono : Monotone Φ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hsub : ∀ x, SubAdditive ρ (Φ · x)) {C : ℝ} (hη : 0 < η) {v : X → ℝ} (hv : Φ v ≤ v)
    (hvC : ∀ x, v x - Φ v x ≤ C) :
    ∃ n ≤ ⌈Real.log (C / η) / (-Real.log ρ)⌉₊, ∀ x,
      globalIterRun Φ η v n x - Φ (globalIterRun Φ η v n) x ≤ η :=
  ⟨_, le_rfl, fun x => (le_pow_mul hmono hρ0.le hsub η hv hvC _ x).trans
    (max_le (pow_mul_le hρ0 hρ1 hη C) le_rfl)⟩

theorem subRun_terminates (hmono : Monotone Φ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hsub : ∀ x, SubAdditive ρ (Φ · x)) {C : ℝ} (hη : 0 < η) {v : X → ℝ} (hv : v ≤ Φ v)
    (hvC : ∀ x, Φ v x - v x ≤ C) :
    ∃ n ≤ ⌈Real.log (C / η) / (-Real.log ρ)⌉₊, ∀ x,
      Φ (globalIterSubRun Φ η v n) x - globalIterSubRun Φ η v n x ≤ η :=
  ⟨_, le_rfl, fun x => (subRun_le_pow_mul hmono hρ0.le hsub η hv hvC _ x).trans
    (max_le (pow_mul_le hρ0 hρ1 hη C) le_rfl)⟩

end GuaranteedSubsol.GlobalIterationProof
