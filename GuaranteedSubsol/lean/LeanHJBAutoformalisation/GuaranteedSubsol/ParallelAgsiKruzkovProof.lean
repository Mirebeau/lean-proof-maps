/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ParallelAgsiCplxProof
import LeanHJBAutoformalisation.GuaranteedSubsol.ParallelAgsiSubProof

/-!
# Parallel AGSI applied to `Φ_α`: proofs

Provider proofs for the frozen anchors `GuaranteedSubsol.parallelAgsiRun_kruzkovOp_count_le` and
`GuaranteedSubsol.parallelAgsiSubRun_kruzkovOp_count_le`, see `ANCHORS.md`. The operator
`Φ_α = Global.kruzkovOp α Λ` is monotone for `α > 0` (`monotone_kruzkovOp`), whatever `Λ`, so the
complexity bounds for a monotone `ρ`-sub-additive operator apply.
-/

namespace GuaranteedSubsol.ParallelAgsiKruzkovProof

variable {X : Type*} {Λ : (X → ℝ) → X → ℝ} {α : ℝ}

theorem monotone_global_kruzkovOp (hα : 0 < α) : Monotone (Global.kruzkovOp α Λ) :=
  fun _ _ h x => KruzkovProof.monotone_kruzkovOp hα (Λ · x) h

theorem parallelAgsiRun_kruzkovOp_count_le [Finite X] {ρ : ℝ} (hα : 0 < α) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hsub : ∀ x, SubAdditive ρ (kruzkovOp α (Λ · x))) {η C : ℝ} (hη : 0 < η)
    {v : X → ℝ} (hv : Global.kruzkovOp α Λ v ≤ v)
    (hvC : ∀ x, v x - Global.kruzkovOp α Λ v x ≤ C) (n : ℕ) (x : X) :
    ((parallelAgsiRun (Global.kruzkovOp α Λ) η v n).count x : ℝ) ≤
      ⌈Real.log ((1 - ρ) * C / η) / (-Real.log ρ)⌉₊ + 2 / (1 - ρ) ^ 2 :=
  ParallelAgsiCplxProof.count_le_of_subAdditive (monotone_global_kruzkovOp hα) hρ0 hρ1 hsub hη
    hv hvC n x

theorem parallelAgsiSubRun_kruzkovOp_count_le [Finite X] {ρ : ℝ} (hα : 0 < α) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hsub : ∀ x, SubAdditive ρ (kruzkovOp α (Λ · x))) {η C : ℝ} (hη : 0 < η)
    {v : X → ℝ} (hv : v ≤ Global.kruzkovOp α Λ v)
    (hvC : ∀ x, Global.kruzkovOp α Λ v x - v x ≤ C) (n : ℕ) (x : X) :
    ((parallelAgsiSubRun (Global.kruzkovOp α Λ) η v n).count x : ℝ) ≤
      ⌈Real.log ((1 - ρ) * C / η) / (-Real.log ρ)⌉₊ + 2 / (1 - ρ) ^ 2 :=
  ParallelAgsiSubProof.count_le_of_subAdditive (monotone_global_kruzkovOp hα) hρ0 hρ1 hsub hη
    hv hvC n x

end GuaranteedSubsol.ParallelAgsiKruzkovProof
