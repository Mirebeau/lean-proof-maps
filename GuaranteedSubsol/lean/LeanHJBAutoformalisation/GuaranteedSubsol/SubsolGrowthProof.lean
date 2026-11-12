/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.Axioms
import LeanHJBAutoformalisation.GuaranteedSubsol.CpastFormulationProof
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

/-!
# Growth of a sub-solution above a level: proof

Provider proof for the frozen anchor `GuaranteedSubsol.subsol_growth` (see `ANCHORS.md`): Prop.
prop:olu_ge_ustar (Complexity.tex). With `T = C_past + C'_Γ + (1+ε) t - C_Γ t`,
`v = T + C_Γ u` and `w = max {v, (1+ε) t}`, the function `w` is a super-solution on
`J = {u ≥ t}`: on `J ∩ I`, eq. (Lambda_max_u_t) gives `Λ w = Λ v ≤ v = w` by comparability;
on `J \ I`, `Λ w = ubd = Γ u ≤ u ≤ w`. Off `J`, `uSub ≤ (1+ε) u ≤ w`. The comparison principle
gives `uSub ≤ w`, which on `J` is the claimed bound.
-/

namespace GuaranteedSubsol.SubsolGrowthProof

theorem subsol_growth {X : Type*} {Λ Γ : (X → ℝ) → X → ℝ} {I : Set X} {ubd : X → ℝ}
    (hΛbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) (hΓbd : ∀ u, ∀ x ∉ I, Γ u x = ubd x)
    {Cpast CΓ CΓ' : ℝ} (hCpast : 0 ≤ Cpast) (hCΓ : 1 ≤ CΓ) (hCΓ' : 0 ≤ CΓ')
    (hmono : ∀ x ∈ I, Monotone (Λ · x)) (hadd : ∀ x ∈ I, AdditivelyInvariant (Λ · x))
    (hmem : ∀ x ∈ I, HasMemory Cpast (Λ · x))
    (hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (Λ · x) (Γ · x))
    (hcomp : ∀ J : Set X, HasComparisonPrinciple J Λ)
    {uSub : X → ℝ} (huSub : uSub ≤ Λ uSub) {u : X → ℝ} {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε)
    (hlow : ∀ x, u x < t → uSub x ≤ (1 + ε) * u x) (hΓu : ∀ x, Γ u x ≤ u x)
    (huΛ : ∀ x, u x ≤ Λ u x) :
    ∀ x, t ≤ u x → t + (uSub x - (1 + ε) * t - Cpast - CΓ') / CΓ ≤ u x := by
  set T : ℝ := Cpast + CΓ' + (1 + ε) * t - CΓ * t with hT
  set v : X → ℝ := fun y => CΓ * u y + T with hv
  set w : X → ℝ := fun y => max (v y) ((1 + ε) * t) with hw
  set J : Set X := {y | t ≤ u y} with hJ
  have hCΓ0 : (0 : ℝ) < CΓ := by linarith
  -- On `J`, `w = v` and `u ≤ v`.
  have hwv : ∀ y ∈ J, w y = v y := fun y hy => by
    have hy' : t ≤ u y := hy
    have : CΓ * t ≤ CΓ * u y := mul_le_mul_of_nonneg_left hy' hCΓ0.le
    exact max_eq_left (by simp only [hv, hT]; linarith)
  have huv : ∀ y ∈ J, u y ≤ v y := fun y hy => by
    have hy' : t ≤ u y := hy
    have : 0 ≤ (CΓ - 1) * (u y - t) := mul_nonneg (by linarith) (by linarith)
    have : 0 ≤ ε * t := mul_nonneg hε.le ht
    simp only [hv, hT]; linarith
  -- `Λ v x = Λ (C_Γ u) x + T` on `I`.
  have hΛv : ∀ x ∈ I, Λ v x = Λ (fun y => CΓ * u y) x + T := fun x hx =>
    hadd x hx (fun y => CΓ * u y) T
  have hsuper : ∀ x ∈ J, Λ w x ≤ w x := by
    intro x hxJ
    by_cases hxI : x ∈ I
    · have h1 := (hcmp x hxI u).1
      have h2 := (hcmp x hxI u).2
      have h3 : CΓ * u x ≤ CΓ * Λ u x := mul_le_mul_of_nonneg_left (huΛ x) hCΓ0.le
      have h4 : CΓ * Γ u x ≤ CΓ * u x := mul_le_mul_of_nonneg_left (hΓu x) hCΓ0.le
      have hx' : t ≤ u x := hxJ
      have h5 : CΓ * t ≤ CΓ * u x := mul_le_mul_of_nonneg_left hx' hCΓ0.le
      have hlev : (1 + ε) * t ≤ Λ v x - Cpast := by
        rw [hΛv x hxI]; simp only [hT]; linarith
      have heq := CpastFormulationProof.apply_eq_apply_max (hmono x hxI) (hadd x hxI)
        (hmem x hxI) v hlev
      have heq' : Λ w x = Λ v x := heq.symm
      rw [heq', hwv x hxJ, hΛv x hxI]
      simp only [hv]; linarith
    · rw [hΛbd w x hxI, ← hΓbd u x hxI]
      exact (hΓu x).trans ((huv x hxJ).trans (le_max_left _ _))
  have hoff : ∀ x ∉ J, uSub x ≤ w x := fun x hx => by
    have hx' : u x < t := lt_of_not_ge hx
    have h1 := hlow x hx'
    have h2 : (1 + ε) * u x ≤ (1 + ε) * t := mul_le_mul_of_nonneg_left hx'.le (by linarith)
    exact h1.trans (h2.trans (le_max_right _ _))
  have hle := hcomp J uSub w (fun x _ => huSub x) hsuper hoff
  intro x hx
  have h1 : uSub x ≤ v x := (hwv x hx) ▸ hle x
  simp only [hv, hT] at h1
  have h2 : (uSub x - (1 + ε) * t - Cpast - CΓ') / CΓ ≤ u x - t := by
    rw [div_le_iff₀ hCΓ0]; linarith
  linarith

end GuaranteedSubsol.SubsolGrowthProof
