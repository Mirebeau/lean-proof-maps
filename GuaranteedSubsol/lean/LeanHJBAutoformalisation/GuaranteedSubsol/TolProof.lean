/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.Axioms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Tolerance bounds: proofs of Corol. corol:tol

Provider proofs for the frozen anchors `GuaranteedSubsol.subSolution_of_subMultiplicative`,
`GuaranteedSubsol.superSolution_of_subMultiplicative`,
`GuaranteedSubsol.tol_of_subSolution_superSolution`,
`GuaranteedSubsol.tol_of_superSolution_subMultiplicative` and
`GuaranteedSubsol.tol_of_subSolution_subMultiplicative` (see `ANCHORS.md`), following
Corol. corol:tol of Complexity.tex. The two rescaling results turn an approximate sub-solution
(resp. super-solution) of a `ν`-sub-multiplicative operator into an exact one, by multiplying it
by `ν / (ν + ε)` (resp. `ν / (ν - ε)`); the tolerance bounds then follow from the comparison
principle.
-/

namespace GuaranteedSubsol.TolProof

theorem subSolution_of_subMultiplicative {X : Type*} {Λ : (X → ℝ) → ℝ} {ν : ℝ} (hν : 0 < ν)
    (hmul : SubMultiplicative ν Λ) {u : X → ℝ} {x : X} {ε : ℝ} (hε : 0 ≤ ε)
    (hu : u x - ε ≤ Λ u) :
    ν / (ν + ε) * u x ≤ Λ (fun y => ν / (ν + ε) * u y) := by
  set c := ν / (ν + ε) with hc
  have hνε : 0 < ν + ε := by linarith
  have hc0 : 0 ≤ c := by positivity
  have ht : 0 ≤ ε / ν := by positivity
  have h1 : c * (1 + ε / ν) = 1 := by rw [hc]; field_simp
  have h2 : ν * (ε / ν) = ε := by field_simp
  have key : (fun y => (1 + ε / ν) * (c * u y)) = u := by
    funext y
    rw [← mul_assoc, mul_comm (1 + ε / ν), h1, one_mul]
  have h := hmul (ε / ν) ht (fun y => c * u y)
  rw [key, h2] at h
  have h3 := mul_le_mul_of_nonneg_left (hu.trans h) hc0
  have h4 : c * ((1 + ε / ν) * Λ (fun y => c * u y) - ε) = Λ (fun y => c * u y) - c * ε := by
    rw [mul_sub, ← mul_assoc, h1, one_mul]
  nlinarith

theorem superSolution_of_subMultiplicative {X : Type*} {Λ : (X → ℝ) → ℝ} {ν : ℝ}
    (hmul : SubMultiplicative ν Λ) {u : X → ℝ} {x : X} {ε : ℝ} (hε : 0 ≤ ε) (hεν : ε < ν)
    (hu : Λ u ≤ u x + ε) :
    Λ (fun y => ν / (ν - ε) * u y) ≤ ν / (ν - ε) * u x := by
  have hνε : 0 < ν - ε := by linarith
  have hη : 0 ≤ ε / (ν - ε) := by positivity
  have h1 : ν / (ν - ε) = 1 + ε / (ν - ε) := by field_simp; ring
  have h2 : (1 + ε / (ν - ε)) * ε = ν * (ε / (ν - ε)) := by field_simp; ring
  rw [h1]
  have h := hmul (ε / (ν - ε)) hη u
  have h3 := mul_le_mul_of_nonneg_left hu (by linarith : (0 : ℝ) ≤ 1 + ε / (ν - ε))
  rw [mul_add, h2] at h3
  linarith

theorem tol_of_subSolution_superSolution {X : Type*} {Λ : (X → ℝ) → X → ℝ}
    (hmono : Monotone Λ) (hcomp : HasComparisonPrinciple Set.univ Λ)
    {uFix : X → ℝ} (hfix : Λ uFix = uFix) {ε : ℝ} (hε : 0 ≤ ε) {uSub uSup : X → ℝ}
    (hsub : uSub ≤ Λ uSub) (hsup : Λ uSup ≤ uSup) (htol : ∀ x, uSup x ≤ (1 + ε) * uSub x) :
    ∀ x, ((1 + ε)⁻¹ * uFix x ≤ uSub x ∧ uSub x ≤ uFix x) ∧
      (uFix x ≤ uSup x ∧ uSup x ≤ (1 + ε) * uFix x) ∧
      (0 ≤ Λ uSub x - uSub x ∧ Λ uSub x - uSub x ≤ ε * uFix x) ∧
      (0 ≤ uSup x - Λ uSup x ∧ uSup x - Λ uSup x ≤ ε * uFix x) := by
  replace hcomp : ∀ u v : X → ℝ, u ≤ Λ u → Λ v ≤ v → u ≤ v :=
    fun u v hu hv => hcomp u v (fun x _ => hu x) (fun x _ => hv x) (fun x hx => absurd trivial hx)
  intro x
  have hfix' : Λ uFix ≤ uFix := hfix.le
  have hfix'' : uFix ≤ Λ uFix := hfix.ge
  have a1 : uSub x ≤ uFix x := hcomp uSub uFix hsub hfix' x
  have a2 : uFix x ≤ uSup x := hcomp uFix uSup hfix'' hsup x
  have a3 : Λ uSub x ≤ uFix x := hcomp (Λ uSub) uFix (hmono hsub) hfix' x
  have a4 : uFix x ≤ Λ uSup x := hcomp uFix (Λ uSup) hfix'' (hmono hsup) x
  have a5 := htol x
  have a6 := hsub x
  have a7 := hsup x
  have hpos : 0 < 1 + ε := by linarith
  have b1 : uFix x ≤ (1 + ε) * uSub x := a2.trans a5
  have b2 : (1 + ε)⁻¹ * uFix x ≤ uSub x := by
    rw [inv_mul_le_iff₀ hpos]; exact b1
  have b3 : 0 ≤ ε * uFix x := by nlinarith
  refine ⟨⟨b2, a1⟩, ⟨a2, by nlinarith⟩, ⟨by linarith, by nlinarith⟩, ⟨by linarith, by nlinarith⟩⟩

theorem tol_of_superSolution_subMultiplicative {X : Type*} {Λ : (X → ℝ) → X → ℝ} {I : Set X}
    {ubd : X → ℝ} (hbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) (hubd : ∀ x ∉ I, 0 ≤ ubd x)
    {ν : ℝ} (hν : 0 < ν) (hmul : ∀ x ∈ I, SubMultiplicative ν (Λ · x))
    (hcomp : HasComparisonPrinciple Set.univ Λ)
    {uFix : X → ℝ} (hfix : Λ uFix = uFix) {ε : ℝ} (hε : 0 ≤ ε) {uSup : X → ℝ}
    (hsup : Λ uSup ≤ uSup) (htol : ∀ x, uSup x - Λ uSup x ≤ ε)
    (hsupbd : ∀ x ∉ I, uSup x = ubd x) :
    ∀ x, uFix x ≤ uSup x ∧ uSup x ≤ (1 + ε / ν) * uFix x := by
  replace hcomp : ∀ u v : X → ℝ, u ≤ Λ u → Λ v ≤ v → u ≤ v :=
    fun u v hu hv => hcomp u v (fun x _ => hu x) (fun x _ => hv x) (fun x hx => absurd trivial hx)
  have hνε : 0 < ν + ε := by linarith
  have hc0 : 0 < ν / (ν + ε) := by positivity
  have hc1 : ν / (ν + ε) ≤ 1 := by rw [div_le_one hνε]; linarith
  have hw : (fun y => ν / (ν + ε) * uSup y) ≤ Λ (fun y => ν / (ν + ε) * uSup y) := by
    intro x
    by_cases hx : x ∈ I
    · exact subSolution_of_subMultiplicative hν (hmul x hx) hε (by linarith [htol x])
    · change ν / (ν + ε) * uSup x ≤ _
      rw [hbd _ x hx, hsupbd x hx]
      nlinarith [hubd x hx]
  have hle := hcomp _ uFix hw hfix.le
  intro x
  refine ⟨hcomp uFix uSup hfix.ge hsup x, ?_⟩
  have h := hle x
  have h1 : (1 + ε / ν) * (ν / (ν + ε)) = 1 := by field_simp
  have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 1 + ε / ν)
  rw [← mul_assoc, h1, one_mul] at h2
  exact h2

theorem tol_of_subSolution_subMultiplicative {X : Type*} {Λ : (X → ℝ) → X → ℝ} {I : Set X}
    {ubd : X → ℝ} (hbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) (hubd : ∀ x ∉ I, 0 ≤ ubd x)
    {ν : ℝ} (hmul : ∀ x ∈ I, SubMultiplicative ν (Λ · x))
    (hcomp : HasComparisonPrinciple Set.univ Λ)
    {uFix : X → ℝ} (hfix : Λ uFix = uFix) {ε : ℝ} (hε : 0 ≤ ε) (hεν : ε < ν)
    {uSub : X → ℝ} (hsub : uSub ≤ Λ uSub) (htol : ∀ x, Λ uSub x - uSub x ≤ ε)
    (hsubbd : ∀ x ∉ I, uSub x = ubd x) :
    ∀ x, (1 - ε / ν) * uFix x ≤ uSub x ∧ uSub x ≤ uFix x := by
  replace hcomp : ∀ u v : X → ℝ, u ≤ Λ u → Λ v ≤ v → u ≤ v :=
    fun u v hu hv => hcomp u v (fun x _ => hu x) (fun x _ => hv x) (fun x hx => absurd trivial hx)
  have hν : 0 < ν := by linarith
  have hνε : 0 < ν - ε := by linarith
  have hc1 : 1 ≤ ν / (ν - ε) := by rw [one_le_div hνε]; linarith
  have hw : Λ (fun y => ν / (ν - ε) * uSub y) ≤ (fun y => ν / (ν - ε) * uSub y) := by
    intro x
    by_cases hx : x ∈ I
    · exact superSolution_of_subMultiplicative (hmul x hx) hε hεν (by linarith [htol x])
    · change _ ≤ ν / (ν - ε) * uSub x
      rw [hbd _ x hx, hsubbd x hx]
      nlinarith [hubd x hx]
  have hle := hcomp uFix _ hfix.ge hw
  intro x
  refine ⟨?_, hcomp uSub uFix hsub hfix.le x⟩
  have h := hle x
  have h1 : (1 - ε / ν) * (ν / (ν - ε)) = 1 := by field_simp
  have h0 : (0 : ℝ) ≤ 1 - ε / ν := by
    rw [sub_nonneg, div_le_one hν]; exact hεν.le
  have h2 := mul_le_mul_of_nonneg_left h h0
  rw [← mul_assoc, h1, one_mul] at h2
  exact h2

end GuaranteedSubsol.TolProof
