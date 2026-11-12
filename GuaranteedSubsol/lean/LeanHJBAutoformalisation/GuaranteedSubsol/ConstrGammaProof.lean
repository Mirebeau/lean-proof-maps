/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ConstrGamma
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Construction of `Γ` from `Λ`: proof

Provider proof for the frozen anchor `GuaranteedSubsol.constrGammaLoc` (see `ANCHORS.md`), following
the proof of Prop. prop:constr_Gamma (Effective.tex), in scalar form at an interior point.
-/

namespace GuaranteedSubsol.ConstrGamma

variable {X : Type*} {Λ : (X → ℝ) → ℝ} {V : Finset X}

/-- Translation commutes with the minimum over `V`. -/
theorem inf'_add (hV : V.Nonempty) (u : X → ℝ) (t : ℝ) :
    V.inf' hV (fun y => u y + t) = V.inf' hV u + t :=
  (Finset.apply_inf'_eq_inf'_comp hV (fun a => a + t)
    fun a b => (min_add_add_right a b t).symm).symm

/-- Multiplication by `C ≥ 0` commutes with the minimum over `V`. -/
theorem inf'_mul (hV : V.Nonempty) (u : X → ℝ) {C : ℝ} (hC : 0 ≤ C) :
    V.inf' hV (fun y => C * u y) = C * V.inf' hV u :=
  (Finset.apply_inf'_eq_inf'_comp hV (fun a => C * a)
    fun a b => mul_min_of_nonneg a b hC).symm

/-- Truncation from above commutes with the minimum over `V`. -/
theorem inf'_min (hV : V.Nonempty) (u : X → ℝ) (t : ℝ) :
    V.inf' hV (fun y => min (u y) t) = min (V.inf' hV u) t :=
  (Finset.apply_inf'_eq_inf'_comp hV (fun a => min a t)
    fun a b => inf_inf_distrib_right a b t).symm

/-- The dependency bound, in terms of the minimum over `V`: `Λ u ≤ C + min_V u`. -/
theorem le_add_inf' {C : ℝ} (hV : V.Nonempty) (hdep : HasDependency C V Λ) (u : X → ℝ) :
    Λ u ≤ C + V.inf' hV u := by
  obtain ⟨y, hy, hyeq⟩ := V.exists_mem_eq_inf' hV u
  rw [hyeq]
  exact hdep.2 u y (Finset.mem_coe.2 hy)

/-- One half of the memory property: if `t + C < Λ u` and `max {u,t} = max {v,t}`,
then `Λ u = Λ v`. -/
theorem eq_of_lt {C : ℝ} {u v : X → ℝ} {t : ℝ} (hdep : HasDependency C V Λ)
    (h : ∀ y, max (u y) t = max (v y) t) (hlt : t + C < Λ u) : Λ u = Λ v := by
  refine hdep.1 u v fun y hy => ?_
  have hty : t < u y := by linarith [hdep.2 u y hy]
  have hmax := h y
  rw [max_eq_left hty.le] at hmax
  rcases le_total (v y) t with hvt | hvt
  · rw [max_eq_right hvt] at hmax
    linarith
  · rw [max_eq_left hvt] at hmax
    exact hmax

/-- `Λ` has `C`-memory when it has `C`-dependency. -/
theorem hasMemory {C : ℝ} (hdep : HasDependency C V Λ) : HasMemory C Λ := by
  intro u v t h
  by_cases h1 : t + C < Λ u
  · rw [eq_of_lt hdep h h1]
  by_cases h2 : t + C < Λ v
  · rw [eq_of_lt hdep (fun y => (h y).symm) h2]
  rw [max_eq_right (not_lt.1 h1), max_eq_right (not_lt.1 h2)]

/-- An elementary identity behind strict causality: if `δ ≤ c`, then
`min {c + a, t + δ} = min {c + min {a,t}, t + δ}`. -/
theorem min_add_min {a c t δ : ℝ} (hc : δ ≤ c) :
    min (c + a) (t + δ) = min (c + min a t) (t + δ) := by
  rcases le_total a t with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, min_eq_right (by linarith), min_eq_right (by linarith)]

/-- `constrGamma Λ V hV` underestimates `Λ`. -/
theorem le_self (hV : V.Nonempty) (hmono : Monotone Λ) (hadd : AdditivelyInvariant Λ)
    (hst : HasStencil V Λ) (u : X → ℝ) : constrGamma Λ V hV u ≤ Λ u := by
  set m := V.inf' hV u
  have h1 : constrGamma Λ V hV u = Λ (fun y => (0 : X → ℝ) y + m) := (hadd 0 m).symm
  have h2 : Λ (fun y => max (u y) m) = Λ u :=
    hst _ _ fun y hy => max_eq_left (Finset.inf'_le u (Finset.mem_coe.1 hy))
  rw [h1, ← h2]
  exact hmono fun y => by simp

/-- `Γ u := Λ[0] + min_V u` is monotone. -/
theorem monotone (hV : V.Nonempty) : Monotone (constrGamma Λ V hV) := fun u v h => by
  unfold constrGamma
  have hinf : V.inf' hV u ≤ V.inf' hV v :=
    Finset.le_inf' hV v fun y hy => (Finset.inf'_le u hy).trans (h y)
  linarith

end GuaranteedSubsol.ConstrGamma

namespace GuaranteedSubsol

open ConstrGamma in
theorem ConstrGamma.loc {X : Type*} {Λ : (X → ℝ) → ℝ} {V : Finset X} (hV : V.Nonempty)
    {Cpast δ : ℝ} (hCpast : 0 ≤ Cpast) (hδ : 0 < δ) (hmono : Monotone Λ)
    (hadd : AdditivelyInvariant Λ) (hΛ0 : δ ≤ Λ 0) (hdep : HasDependency Cpast V Λ) :
    HasMemory Cpast Λ ∧ AdditivelyInvariant (constrGamma Λ V hV) ∧
      StrictlyCausal δ (constrGamma Λ V hV) ∧ (∀ u, constrGamma Λ V hV u ≤ Λ u) ∧
      Comparable (Cpast / δ) (Cpast * (Cpast / δ) - δ) Λ (constrGamma Λ V hV) := by
  refine ⟨hasMemory hdep, fun u t => ?_, fun u v t h => ?_, le_self hV hmono hadd hdep.1,
    fun u => ?_⟩
  · simp only [constrGamma, inf'_add]
    ring
  · simp only [constrGamma]
    rw [min_add_min hΛ0, ← inf'_min, min_add_min (a := V.inf' hV v) hΛ0, ← inf'_min]
    simp only [h]
  · set C := Cpast / δ
    have hC : 0 ≤ C := div_nonneg hCpast hδ.le
    have hCδ : C * δ = Cpast := div_mul_cancel₀ Cpast hδ.ne'
    have hΓ : constrGamma Λ V hV (fun y => C * u y) = Λ 0 + C * V.inf' hV u := by
      simp only [constrGamma, inf'_mul hV u hC]
    have hb := le_add_inf' hV hdep u
    have hbC := le_add_inf' hV hdep (fun y => C * u y)
    rw [inf'_mul hV u hC] at hbC
    have hle := le_self hV hmono hadd hdep.1 (fun y => C * u y)
    have h1 := mul_le_mul_of_nonneg_left hb hC
    have h2 := mul_le_mul_of_nonneg_left hΛ0 hC
    refine ⟨?_, ?_⟩
    · rw [hΓ] at hle
      rw [mul_add] at h1
      linarith
    · simp only [constrGamma, mul_add]
      linarith

end GuaranteedSubsol
