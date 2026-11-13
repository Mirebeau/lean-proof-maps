/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.SubaddConcaveProof
public import LeanHJBAutoformalisation.GuaranteedSubsol.Rescale

/-!
# Strict causality implies sub-additivity of `Φ_α`: proof

Provider proof for the frozen anchor `GuaranteedSubsol.subAdditive_kruzkovOp_of_strictlyCausal`
(Prop. prop:strict_causal_implies_subadd), see `ANCHORS.md` and Subadd.tex.

* Case `α = 1` (`subAdditive_kruzkovOp_one`): for `η < δ` and small `t > 0`, the paper's
  steps (i) strict causality at level `Λ u - η`, (ii) monotonicity, (iii) `1`-sub-additivity give
  `Λ[u + t exp u] ≤ Λ u + exp(-η) t exp(Λ u)`. By Prop. prop:subadd_local, `Φ_1` is
  `exp(-η)`-sub-additive, and letting `η → δ` gives the constant `exp(-δ)`.
* General `α`: `Φ_α` of `Λ` is `Φ_1` of the rescaled operator `rescaleOp α Λ`, which is
  monotone, `1`-sub-additive and `δ/α`-strictly-causal (`Rescale.lean`).
-/

@[expose] public section

namespace GuaranteedSubsol.StrictCausalSubaddProof

open Filter Topology

variable {X : Type*}

/-- The local inequality of the paper's proof, at `α = 1`, for `t ≥ 0` with `C t ≤ δ - η`,
where `0 ≤ C` and `exp ∘ u ≤ C`. -/
theorem local_ineq {Λ : (X → ℝ) → ℝ} (hmono : Monotone Λ) (hsub1 : SubAdditive 1 Λ)
    {δ η : ℝ} (hcaus : StrictlyCausal δ Λ) (u : X → ℝ) {C t : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ y, Real.exp (u y) ≤ C) (ht : 0 ≤ t) (htC : C * t ≤ δ - η) :
    Λ (fun y => u y + t * Real.exp (u y)) ≤
      Λ u + Real.exp (-η) * t * Real.exp (Λ u) := by
  set w : X → ℝ := fun y => u y + t * Real.exp (u y) with hw_def
  set s := Λ u - η with hs_def
  -- a priori bound `Λ w ≤ Λ u + C t`
  have hw : Λ w ≤ s + δ := by
    calc Λ w ≤ Λ (fun y => u y + C * t) :=
          hmono fun y => by simp only [w]; nlinarith [hC y]
      _ ≤ Λ u + 1 * (C * t) := hsub1 u _ (mul_nonneg hC0 ht)
      _ ≤ s + δ := by rw [hs_def]; linarith
  -- (i) strict causality at level `s`
  have h1 : Λ w ≤ Λ (fun y => min (w y) s) := by
    have key := hcaus w (fun y => min (w y) s) s fun y => by simp
    rw [min_eq_left hw] at key
    rw [key]
    exact min_le_left _ _
  -- (ii) monotonicity
  have h2 : Λ (fun y => min (w y) s) ≤ Λ (fun y => u y + Real.exp s * t) := by
    refine hmono fun y => ?_
    by_cases hy : u y ≤ s
    · refine (min_le_left _ _).trans ?_
      simp only [w]
      nlinarith [Real.exp_le_exp.2 hy]
    · refine (min_le_right _ _).trans ?_
      nlinarith [Real.exp_pos s]
  -- (iii) `1`-sub-additivity
  have h3 : Λ (fun y => u y + Real.exp s * t) ≤ Λ u + 1 * (Real.exp s * t) :=
    hsub1 u _ (mul_nonneg (Real.exp_pos s).le ht)
  have he : Real.exp s = Real.exp (-η) * Real.exp (Λ u) := by
    rw [← Real.exp_add, hs_def]; ring_nf
  calc Λ w ≤ Λ u + 1 * (Real.exp s * t) := h1.trans (h2.trans h3)
    _ = Λ u + Real.exp (-η) * t * Real.exp (Λ u) := by rw [he]; ring

/-- Case `α = 1` with a constant `exp(-η)`, `η < δ`, via Prop. prop:subadd_local. -/
theorem subAdditive_kruzkovOp_one_of_lt [Finite X] {Λ : (X → ℝ) → ℝ} (hmono : Monotone Λ)
    (hsub1 : SubAdditive 1 Λ) {δ η : ℝ} (hηδ : η < δ) (hcaus : StrictlyCausal δ Λ) :
    SubAdditive (Real.exp (-η)) (kruzkovOp 1 Λ) := by
  refine SubaddLocalBwdProof.subAdditive_of_kruzkov_local hmono
    (SubaddConcaveProof.continuous_of_subAdditive_one hmono hsub1) one_pos (one_mul 1)
    (Real.exp_pos _).le fun u η' hη' => ?_
  obtain ⟨M, hM⟩ := (Set.finite_range u).bddAbove
  set C := Real.exp M
  have hC : ∀ y, Real.exp (u y) ≤ C := fun y => Real.exp_le_exp.2 (hM ⟨y, rfl⟩)
  have hC0 : 0 < C := Real.exp_pos M
  filter_upwards [Ioo_mem_nhdsGT (div_pos (sub_pos.2 hηδ) hC0)] with t ht
  have htC : C * t ≤ δ - η := by
    have := ht.2; rw [lt_div_iff₀ hC0] at this; linarith
  have := local_ineq hmono hsub1 hcaus u hC0.le hC ht.1.le htC
  simp only [one_mul]
  nlinarith [ht.1]

/-- Case `α = 1`: `Φ_1` is `exp(-δ)`-sub-additive, letting `η → δ`. -/
theorem subAdditive_kruzkovOp_one [Finite X] {Λ : (X → ℝ) → ℝ} (hmono : Monotone Λ)
    (hsub1 : SubAdditive 1 Λ) {δ : ℝ} (hcaus : StrictlyCausal δ Λ) :
    SubAdditive (Real.exp (-δ)) (kruzkovOp 1 Λ) := by
  intro v t ht
  have hlim : Tendsto (fun η => kruzkovOp 1 Λ v + Real.exp (-η) * t) (𝓝[<] δ)
      (𝓝 (kruzkovOp 1 Λ v + Real.exp (-δ) * t)) :=
    ((by fun_prop : Continuous fun η => kruzkovOp 1 Λ v + Real.exp (-η) * t).tendsto δ).mono_left
      nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun η hη =>
    subAdditive_kruzkovOp_one_of_lt hmono hsub1 hη hcaus v t ht)

/-- Prop. prop:strict_causal_implies_subadd, general `α > 0`, by rescaling to `α = 1`. The
hypothesis `δ > 0` of the paper is not needed. -/
theorem subAdditive_kruzkovOp_of_strictlyCausal [Finite X] {Λ : (X → ℝ) → ℝ}
    (hmono : Monotone Λ) (hsub1 : SubAdditive 1 Λ) {δ α : ℝ}
    (hcaus : StrictlyCausal δ Λ) (hα : 0 < α) :
    SubAdditive (Real.exp (-δ / α)) (kruzkovOp α Λ) := by
  have h := subAdditive_kruzkovOp_one (GuaranteedSubsol.Monotone.rescaleOp hα hmono)
    (hsub1.rescaleOp hα) (hcaus.rescaleOp hα)
  rwa [kruzkovOp_rescaleOp hα, mul_one, ← neg_div] at h

end GuaranteedSubsol.StrictCausalSubaddProof
