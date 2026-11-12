/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.SubaddConcaveProof
import LeanHJBAutoformalisation.GuaranteedSubsol.MonMinMaxProof
import LeanHJBAutoformalisation.GuaranteedSubsol.Rescale

/-!
# Causality implies sub-additivity of `Φ_α`: proof

Provider proof for the frozen anchor `GuaranteedSubsol.subAdditive_kruzkovOp_of_causal`
(Prop. prop:causal_implies_subadd), see `ANCHORS.md` and Subadd.tex. Notation:
`c₁ := 1 - exp(-C)`, `C₁ := (c₁/C) exp(-C)`, `ρ := 1 - (ν/C) c₁`.

* Case `α = 1`: we show (subadd_local_x) and conclude by Prop. prop:subadd_local. By additive
  invariance, `Λ u = 0`. With `u_t := u + t exp u` and, for `η > 0`,
  `v_t := (1 + c₁ t/C) u + t + C₁ t² + η t`, Corol. corol:mon_min_max with `t₀ := -C` and a
  small `t₁ := ε(η) > 0` gives `Λ u_t ≤ Λ v_t ≤ ρ t + η t + C₁ t²`.
  The paper takes `η = 0` and `t₁ = 0`, but `t₁ ≥ Λ u_t` is needed and in general
  `Λ u_t > 0`: the slack `η t` fixes this, at no cost in the `o(t)` estimate.
* General `α`: `Φ_α` of `Λ` is `Φ_1` of `rescaleOp α Λ`, which has memory `C/α` and is
  `ν/α`-sub-multiplicative, and `(ν/α)/(C/α) = ν/C`.
-/

namespace GuaranteedSubsol.CausalSubaddProof

open Filter Topology

variable {X : Type*}

/-- Convexity of `exp` on `[-C, 0]`: `exp a ≤ 1 + (1 - exp(-C)) a / C` for `-C ≤ a ≤ 0`. -/
theorem exp_le_chord {C a : ℝ} (hC : 0 < C) (ha1 : -C ≤ a) (ha2 : a ≤ 0) :
    Real.exp a ≤ 1 + (1 - Real.exp (-C)) * a / C := by
  have hl0 : 0 ≤ -a / C := div_nonneg (by linarith) hC.le
  have hl1 : -a / C ≤ 1 := (div_le_one hC).2 (by linarith)
  have h := convexOn_exp.2 (Set.mem_univ (-C)) (Set.mem_univ 0) hl0 (by linarith : 0 ≤ 1 - -a / C)
    (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
  have : -a / C * -C = a := by field_simp
  rw [this] at h
  calc Real.exp a ≤ -a / C * Real.exp (-C) + (1 - -a / C) := h
    _ = 1 + (1 - Real.exp (-C)) * a / C := by field_simp; ring

/-- `exp z - 1 ≤ z exp z`. -/
theorem exp_sub_one_le (z : ℝ) : Real.exp z - 1 ≤ z * Real.exp z := by
  have h := Real.add_one_le_exp (-z)
  have h2 : Real.exp (-z) * Real.exp z = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos z]

/-- Pointwise comparison (ineq:vt_ut) with slack `η t`, for `a ≤ ε` and `-C ≤ a + t exp a`, where
`exp z - 1 ≤ η` on `[0, ε]`. -/
theorem pointwise {C a t η ε : ℝ} (hC : 0 < C) (ht : 0 ≤ t) (hη : 0 ≤ η)
    (hε : ∀ z, 0 ≤ z → z ≤ ε → Real.exp z - 1 ≤ η)
    (hlow : -C ≤ a + t * Real.exp a) (ha : a ≤ ε) :
    a + t * Real.exp a ≤ (1 + (1 - Real.exp (-C)) * t / C) * a + t
      + (1 - Real.exp (-C)) / C * Real.exp (-C) * t ^ 2 + η * t := by
  have hc1 : 0 ≤ 1 - Real.exp (-C) := by
    have := Real.exp_le_one_iff.2 (by linarith : -C ≤ 0); linarith
  have hC1 : 0 ≤ (1 - Real.exp (-C)) / C * Real.exp (-C) :=
    mul_nonneg (div_nonneg hc1 hC.le) (Real.exp_pos _).le
  -- it suffices that `exp a ≤ 1 + c₁ a / C + C₁ t + η`
  suffices key : Real.exp a ≤ 1 + (1 - Real.exp (-C)) * a / C
      + (1 - Real.exp (-C)) / C * Real.exp (-C) * t + η by
    have := mul_le_mul_of_nonneg_left key ht
    have e : (1 + (1 - Real.exp (-C)) * t / C) * a + t
        + (1 - Real.exp (-C)) / C * Real.exp (-C) * t ^ 2 + η * t
        = a + t * (1 + (1 - Real.exp (-C)) * a / C
          + (1 - Real.exp (-C)) / C * Real.exp (-C) * t + η) := by ring
    rw [e]; linarith
  rcases le_or_gt 0 a with ha0 | ha0
  · -- `0 ≤ a ≤ ε`
    have h1 := hε a ha0 ha
    have h2 : 0 ≤ (1 - Real.exp (-C)) * a / C := div_nonneg (mul_nonneg hc1 ha0) hC.le
    linarith [mul_nonneg hC1 ht]
  rcases le_or_gt (-C) a with haC | haC
  · -- `-C ≤ a ≤ 0`: convexity
    have := exp_le_chord hC haC ha0.le
    linarith [mul_nonneg hC1 ht]
  · -- `a < -C ≤ u_t`
    have hea : Real.exp a ≤ Real.exp (-C) := Real.exp_le_exp.2 haC.le
    have hlow' : -(t * Real.exp (-C)) ≤ a + C := by
      linarith [mul_le_mul_of_nonneg_left hea ht]
    have e : 1 + (1 - Real.exp (-C)) * a / C
        = Real.exp (-C) + (1 - Real.exp (-C)) / C * (a + C) := by field_simp; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hlow' (div_nonneg hc1 hC.le)
    linarith

/-- The core estimate at `α = 1`: if `Λ u = 0` and `η > 0`, then for small `t > 0`,
`Λ[u + t exp u] ≤ ρ t + η t + C₁ t²`. -/
theorem core [Finite X] {Λ : (X → ℝ) → ℝ} (hmono : Monotone Λ) (hcaus : Causal Λ)
    (hadd : AdditivelyInvariant Λ) {ν C : ℝ} (hC : 0 < C) (hsubm : SubMultiplicative ν Λ)
    (hmem : HasMemory C Λ) {u : X → ℝ} (hu : Λ u = 0) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), Λ (fun y => u y + t * Real.exp (u y)) ≤
      (1 - ν / C * (1 - Real.exp (-C))) * t + η * t
        + (1 - Real.exp (-C)) / C * Real.exp (-C) * t ^ 2 := by
  set c₁ := 1 - Real.exp (-C) with hc₁
  set C₁ := c₁ / C * Real.exp (-C) with hC₁
  have hc1 : 0 ≤ c₁ := by
    have := Real.exp_le_one_iff.2 (by linarith : -C ≤ 0); linarith
  -- the threshold `ε`
  set ε := min (1 / 2) (η / 2) with hε_def
  have hε0 : 0 < ε := lt_min (by norm_num) (by linarith)
  have hε : ∀ z, 0 ≤ z → z ≤ ε → Real.exp z - 1 ≤ η := by
    intro z hz0 hz
    have h1 := exp_sub_one_le z
    have h12 : z ≤ 1 / 2 := hz.trans (min_le_left _ _)
    have h3 : z ≤ η / 2 := hz.trans (min_le_right _ _)
    -- `exp z (1 - z) ≤ exp z exp (-z) = 1`, so `exp z ≤ 2`
    have h4 := Real.add_one_le_exp (-z)
    have h5 : Real.exp (-z) * Real.exp z = 1 := by rw [← Real.exp_add]; simp
    have h2 : Real.exp z ≤ 2 := by nlinarith [Real.exp_pos z]
    nlinarith [Real.exp_pos z]
  -- a bound `exp ∘ u ≤ C₀`
  obtain ⟨M, hM⟩ := (Set.finite_range u).bddAbove
  set C₀ := Real.exp M
  have hC₀ : ∀ y, Real.exp (u y) ≤ C₀ := fun y => Real.exp_le_exp.2 (hM ⟨y, rfl⟩)
  have hC₀0 : 0 < C₀ := Real.exp_pos M
  filter_upwards [Ioo_mem_nhdsGT (div_pos hε0 hC₀0)] with t ⟨ht0, htε⟩
  have htC₀ : t * C₀ ≤ ε := by rw [lt_div_iff₀ hC₀0] at htε; linarith
  set ut : X → ℝ := fun y => u y + t * Real.exp (u y) with hut
  set τ := c₁ * t / C with hτ
  have hτ0 : 0 ≤ τ := div_nonneg (mul_nonneg hc1 ht0.le) hC.le
  set K := t + C₁ * t ^ 2 + η * t with hK
  set v : X → ℝ := fun y => (1 + τ) * u y + K with hv
  -- `0 ≤ Λ u_t ≤ ε`
  have hut0 : 0 ≤ Λ ut := hu ▸ hmono fun y => by
    simp only [ut]; nlinarith [Real.exp_pos (u y)]
  have hutε : Λ ut ≤ ε := by
    have := hmono (show ut ≤ fun y => u y + t * C₀ from fun y => by
      simp only [ut]; nlinarith [hC₀ y])
    rw [hadd, hu] at this; linarith
  have hpt : ∀ y, -C ≤ ut y → u y ≤ ε → ut y ≤ v y := fun y hl ha => by
    have := pointwise hC ht0.le hη.le hε hl ha
    simp only [ut, v, K, τ]; linarith
  -- Corol. corol:mon_min_max
  have hmm : Λ ut ≤ Λ v := by
    refine MonMinMaxProof.apply_le_apply_of_causal_memory hmono hcaus hadd hmem
      (t₀ := -C) (t₁ := ε) (by linarith) hutε (fun y hl hr => hpt y hl ?_) (fun y hy => ?_)
    · have : 0 ≤ t * Real.exp (u y) := by positivity
      simp only [ut] at hr; linarith
    · rcases le_or_gt ε (u y) with hy' | hy'
      · have : 0 ≤ τ * u y := mul_nonneg hτ0 (hε0.le.trans hy')
        have : 0 ≤ C₁ * t ^ 2 := mul_nonneg (by positivity) (by positivity)
        simp only [v, K]; nlinarith
      · exact hy.trans (hpt y (by linarith) hy'.le)
  -- additive invariance and sub-multiplicativity
  have hv' : Λ v ≤ -ν * τ + K := by
    have h1 := hadd (fun y => (1 + τ) * u y) K
    have h2 := hsubm τ hτ0 u
    rw [hu] at h2
    simp only [v]; rw [h1]; linarith
  calc Λ ut ≤ -ν * τ + K := hmm.trans hv'
    _ = (1 - ν / C * c₁) * t + η * t + C₁ * t ^ 2 := by
      simp only [τ, K]; field_simp; ring

/-- Memory and sub-multiplicativity force `ν ≤ Λ[0] ≤ C`. -/
theorem le_of_memory_subMultiplicative {Λ : (X → ℝ) → ℝ} (hadd : AdditivelyInvariant Λ)
    {ν C : ℝ} (hsubm : SubMultiplicative ν Λ) (hmem : HasMemory C Λ) : ν ≤ C := by
  have h1 : ν ≤ Λ 0 := by
    have := hsubm 1 zero_le_one 0
    simp only [Pi.zero_apply, mul_zero] at this
    have e : (fun _ : X => (0 : ℝ)) = 0 := rfl
    rw [e] at this; linarith
  have h2 : Λ 0 ≤ C := by
    set M := |Λ 0| + |C| + 1
    have hM : 0 ≤ M := by positivity
    have := hmem 0 (fun _ => 0 + -M) 0 fun y => by simp [hM]
    have e : Λ (fun _ => 0 + -M) = Λ 0 + -M := hadd 0 (-M)
    have e2 : max (Λ 0 + -M) (0 + C) = 0 + C :=
      max_eq_right (by linarith [le_abs_self (Λ 0), neg_abs_le C])
    rw [e, e2] at this
    have := le_max_left (Λ 0) (0 + C)
    linarith
  linarith

/-- Case `α = 1` of Prop. prop:causal_implies_subadd. -/
theorem subAdditive_kruzkovOp_one [Finite X] {Λ : (X → ℝ) → ℝ} (hmono : Monotone Λ)
    (hcaus : Causal Λ) (hadd : AdditivelyInvariant Λ) {ν C : ℝ} (hC : 0 < C)
    (hsubm : SubMultiplicative ν Λ) (hmem : HasMemory C Λ) :
    SubAdditive (1 - ν / C * (1 - Real.exp (-C))) (kruzkovOp 1 Λ) := by
  have hsub1 : SubAdditive 1 Λ := fun v t _ => by rw [hadd, one_mul]
  -- `ρ ≥ exp(-C) > 0`, since `ν ≤ C`
  have hρ : 0 ≤ 1 - ν / C * (1 - Real.exp (-C)) := by
    have hνC : ν / C ≤ 1 := (div_le_one hC).2 (le_of_memory_subMultiplicative hadd hsubm hmem)
    have he1 : Real.exp (-C) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have := mul_le_mul_of_nonneg_right hνC (by linarith : 0 ≤ 1 - Real.exp (-C))
    linarith [Real.exp_pos (-C)]
  refine SubaddLocalBwdProof.subAdditive_of_kruzkov_local hmono
    (SubaddConcaveProof.continuous_of_subAdditive_one hmono hsub1) one_pos (one_mul 1) hρ
    ((LocalXProof.local_iff_local_x Λ).2 fun u η hη => ?_)
  -- normalize to `Λ w = 0`
  set L := Λ u
  set w : X → ℝ := fun y => u y + -L
  have hw : Λ w = 0 := by simp only [w]; rw [hadd]; ring
  have hcore := core hmono hcaus hadd hC hsubm hmem hw (half_pos hη)
  have hsq : ∀ᶠ t in 𝓝[>] (0 : ℝ), Λ (fun y => u y + t * Real.exp (1 * (u y - L))) ≤
      (L + (1 - ν / C * (1 - Real.exp (-C))) * t + η / 2 * t)
        + (1 - Real.exp (-C)) / C * Real.exp (-C) * t ^ 2 := by
    filter_upwards [hcore] with t ht
    have e : (fun y => u y + t * Real.exp (1 * (u y - L)))
        = fun y => (w y + t * Real.exp (w y)) + L := by
      funext y; simp only [w, one_mul]; ring_nf
    rw [e, hadd]; linarith
  filter_upwards [SubaddConcaveProof.eventually_le_add_mul_of_sq hsq (half_pos hη)] with t ht
  linarith

/-- Prop. prop:causal_implies_subadd, general `α > 0`, by rescaling to `α = 1`. -/
theorem subAdditive_kruzkovOp_of_causal [Finite X] {Λ : (X → ℝ) → ℝ}
    (hmono : Monotone Λ) (hcaus : Causal Λ) (hadd : AdditivelyInvariant Λ) {ν C α : ℝ}
    (hC : 0 < C) (hsubm : SubMultiplicative ν Λ) (hmem : HasMemory C Λ) (hα : 0 < α) :
    SubAdditive (1 - ν / C * (1 - Real.exp (-C / α))) (kruzkovOp α Λ) := by
  have h := subAdditive_kruzkovOp_one (GuaranteedSubsol.Monotone.rescaleOp hα hmono)
    (hcaus.rescaleOp hα) (hadd.rescaleOp hα) (div_pos hC hα) (hsubm.rescaleOp hα)
    (hmem.rescaleOp hα)
  rw [kruzkovOp_rescaleOp hα, mul_one] at h
  convert h using 3
  · field_simp
  · rw [neg_div]

end GuaranteedSubsol.CausalSubaddProof
