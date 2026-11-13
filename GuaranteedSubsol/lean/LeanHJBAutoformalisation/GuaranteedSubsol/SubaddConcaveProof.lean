/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.SubaddLocalFwdProof
public import LeanHJBAutoformalisation.GuaranteedSubsol.SubaddLocalBwdProof
public import LeanHJBAutoformalisation.GuaranteedSubsol.LocalXProof
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Sub-additivity of `Φ_α` for concave schemes and at larger timescales: proofs

Provider proofs for the frozen anchors `GuaranteedSubsol.subAdditive_kruzkovOp_iff_of_concave`
(Corol. corol:subadd_concave) and `GuaranteedSubsol.subAdditive_kruzkovOp_of_le`
(Prop. prop:subadd_alpha_beta), see `ANCHORS.md` and Subadd.tex.

* Concave case: a concave `Λ` on `X → ℝ` (finite `X`) is continuous, so the local
  characterization of Prop. prop:subadd_local applies. Along a ray `s ↦ u + s w`, concavity
  makes the slopes non-increasing, so the local inequality at `s → 0⁺` globalizes to all `t ≥ 0`.
* Larger timescale: a monotone `1`-sub-additive `Λ` is `1`-Lipschitz for the sup norm, hence
  continuous. With `s = α/β`, convexity of `exp` gives `exp(z/β) ≤ s exp(z/α) + (1 - s)`, and
  `1`-sub-additivity turns (subadd_local_x) at timescale `α` into the same expansion at
  timescale `β` with constant `ρ s + (1 - s) ≤ σ`.
-/

@[expose] public section

namespace GuaranteedSubsol.SubaddConcaveProof

open Filter Topology

/-- An `O(t²)` remainder is an `o(t)` remainder as `t → 0⁺`. -/
theorem eventually_le_add_mul_of_sq {A B : ℝ → ℝ} {K : ℝ}
    (h : ∀ᶠ t in 𝓝[>] (0 : ℝ), A t ≤ B t + K * t ^ 2) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), A t ≤ B t + η * t := by
  have hpos : 0 < η / (|K| + 1) := div_pos hη (by positivity)
  filter_upwards [h, Ioo_mem_nhdsGT hpos] with t ht ht'
  obtain ⟨h0, h1⟩ := ht'
  have h2 : t * (|K| + 1) < η := (lt_div_iff₀ (by positivity)).1 h1
  nlinarith [le_abs_self K, abs_nonneg K, mul_pos h0 h0]

/-- Concavity along a ray: for `0 < s ≤ t`,
`s (Λ (u + t w) - Λ u) ≤ t (Λ (u + s w) - Λ u)` (non-increasing slopes). -/
theorem slope_le_of_concave {X : Type*} {Λ : (X → ℝ) → ℝ} (hconc : ConcaveOn ℝ Set.univ Λ)
    (u w : X → ℝ) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    s * (Λ (fun y => u y + t * w y) - Λ u) ≤ t * (Λ (fun y => u y + s * w y) - Λ u) := by
  have ht : 0 < t := hs.trans_le hst
  have hb : 0 ≤ s / t := div_nonneg hs.le ht.le
  have ha : 0 ≤ 1 - s / t := by rw [sub_nonneg, div_le_one ht]; exact hst
  have key := hconc.2 (Set.mem_univ u) (Set.mem_univ (fun y => u y + t * w y)) ha hb
    (by ring)
  have heq : ((1 - s / t) • u + (s / t) • fun y => u y + t * w y) =
      fun y => u y + s * w y := by
    funext y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  rw [heq, smul_eq_mul, smul_eq_mul] at key
  have key' : t * ((1 - s / t) * Λ u + s / t * Λ (fun y => u y + t * w y)) =
      t * Λ u - s * Λ u + s * Λ (fun y => u y + t * w y) := by
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left key ht.le]

/-- A concave function on all of `X → ℝ`, with `X` finite, is continuous. -/
theorem continuous_of_concave {X : Type*} [Finite X] {Λ : (X → ℝ) → ℝ}
    (hconc : ConcaveOn ℝ Set.univ Λ) : Continuous Λ := by
  have := Fintype.ofFinite X
  exact hconc.locallyLipschitz.continuous

/-- A monotone `1`-sub-additive `Λ` on `X → ℝ`, with `X` finite, is continuous
(it is `1`-Lipschitz for the sup norm). -/
theorem continuous_of_subAdditive_one {X : Type*} [Finite X] {Λ : (X → ℝ) → ℝ}
    (hmono : Monotone Λ) (hsub1 : SubAdditive 1 Λ) : Continuous Λ := by
  have := Fintype.ofFinite X
  refine (LipschitzWith.of_le_add fun u v => ?_).continuous
  have hle : u ≤ fun y => v y + dist u v := by
    intro y
    have h1 : dist (u y) (v y) ≤ dist u v := dist_le_pi_dist u v y
    rw [Real.dist_eq] at h1
    linarith [le_abs_self (u y - v y)]
  calc Λ u ≤ Λ (fun y => v y + dist u v) := hmono hle
    _ ≤ Λ v + 1 * dist u v := hsub1 v _ dist_nonneg
    _ = Λ v + dist u v := by ring

/-- Pointwise convexity of `exp`: with `0 ≤ s ≤ 1`, `exp (s x) ≤ s exp x + (1 - s)`. -/
theorem exp_mul_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (x : ℝ) :
    Real.exp (s * x) ≤ s * Real.exp x + (1 - s) := by
  have h := convexOn_exp.2 (Set.mem_univ x) (Set.mem_univ 0) hs0 (sub_nonneg.2 hs1)
    (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
  exact h

theorem subAdditive_kruzkovOp_iff_of_concave {X : Type*} [Finite X] {Λ : (X → ℝ) → ℝ}
    (hmono : Monotone Λ) (hconc : ConcaveOn ℝ Set.univ Λ) {α αinv ρ : ℝ} (hα : 0 < α)
    (hααinv : α * αinv = 1) (hρ : 0 ≤ ρ) :
    SubAdditive ρ (kruzkovOp α Λ) ↔
      ∀ (u : X → ℝ) (t : ℝ), 0 ≤ t →
        Λ (fun y => u y + t * Real.exp (αinv * u y)) ≤ Λ u + ρ * t * Real.exp (αinv * Λ u) := by
  constructor
  · intro h u t ht
    rcases ht.eq_or_lt with rfl | ht
    · simp
    obtain ⟨K, hK⟩ := SubaddLocalFwdProof.kruzkov_local_of_subAdditive hmono hα hααinv hρ h u
    set E := Real.exp (αinv * Λ u)
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ),
        Λ (fun y => u y + t * Real.exp (αinv * u y)) - Λ u - ρ * t * E ≤ t * K * s := by
      filter_upwards [hK, Ioo_mem_nhdsGT ht, self_mem_nhdsWithin] with s hs hst hs0
      have hs0' : (0 : ℝ) < s := hs0
      have hsl := slope_le_of_concave hconc u (fun y => Real.exp (αinv * u y)) hs0' hst.2.le
      have h3 : s * (Λ (fun y => u y + t * Real.exp (αinv * u y)) - Λ u) ≤
          s * (ρ * t * E + t * K * s) := by nlinarith
      have h4 := le_of_mul_le_mul_left h3 hs0'
      linarith
    have hlim : Tendsto (fun s : ℝ => t * K * s) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun s : ℝ => t * K * s) (𝓝 0) (𝓝 (t * K * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have := ge_of_tendsto hlim hev
    linarith
  · intro h
    refine SubaddLocalBwdProof.subAdditive_of_kruzkov_local hmono (continuous_of_concave hconc)
      hα hααinv hρ fun u η hη => ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := ht
    have := h u t ht'.le
    nlinarith

theorem subAdditive_kruzkovOp_of_le {X : Type*} [Finite X] {Λ : (X → ℝ) → ℝ}
    (hmono : Monotone Λ) (hsub1 : SubAdditive 1 Λ) {α β ρ σ : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hρ : 0 ≤ ρ) (hσ : (1 - α / β) + ρ * (α / β) ≤ σ) (h : SubAdditive ρ (kruzkovOp α Λ)) :
    SubAdditive σ (kruzkovOp β Λ) := by
  have hβ : 0 < β := hα.trans_le hαβ
  set s := α / β with hs_def
  have hs0 : 0 < s := div_pos hα hβ
  have hs1 : s ≤ 1 := (div_le_one hβ).2 hαβ
  have hσ0 : 0 ≤ σ := by nlinarith
  have hb : 1 / β = s * (1 / α) := by rw [hs_def]; field_simp
  -- (subadd_local_x) at timescale `α`, with an `O(t²)` remainder
  have hx := (LocalXProof.local_iff_local_x_sq Λ).1
    (SubaddLocalFwdProof.kruzkov_local_of_subAdditive hmono hα
      (by field_simp : α * (1 / α) = 1) hρ h)
  -- (subadd_local_x) at timescale `β`, with an `o(t)` remainder
  have hxβ : ∀ (u : X → ℝ), ∀ η > (0 : ℝ), ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Λ (fun y => u y + t * Real.exp (1 / β * (u y - Λ u))) ≤ Λ u + σ * t + η * t := by
    intro u η hη
    obtain ⟨K, hK⟩ := hx u
    have hK' := LocalXProof.eventually_mul hs0
      (eventually_le_add_mul_of_sq hK (div_pos hη hs0))
    filter_upwards [hK', self_mem_nhdsWithin] with t ht ht0
    have ht0' : (0 : ℝ) < t := ht0
    have hle : (fun y => u y + t * Real.exp (1 / β * (u y - Λ u))) ≤
        fun y => (u y + s * t * Real.exp (1 / α * (u y - Λ u))) + t * (1 - s) := by
      intro y
      have he := exp_mul_le hs0.le hs1 (1 / α * (u y - Λ u))
      dsimp only
      rw [hb, mul_assoc s]
      nlinarith
    have h1 := hsub1 (fun y => u y + s * t * Real.exp (1 / α * (u y - Λ u))) (t * (1 - s))
      (mul_nonneg ht0'.le (sub_nonneg.2 hs1))
    have h2 : η / s * (s * t) = η * t := by field_simp
    calc Λ (fun y => u y + t * Real.exp (1 / β * (u y - Λ u)))
        ≤ Λ (fun y => (u y + s * t * Real.exp (1 / α * (u y - Λ u))) + t * (1 - s)) :=
          hmono hle
      _ ≤ Λ (fun y => u y + s * t * Real.exp (1 / α * (u y - Λ u))) + 1 * (t * (1 - s)) := h1
      _ ≤ Λ u + ρ * (s * t) + η / s * (s * t) + 1 * (t * (1 - s)) := by linarith
      _ ≤ Λ u + σ * t + η * t := by rw [h2]; nlinarith
  exact SubaddLocalBwdProof.subAdditive_of_kruzkov_local hmono
    (continuous_of_subAdditive_one hmono hsub1) hβ (by field_simp : β * (1 / β) = 1) hσ0
    ((LocalXProof.local_iff_local_x Λ).2 hxβ)

end GuaranteedSubsol.SubaddConcaveProof
