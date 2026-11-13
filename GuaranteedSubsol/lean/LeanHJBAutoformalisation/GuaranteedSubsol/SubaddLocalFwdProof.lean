/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.ComparisonLambdaProof
public import LeanHJBAutoformalisation.GuaranteedSubsol.KruzkovProof
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Sub-additivity in Kruzkov coordinates implies the local expansion: proof

Provider proof for the frozen anchor `GuaranteedSubsol.kruzkov_local_of_subAdditive` (see
`ANCHORS.md`): Prop. prop:subadd_local (Subadd.tex), direct implication with `O(t²)` remainder.
With `a = 1/α`, `w = u + t exp(a u)` and `v = E_α u`, one has `E_α w ≤ v + a t` pointwise (by
`1 - exp(-z) ≤ z`). Monotonicity and `ρ`-sub-additivity of `Φ_α` give
`E_α (Λ w) ≤ E_α (Λ u) + ρ a t`, and `log(1 - x) ≥ -x - 2x²` for `0 ≤ x ≤ 1/2` yields the
expansion. Only monotonicity of `Λ` is used; the continuity hypothesis of the paper is not needed.
-/

@[expose] public section

open Filter Topology

namespace GuaranteedSubsol.SubaddLocalFwdProof

/-- `log (1 - x) ≥ -x - 2x²` for `x ≤ 1/2`. -/
theorem neg_sub_le_log_one_sub {x : ℝ} (hx1 : x ≤ 1 / 2) :
    -x - 2 * x ^ 2 ≤ Real.log (1 - x) := by
  have hpos : 0 < 1 - x := by linarith
  have h1 := Real.one_sub_inv_le_log_of_pos hpos
  have h2 : -x - 2 * x ^ 2 ≤ 1 - (1 - x)⁻¹ := by
    rw [show 1 - (1 - x)⁻¹ = -x / (1 - x) by field_simp; ring, le_div_iff₀ hpos]
    nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 1 - 2 * x)]
  linarith

/-- Pointwise Kruzkov bound: `-exp(-a (r + t exp(a r))) ≤ -exp(-a r) + a t` for `t ≥ 0`. -/
theorem neg_exp_shift_le (a r t : ℝ) :
    -Real.exp (-a * (r + t * Real.exp (a * r))) ≤ -Real.exp (-a * r) + a * t := by
  have hsplit : Real.exp (-a * (r + t * Real.exp (a * r))) =
      Real.exp (-a * r) * Real.exp (-(a * t * Real.exp (a * r))) := by
    rw [← Real.exp_add]; ring_nf
  have hprod : Real.exp (-a * r) * Real.exp (a * r) = 1 := by
    rw [← Real.exp_add]; simp
  have h1 := Real.add_one_le_exp (-(a * t * Real.exp (a * r)))
  have hE := (Real.exp_pos (-a * r)).le
  have h2 := mul_le_mul_of_nonneg_left h1 hE
  have h3 : Real.exp (-a * r) * (-(a * t * Real.exp (a * r)) + 1) =
      Real.exp (-a * r) - a * t := by
    linear_combination (-(a * t)) * hprod
  rw [hsplit]
  linarith

theorem kruzkov_local_of_subAdditive {X : Type*} {Λ : (X → ℝ) → ℝ} (hmono : Monotone Λ)
    {α αinv ρ : ℝ} (hα : 0 < α) (hααinv : α * αinv = 1) (hρ : 0 ≤ ρ)
    (h : SubAdditive ρ (kruzkovOp α Λ)) (u : X → ℝ) :
    ∃ K : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Λ (fun y => u y + t * Real.exp (αinv * u y)) ≤
        Λ u + ρ * t * Real.exp (αinv * Λ u) + K * t ^ 2 := by
  set a := αinv with ha_def
  have ha1 : 1 / α = a := by field_simp; linarith
  have ha : 0 < a := by
    by_contra hneg; rw [not_lt] at hneg; nlinarith
  set E := Real.exp (a * Λ u) with hE_def
  have hEpos : 0 < E := Real.exp_pos _
  refine ⟨2 * α * ρ ^ 2 * a ^ 2 * E ^ 2, ?_⟩
  have hT : (0 : ℝ) < 1 / (2 * ρ * a * E + 1) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hT] with t ht
  obtain ⟨ht0, htT⟩ := ht
  set w : X → ℝ := fun y => u y + t * Real.exp (a * u y) with hw_def
  -- Kruzkov-coordinate inequality
  have hpt : (fun y => kruzkov (1 / α) (w y : WithTop ℝ)) ≤
      fun y => kruzkov (1 / α) (u y : WithTop ℝ) + a * t := by
    intro y
    simp only [ha1]
    exact neg_exp_shift_le a (u y) t
  have hK := (KruzkovProof.monotone_kruzkovOp hα Λ hpt).trans
    (h (fun y => kruzkov (1 / α) (u y : WithTop ℝ)) (a * t) (by positivity))
  rw [ComparisonLambdaProof.kruzkovOp_kruzkov hα.ne' hmono,
    ComparisonLambdaProof.kruzkovOp_kruzkov hα.ne' hmono, ha1] at hK
  change -Real.exp (-a * Λ w) ≤ -Real.exp (-a * Λ u) + ρ * (a * t) at hK
  -- algebra
  set x := ρ * a * t * E with hx_def
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 / 2 := by
    rw [lt_div_iff₀ (by positivity)] at htT
    nlinarith
  have hprod : Real.exp (-a * Λ u) * E = 1 := by
    rw [hE_def, ← Real.exp_add]; simp
  have hfac : Real.exp (-a * Λ u) * (1 - x) ≤ Real.exp (-a * Λ w) := by
    have : Real.exp (-a * Λ u) * (1 - x) = Real.exp (-a * Λ u) - ρ * (a * t) := by
      rw [hx_def]; linear_combination (-(ρ * a * t)) * hprod
    linarith
  have hpos : 0 < Real.exp (-a * Λ u) * (1 - x) :=
    mul_pos (Real.exp_pos _) (by linarith)
  have hlog := Real.log_le_log hpos hfac
  rw [Real.log_mul (Real.exp_pos _).ne' (by linarith), Real.log_exp, Real.log_exp] at hlog
  have hbd := neg_sub_le_log_one_sub hx1
  have haw : a * Λ w ≤ a * Λ u + x + 2 * x ^ 2 := by linarith
  have := mul_le_mul_of_nonneg_left haw hα.le
  have hαa : α * a = 1 := hααinv
  have key : Λ w ≤ Λ u + α * x + 2 * α * x ^ 2 := by
    have e1 : α * (a * Λ w) = Λ w := by rw [← mul_assoc, hαa, one_mul]
    have e2 : α * (a * Λ u + x + 2 * x ^ 2) = Λ u + α * x + 2 * α * x ^ 2 := by
      rw [mul_add, mul_add, ← mul_assoc, hαa, one_mul]; ring
    linarith
  have e3 : α * x = ρ * t * E := by
    rw [hx_def]; linear_combination (ρ * t * E) * hαa
  have e4 : 2 * α * x ^ 2 = 2 * α * ρ ^ 2 * a ^ 2 * E ^ 2 * t ^ 2 := by rw [hx_def]; ring
  linarith

end GuaranteedSubsol.SubaddLocalFwdProof
