/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.ComparisonProof
public import LeanHJBAutoformalisation.GuaranteedSubsol.KruzkovProof
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Linarith

/-!
# The tolerance criterion advances in the narrow band: proof

Provider proof for the frozen anchor `GuaranteedSubsol.t_advances` (see `ANCHORS.md`): Prop.
prop:t_advances (Complexity.tex). With `γ = exp(-ε αinv T⁻)` and `w = γ v̲ + 2ξ`, the function
`w` is a super-solution on `J = {T⁻ ≤ u̲ < T⁺}`: on `J ∩ I` by sub-additivity and the
multiplicative invariance `Φ (γ v) = γ Φ v`; on `J \ I` because `Φ` is constant there. Off `J`,
`v̄ ≤ w` follows from assumptions (b) and (c). The comparison principle gives `v̄ ≤ w`, and the
estimate eq. (ineq:t_advances) gives `w ≤ v̲ exp(-ε αinv u̲)` in the band `|u̲ - t| ≤ Δ/2`.
-/

@[expose] public section

namespace GuaranteedSubsol.TAdvancesProof

variable {X : Type*}

/-- The Kruzkov operator of a constant operator is constant. -/
theorem kruzkovOp_const (α c : ℝ) (v : X → ℝ) :
    kruzkovOp α (fun _ => c) v = kruzkov (1 / α) (c : WithTop ℝ) := by
  unfold kruzkovOp monotoneExtension
  have := KruzkovProof.nonempty_minorant (fun y => kruzkovInv α (v y))
  rw [ciSup_const]

/-- Off `I`, the Kruzkov operator at `x` does not depend on its argument. -/
theorem kruzkovOp_of_not_mem {Λ : (X → ℝ) → X → ℝ} {I : Set X} {ubd : X → ℝ}
    (hΛbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) (α : ℝ) {x : X} (hx : x ∉ I) (v v' : X → ℝ) :
    kruzkovOp α (Λ · x) v = kruzkovOp α (Λ · x) v' := by
  have h : (Λ · x) = fun _ => ubd x := funext fun u => hΛbd u x hx
  rw [h, kruzkovOp_const, kruzkovOp_const]

/-- Off `I`, the Kruzkov operator at `x` is `ρ`-sub-additive for `ρ ≥ 0`. -/
theorem subAdditive_of_not_mem {Λ : (X → ℝ) → X → ℝ} {I : Set X} {ubd : X → ℝ}
    (hΛbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) (α : ℝ) {ρ : ℝ} (hρ₀ : 0 ≤ ρ) {x : X} (hx : x ∉ I) :
    SubAdditive ρ (kruzkovOp α (Λ · x)) := by
  intro v s hs
  rw [kruzkovOp_of_not_mem hΛbd α hx (fun y => v y + s) v]
  linarith [mul_nonneg hρ₀ hs]

/-- `(b - a) / e ≤ exp(-a) - exp(-b)` for `a ≤ b ≤ 1`. -/
theorem exp_neg_sub_exp_neg_ge {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 1) :
    (b - a) * Real.exp (-1) ≤ Real.exp (-a) - Real.exp (-b) := by
  have h1 : Real.exp (-a) = Real.exp (-b) * Real.exp (b - a) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : b - a + 1 ≤ Real.exp (b - a) := Real.add_one_le_exp _
  have h3 : Real.exp (-1) ≤ Real.exp (-b) := Real.exp_le_exp.2 (by linarith)
  have h4 : 0 ≤ b - a := by linarith
  rw [h1]
  linarith [mul_le_mul_of_nonneg_left h2 (Real.exp_pos (-b)).le,
    mul_le_mul_of_nonneg_left h3 h4]

/-- Estimate eq. (ineq:t_advances): in the band `T⁻ + Δ/2 ≤ u ≤ T⁺ - Δ/2`,
`2ξ ≤ exp(-αinv u) (exp(-ε αinv T⁻) - exp(-ε αinv u))`. -/
theorem band_estimate {α αinv ξ ε C Tm Tp Δ u : ℝ} (hα : 0 < α) (hααinv : α * αinv = 1)
    (hε : 0 < ε) (hC : 1 ≤ C) (hlo : Tm + Δ / 2 ≤ u) (hhi : u ≤ Tp - Δ / 2)
    (hξC : ξ ≤ C * Real.exp (-αinv * Tp)) (hεT : ε * Tp ≤ α)
    (hΔlarge : 2 * α * max 1 (Real.log (2 * Real.exp 1 * C / ε)) ≤ Δ) :
    2 * ξ ≤ Real.exp (-αinv * u) * (Real.exp (-ε * αinv * Tm) - Real.exp (-ε * αinv * u)) := by
  have hαinv : 0 < αinv := by
    by_contra h
    linarith [mul_nonpos_of_nonneg_of_nonpos hα.le (not_lt.1 h)]
  set K := 2 * Real.exp 1 * C / ε with hK
  have hKpos : 0 < K := by positivity
  have hΔ1 : 2 * α ≤ Δ := le_trans (by nlinarith [le_max_left 1 (Real.log K)]) hΔlarge
  have hΔ2 : 2 * α * Real.log K ≤ Δ :=
    le_trans (by nlinarith [le_max_right 1 (Real.log K)]) hΔlarge
  set s := αinv * Δ / 2 with hs
  have hs1 : 1 ≤ s := by linarith [mul_le_mul_of_nonneg_left hΔ1 hαinv.le]
  have hsK : Real.log K ≤ s := by nlinarith [mul_le_mul_of_nonneg_left hΔ2 hαinv.le]
  -- `K exp(-s) ≤ 1`, i.e. `2 C exp(-s) ≤ ε exp(-1)`
  have hKs : K * Real.exp (-s) ≤ 1 := by
    rw [← Real.exp_log hKpos, ← Real.exp_add, ← Real.exp_zero]
    exact Real.exp_le_exp.2 (by linarith)
  have hCs : 2 * C * Real.exp (-s) ≤ ε * Real.exp (-1) := by
    have he : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
    have hKe : K * ε * Real.exp (-1) = 2 * C := by
      rw [hK]; field_simp; exact he
    nlinarith [mul_le_mul_of_nonneg_right hKs (mul_pos hε (Real.exp_pos (-1))).le,
      Real.exp_pos (-s)]
  -- `exp(-αinv T⁺) ≤ exp(-αinv u) exp(-s)`
  have hTp : Real.exp (-αinv * Tp) ≤ Real.exp (-αinv * u) * Real.exp (-s) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [mul_le_mul_of_nonneg_left hhi hαinv.le])
  -- `ε / e ≤ exp(-ε αinv T⁻) - exp(-ε αinv u)`
  have hb1 : ε * αinv * u ≤ 1 := by
    have hu : u ≤ Tp := by linarith
    linarith [mul_le_mul_of_nonneg_left hu (mul_pos hε hαinv).le,
      mul_le_mul_of_nonneg_right hεT hαinv.le]
  have hab : ε * αinv * Tm ≤ ε * αinv * u :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_pos hε hαinv).le
  have hdiff := exp_neg_sub_exp_neg_ge hab hb1
  have hεs : ε ≤ ε * αinv * u - ε * αinv * Tm := by
    nlinarith [mul_le_mul_of_nonneg_left hlo (mul_pos hε hαinv).le]
  have hgap : ε * Real.exp (-1) ≤ Real.exp (-ε * αinv * Tm) - Real.exp (-ε * αinv * u) := by
    simp only [neg_mul]
    linarith [mul_le_mul_of_nonneg_right hεs (Real.exp_pos (-1)).le]
  have hE := Real.exp_pos (-αinv * u)
  have hCpos : 0 ≤ 2 * C := by linarith
  calc 2 * ξ ≤ 2 * C * Real.exp (-αinv * Tp) := by linarith
    _ ≤ 2 * C * (Real.exp (-αinv * u) * Real.exp (-s)) :=
        mul_le_mul_of_nonneg_left hTp hCpos
    _ = Real.exp (-αinv * u) * (2 * C * Real.exp (-s)) := by ring
    _ ≤ Real.exp (-αinv * u) * (ε * Real.exp (-1)) := mul_le_mul_of_nonneg_left hCs hE.le
    _ ≤ _ := mul_le_mul_of_nonneg_left hgap hE.le

theorem t_advances {X : Type*} [Finite X] {Λ : (X → ℝ) → X → ℝ} {I : Set X} {ubd : X → ℝ}
    (hΛbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) {α αinv ρ : ℝ} (hα : 0 < α) (hααinv : α * αinv = 1)
    (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) (hadd : ∀ x ∈ I, AdditivelyInvariant (Λ · x))
    (hsub : ∀ x ∈ I, SubAdditive ρ (kruzkovOp α (Λ · x)))
    {uSub vsub vsup : X → ℝ} (hvsub : ∀ x, vsub x = kruzkov αinv (uSub x))
    (hvsup : ∀ x, vsup x ≤ 0) {Tm Tp ξ ε C t Δ : ℝ} (hTm : 0 ≤ Tm) (hξ : 0 ≤ ξ)
    (hε : 0 < ε) (hC : 1 ≤ C) (ht : t = (Tp + Tm) / 2) (hΔ : Δ = (Tp - Tm) / 2)
    (ha₁ : ∀ x, Tm ≤ uSub x → uSub x < Tp → -((1 - ρ) * ξ) ≤ vsub x - kruzkovOp α (Λ · x) vsub)
    (ha₂ : ∀ x, Tm ≤ uSub x → uSub x < Tp → vsup x - kruzkovOp α (Λ · x) vsup ≤ (1 - ρ) * ξ)
    (hb : ∀ x, Tp ≤ uSub x → -ξ ≤ vsub x)
    (hc : ∀ x, uSub x < Tm → vsup x ≤ vsub x * Real.exp (-ε * αinv * uSub x))
    (hξC : ξ ≤ C * Real.exp (-αinv * Tp)) (hεT : ε * Tp ≤ α)
    (hΔlarge : 2 * α * max 1 (Real.log (2 * Real.exp 1 * C / ε)) ≤ Δ) :
    ∀ x, t - Δ / 2 ≤ uSub x → uSub x ≤ t + Δ / 2 →
      vsup x ≤ vsub x * Real.exp (-ε * αinv * uSub x) := by
  intro x hlo hhi
  have hband := band_estimate (u := uSub x) (Tm := Tm) hα hααinv hε hC (by linarith)
    (by linarith) hξC hεT hΔlarge
  have hαinv : 0 < αinv := by
    by_contra h
    linarith [mul_nonpos_of_nonneg_of_nonpos hα.le (not_lt.1 h)]
  have hεα : 0 < ε * αinv := mul_pos hε hαinv
  have hvsub' : ∀ y, vsub y = -Real.exp (-αinv * uSub y) := fun y => hvsub y
  have hvneg : ∀ y, vsub y < 0 := fun y => by
    rw [hvsub' y]; exact neg_neg_of_pos (Real.exp_pos _)
  set γ := Real.exp (-ε * αinv * Tm) with hγ
  have hγpos : 0 < γ := Real.exp_pos _
  have hγle : γ ≤ 1 := Real.exp_le_one_iff.2 (by linarith [mul_nonneg hεα.le hTm])
  set w : X → ℝ := fun y => γ * vsub y + 2 * ξ with hw
  set Φ : (X → ℝ) → X → ℝ := fun v y => kruzkovOp α (Λ · y) v with hΦ
  set J : Set X := {y | Tm ≤ uSub y ∧ uSub y < Tp} with hJ
  have hmono : ∀ y ∈ J, Monotone (Φ · y) := fun y _ => KruzkovProof.monotone_kruzkovOp hα _
  have hsubJ : ∀ y ∈ J, SubAdditive ρ (Φ · y) := fun y _ => by
    by_cases hy : y ∈ I
    · exact hsub y hy
    · exact subAdditive_of_not_mem hΛbd α hρ₀ hy
  have hsuper : ∀ y ∈ J, vsup y - Φ vsup y ≤ w y - Φ w y := by
    intro y hy
    have h1 := ha₁ y hy.1 hy.2
    have h2 := ha₂ y hy.1 hy.2
    have hρξ : 0 ≤ (1 - ρ) * ξ := mul_nonneg (by linarith) hξ
    by_cases hyI : y ∈ I
    · have hs := hsub y hyI (fun z => γ * vsub z) (2 * ξ) (by linarith)
      have hm := KruzkovProof.kruzkovOp_mul hα (hadd y hyI) hγpos vsub
      have hΦw : Φ w y ≤ γ * Φ vsub y + ρ * (2 * ξ) := by
        simp only [hΦ, hw]; rw [← hm]; exact hs
      have hγ1 := mul_le_mul_of_nonneg_left h1 hγpos.le
      have hγ2 : 0 ≤ (1 - γ) * ((1 - ρ) * ξ) := mul_nonneg (by linarith) hρξ
      simp only [hΦ, hw] at hΦw ⊢
      linarith
    · have hΦw : Φ w y = Φ vsub y := kruzkovOp_of_not_mem hΛbd α hyI w vsub
      have hγv : vsub y ≤ γ * vsub y := by nlinarith [hvneg y]
      rw [hΦw]
      simp only [hΦ, hw] at h1 h2 ⊢
      linarith [mul_nonneg hρ₀ hξ]
  have hbd : ∀ y ∉ J, vsup y ≤ w y := by
    intro y hy
    simp only [hJ, Set.mem_ofPred_eq, not_and_or, not_le, not_lt] at hy
    rcases hy with hy | hy
    · have hexp : γ ≤ Real.exp (-ε * αinv * uSub y) :=
        Real.exp_le_exp.2 (by linarith [mul_le_mul_of_nonneg_left hy.le hεα.le])
      have := mul_le_mul_of_nonpos_left hexp (hvneg y).le
      have := hc y hy
      simp only [hw]
      linarith
    · have h1 := mul_le_mul_of_nonneg_left (hb y hy) hγpos.le
      have h2 : γ * ξ ≤ ξ := mul_le_of_le_one_left hξ hγle
      have := hvsup y
      simp only [hw]
      linarith
  have hle := ComparisonProof.le_of_comparison hρ₁ hmono hsubJ hsuper hbd x
  simp only [hw] at hle
  rw [hvsub' x] at hle ⊢
  linarith

end GuaranteedSubsol.TAdvancesProof
