/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.TAdvancesProof
public import LeanHJBAutoformalisation.GuaranteedSubsol.KruzkovRpowProof
public import LeanHJBAutoformalisation.GuaranteedSubsol.PowrDiffProof
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The tolerance criterion advances, unknown parameters: proof

Provider proof for the frozen anchor `GuaranteedSubsol.t_advances_withUnknown` (see
`ANCHORS.md`): Prop. prop:t_advances_withUnknown (Complexity.tex). With `r = α / β ∈ (0, 1]`,
the change of variables `v ↦ -(-v)^r` maps the Kruzkov coordinates of timescale `α` to those of
timescale `β`, and intertwines `Φ_α` and `Φ_β`. The assumptions (a), (b), (c) transfer to
`w̄ = -(-v̄)^r`, `w̲ = -(-v̲)^r` with `ζ = C ξ^r` in place of `ξ`, by the Hölder continuity
`|a^r - b^r| ≤ |a - b|^r`. Then `t_advances` applies with timescale `β` and sub-additivity
constant `σ`, and the conclusion is pulled back by the monotonicity of `v ↦ -(-v)^r`.
-/

@[expose] public section

namespace GuaranteedSubsol.TAdvancesWithUnknownProof

variable {X : Type*}

/-- The Kruzkov transform is nonpositive. -/
theorem kruzkov_nonpos (αinv : ℝ) (z : WithTop ℝ) : kruzkov αinv z ≤ 0 := by
  cases z with
  | top => simp [kruzkov]
  | coe u => simp only [kruzkov]; exact neg_nonpos.2 (Real.exp_pos _).le

/-- Timescale change for the inverse Kruzkov transform: for `a ≤ 0` and `r β = α`,
`E_β⁻¹ (-(-a)^r) = E_α⁻¹ a`. -/
theorem kruzkovInv_neg_rpow {α β r a : ℝ} (hr : 0 < r) (hrβ : r * β = α) (ha : a ≤ 0) :
    kruzkovInv β (-(-a) ^ r) = kruzkovInv α a := by
  rcases ha.lt_or_eq with ha | ha
  · have hpos : 0 < (-a) ^ r := Real.rpow_pos_of_pos (by linarith) r
    have hneg : -(-a) ^ r < 0 := by linarith
    simp only [kruzkovInv, hneg, ha, ↓reduceIte, neg_neg, Real.log_rpow (by linarith : 0 < -a),
      ← hrβ]
    congr 1
    ring
  · subst ha
    simp [kruzkovInv, Real.zero_rpow hr.ne']

/-- Timescale change for the Kruzkov transform on `ℝ_∞`:
`E_β z = -(-E_α z)^r`, with `βinv = r * αinv`. -/
theorem kruzkov_mul_eq_neg_rpow' {r : ℝ} (hr : 0 < r) (αinv : ℝ) (z : WithTop ℝ) :
    kruzkov (r * αinv) z = -(-kruzkov αinv z) ^ r := by
  cases z with
  | top => simp [kruzkov, Real.zero_rpow hr.ne']
  | coe u => exact KruzkovRpowProof.kruzkov_mul_eq_neg_rpow αinv r u

/-- Timescale change for the Kruzkov operator: for `v ≤ 0`,
`Φ_β (-(-v)^r) = -(-Φ_α v)^r`, with `r β = α`. -/
theorem kruzkovOp_neg_rpow {α β r : ℝ} (hr : 0 < r) (hrβ : r * β = α)
    (hinv : 1 / β = r * (1 / α)) (Λx : (X → ℝ) → ℝ) {v : X → ℝ} (hv : ∀ y, v y ≤ 0) :
    kruzkovOp β Λx (fun y => -(-v y) ^ r) = -(-kruzkovOp α Λx v) ^ r := by
  unfold kruzkovOp
  have h : (fun y => kruzkovInv β (-(-v y) ^ r)) = fun y => kruzkovInv α (v y) :=
    funext fun y => kruzkovInv_neg_rpow hr hrβ (hv y)
  rw [h, hinv, kruzkov_mul_eq_neg_rpow' hr]

/-- One-sided Hölder estimate: `p - q ≤ d` implies `p^r - q^r ≤ d^r` for nonnegative
`p, q, d` and `r ∈ [0, 1]`. -/
theorem rpow_sub_rpow_le {p q d r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hd : 0 ≤ d)
    (hpq : p - q ≤ d) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) : p ^ r - q ^ r ≤ d ^ r := by
  rcases le_total p q with h | h
  · have := Real.rpow_le_rpow hp h hr₀
    have := Real.rpow_nonneg hd r
    linarith
  · have h1 := PowrDiffProof.abs_rpow_sub_rpow_le hp hq hr₀ hr₁
    rw [abs_of_nonneg (by linarith : 0 ≤ p - q)] at h1
    have h2 := Real.rpow_le_rpow (by linarith) hpq hr₀
    linarith [le_abs_self (p ^ r - q ^ r)]

/-- The map `a ↦ -(-a)^r` is an order embedding of `(-∞, 0]` for `r > 0`. -/
theorem neg_rpow_neg_le_iff {a b r : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) (hr : 0 < r) :
    -(-a) ^ r ≤ -(-b) ^ r ↔ a ≤ b := by
  rw [neg_le_neg_iff, Real.rpow_le_rpow_iff (by linarith) (by linarith) hr]
  constructor <;> intro h <;> linarith

/-- `-(-v)^r * exp(s r) = -(-(v exp s))^r` for `v ≤ 0`. -/
theorem neg_rpow_mul_exp {v : ℝ} (hv : v ≤ 0) (r s : ℝ) :
    -(-v) ^ r * Real.exp (s * r) = -(-(v * Real.exp s)) ^ r := by
  rw [Real.exp_mul, show -(v * Real.exp s) = -v * Real.exp s by ring,
    Real.mul_rpow (by linarith) (Real.exp_pos s).le]
  ring

theorem t_advances_withUnknown {X : Type*} [Finite X] {Λ : (X → ℝ) → X → ℝ} {I : Set X}
    {ubd : X → ℝ} (hΛbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) {α β αinv ρ σ r C : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hααinv : α * αinv = 1)
    (hρ₁ : ρ < 1) (hσ₀ : 0 ≤ σ) (hσ₁ : σ < 1) (hr : r = α / β) (hr₁ : r ≤ 1)
    (hCdef : C = (1 - ρ) ^ r / (1 - σ)) (hC : 1 ≤ C)
    (hadd : ∀ x ∈ I, AdditivelyInvariant (Λ · x))
    (hsub : ∀ x ∈ I, SubAdditive σ (kruzkovOp β (Λ · x)))
    {uSub vsub vsup : X → ℝ} (hvsub : ∀ x, vsub x = kruzkov αinv (uSub x))
    (hvsup : ∀ x, vsup x ≤ 0) {Tm Tp ξ ε t Δ : ℝ} (hTm : 0 ≤ Tm) (hξ : 0 ≤ ξ) (hε : 0 < ε)
    (ht : t = (Tp + Tm) / 2) (hΔ : Δ = (Tp - Tm) / 2)
    (ha₁ : ∀ x, Tm ≤ uSub x → uSub x < Tp → -((1 - ρ) * ξ) ≤ vsub x - kruzkovOp α (Λ · x) vsub)
    (ha₂ : ∀ x, Tm ≤ uSub x → uSub x < Tp → vsup x - kruzkovOp α (Λ · x) vsup ≤ (1 - ρ) * ξ)
    (hb : ∀ x, Tp ≤ uSub x → -ξ ≤ vsub x)
    (hc : ∀ x, uSub x < Tm → vsup x ≤ vsub x * Real.exp (-ε * αinv * uSub x))
    (hξT : ξ ≤ Real.exp (-αinv * Tp)) (hεT : ε * Tp ≤ α)
    (hΔlarge : 2 * β * max 1 (Real.log (2 * Real.exp 1 * C / ε)) ≤ Δ) :
    ∀ x, t - Δ / 2 ≤ uSub x → uSub x ≤ t + Δ / 2 →
      vsup x ≤ vsub x * Real.exp (-ε * αinv * uSub x) := by
  -- the inverse timescale of `β`, used to apply `t_advances` at timescale `β`
  set βinv : ℝ := 1 / β with hβdef
  have hββinv : β * βinv = 1 := by rw [hβdef]; field_simp
  -- the exponent `r = α / β ∈ (0, 1]` and the inverse timescales
  have hr0 : 0 < r := by rw [hr]; positivity
  have hrβ : r * β = α := by rw [hr]; field_simp
  have hαinv : αinv = 1 / α := by field_simp; linarith
  have hβinv' : βinv = 1 / β := by field_simp; linarith
  have hβinv : βinv = r * αinv := by
    rw [hβinv', hαinv, ← hrβ]; field_simp
  have hinv : 1 / β = r * (1 / α) := by rw [← hβinv', ← hαinv, hβinv]
  -- sign facts
  have hvneg : ∀ y, vsub y ≤ 0 := fun y => by rw [hvsub y]; exact kruzkov_nonpos _ _
  have hΦneg : ∀ (y : X) (v : X → ℝ), kruzkovOp α (Λ · y) v ≤ 0 :=
    fun y v => kruzkov_nonpos _ _
  -- the transformed data
  set wsub : X → ℝ := fun y => -(-vsub y) ^ r with hwsubdef
  set wsup : X → ℝ := fun y => -(-vsup y) ^ r with hwsupdef
  set ζ := C * ξ ^ r with hζ
  have hσC : (1 - σ) * ζ = ((1 - ρ) * ξ) ^ r := by
    rw [hζ, hCdef, Real.mul_rpow (by linarith) hξ]
    field_simp [(by linarith : (1 - σ) ≠ 0)]
  have hρξ : 0 ≤ (1 - ρ) * ξ := mul_nonneg (by linarith) hξ
  have hΦsub : ∀ y, kruzkovOp β (Λ · y) wsub = -(-kruzkovOp α (Λ · y) vsub) ^ r :=
    fun y => kruzkovOp_neg_rpow hr0 hrβ hinv _ hvneg
  have hΦsup : ∀ y, kruzkovOp β (Λ · y) wsup = -(-kruzkovOp α (Λ · y) vsup) ^ r :=
    fun y => kruzkovOp_neg_rpow hr0 hrβ hinv _ hvsup
  -- hypotheses of `t_advances` at timescale `β`
  have hwsub : ∀ y, wsub y = kruzkov βinv (uSub y) := fun y => by
    rw [hβinv, KruzkovRpowProof.kruzkov_mul_eq_neg_rpow, ← hvsub y]
  have hwsup' : ∀ y, wsup y ≤ 0 := fun y =>
    neg_nonpos.2 (Real.rpow_nonneg (by linarith [hvsup y]) r)
  have hζ0 : 0 ≤ ζ := mul_nonneg (by linarith) (Real.rpow_nonneg hξ r)
  have ha₁' : ∀ y, Tm ≤ uSub y → uSub y < Tp →
      -((1 - σ) * ζ) ≤ wsub y - kruzkovOp β (Λ · y) wsub := by
    intro y h1 h2
    have h := ha₁ y h1 h2
    have := rpow_sub_rpow_le (p := -vsub y) (q := -kruzkovOp α (Λ · y) vsub)
      (by linarith [hvneg y]) (by linarith [hΦneg y vsub]) hρξ (by linarith) hr0.le hr₁
    rw [hΦsub y, hσC]
    simp only [hwsubdef]
    linarith
  have ha₂' : ∀ y, Tm ≤ uSub y → uSub y < Tp →
      wsup y - kruzkovOp β (Λ · y) wsup ≤ (1 - σ) * ζ := by
    intro y h1 h2
    have h := ha₂ y h1 h2
    have := rpow_sub_rpow_le (p := -kruzkovOp α (Λ · y) vsup) (q := -vsup y)
      (by linarith [hΦneg y vsup]) (by linarith [hvsup y]) hρξ (by linarith) hr0.le hr₁
    rw [hΦsup y, hσC]
    simp only [hwsupdef]
    linarith
  have hb' : ∀ y, Tp ≤ uSub y → -ζ ≤ wsub y := by
    intro y hy
    have h := hb y hy
    have h1 := Real.rpow_le_rpow (by linarith [hvneg y]) (by linarith : -vsub y ≤ ξ) hr0.le
    have h2 : ξ ^ r ≤ C * ξ ^ r := le_mul_of_one_le_left (Real.rpow_nonneg hξ r) hC
    simp only [hwsubdef]
    linarith
  have hexp : ∀ y, wsub y * Real.exp (-ε * βinv * uSub y)
      = -(-(vsub y * Real.exp (-ε * αinv * uSub y))) ^ r := fun y => by
    rw [← neg_rpow_mul_exp (hvneg y)]
    congr 2
    rw [hβinv]; ring
  have hvexp : ∀ y, vsub y * Real.exp (-ε * αinv * uSub y) ≤ 0 :=
    fun y => mul_nonpos_of_nonpos_of_nonneg (hvneg y) (Real.exp_pos _).le
  have hc' : ∀ y, uSub y < Tm → wsup y ≤ wsub y * Real.exp (-ε * βinv * uSub y) := by
    intro y hy
    rw [hexp y]
    exact (neg_rpow_neg_le_iff (hvsup y) (hvexp y) hr0).2 (hc y hy)
  have hξC : ζ ≤ C * Real.exp (-βinv * Tp) := by
    have h1 := Real.rpow_le_rpow hξ hξT hr0.le
    rw [← Real.exp_mul] at h1
    have h2 : -αinv * Tp * r = -βinv * Tp := by rw [hβinv]; ring
    rw [h2] at h1
    exact mul_le_mul_of_nonneg_left h1 (by linarith)
  have hεT' : ε * Tp ≤ β := by nlinarith
  intro x hlo hhi
  have key := TAdvancesProof.t_advances hΛbd hβ hββinv hσ₀ hσ₁ hadd hsub hwsub hwsup' hTm hζ0
    hε hC ht hΔ ha₁' ha₂' hb' hc' hξC hεT' hΔlarge x hlo hhi
  rw [hexp x] at key
  exact (neg_rpow_neg_le_iff (hvsup x) (hvexp x) hr0).1 key

end GuaranteedSubsol.TAdvancesWithUnknownProof
