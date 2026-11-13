/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.ComparisonLambdaProof
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The local expansion implies sub-additivity of `Φ_α`: proof

Provider proof for the frozen anchor `GuaranteedSubsol.subAdditive_of_kruzkov_local` (see
`ANCHORS.md`): converse implication of Prop. prop:subadd_local (Subadd.tex). Write
`Φ = kruzkovOp α Λ` and `N = {v | ∀ y, v y < 0}`, on which `Φ v = E_α (Λ (E_α⁻¹ v))`.

* Local step: for `v ∈ N` and `ε > 0`, `Φ (v + s) ≤ Φ v + (ρ + ε) s` for small `s > 0`. Indeed
  `E_α⁻¹ (v + s) ≤ u + α κ s exp(u/α)` with `u = E_α⁻¹ v` and `κ > 1` (from `log x ≤ x - 1`),
  so monotonicity of `Λ` and the hypothesis apply, followed by `exp x ≥ 1 + x`.
* Globalization on `[0, S]` by continuous induction (`Φ` is continuous on `N` since `Λ` is
  continuous), then `ε → 0`.
* Extension to all `v`: `Φ (v + t)` is approximated from below by `E_α (Λ w)` for finite
  minorants `w` of `E_α⁻¹ (v + t)`, and `E_α w - t ∈ N` lies below `v`.

As in the paper, only the continuity of `Λ` is assumed.
-/

@[expose] public section

namespace GuaranteedSubsol.SubaddLocalBwdProof

open Filter Topology

variable {X : Type*}

/-- On the negative region, `Φ_α v = -exp(-αinv Λ(-α log(-v)))`. -/
theorem kruzkovOp_of_neg {α αinv : ℝ} (hα : 0 < α) (hααinv : α * αinv = 1)
    {Λ : (X → ℝ) → ℝ} (hmono : Monotone Λ) {v : X → ℝ} (hv : ∀ y, v y < 0) :
    kruzkovOp α Λ v = -Real.exp (-αinv * Λ (fun y => -α * Real.log (-v y))) := by
  have hαinv : 1 / α = αinv := by field_simp; linarith
  unfold kruzkovOp
  have : (fun y => kruzkovInv α (v y)) =
      fun y => ((-α * Real.log (-v y) : ℝ) : WithTop ℝ) := by
    funext y; simp [kruzkovInv, hv y]
  rw [this, MonotoneExtension.coe_eq hmono, hαinv]
  rfl

/-- Pointwise bound on `E_α⁻¹ (v + s)`: if `1 < κ`, `0 < p` and `κ s ≤ (κ - 1) p`, then
`-α log (p - s) ≤ -α log p + α κ s exp(αinv (-α log p))`. -/
theorem neg_log_sub_le {α αinv κ p s : ℝ} (hα : 0 < α) (hααinv : α * αinv = 1)
    (hκ : 1 < κ) (hp : 0 < p) (hs : 0 < s) (hκs : κ * s ≤ (κ - 1) * p) :
    -α * Real.log (p - s) ≤
      -α * Real.log p + α * κ * s * Real.exp (αinv * (-α * Real.log p)) := by
  have hq : 0 < p - s := by nlinarith
  have hexp : Real.exp (αinv * (-α * Real.log p)) = p⁻¹ := by
    rw [show αinv * (-α * Real.log p) = -Real.log p by linear_combination (-Real.log p) * hααinv,
      Real.exp_neg, Real.exp_log hp]
  rw [hexp]
  have hlog : Real.log p - Real.log (p - s) ≤ s / (p - s) := by
    rw [← Real.log_div hp.ne' hq.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hp hq)
    have h2 : p / (p - s) - 1 = s / (p - s) := by field_simp; ring
    linarith
  have h3 : s / (p - s) ≤ κ * s * p⁻¹ := by
    rw [div_le_iff₀ hq]
    have : κ * s * p⁻¹ * (p - s) = κ * s - κ * s * s * p⁻¹ := by field_simp
    rw [this]
    have h4 : s * s * p⁻¹ * κ ≤ s * (κ - 1) := by
      rw [show s * s * p⁻¹ * κ = s * (κ * s) * p⁻¹ by ring]
      calc s * (κ * s) * p⁻¹ ≤ s * ((κ - 1) * p) * p⁻¹ := by gcongr
        _ = s * (κ - 1) := by field_simp
    linarith
  nlinarith

/-- Local step: for `v` in the negative region and `ε > 0`, eventually as `s → 0⁺`,
`Φ_α (v + s) ≤ Φ_α v + (ρ + ε) s`. -/
theorem eventually_le_local [Finite X] {Λ : (X → ℝ) → ℝ} (hmono : Monotone Λ)
    {α αinv ρ : ℝ} (hα : 0 < α) (hααinv : α * αinv = 1) (hρ : 0 ≤ ρ)
    (h : ∀ (u : X → ℝ), ∀ η > (0 : ℝ), ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Λ (fun y => u y + t * Real.exp (αinv * u y)) ≤
        Λ u + ρ * t * Real.exp (αinv * Λ u) + η * t)
    {v : X → ℝ} (hv : ∀ y, v y < 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      kruzkovOp α Λ (fun y => v y + s) ≤ kruzkovOp α Λ v + (ρ + ε) * s := by
  have hαinv : 0 < αinv := by
    by_contra hc; push Not at hc; nlinarith
  set u : X → ℝ := fun y => -α * Real.log (-v y) with hu
  set A := Real.exp (-αinv * Λ u) with hA
  set B := Real.exp (αinv * Λ u) with hB
  have hAB : A * B = 1 := by rw [hA, hB, ← Real.exp_add]; simp
  have hApos : 0 < A := Real.exp_pos _
  have hBpos : 0 < B := Real.exp_pos _
  set κ := (ρ + ε) / (ρ + ε / 2) with hκ
  have hden : 0 < ρ + ε / 2 := by linarith
  have hκ1 : 1 < κ := by rw [hκ, one_lt_div hden]; linarith
  have hκρ : κ * (ρ + ε / 2) = ρ + ε := by rw [hκ]; field_simp
  set η := ε / 2 * B with hη
  have hηpos : 0 < η := by positivity
  have hscale : Tendsto (fun s : ℝ => α * κ * s) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Continuous fun s : ℝ => α * κ * s := continuous_const.mul continuous_id
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact mul_pos (mul_pos hα (by linarith)) hs
  have h1 := hscale.eventually (h u η hηpos)
  have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ y, κ * s ≤ (κ - 1) * (-v y) := by
    refine eventually_all.2 fun y => ?_
    have hc : 0 < (κ - 1) * (-v y) / κ :=
      div_pos (mul_pos (by linarith) (by linarith [hv y])) (by linarith)
    filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hc)] with s hs
    have := (lt_div_iff₀ (by linarith : (0 : ℝ) < κ)).1 hs
    linarith
  filter_upwards [h1, h2, self_mem_nhdsWithin] with s hs1 hs2 hs3
  have hs3 : 0 < s := hs3
  have hvs : ∀ y, v y + s < 0 := fun y => by
    have := hs2 y; nlinarith [hv y]
  rw [kruzkovOp_of_neg hα hααinv hmono hvs, kruzkovOp_of_neg hα hααinv hmono hv]
  obtain ⟨D, hD⟩ : ∃ D, D = ρ * (α * κ * s) * B + η * (α * κ * s) := ⟨_, rfl⟩
  have hkey : Λ (fun y => -α * Real.log (-(v y + s))) ≤ Λ u + D := by
    refine le_trans (hmono (?_ : _ ≤ fun y => u y + α * κ * s * Real.exp (αinv * u y))) ?_
    swap
    · exact hs1.trans_eq (by rw [hD, hB]; ring)
    intro y
    have := neg_log_sub_le (p := -v y) hα hααinv hκ1 (by linarith [hv y]) hs3 (hs2 y)
    simp only [hu]
    rw [show -(v y + s) = -v y - s by ring]
    linarith
  have hexp1 : Real.exp (-αinv * (Λ u + D)) ≤
      Real.exp (-αinv * Λ (fun y => -α * Real.log (-(v y + s)))) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hexp2 : A * (1 - αinv * D) ≤ Real.exp (-αinv * (Λ u + D)) := by
    rw [show -αinv * (Λ u + D) = -αinv * Λ u + -(αinv * D) by ring, Real.exp_add, ← hA]
    have := Real.add_one_le_exp (-(αinv * D))
    nlinarith
  have hAD : A * (αinv * D) = (ρ + ε) * s := by
    have : A * (αinv * D) = (α * αinv) * (A * B) * (κ * (ρ + ε / 2)) * s := by
      rw [hD, hη]; ring
    rw [this, hααinv, hAB, hκρ]; ring
  linarith

/-- Globalization: if `v + S` lies in the negative region, `S ≥ 0` and `ε > 0`, then
`Φ_α (v + S) ≤ Φ_α v + (ρ + ε) S`, by continuous induction on `[0, S]`. -/
theorem le_add_of_neg [Finite X] {Λ : (X → ℝ) → ℝ} (hmono : Monotone Λ)
    (hcont : Continuous Λ) {α αinv ρ : ℝ} (hα : 0 < α) (hααinv : α * αinv = 1) (hρ : 0 ≤ ρ)
    (h : ∀ (u : X → ℝ), ∀ η > (0 : ℝ), ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Λ (fun y => u y + t * Real.exp (αinv * u y)) ≤
        Λ u + ρ * t * Real.exp (αinv * Λ u) + η * t)
    {v : X → ℝ} {S : ℝ} (hS : 0 ≤ S) (hvS : ∀ y, v y + S < 0) {ε : ℝ} (hε : 0 < ε) :
    kruzkovOp α Λ (fun y => v y + S) ≤ kruzkovOp α Λ v + (ρ + ε) * S := by
  set g : ℝ → ℝ := fun s => kruzkovOp α Λ (fun y => v y + s) - (ρ + ε) * s with hg
  have hneg : ∀ s ∈ Set.Icc 0 S, ∀ y, v y + s < 0 := fun s hs y => by
    have := hvS y; linarith [hs.2]
  have hcont_g : ContinuousOn g (Set.Icc 0 S) := by
    have hF : ContinuousOn (fun s : ℝ =>
        -Real.exp (-αinv * Λ (fun y => -α * Real.log (-(v y + s)))) - (ρ + ε) * s)
        (Set.Icc 0 S) := by
      refine ContinuousOn.sub (ContinuousOn.neg (Real.continuous_exp.comp_continuousOn
        (ContinuousOn.mul continuousOn_const (hcont.comp_continuousOn ?_))))
        (continuous_const.mul continuous_id).continuousOn
      refine continuousOn_pi.2 fun y => ContinuousOn.mul continuousOn_const ?_
      refine ContinuousOn.log (by fun_prop) fun s hs => ?_
      have := hneg s hs y; linarith
    refine hF.congr fun s hs => ?_
    simp only [hg]
    rw [kruzkovOp_of_neg hα hααinv hmono (hneg s hs)]
  have hmem : S ∈ {s | g s ≤ g 0} := by
    refine IsClosed.mem_of_ge_of_forall_exists_gt ?_ (show g 0 ≤ g 0 from le_rfl) hS ?_
    · rw [Set.inter_comm]
      exact hcont_g.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    · rintro x ⟨hx, hx0, hxS⟩
      have hw : ∀ y, v y + x < 0 := hneg x ⟨hx0, hxS.le⟩
      have hloc := eventually_le_local hmono hα hααinv hρ h hw hε
      obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ :=
        (hloc.and ((eventually_lt_nhds (sub_pos.2 hxS)).filter_mono nhdsWithin_le_nhds) |>.and
          self_mem_nhdsWithin).exists
      have hs3 : 0 < s := hs3
      refine ⟨x + s, ?_, by linarith, by linarith⟩
      have hx' : g x ≤ g 0 := hx
      have heq : (fun y => v y + (x + s)) = fun y => (v y + x) + s := by
        funext y; ring
      change g (x + s) ≤ g 0
      simp only [hg] at hx' ⊢
      rw [heq]
      linarith
  have hS' : g S ≤ g 0 := hmem
  simp only [hg, add_zero, mul_zero, sub_zero] at hS'
  linarith

/-- Sub-additivity on the negative region: if `v + S` lies in it and `S ≥ 0`, then
`Φ_α (v + S) ≤ Φ_α v + ρ S`. -/
theorem le_add_of_neg' [Finite X] {Λ : (X → ℝ) → ℝ} (hmono : Monotone Λ)
    (hcont : Continuous Λ) {α αinv ρ : ℝ} (hα : 0 < α) (hααinv : α * αinv = 1) (hρ : 0 ≤ ρ)
    (h : ∀ (u : X → ℝ), ∀ η > (0 : ℝ), ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Λ (fun y => u y + t * Real.exp (αinv * u y)) ≤
        Λ u + ρ * t * Real.exp (αinv * Λ u) + η * t)
    {v : X → ℝ} {S : ℝ} (hS : 0 ≤ S) (hvS : ∀ y, v y + S < 0) :
    kruzkovOp α Λ (fun y => v y + S) ≤ kruzkovOp α Λ v + ρ * S := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hε' : 0 < ε / (S + 1) := by positivity
  have := le_add_of_neg hmono hcont hα hααinv hρ h hS hvS hε'
  have h2 : ε / (S + 1) * S ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; linarith
  linarith

/-- Approximation of `E_α` from below: for every `z` and `ε > 0` there is a finite `R < z`
with `E_α z = E_α R + ε`. -/
theorem exists_kruzkov_eq_add {α : ℝ} (hα : 0 < α) (z : WithTop ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, (R : WithTop ℝ) < z ∧
      kruzkov (1 / α) z = kruzkov (1 / α) (R : WithTop ℝ) + ε := by
  set c := -kruzkov (1 / α) z with hc
  have hc0 : 0 ≤ c := by
    cases z with
    | top => simp [hc, kruzkov]
    | coe r => exact neg_nonneg.2 (ComparisonLambdaProof.kruzkov_coe_neg _ r).le
  refine ⟨-α * Real.log (-(-(c + ε))), ?_, ?_⟩
  · cases z with
    | top => exact WithTop.coe_lt_top _
    | coe r =>
      refine WithTop.coe_lt_coe.2 (lt_of_not_ge fun hle => ?_)
      have := (ComparisonLambdaProof.kruzkov_coe_le_iff hα _ _).2 hle
      rw [ComparisonLambdaProof.kruzkov_coe_log hα.ne' (by linarith)] at this
      linarith
  · rw [ComparisonLambdaProof.kruzkov_coe_log hα.ne' (by linarith)]
    linarith

/-- `E_α (E_α⁻¹ z) ≤ z`. -/
theorem kruzkov_kruzkovInv_le {α : ℝ} (hα : 0 < α) (z : ℝ) :
    kruzkov (1 / α) (kruzkovInv α z) ≤ z := by
  unfold kruzkovInv
  split_ifs with hz
  · rw [ComparisonLambdaProof.kruzkov_coe_log hα.ne' hz]
  · change (0 : ℝ) ≤ z
    linarith

theorem subAdditive_of_kruzkov_local {X : Type*} [Finite X] {Λ : (X → ℝ) → ℝ}
    (hmono : Monotone Λ) (hcont : Continuous Λ) {α αinv ρ : ℝ} (hα : 0 < α)
    (hααinv : α * αinv = 1) (hρ : 0 ≤ ρ)
    (h : ∀ (u : X → ℝ), ∀ η > (0 : ℝ), ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Λ (fun y => u y + t * Real.exp (αinv * u y)) ≤
        Λ u + ρ * t * Real.exp (αinv * Λ u) + η * t) :
    SubAdditive ρ (kruzkovOp α Λ) := by
  intro v t ht
  -- finite minorants of `E_α⁻¹ (v + t)` are controlled by sub-additivity on the negative region
  have hcore : ∀ w : X → ℝ, (∀ y, (w y : WithTop ℝ) ≤ kruzkovInv α (v y + t)) →
      kruzkov (1 / α) (Λ w : WithTop ℝ) ≤ kruzkovOp α Λ v + ρ * t := by
    intro w hw
    set v' : X → ℝ := fun y => kruzkov (1 / α) (w y : WithTop ℝ) with hv'
    have hv'neg : ∀ y, v' y < 0 := fun y => ComparisonLambdaProof.kruzkov_coe_neg _ _
    have hv'le : ∀ y, v' y ≤ v y + t := fun y =>
      (KruzkovProof.monotone_kruzkov hα (hw y)).trans (kruzkov_kruzkovInv_le hα _)
    rw [← ComparisonLambdaProof.kruzkovOp_kruzkov hα.ne' hmono]
    have heq : (fun y => kruzkov (1 / α) (w y : WithTop ℝ)) = fun y => (v' y - t) + t := by
      funext y; simp [hv']
    rw [heq]
    refine (le_add_of_neg' hmono hcont hα hααinv hρ h ht
      (fun y => by simpa using hv'neg y)).trans ?_
    have := KruzkovProof.monotone_kruzkovOp hα Λ (fun y => by linarith [hv'le y] :
      (fun y => v' y - t) ≤ v)
    linarith
  change kruzkov (1 / α) (monotoneExtension Λ fun y => kruzkovInv α (v y + t)) ≤ _
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨R, hR, hRe⟩ := exists_kruzkov_eq_add hα
    (monotoneExtension Λ fun y => kruzkovInv α (v y + t)) hε
  have := KruzkovProof.nonempty_minorant (fun y => kruzkovInv α (v y + t))
  obtain ⟨w, hw⟩ := exists_lt_of_lt_ciSup hR
  have h1 := KruzkovProof.monotone_kruzkov hα hw.le
  have h2 := hcore w.1 w.2
  rw [hRe]
  linarith

end GuaranteedSubsol.SubaddLocalBwdProof
