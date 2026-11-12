/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ComparisonLambdaProof
import LeanHJBAutoformalisation.GuaranteedSubsol.CausalProof
import LeanHJBAutoformalisation.GuaranteedSubsol.CausalExtProof

/-!
# Sufficient conditions for the comparison principle

The comparison principle `HasComparisonPrinciple I Λ` (Complexity.tex, eq. eq:comparison_Lambda,
V1), restated from the proved comparison results:
* Prop. prop:comparison_Lambda: `Λ` monotone on `I` and `Φ_α` `ρ`-sub-additive on `I`;
* Prop. prop:comp_of_causal: `Λ` monotone and causal on `I`, on `ℝ` and on `ℝ_∞`;
* on `ℝ_∞`, for the extension `Λ_∞` of a real `Λ`: `Φ_α` `ρ`-sub-additive on `I`
  (`Ext.hasComparisonPrinciple_of_kruzkov`), via the order embedding `E_α : ℝ_∞ → ℝ` and the
  conjugation `Φ_α ∘ E_α = E_α ∘ Λ_∞`.
`X` is finite throughout.
-/

namespace GuaranteedSubsol

variable {X : Type*} [Finite X]

/-- Prop. prop:comparison_Lambda: the comparison principle holds on `I` if `Λ` is
monotone on `I` and `Φ_α` is `ρ`-sub-additive on `I`, with `α > 0` and `ρ < 1`. -/
theorem hasComparisonPrinciple_of_kruzkov {Λ : (X → ℝ) → X → ℝ} {α ρ : ℝ} (hα : 0 < α)
    (hρ : ρ < 1) {I : Set X} (hmono : ∀ x ∈ I, Monotone (Λ · x))
    (hsub : ∀ x ∈ I, SubAdditive ρ (kruzkovOp α (Λ · x))) :
    HasComparisonPrinciple I Λ :=
  fun _ _ hu hv hbd =>
    ComparisonLambdaProof.le_of_subSolution_superSolution hα hρ hmono hsub hu hv hbd

/-- Prop. prop:comp_of_causal (real values): the comparison principle holds on `I` if `Λ` is
monotone and causal on `I`. -/
theorem hasComparisonPrinciple_of_causal {Λ : (X → ℝ) → X → ℝ} {I : Set X}
    (hmono : ∀ x ∈ I, Monotone (Λ · x)) (hcaus : ∀ x ∈ I, Causal (Λ · x)) :
    HasComparisonPrinciple I Λ :=
  fun _ _ hu hv hbd => CausalProof.le_of_causal_real hmono hcaus hu hv hbd

/-- Prop. prop:comp_of_causal (values in `ℝ_∞`): the comparison principle holds on `I` if `Λ`
is monotone and causal (`Ext.Causal`) on `I`. -/
theorem Ext.hasComparisonPrinciple_of_causal {Λ : (X → WithTop ℝ) → X → WithTop ℝ} {I : Set X}
    (hmono : ∀ x ∈ I, Monotone (Λ · x)) (hcaus : ∀ x ∈ I, Ext.Causal (Λ · x)) :
    Ext.HasComparisonPrinciple I Λ :=
  fun _ _ hu hv hbd => CausalExtProof.le_of_causal_ext hmono hcaus hu hv hbd

/-- `E_α⁻¹ (E_α a) = a` on `ℝ_∞`, when `α ≠ 0` (`E_α ∞ = 0` and `E_α⁻¹ 0 = ∞`). -/
theorem kruzkovInv_kruzkov {α : ℝ} (hα : α ≠ 0) (a : WithTop ℝ) :
    kruzkovInv α (kruzkov (1 / α) a) = a := by
  induction a using WithTop.recTopCoe with
  | top => simp [kruzkov, kruzkovInv]
  | coe r => exact ComparisonLambdaProof.kruzkovInv_kruzkov_coe hα r

/-- For `α > 0`, `E_α` is an order embedding of `ℝ_∞` into `ℝ`. -/
theorem kruzkov_le_iff {α : ℝ} (hα : 0 < α) (a b : WithTop ℝ) :
    kruzkov (1 / α) a ≤ kruzkov (1 / α) b ↔ a ≤ b := by
  induction a using WithTop.recTopCoe with
  | top =>
    induction b using WithTop.recTopCoe with
    | top => simp
    | coe s =>
      have := ComparisonLambdaProof.kruzkov_coe_neg (1 / α) s
      simp only [top_le_iff, WithTop.coe_ne_top, iff_false, not_le]
      exact this
  | coe r =>
    induction b using WithTop.recTopCoe with
    | top =>
      have := ComparisonLambdaProof.kruzkov_coe_neg (1 / α) r
      simp only [le_top, iff_true]
      exact this.le
    | coe s => rw [WithTop.coe_le_coe]; exact ComparisonLambdaProof.kruzkov_coe_le_iff hα r s

omit [Finite X] in
/-- Conjugation on `ℝ_∞`: `Φ_α (E_α u) = E_α (Λ_∞ u)`, for any `Λ`. -/
theorem kruzkovOp_kruzkov_ext {α : ℝ} (hα : α ≠ 0) (Λ : (X → ℝ) → ℝ) (u : X → WithTop ℝ) :
    kruzkovOp α Λ (fun y => kruzkov (1 / α) (u y)) =
      kruzkov (1 / α) (monotoneExtension Λ u) := by
  unfold kruzkovOp
  simp_rw [kruzkovInv_kruzkov hα]

/-- Prop. prop:comparison_Lambda, on `ℝ_∞`: if `Φ_α` is `ρ`-sub-additive on `I`, with
`α > 0` and `ρ < 1`, the extension `Λ_∞ := Global.monotoneExtension Λ` of `Λ` to `ℝ_∞` satisfies
the comparison principle on `I`. No monotonicity of `Λ` is needed; note however that `Λ_∞` is
the paper's extension only for monotone `Λ` (otherwise it extends the monotone envelope of `Λ`). -/
theorem Ext.hasComparisonPrinciple_of_kruzkov {Λ : (X → ℝ) → X → ℝ} {α ρ : ℝ} (hα : 0 < α)
    (hρ : ρ < 1) {I : Set X}
    (hsub : ∀ x ∈ I, GuaranteedSubsol.SubAdditive ρ (kruzkovOp α (Λ · x))) :
    Ext.HasComparisonPrinciple I (Global.monotoneExtension Λ) := by
  intro u v hu hv hbd
  have hc := ComparisonProof.le_of_comparison (Φ := Global.kruzkovOp α Λ) (I := I)
    (u := fun y => kruzkov (1 / α) (u y)) (v := fun y => kruzkov (1 / α) (v y)) hρ
    (fun x _ => KruzkovProof.monotone_kruzkovOp hα _) hsub (fun x hx => ?_)
    (fun x hx => (kruzkov_le_iff hα _ _).2 (hbd x hx))
  · exact fun y => (kruzkov_le_iff hα _ _).1 (hc y)
  · simp only [Global.kruzkovOp, Global.monotoneExtension, kruzkovOp_kruzkov_ext hα.ne'] at *
    have h1 := (kruzkov_le_iff hα _ _).2 (hu x hx)
    have h2 := (kruzkov_le_iff hα _ _).2 (hv x hx)
    linarith

end GuaranteedSubsol
