/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.MonotoneExtension
import LeanHJBAutoformalisation.GuaranteedSubsol.KruzkovProof
import LeanHJBAutoformalisation.GuaranteedSubsol.ComparisonProof
import LeanHJBAutoformalisation.GuaranteedSubsol.ContractivityProof

/-!
# Comparison principle and fixed point for `Λ`, via the Kruzkov transform

Provider proofs for the frozen anchors `GuaranteedSubsol.le_of_subSolution_superSolution` and
`GuaranteedSubsol.existsUnique_fixedPoint_of_kruzkov` (see `ANCHORS.md`), from
Prop. prop:comparison_Lambda (Complexity.tex). The Kruzkov transform `E_α` is strictly increasing
on finite values, and conjugates `Λ` (at points where it is monotone) to `Φ_α`. The results
follow from the comparison principle and the unique fixed point of the monotone sub-additive
operator `Φ_α`.
-/

namespace GuaranteedSubsol.ComparisonLambdaProof

/-- `E_α⁻¹ (E_α r) = r` for finite `r`, when `α ≠ 0`. -/
theorem kruzkovInv_kruzkov_coe {α : ℝ} (hα : α ≠ 0) (r : ℝ) :
    kruzkovInv α (kruzkov (1 / α) (r : WithTop ℝ)) = (r : WithTop ℝ) := by
  change kruzkovInv α (-Real.exp (-(1 / α) * r)) = r
  have hneg : -Real.exp (-(1 / α) * r) < 0 := neg_neg_of_pos (Real.exp_pos _)
  unfold kruzkovInv
  simp only [hneg, ↓reduceIte]
  rw [neg_neg, Real.log_exp]
  congr 1
  field_simp

/-- For `α > 0`, `E_α` is an order embedding on finite values: `E_α r ≤ E_α s ↔ r ≤ s`. -/
theorem kruzkov_coe_le_iff {α : ℝ} (hα : 0 < α) (r s : ℝ) :
    kruzkov (1 / α) (r : WithTop ℝ) ≤ kruzkov (1 / α) (s : WithTop ℝ) ↔ r ≤ s := by
  change -Real.exp (-(1 / α) * r) ≤ -Real.exp (-(1 / α) * s) ↔ r ≤ s
  rw [neg_le_neg_iff, Real.exp_le_exp, neg_mul, neg_mul, neg_le_neg_iff]
  exact mul_le_mul_iff_of_pos_left (by positivity)

/-- For `α > 0`, `E_α` is injective on finite values. -/
theorem kruzkov_coe_injective {α : ℝ} (hα : 0 < α) {r s : ℝ}
    (h : kruzkov (1 / α) (r : WithTop ℝ) = kruzkov (1 / α) (s : WithTop ℝ)) : r = s :=
  le_antisymm ((kruzkov_coe_le_iff hα r s).1 h.le) ((kruzkov_coe_le_iff hα s r).1 h.ge)

/-- `E_α r < 0` for finite `r`. -/
theorem kruzkov_coe_neg (αinv r : ℝ) : kruzkov αinv (r : WithTop ℝ) < 0 :=
  neg_neg_of_pos (Real.exp_pos _)

/-- `E_α (-α log (-v)) = v` for `v < 0`, when `α ≠ 0`. -/
theorem kruzkov_coe_log {α : ℝ} (hα : α ≠ 0) {v : ℝ} (hv : v < 0) :
    kruzkov (1 / α) ((-α * Real.log (-v) : ℝ) : WithTop ℝ) = v := by
  change -Real.exp (-(1 / α) * (-α * Real.log (-v))) = v
  rw [show -(1 / α) * (-α * Real.log (-v)) = Real.log (-v) by field_simp,
    Real.exp_log (by linarith), neg_neg]

/-- Conjugation: for monotone `Λ`, `Φ_α (E_α u) = E_α (Λ u)` on finite `u`. -/
theorem kruzkovOp_kruzkov {X : Type*} {α : ℝ} (hα : α ≠ 0) {Λ : (X → ℝ) → ℝ}
    (hΛ : Monotone Λ) (u : X → ℝ) :
    kruzkovOp α Λ (fun y => kruzkov (1 / α) (u y : WithTop ℝ)) =
      kruzkov (1 / α) (Λ u : WithTop ℝ) := by
  unfold kruzkovOp
  simp_rw [kruzkovInv_kruzkov_coe hα]
  rw [MonotoneExtension.coe_eq hΛ]

theorem le_of_subSolution_superSolution {X : Type*} [Finite X] {Λ : (X → ℝ) → X → ℝ}
    {α ρ : ℝ} (hα : 0 < α) (hρ : ρ < 1) {I : Set X} (hmono : ∀ x ∈ I, Monotone (Λ · x))
    (hsub : ∀ x ∈ I, SubAdditive ρ (kruzkovOp α (Λ · x))) {u v : X → ℝ}
    (hu : ∀ x ∈ I, u x ≤ Λ u x) (hv : ∀ x ∈ I, Λ v x ≤ v x) (hbd : ∀ x ∉ I, u x ≤ v x) :
    u ≤ v := by
  have hc := ComparisonProof.le_of_comparison (Φ := fun w x => kruzkovOp α (Λ · x) w) (I := I)
    (u := fun y => kruzkov (1 / α) (u y : WithTop ℝ))
    (v := fun y => kruzkov (1 / α) (v y : WithTop ℝ)) hρ
    (fun x _ => KruzkovProof.monotone_kruzkovOp hα _) hsub (fun x hx => ?_)
    (fun x hx => (kruzkov_coe_le_iff hα _ _).2 (hbd x hx))
  · exact fun y => (kruzkov_coe_le_iff hα _ _).1 (hc y)
  · simp only [kruzkovOp_kruzkov hα.ne' (hmono x hx)]
    have h1 := (kruzkov_coe_le_iff hα _ _).2 (hu x hx)
    have h2 := (kruzkov_coe_le_iff hα _ _).2 (hv x hx)
    linarith

theorem existsUnique_fixedPoint_of_kruzkov {X : Type*} [Finite X] {Λ : (X → ℝ) → X → ℝ}
    {α ρ : ℝ} (hα : 0 < α) (hρ : ρ < 1) (hmono : ∀ x, Monotone (Λ · x))
    (hsub : ∀ x, SubAdditive ρ (kruzkovOp α (Λ · x))) {uSup : X → ℝ} (huSup : Λ uSup ≤ uSup) :
    ∃ uFix : X → ℝ, Λ uFix = uFix ∧ (∀ w, Λ w = w → w = uFix) ∧ uFix ≤ uSup := by
  have := Fintype.ofFinite X
  set Φ : (X → ℝ) → X → ℝ := fun w x => kruzkovOp α (Λ · x) w with hΦ
  have hconj : ∀ u : X → ℝ, Φ (fun y => kruzkov (1 / α) (u y : WithTop ℝ)) =
      fun x => kruzkov (1 / α) (Λ u x : WithTop ℝ) := fun u =>
    funext fun x => kruzkovOp_kruzkov hα.ne' (hmono x) u
  have hΦmono : Monotone Φ := fun w w' hw x => KruzkovProof.monotone_kruzkovOp hα _ hw
  obtain ⟨vFix, hfix, huniq, -⟩ :=
    ContractivityProof.existsUnique_fixedPoint_of_subAdditive hρ hΦmono hsub
  -- `vFix` lies below `E_α uSup`, hence is negative
  have hle : vFix ≤ fun y => kruzkov (1 / α) (uSup y : WithTop ℝ) := by
    refine ComparisonProof.le_of_comparison (Φ := Φ) (I := Set.univ) hρ
      (fun x _ => KruzkovProof.monotone_kruzkovOp hα _) (fun x _ => hsub x)
      (fun x _ => ?_) (fun x hx => absurd (Set.mem_univ x) hx)
    have h1 : Φ vFix x = vFix x := congrFun hfix x
    have h2 := congrFun (hconj uSup) x
    have h3 := (kruzkov_coe_le_iff hα _ _).2 (huSup x)
    linarith
  have hneg : ∀ y, vFix y < 0 := fun y => lt_of_le_of_lt (hle y) (kruzkov_coe_neg _ _)
  set uFix : X → ℝ := fun y => -α * Real.log (-vFix y) with hustar
  have hE : (fun y => kruzkov (1 / α) (uFix y : WithTop ℝ)) = vFix :=
    funext fun y => kruzkov_coe_log hα.ne' (hneg y)
  -- `E_α` determines finite functions
  have hinj : ∀ u w : X → ℝ, (fun y => kruzkov (1 / α) (u y : WithTop ℝ)) =
      (fun y => kruzkov (1 / α) (w y : WithTop ℝ)) → u = w := fun u w h =>
    funext fun y => kruzkov_coe_injective hα (congrFun h y)
  refine ⟨uFix, ?_, fun w hw => ?_, fun y => ?_⟩
  · refine hinj _ _ ?_
    rw [← hconj, hE, hfix]
  · refine hinj _ _ ?_
    rw [hE]
    refine huniq _ ?_
    rw [hconj, hw]
  · have := hle y
    rw [← hE] at this
    exact (kruzkov_coe_le_iff hα _ _).1 this

end GuaranteedSubsol.ComparisonLambdaProof
