/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.Axioms
public import LeanHJBAutoformalisation.GuaranteedSubsol.Kruzkov
public import LeanHJBAutoformalisation.GuaranteedSubsol.KruzkovProof

/-!
# Rescaling of an operator

The rescaled operator `Λ' u := (1/α) Λ[α u]`, with `α > 0`, and the transfer of the scheme axioms
of `Axioms.lean` from `Λ` to `Λ'`. Additive invariance, causality, the stencil, monotonicity and
the sub-additivity constant are unchanged, while the constants of memory, strict causality,
sub-multiplicativity, dependency and comparison (`C'`) are divided by `α`. In Kruzkov coordinates,
`Φ_β` for `Λ'` is `Φ_{αβ}` for `Λ` (`kruzkovOp_rescaleOp`).

Not from the paper: introduced at the author's request.
-/

@[expose] public section

namespace GuaranteedSubsol

variable {X : Type*}

/-- Rescaled operator `Λ' u := (1/α) Λ[α u]`. -/
noncomputable def rescaleOp (α : ℝ) (Λ : (X → ℝ) → ℝ) (u : X → ℝ) : ℝ :=
  Λ (fun y => α * u y) / α

variable {Λ Γ : (X → ℝ) → ℝ} {α : ℝ}

theorem Monotone.rescaleOp (hα : 0 < α) (h : Monotone Λ) : Monotone (rescaleOp α Λ) := by
  intro u v huv
  unfold GuaranteedSubsol.rescaleOp
  gcongr
  exact h fun y => mul_le_mul_of_nonneg_left (huv y) hα.le

theorem AdditivelyInvariant.rescaleOp (hα : 0 < α) (h : AdditivelyInvariant Λ) :
    AdditivelyInvariant (rescaleOp α Λ) := by
  intro u t
  unfold GuaranteedSubsol.rescaleOp
  have : (fun y => α * (u y + t)) = fun y => α * u y + α * t := funext fun y => mul_add _ _ _
  rw [this, h]
  field_simp

theorem HasMemory.rescaleOp (hα : 0 < α) {C : ℝ} (h : HasMemory C Λ) :
    HasMemory (C / α) (rescaleOp α Λ) := by
  intro u v t huv
  unfold GuaranteedSubsol.rescaleOp
  have key := h (fun y => α * u y) (fun y => α * v y) (α * t)
    fun y => by rw [← mul_max_of_nonneg _ _ hα.le, huv, mul_max_of_nonneg _ _ hα.le]
  rw [show t + C / α = (α * t + C) / α by field_simp, max_div_div_right hα.le,
    max_div_div_right hα.le, key]

theorem Causal.rescaleOp (hα : 0 < α) (h : Causal Λ) : Causal (rescaleOp α Λ) := by
  intro u v t huv
  unfold GuaranteedSubsol.rescaleOp
  obtain ⟨δ, hδ, key⟩ := h (fun y => α * u y) (fun y => α * v y) (α * t)
    fun y => by rw [← mul_min_of_nonneg _ _ hα.le, huv, mul_min_of_nonneg _ _ hα.le]
  refine ⟨δ / α, div_pos hδ hα, ?_⟩
  rw [show t + δ / α = (α * t + δ) / α by field_simp, min_div_div_right hα.le,
    min_div_div_right hα.le, key]

theorem StrictlyCausal.rescaleOp (hα : 0 < α) {δ : ℝ} (h : StrictlyCausal δ Λ) :
    StrictlyCausal (δ / α) (rescaleOp α Λ) := by
  intro u v t huv
  unfold GuaranteedSubsol.rescaleOp
  have key := h (fun y => α * u y) (fun y => α * v y) (α * t)
    fun y => by rw [← mul_min_of_nonneg _ _ hα.le, huv, mul_min_of_nonneg _ _ hα.le]
  rw [show t + δ / α = (α * t + δ) / α by field_simp, min_div_div_right hα.le,
    min_div_div_right hα.le, key]

theorem SubMultiplicative.rescaleOp (hα : 0 < α) {ν : ℝ} (h : SubMultiplicative ν Λ) :
    SubMultiplicative (ν / α) (rescaleOp α Λ) := by
  intro t ht u
  unfold GuaranteedSubsol.rescaleOp
  have : (fun y => α * ((1 + t) * u y)) = fun y => (1 + t) * (α * u y) :=
    funext fun y => mul_left_comm _ _ _
  rw [this, show (1 + t) * (Λ (fun y => α * u y) / α) - ν / α * t
    = ((1 + t) * Λ (fun y => α * u y) - ν * t) / α by field_simp]
  gcongr
  exact h t ht _

theorem SubAdditive.rescaleOp (hα : 0 < α) {ρ : ℝ} (h : SubAdditive ρ Λ) :
    SubAdditive ρ (rescaleOp α Λ) := by
  intro v t ht
  unfold GuaranteedSubsol.rescaleOp
  have : (fun y => α * (v y + t)) = fun y => α * v y + α * t := funext fun y => mul_add _ _ _
  rw [this, show Λ (fun y => α * v y) / α + ρ * t
    = (Λ (fun y => α * v y) + ρ * (α * t)) / α by field_simp]
  gcongr
  exact h _ _ (mul_nonneg hα.le ht)

theorem HasStencil.rescaleOp {V : Set X} (h : HasStencil V Λ) :
    HasStencil V (rescaleOp α Λ) := by
  intro u v huv
  unfold GuaranteedSubsol.rescaleOp
  rw [h _ _ fun y hy => by rw [huv y hy]]

theorem HasDependency.rescaleOp (hα : 0 < α) {C : ℝ} {V : Set X} (h : HasDependency C V Λ) :
    HasDependency (C / α) V (rescaleOp α Λ) := by
  refine ⟨h.1.rescaleOp, fun u y hy => ?_⟩
  unfold GuaranteedSubsol.rescaleOp
  rw [show C / α + u y = (C + α * u y) / α by field_simp]
  gcongr
  exact h.2 _ y hy

theorem Comparable.rescaleOp (hα : 0 < α) {C C' : ℝ} (h : Comparable C C' Λ Γ) :
    Comparable C (C' / α) (rescaleOp α Λ) (rescaleOp α Γ) := by
  intro u
  unfold GuaranteedSubsol.rescaleOp
  have : (fun y => α * (C * u y)) = fun y => C * (α * u y) := funext fun y => mul_left_comm _ _ _
  obtain ⟨h1, h2⟩ := h fun y => α * u y
  rw [this, show C * (Λ (fun y => α * u y) / α) - C' / α
    = (C * Λ (fun y => α * u y) - C') / α by field_simp,
    show C * (Γ (fun y => α * u y) / α) = C * Γ (fun y => α * u y) / α by ring]
  constructor <;> gcongr

/-- Multiplying by `α > 0` maps the bound `kruzkovInv β a` to `kruzkovInv (α * β) a`. -/
theorem coe_mul_le_kruzkovInv_iff (hα : 0 < α) (β x a : ℝ) :
    ((α * x : ℝ) : WithTop ℝ) ≤ kruzkovInv (α * β) a ↔ (x : WithTop ℝ) ≤ kruzkovInv β a := by
  unfold kruzkovInv
  split_ifs
  · simp only [WithTop.coe_le_coe]
    constructor <;> intro h <;> nlinarith
  · simp

/-- `Φ_β` for the rescaled operator is `Φ_{αβ}` for `Λ`. -/
theorem kruzkovOp_rescaleOp (hα : 0 < α) {β : ℝ} :
    kruzkovOp β (rescaleOp α Λ) = kruzkovOp (α * β) Λ := by
  funext v
  unfold kruzkovOp monotoneExtension
  -- reindex the supremum by `w ↦ α w`
  let g : {w : X → ℝ // ∀ y, (w y : WithTop ℝ) ≤ kruzkovInv β (v y)} →
      {w : X → ℝ // ∀ y, (w y : WithTop ℝ) ≤ kruzkovInv (α * β) (v y)} :=
    fun w => ⟨fun y => α * w.1 y, fun y => (coe_mul_le_kruzkovInv_iff hα β _ _).2 (w.2 y)⟩
  have hg : Function.Surjective g := by
    intro w
    refine ⟨⟨fun y => w.1 y / α, fun y => ?_⟩, ?_⟩
    · rw [← coe_mul_le_kruzkovInv_iff hα, mul_div_cancel₀ _ hα.ne']
      exact w.2 y
    · ext y
      exact mul_div_cancel₀ _ hα.ne'
  rw [← hg.iSup_comp]
  -- the map `↑x ↦ ↑(α x)` is an order isomorphism of `WithTop ℝ`
  let e : WithTop ℝ ≃o WithTop ℝ := (OrderIso.mulLeft₀ α hα).withTopCongr
  have he : ∀ x : ℝ, e x = ((α * x : ℝ) : WithTop ℝ) := fun x => rfl
  have hsup : (⨆ w : {w : X → ℝ // ∀ y, (w y : WithTop ℝ) ≤ kruzkovInv β (v y)},
        ((Λ (g w).1 : ℝ) : WithTop ℝ))
      = e (⨆ w : {w : X → ℝ // ∀ y, (w y : WithTop ℝ) ≤ kruzkovInv β (v y)},
        ((rescaleOp α Λ w.1 : ℝ) : WithTop ℝ)) := by
    have := KruzkovProof.nonempty_minorant fun y => kruzkovInv β (v y)
    rw [e.map_ciSup (OrderTop.bddAbove _)]
    congr 1
    funext w
    rw [he, rescaleOp, mul_div_cancel₀ _ hα.ne']
  rw [hsup]
  generalize (⨆ w : {w : X → ℝ // ∀ y, (w y : WithTop ℝ) ≤ kruzkovInv β (v y)},
    ((rescaleOp α Λ w.1 : ℝ) : WithTop ℝ)) = z
  cases z with
  | top => rfl
  | coe x =>
    rw [he]
    simp only [kruzkov]
    congr 2
    field_simp

end GuaranteedSubsol
