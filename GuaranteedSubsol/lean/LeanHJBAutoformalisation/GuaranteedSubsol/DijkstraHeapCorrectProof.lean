/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.DijkstraHeapProof
import LeanHJBAutoformalisation.GuaranteedSubsol.ExtCausalCutoffProof

/-!
# Dijkstra's method with a sorted list and a stopping time: correctness

Provider proof for the frozen anchor `GuaranteedSubsol.dijkstraHeapLoop_correct`, see
`ANCHORS.md` (Prop. prop:Dijkstra_correct, Complexity.tex, V1). The operator `Γ^{<T}`
(`dijkstraCutOp T Γ`) is monotone and causal when `Γ` is (`monotone_cutOp`, `causal_cutOp`), so
algo:Dijkstra applied to it reaches a fixed point within `#X` steps, updating each point at most
once (`DijkstraProof`); the while loop with the sorted list follows it
(`DijkstraHeapProof.loop_spec`). At the fixed point, no key of `L` is below `T`.
-/

namespace GuaranteedSubsol.DijkstraHeapCorrectProof

open DijkstraHeapProof

variable {X : Type*}

/-! ### The cutoff `Γ^{<T}` -/

theorem cutoffLt_mono {T : ℝ} {a b : WithTop ℝ} (h : a ≤ b) : cutoffLt T a ≤ cutoffLt T b := by
  rcases lt_or_ge b T with hb | hb
  · rw [cutoffLt_of_lt hb, cutoffLt_of_lt (h.trans_lt hb)]
    exact h
  · rw [cutoffLt_of_le hb]
    exact le_top

/-- `(a^{<T})^{≤t} = (a^{≤t})^{<T}`. -/
theorem cutoffLe_cutoffLt (t T : ℝ) (a : WithTop ℝ) :
    cutoffLe t (cutoffLt T a) = cutoffLt T (cutoffLe t a) := by
  rcases le_or_gt a t with ht | ht
  · rw [cutoffLe_of_le ht]
    rcases lt_or_ge a T with hT | hT
    · rw [cutoffLt_of_lt hT, cutoffLe_of_le ht]
    · rw [cutoffLt_of_le hT, cutoffLe_of_lt (WithTop.coe_lt_top t)]
  · rw [cutoffLe_of_lt ht, cutoffLt_of_le le_top]
    rcases lt_or_ge a T with hT | hT
    · rw [cutoffLt_of_lt hT, cutoffLe_of_lt ht]
    · rw [cutoffLt_of_le hT, cutoffLe_of_lt (WithTop.coe_lt_top t)]

theorem causal_cutoffLt {F : (X → WithTop ℝ) → WithTop ℝ} (hF : Ext.Causal F) (T : ℝ) :
    Ext.Causal fun u => cutoffLt T (F u) := by
  rw [ExtCausalCutoffProof.causal_iff_cutoff] at hF ⊢
  intro u v t h
  rw [cutoffLe_cutoffLt, cutoffLe_cutoffLt, hF u v t h]

theorem monotone_cutOp {Γ : (X → WithTop ℝ) → X → WithTop ℝ} (hmono : Monotone Γ)
    (T : WithTop ℝ) : Monotone (dijkstraCutOp T Γ) := by
  induction T using WithTop.recTopCoe with
  | top => rw [dijkstraCutOp_top]; exact hmono
  | coe t => exact fun u v h x => cutoffLt_mono (hmono h x)

theorem causal_cutOp {Γ : (X → WithTop ℝ) → X → WithTop ℝ} (hcaus : ∀ x, Ext.Causal (Γ · x))
    (T : WithTop ℝ) (x : X) : Ext.Causal (dijkstraCutOp T Γ · x) := by
  induction T using WithTop.recTopCoe with
  | top => rw [dijkstraCutOp_top]; exact hcaus x
  | coe t => exact causal_cutoffLt (hcaus x) t

/-! ### The while loop -/

variable [Fintype X] [LinearOrder X] {Γ : (X → WithTop ℝ) → X → WithTop ℝ} {𝒱 : X → Set X}

/-- Prop. prop:Dijkstra_correct for the while loop with the sorted list and the stopping time
`T`: termination (number of acceptances), fixed point of `Γ^{<T}`, the list `L` afterwards, the
updated points, the costs. -/
theorem loop_correct (hst : Global.Ext.HasStencil 𝒱 Γ) (hmono : Monotone Γ)
    (hcaus : ∀ x, Ext.Causal (Γ · x)) (T : WithTop ℝ) (s₀ : DijkstraHeapState X)
    (hL : s₀.L.v = dijkstraKey Γ s₀.u) (hsup : dijkstraCutOp T Γ s₀.u ≤ s₀.u) :
    dijkstraHeapStopIndex Γ 𝒱 T s₀ ≤ Fintype.card X ∧
    dijkstraHeapStopIndex Γ 𝒱 T s₀ =
      ((∑ x, ((dijkstraHeapLoop Γ 𝒱 T s₀).count x - s₀.count x) : ℕ) : ℕ∞) ∧
    dijkstraCutOp T Γ (dijkstraHeapLoop Γ 𝒱 T s₀).u = (dijkstraHeapLoop Γ 𝒱 T s₀).u ∧
    (dijkstraHeapLoop Γ 𝒱 T s₀).L.v = dijkstraKey Γ (dijkstraHeapLoop Γ 𝒱 T s₀).u ∧
    (∀ y t, (dijkstraHeapLoop Γ 𝒱 T s₀).L.v y = some t → T ≤ t) ∧
    (∀ x, (dijkstraHeapLoop Γ 𝒱 T s₀).count x ≤ s₀.count x + 1 ∧
      ((dijkstraHeapLoop Γ 𝒱 T s₀).count x = s₀.count x + 1 ↔
        (dijkstraHeapLoop Γ 𝒱 T s₀).u x < s₀.u x)) ∧
    (dijkstraHeapLoop Γ 𝒱 T s₀).evalCount = s₀.evalCount +
      ∑ x, ((dijkstraHeapLoop Γ 𝒱 T s₀).count x - s₀.count x) * (Global.Ext.revStencil 𝒱 x).card ∧
    (dijkstraHeapLoop Γ 𝒱 T s₀).L.count = s₀.L.count + 1 +
      ∑ x, ((dijkstraHeapLoop Γ 𝒱 T s₀).count x - s₀.count x) *
        (2 + (Global.Ext.revStencil 𝒱 x).card) := by
  set G := dijkstraCutOp T Γ with hG
  have hGmono : Monotone G := monotone_cutOp hmono T
  have hGcaus : ∀ x, Ext.Causal (G · x) := causal_cutOp hcaus T
  obtain ⟨N, hNle, hfix⟩ := DijkstraProof.fixedPoint hGmono hGcaus hsup
  have hfix' : G (dijkstraRun G s₀.u N).u = (dijkstraRun G s₀.u N).u := hfix
  have hN : ∀ y, ¬G (dijkstraRun G s₀.u N).u y < (dijkstraRun G s₀.u N).u y := fun y h => by
    rw [hfix'] at h; exact lt_irrefl _ h
  obtain ⟨hmN, hm, hu, hc, hLv, he, hLc⟩ := loop_spec hst T s₀ hL N hN
  rw [← hG] at hm hu hc he hLc
  have hsub : ∀ x, (dijkstraHeapLoop Γ 𝒱 T s₀).count x - s₀.count x =
      (dijkstraRun G s₀.u N).count x := fun x => by
    rw [hc, Pi.add_apply, Nat.add_sub_cancel_left]
  simp only [hsub]
  refine ⟨?_, hm, ?_, hLv, fun y t ht => ?_, fun x => ?_, he, ?_⟩
  · rw [← Nat.card_eq_fintype_card]; exact hmN.trans (Nat.cast_le.2 hNle)
  · rw [hu]; exact hfix'
  · rw [hLv, hu] at ht
    unfold dijkstraKey at ht
    split_ifs at ht with hact
    rw [← Option.some_injective _ ht]
    by_contra hlt
    have hcut : G (dijkstraRun G s₀.u N).u y = Γ (dijkstraRun G s₀.u N).u y := by
      have key : ∀ u, Γ u y < T → dijkstraCutOp T Γ u y = Γ u y := fun u h => by
        unfold dijkstraCutOp; simp only [h, ↓reduceIte]
      exact key _ (not_le.1 hlt)
    exact hN y (hcut ▸ hact)
  · have h1 := DijkstraProof.count_le_one hGcaus s₀.u N x
    have h2 := DijkstraProof.count_eq_one_iff hGcaus s₀.u N x
    change (dijkstraRun G s₀.u N).count x ≤ 1 at h1
    change (dijkstraRun G s₀.u N).count x = 1 ↔ (dijkstraRun G s₀.u N).u x < s₀.u x at h2
    rw [hc, hu, Pi.add_apply, ← h2]
    omega
  · rw [hLc]
    have : ∀ x, (dijkstraRun G s₀.u N).count x * (2 + (Global.Ext.revStencil 𝒱 x).card) =
        (dijkstraRun G s₀.u N).count x +
          (dijkstraRun G s₀.u N).count x * (1 + (Global.Ext.revStencil 𝒱 x).card) :=
      fun x => by
        rw [show 2 + (Global.Ext.revStencil 𝒱 x).card = 1 + (1 + (Global.Ext.revStencil 𝒱 x).card)
          by omega, Nat.mul_add, Nat.mul_one]
    simp only [this, Finset.sum_add_distrib]
    omega

end GuaranteedSubsol.DijkstraHeapCorrectProof
