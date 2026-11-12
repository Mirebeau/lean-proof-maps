/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.ULessTProof
import LeanHJBAutoformalisation.GuaranteedSubsol.DijkstraHeapCorrectProof
import LeanHJBAutoformalisation.GuaranteedSubsol.CausalExtProof
import LeanHJBAutoformalisation.GuaranteedSubsol.CausalProof
import LeanHJBAutoformalisation.GuaranteedSubsol.MaxMinProof
import LeanHJBAutoformalisation.GuaranteedSubsol.MaxMinMonCausalProof

/-!
# Existence and uniqueness of the fixed points of lem:u_less_t and lem:max_min

Provider proofs for the frozen anchors `GuaranteedSubsol.u_less_t_existsUnique` and
`GuaranteedSubsol.max_min_unique`, see `ANCHORS.md`. A monotone operator on `ℝ_∞^X`, causal at
every point, has a fixed point, reached by algo:Dijkstra from the super-solution `⊤`
(`DijkstraProof.fixedPoint`), and it is unique by the comparison principle
(`CausalExtProof.le_of_causal_ext`, Prop. prop:comp_of_causal). The three operators of
lem:u_less_t are monotone and causal (lem:causal_mix, prop:causal_formulation). For lem:max_min,
`û` is a fixed point (`MaxMinProof.max_min_fixedPoint`), unique by `CausalProof.le_of_causal_real`.
-/

namespace GuaranteedSubsol.ExistsUniqueProof

variable {X : Type*}

/-- A monotone operator on `ℝ_∞^X`, causal at every point, has a unique fixed point. -/
theorem existsUnique_fixedPoint [Finite X] {G : (X → WithTop ℝ) → X → WithTop ℝ}
    (hmono : ∀ x, Monotone (G · x)) (hcaus : ∀ x, Ext.Causal (G · x)) :
    ∃! u : X → WithTop ℝ, u = G u := by
  classical
  have := Fintype.ofFinite X
  let _ : LinearOrder X :=
    LinearOrder.lift' (Fintype.equivFin X) (Fintype.equivFin X).injective
  have hG : Monotone G := fun _ _ h x => hmono x h
  obtain ⟨N, -, hN⟩ := DijkstraProof.fixedPoint hG hcaus (u₀ := fun _ => ⊤) fun _ => le_top
  have hbd : ∀ {u v : X → WithTop ℝ}, ∀ y ∉ (Set.univ : Set X), u y ≤ v y :=
    fun y h => absurd (Set.mem_univ y) h
  refine ⟨_, hN.symm, fun v hv => le_antisymm ?_ ?_⟩
  · exact CausalExtProof.le_of_causal_ext (I := Set.univ) (fun y _ => hmono y)
      (fun y _ => hcaus y) (fun y _ => (congrFun hv y).le) (fun y _ => (congrFun hN y).le) hbd
  · exact CausalExtProof.le_of_causal_ext (I := Set.univ) (fun y _ => hmono y)
      (fun y _ => hcaus y) (fun y _ => (congrFun hN y).ge) (fun y _ => (congrFun hv y).ge) hbd

/-- Lemma lem:u_less_t, first sentence: the operators `max {ū, Γ}`, `max {ū, Γ}^{<T}` and
`max {ū, min {T, Γ}}` are monotone and causal, and each has a unique fixed point in `ℝ_∞^X`. -/
theorem u_less_t_existsUnique [Finite X] {Γ : (X → WithTop ℝ) → X → WithTop ℝ}
    (hmono : ∀ x, Monotone (Γ · x)) (hcaus : ∀ x, Ext.Causal (Γ · x)) (uSub : X → ℝ) (T : ℝ) :
    (∀ x, Monotone (fun u => max (uSub x : WithTop ℝ) (Γ u x)) ∧
      Ext.Causal (fun u => max (uSub x : WithTop ℝ) (Γ u x))) ∧
    (∀ x, Monotone (fun u => cutoffLt T (max (uSub x : WithTop ℝ) (Γ u x))) ∧
      Ext.Causal (fun u => cutoffLt T (max (uSub x : WithTop ℝ) (Γ u x)))) ∧
    (∀ x, Monotone (fun u => max (uSub x : WithTop ℝ) (min (T : WithTop ℝ) (Γ u x))) ∧
      Ext.Causal (fun u => max (uSub x : WithTop ℝ) (min (T : WithTop ℝ) (Γ u x)))) ∧
    (∃! u : X → WithTop ℝ, u = fun x => max (uSub x : WithTop ℝ) (Γ u x)) ∧
    (∃! u : X → WithTop ℝ, u = fun x => cutoffLt T (max (uSub x : WithTop ℝ) (Γ u x))) ∧
    (∃! u : X → WithTop ℝ,
      u = fun x => max (uSub x : WithTop ℝ) (min (T : WithTop ℝ) (Γ u x))) := by
  have h1 : ∀ x, Monotone (fun u => max (uSub x : WithTop ℝ) (Γ u x)) ∧
      Ext.Causal (fun u => max (uSub x : WithTop ℝ) (Γ u x)) := fun x =>
    ⟨fun _ _ h => max_le_max le_rfl (hmono x h),
      ExtCausalMixProof.causal_max (ULessTProof.causal_const _) (hcaus x)⟩
  have h2 : ∀ x, Monotone (fun u => cutoffLt T (max (uSub x : WithTop ℝ) (Γ u x))) ∧
      Ext.Causal (fun u => cutoffLt T (max (uSub x : WithTop ℝ) (Γ u x))) := fun x =>
    ⟨fun _ _ h => DijkstraHeapCorrectProof.cutoffLt_mono ((h1 x).1 h),
      DijkstraHeapCorrectProof.causal_cutoffLt (h1 x).2 T⟩
  have h3 : ∀ x, Monotone (fun u => max (uSub x : WithTop ℝ) (min (T : WithTop ℝ) (Γ u x))) ∧
      Ext.Causal (fun u => max (uSub x : WithTop ℝ) (min (T : WithTop ℝ) (Γ u x))) := fun x =>
    ⟨fun _ _ h => max_le_max le_rfl (min_le_min le_rfl (hmono x h)),
      ExtCausalMixProof.causal_max (ULessTProof.causal_const _)
        (ExtCausalMixProof.causal_min (ULessTProof.causal_const _) (hcaus x))⟩
  exact ⟨h1, h2, h3, existsUnique_fixedPoint (fun x => (h1 x).1) (fun x => (h1 x).2),
    existsUnique_fixedPoint (fun x => (h2 x).1) (fun x => (h2 x).2),
    existsUnique_fixedPoint (fun x => (h3 x).1) (fun x => (h3 x).2)⟩

/-- Lemma lem:max_min, uniqueness: `û` is the only fixed point of `max {ū, min {T, Γ}}`. -/
theorem max_min_unique [Finite X] {Γ : (X → ℝ) → X → ℝ} (hmono : ∀ x, Monotone (Γ · x))
    (hcaus : ∀ x, Causal (Γ · x)) (uSub : X → ℝ) (T : ℝ) {u uHat v : X → ℝ}
    (hu : u = fun x => max (uSub x) (Γ u x))
    (huHat : uHat = fun x => max (uSub x) (min T (u x)))
    (hv : v = fun x => max (uSub x) (min T (Γ v x))) : v = uHat := by
  have hfix := (MaxMinProof.max_min_fixedPoint hcaus uSub T hu huHat).1
  have hm : ∀ x ∈ (Set.univ : Set X), Monotone (fun w => max (uSub x) (min T (Γ w x))) :=
    fun x _ => MaxMinMonCausalProof.monotone_max_min (hmono x) _ _
  have hc : ∀ x ∈ (Set.univ : Set X), Causal (fun w => max (uSub x) (min T (Γ w x))) :=
    fun x _ => MaxMinMonCausalProof.causal_max_min (hcaus x) _ _
  have hbd : ∀ {a b : X → ℝ}, ∀ y ∉ (Set.univ : Set X), a y ≤ b y :=
    fun y h => absurd (Set.mem_univ y) h
  apply le_antisymm
  · exact CausalProof.le_of_causal_real (Γ := fun w x => max (uSub x) (min T (Γ w x))) hm hc
      (fun y _ => (congrFun hv y).le) (fun y _ => (congrFun hfix y).le) hbd
  · exact CausalProof.le_of_causal_real (Γ := fun w x => max (uSub x) (min T (Γ w x))) hm hc
      (fun y _ => (congrFun hfix y).ge) (fun y _ => (congrFun hv y).ge) hbd

end GuaranteedSubsol.ExistsUniqueProof
