/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.DijkstraProof
public import LeanHJBAutoformalisation.GuaranteedSubsol.CausalProof
public import LeanHJBAutoformalisation.GuaranteedSubsol.KruzkovProof
public import LeanHJBAutoformalisation.GuaranteedSubsol.AxiomsExtTransfer
public import LeanHJBAutoformalisation.GuaranteedSubsol.MonotoneExtension

/-!
# Fixed point of a monotone causal operator: proofs

Provider proof for the frozen anchor `GuaranteedSubsol.exists_fixedPoint_of_causal`, see
`ANCHORS.md`. Dijkstra's method (Prop. prop:Dijkstra_correct), applied to the extension `Γ_∞` and
started from the finite super-solution `w`, reaches a fixed point below `w`, hence finite; by the
comparison principle for causal operators (Prop. prop:comp_of_causal, with `Int Y = X`), it lies
above every sub-solution and below every super-solution. A linear order on `X` (tie-breaking in
Dijkstra's method) is chosen from finiteness.
-/

@[expose] public section

namespace GuaranteedSubsol.CausalFixedPointProof

variable {X : Type*}

/-- Dijkstra's method started from a super-solution stays below its initial guess. -/
theorem iterate_le_init [LinearOrder X] {G : (X → WithTop ℝ) → X → WithTop ℝ} (hmono : Monotone G)
    {u₀ : X → WithTop ℝ} (hu₀ : G u₀ ≤ u₀) (n : ℕ) :
    ((dijkstraStep G)^[n] (dijkstraInit u₀)).u ≤ u₀ := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    set s := (dijkstraStep G)^[n] (dijkstraInit u₀)
    by_cases h : ∃ x, dijkstraSelect G s.u x
    · obtain ⟨x, -, hstep⟩ := DijkstraProof.step_of_select s h
      rw [hstep]
      dsimp only
      intro y
      rcases eq_or_ne y x with rfl | hyx
      · rw [Function.update_self]
        exact (DijkstraProof.superSolution hmono hu₀ n y).trans (ih y)
      · rw [Function.update_of_ne hyx]; exact ih y
    · rw [DijkstraProof.step_of_not_select s h]; exact ih

theorem exists_fixedPoint_of_causal [Finite X] {Γ : (X → ℝ) → X → ℝ}
    (hmono : ∀ x, Monotone (Γ · x)) (hcaus : ∀ x, Causal (Γ · x)) {w : X → ℝ} (hw : Γ w ≤ w) :
    ∃ u : X → ℝ, Γ u = u ∧ (∀ v, v ≤ Γ v → v ≤ u) ∧ (∀ v, Γ v ≤ v → u ≤ v) := by
  classical
  have := Fintype.ofFinite X
  let _ : LinearOrder X :=
    LinearOrder.lift' (Fintype.equivFin X) (Fintype.equivFin X).injective
  -- Dijkstra's method for `Γ_∞`, started from `w`
  set G := Global.monotoneExtension Γ
  have hGmono : Monotone G := fun _ _ h y => KruzkovProof.monotone_monotoneExtension (Γ · y) h
  have hGcaus : ∀ y, Ext.Causal (G · y) := fun y => (hcaus y).ext (hmono y)
  have hGcoe : ∀ (v : X → ℝ) y, G (fun z => (v z : WithTop ℝ)) y = (Γ v y : WithTop ℝ) :=
    fun v y => MonotoneExtension.coe_eq (hmono y) v
  have hw0 : G (fun z => (w z : WithTop ℝ)) ≤ fun z => (w z : WithTop ℝ) := fun y => by
    rw [hGcoe]; exact WithTop.coe_le_coe.2 (hw y)
  obtain ⟨N, -, hN⟩ := DijkstraProof.fixedPoint hGmono hGcaus hw0
  set f := ((dijkstraStep G)^[N] (dijkstraInit fun z => (w z : WithTop ℝ))).u
  -- the fixed point lies below `w`, hence is finite
  have hfin : ∀ y, f y ≠ ⊤ := fun y =>
    ne_top_of_le_ne_top WithTop.coe_ne_top (iterate_le_init hGmono hw0 N y)
  set u : X → ℝ := fun y => (f y).untop (hfin y)
  have hfu : f = fun y => (u y : WithTop ℝ) := funext fun y => (WithTop.coe_untop _ _).symm
  have hu : Γ u = u := funext fun y => by
    have h := congrFun hN y
    rw [hfu, hGcoe, WithTop.coe_inj] at h
    exact h
  -- comparison with sub- and super-solutions (Prop. prop:comp_of_causal, `Int Y = X`)
  refine ⟨u, hu, fun v hv => ?_, fun v hv => ?_⟩
  · exact CausalProof.le_of_causal_real (I := Set.univ) (fun y _ => hmono y) (fun y _ => hcaus y)
      (fun y _ => hv y) (fun y _ => (congrFun hu y).le) (fun y hy => absurd (Set.mem_univ y) hy)
  · exact CausalProof.le_of_causal_real (I := Set.univ) (fun y _ => hmono y) (fun y _ => hcaus y)
      (fun y _ => (congrFun hu y).ge) (fun y _ => hv y) (fun y hy => absurd (Set.mem_univ y) hy)

end GuaranteedSubsol.CausalFixedPointProof
