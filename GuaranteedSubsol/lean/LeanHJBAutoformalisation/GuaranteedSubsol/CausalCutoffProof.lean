/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.Axioms
import LeanHJBAutoformalisation.GuaranteedSubsol.CutoffProof
import LeanHJBAutoformalisation.GuaranteedSubsol.CutoffLeProof

/-!
# Causality in terms of cutoffs: proof

Provider proof for the frozen anchor `GuaranteedSubsol.causal_iff_cutoff` (see `ANCHORS.md`):
Prop. prop:causal_formulation (Complexity.tex), eq. (causal_old), scalar form. It combines the two
scalar equivalences `CutoffProof.min_eq_min_iff_cutoffLt_eq` and
`CutoffLeProof.exists_min_eq_min_iff_cutoffLe_eq`, through the embedding `ℝ → WithTop ℝ`.
-/

namespace GuaranteedSubsol.CausalCutoffProof

/-- Truncations of real values agree in `ℝ` iff they agree in `WithTop ℝ`. -/
theorem min_eq_min_iff_coe (a b s : ℝ) :
    min a s = min b s ↔ min (a : WithTop ℝ) (s : WithTop ℝ) = min (b : WithTop ℝ) s := by
  rw [← WithTop.coe_min, ← WithTop.coe_min, WithTop.coe_inj]

theorem causal_iff_cutoff {X : Type*} (Γ : (X → ℝ) → ℝ) :
    Causal Γ ↔ ∀ (u v : X → ℝ) (t : ℝ),
      (∀ y, cutoffLt t (u y) = cutoffLt t (v y)) → cutoffLe t (Γ u) = cutoffLe t (Γ v) := by
  unfold Causal
  refine forall_congr' fun u => forall_congr' fun v => forall_congr' fun t => imp_congr ?_ ?_
  · refine forall_congr' fun y => ?_
    rw [min_eq_min_iff_coe, CutoffProof.min_eq_min_iff_cutoffLt_eq]
  · rw [← CutoffLeProof.exists_min_eq_min_iff_cutoffLe_eq]
    refine exists_congr fun δ => and_congr_right fun _ => ?_
    exact min_eq_min_iff_coe _ _ _

end GuaranteedSubsol.CausalCutoffProof
