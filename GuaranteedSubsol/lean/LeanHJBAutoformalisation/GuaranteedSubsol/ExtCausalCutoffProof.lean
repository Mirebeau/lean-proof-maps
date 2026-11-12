/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AxiomsExt
import LeanHJBAutoformalisation.GuaranteedSubsol.CutoffProof
import LeanHJBAutoformalisation.GuaranteedSubsol.CutoffLeProof

/-!
# Causality on `ℝ_∞` in terms of cutoffs: proof

Provider proof for the frozen anchor `GuaranteedSubsol.Ext.causal_iff_cutoff` (see `ANCHORS.md`):
Prop. prop:causal_formulation (Complexity.tex), eq. (causal_old), scalar form on `ℝ_∞`. It
combines `CutoffProof.min_eq_min_iff_cutoffLt_eq` and
`CutoffLeProof.exists_min_eq_min_iff_cutoffLe_eq`.
-/

namespace GuaranteedSubsol.ExtCausalCutoffProof

theorem causal_iff_cutoff {X : Type*} (Γ : (X → WithTop ℝ) → WithTop ℝ) :
    Ext.Causal Γ ↔ ∀ (u v : X → WithTop ℝ) (t : ℝ),
      (∀ y, cutoffLt t (u y) = cutoffLt t (v y)) → cutoffLe t (Γ u) = cutoffLe t (Γ v) := by
  unfold Ext.Causal
  refine forall_congr' fun u => forall_congr' fun v => forall_congr' fun t => imp_congr ?_ ?_
  · exact forall_congr' fun y => CutoffProof.min_eq_min_iff_cutoffLt_eq (u y) (v y) t
  · exact CutoffLeProof.exists_min_eq_min_iff_cutoffLe_eq (Γ u) (Γ v) t

end GuaranteedSubsol.ExtCausalCutoffProof
