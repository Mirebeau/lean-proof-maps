/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.Cutoff

/-!
# Cutoffs: proofs

Provider proof for the frozen anchor `GuaranteedSubsol.min_eq_min_iff_cutoffLt_eq`
(see `ANCHORS.md`): Prop. prop:causal_formulation (Complexity.tex), cutoffs of eq. eqdef:u_less_t,
scalar form.
-/

namespace GuaranteedSubsol.CutoffProof

theorem min_eq_min_iff_cutoffLt_eq (a b : WithTop ℝ) (t : ℝ) :
    min a t = min b t ↔ cutoffLt t a = cutoffLt t b := by
  by_cases ha : a < t <;> by_cases hb : b < t
  · rw [min_eq_left ha.le, min_eq_left hb.le, cutoffLt_of_lt ha, cutoffLt_of_lt hb]
  · rw [min_eq_left ha.le, min_eq_right (not_lt.1 hb), cutoffLt_of_lt ha,
      cutoffLt_of_le (not_lt.1 hb)]
    exact ⟨fun h => absurd ha (h ▸ lt_irrefl _), fun h => absurd ha (h ▸ not_lt.2 le_top)⟩
  · rw [min_eq_right (not_lt.1 ha), min_eq_left hb.le, cutoffLt_of_le (not_lt.1 ha),
      cutoffLt_of_lt hb]
    exact ⟨fun h => absurd hb (h ▸ lt_irrefl _), fun h => absurd hb (h ▸ not_lt.2 le_top)⟩
  · rw [min_eq_right (not_lt.1 ha), min_eq_right (not_lt.1 hb), cutoffLt_of_le (not_lt.1 ha),
      cutoffLt_of_le (not_lt.1 hb)]
    exact ⟨fun _ => rfl, fun _ => rfl⟩

end GuaranteedSubsol.CutoffProof
