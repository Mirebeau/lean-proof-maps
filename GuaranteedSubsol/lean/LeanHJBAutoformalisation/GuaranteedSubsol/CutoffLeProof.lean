/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.Cutoff
import Mathlib.Tactic.Linarith

/-!
# Cutoffs `a^{≤t}`: proofs

Provider proof for the frozen anchor `GuaranteedSubsol.exists_min_eq_min_iff_cutoffLe_eq`
(see `ANCHORS.md`): Prop. prop:causal_formulation (Complexity.tex), second equivalence,
scalar form.
-/

namespace GuaranteedSubsol.CutoffLeProof

/-- If `a ≤ t`, then `min a (t + δ) = a` for every `δ > 0`. -/
theorem min_add_eq_left {a : WithTop ℝ} {t δ : ℝ} (ha : a ≤ t) (hδ : 0 < δ) :
    min a ((t + δ : ℝ) : WithTop ℝ) = a :=
  min_eq_left (ha.trans (WithTop.coe_le_coe.2 (by linarith)))

/-- If `t < a`, then `t < min a (t + δ)` for every `δ > 0`. -/
theorem lt_min_add {a : WithTop ℝ} {t δ : ℝ} (ha : (t : WithTop ℝ) < a) (hδ : 0 < δ) :
    (t : WithTop ℝ) < min a ((t + δ : ℝ) : WithTop ℝ) :=
  lt_min ha (WithTop.coe_lt_coe.2 (by linarith))

/-- If `t < a` and `t < b`, there is `δ > 0` with `t + δ ≤ a` and `t + δ ≤ b`. -/
theorem exists_pos_add_le {a b : WithTop ℝ} {t : ℝ} (ha : (t : WithTop ℝ) < a)
    (hb : (t : WithTop ℝ) < b) :
    ∃ δ > (0 : ℝ), ((t + δ : ℝ) : WithTop ℝ) ≤ a ∧ ((t + δ : ℝ) : WithTop ℝ) ≤ b := by
  obtain ⟨c, htc, hc⟩ := exists_between (lt_min ha hb)
  obtain ⟨r, rfl⟩ := WithTop.ne_top_iff_exists.1 (hc.trans_le le_top).ne
  refine ⟨r - t, by linarith [WithTop.coe_lt_coe.1 htc], ?_, ?_⟩
  · rw [add_sub_cancel]; exact (hc.trans_le (min_le_left _ _)).le
  · rw [add_sub_cancel]; exact (hc.trans_le (min_le_right _ _)).le

theorem exists_min_eq_min_iff_cutoffLe_eq (a b : WithTop ℝ) (t : ℝ) :
    (∃ δ > (0 : ℝ), min a ((t + δ : ℝ) : WithTop ℝ) = min b ((t + δ : ℝ) : WithTop ℝ)) ↔
      cutoffLe t a = cutoffLe t b := by
  by_cases ha : a ≤ t <;> by_cases hb : b ≤ t
  · rw [cutoffLe_of_le ha, cutoffLe_of_le hb]
    refine ⟨fun ⟨δ, hδ, h⟩ => ?_, fun h => ⟨1, one_pos, by rw [h]⟩⟩
    rwa [min_add_eq_left ha hδ, min_add_eq_left hb hδ] at h
  · have hb' := not_le.1 hb
    rw [cutoffLe_of_le ha, cutoffLe_of_lt hb']
    refine ⟨fun ⟨δ, hδ, h⟩ => ?_, fun h => ?_⟩
    · rw [min_add_eq_left ha hδ] at h
      exact absurd (h ▸ ha) (not_le.2 (lt_min_add hb' hδ))
    · exact absurd (h ▸ ha) (not_le.2 (WithTop.coe_lt_top t))
  · have ha' := not_le.1 ha
    rw [cutoffLe_of_lt ha', cutoffLe_of_le hb]
    refine ⟨fun ⟨δ, hδ, h⟩ => ?_, fun h => ?_⟩
    · rw [min_add_eq_left hb hδ] at h
      exact absurd (h ▸ hb) (not_le.2 (lt_min_add ha' hδ))
    · exact absurd (h ▸ hb) (not_le.2 (WithTop.coe_lt_top t))
  · have ha' := not_le.1 ha
    have hb' := not_le.1 hb
    rw [cutoffLe_of_lt ha', cutoffLe_of_lt hb']
    refine ⟨fun _ => rfl, fun _ => ?_⟩
    obtain ⟨δ, hδ, hδa, hδb⟩ := exists_pos_add_le ha' hb'
    exact ⟨δ, hδ, by rw [min_eq_right hδa, min_eq_right hδb]⟩

end GuaranteedSubsol.CutoffLeProof
