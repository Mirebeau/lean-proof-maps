/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.WithBot

/-!
# Cutoff above a level

The map `a ↦ a^{<t}` of eq. eqdef:u_less_t (Complexity.tex; used in
Prop. prop:causal_formulation), on `ℝ_∞ = WithTop ℝ`: values below `t` are kept, the others are
sent to `∞`. Applied pointwise to `u : X → ℝ_∞`, it gives `u^{<t}`. Likewise `a ↦ a^{≤t}` keeps
the values `≤ t`.
-/

namespace GuaranteedSubsol

/-- Cutoff `a^{<t}` (Complexity.tex, eq. eqdef:u_less_t, left): `a` if `a < t`, and `∞`
otherwise. -/
noncomputable def cutoffLt (t : ℝ) (a : WithTop ℝ) : WithTop ℝ :=
  if a < t then a else ⊤

theorem cutoffLt_of_lt {t : ℝ} {a : WithTop ℝ} (h : a < t) : cutoffLt t a = a := by
  simp [cutoffLt, h]

theorem cutoffLt_of_le {t : ℝ} {a : WithTop ℝ} (h : (t : WithTop ℝ) ≤ a) : cutoffLt t a = ⊤ := by
  simp [cutoffLt, not_lt.2 h]

/-- Cutoff `a^{≤t}` (Complexity.tex, eq. eqdef:u_less_t, right): `a` if `a ≤ t`, and `∞`
otherwise. -/
noncomputable def cutoffLe (t : ℝ) (a : WithTop ℝ) : WithTop ℝ :=
  if a ≤ t then a else ⊤

theorem cutoffLe_of_le {t : ℝ} {a : WithTop ℝ} (h : a ≤ t) : cutoffLe t a = a := by
  simp [cutoffLe, h]

theorem cutoffLe_of_lt {t : ℝ} {a : WithTop ℝ} (h : (t : WithTop ℝ) < a) : cutoffLe t a = ⊤ := by
  simp [cutoffLe, not_le.2 h]

end GuaranteedSubsol
