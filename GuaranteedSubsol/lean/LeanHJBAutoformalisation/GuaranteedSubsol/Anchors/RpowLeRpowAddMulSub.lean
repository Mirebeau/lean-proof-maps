/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.PowCvxProof

/-!
# Frozen statement: the tangent inequality for `t ↦ t^s`

Source: Lemma lem:pow_cvx (Complexity.tex, V1): for `0 ≤ a ≤ b` and `s ≥ 1`,
`b^s ≤ a^s + s b^{s-1} (b - a)` (real powers, `Real.rpow`).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem rpow_le_rpow_add_mul_sub {a b s : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hs : 1 ≤ s) :
    b ^ s ≤ a ^ s + s * b ^ (s - 1) * (b - a) := by
  exact PowCvxProof.rpow_le_rpow_add_mul_sub ha hab hs

end GuaranteedSubsol
