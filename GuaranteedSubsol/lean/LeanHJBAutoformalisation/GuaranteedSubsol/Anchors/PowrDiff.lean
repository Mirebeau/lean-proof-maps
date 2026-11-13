/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.PowrDiffProof

/-!
# Frozen statement: difference of powers

Source: Lemma lem:powr_diff (Complexity.tex): for all `a, b ≥ 0` and `r ∈ [0,1]`,
`|a^r - b^r| ≤ |a - b|^r` (real powers `Real.rpow`). The paper assumes `r ∈ ]0,1]`; the case
`r = 0` also holds (author ruling: `0 ≤ r`).

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem abs_rpow_sub_rpow_le {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    |a ^ r - b ^ r| ≤ |a - b| ^ r := by
  exact PowrDiffProof.abs_rpow_sub_rpow_le ha hb hr₀ hr₁

end GuaranteedSubsol
