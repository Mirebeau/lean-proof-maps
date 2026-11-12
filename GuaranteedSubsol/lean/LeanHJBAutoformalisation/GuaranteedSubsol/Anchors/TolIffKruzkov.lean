/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.TolKruzkovProof

/-!
# Frozen statement: the tolerance criterion in Kruzkov coordinates

Source: Complexity.tex, eq. (tol_as_Kruzkov), scalar form:
`(1+ε) ū ≥ u̲ ⇔ v̄ exp(-ε ū/α) ≥ v̲`, where `v̄ := E_α ū` and `v̲ := E_α u̲`.
Here `E_α = kruzkov αinv`, with `αinv = 1/α > 0`. The value `u̲ ∈ ℝ_∞ = WithTop ℝ` may be
infinite (as for the super-solution of the ANB method), while `ū ∈ ℝ`.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem le_mul_iff_kruzkov {αinv ε : ℝ} (hα : 0 < αinv) (uSub : ℝ) (uSup : WithTop ℝ) :
    uSup ≤ (((1 + ε) * uSub : ℝ) : WithTop ℝ) ↔
      kruzkov αinv uSup ≤ kruzkov αinv uSub * Real.exp (-ε * αinv * uSub) := by
  exact TolKruzkovProof.le_mul_iff_kruzkov hα uSub uSup

end GuaranteedSubsol
