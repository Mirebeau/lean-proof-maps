/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.CausalSubaddProof

/-!
# Frozen statement: causality implies sub-additivity in Kruzkov coordinates

Source: Prop. prop:causal_implies_subadd (Subadd.tex), scalar form: if `Λ` is monotone, causal,
additively invariant, `ν`-sub-multiplicative and has `C`-memory (`C = C_past`), with `ν, C > 0`,
then `Φ_α` is `ρ`-sub-additive for any `α > 0`, where `ρ := 1 - (ν/C)(1 - exp(-C/α))`. The
paper's remark `ρ < 1` is not part of the statement. Author ruling: the assumption `ν > 0` is
dropped, being unneeded. `X` is finite (standing assumption).

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem subAdditive_kruzkovOp_of_causal {X : Type*} [Finite X] {Λ : (X → ℝ) → ℝ}
    (hmono : Monotone Λ) (hcaus : Causal Λ) (hadd : AdditivelyInvariant Λ) {ν C α : ℝ}
    (hC : 0 < C) (hsubm : SubMultiplicative ν Λ) (hmem : HasMemory C Λ)
    (hα : 0 < α) :
    SubAdditive (1 - ν / C * (1 - Real.exp (-C / α))) (kruzkovOp α Λ) := by
  exact CausalSubaddProof.subAdditive_kruzkovOp_of_causal hmono hcaus hadd hC hsubm hmem hα

end GuaranteedSubsol
