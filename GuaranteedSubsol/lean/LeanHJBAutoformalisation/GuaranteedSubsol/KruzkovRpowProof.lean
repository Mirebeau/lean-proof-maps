/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.Kruzkov
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Ring

/-!
# Change of Kruzkov timescale: proof

Provider proof for the frozen anchor `GuaranteedSubsol.kruzkov_mul_eq_neg_rpow` (see
`ANCHORS.md`): Complexity.tex, subsection "Complexity with unknown properties constants",
`E_β u = -(-E_α u)^r` with `r = α/β`, i.e. `βinv = r * αinv`. One has
`(-E_α u)^r = (exp(-αinv u))^r = exp(-r αinv u)` by `Real.exp_mul`.
-/

@[expose] public section

namespace GuaranteedSubsol.KruzkovRpowProof

theorem kruzkov_mul_eq_neg_rpow (αinv r u : ℝ) :
    kruzkov (r * αinv) u = -(-kruzkov αinv u) ^ r := by
  simp only [kruzkov, neg_neg]
  rw [← Real.exp_mul]
  congr 2
  ring

end GuaranteedSubsol.KruzkovRpowProof
