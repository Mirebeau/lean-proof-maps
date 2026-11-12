/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.KruzkovRpowProof

/-!
# Frozen statement: change of Kruzkov timescale

Source: Complexity.tex, subsection "Complexity with unknown property constants" (equation before
Lemma lem:powr_diff), scalar form: if `v := E_α u` and `w := E_β u`, then `w = -(-v)^r` with
`r := α/β`. With inverse timescales, `E_α = kruzkov αinv` and `E_β = kruzkov (r * αinv)`.
Real `u`, as in the paper.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

theorem kruzkov_mul_eq_neg_rpow (αinv r u : ℝ) :
    kruzkov (r * αinv) u = -(-kruzkov αinv u) ^ r := by
  exact KruzkovRpowProof.kruzkov_mul_eq_neg_rpow αinv r u

end GuaranteedSubsol
