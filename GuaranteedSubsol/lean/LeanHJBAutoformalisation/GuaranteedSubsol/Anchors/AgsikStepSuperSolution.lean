/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.AgsikProof

/-!
# Frozen statement: the AGSIK preserves super-solutions

Source: Algorithm algo:agsik (AGSI2.tex), "Ensures at termination: `Λ u ≤ u`": for a monotone
`Λ` on `ℝ_∞`, if `Λ u ≤ u` (e.g. `u = +∞` at initialization), this remains true at all times.

State: see `ANCHORS.md`.
-/

@[expose] public section

namespace GuaranteedSubsol

theorem agsikStep_superSolution {X : Type*} {Λ : (X → WithTop ℝ) → X → WithTop ℝ}
    (hmono : Monotone Λ) (αinv ε : ℝ) {s : AgsikState X} (hs : Λ s.u ≤ s.u) (k : ℕ) :
    Λ ((agsikStep Λ αinv ε)^[k] s).u ≤ ((agsikStep Λ αinv ε)^[k] s).u := by
  exact AgsikProof.superSolution hmono αinv ε hs k

end GuaranteedSubsol
