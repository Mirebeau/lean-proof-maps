/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.Kruzkov

/-!
# AGSIK

The AGSI with Kruzkov based intermediate stopping criteria, Algorithm algo:agsik (AGSI2.tex),
modelled as a step function on a state. The map `u` takes values in `ℝ_∞ = WithTop ℝ` (it is
initialized to `+∞`), and so does the operator `Λ : (X → ℝ_∞) → X → ℝ_∞`; for a real-valued
monotone operator, this is its monotone extension `Λ_∞`.

One step is: a parallel pass of line agsik:parallel_for at the current level `n`, if some point is
selected; otherwise stay put if the stopping criterion `u ≤ Λ u + ε` holds; otherwise `n ← n + 1`.
This is the nested loop of the algorithm, except that the paper increments `n` once more before
testing the stopping criterion.

With `-kruzkov αinv a = exp(-a/α)` (and `+∞ ↦ 0`), `αinv = 1/α`, the selection criterion
`exp(-Λu/α) ≥ exp((ε-u)/α) + 2^{-n}` reads
`2^{-n} + exp(ε/α) (-kruzkov αinv u) ≤ -kruzkov αinv (Λ u)`.

The state also records the number of updates at each point.
-/

@[expose] public section

namespace GuaranteedSubsol

variable {X : Type*}

/-- State of the AGSIK (algo:agsik): the main iteration index `n`, the map `u`, and the number
`count x` of updates `u(x) ← Λ u(x)` performed so far at each point. -/
structure AgsikState (X : Type*) where
  n : ℕ
  u : X → WithTop ℝ
  count : X → ℕ

/-- Selection criterion of line agsik:parallel_for at level `n`:
`exp(-Λu(x)/α) ≥ exp((ε-u(x))/α) + 2^{-n}`, with `αinv = 1/α`. -/
def agsikSelect (Λ : (X → WithTop ℝ) → X → WithTop ℝ) (αinv ε : ℝ) (n : ℕ)
    (u : X → WithTop ℝ) (x : X) : Prop :=
  (2 : ℝ)⁻¹ ^ n + Real.exp (αinv * ε) * -kruzkov αinv (u x) ≤ -kruzkov αinv (Λ u x)

/-- Stopping criterion of the main loop of algo:agsik: `u ≤ Λ u + ε` on `X`. -/
def agsikDone (Λ : (X → WithTop ℝ) → X → WithTop ℝ) (ε : ℝ) (u : X → WithTop ℝ) : Prop :=
  ∀ x, u x ≤ Λ u x + (ε : WithTop ℝ)

/-- Initialization of algo:agsik: `n = 0`, `u = +∞`, no updates. -/
def agsikInit : AgsikState X := ⟨0, fun _ => ⊤, 0⟩

open Classical in
/-- One step of the AGSIK (algo:agsik): a parallel pass `u(x) ← Λ u(x)` on the selected points
at level `n` if there are any; otherwise stay put if `u ≤ Λ u + ε`; otherwise `n ← n + 1`. -/
noncomputable def agsikStep (Λ : (X → WithTop ℝ) → X → WithTop ℝ) (αinv ε : ℝ)
    (s : AgsikState X) : AgsikState X :=
  if ∃ x, agsikSelect Λ αinv ε s.n s.u x then
    { n := s.n
      u := fun x => if agsikSelect Λ αinv ε s.n s.u x then Λ s.u x else s.u x
      count := fun x => if agsikSelect Λ αinv ε s.n s.u x then s.count x + 1 else s.count x }
  else if agsikDone Λ ε s.u then s
  else { s with n := s.n + 1 }

/-- The state of algo:agsik after `k` steps, started from `u = +∞` (`agsikInit`). -/
noncomputable def agsikRun (Λ : (X → WithTop ℝ) → X → WithTop ℝ) (αinv ε : ℝ) (k : ℕ) :
    AgsikState X :=
  (agsikStep Λ αinv ε)^[k] agsikInit

end GuaranteedSubsol
