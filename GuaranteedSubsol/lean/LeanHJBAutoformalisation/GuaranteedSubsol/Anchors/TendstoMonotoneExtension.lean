/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.MonotoneExtension
import Mathlib.Topology.Order.WithTop

/-!
# Frozen statement: `Λ_∞ u = lim_{t→∞} Λ min {u,t}`

Source: Intro.tex eq. eqdef:monotone_extension, `Λ_∞ u := lim_{t→∞} Λ min {u,t}`, for monotone `Λ`.
Agreement of the generalized `monotoneExtension` (supremum over finite minorants) with the
paper's definition. `WithTop ℝ` carries the order topology, i.e. that of `]-∞,∞]`.

`[Finite X]` is needed: on an infinite `X`, a finite minorant `w ≤ u` may be unbounded above,
and then is not below any truncation `min {u,t}`. The paper's `X` is finite.

State: see `ANCHORS.md`.
-/

namespace GuaranteedSubsol

open Filter Topology

theorem tendsto_monotoneExtension {X : Type*} [Finite X] {Λ : (X → ℝ) → ℝ} (hΛ : Monotone Λ)
    (u : X → WithTop ℝ) :
    Tendsto (fun t : ℝ => ((Λ fun y => min ((u y).untopD t) t : ℝ) : WithTop ℝ)) atTop
      (𝓝 (monotoneExtension Λ u)) := by exact MonotoneExtension.tendsto hΛ u

end GuaranteedSubsol
