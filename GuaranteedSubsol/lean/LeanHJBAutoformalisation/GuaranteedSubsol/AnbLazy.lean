/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.Anb
import LeanHJBAutoformalisation.GuaranteedSubsol.Cutoff

/-!
# The ANB with a placeholder (AnbEquivalence note)

A program equivalent to algo:anb (Papers/AnbEquivalence, `Claude_AnbEquivalence.tex`), which stores
the sub-solution as `ũ ∈ ℝ_⋄^X` (`Option ℝ`; author's decision), where the value `⋄ = none` is a
placeholder for `(n-1)τ` (`ū = ũ^{⋄→(n-1)τ}`, `AnbLazyState.uSub`), and the initial guess of
Dijkstra's method as `ǔ^init ∈ ℝ_∞^X`, from which the guess of the ANB is recovered as
`û^init = min {ǔ^init, max {ū, nτ}}` (`AnbLazyState.uHatInit`). In iteration `n`, with `T = nτ`:
* Dijkstra's method, started from `ǔ^init`, solves `ǔ = max {ū, Γ ǔ}^{<T}` (`anbCheckOp`);
* `ũ^init(x) := ⋄` if `ǔ(x) = ∞` and `ū(x) < T`, and `max {ū, min {ǔ, T}}(x)` otherwise;
* `t_n := min {T, min {ũ^init(x) | (1 + ε) ũ^init(x) < u̲~(x)}}` (`anbLazyLevel`; the placeholder
  never satisfies the condition), `Δ_n := T - t_n`, `t⁻_n := T - 2Δ_n`,
  `η_n := (1 - ρ) exp(-T/α)`, and `B_n := {T - 2Δ_n ≤ ũ^init < T}`;
* `ǔ^init` of the next iteration is `ǔ^{<t⁻_n}`;
* the inner loops are run on `B_n` with the inner solver `S`, as in the ANB (`anbStepWith`), from
  `(ũ^init)^{⋄→T}` and from `u̲~`, the values outside `B_n` being frozen to these maps; outside
  `B_n`, the next `ũ` is `ũ^init` (placeholders included).

The stopping test is `(1 + ε) ũ^{⋄→(n-1)τ} ≥ u̲~` (`anbLazyDone`), and the initial state is
`ũ_0 = 0`, `u̲~_0 = ∞`, `ǔ_0^init = ∞`, with the iteration `n = 0` vacuous as for the ANB.
-/

namespace GuaranteedSubsol

variable {X : Type*}

/-- State of the ANB with a placeholder: the iteration index `n`, the map `ũ` (`uTilde`), whose
value `none` (`⋄`) is a placeholder for `(n-1)τ`, the super-solution `u̲~` (`uSup`), the
initial guess `ǔ^init` (`uCheckInit`) for Dijkstra's method, and the numbers of updates of `ū`,
`u̲~` and `ǔ` at each point. -/
structure AnbLazyState (X : Type*) where
  n : ℕ
  uTilde : X → Option ℝ
  uSup : X → WithTop ℝ
  uCheckInit : X → WithTop ℝ
  countSub : X → ℕ∞
  countSup : X → ℕ∞
  countHat : X → ℕ

namespace AnbLazyState

/-- The sub-solution `ū := ũ^{⋄→(n-1)τ}`: the placeholder `⋄ = none` stands for `(n-1)τ`. -/
def uSub (s : AnbLazyState X) (τ : ℝ) : X → ℝ :=
  fun x => (s.uTilde x).getD (((s.n : ℝ) - 1) * τ)

/-- The initial guess of the ANB, `û^init := min {ǔ^init, max {ū, nτ}}`. -/
def uHatInit (s : AnbLazyState X) (τ : ℝ) : X → WithTop ℝ :=
  fun x => min (s.uCheckInit x) ((max (s.uSub τ x) (s.n * τ) : ℝ) : WithTop ℝ)

end AnbLazyState

/-- Initial state: `ũ_0 = 0` (no placeholder), `u̲~_0 = ∞`, `ǔ_0^init = ∞`, no updates. -/
def anbLazyInit : AnbLazyState X := ⟨0, fun _ => some 0, fun _ => ⊤, fun _ => ⊤, 0, 0, 0⟩

/-- Stopping test `(1 + ε) ũ^{⋄→(n-1)τ} ≥ u̲~`. -/
def anbLazyDone (p : AnbParams X) (s : AnbLazyState X) : Prop :=
  ∀ x, s.uSup x ≤ (((1 + p.ε) * s.uSub p.τ x : ℝ) : WithTop ℝ)

/-- The operator `u ↦ max {ū, Γ_∞ u}^{<T}` of the Dijkstra step. -/
noncomputable def anbCheckOp (Γ : (X → ℝ) → X → ℝ) (uSub : X → ℝ) (T : ℝ) :
    (X → WithTop ℝ) → X → WithTop ℝ :=
  fun u x => cutoffLt T (max (uSub x : WithTop ℝ) (Global.monotoneExtension Γ u x))

open Classical in
/-- `t_n := min {T, min {ũ^init(x) | (1 + ε) ũ^init(x) < u̲~(x)}}`, the placeholder `none` never
satisfying the condition; it is `T` if the set is empty. -/
noncomputable def anbLazyLevel [Fintype X] (ε T : ℝ) (uTildeInit : X → Option ℝ)
    (uSup : X → WithTop ℝ) : ℝ :=
  let S := Finset.univ.filter fun x =>
    uTildeInit x ≠ none ∧ (((1 + ε) * (uTildeInit x).getD T : ℝ) : WithTop ℝ) < uSup x
  if h : S.Nonempty then min T (S.inf' h fun x => (uTildeInit x).getD T) else T

/-- The quantities of one iteration of the ANB with a placeholder, computed from the state at its
start: Dijkstra's run, `ǔ`, `ũ^init`, its value `û := (ũ^init)^{⋄→T}` (`uHat`), `t_n`, `Δ_n`,
`B_n`, `η_n`, the inputs of the inner loops in Kruzkov coordinates, and the operators acting on the
band. -/
structure AnbLazyStepData (X : Type*) where
  checkRun : DijkstraState X
  uCheck : X → WithTop ℝ
  uTildeInit : X → Option ℝ
  uHat : X → ℝ
  t : ℝ
  Δ : ℝ
  band : Set X
  η : ℝ
  vSub : X → ℝ
  vSup : X → ℝ
  ΦSub : (band → ℝ) → band → ℝ
  ΦSup : (band → ℝ) → band → ℝ

open Classical in
/-- The quantities of the iteration started from the state `s` (see the module docstring). -/
noncomputable def anbLazyStepData [Fintype X] [LinearOrder X] (p : AnbParams X)
    (s : AnbLazyState X) : AnbLazyStepData X :=
  let T : ℝ := s.n * p.τ
  let D := dijkstraRun (anbCheckOp p.Γ (s.uSub p.τ) T) s.uCheckInit (Nat.card X)
  let uTildeInit : X → Option ℝ := fun x =>
    if D.u x = ⊤ ∧ s.uSub p.τ x < T then none
    else some (max (s.uSub p.τ x) (min ((D.u x).untopD T) T))
  let uHat : X → ℝ := fun x => (uTildeInit x).getD T
  let t := anbLazyLevel p.ε T uTildeInit s.uSup
  let B : Set X := {x | ∃ r, uTildeInit x = some r ∧ T - 2 * (T - t) ≤ r ∧ r < T}
  { checkRun := D, uCheck := D.u, uTildeInit := uTildeInit, uHat := uHat, t := t, Δ := T - t,
    band := B
    η := (1 - p.ρ) * Real.exp (-T / p.α)
    vSub := fun x => kruzkov (1 / p.α) (uHat x)
    vSup := fun x => kruzkov (1 / p.α) (s.uSup x)
    ΦSub := bandOp (Global.kruzkovOp p.α p.Λ) B fun x => kruzkov (1 / p.α) (uHat x)
    ΦSup := bandOp (Global.kruzkovOp p.α p.Λ) B fun x => kruzkov (1 / p.α) (s.uSup x) }

open Classical in
/-- One iteration of the ANB with a placeholder, with the inner solver `S`: on the band, the
results of the inner loops (extended by the frozen values outside the band), converted back from
Kruzkov coordinates; outside the band, `ũ := ũ^init` (placeholders included); the next guess
`ǔ^{<t⁻_n}`; the counters. -/
noncomputable def anbLazyStepWith [Fintype X] [LinearOrder X] (S : AnbInnerSolver X)
    (p : AnbParams X) (s : AnbLazyState X) : AnbLazyState X :=
  let d := anbLazyStepData p s
  let T : ℝ := s.n * p.τ
  let wSub : X → ℝ :=
    bandExtend d.band d.vSub (S.subResult d.band d.ΦSub d.η fun x => d.vSub x)
  let wSup : X → ℝ := bandExtend d.band d.vSup (S.supResult d.band d.ΦSup d.η fun x => d.vSup x)
  { n := s.n + 1
    uTilde := fun x => if x ∈ d.band then some (-p.α * Real.log (-wSub x))
      else d.uTildeInit x
    uSup := fun x => kruzkovInv p.α (wSup x)
    uCheckInit := fun x => cutoffLt (T - 2 * d.Δ) (d.uCheck x)
    countSub := fun x =>
      s.countSub x + if x ∈ d.band then S.subCount d.band d.ΦSub d.η (fun y => d.vSub y) x else 0
    countSup := fun x =>
      s.countSup x + if x ∈ d.band then S.supCount d.band d.ΦSup d.η (fun y => d.vSup y) x else 0
    countHat := fun x => s.countHat x + d.checkRun.count x }

/-- The state of the ANB with a placeholder and inner solver `S`, after `k` iterations. -/
noncomputable def anbLazyRunWith [Fintype X] [LinearOrder X] (S : AnbInnerSolver X)
    (p : AnbParams X) (k : ℕ) : AnbLazyState X :=
  (anbLazyStepWith S p)^[k] anbLazyInit

/-- The quantities of iteration `n = k` of the ANB with a placeholder and inner solver `S`. -/
noncomputable def anbLazyRunDataWith [Fintype X] [LinearOrder X] (S : AnbInnerSolver X)
    (p : AnbParams X) (k : ℕ) : AnbLazyStepData X :=
  anbLazyStepData p (anbLazyRunWith S p k)

open Classical in
/-- The iteration at which the ANB with a placeholder terminates: the first `k` such that the
stopping test holds at the start of iteration `k` (`⊤` if it never holds). -/
noncomputable def anbLazyStopIndexWith [Fintype X] [LinearOrder X] (S : AnbInnerSolver X)
    (p : AnbParams X) : ℕ∞ :=
  if h : ∃ k, anbLazyDone p (anbLazyRunWith S p k) then (Nat.find h : ℕ∞) else ⊤

end GuaranteedSubsol
