/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.AnbLazy
public import LeanHJBAutoformalisation.GuaranteedSubsol.DijkstraHeap

/-!
# The ANB with sorted lists (algo:anb_lazy)

Algorithm algo:anb_lazy (Complexity.tex), with the sorted lists stored in ordered partial maps
(`OrderedPartialMap`, a model of `std::set`). As in `AnbLazy`, the placeholder `⋄` of `ũ` is
`none` (`ũ` takes values in `Option ℝ`, author's ruling) and stands for `(n-1)τ`
(`ū = ũ^{⋄→(n-1)τ}`, `AnbHeapState.uSub`). The lists are:
* `L` (in the state of Dijkstra's method, `DijkstraHeapState`): the keys `max {ū, Γ ǔ}(x)` of the
  points where this is `< ǔ(x)` (eq. eqdef:L_heap);
* `M`: the keys `ũ(x)` of the points where `ũ(x) ≠ ⋄` and `(1 + ε) ũ(x) < u̲~(x)`
  (eq. eqdef:M_heap);
* `S`: the keys `ũ(x)` of the points where `ũ(x) ≠ ⋄` (eq. eqdef:S_heap);
* `Sc` (eq. eqdef:Sc_heap): the keys `u̲~(x)`, in reverse order, of
  the points where `ũ(x) = ⋄`, so that `bot` gives the largest of them. It makes the stopping test
  exactly that of algo:anb.

In iteration `n`, with `T = nτ`:
* line anb_lazy:Dijkstra: Dijkstra's method with the list `L`, for the operator `max {ū, Γ_∞}`
  and the stopping time `T` (`dijkstraHeapLoop`);
* line anb_lazy:olu_gets_hatu: for the points of `B_{n-1}`, the points selected by Dijkstra's
  method, and the points of `S` with key in `[(n-1)τ, T[` (as in the paper),
  `ũ(x) := ⋄` if `ǔ(x) = ∞` and `ū(x) < T` (as in the paper: the placeholder is set exactly when
  `T` is selected in `min {T, ǔ(x)}`), and `ũ(x) := max {ū(x), min {T, ǔ(x)}}` otherwise; update
  of `M`, `S`, `Sc`;
* line anb_lazy:tn: `t_n := min {T, smallest key of M}`; `Δ_n := T - t_n`;
* line anb_lazy:Bn: `B_n := {x | (ũ(x), x) ∈ S, T - 2Δ_n ≤ ũ(x) < T}`; `η_n := (1 - ρ) exp(-T/α)`;
* lines anb_lazy:while_sub, anb_lazy:while_sup: the inner loops on `B_n`, with the inner solver
  `S`, as in `AnbLazy`, from `ũ^{⋄→T}` and `u̲~`; line anb_lazy:update_MS: update of `M`, `S`, `Sc`;
* line anb_lazy:parallel_for2: `ǔ(x) := ∞` on `B_n`;
* line anb_lazy:L: the keys of `L` are recomputed, with `ū := ũ^{⋄→T}`, on `B_n` and the reversed
  stencils of its points.

The stopping test is `M = ∅` and `u̲~(x) ≤ (1 + ε)(n-1)τ` for the largest key of `Sc`
(`anbHeapDone`). The stencils `𝒱` of `Γ` are a parameter. Since the operator `Γ` is general, the
list `L` is initialized with the keys of all the points (`dijkstraHeapInit`), rather than of the
boundary points. As for the ANB, the iteration `n = 0` is vacuous.

The state records the operation counters: of `L` (`dij.L.count`), `M`, `S`, `Sc`, the number of
evaluations of `Γ` (`dij.evalCount`), the acceptances of Dijkstra's method at each point
(`dij.count`), and the numbers of updates of `ū` and `u̲~` at each point.
-/

@[expose] public section

namespace GuaranteedSubsol

variable {X : Type*}

/-- The key of `x` in the list `S` (eq. eqdef:S_heap): `ũ(x)` if it is not the placeholder (the map
`ũ` itself). -/
def anbKeyS (u : X → Option ℝ) : X → Option ℝ := u

/-- The key of `x` in the list `M` (eq. eqdef:M_heap): `ũ(x)` if it is not the placeholder and
`(1 + ε) ũ(x) < u̲~(x)`. -/
noncomputable def anbKeyM (ε : ℝ) (u : X → Option ℝ) (uSup : X → WithTop ℝ) : X → Option ℝ :=
  fun x => match u x with
    | none => none
    | some r => if (((1 + ε) * r : ℝ) : WithTop ℝ) < uSup x then some r else none

/-- The key of `x` in the list `Sc`: `u̲~(x)`, in the reverse order, if `ũ(x)` is the
placeholder. -/
def anbKeySc (u : X → Option ℝ) (uSup : X → WithTop ℝ) : X → Option (WithTop ℝ)ᵒᵈ :=
  fun x => match u x with
    | none => some (OrderDual.toDual (uSup x))
    | some _ => none

/-- The operator `max {ū, Γ_∞}` of the Dijkstra step, without the cutoff (the threshold `nτ` is the
stopping test of the loop). -/
noncomputable def anbHeapOp (Γ : (X → ℝ) → X → ℝ) (uSub : X → ℝ) :
    (X → WithTop ℝ) → X → WithTop ℝ :=
  fun u x => max (uSub x : WithTop ℝ) (Global.monotoneExtension Γ u x)

/-- State of the ANB with sorted lists: the iteration index `n`, the map `ũ` (`uTilde`; `none` is
the placeholder `⋄`, standing for `(n-1)τ`), the super-solution `u̲~` (`uSup`), the state of
Dijkstra's method (`ǔ`, the list `L`, the acceptance counts, the number of evaluations of `Γ`), the
lists `M`, `S`, `Sc`, the previous band `B_{n-1}` (`bandPrev`), and the numbers of updates of `ū`
and `u̲~` at each point. -/
structure AnbHeapState (X : Type*) where
  n : ℕ
  uTilde : X → Option ℝ
  uSup : X → WithTop ℝ
  dij : DijkstraHeapState X
  M : OrderedPartialMap X ℝ
  S : OrderedPartialMap X ℝ
  Sc : OrderedPartialMap X (WithTop ℝ)ᵒᵈ
  bandPrev : Finset X
  countSub : X → ℕ∞
  countSup : X → ℕ∞

namespace AnbHeapState

/-- The sub-solution `ū := ũ^{⋄→(n-1)τ}`. -/
def uSub (s : AnbHeapState X) (τ : ℝ) : X → ℝ :=
  fun x => (s.uTilde x).getD (((s.n : ℝ) - 1) * τ)

end AnbHeapState

variable [Fintype X] [LinearOrder X]

/-- Initial state: `ũ = ⋄`, `ǔ = u̲~ = ∞`, `M = S = ∅`, `Sc` holds all the points (`#X`
operations), `B_{-1} = ∅`, and `L` holds the keys of `max {0, Γ_∞}` at `ǔ = ∞` (`#X` evaluations
of `Γ` and operations; `0 = ⋄→0` is the value of the placeholder in the first effective iteration
`n = 1`). -/
noncomputable def anbHeapInit (Γ : (X → ℝ) → X → ℝ) : AnbHeapState X :=
  { n := 0, uTilde := fun _ => none, uSup := fun _ => ⊤
    dij := dijkstraHeapInit (anbHeapOp Γ 0) fun _ => ⊤
    M := ⟨fun _ => none, 0⟩, S := ⟨fun _ => none, 0⟩
    Sc := (⟨fun _ => none, 0⟩ : OrderedPartialMap X (WithTop ℝ)ᵒᵈ).set Finset.univ
      (anbKeySc (fun _ => none) fun _ => ⊤)
    bandPrev := ∅, countSub := 0, countSup := 0 }

/-- Stopping test: `M = ∅`, and the largest key `u̲~(x)` of `Sc` (if any) is
`≤ (1 + ε)(n-1)τ`. -/
def anbHeapDone (p : AnbParams X) (s : AnbHeapState X) : Prop :=
  (∀ x, s.M.v x = none) ∧ ∀ t x, OrderedPartialMap.botVal s.Sc.v = some (t, x) →
    OrderDual.ofDual t ≤ (((1 + p.ε) * (((s.n : ℝ) - 1) * p.τ) : ℝ) : WithTop ℝ)

/-- The quantities of one iteration of the ANB with sorted lists, in the order of the program. -/
structure AnbHeapStepData (X : Type*) where
  /-- The state of Dijkstra's method after line anb_lazy:Dijkstra. -/
  dij : DijkstraHeapState X
  /-- The points selected in line anb_lazy:Dijkstra (line Dijkstra:accept of algo:Dijkstra). -/
  selected : Finset X
  /-- The points updated in line anb_lazy:olu_gets_hatu. -/
  updated : Finset X
  /-- `ũ` after line anb_lazy:olu_gets_hatu. -/
  uTildeInit : X → Option ℝ
  /-- The lists `M`, `S`, `Sc` before line anb_lazy:update_MS. -/
  M : OrderedPartialMap X ℝ
  S : OrderedPartialMap X ℝ
  Sc : OrderedPartialMap X (WithTop ℝ)ᵒᵈ
  t : ℝ
  Δ : ℝ
  band : Finset X
  η : ℝ
  vSub : X → ℝ
  vSup : X → ℝ
  ΦSub : (↥(band : Set X) → ℝ) → ↥(band : Set X) → ℝ
  ΦSup : (↥(band : Set X) → ℝ) → ↥(band : Set X) → ℝ

open Classical in
/-- The quantities of the iteration started from the state `s`, with stencils `𝒱` (see the module
docstring). -/
noncomputable def anbHeapStepData (p : AnbParams X) (𝒱 : X → Set X) (s : AnbHeapState X) :
    AnbHeapStepData X :=
  let T : ℝ := s.n * p.τ
  let D := dijkstraHeapLoop (anbHeapOp p.Γ (s.uSub p.τ)) 𝒱 T s.dij
  let sel := Finset.univ.filter fun x => D.count x ≠ s.dij.count x
  let W := s.S.entriesIco ((s.n - 1) * p.τ) T
  let P := s.bandPrev ∪ sel ∪ W.1
  let uTildeInit : X → Option ℝ := fun x =>
    if x ∈ P then
      (if D.u x = ⊤ ∧ s.uSub p.τ x < T then none
        else some (max (s.uSub p.τ x) (min T ((D.u x).untopD T))))
    else s.uTilde x
  let M₁ := s.M.set P (anbKeyM p.ε uTildeInit s.uSup)
  let S₁ := W.2.set P (anbKeyS uTildeInit)
  let Sc₁ := s.Sc.set P (anbKeySc uTildeInit s.uSup)
  let bM := M₁.bot
  let t : ℝ := match bM.1 with
    | none => T
    | some (t, _) => min T t
  let B := S₁.entriesIco (T - 2 * (T - t)) T
  let uHat : X → ℝ := fun x => (uTildeInit x).getD T
  { dij := D, selected := sel, updated := P, uTildeInit := uTildeInit, M := bM.2, S := B.2
    Sc := Sc₁, t := t, Δ := T - t, band := B.1
    η := (1 - p.ρ) * Real.exp (-T / p.α)
    vSub := fun x => kruzkov (1 / p.α) (uHat x)
    vSup := fun x => kruzkov (1 / p.α) (s.uSup x)
    ΦSub := bandOp (Global.kruzkovOp p.α p.Λ) B.1 fun x => kruzkov (1 / p.α) (uHat x)
    ΦSup := bandOp (Global.kruzkovOp p.α p.Λ) B.1 fun x => kruzkov (1 / p.α) (s.uSup x) }

open Classical in
/-- One iteration of the ANB with sorted lists, inner solver `S` and stencils `𝒱`: the inner loops
on the band (as in `AnbLazy`), the update of `M`, `S`, `Sc`, the reset of `ǔ` on the band, and the
update of the keys of `L`. -/
noncomputable def anbHeapStepWith (S : AnbInnerSolver X) (p : AnbParams X) (𝒱 : X → Set X)
    (s : AnbHeapState X) : AnbHeapState X :=
  let d := anbHeapStepData p 𝒱 s
  let T : ℝ := s.n * p.τ
  let B : Set X := d.band
  let wSub : X → ℝ := bandExtend B d.vSub (S.subResult B d.ΦSub d.η fun x => d.vSub x)
  let wSup : X → ℝ := bandExtend B d.vSup (S.supResult B d.ΦSup d.η fun x => d.vSup x)
  let uTilde : X → Option ℝ := fun x =>
    if x ∈ d.band then some (-p.α * Real.log (-wSub x)) else d.uTildeInit x
  let uSup : X → WithTop ℝ := fun x => kruzkovInv p.α (wSup x)
  let uCheck : X → WithTop ℝ := fun x => if x ∈ d.band then ⊤ else d.dij.u x
  let uSubNext : X → ℝ := fun x => (uTilde x).getD T
  let R := d.band ∪ d.band.biUnion (Global.Ext.revStencil 𝒱)
  { n := s.n + 1
    uTilde := uTilde
    uSup := uSup
    dij := { u := uCheck, count := d.dij.count
             L := d.dij.L.set R (dijkstraKey (anbHeapOp p.Γ uSubNext) uCheck)
             evalCount := d.dij.evalCount + R.card }
    M := d.M.set d.band (anbKeyM p.ε uTilde uSup)
    S := d.S.set d.band (anbKeyS uTilde)
    Sc := d.Sc.set d.band (anbKeySc uTilde uSup)
    bandPrev := d.band
    countSub := fun x =>
      s.countSub x + if x ∈ d.band then S.subCount B d.ΦSub d.η (fun y => d.vSub y) x else 0
    countSup := fun x =>
      s.countSup x + if x ∈ d.band then S.supCount B d.ΦSup d.η (fun y => d.vSup y) x else 0 }

/-- The state of the ANB with sorted lists after `k` iterations. -/
noncomputable def anbHeapRunWith (S : AnbInnerSolver X) (p : AnbParams X) (𝒱 : X → Set X)
    (k : ℕ) : AnbHeapState X :=
  (anbHeapStepWith S p 𝒱)^[k] (anbHeapInit p.Γ)

/-- The quantities of iteration `n = k` of the ANB with sorted lists. -/
noncomputable def anbHeapRunDataWith (S : AnbInnerSolver X) (p : AnbParams X) (𝒱 : X → Set X)
    (k : ℕ) : AnbHeapStepData X :=
  anbHeapStepData p 𝒱 (anbHeapRunWith S p 𝒱 k)

open Classical in
/-- The iteration at which the ANB with sorted lists terminates: the first `k` such that the
stopping test holds at the start of iteration `k` (`⊤` if it never holds). -/
noncomputable def anbHeapStopIndexWith (S : AnbInnerSolver X) (p : AnbParams X)
    (𝒱 : X → Set X) : ℕ∞ :=
  if h : ∃ k, anbHeapDone p (anbHeapRunWith S p 𝒱 k) then (Nat.find h : ℕ∞) else ⊤

/-- `countB'(x)`: the number of selections of `x` in line anb_lazy:Dijkstra (line Dijkstra:accept;
updates by Dijkstra's method) in the iterations `k < K` of the ANB with sorted lists. By
Prop. prop:Dijkstra_band, they lie in the bands `B'_n` (formalized for algo:anb with the global
iteration, `anbRun_hatRun_count_mem`). -/
noncomputable def anbHeapCountB' (S : AnbInnerSolver X) (p : AnbParams X) (𝒱 : X → Set X) (K : ℕ)
    (x : X) : ℕ :=
  (anbHeapRunWith S p 𝒱 K).dij.count x

/-- `countB(x)`: the number of iterations `k < K` of the ANB with sorted lists in which `x` is in
the narrow band `B_k`. -/
noncomputable def anbHeapCountB (S : AnbInnerSolver X) (p : AnbParams X) (𝒱 : X → Set X) (K : ℕ)
    (x : X) : ℕ :=
  ((Finset.range K).filter fun k => x ∈ (anbHeapRunDataWith S p 𝒱 k).band).card

end GuaranteedSubsol
