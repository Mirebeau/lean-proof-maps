/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.Dijkstra
import LeanHJBAutoformalisation.GuaranteedSubsol.GlobalIteration
import LeanHJBAutoformalisation.GuaranteedSubsol.ParallelAGSI
import LeanHJBAutoformalisation.GuaranteedSubsol.Kruzkov
import LeanHJBAutoformalisation.GuaranteedSubsol.Band
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Adaptive Narrow Band (ANB)

Algorithm algo:anb (Intro.tex), modelled as a step function on a state (as requested by a V0
`\formalizationInstruction`, removed in V1):
* the state holds `n`, the sub-solution `ū` (`uSub`), the super-solution `u̲` (`uSup`), and the
  numbers of updates of `ū`, `u̲` and `û` at each point;
* line anb:hatu computes `û_n` with Dijkstra's method (algo:Dijkstra), applied to
  `Γ' := max (ū, min (nτ, Γ_∞))` from the initial guess `uHatInit` stored in the state: `0` at
  `n = 0`, and afterwards the guess `u` of eq. eqdef:Dijkstra_supsol (Prop. prop:Dijkstra_band),
  built at the end of the previous iteration (`anbDijkstraGuess`);
* line anb:hatu2 is skipped: `t_n`, `Δ_n` and `B_n` are computed from `û_n`;
* lines anb:while_sub and anb:while_sup are calls to the global iteration (algo:global_iteration)
  on the narrow band `B_n`, in Kruzkov coordinates `v = E_α u`: the iteration acts on the maps on
  the subtype `B_n`, through the operator `bandOp Φ_α B_n w` (`Band.lean`), the values outside
  `B_n` being frozen to `w := E_α û_n` (resp. `E_α u̲`); the criterion
  `exp(-ū/α) ≤ exp(-Λū/α) + η_n` on `B_n` reads `Φ_α v - v ≤ η_n` (sub-solution variant, started
  from `E_α û_n`), and `exp(-Λu̲/α) ≤ exp(-u̲/α) + η_n` reads `v - Φ_α v ≤ η_n` (super-solution
  version, started from `E_α u̲`). The results on `B_n` are extended by the frozen values outside
  `B_n`.

The iterations are numbered from `n = 0` rather than `n = 1` (Remark rem:anb_npos), so that
`anbRun p k` is the state at the start of iteration `n = k`; the iteration `n = 0` is vacuous.
The step `anbStep` is the body of the main loop; the stopping test `(1 + ε) ū ≥ u̲` of line anb:for
is a property of the run (`anbDone`, `anbStopIndex`), after which the iterations continue but leave
`u̲` unchanged (the band is empty).

The quantities of iteration `n` (`û_n`, `t_n`, `Δ_n`, `B_n`, `η_n`, ...) are not stored in the
state: they are computed from the state at the start of the iteration by `anbStepData`.

The inner solver of lines anb:while_sub and anb:while_sup is a parameter (`AnbInnerSolver`) of the
step `anbStepWith`, of the run `anbRunWith`, etc.: the ANB itself (`anbStep`, `anbRun`, ...) uses
the global iteration (`anbGlobalIter`), and the variant of Theorem th:complexity_with_agsi
(`anbAgsiRun`, ...) uses the parallel AGSI (`anbAgsi`, algo:agsi_parallel).
-/

namespace GuaranteedSubsol

variable {X : Type*}

/-- Parameters of algo:anb: the scheme `Λ`, its causal underestimate `Γ` (line anb:hatu), the
tolerance `ε`, and the constants `τ`, `α`, `ρ` of line anb:input. -/
structure AnbParams (X : Type*) where
  Λ : (X → ℝ) → X → ℝ
  Γ : (X → ℝ) → X → ℝ
  ε : ℝ
  τ : ℝ
  α : ℝ
  ρ : ℝ

/-- State of algo:anb: iteration index `n`, sub-solution `ū`, super-solution `u̲`, the initial
guess `uHatInit` for Dijkstra's method at line anb:hatu (built at the end of the previous iteration,
see Prop. prop:Dijkstra_band and `anbDijkstraGuess`), and the number of updates of `ū`, `u̲` and `û`
performed so far at each point. The counters of `ū` and `u̲` take values in `ℕ∞`: they become `⊤`
when an inner loop (lines anb:while_sub, anb:while_sup) involving the point never exits, so that a
bound on them also expresses termination; Dijkstra's method always performs `card X` steps, and the
counter of `û` is in `ℕ`. -/
structure AnbState (X : Type*) where
  n : ℕ
  uSub : X → ℝ
  uSup : X → WithTop ℝ
  uHatInit : X → WithTop ℝ
  countSub : X → ℕ∞
  countSup : X → ℕ∞
  countHat : X → ℕ

/-- Line anb:init, starting at `n = 0` (Remark rem:anb_npos: the iteration `n = 0` is vacuous):
`ū = 0`, `u̲ = ∞`, initial guess `0` for `û` (the natural super-solution at the start; the
iteration `n = 0` then computes `û_0 = 0` and `t⁻_0 = 0`, the conventions of
Prop. prop:Dijkstra_band), no updates. -/
def anbInit : AnbState X := ⟨0, 0, fun _ => ⊤, 0, 0, 0, 0⟩

/-- Stopping criterion of line anb:for: `(1 + ε) ū ≥ u̲` on `X`. -/
def anbDone (p : AnbParams X) (s : AnbState X) : Prop :=
  ∀ x, s.uSup x ≤ (((1 + p.ε) * s.uSub x : ℝ) : WithTop ℝ)

/-- Line anb:hatu: the operator `Γ' u := max (ū, min (T, Γ_∞ u))`, with `T = nτ`, whose fixed point
is `û_n` (Prop. prop:Dijkstra_band). -/
noncomputable def anbHatOp (Γ : (X → ℝ) → X → ℝ) (uSub : X → ℝ) (T : ℝ) :
    (X → WithTop ℝ) → X → WithTop ℝ :=
  fun u x => max (uSub x : WithTop ℝ) (min (T : WithTop ℝ) (Global.monotoneExtension Γ u x))

open Classical in
/-- Line anb:tn: `t_n := min (T, min {û(x) | (1 + ε) û(x) < u̲(x)})`, with `T = nτ`; it is `T` if
this set is empty. -/
noncomputable def anbLevel [Fintype X] (ε T : ℝ) (uHat : X → ℝ) (uSup : X → WithTop ℝ) : ℝ :=
  let S := Finset.univ.filter fun x => (((1 + ε) * uHat x : ℝ) : WithTop ℝ) < uSup x
  if h : S.Nonempty then min T (S.inf' h uHat) else T

/-- Line anb:Bn: `B_n := {x | T - 2Δ ≤ û(x) < T}`, with `T = nτ` and `Δ = Δ_n`. -/
def anbBand (T Δ : ℝ) (uHat : X → ℝ) : Set X :=
  {x | T - 2 * Δ ≤ uHat x ∧ uHat x < T}

/-- The quantities of one iteration of algo:anb, computed from the state at its start: Dijkstra's
run for `û_n`, `û_n`, `t_n`, `Δ_n`, `B_n`, `η_n`, the inputs `E_α û_n`, `E_α u̲` of the two global
iterations, and the operators `Φ_α` acting on the band `B_n`, the values outside `B_n` being frozen
to `E_α û_n` (sub-solution variant) and to `E_α u̲` (super-solution version). -/
structure AnbStepData (X : Type*) where
  hatRun : DijkstraState X
  uHat : X → ℝ
  t : ℝ
  Δ : ℝ
  band : Set X
  η : ℝ
  vSub : X → ℝ
  vSup : X → ℝ
  ΦSub : (band → ℝ) → band → ℝ
  ΦSup : (band → ℝ) → band → ℝ

/-- `t⁻_n := t_n - Δ_n` (Prop. prop:Dijkstra_band); for the data computed by `anbStepData`, this is
`nτ - 2Δ_n`, the lower end of the band `B_n`. -/
def AnbStepData.tMinus (d : AnbStepData X) : ℝ := d.t - d.Δ

/-- `t⁺_n := (1 + ε) t_n + C_past + C'_Γ + C_Γ Δ_n` (Corollary corol:Bn_comp), the upper bound of
the exact solution `u_*` on the bands `B_n` and `B'_n`. -/
def AnbStepData.tPlus (d : AnbStepData X) (ε Cpast CΓ CΓ' : ℝ) : ℝ :=
  (1 + ε) * d.t + Cpast + CΓ' + CΓ * d.Δ

/-- The number of passes of the inner loop of line anb:while_sub (the global iteration on the band
`B_n`, sub-solution variant, started from `E_α û_n`), in `ℕ∞` (`⊤` if it never stops). -/
noncomputable def AnbStepData.passesSub (d : AnbStepData X) : ℕ∞ :=
  globalIterSubPasses d.ΦSub d.η fun x => d.vSub x

/-- The number of passes of the inner loop of line anb:while_sup (the global iteration on the band
`B_n`, super-solution version, started from `E_α u̲`), in `ℕ∞` (`⊤` if it never stops). -/
noncomputable def AnbStepData.passesSup (d : AnbStepData X) : ℕ∞ :=
  globalIterPasses d.ΦSup d.η fun x => d.vSup x

/-- The quantities of the iteration of algo:anb started from the state `s` (lines anb:hatu to
algoline:etan, with line anb:hatu2 skipped). `û_n` is finite in the analysis; the conversion from
`ℝ_∞` uses the junk value `0` otherwise. -/
noncomputable def anbStepData [Fintype X] [LinearOrder X] (p : AnbParams X) (s : AnbState X) :
    AnbStepData X :=
  let T : ℝ := s.n * p.τ
  let D := dijkstraRun (anbHatOp p.Γ s.uSub T) s.uHatInit (Nat.card X)
  let uHat : X → ℝ := fun x => (D.u x).untopD 0
  let t := anbLevel p.ε T uHat s.uSup
  let B := anbBand T (T - t) uHat
  { hatRun := D, uHat := uHat, t := t, Δ := T - t, band := B
    η := (1 - p.ρ) * Real.exp (-T / p.α)
    vSub := fun x => kruzkov (1 / p.α) (uHat x)
    vSup := fun x => kruzkov (1 / p.α) (s.uSup x)
    ΦSub := bandOp (Global.kruzkovOp p.α p.Λ) B fun x => kruzkov (1 / p.α) (uHat x)
    ΦSup := bandOp (Global.kruzkovOp p.α p.Λ) B fun x => kruzkov (1 / p.α) (s.uSup x) }

open Classical in
/-- Eq. eqdef:Dijkstra_supsol (Prop. prop:Dijkstra_band): the initial guess `uHatInit` for
Dijkstra's method at line anb:hatu of iteration `n + 1`, built at the end of iteration `n`:
`u(x) := û_n(x)` if `û_n(x) < t⁻_n`, and `u(x) := max (ū_{n+1}(x), T)` otherwise, with
`T = (n + 1)τ` and `t⁻_n := t_n - Δ_n`. -/
noncomputable def anbDijkstraGuess (T tMinus : ℝ) (uHat uSub : X → ℝ) : X → WithTop ℝ :=
  fun x => if uHat x < tMinus then (uHat x : WithTop ℝ) else ((max (uSub x) T : ℝ) : WithTop ℝ)

/-- Eq. eqdef:Bpn: `B'_n := {x | t⁻_{n-1} ≤ û_{n-1}(x) ∧ û_n(x) < T}`, with `T = nτ`, the band
containing the points updated by Dijkstra's method in iteration `n` (Prop. prop:Dijkstra_band). -/
def anbDijkstraBand (tMinus T : ℝ) (uHatPrev uHat : X → ℝ) : Set X :=
  {x | tMinus ≤ uHatPrev x ∧ uHat x < T}

/-- The inner solver of lines anb:while_sub and anb:while_sup, acting on the maps on a band `B`
with operator `Φ`, tolerance `η` and initial map `v`: the result, and the number of updates at each
point of `B` (`⊤` if the loop never stops; the values at the points outside `B` are not used), for
the sub-solution variant and the super-solution version. -/
structure AnbInnerSolver (X : Type*) where
  subResult : (B : Set X) → ((B → ℝ) → B → ℝ) → ℝ → (B → ℝ) → B → ℝ
  subCount : (B : Set X) → ((B → ℝ) → B → ℝ) → ℝ → (B → ℝ) → X → ℕ∞
  supResult : (B : Set X) → ((B → ℝ) → B → ℝ) → ℝ → (B → ℝ) → B → ℝ
  supCount : (B : Set X) → ((B → ℝ) → B → ℝ) → ℝ → (B → ℝ) → X → ℕ∞

/-- The inner solver of algo:anb: the global iteration (algo:global_iteration), which updates each
point of the band once per pass. -/
noncomputable def anbGlobalIter : AnbInnerSolver X :=
  ⟨fun _ Φ η v => globalIterSubResult Φ η v, fun _ Φ η v _ => globalIterSubPasses Φ η v,
    fun _ Φ η v => globalIterResult Φ η v, fun _ Φ η v _ => globalIterPasses Φ η v⟩

open Classical in
/-- The inner solver of the variant of Theorem th:complexity_with_agsi: the parallel AGSI
(algo:agsi_parallel). -/
noncomputable def anbAgsi : AnbInnerSolver X :=
  ⟨fun _ => parallelAgsiSubResult,
    fun B Φ η v x => if h : x ∈ B then parallelAgsiSubCount Φ η v ⟨x, h⟩ else 0,
    fun _ => parallelAgsiResult,
    fun B Φ η v x => if h : x ∈ B then parallelAgsiCount Φ η v ⟨x, h⟩ else 0⟩

/-- The properties of an inner solver used in the analysis of algo:anb: its outputs lie in any set
of maps which contains the input and is closed under partial updates `w(y) ← Φ w(y)`, and when the
numbers of updates are finite at all the points of the band, the outputs satisfy the stopping
criteria. -/
class AnbInnerSolver.Valid (S : AnbInnerSolver X) : Prop where
  subResult_mem : ∀ (B : Set X) (Φ : (B → ℝ) → B → ℝ) (η : ℝ) (v : B → ℝ) (N : Set (B → ℝ)),
    v ∈ N → (∀ w ∈ N, ∀ w' : B → ℝ, (∀ y, w' y = w y ∨ w' y = Φ w y) → w' ∈ N) →
      S.subResult B Φ η v ∈ N
  supResult_mem : ∀ (B : Set X) (Φ : (B → ℝ) → B → ℝ) (η : ℝ) (v : B → ℝ) (N : Set (B → ℝ)),
    v ∈ N → (∀ w ∈ N, ∀ w' : B → ℝ, (∀ y, w' y = w y ∨ w' y = Φ w y) → w' ∈ N) →
      S.supResult B Φ η v ∈ N
  subResult_crit : ∀ (B : Set X) (Φ : (B → ℝ) → B → ℝ) (η : ℝ) (v : B → ℝ),
    (∀ x ∈ B, S.subCount B Φ η v x < ⊤) →
      ∀ y, Φ (S.subResult B Φ η v) y - S.subResult B Φ η v y ≤ η
  supResult_crit : ∀ (B : Set X) (Φ : (B → ℝ) → B → ℝ) (η : ℝ) (v : B → ℝ),
    (∀ x ∈ B, S.supCount B Φ η v x < ⊤) →
      ∀ y, S.supResult B Φ η v y - Φ (S.supResult B Φ η v) y ≤ η

open Classical in
/-- One iteration of the main loop of algo:anb (its body, lines anb:hatu to anb:while_sup; the
stopping test of line anb:for is not applied here, see `anbDone`), with the inner solver `S`:
compute the quantities of the iteration (`anbStepData`), run the two inner loops on the band `B_n`
(on the subtype), extend their results by the frozen values outside `B_n`, convert back from
Kruzkov coordinates, update the counters, set the initial guess for `û` of the next iteration
(`anbDijkstraGuess`, eq. eqdef:Dijkstra_supsol), and increment `n`. -/
noncomputable def anbStepWith [Fintype X] [LinearOrder X] (S : AnbInnerSolver X) (p : AnbParams X)
    (s : AnbState X) : AnbState X :=
  let d := anbStepData p s
  let wSub : X → ℝ :=
    bandExtend d.band d.vSub (S.subResult d.band d.ΦSub d.η fun x => d.vSub x)
  let wSup : X → ℝ := bandExtend d.band d.vSup (S.supResult d.band d.ΦSup d.η fun x => d.vSup x)
  let uSub : X → ℝ := fun x => -p.α * Real.log (-wSub x)
  { n := s.n + 1
    uSub := uSub
    uSup := fun x => kruzkovInv p.α (wSup x)
    uHatInit := anbDijkstraGuess (((s.n + 1 : ℕ) : ℝ) * p.τ) d.tMinus d.uHat uSub
    countSub := fun x =>
      s.countSub x + if x ∈ d.band then S.subCount d.band d.ΦSub d.η (fun y => d.vSub y) x else 0
    countSup := fun x =>
      s.countSup x + if x ∈ d.band then S.supCount d.band d.ΦSup d.η (fun y => d.vSup y) x else 0
    countHat := fun x => s.countHat x + d.hatRun.count x }

/-- The number of updates at each point of the band `B_n` of the inner loop of line anb:while_sub
(inner solver `S`) in the iteration started from `s` (`⊤` if the loop never stops). -/
noncomputable def anbSubCount [Fintype X] [LinearOrder X] (S : AnbInnerSolver X) (p : AnbParams X)
    (s : AnbState X) : X → ℕ∞ :=
  S.subCount (anbStepData p s).band (anbStepData p s).ΦSub (anbStepData p s).η
    fun y => (anbStepData p s).vSub y

/-- The number of updates at each point of the band `B_n` of the inner loop of line anb:while_sup
(inner solver `S`) in the iteration started from `s` (`⊤` if the loop never stops). -/
noncomputable def anbSupCount [Fintype X] [LinearOrder X] (S : AnbInnerSolver X) (p : AnbParams X)
    (s : AnbState X) : X → ℕ∞ :=
  S.supCount (anbStepData p s).band (anbStepData p s).ΦSup (anbStepData p s).η
    fun y => (anbStepData p s).vSup y

/-- One iteration of the main loop of algo:anb (its body, lines anb:hatu to anb:while_sup; the
stopping test of line anb:for is not applied here, see `anbDone`): the inner loops are global
iterations on the band `B_n` (`anbGlobalIter`). -/
noncomputable def anbStep [Fintype X] [LinearOrder X] (p : AnbParams X) (s : AnbState X) :
    AnbState X :=
  anbStepWith anbGlobalIter p s

/-- `Δ_max := 2α ln(2e/ε) + 2τ`, the bound on the half-width of the narrow band
(Corollary corol:max_width, as in V1; V0 had `2α ln(2e/ε) + τ`). -/
noncomputable def AnbParams.Δmax (p : AnbParams X) : ℝ :=
  2 * p.α * Real.log (2 * Real.exp 1 / p.ε) + 2 * p.τ

/-- `(‖u_*‖_∞ + Δ_max) / τ`, for the fixed point `u_*`: V1's `n_max` (Corollary corol:max_width)
is its ceiling `⌈nMax⌉₊`. -/
noncomputable def AnbParams.nMax [Fintype X] (p : AnbParams X) (uFix : X → ℝ) : ℝ :=
  (‖uFix‖ + p.Δmax) / p.τ

/-- `ε_max := min (α / (‖u_*‖_∞ + Δ_max), 2)` (Corollary corol:max_width), for the fixed point
`u_*`. Note that `Δ_max` depends on `ε`. -/
noncomputable def AnbParams.εmax [Fintype X] (p : AnbParams X) (uFix : X → ℝ) : ℝ :=
  min (p.α / (‖uFix‖ + p.Δmax)) 2

/-- `Δ⁺_max := (C_Γ - 1) Δ_max + ε ‖u_*‖_∞ + C_past + C'_Γ` (Corollary corol:NGamma). -/
noncomputable def AnbParams.ΔplusMax [Fintype X] (p : AnbParams X) (Cpast CΓ CΓ' : ℝ)
    (uFix : X → ℝ) : ℝ :=
  (CΓ - 1) * p.Δmax + p.ε * ‖uFix‖ + Cpast + CΓ'

/-- `N'_Λ := ⌈(2 Δ_max + Δ⁺_max) / τ⌉`, the bound on the number of iterations with `x ∈ B_n`
(Corollary corol:NGamma). -/
noncomputable def AnbParams.NΛ' [Fintype X] (p : AnbParams X) (Cpast CΓ CΓ' : ℝ)
    (uFix : X → ℝ) : ℕ :=
  ⌈(2 * p.Δmax + p.ΔplusMax Cpast CΓ CΓ' uFix) / p.τ⌉₊

/-- `N_Γ := N'_Λ + 1`, the bound on the number of iterations with `x ∈ B'_n` (Corollary
corol:NGamma). -/
noncomputable def AnbParams.NΓ [Fintype X] (p : AnbParams X) (Cpast CΓ CΓ' : ℝ)
    (uFix : X → ℝ) : ℕ :=
  p.NΛ' Cpast CΓ CΓ' uFix + 1

/-- `N''_Λ := ⌈(2 Δ_max / α - ln (1 - ρ)) / (-ln ρ)⌉`, the bound on the number of passes of the
inner loops (Prop. prop:niter_while). -/
noncomputable def AnbParams.NΛ'' (p : AnbParams X) : ℕ :=
  ⌈(2 * p.Δmax / p.α - Real.log (1 - p.ρ)) / (-Real.log p.ρ)⌉₊

/-- `N''_Λ := ⌈2 Δ_max / (-α ln ρ)⌉₊ + 2/(1-ρ)²` (Theorem th:complexity_with_agsi, V1), the
bound on the number of updates at each point of the band in each iteration of the variant with the
parallel AGSI; its second term is rounded down, since the update counts are integers. -/
noncomputable def AnbParams.NΛ''agsi (p : AnbParams X) : ℕ :=
  ⌈2 * p.Δmax / (-(p.α * Real.log p.ρ))⌉₊ + ⌊2 / (1 - p.ρ) ^ 2⌋₊

/-- The parameters `p` of algo:anb, together with constants `β`, `σ` such that `Φ_β` is
`σ`-sub-additive (Theorem th:complexity_withUnknown). These constants are *unknown*: they are not
parameters of the algorithm, which only uses `p`; they only enter the complexity analysis. -/
structure AnbParams.WithUnknown (X : Type*) where
  p : AnbParams X
  β : ℝ
  σ : ℝ

/-- The parameters `p` of algo:anb, together with unknown constants `β`, `σ`. -/
def AnbParams.withUnknown (p : AnbParams X) (β σ : ℝ) : AnbParams.WithUnknown X := ⟨p, β, σ⟩

namespace AnbParams.WithUnknown

/-- `C := (1 - ρ)^(α/β) / (1 - σ)` (Prop. prop:t_advances_withUnknown). -/
noncomputable def C (q : AnbParams.WithUnknown X) : ℝ :=
  (1 - q.p.ρ) ^ (q.p.α / q.β) / (1 - q.σ)

/-- `Δ_max := 2β ln(2eC/ε) + 2τ` (Corollary corol:max_width_withUnknown). -/
noncomputable def Δmax (q : AnbParams.WithUnknown X) : ℝ :=
  2 * q.β * Real.log (2 * Real.exp 1 * q.C / q.p.ε) + 2 * q.p.τ

/-- `(‖u_*‖_∞ + Δ_max) / τ`: V1's `n_max` (Corollary corol:max_width_withUnknown) is its ceiling
`⌈nMax⌉₊`. -/
noncomputable def nMax [Fintype X] (q : AnbParams.WithUnknown X) (uFix : X → ℝ) : ℝ :=
  (‖uFix‖ + q.Δmax) / q.p.τ

/-- `ε_max := min (α / (‖u_*‖_∞ + Δ_max), 2)` (Corollary corol:max_width_withUnknown). -/
noncomputable def εmax [Fintype X] (q : AnbParams.WithUnknown X) (uFix : X → ℝ) : ℝ :=
  min (q.p.α / (‖uFix‖ + q.Δmax)) 2

/-- `N''_Λ := ⌈(2 Δ_max / α + ln (β / α) - ln (1 - ρ)) / (-ln σ)⌉`, the bound on the number of
passes of the inner loops (Prop. prop:niter_while_withUnknown, V1; author's ruling 2026-10-16: the
V0 constant `⌈((2 Δ_max + β ln 2) / α - ln (1 - ρ)) / (-ln σ)⌉` is discarded). -/
noncomputable def NΛ'' (q : AnbParams.WithUnknown X) : ℕ :=
  ⌈(2 * q.Δmax / q.p.α + Real.log (q.β / q.p.α) - Real.log (1 - q.p.ρ)) / (-Real.log q.σ)⌉₊

/-- `Δ⁺_max := (C_Γ - 1) Δ_max + ε ‖u_*‖_∞ + C_past + C'_Γ`, with the modified `Δ_max`
(Corollary corol:max_width_withUnknown, last sentence; Theorem th:complexity_withUnknown). -/
noncomputable def ΔplusMax [Fintype X] (q : AnbParams.WithUnknown X) (Cpast CΓ CΓ' : ℝ)
    (uFix : X → ℝ) : ℝ :=
  (CΓ - 1) * q.Δmax + q.p.ε * ‖uFix‖ + Cpast + CΓ'

/-- `N'_Λ := ⌈(2 Δ_max + Δ⁺_max) / τ⌉`, with the modified `Δ_max`. -/
noncomputable def NΛ' [Fintype X] (q : AnbParams.WithUnknown X) (Cpast CΓ CΓ' : ℝ)
    (uFix : X → ℝ) : ℕ :=
  ⌈(2 * q.Δmax + q.ΔplusMax Cpast CΓ CΓ' uFix) / q.p.τ⌉₊

/-- `N_Γ := N'_Λ + 1`, with the modified `Δ_max`. -/
noncomputable def NΓ [Fintype X] (q : AnbParams.WithUnknown X) (Cpast CΓ CΓ' : ℝ)
    (uFix : X → ℝ) : ℕ :=
  q.NΛ' Cpast CΓ CΓ' uFix + 1

end AnbParams.WithUnknown

/-- The state of the ANB with the inner solver `S` after `k` iterations of its main loop (at the
start of iteration `n = k`). -/
noncomputable def anbRunWith [Fintype X] [LinearOrder X] (S : AnbInnerSolver X) (p : AnbParams X)
    (k : ℕ) : AnbState X :=
  (anbStepWith S p)^[k] anbInit

/-- The quantities of iteration `n = k` of the ANB with the inner solver `S`. -/
noncomputable def anbRunDataWith [Fintype X] [LinearOrder X] (S : AnbInnerSolver X)
    (p : AnbParams X) (k : ℕ) : AnbStepData X :=
  anbStepData p (anbRunWith S p k)

open Classical in
/-- The iteration at which the ANB with the inner solver `S` terminates: the first `k` such that
the stopping test `(1 + ε) ū ≥ u̲` holds at the start of iteration `k` (`⊤` if it never holds). -/
noncomputable def anbStopIndexWith [Fintype X] [LinearOrder X] (S : AnbInnerSolver X)
    (p : AnbParams X) : ℕ∞ :=
  if h : ∃ k, anbDone p (anbRunWith S p k) then (Nat.find h : ℕ∞) else ⊤

/-- The properties of Prop. prop:always_subsol for the iteration of the ANB with the inner solver
`S` started from the state `s`: with `û := (anbStepData p s).uHat` and the next state
`s' := anbStepWith S p s`, `ū ≤ Λ ū`, `Λ u̲ ≤ u̲`, `û ≤ Λ û`, `ū ≤ û ≤ ū'` and `u̲' ≤ u̲`
(eq. (always_subsol)). -/
structure AnbAlwaysSubsolWith [Fintype X] [LinearOrder X] (S : AnbInnerSolver X)
    (p : AnbParams X) (s : AnbState X) : Prop where
  uSub_le : s.uSub ≤ p.Λ s.uSub
  uSup_ge : Global.monotoneExtension p.Λ s.uSup ≤ s.uSup
  uHat_le : (anbStepData p s).uHat ≤ p.Λ (anbStepData p s).uHat
  uSub_le_uHat : s.uSub ≤ (anbStepData p s).uHat
  uHat_le_uSub_step : (anbStepData p s).uHat ≤ (anbStepWith S p s).uSub
  uSup_step_le : (anbStepWith S p s).uSup ≤ s.uSup

/-- The state of algo:anb after `k` iterations of its main loop (at the start of iteration
`n = k`). The iterations are not stopped by the test `anbDone`; the algorithm terminates at the
first `k` such that `anbDone p (anbRun p k)` (`anbStopIndex`). -/
noncomputable def anbRun [Fintype X] [LinearOrder X] (p : AnbParams X) (k : ℕ) : AnbState X :=
  anbRunWith anbGlobalIter p k

/-- The quantities of iteration `n = k` of algo:anb (`û_k`, `t_k`, `Δ_k`, `B_k`, ...), computed from
the state at its start. -/
noncomputable def anbRunData [Fintype X] [LinearOrder X] (p : AnbParams X) (k : ℕ) :
    AnbStepData X :=
  anbRunDataWith anbGlobalIter p k

/-- The iteration at which algo:anb terminates: the first `k` such that the stopping test
`(1 + ε) ū ≥ u̲` holds at the start of iteration `k` (`⊤` if it never holds). -/
noncomputable def anbStopIndex [Fintype X] [LinearOrder X] (p : AnbParams X) : ℕ∞ :=
  anbStopIndexWith anbGlobalIter p

/-- The properties of Prop. prop:always_subsol for the iteration of algo:anb started from the state
`s`: with `û := (anbStepData p s).uHat` and the next state `s' := anbStep p s`,
`ū ≤ Λ ū`, `Λ u̲ ≤ u̲`, `û ≤ Λ û`, `ū ≤ û ≤ ū'` and `u̲' ≤ u̲` (eq. (always_subsol)). -/
def AnbAlwaysSubsol [Fintype X] [LinearOrder X] (p : AnbParams X) (s : AnbState X) : Prop :=
  AnbAlwaysSubsolWith anbGlobalIter p s

/-- The state of the variant of algo:anb of Theorem th:complexity_with_agsi, whose inner loops are
parallel AGSI on the band `B_n` (`anbAgsi`), after `k` iterations of its main loop. -/
noncomputable def anbAgsiRun [Fintype X] [LinearOrder X] (p : AnbParams X) (k : ℕ) :
    AnbState X :=
  anbRunWith anbAgsi p k

/-- The quantities of iteration `n = k` of the variant of algo:anb with the parallel AGSI. -/
noncomputable def anbAgsiRunData [Fintype X] [LinearOrder X] (p : AnbParams X) (k : ℕ) :
    AnbStepData X :=
  anbRunDataWith anbAgsi p k

/-- The iteration at which the variant of algo:anb with the parallel AGSI terminates (`⊤` if the
stopping test never holds). -/
noncomputable def anbAgsiStopIndex [Fintype X] [LinearOrder X] (p : AnbParams X) : ℕ∞ :=
  anbStopIndexWith anbAgsi p

theorem AnbStepData.tMinus_def (d : AnbStepData X) : d.tMinus = d.t - d.Δ := rfl

theorem AnbStepData.tPlus_def (d : AnbStepData X) (ε Cpast CΓ CΓ' : ℝ) :
    d.tPlus ε Cpast CΓ CΓ' = (1 + ε) * d.t + Cpast + CΓ' + CΓ * d.Δ := rfl

theorem anbRunData_def [Fintype X] [LinearOrder X] (p : AnbParams X) (k : ℕ) :
    anbRunData p k = anbStepData p (anbRun p k) := rfl

theorem anbRun_eq_with [Fintype X] [LinearOrder X] (p : AnbParams X) (k : ℕ) :
    anbRun p k = anbRunWith anbGlobalIter p k := rfl

theorem anbRunDataWith_def [Fintype X] [LinearOrder X] (S : AnbInnerSolver X) (p : AnbParams X)
    (k : ℕ) : anbRunDataWith S p k = anbStepData p (anbRunWith S p k) := rfl

section StepData

variable [Fintype X] [LinearOrder X] (p : AnbParams X) (s : AnbState X)

@[simp] theorem anbStepData_hatRun : (anbStepData p s).hatRun =
    dijkstraRun (anbHatOp p.Γ s.uSub (s.n * p.τ)) s.uHatInit (Nat.card X) := rfl

@[simp] theorem anbStepData_uHat (x : X) : (anbStepData p s).uHat x =
    ((anbStepData p s).hatRun.u x).untopD 0 := rfl

@[simp] theorem anbStepData_t : (anbStepData p s).t =
    anbLevel p.ε (s.n * p.τ) (anbStepData p s).uHat s.uSup := rfl

@[simp] theorem anbStepData_Δ : (anbStepData p s).Δ = s.n * p.τ - (anbStepData p s).t := rfl

@[simp] theorem anbStepData_band : (anbStepData p s).band =
    anbBand (s.n * p.τ) (anbStepData p s).Δ (anbStepData p s).uHat := rfl

@[simp] theorem anbStepData_η : (anbStepData p s).η =
    (1 - p.ρ) * Real.exp (-(s.n * p.τ) / p.α) := rfl

@[simp] theorem anbStepData_vSub (x : X) : (anbStepData p s).vSub x =
    kruzkov (1 / p.α) ((anbStepData p s).uHat x) := rfl

@[simp] theorem anbStepData_vSup (x : X) : (anbStepData p s).vSup x =
    kruzkov (1 / p.α) (s.uSup x) := rfl

end StepData

end GuaranteedSubsol
