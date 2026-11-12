# Formalized definitions — GuaranteedSubsolutions, Introduction

Source: `Papers/Claude_GuaranteedSubsol/Include/Intro.tex`. Namespace `GuaranteedSubsol`.
Axioms are stated for a scalar operator `Λ : (X → ℝ) → ℝ` (the value at one interior point),
as requested by the `\formalizationInstruction` box of `Intro.tex`.

| Source | Lean | File |
|---|---|---|
| Monotonicity (l.126) | Mathlib `Monotone` | — |
| Additive invariance (l.127) | `AdditivelyInvariant` | `LeanHJBAutoformalisation/GuaranteedSubsol/Axioms.lean` |
| `C_past`-memory (eq. Cpast_memory) | `HasMemory C` | same |
| Causality (eq. causality) | `Causal` | same |
| `δ`-strict causality (rem:submult_strictcaus) | `StrictlyCausal δ` | same |
| `ν`-sub-multiplicativity (rem:submult_strictcaus) | `SubMultiplicative ν` | same |
| `ρ`-sub-additivity (l.179) | `SubAdditive ρ` (any operator `Φ`) | same |
| Stencil (eq. Cpast_dependency, left) | `HasStencil V` | same |
| `C_past`-dependency (eq. Cpast_dependency) | `HasDependency C V` | same |
| `C_Γ,C'_Γ`-comparison (l.200) | `Comparable C C'` | same |
| Comparison principle (Complexity.tex, eq. comparison_Lambda) | `HasComparisonPrinciple I Λ` (global operator, partition `I ⊔ Iᶜ`; `Ext.HasComparisonPrinciple` on `ℝ_∞`) | same; sufficient conditions in `GuaranteedSubsol/ComparisonPrinciple.lean` |
| `Γ` of Prop. prop:constr_Gamma (eq. constr_Gamma) | `constrGamma Λ V hV` | `LeanHJBAutoformalisation/GuaranteedSubsol/ConstrGamma.lean` |
| Kruzkov transform `E_α` (eq. Kruzkov) | `kruzkov αinv` (`αinv = 1/α`) | `LeanHJBAutoformalisation/GuaranteedSubsol/Kruzkov.lean` |
| Left inverse `E_α⁻¹` (eq. Kruzkov) | `kruzkovInv α` | same |
| Monotone extension `Λ_∞` (eq. monotonic_extension) | `monotoneExtension Λ` (generalized: sup over finite minorants, any `Λ`; agreement with the paper for monotone `Λ` proved, see `ANCHORS.md`) | same |
| `Φ_α = E_α Λ_∞ E_α⁻¹` (eq. Phi) | `kruzkovOp α Λ` | same |
| Restriction `Λ_B` (Complexity.tex, after prop:monotonic_Phi) | `restrictOp Λ B` (global operator `(X → ℝ) → X → ℝ`) | `LeanHJBAutoformalisation/GuaranteedSubsol/Restriction.lean` |

The paper's "`Φ_α` is `ρ`-sub-additive" reads `SubAdditive ρ (kruzkovOp α Λ)`.

Variants of the axioms for operators `(X → ℝ_∞) → ℝ_∞` (`ℝ_∞ = WithTop ℝ`, real constants and
real `t`) live in `LeanHJBAutoformalisation/GuaranteedSubsol/AxiomsExt.lean`, namespace
`GuaranteedSubsol.Ext`, with the same names: `AdditivelyInvariant`, `HasMemory`, `Causal`,
`StrictlyCausal`, `SubMultiplicative`, `SubAdditive`, `HasStencil`, `HasDependency`, `Comparable`.
For each of them, `<Axiom>.ext` (in `LeanHJBAutoformalisation/GuaranteedSubsol/AxiomsExtTransfer.lean`,
proved) transfers the real axiom of `Λ : (X → ℝ) → ℝ` to `monotoneExtension Λ`; monotonicity of
`Λ` and finiteness of `X` are assumed for `HasMemory`, `Causal`, `StrictlyCausal`, and `0 < C` for
`Comparable`.

| Source | Lean | File |
|---|---|---|
| `u^{<t}` (Complexity.tex, eq. u_less_t) | `cutoffLt t` (scalar, on `WithTop ℝ`) | `LeanHJBAutoformalisation/GuaranteedSubsol/Cutoff.lean` |
| `u^{≤t}` (prop:causal_formulation) | `cutoffLe t` | same |

Global forms (literal transcriptions of the paper's axioms for `Λ : ℝ^X → ℝ^X`) of `HasMemory`,
`Causal`, `StrictlyCausal`, `SubAdditive` are in `LeanHJBAutoformalisation/GuaranteedSubsol/Global.lean`
(namespace `GuaranteedSubsol.Global`), with proved equivalences to "for all `x ∈ Int X`, local"
under Dirichlet data (`monotone_iff`, `hasMemory_iff`, `causal_iff` with `X` finite,
`strictlyCausal_iff`, `subAdditive_iff` with `ρ ≥ 0` and `Φ` constant off `Int X`).
The same for the `Ext` axioms on `ℝ_∞ = WithTop ℝ`: `LeanHJBAutoformalisation/GuaranteedSubsol/GlobalExt.lean`
(namespace `GuaranteedSubsol.Global.Ext`, Dirichlet data `ubd : X → WithTop ℝ`).

Rescaling (not from the paper, introduced at the author's request): `rescaleOp α Λ u := Λ[α u] / α`
in `LeanHJBAutoformalisation/GuaranteedSubsol/Rescale.lean` (proved), with transfer lemmas
`<Axiom>.rescaleOp` (for `0 < α`): `Monotone`, `AdditivelyInvariant`, `Causal`, `HasStencil`,
`SubAdditive ρ` keep their constants; `HasMemory`, `StrictlyCausal`, `SubMultiplicative`,
`HasDependency` constants and `C'` in `Comparable` are divided by `α`; and
`kruzkovOp β (rescaleOp α Λ) = kruzkovOp (α * β) Λ` (`kruzkovOp_rescaleOp`).

Parallel AGSI (AGSI2.tex, Algorithm algo:agsi_parallel, super-solution version), in
`LeanHJBAutoformalisation/GuaranteedSubsol/ParallelAGSI.lean`: the state `ParallelAgsiState X` (map `v` and update
counter `count : X → ℕ`) and one pass `parallelAgsiStep Φ η` of the while loop (`v ← Φ_B v` and
`count ← count + 1` on `B = {v - Φ v > η}`). The algorithm from `v` is the sequence
`(parallelAgsiStep Φ η)^[n] ⟨v, 0⟩`; termination is the existence of `n` at which `v - Φ v ≤ η`.
The sub-solution variant `parallelAgsiSubStep` (same file) replaces `v - Φ v` with `Φ v - v`; it is
the super-solution version for `reflectOp Φ` run on `-v` (`parallelAgsiSubStep_iterate`).

Reflection (not from the paper, introduced at the author's request): `reflectOp Λ u := -Λ[-u]`, for
scalar operators and (pointwise) for global ones, in
`LeanHJBAutoformalisation/GuaranteedSubsol/Reflect.lean` (proved). For scalar operators it is
`rescaleOp (-1) Λ`; it is an involution and exchanges sub- and super-solutions. Monotonicity,
additive invariance, `SubAdditive ρ` (same `ρ`), stencil and the comparison principle are preserved
(`_iff` lemmas).

AGSIK (AGSI2.tex, Algorithm algo:agsik), in `LeanHJBAutoformalisation/GuaranteedSubsol/AGSIK.lean`:
the state `AgsikState X` (level `n`, map `u : X → WithTop ℝ`, update counter), the selection
criterion `agsikSelect`, the stopping criterion `agsikDone`, the initialization `agsikInit`
(`u = +∞`) and one step `agsikStep Λ αinv ε` (parallel pass if some point is selected, otherwise
stop if done, otherwise `n ← n + 1`), for an operator `Λ` on `ℝ_∞`.

Supporting results: `Ext.hasComparisonPrinciple_of_kruzkov` in
`ComparisonPrinciple.lean` (comparison principle for the extension `Λ_∞` on `ℝ_∞`, from the
`ρ`-sub-additivity of `Φ_α`, `ρ < 1`); `agsikRun_terminates_of_kruzkov` (frozen anchor, proof in `AgsikKruzkov.lean`)
(AGSIK termination for `Λ_∞` with `Φ_β` `ρ`-sub-additive); `agsik_until_iff` (frozen
anchor, proof in `AgsikCriterion.lean`) (the criterion of line agsik:until and its reformulation in the paper, with
a strict inequality).

Distance to the boundary along the stencils (proof of Prop. prop:constr_Gamma, Effective.tex), in
`LeanHJBAutoformalisation/GuaranteedSubsol/StencilDist.lean`: `stencilReach I V n x` (a path of
`n` stencil edges from `x` to the boundary `Iᶜ`) and `stencilDist I V x` (the paper's
`d_V(x, ∂X)`, with junk value `0` when the boundary is unreachable).

Generalized Dijkstra (Complexity.tex, Algorithm algo:Dijkstra), in
`LeanHJBAutoformalisation/GuaranteedSubsol/Dijkstra.lean`: the state `DijkstraState X` (map
`u : X → WithTop ℝ` and update counter), the selection `dijkstraSelect` (active point with minimal
`(Γ u x, x)` for the lexicographic order, given a linear order on `X`), the initialization
`dijkstraInit u₀` and one iteration `dijkstraStep Γ`. The list `L` is not stored.

`Global.monotoneExtension Λ` and `Global.kruzkovOp α Λ` (in `Kruzkov.lean`): the global forms
`Λ_∞ u (x) := (Λ · x)_∞ u` and `Φ_α v (x) := (Φ_α)(Λ · x) v` of `monotoneExtension` and
`kruzkovOp` for a global operator `Λ : (X → ℝ) → X → ℝ`. `dijkstraRun Γ u₀ n` (in `Dijkstra.lean`):
the state of algo:Dijkstra after `n` iterations from `u₀`. `parallelAgsiRun Φ η v n` and
`parallelAgsiSubRun Φ η v n` (in `ParallelAGSI.lean`): the state of algo:agsi_parallel (super- and
sub-solution versions) after `n` passes from `⟨v, 0⟩`.
`agsikRun Λ αinv ε k` (in `AGSIK.lean`): the state of algo:agsik after `k` steps from `u = +∞`.

Global iteration (Complexity.tex, Algorithm algo:global_iteration), in
`LeanHJBAutoformalisation/GuaranteedSubsol/GlobalIteration.lean`: one iteration `globalIterStep Φ η`
(`v ← Φ v` unless `v - Φ v ≤ η`) and its sub-solution variant `globalIterSubStep Φ η` (criterion
`Φ v - v ≤ η`), and the maps `globalIterRun Φ η v n`, `globalIterSubRun Φ η v n` after `n`
iterations from `v`.
`globalIterPasses`, `globalIterResult` (and `globalIterSubPasses`, `globalIterSubResult`), in
`GlobalIteration.lean`: number of iterations until the stopping criterion holds, in `ℕ∞` (via
`Nat.find`, `⊤` if it never holds), and the output of the global iteration (after `passes.toNat`
iterations, i.e. the junk value after `0` iterations if the loop never stops).

ANB (Intro.tex, Algorithm algo:anb), in `LeanHJBAutoformalisation/GuaranteedSubsol/Anb.lean`: the
parameters `AnbParams X` (`Λ`, `Γ`, `ε`, `τ`, `α`, `ρ`), the
state `AnbState X` (`n`, `uSub` = ū, `uSup` = u̲, `uHatInit` = initial guess for Dijkstra at
line anb:hatu, update counters `countSub`, `countSup`,
`countHat`), `anbInit`, the stopping test `anbDone`, the operator `anbHatOp` of line anb:hatu,
`anbLevel` (`t_n`), `anbBand` (`B_n`), the record `AnbStepData` of the quantities of one iteration
(`û_n`, `t_n`, `Δ_n`, `B_n`, `η_n`, Kruzkov inputs, band operators `ΦSub`, `ΦSup`) computed by `anbStepData`, one
iteration `anbStep` (the loop body), the run `anbRun`, the stopping index `anbStopIndex`, and the
properties `AnbAlwaysSubsol p s` of Prop. prop:always_subsol for one iteration; the initial guess
`anbDijkstraGuess` of Dijkstra's method (eq. eqdef:Dijkstra_supsol, stored in `uHatInit`) and the
band `anbDijkstraBand` (`B'_n`, eq. eqdef:Bpn) of Prop. prop:Dijkstra_band; the abbreviations `anbRunData p k`
(the quantities of iteration `k`) and `AnbStepData.tMinus` (`t⁻_n = t_n - Δ_n`), `AnbStepData.passesSub`, `AnbStepData.passesSup` (the
numbers of passes of the inner loops, in `ℕ∞`), and
`AnbStepData.tPlus` (`t⁺_n = (1 + ε) t_n + C_past + C'_Γ + C_Γ Δ_n`, Corollary corol:Bn_comp); and
the constants of Corollary corol:max_width: `AnbParams.Δmax` (`Δ_max = 2α ln(2e/ε) + 2τ`),
`AnbParams.nMax` (`n_max`) and `AnbParams.εmax` (`ε_max`), the last two
as functions of the fixed point `u_*`; the constants of Corollary corol:NGamma:
`AnbParams.ΔplusMax` (`Δ⁺_max`), `AnbParams.NΛ'` (`N'_Λ`), `AnbParams.NΓ` (`N_Γ`); and
`AnbParams.NΛ''` (`N''_Λ`, Prop. prop:niter_while). For Theorem th:complexity_withUnknown,
`AnbParams.WithUnknown` bundles the parameters `p` of the algorithm with the unknown analysis
constants `β`, `σ` (`Φ_β` is `σ`-sub-additive), with the constants `WithUnknown.C`
(`(1 - ρ)^(α/β)/(1 - σ)`), `WithUnknown.Δmax` (`2β ln(2eC/ε) + 2τ`),
`WithUnknown.nMax`, `WithUnknown.εmax`, `WithUnknown.NΛ''` (the constant of the paper
`⌈(2Δ_max/α + ln(β/α) - ln(1 - ρ))/(-ln σ)⌉`), and `WithUnknown.ΔplusMax`,
`WithUnknown.NΛ'`, `WithUnknown.NΓ` (built from the modified `Δ_max`)
(Corollary corol:max_width_withUnknown, Prop. prop:niter_while_withUnknown). The inner loops act on the band
as a subtype, with frozen values outside: `bandExtend`, `bandOp` (`Band.lean`). The numbers of
passes of the global iteration, the counters `countSub`, `countSup` and `anbStopIndex` take values in
`ℕ∞` (`⊤` when a loop never stops). Line anb:hatu2 is
skipped; lines anb:while_sub and
anb:while_sup are global iterations in Kruzkov coordinates, on the band. The inner solver of these lines is a
parameter, `AnbInnerSolver` (result and number of updates at each point of the band, for the
sub-solution variant and the super-solution version), of `anbStepWith`, `anbRunWith`,
`anbRunDataWith`, `anbStopIndexWith`, `AnbAlwaysSubsolWith`, with the per-point counts
`anbSubCount`, `anbSupCount` and the properties `AnbInnerSolver.Valid` used in the analysis:
`anbStep`, `anbRun`, `anbRunData`, `anbStopIndex`, `AnbAlwaysSubsol` are the instances for the
global iteration `anbGlobalIter`, and `anbAgsiRun`, `anbAgsiRunData`, `anbAgsiStopIndex` those for
the parallel AGSI `anbAgsi` (Theorem th:complexity_with_agsi), with the constant
`AnbParams.NΛ''agsi` (`N''_Λ := ⌈2Δ_max/(-α ln ρ)⌉ + ⌊2/(1 - ρ)²⌋`). The output of the parallel
AGSI: `parallelAgsiPasses`, `parallelAgsiResult`, `parallelAgsiCount` and their sub-solution
variants (`ParallelAGSI.lean`). The ANB with a placeholder (Papers/AnbEquivalence; `AnbLazy.lean`):
state `AnbLazyState` (`n`, `ũ : X → Option ℝ` with `none` a placeholder for `(n-1)τ`, `u̲~`, `ǔ^init`, counters), with
the derived maps `AnbLazyState.uSub` (`ū = ũ^{⋄→(n-1)τ}`) and `AnbLazyState.uHatInit`
(`û^init = min {ǔ^init, max {ū, nτ}}`); the Dijkstra operator `anbCheckOp` (`max {ū, Γ}^{<nτ}`), the
level `anbLazyLevel`, the per-iteration data `AnbLazyStepData`/`anbLazyStepData`, and
`anbLazyStepWith`, `anbLazyRunWith`, `anbLazyRunDataWith`, `anbLazyDone`, `anbLazyStopIndexWith`
(inner solver as a parameter). Ordered partial maps (Papers/OrderedPartialMap; `OrderedPartialMap.lean`): a model of
`std::set<std::pair<V, X>>`, with a partial map `v : X → Option V` and an operation counter, and the
operations `empty`, `bot` (via `botVal`, the lexicographic minimum of `entries`), `set1`, `set`,
`erase1`, `erase`, `pop`, `entriesIco`. The global stencil property `Global.Ext.HasStencil` and the
reversed stencil `Global.Ext.revStencil` (`GlobalExt.lean`, eq. eqdef:stencil). Dijkstra's method with
a sorted list (`DijkstraHeap.lean`): `dijkstraKey`, `dijkstraCutOp` (`Γ^{<T}`), `DijkstraHeapState`
(with the counters `L.count` and `evalCount`), `dijkstraHeapStep` (with a threshold `T`),
`dijkstraHeapRun`, `dijkstraHeapInit`, and the while loop `dijkstraHeapLoop` (with
`DijkstraHeapState.Stopped`, `dijkstraHeapStopIndex`, in `ℕ∞`, `⊤` if the loop never stops). The ANB with sorted lists (algo:anb_lazy;
`AnbHeap.lean`): the keys `anbKeyS`, `anbKeyM` (eqs. eqdef:S_heap, eqdef:M_heap) and `anbKeySc` (the
fourth list `Sc`, author's addition), the operator `anbHeapOp` (`max {ū, Γ}`), the state
`AnbHeapState` (with `ǔ` and `L` in a `DijkstraHeapState`, the lists `M`, `S`, `Sc`, the previous
band), `AnbHeapState.uSub`, `anbHeapInit`, `anbHeapDone`, the per-iteration data
`AnbHeapStepData`/`anbHeapStepData`, and `anbHeapStepWith`, `anbHeapRunWith`, `anbHeapRunDataWith`,
`anbHeapStopIndexWith` (inner solver and stencils as parameters), and the counts
`anbHeapCountB'` (`countB'`, selections by Dijkstra's method) and `anbHeapCountB` (`countB`,
iterations in the band). The bounds of Prop. prop:complexity_lazy at termination,
`AnbHeapCostBound` (`AnbHeapComplexity.lean`), with its instances `anbHeapRun_complexity`,
`anbHeapRun_complexity_withUnknown`, `anbHeapAgsiRun_complexity` (ordinary theorems, author's
decision). The frozen anchors `anbHeapRun_correct_complexity` and
`anbHeapRun_correct_complexity_withUnknown` (`AnbHeapCorrectComplexityProof.lean`) add the
correctness at termination, the band half-width and the bounds per point (eq. eq:ln_N_eps).
