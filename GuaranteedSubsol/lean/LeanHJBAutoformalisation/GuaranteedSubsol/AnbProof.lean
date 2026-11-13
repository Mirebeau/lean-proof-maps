/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.Anb
public import LeanHJBAutoformalisation.GuaranteedSubsol.DijkstraProof
public import LeanHJBAutoformalisation.GuaranteedSubsol.GlobalIterationProof
public import LeanHJBAutoformalisation.GuaranteedSubsol.ParallelAgsiKruzkovProof
public import LeanHJBAutoformalisation.GuaranteedSubsol.ComparisonPrinciple
public import LeanHJBAutoformalisation.GuaranteedSubsol.AxiomsExtTransfer
public import LeanHJBAutoformalisation.GuaranteedSubsol.ExtCausalMixProof
public import LeanHJBAutoformalisation.GuaranteedSubsol.ULessTProof
public import LeanHJBAutoformalisation.GuaranteedSubsol.BandProof
public import LeanHJBAutoformalisation.GuaranteedSubsol.ParallelAgsiResultProof

/-!
# ANB: proofs

Provider proofs for the frozen anchors on Algorithm algo:anb, see `ANCHORS.md`.

* `zero_vacuous` (Remark rem:anb_npos): at `n = 0`, the operator `Γ' = max (0, min (0, Γ_∞))` of
  line anb:hatu is identically `0`, so Dijkstra's method started from the guess `0` makes no
  update and `û_0 = 0`; then `t_0 = Δ_0 = 0` and `B_0 = ∅`, on which the global iterations change
  nothing.
* `uHat_eq` (line anb:hatu): from a super-solution guess, Dijkstra's method reaches the fixed
  point of `Γ'` within `card X` iterations (Prop. prop:Dijkstra_correct); it is finite, below
  `max (ū, nτ)`.
* `eq_of_notMem_band` (lines anb:while_sub, anb:while_sup): the global iterations act on the band
  (on the subtype), and their results are extended by the frozen values outside the band, so
  `ū' = û_n` and `u̲' = u̲` there (`wSub_of_notMem`, `wSup_of_notMem`).
* `subRun_props`, `supRun_props`: along the global iterations on the band, the extended maps are
  sub- (resp. super-) solutions of the restriction `(Φ_α)_B` (`BandProof.restrictOp_bandExtend`).
* `guess_run`, `hatRun_count_mem` (Prop. prop:Dijkstra_band): the guess `anbDijkstraGuess` is a
  super-solution of the next `Γ'` (`guess_step`), and a point updated by Dijkstra's method has
  decreased from the guess, which forces it into `B'_n`.
* `always_subsol` (Prop. prop:always_subsol): induction over the run (`step_always_subsol`), with
  the global iterations in Kruzkov coordinates (`subRun_props`, `supRun_props`) converted back
  (`sub_convert`, `sup_convert`).
* `succ_of_done`: once `(1 + ε) ū ≥ u̲`, the set defining `t_n` is empty, so `t_n = nτ`,
  `Δ_n = 0` and the band is empty.

The results are stated for the ANB with any inner solver `S` satisfying `AnbInnerSolver.Valid`
(instances: the global iteration `anbGlobalIter` of algo:anb, and the parallel AGSI `anbAgsi` of
Theorem th:complexity_with_agsi); `anbRunWith S p` is `anbRunWith anbGlobalIter p` by definition.
-/

@[expose] public section

namespace GuaranteedSubsol.AnbProof

variable {X : Type*}

/-- At `n = 0` with `ū = 0` and the guess `0`, Dijkstra's method makes no update. -/
theorem hatRun_zero [LinearOrder X] (Γ : (X → ℝ) → X → ℝ) (k : ℕ) :
    dijkstraRun (anbHatOp Γ 0 0) 0 k = dijkstraInit 0 := by
  have hop : ∀ u x, anbHatOp Γ 0 0 u x = 0 := fun u x => by
    simp only [anbHatOp, Pi.zero_apply, WithTop.coe_zero]
    exact max_eq_left (min_le_left _ _)
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [dijkstraRun, Function.iterate_succ_apply', ← dijkstraRun, ih]
    refine DijkstraProof.step_of_not_select _ fun ⟨x, hx⟩ => ?_
    have := hx.1
    simp only [hop, dijkstraInit, Pi.zero_apply, lt_self_iff_false] at this

/-! ### The inner solvers -/

/-- The global iteration is a valid inner solver: each pass leaves the map unchanged or replaces it
with its image, and when the loop stops its output satisfies the stopping criterion. -/
instance anbGlobalIter_valid : (anbGlobalIter (X := X)).Valid where
  subResult_mem B Φ η v N hv hN := by
    change globalIterSubRun Φ η v _ ∈ N
    generalize (globalIterSubPasses Φ η v).toNat = n
    induction n with
    | zero => exact hv
    | succ n ih =>
      rw [GlobalIterationProof.subRun_succ]
      rcases GlobalIterationProof.subStep_eq (Φ := Φ) (η := η) (globalIterSubRun Φ η v n)
        with h | h <;> rw [h]
      · exact ih
      · exact hN _ ih _ fun y => Or.inr rfl
  supResult_mem B Φ η v N hv hN := by
    change globalIterRun Φ η v _ ∈ N
    generalize (globalIterPasses Φ η v).toNat = n
    induction n with
    | zero => exact hv
    | succ n ih =>
      rw [GlobalIterationProof.run_succ]
      rcases GlobalIterationProof.step_eq (Φ := Φ) (η := η) (globalIterRun Φ η v n)
        with h | h <;> rw [h]
      · exact ih
      · exact hN _ ih _ fun y => Or.inr rfl
  subResult_crit B Φ η v hc y := by
    classical
    have h : globalIterSubPasses Φ η v < ⊤ := hc y.1 y.2
    change Φ (globalIterSubResult Φ η v) y - globalIterSubResult Φ η v y ≤ η
    by_cases hex : ∃ n, ∀ y, Φ (globalIterSubRun Φ η v n) y - globalIterSubRun Φ η v n y ≤ η
    · unfold globalIterSubResult globalIterSubPasses
      simp only [hex, ↓reduceDIte, ENat.toNat_natCast]
      exact Nat.find_spec hex y
    · unfold globalIterSubPasses at h
      simp only [hex, ↓reduceDIte, lt_self_iff_false] at h
  supResult_crit B Φ η v hc y := by
    classical
    have h : globalIterPasses Φ η v < ⊤ := hc y.1 y.2
    change globalIterResult Φ η v y - Φ (globalIterResult Φ η v) y ≤ η
    by_cases hex : ∃ n, ∀ y, globalIterRun Φ η v n y - Φ (globalIterRun Φ η v n) y ≤ η
    · unfold globalIterResult globalIterPasses
      simp only [hex, ↓reduceDIte, ENat.toNat_natCast]
      exact Nat.find_spec hex y
    · unfold globalIterPasses at h
      simp only [hex, ↓reduceDIte, lt_self_iff_false] at h

/-- The parallel AGSI is a valid inner solver: each pass replaces some values `v(x)` with
`Φ v(x)`, and when the loop stops its output satisfies the stopping criterion. -/
instance anbAgsi_valid : (anbAgsi (X := X)).Valid where
  subResult_mem B Φ η v N hv hN := ParallelAgsiResultProof.subResult_mem hv hN
  supResult_mem B Φ η v N hv hN := ParallelAgsiResultProof.result_mem hv hN
  subResult_crit B Φ η v hc y := by
    classical
    have h := hc y.1 y.2
    change (if h : (y : X) ∈ B then parallelAgsiSubCount Φ η v ⟨y, h⟩ else 0) < ⊤ at h
    simp only [y.2, ↓reduceDIte] at h
    exact ParallelAgsiResultProof.subResult_crit
      ((ParallelAgsiResultProof.subCount_lt_top_iff _).1 h) y
  supResult_crit B Φ η v hc y := by
    classical
    have h := hc y.1 y.2
    change (if h : (y : X) ∈ B then parallelAgsiCount Φ η v ⟨y, h⟩ else 0) < ⊤ at h
    simp only [y.2, ↓reduceDIte] at h
    exact ParallelAgsiResultProof.result_crit
      ((ParallelAgsiResultProof.count_lt_top_iff _).1 h) y

variable [Fintype X] [LinearOrder X] {S : AnbInnerSolver X}

/-- The result of line anb:while_sub: the inner solver on the band `B_n`, extended by the frozen
values `E_α û_n` outside `B_n`. -/
noncomputable def wSub (S : AnbInnerSolver X) (p : AnbParams X) (s : AnbState X) : X → ℝ :=
  bandExtend (anbStepData p s).band (anbStepData p s).vSub
    (S.subResult (anbStepData p s).band (anbStepData p s).ΦSub (anbStepData p s).η
      fun x => (anbStepData p s).vSub x)

/-- The result of line anb:while_sup: the inner solver on the band `B_n`, extended by the frozen
values `E_α u̲_n` outside `B_n`. -/
noncomputable def wSup (S : AnbInnerSolver X) (p : AnbParams X) (s : AnbState X) : X → ℝ :=
  bandExtend (anbStepData p s).band (anbStepData p s).vSup
    (S.supResult (anbStepData p s).band (anbStepData p s).ΦSup (anbStepData p s).η
      fun x => (anbStepData p s).vSup x)

open Classical in
/-- One iteration of the ANB, in terms of `anbStepData`. -/
theorem anbStep_eq (p : AnbParams X) (s : AnbState X) :
    anbStepWith S p s =
      { n := s.n + 1
        uSub := fun x => -p.α * Real.log (-wSub S p s x)
        uSup := fun x => kruzkovInv p.α (wSup S p s x)
        uHatInit := anbDijkstraGuess (((s.n + 1 : ℕ) : ℝ) * p.τ)
          (anbStepData p s).tMinus (anbStepData p s).uHat fun x =>
            -p.α * Real.log (-wSub S p s x)
        countSub := fun x => s.countSub x + if x ∈ (anbStepData p s).band then
          S.subCount (anbStepData p s).band (anbStepData p s).ΦSub (anbStepData p s).η
            (fun y => (anbStepData p s).vSub y) x else 0
        countSup := fun x => s.countSup x + if x ∈ (anbStepData p s).band then
          S.supCount (anbStepData p s).band (anbStepData p s).ΦSup (anbStepData p s).η
            (fun y => (anbStepData p s).vSup y) x else 0
        countHat := fun x => s.countHat x + (anbStepData p s).hatRun.count x } := rfl

/-- Outside the band, the results of the two global iterations are the frozen values. -/
theorem wSub_of_notMem (p : AnbParams X) (s : AnbState X) {x : X}
    (hx : x ∉ (anbStepData p s).band) : wSub S p s x = (anbStepData p s).vSub x :=
  bandExtend_of_notMem _ _ _ hx

theorem wSup_of_notMem (p : AnbParams X) (s : AnbState X) {x : X}
    (hx : x ∉ (anbStepData p s).band) : wSup S p s x = (anbStepData p s).vSup x :=
  bandExtend_of_notMem _ _ _ hx

theorem zero_vacuous (p : AnbParams X) :
    (anbRunDataWith S p 0).uHat = 0 ∧ (anbRunDataWith S p 0).t = 0 ∧
    (anbRunDataWith S p 0).Δ = 0 ∧ (anbRunDataWith S p 0).band = ∅ ∧
    (anbRunWith S p 1).n = 1 ∧ (anbRunWith S p 1).uSub = (anbRunWith S p 0).uSub ∧
    (anbRunWith S p 1).uSup = (anbRunWith S p 0).uSup ∧ (anbRunWith S p 1).countSub = 0 ∧
    (anbRunWith S p 1).countSup = 0 ∧ (anbRunWith S p 1).countHat = 0 := by
  classical
  simp only [anbRunDataWith_def]
  have h0 : anbRunWith S p 0 = anbInit := rfl
  have hT : ((anbInit : AnbState X).n : ℝ) * p.τ = 0 := by simp [anbInit]
  -- `û_0 = 0`
  have hD : (anbStepData p anbInit).hatRun = dijkstraInit 0 := by
    rw [anbStepData_hatRun, hT]; exact hatRun_zero p.Γ _
  have hHat : (anbStepData p anbInit).uHat = 0 := funext fun x => by
    rw [anbStepData_uHat, hD]; rfl
  -- `t_0 = 0`, `Δ_0 = 0`, `B_0 = ∅`
  have ht : (anbStepData p anbInit).t = 0 := by
    rw [anbStepData_t, hHat, hT]
    unfold anbLevel
    dsimp only
    split_ifs with h
    · simp [Finset.inf'_const]
    · rfl
  have hΔ : (anbStepData p anbInit).Δ = 0 := by rw [anbStepData_Δ, ht, hT]; ring
  have hB : (anbStepData p anbInit).band = ∅ := by
    rw [anbStepData_band, hΔ, hHat, hT]
    ext x; simp [anbBand]
  -- the iteration changes nothing on the empty band
  have hoff : ∀ x, x ∉ (anbStepData p anbInit).band := fun x => by
    rw [hB]; exact Set.notMem_empty x
  have h1 : anbRunWith S p 1 = anbStepWith S p anbInit := rfl
  rw [h0, h1, anbStep_eq p]
  refine ⟨hHat, ht, hΔ, hB, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · funext x
    simp only [wSub_of_notMem p anbInit (hoff x), anbStepData_vSub, hHat, Pi.zero_apply,
      WithTop.coe_zero]
    simp [anbInit, kruzkov]
  · funext x
    simp only [wSup_of_notMem p anbInit (hoff x), anbStepData_vSup]
    simp [anbInit, kruzkov, kruzkovInv]
  · funext x; simp only [hB, Set.mem_empty_iff_false, ↓reduceIte]; rfl
  · funext x; simp only [hB, Set.mem_empty_iff_false, ↓reduceIte]; rfl
  · funext x; simp only [hD]; rfl

/-! ### Line anb:hatu -/

omit [Fintype X] [LinearOrder X] in
theorem monotone_anbHatOp (Γ : (X → ℝ) → X → ℝ) (c : X → ℝ) (T : ℝ) :
    Monotone (anbHatOp Γ c T) := fun _ _ h x =>
  max_le_max le_rfl (min_le_min le_rfl (KruzkovProof.monotone_monotoneExtension (Γ · x) h))

omit [Fintype X] [LinearOrder X] in
theorem causal_anbHatOp [Finite X] {Γ : (X → ℝ) → X → ℝ} (hΓmono : ∀ x, Monotone (Γ · x))
    (hΓcaus : ∀ x, Causal (Γ · x)) (c : X → ℝ) (T : ℝ) (x : X) :
    Ext.Causal (anbHatOp Γ c T · x) :=
  ExtCausalMixProof.causal_max (ULessTProof.causal_const _)
    (ExtCausalMixProof.causal_min (ULessTProof.causal_const _) ((hΓcaus x).ext (hΓmono x)))

omit [Fintype X] in
/-- Dijkstra's method has reached a fixed point after `card X` iterations. -/
theorem dijkstraRun_card_fixed [Finite X] {Γ : (X → WithTop ℝ) → X → WithTop ℝ}
    (hmono : Monotone Γ) (hcaus : ∀ x, Ext.Causal (Γ · x)) {u₀ : X → WithTop ℝ}
    (hu₀ : Γ u₀ ≤ u₀) :
    Γ (dijkstraRun Γ u₀ (Nat.card X)).u = (dijkstraRun Γ u₀ (Nat.card X)).u := by
  obtain ⟨N, hN, hfix⟩ := DijkstraProof.fixedPoint hmono hcaus hu₀
  have hstay : ∀ m, (dijkstraStep Γ)^[N + m] (dijkstraInit u₀) =
      (dijkstraStep Γ)^[N] (dijkstraInit u₀) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [← add_assoc, Function.iterate_succ_apply', ih]
      refine DijkstraProof.step_of_not_select _ fun ⟨y, hy⟩ => ?_
      have := hy.1
      rw [hfix] at this
      exact lt_irrefl _ this
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hN
  simp only [dijkstraRun]
  rw [hm, hstay]
  exact hfix

theorem uHat_eq {p : AnbParams X} (hΓmono : ∀ x, Monotone (p.Γ · x))
    (hΓcaus : ∀ x, Causal (p.Γ · x)) {s : AnbState X}
    (hinit : anbHatOp p.Γ s.uSub (s.n * p.τ) s.uHatInit ≤ s.uHatInit) (x : X) :
    (anbStepData p s).hatRun.u x = ((anbStepData p s).uHat x : WithTop ℝ) ∧
      (anbStepData p s).uHat x =
        max (s.uSub x) (min (s.n * p.τ) (p.Γ (anbStepData p s).uHat x)) := by
  have hfix : anbHatOp p.Γ s.uSub (s.n * p.τ) (anbStepData p s).hatRun.u =
      (anbStepData p s).hatRun.u := by
    rw [anbStepData_hatRun]
    exact dijkstraRun_card_fixed (monotone_anbHatOp _ _ _) (causal_anbHatOp hΓmono hΓcaus _ _)
      hinit
  have hfin : ∀ y, (anbStepData p s).hatRun.u y = ((anbStepData p s).uHat y : WithTop ℝ) := by
    intro y
    have hy := congrFun hfix y
    have hle : (anbStepData p s).hatRun.u y ≤ ((max (s.uSub y) (s.n * p.τ) : ℝ) : WithTop ℝ) := by
      rw [← hy]
      exact max_le (WithTop.coe_le_coe.2 (le_max_left _ _))
        ((min_le_left _ _).trans (WithTop.coe_le_coe.2 (le_max_right _ _)))
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hle)
    rw [anbStepData_uHat, ← hr]
    rfl
  refine ⟨hfin x, ?_⟩
  have hy := congrFun hfix x
  have hcoe : (anbStepData p s).hatRun.u = fun y => ((anbStepData p s).uHat y : WithTop ℝ) :=
    funext hfin
  simp only [anbHatOp] at hy
  rw [hcoe] at hy
  change max _ (min _ (monotoneExtension (p.Γ · x) _)) = _ at hy
  rw [MonotoneExtension.coe_eq (hΓmono x), ← WithTop.coe_min, ← WithTop.coe_max,
    WithTop.coe_inj] at hy
  exact hy.symm

/-! ### Outside the band -/

/-- `-α ln (-E_α a) = a`. -/
theorem neg_mul_log_kruzkov {α : ℝ} (hα : α ≠ 0) (a : ℝ) :
    -α * Real.log (-kruzkov (1 / α) (a : WithTop ℝ)) = a := by
  change -α * Real.log (-(-Real.exp (-(1 / α) * a))) = a
  rw [neg_neg, Real.log_exp]
  field_simp

theorem eq_of_notMem_band {p : AnbParams X} (hα : 0 < p.α) {s : AnbState X} {x : X}
    (hx : x ∉ (anbStepData p s).band) :
    (anbStepWith S p s).uSub x = (anbStepData p s).uHat x ∧
      (anbStepWith S p s).uSup x = s.uSup x := by
  rw [anbStep_eq]
  refine ⟨?_, ?_⟩
  · change -p.α * Real.log (-wSub S p s x) = _
    rw [wSub_of_notMem p s hx, anbStepData_vSub]
    exact neg_mul_log_kruzkov hα.ne' _
  · change kruzkovInv p.α (wSup S p s x) = _
    rw [wSup_of_notMem p s hx, anbStepData_vSup]
    exact kruzkovInv_kruzkov hα.ne' _

/-! ### Lines anb:while_sub and anb:while_sup in Kruzkov coordinates -/

omit [Fintype X] [LinearOrder X] in
/-- `E_α (E_α⁻¹ v) = v` for `v ≤ 0`. -/
theorem kruzkov_kruzkovInv {α : ℝ} (hα : α ≠ 0) {v : ℝ} (hv : v ≤ 0) :
    kruzkov (1 / α) (kruzkovInv α v) = v := by
  rcases hv.lt_or_eq with hv | hv
  · unfold kruzkovInv
    simp only [hv, ↓reduceIte]
    exact ComparisonLambdaProof.kruzkov_coe_log hα hv
  · subst hv
    simp [kruzkovInv, kruzkov]

omit [Fintype X] [LinearOrder X] in
theorem kruzkov_nonpos (αinv : ℝ) (a : WithTop ℝ) : kruzkov αinv a ≤ 0 := by
  induction a using WithTop.recTopCoe with
  | top => exact le_rfl
  | coe r => exact (ComparisonLambdaProof.kruzkov_coe_neg αinv r).le

omit [Fintype X] [LinearOrder X] in
/-- Back from Kruzkov coordinates, sub-solution version. -/
theorem sub_convert {Λ : (X → ℝ) → X → ℝ} (hΛmono : ∀ x, Monotone (Λ · x)) {α : ℝ} (hα : 0 < α)
    {B : Set X} {uHat u' w : X → ℝ} (huHat : uHat ≤ Λ uHat)
    (hwu : ∀ y, w y = kruzkov (1 / α) (u' y : WithTop ℝ))
    (h0 : ∀ y, kruzkov (1 / α) (uHat y : WithTop ℝ) ≤ w y)
    (hw : w ≤ restrictOp (Global.kruzkovOp α Λ) B w)
    (hoff : ∀ y ∉ B, w y = kruzkov (1 / α) (uHat y : WithTop ℝ)) :
    u' ≤ Λ u' ∧ uHat ≤ u' := by
  have hle : uHat ≤ u' := fun y =>
    (ComparisonLambdaProof.kruzkov_coe_le_iff hα _ _).1 ((h0 y).trans_eq (hwu y))
  refine ⟨fun y => ?_, hle⟩
  by_cases hy : y ∈ B
  · have h1 := hw y
    rw [restrictOp_of_mem _ hy] at h1
    change w y ≤ kruzkovOp α (Λ · y) w at h1
    have hw' : w = fun z => kruzkov (1 / α) (u' z : WithTop ℝ) := funext hwu
    rw [hwu y, hw', ComparisonLambdaProof.kruzkovOp_kruzkov hα.ne' (hΛmono y)] at h1
    exact (ComparisonLambdaProof.kruzkov_coe_le_iff hα _ _).1 h1
  · have : u' y = uHat y :=
      ComparisonLambdaProof.kruzkov_coe_injective hα ((hwu y).symm.trans (hoff y hy))
    rw [this]
    exact (huHat y).trans (hΛmono y hle)

omit [Fintype X] [LinearOrder X] in
/-- Back from Kruzkov coordinates, super-solution version. -/
theorem sup_convert {Λ : (X → ℝ) → X → ℝ} {α : ℝ} (hα : 0 < α) {B : Set X}
    {uSup u' : X → WithTop ℝ} {w : X → ℝ} (hsup : Global.monotoneExtension Λ uSup ≤ uSup)
    (hwu : ∀ y, w y = kruzkov (1 / α) (u' y)) (h0 : ∀ y, w y ≤ kruzkov (1 / α) (uSup y))
    (hw : restrictOp (Global.kruzkovOp α Λ) B w ≤ w)
    (hoff : ∀ y ∉ B, w y = kruzkov (1 / α) (uSup y)) :
    Global.monotoneExtension Λ u' ≤ u' ∧ u' ≤ uSup := by
  have hle : u' ≤ uSup := fun y => (kruzkov_le_iff hα _ _).1 ((hwu y).symm.trans_le (h0 y))
  refine ⟨fun y => ?_, hle⟩
  by_cases hy : y ∈ B
  · have h1 := hw y
    rw [restrictOp_of_mem _ hy] at h1
    change kruzkovOp α (Λ · y) w ≤ w y at h1
    have hw' : w = fun z => kruzkov (1 / α) (u' z) := funext hwu
    rw [hwu y, hw', kruzkovOp_kruzkov_ext hα.ne'] at h1
    exact (kruzkov_le_iff hα _ _).1 h1
  · have h2 : u' y = uSup y := le_antisymm (hle y)
      ((kruzkov_le_iff hα _ _).1 ((hoff y hy).symm.trans_le (hwu y).le))
    calc Global.monotoneExtension Λ u' y ≤ Global.monotoneExtension Λ uSup y :=
          KruzkovProof.monotone_monotoneExtension (Λ · y) hle
      _ ≤ uSup y := hsup y
      _ = u' y := h2.symm

omit [Fintype X] [LinearOrder X] in
/-- `Φ_α` maps negative maps to negative maps. -/
theorem kruzkovOp_neg {Λ : (X → ℝ) → X → ℝ} (hΛmono : ∀ x, Monotone (Λ · x)) {α : ℝ}
    (hα : 0 < α) {r : X → ℝ} (hr : ∀ y, r y < 0) (y : X) : Global.kruzkovOp α Λ r y < 0 := by
  change kruzkovOp α (Λ · y) r < 0
  have hr' : r = fun z => kruzkov (1 / α) ((-α * Real.log (-r z) : ℝ) : WithTop ℝ) :=
    funext fun z => (ComparisonLambdaProof.kruzkov_coe_log hα.ne' (hr z)).symm
  rw [hr', ComparisonLambdaProof.kruzkovOp_kruzkov hα.ne' (hΛmono y)]
  exact ComparisonLambdaProof.kruzkov_coe_neg _ _

omit [Fintype X] [LinearOrder X] in
/-- For the output `r` of the inner solver (sub-solution variant) on the band `B`, started from
`E_α û` with `û ≤ Λ û`, the values outside `B` being frozen to `E_α û`: the extended map `W`
satisfies `E_α û ≤ W`, `W ≤ (Φ_α)_B W` and `W < 0`. These properties are preserved by partial
updates `w(y) ← Ψ w(y)`, hence hold for the output (`AnbInnerSolver.Valid`). -/
theorem subRun_props (S : AnbInnerSolver X) [S.Valid] {Λ : (X → ℝ) → X → ℝ}
    (hΛmono : ∀ x, Monotone (Λ · x)) {α : ℝ} (hα : 0 < α) (B : Set X) {uHat : X → ℝ}
    (huHat : uHat ≤ Λ uHat) (η : ℝ) :
    let v := fun y => kruzkov (1 / α) (uHat y : WithTop ℝ)
    let Ψ := bandOp (Global.kruzkovOp α Λ) B v
    let W := bandExtend B v (S.subResult B Ψ η (fun x => v x))
    v ≤ W ∧ W ≤ restrictOp (Global.kruzkovOp α Λ) B W ∧ ∀ y, W y < 0 := by
  intro v Ψ W
  have hmonoΦ := ParallelAgsiKruzkovProof.monotone_global_kruzkovOp (Λ := Λ) hα
  have hΨ : Monotone Ψ := BandProof.monotone_bandOp fun x _ _ _ h => hmonoΦ h x
  have hv : v ≤ Global.kruzkovOp α Λ v := fun y => by
    change v y ≤ kruzkovOp α (Λ · y) v
    rw [ComparisonLambdaProof.kruzkovOp_kruzkov hα.ne' (hΛmono y)]
    exact (ComparisonLambdaProof.kruzkov_coe_le_iff hα _ _).2 (huHat y)
  have hvneg : ∀ y, v y < 0 := fun y => ComparisonLambdaProof.kruzkov_coe_neg _ _
  have hr0 : (fun x : B => v x) ≤ Ψ fun x => v x := fun x => by
    change v x ≤ Global.kruzkovOp α Λ (bandExtend B v fun x => v x) x
    rw [bandExtend_restrict]
    exact hv x
  -- the invariant set
  let N : Set (B → ℝ) := {w | (fun x : B => v x) ≤ w ∧ w ≤ Ψ w ∧ ∀ y, w y < 0}
  have hN : ∀ w ∈ N, ∀ w' : B → ℝ, (∀ y, w' y = w y ∨ w' y = Ψ w y) → w' ∈ N := by
    rintro w ⟨hw1, hw2, hw3⟩ w' hw'
    have hle : w ≤ w' := fun y => by
      rcases hw' y with h | h <;> rw [h]
      exact hw2 y
    have hle' : w' ≤ Ψ w := fun y => by
      rcases hw' y with h | h <;> rw [h]
      exact hw2 y
    refine ⟨hw1.trans hle, hle'.trans (hΨ hle), fun y => ?_⟩
    rcases hw' y with h | h <;> rw [h]
    · exact hw3 y
    · refine kruzkovOp_neg hΛmono hα (fun z => ?_) y
      by_cases hz : z ∈ B
      · rw [bandExtend_of_mem _ _ _ hz]; exact hw3 _
      · rw [bandExtend_of_notMem _ _ _ hz]; exact hvneg z
  obtain ⟨hinc, hsub, hneg⟩ : S.subResult B Ψ η (fun x => v x) ∈ N :=
    AnbInnerSolver.Valid.subResult_mem B Ψ η _ N ⟨le_rfl, hr0, fun y => hvneg y⟩ hN
  set r := S.subResult B Ψ η (fun x => v x) with hr
  refine ⟨fun y => ?_, ?_, fun y => ?_⟩
  · change v y ≤ bandExtend B v r y
    by_cases hy : y ∈ B
    · rw [bandExtend_of_mem _ _ _ hy]
      exact hinc ⟨y, hy⟩
    · rw [bandExtend_of_notMem _ _ _ hy]
  · change bandExtend B v r ≤ restrictOp (Global.kruzkovOp α Λ) B (bandExtend B v r)
    rw [BandProof.restrictOp_bandExtend]
    exact BandProof.bandExtend_mono hsub
  · change bandExtend B v r y < 0
    by_cases hy : y ∈ B
    · rw [bandExtend_of_mem _ _ _ hy]; exact hneg _
    · rw [bandExtend_of_notMem _ _ _ hy]; exact hvneg y

omit [Fintype X] [LinearOrder X] in
/-- For the output `r` of the inner solver (super-solution version) on the band `B`, started from
`E_α u̲` with `Λ_∞ u̲ ≤ u̲`, the values outside `B` being frozen to `E_α u̲`: the extended map `W`
satisfies `W ≤ E_α u̲` and `(Φ_α)_B W ≤ W`. -/
theorem supRun_props (S : AnbInnerSolver X) [S.Valid] {Λ : (X → ℝ) → X → ℝ} {α : ℝ}
    (hα : 0 < α) (B : Set X) {uSup : X → WithTop ℝ}
    (hsup : Global.monotoneExtension Λ uSup ≤ uSup) (η : ℝ) :
    let v := fun y => kruzkov (1 / α) (uSup y)
    let Ψ := bandOp (Global.kruzkovOp α Λ) B v
    let W := bandExtend B v (S.supResult B Ψ η (fun x => v x))
    W ≤ v ∧ restrictOp (Global.kruzkovOp α Λ) B W ≤ W := by
  intro v Ψ W
  have hmonoΦ := ParallelAgsiKruzkovProof.monotone_global_kruzkovOp (Λ := Λ) hα
  have hΨ : Monotone Ψ := BandProof.monotone_bandOp fun x _ _ _ h => hmonoΦ h x
  have hv : Global.kruzkovOp α Λ v ≤ v := fun y => by
    change kruzkovOp α (Λ · y) v ≤ v y
    rw [kruzkovOp_kruzkov_ext hα.ne']
    exact (kruzkov_le_iff hα _ _).2 (hsup y)
  have hr0 : (Ψ fun x : B => v x) ≤ fun x : B => v x := fun x => by
    change Global.kruzkovOp α Λ (bandExtend B v fun x => v x) x ≤ v x
    rw [bandExtend_restrict]
    exact hv x
  let N : Set (B → ℝ) := {w | w ≤ (fun x : B => v x) ∧ Ψ w ≤ w}
  have hN : ∀ w ∈ N, ∀ w' : B → ℝ, (∀ y, w' y = w y ∨ w' y = Ψ w y) → w' ∈ N := by
    rintro w ⟨hw1, hw2⟩ w' hw'
    have hle : w' ≤ w := fun y => by
      rcases hw' y with h | h <;> rw [h]
      exact hw2 y
    have hle' : Ψ w ≤ w' := fun y => by
      rcases hw' y with h | h <;> rw [h]
      exact hw2 y
    exact ⟨hle.trans hw1, (hΨ hle).trans hle'⟩
  obtain ⟨hdec, hsup'⟩ : S.supResult B Ψ η (fun x => v x) ∈ N :=
    AnbInnerSolver.Valid.supResult_mem B Ψ η _ N ⟨le_rfl, hr0⟩ hN
  set r := S.supResult B Ψ η (fun x => v x) with hr
  refine ⟨fun y => ?_, ?_⟩
  · change bandExtend B v r y ≤ v y
    by_cases hy : y ∈ B
    · rw [bandExtend_of_mem _ _ _ hy]; exact hdec ⟨y, hy⟩
    · rw [bandExtend_of_notMem _ _ _ hy]
  · change restrictOp (Global.kruzkovOp α Λ) B (bandExtend B v r) ≤ bandExtend B v r
    rw [BandProof.restrictOp_bandExtend]
    exact BandProof.bandExtend_mono hsup'

/-! ### Prop. prop:Dijkstra_band: the initial guess -/

omit [LinearOrder X] in
theorem anbLevel_le (ε T : ℝ) (uHat : X → ℝ) (uSup : X → WithTop ℝ) :
    anbLevel ε T uHat uSup ≤ T := by
  unfold anbLevel
  dsimp only
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-- `B_n = {t⁻_n ≤ û_n < nτ}`, with `t⁻_n = t_n - Δ_n`. -/
theorem mem_band_iff (p : AnbParams X) (s : AnbState X) (x : X) :
    x ∈ (anbStepData p s).band ↔ (anbStepData p s).tMinus ≤
      (anbStepData p s).uHat x ∧ (anbStepData p s).uHat x < s.n * p.τ := by
  rw [anbStepData_band, AnbStepData.tMinus_def, anbStepData_Δ]
  simp only [anbBand, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, h2⟩

theorem anbRun_n (p : AnbParams X) (k : ℕ) : (anbRunWith S p k).n = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [anbRunWith, Function.iterate_succ_apply', ← anbRunWith]
    exact congrArg (· + 1) ih

/-- The first claim of Prop. prop:Dijkstra_band: if the initial guess of an iteration is a
super-solution of its operator `Γ'`, then so is the guess `anbDijkstraGuess` built for the next
iteration. Below `t⁻_n`, the guess is `û_n = ū_{n+1}` (the band lies above `t⁻_n`) and, by
causality, `Γ` takes the same value at the guess and at `û_n`, below `û_n`. -/
theorem guess_step {p : AnbParams X} (hΓmono : ∀ x, Monotone (p.Γ · x))
    (hΓcaus : ∀ x, Causal (p.Γ · x)) (hα : 0 < p.α) (hτ : 0 ≤ p.τ) {s : AnbState X}
    (h3 : anbHatOp p.Γ s.uSub (s.n * p.τ) s.uHatInit ≤ s.uHatInit) :
    anbHatOp p.Γ (anbStepWith S p s).uSub ((anbStepWith S p s).n * p.τ)
      (anbStepWith S p s).uHatInit ≤
      (anbStepWith S p s).uHatInit := by
  classical
  set d := anbStepData p s with hd
  set T : ℝ := s.n * p.τ with hT
  set T' : ℝ := ((s.n + 1 : ℕ) : ℝ) * p.τ with hT'
  set tm := d.tMinus with htm
  set u' := (anbStepWith S p s).uSub with hu'
  have hEq : ∀ x, d.uHat x = max (s.uSub x) (min T (p.Γ d.uHat x)) := fun x =>
    (uHat_eq hΓmono hΓcaus h3 x).2
  have htmT : tm ≤ T := by
    have := anbLevel_le p.ε T d.uHat s.uSup
    rw [htm, hd, AnbStepData.tMinus_def, anbStepData_Δ, anbStepData_t]
    linarith
  have hTT' : T ≤ T' := by rw [hT, hT']; push_cast; linarith
  let g : X → ℝ := fun y => if d.uHat y < tm then d.uHat y else max (u' y) T'
  have hg : (anbStepWith S p s).uHatInit = fun y => (g y : WithTop ℝ) := by
    funext y
    change anbDijkstraGuess T' tm d.uHat u' y = _
    unfold anbDijkstraGuess
    by_cases h : d.uHat y < tm <;> simp only [g, h, ↓reduceIte]
  have hn : ((anbStepWith S p s).n : ℝ) * p.τ = T' := rfl
  rw [hg, hn]
  intro x
  change max _ (min _ (monotoneExtension (p.Γ · x) _)) ≤ _
  rw [MonotoneExtension.coe_eq (hΓmono x), ← WithTop.coe_min, ← WithTop.coe_max,
    WithTop.coe_le_coe]
  by_cases hx : d.uHat x < tm
  · have hgx : g x = d.uHat x := by simp only [g, hx, ↓reduceIte]
    have hnot : x ∉ d.band := fun h => absurd ((mem_band_iff p s x).1 h).1 (not_le.2 hx)
    have hux : u' x = d.uHat x := (eq_of_notMem_band hα hnot).1
    -- `Γ û_n(x) ≤ û_n(x) < t⁻_n`
    have hΓle : p.Γ d.uHat x ≤ d.uHat x := by
      have h1 : min T (p.Γ d.uHat x) ≤ d.uHat x := (hEq x).symm ▸ le_max_right _ _
      have h2 : min T (p.Γ d.uHat x) < T := h1.trans_lt (hx.trans_le htmT)
      rwa [min_eq_right (le_of_lt (lt_of_not_ge fun h => (min_eq_left h ▸ h2).false))] at h1
    -- by causality, `Γ g(x) = Γ û_n(x)`
    have hmin : ∀ y, min (g y) tm = min (d.uHat y) tm := fun y => by
      by_cases hy : d.uHat y < tm
      · simp only [g, hy, ↓reduceIte]
      · have hgy : g y = max (u' y) T' := by simp only [g, hy, ↓reduceIte]
        rw [hgy, min_eq_right ((htmT.trans hTT').trans (le_max_right _ _)),
          min_eq_right (not_lt.1 hy)]
    obtain ⟨δ, hδ, hcaus⟩ := hΓcaus x g d.uHat tm hmin
    have hlt : p.Γ d.uHat x < tm + δ := (hΓle.trans_lt hx).trans (lt_add_of_pos_right _ hδ)
    rw [min_eq_left hlt.le] at hcaus
    have hΓg : p.Γ g x = p.Γ d.uHat x := by
      rcases le_or_gt (tm + δ) (p.Γ g x) with h | h
      · rw [min_eq_right h] at hcaus; exact absurd hcaus hlt.ne'
      · rwa [min_eq_left h.le] at hcaus
    rw [hgx, hux]
    exact max_le le_rfl ((min_le_right _ _).trans (hΓg ▸ hΓle))
  · have hgx : g x = max (u' x) T' := by simp only [g, hx, ↓reduceIte]
    rw [hgx]
    exact max_le (le_max_left _ _) ((min_le_left _ _).trans (le_max_right _ _))

/-- Along the run, the initial guess of line anb:hatu is a super-solution of `Γ'`. -/
theorem guess_run {p : AnbParams X} (hΓmono : ∀ x, Monotone (p.Γ · x))
    (hΓcaus : ∀ x, Causal (p.Γ · x)) (hα : 0 < p.α) (hτ : 0 ≤ p.τ) (k : ℕ) :
    anbHatOp p.Γ (anbRunWith S p k).uSub ((anbRunWith S p k).n * p.τ) (anbRunWith S p k).uHatInit ≤
      (anbRunWith S p k).uHatInit := by
  induction k with
  | zero =>
    intro x
    simp only [anbRunWith, Function.iterate_zero, id, anbInit, Nat.cast_zero, zero_mul, anbHatOp,
      Pi.zero_apply, WithTop.coe_zero]
    exact max_le le_rfl (min_le_left _ _)
  | succ k ih =>
    rw [anbRunWith, Function.iterate_succ_apply', ← anbRunWith]
    exact guess_step hΓmono hΓcaus hα hτ ih

theorem anbRun_succ (p : AnbParams X) (k : ℕ) :
    anbRunWith S p (k + 1) = anbStepWith S p (anbRunWith S p k) :=
  Function.iterate_succ_apply' _ _ _

/-! ### Prop. prop:Dijkstra_band: the points updated by Dijkstra's method -/

theorem hatRun_count_mem {p : AnbParams X} (hΓmono : ∀ x, Monotone (p.Γ · x))
    (hΓcaus : ∀ x, Causal (p.Γ · x)) (hα : 0 < p.α) (hτ : 0 ≤ p.τ) {k : ℕ} {x : X}
    (hx : (anbRunDataWith S p (k + 1)).hatRun.count x ≠ 0) :
    x ∈ anbDijkstraBand (anbRunDataWith S p k).tMinus (((k + 1 : ℕ) : ℝ) * p.τ)
      (anbRunDataWith S p k).uHat (anbRunDataWith S p (k + 1)).uHat := by
  classical
  simp only [anbRunDataWith_def] at hx ⊢
  have hG' := guess_run (S := S) hΓmono hΓcaus hα hτ (k + 1)
  rw [anbRun_succ] at hx hG' ⊢
  set s := anbRunWith S p k with hs
  set d := anbStepData p s with hd
  set s' := anbStepWith S p s with hs'
  have hcaus' := causal_anbHatOp hΓmono hΓcaus s'.uSub (s'.n * p.τ)
  -- the point is updated once, so its value has decreased
  have h1 : (anbStepData p s').hatRun.count x = 1 := by
    rw [anbStepData_hatRun] at hx ⊢
    exact le_antisymm (DijkstraProof.count_le_one hcaus' _ _ x) (Nat.one_le_iff_ne_zero.2 hx)
  have hlt : (anbStepData p s').hatRun.u x < s'.uHatInit x := by
    rw [anbStepData_hatRun] at h1 ⊢
    exact (DijkstraProof.count_eq_one_iff hcaus' _ _ x).1 h1
  rw [(uHat_eq hΓmono hΓcaus hG' x).1] at hlt
  have hge : s'.uSub x ≤ (anbStepData p s').uHat x := by
    rw [(uHat_eq hΓmono hΓcaus hG' x).2]; exact le_max_left _ _
  change _ < anbDijkstraGuess (((s.n + 1 : ℕ) : ℝ) * p.τ) d.tMinus d.uHat s'.uSub x at hlt
  unfold anbDijkstraGuess at hlt
  split_ifs at hlt with hxm
  · -- below `t⁻`, the guess is `û_n(x) = ū_{n+1}(x) ≤ û_{n+1}(x)`
    exfalso
    have hnot : x ∉ d.band := fun h => absurd ((mem_band_iff p s x).1 h).1 (not_le.2 hxm)
    rw [WithTop.coe_lt_coe, ← (eq_of_notMem_band hα hnot).1] at hlt
    exact absurd hge (not_le.2 hlt)
  · rw [WithTop.coe_lt_coe] at hlt
    refine ⟨not_lt.1 hxm, ?_⟩
    rw [hs, anbRun_n] at hlt
    by_contra hT
    exact absurd (max_le hge (not_lt.1 hT)) (not_le.2 hlt)

/-- One iteration from a state with `ū ≤ Λ ū`, `Λ u̲ ≤ u̲` and a valid initial guess satisfies
the properties of Prop. prop:always_subsol, and the next state again has `ū ≤ Λ ū`, `Λ u̲ ≤ u̲`. -/
theorem step_always_subsol [S.Valid] {p : AnbParams X} (hΛmono : ∀ x, Monotone (p.Λ · x))
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x))
    (hΓΛ : ∀ u, p.Γ u ≤ p.Λ u) (hα : 0 < p.α) {s : AnbState X} (h1 : s.uSub ≤ p.Λ s.uSub)
    (h2 : Global.monotoneExtension p.Λ s.uSup ≤ s.uSup)
    (h3 : anbHatOp p.Γ s.uSub (s.n * p.τ) s.uHatInit ≤ s.uHatInit) :
    AnbAlwaysSubsolWith S p s ∧ (anbStepWith S p s).uSub ≤ p.Λ (anbStepWith S p s).uSub ∧
      Global.monotoneExtension p.Λ (anbStepWith S p s).uSup ≤ (anbStepWith S p s).uSup := by
  have hEq : ∀ x, (anbStepData p s).uHat x =
      max (s.uSub x) (min (s.n * p.τ) (p.Γ (anbStepData p s).uHat x)) := fun x =>
    (uHat_eq hΓmono hΓcaus h3 x).2
  have hle : s.uSub ≤ (anbStepData p s).uHat := fun x => by rw [hEq x]; exact le_max_left _ _
  have hhat : (anbStepData p s).uHat ≤ p.Λ (anbStepData p s).uHat := fun x => by
    rw [hEq x]
    exact max_le ((h1 x).trans (hΛmono x hle))
      ((min_le_right _ _).trans (hΓΛ (anbStepData p s).uHat x))
  -- line anb:while_sub
  obtain ⟨ha, hb, hc⟩ := subRun_props S hΛmono hα (anbStepData p s).band hhat
    (anbStepData p s).η
  have hsub := sub_convert (u' := (anbStepWith S p s).uSub) (w := wSub S p s) hΛmono hα hhat
    (fun y => (ComparisonLambdaProof.kruzkov_coe_log hα.ne' (hc y)).symm) ha hb
    (fun y hy => wSub_of_notMem p s hy)
  -- line anb:while_sup
  obtain ⟨hd, he⟩ := supRun_props S hα (anbStepData p s).band h2 (anbStepData p s).η
  have hsup := sup_convert (u' := (anbStepWith S p s).uSup) (w := wSup S p s) hα h2
    (fun y => (kruzkov_kruzkovInv hα.ne' ((hd y).trans (kruzkov_nonpos _ _))).symm) hd he
    (fun y hy => wSup_of_notMem p s hy)
  exact ⟨⟨h1, h2, hhat, hle, hsub.2, hsup.2⟩, hsub.1, hsup.1⟩

theorem always_subsol [S.Valid] {p : AnbParams X} (hΛmono : ∀ x, Monotone (p.Λ · x))
    (hΛ0 : 0 ≤ p.Λ 0)
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x))
    (hΓΛ : ∀ u, p.Γ u ≤ p.Λ u) (hα : 0 < p.α) (hτ : 0 ≤ p.τ) (k : ℕ) :
    AnbAlwaysSubsolWith S p (anbRunWith S p k) := by
  have hinv : ∀ k, (anbRunWith S p k).uSub ≤ p.Λ (anbRunWith S p k).uSub ∧
      Global.monotoneExtension p.Λ (anbRunWith S p k).uSup ≤ (anbRunWith S p k).uSup := by
    intro k
    induction k with
    | zero => exact ⟨hΛ0, fun _ => le_top⟩
    | succ k ih =>
      rw [anbRun_succ]
      exact (step_always_subsol hΛmono hΓmono hΓcaus hΓΛ hα ih.1 ih.2
        (guess_run (S := S) hΓmono hΓcaus hα hτ k)).2
  exact (step_always_subsol hΛmono hΓmono hΓcaus hΓΛ hα (hinv k).1 (hinv k).2
    (guess_run (S := S) hΓmono hΓcaus hα hτ k)).1

/-! ### After the stopping test -/

theorem succ_of_done {p : AnbParams X} (hΓmono : ∀ x, Monotone (p.Γ · x))
    (hΓcaus : ∀ x, Causal (p.Γ · x)) (hα : 0 < p.α) (hτ : 0 ≤ p.τ) (hε : 0 ≤ 1 + p.ε) {k : ℕ}
    (hk : anbDone p (anbRunWith S p k)) :
    (anbRunDataWith S p k).band = ∅ ∧
    (anbRunWith S p (k + 1)).uSub = (anbRunDataWith S p k).uHat ∧
    (anbRunWith S p (k + 1)).uSup = (anbRunWith S p k).uSup ∧
    (anbRunWith S p (k + 1)).countSub = (anbRunWith S p k).countSub ∧
    (anbRunWith S p (k + 1)).countSup = (anbRunWith S p k).countSup ∧
    anbDone p (anbRunWith S p (k + 1)) := by
  classical
  simp only [anbRunDataWith_def]
  set s := anbRunWith S p k with hs
  have hle : s.uSub ≤ (anbStepData p s).uHat := fun x => by
    rw [(uHat_eq hΓmono hΓcaus (guess_run (S := S) hΓmono hΓcaus hα hτ k) x).2]
    exact le_max_left _ _
  have hmul : ∀ x, s.uSup x ≤ (((1 + p.ε) * (anbStepData p s).uHat x : ℝ) : WithTop ℝ) :=
    fun x => (hk x).trans (WithTop.coe_le_coe.2 (mul_le_mul_of_nonneg_left (hle x) hε))
  -- no point satisfies `(1 + ε) û < u̲`, so `t = nτ`, `Δ = 0` and the band is empty
  have ht : (anbStepData p s).t = s.n * p.τ := by
    rw [anbStepData_t]
    unfold anbLevel
    dsimp only
    split_ifs with hne
    · obtain ⟨x, hx⟩ := hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact absurd hx (not_lt.2 (hmul x))
    · rfl
  have hB : (anbStepData p s).band = ∅ := by
    rw [anbStepData_band, anbStepData_Δ, ht]
    ext x
    simp only [anbBand, sub_self, mul_zero, sub_zero, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2⟩
    exact absurd h2 (not_lt.2 h1)
  have hoff : ∀ x, x ∉ (anbStepData p s).band := fun x => by rw [hB]; exact Set.notMem_empty x
  have hsub : (anbStepWith S p s).uSub = (anbStepData p s).uHat :=
    funext fun x => (eq_of_notMem_band hα (hoff x)).1
  have hsup : (anbStepWith S p s).uSup = s.uSup := funext fun x => (eq_of_notMem_band hα (hoff x)).2
  rw [anbRun_succ]
  refine ⟨hB, hsub, hsup, ?_, ?_, ?_⟩
  · funext x; rw [anbStep_eq, ← hs]; simp only [hB, Set.mem_empty_iff_false, ↓reduceIte, add_zero]
  · funext x; rw [anbStep_eq, ← hs]; simp only [hB, Set.mem_empty_iff_false, ↓reduceIte, add_zero]
  · intro x; rw [hsub, hsup]; exact hmul x

end GuaranteedSubsol.AnbProof
