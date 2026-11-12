/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AnbHeap
import LeanHJBAutoformalisation.GuaranteedSubsol.AnbLazyProof
import LeanHJBAutoformalisation.GuaranteedSubsol.DijkstraHeapProof
import LeanHJBAutoformalisation.GuaranteedSubsol.DijkstraHeapCorrectProof

/-!
# The ANB with sorted lists is equivalent to the ANB with a placeholder: proof

Provider proof for the frozen anchor `GuaranteedSubsol.anbHeapRun_equiv`, see `ANCHORS.md`. By
induction on the iterations, the states are related by `HRel`: same `u̲~`, `ǔ`, counters, the same
`ū` from the first effective iteration on, and the lists `L`, `M`, `S`, `Sc` hold the keys of
eqs. eqdef:L_heap, eqdef:M_heap, eqdef:S_heap (and of `Sc`). Two invariants make the partial
update of line anb_lazy:olu_gets_hatu correct: `ǔ = ∞` at the placeholders (`top_imp`), and
`ǔ = ũ` at the real values `< (n-1)τ` outside `B_{n-1}` (`below`). In each iteration:
* Dijkstra's method with the list `L` follows algo:Dijkstra for `max {ū, Γ}^{<T}`
  (`DijkstraHeapProof.loop_spec`, `dijkstraHeapLoop_correct`), as in the ANB with a placeholder,
  hence yields the same `ǔ`
  (`dij_facts`); at the end, all the keys of `L` are `≥ T`;
* the map `ũ` after line anb_lazy:olu_gets_hatu is that of the ANB with a placeholder: at the
  points that are not updated, it already has the right value, by the two invariants and the fix
  of the paper (the points of `S` with key in `[(n-1)τ, T[`) (`uTildeInit_eq`);
* `t_n` and `B_n` only depend on `(ũ^init)^{⋄→T}` (`level_eq`, `mem_entriesIco_iff`);
* the keys of `L` that are not recomputed in line anb_lazy:L do not change: their stencil does not
  meet `B_n`, and `max {ū, Γ ǔ} < ǔ` is unchanged when `ū` becomes `max {ū, min {T, ǔ}}`, since
  the keys are `≥ T` (`L_step`).
-/

namespace GuaranteedSubsol.AnbHeapProof

open OrderedPartialMap OrderedPartialMapProof AnbProof AnbLazyProof

variable {X : Type*}

/-! ### Keys -/

theorem anbKeyM_eq_some {ε : ℝ} {u : X → Option ℝ} {uSup : X → WithTop ℝ} {x : X} {r : ℝ} :
    anbKeyM ε u uSup x = some r ↔ u x = some r ∧ (((1 + ε) * r : ℝ) : WithTop ℝ) < uSup x := by
  unfold anbKeyM
  cases u x with
  | none => simp
  | some r' =>
    dsimp only
    split_ifs with h
    · simp only [Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨rfl, h⟩
      · rintro ⟨rfl, -⟩; rfl
    · simp only [false_iff, not_and, Option.some.injEq]
      rintro rfl; exact h

theorem anbKeyM_eq_none {ε : ℝ} {u : X → Option ℝ} {uSup : X → WithTop ℝ} {x : X} :
    anbKeyM ε u uSup x = none ↔
      ∀ r : ℝ, u x = some r → uSup x ≤ (((1 + ε) * r : ℝ) : WithTop ℝ) := by
  rw [← not_iff_not, ← ne_eq, Option.ne_none_iff_exists']
  simp only [anbKeyM_eq_some, not_forall, not_le, exists_prop]

theorem anbKeySc_eq_some {u : X → Option ℝ} {uSup : X → WithTop ℝ} {x : X}
    {t : (WithTop ℝ)ᵒᵈ} :
    anbKeySc u uSup x = some t ↔ u x = none ∧ t = OrderDual.toDual (uSup x) := by
  unfold anbKeySc
  cases u x with
  | none => simp [eq_comm]
  | some r => simp

/-- `(a ≤ w < T)` for a real value `w` only depends on `w^{⋄→T}`. -/
theorem exists_iff_getD {a T : ℝ} {w : Option ℝ} :
    (∃ r, w = some r ∧ a ≤ r ∧ r < T) ↔ (a ≤ w.getD T ∧ w.getD T < T) := by
  cases w with
  | none => simp
  | some r => simp

/-! ### The lists -/

variable [Fintype X] [LinearOrder X]

omit [LinearOrder X] in
/-- The points of `S` in `[a, T[`. -/
theorem mem_entriesIco_iff (m : OrderedPartialMap X ℝ) {u : X → Option ℝ}
    (hm : m.v = anbKeyS u) (a T : ℝ) (x : X) :
    x ∈ (m.entriesIco a T).1 ↔ (a ≤ (u x).getD T ∧ (u x).getD T < T) := by
  rw [entriesIco_fst, hm]
  exact exists_iff_getD

omit [LinearOrder X] in
theorem mem_entriesIco_iff' (m : OrderedPartialMap X ℝ) {u : X → Option ℝ}
    (hm : m.v = anbKeyS u) (a T : ℝ) (x : X) :
    x ∈ (m.entriesIco a T).1 ↔ ∃ r : ℝ, u x = some r ∧ a ≤ r ∧ r < T := by
  rw [entriesIco_fst, hm]
  rfl

/-- `t_n` computed from the smallest key of `M`. -/
theorem level_eq (ε T : ℝ) (u : X → Option ℝ) (uSup : X → WithTop ℝ) :
    (match botVal (anbKeyM ε u uSup) with
      | none => T
      | some (t, _) => min T t) = anbLazyLevel ε T u uSup := by
  rcases hb : botVal (anbKeyM ε u uSup) with _ | ⟨t, x⟩
  · refine le_antisymm (le_lazyLevel le_rfl fun y hne hlt => ?_) (lazyLevel_le _ _ _ _)
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 hne
    have := botVal_eq_none_iff.1 hb y
    rw [anbKeyM_eq_none] at this
    rw [hr, Option.getD_some] at hlt
    exact absurd (this r hr) (not_le.2 hlt)
  · obtain ⟨hx, hmin⟩ := botVal_eq_some hb
    rw [anbKeyM_eq_some] at hx
    dsimp only
    refine le_antisymm (le_lazyLevel (min_le_left _ _) fun y hne hlt => ?_)
      (le_min (lazyLevel_le _ _ _ _) ?_)
    · obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 hne
      rw [hr, Option.getD_some] at hlt ⊢
      have hle := hmin y r (anbKeyM_eq_some.2 ⟨hr, hlt⟩)
      rw [Prod.Lex.toLex_le_toLex] at hle
      refine (min_le_right _ _).trans ?_
      rcases hle with h | ⟨h, -⟩
      · exact h.le
      · exact h.le
    · have h := lazyLevel_le_of_mem (ε := ε) (T := T) (u := u) (uSup := uSup) (x := x)
        (by rw [hx.1]; exact Option.some_ne_none _) (by rw [hx.1, Option.getD_some]; exact hx.2)
      rwa [hx.1, Option.getD_some] at h

omit [LinearOrder X] in
/-- `t_n` only depends on `u^{⋄→T}`. -/
theorem lazyLevel_eq_getD (ε T : ℝ) (u : X → Option ℝ) (uSup : X → WithTop ℝ) :
    anbLazyLevel ε T u uSup = anbLevel ε T (fun x => (u x).getD T) uSup :=
  lazyLevel_eq fun x => by
    cases u x with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some r => exact Or.inr rfl

/-- The stopping test with the list `Sc`. -/
theorem sc_iff {u : X → Option ℝ} {uSup : X → WithTop ℝ} (c : WithTop ℝ) :
    (∀ t x, botVal (anbKeySc u uSup) = some (t, x) → OrderDual.ofDual t ≤ c) ↔
      ∀ x, u x = none → uSup x ≤ c := by
  constructor
  · intro h x hx
    rcases hb : botVal (anbKeySc u uSup) with _ | ⟨t, y⟩
    · have := botVal_eq_none_iff.1 hb x
      simp [anbKeySc, hx] at this
    · have hle := (botVal_eq_some hb).2 x _ (anbKeySc_eq_some.2 ⟨hx, rfl⟩)
      rw [Prod.Lex.toLex_le_toLex] at hle
      have hty : t ≤ OrderDual.toDual (uSup x) := by
        rcases hle with h' | ⟨h', -⟩
        · exact h'.le
        · exact h'.le
      have hty' : uSup x ≤ OrderDual.ofDual t := hty
      exact hty'.trans (h t y hb)
  · intro h t x hb
    obtain ⟨hx, -⟩ := botVal_eq_some hb
    obtain ⟨hux, rfl⟩ := anbKeySc_eq_some.1 hx
    exact h x hux

/-! ### Dijkstra's method in the ANB -/

omit [Fintype X] [LinearOrder X] in
theorem dijkstraCutOp_anbHeapOp (Γ : (X → ℝ) → X → ℝ) (c : X → ℝ) (T : ℝ) :
    dijkstraCutOp (T : WithTop ℝ) (anbHeapOp Γ c) = anbCheckOp Γ c T := rfl

omit [Fintype X] [LinearOrder X] in
theorem hasStencil_anbHeapOp {Γ : (X → ℝ) → X → ℝ} {𝒱 : X → Set X}
    (hst : Global.Ext.HasStencil 𝒱 (Global.monotoneExtension Γ)) (c : X → ℝ) :
    Global.Ext.HasStencil 𝒱 (anbHeapOp Γ c) := fun x u v huv => by
  change max _ (Global.monotoneExtension Γ u x) = max _ (Global.monotoneExtension Γ v x)
  rw [show Global.monotoneExtension Γ u x = Global.monotoneExtension Γ v x from hst x u v huv]

omit [Fintype X] in
/-- A point that algo:Dijkstra did not update keeps its initial value (causality only). -/
theorem dijkstraRun_u_of_count_eq_zero {G : (X → WithTop ℝ) → X → WithTop ℝ}
    (hcaus : ∀ x, Ext.Causal (G · x)) (u₀ : X → WithTop ℝ) (n : ℕ) {x : X}
    (h : (dijkstraRun G u₀ n).count x = 0) : (dijkstraRun G u₀ n).u x = u₀ x := by
  obtain ⟨hle, -, hiff, -⟩ := DijkstraProof.inv_iterate hcaus u₀ n
  refine le_antisymm (hle x) (not_lt.1 fun hlt => ?_)
  have := (hiff x).2 hlt
  change (dijkstraRun G u₀ n).count x = 1 at this
  omega

variable {p : AnbParams X} {a : AnbState X} {l : AnbLazyState X}

/-- Facts on the Dijkstra step of the ANB with a placeholder: `ǔ = û^{<T}`,
`û = max {ū, min {T, ǔ}}`, and `ǔ` is a fixed point of `max {ū, Γ}^{<T}`. -/
theorem lazy_facts (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x))
    (hrel : Rel p.τ a l) (hinit : anbHatOp p.Γ a.uSub (a.n * p.τ) a.uHatInit ≤ a.uHatInit) :
    (∀ x, (anbLazyStepData p l).uCheck x =
      cutoffLt (l.n * p.τ) ((anbStepData p a).uHat x : WithTop ℝ)) ∧
    (∀ x, ((anbStepData p a).uHat x : WithTop ℝ) =
      max (l.uSub p.τ x : WithTop ℝ)
        (min ((l.n * p.τ : ℝ) : WithTop ℝ) ((anbLazyStepData p l).uCheck x))) ∧
    anbCheckOp p.Γ (l.uSub p.τ) (l.n * p.τ) (anbLazyStepData p l).uCheck =
      (anbLazyStepData p l).uCheck := by
  have hTl := nτ_eq hrel
  refine ⟨fun x => ?_, fun x => ?_, ?_⟩
  · rw [hTl]; exact congrFun (uCheck_eq hΓmono hΓcaus hrel hinit) x
  · rw [hTl]; exact uHat_of_check hΓmono hΓcaus hrel hinit x
  · set T : ℝ := a.n * p.τ
    have hmono := monotone_anbCheckOp p.Γ a.uSub T
    have hcaus := causal_anbCheckOp hΓmono hΓcaus a.uSub T
    have hg : anbCheckOp p.Γ a.uSub T (fun x => cutoffLt T (a.uHatInit x)) ≤
        fun x => cutoffLt T (a.uHatInit x) := fun x => by
      rw [anbCheckOp_eq hΓmono hΓcaus a.uSub T (fun y => ULessTProof.cutoffLt_cutoffLt T _) x]
      exact cutoffLt_mono (hinit x)
    have hfixD := dijkstraRun_card_fixed hmono hcaus hg
    change anbCheckOp p.Γ (l.uSub p.τ) (l.n * p.τ) (dijkstraRun (anbCheckOp p.Γ (l.uSub p.τ)
      (l.n * p.τ)) l.uCheckInit (Nat.card X)).u = (dijkstraRun (anbCheckOp p.Γ (l.uSub p.τ)
      (l.n * p.τ)) l.uCheckInit (Nat.card X)).u
    rw [hTl, hrel.uSub_eq, hrel.uCheckInit_eq]
    exact hfixD

omit [Fintype X] [LinearOrder X] in
theorem monotone_anbHeapOp (Γ : (X → ℝ) → X → ℝ) (c : X → ℝ) : Monotone (anbHeapOp Γ c) :=
  fun _ _ h _ => max_le_max le_rfl (KruzkovProof.monotone_monotoneExtension _ h)

omit [Fintype X] [LinearOrder X] in
theorem causal_anbHeapOp [Finite X] {Γ : (X → ℝ) → X → ℝ} (hΓmono : ∀ x, Monotone (Γ · x))
    (hΓcaus : ∀ x, Causal (Γ · x)) (c : X → ℝ) (x : X) : Ext.Causal (anbHeapOp Γ c · x) :=
  ExtCausalMixProof.causal_max (ULessTProof.causal_const _) ((hΓcaus x).ext (hΓmono x))

omit [Fintype X] [LinearOrder X] in
/-- The initial guess of Dijkstra's step of the ANB with a placeholder is a super-solution of
`max {ū, Γ}^{<T}`. -/
theorem lazy_check_sup [Finite X] (hΓmono : ∀ x, Monotone (p.Γ · x))
    (hΓcaus : ∀ x, Causal (p.Γ · x))
    (hrel : Rel p.τ a l) (hinit : anbHatOp p.Γ a.uSub (a.n * p.τ) a.uHatInit ≤ a.uHatInit) :
    anbCheckOp p.Γ (l.uSub p.τ) (l.n * p.τ) l.uCheckInit ≤ l.uCheckInit := by
  rw [nτ_eq hrel, hrel.uSub_eq, hrel.uCheckInit_eq]
  intro x
  rw [anbCheckOp_eq hΓmono hΓcaus a.uSub _ (fun y => ULessTProof.cutoffLt_cutoffLt _ _) x]
  exact cutoffLt_mono (hinit x)

/-! ### The relation -/

/-- The relation between the states of the ANB with sorted lists and of the ANB with a
placeholder. -/
structure HRel (p : AnbParams X) (h : AnbHeapState X) (l : AnbLazyState X) : Prop where
  n_eq : h.n = l.n
  uSup_eq : h.uSup = l.uSup
  uCheck_eq : h.dij.u = l.uCheckInit
  uSub_eq : 0 < h.n → h.uSub p.τ = l.uSub p.τ
  L_eq : h.dij.L.v = dijkstraKey (anbHeapOp p.Γ (l.uSub p.τ)) h.dij.u
  M_eq : h.M.v = anbKeyM p.ε h.uTilde h.uSup
  S_eq : h.S.v = anbKeyS h.uTilde
  Sc_eq : h.Sc.v = anbKeySc h.uTilde h.uSup
  top_imp : ∀ x, h.uTilde x = none → h.dij.u x = ⊤
  below : ∀ x (r : ℝ), h.uTilde x = some r → x ∉ h.bandPrev → r < ((h.n : ℝ) - 1) * p.τ →
    h.dij.u x = r
  zero : h.n = 0 → (∀ x, h.uTilde x = none) ∧ h.bandPrev = ∅ ∧ (∀ x, h.dij.u x = ⊤) ∧
    (∀ x, l.uSub p.τ x = 0) ∧ ∀ x, l.uSup x = ⊤
  countSub_eq : h.countSub = l.countSub
  countSup_eq : h.countSup = l.countSup
  count_eq : h.dij.count = l.countHat

variable {𝒱 : X → Set X} {h : AnbHeapState X}

/-- Dijkstra's method with the list `L` yields the `ǔ` of the ANB with a placeholder, and the
keys of `L` are then correct and `≥ T`. -/
theorem dij_facts (hst : Global.Ext.HasStencil 𝒱 (Global.monotoneExtension p.Γ))
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x)) (hrel : HRel p h l)
    (hrelA : Rel p.τ a l) (hinit : anbHatOp p.Γ a.uSub (a.n * p.τ) a.uHatInit ≤ a.uHatInit) :
    (anbHeapStepData p 𝒱 h).dij.u = (anbLazyStepData p l).uCheck ∧
    (anbHeapStepData p 𝒱 h).dij.count =
      h.dij.count + (anbLazyStepData p l).checkRun.count ∧
    (anbHeapStepData p 𝒱 h).dij.L.v =
      dijkstraKey (anbHeapOp p.Γ (l.uSub p.τ)) (anbHeapStepData p 𝒱 h).dij.u ∧
    ∀ y v, (anbHeapStepData p 𝒱 h).dij.L.v y = some v → ((l.n * p.τ : ℝ) : WithTop ℝ) ≤ v := by
  obtain ⟨-, -, hfix⟩ := lazy_facts hΓmono hΓcaus hrelA hinit
  set T : ℝ := l.n * p.τ with hT
  have hTh : (h.n : ℝ) * p.τ = T := by rw [hrel.n_eq]
  have hD : (anbHeapStepData p 𝒱 h).dij =
      dijkstraHeapLoop (anbHeapOp p.Γ (h.uSub p.τ)) 𝒱 ((h.n * p.τ : ℝ) : WithTop ℝ) h.dij := rfl
  have hrun : (anbLazyStepData p l).checkRun =
      dijkstraRun (anbCheckOp p.Γ (l.uSub p.τ) T) l.uCheckInit (Nat.card X) := rfl
  have hcheck : (anbLazyStepData p l).uCheck = (anbLazyStepData p l).checkRun.u := rfl
  rcases Nat.eq_zero_or_pos h.n with h0 | hpos
  · obtain ⟨-, -, hu0, hl0, -⟩ := hrel.zero h0
    have hT0 : T = 0 := by rw [← hTh, h0]; simp
    -- nothing is active: all the values of `max {0, Γ}` are `≥ 0 = T`
    have hnoact : ∀ y, ¬anbCheckOp p.Γ (l.uSub p.τ) T (fun _ => ⊤) y < ⊤ := fun y => by
      unfold anbCheckOp
      rw [cutoffLt_of_le (by rw [hl0 y, hT0]; exact le_max_left _ _)]
      exact lt_irrefl _
    have hutop : h.dij.u = fun _ => ⊤ := funext hu0
    have hstopped : h.dij.Stopped ((h.n * p.τ : ℝ) : WithTop ℝ) := by
      rw [DijkstraHeapProof.stopped_iff _ _ hrel.L_eq, hTh, dijkstraCutOp_anbHeapOp, hutop]
      exact hnoact
    have hloop := DijkstraHeapProof.loop_of_stopped (Γ := anbHeapOp p.Γ (h.uSub p.τ)) (𝒱 := 𝒱)
      _ _ hstopped
    have hlrun : (anbLazyStepData p l).checkRun = dijkstraInit fun _ => ⊤ := by
      rw [hrun, ← hrel.uCheck_eq, hutop]
      exact DijkstraHeapProof.dijkstraRun_stay_of_le _ _ (m := 0) hnoact (Nat.zero_le _)
    rw [hD, hloop, hcheck, hlrun]
    refine ⟨hutop, by simp [dijkstraInit], hrel.L_eq, fun y v hv => ?_⟩
    rw [hrel.L_eq] at hv
    unfold dijkstraKey at hv
    split_ifs at hv
    rw [← Option.some_injective _ hv, hT0, ← hl0 y]
    exact le_max_left _ _
  · have hG : anbHeapOp p.Γ (h.uSub p.τ) = anbHeapOp p.Γ (l.uSub p.τ) := by
      rw [hrel.uSub_eq hpos]
    have hstG := hasStencil_anbHeapOp hst (l.uSub p.τ)
    have hN : ∀ y, ¬dijkstraCutOp (T : WithTop ℝ) (anbHeapOp p.Γ (l.uSub p.τ))
        (dijkstraRun (dijkstraCutOp (T : WithTop ℝ) (anbHeapOp p.Γ (l.uSub p.τ))) h.dij.u
          (Nat.card X)).u y <
        (dijkstraRun (dijkstraCutOp (T : WithTop ℝ) (anbHeapOp p.Γ (l.uSub p.τ))) h.dij.u
          (Nat.card X)).u y := by
      rw [dijkstraCutOp_anbHeapOp, hrel.uCheck_eq, ← hrun, ← hcheck, hfix]
      exact fun y => lt_irrefl _
    obtain ⟨-, -, hu, hc, hLv, -, -⟩ :=
      DijkstraHeapProof.loop_spec hstG (T : WithTop ℝ) h.dij hrel.L_eq (Nat.card X) hN
    rw [dijkstraCutOp_anbHeapOp, hrel.uCheck_eq, ← hrun] at hu hc
    -- the keys of `L` after the loop are `≥ T` (Prop. prop:Dijkstra_correct, frozen)
    have hsup : dijkstraCutOp (T : WithTop ℝ) (anbHeapOp p.Γ (l.uSub p.τ)) h.dij.u ≤ h.dij.u := by
      rw [dijkstraCutOp_anbHeapOp, hrel.uCheck_eq]
      exact lazy_check_sup hΓmono hΓcaus hrelA hinit
    obtain ⟨-, -, -, -, hkeys, -, -, -⟩ := DijkstraHeapCorrectProof.loop_correct hstG
      (monotone_anbHeapOp _ _) (causal_anbHeapOp hΓmono hΓcaus _) (T : WithTop ℝ) h.dij
      hrel.L_eq hsup
    rw [hD, hG, hTh]
    exact ⟨hu.trans hcheck.symm, hc, hLv, hkeys⟩

theorem hd_uTildeInit (x : X) : (anbHeapStepData p 𝒱 h).uTildeInit x =
    if x ∈ (anbHeapStepData p 𝒱 h).updated then
      (if (anbHeapStepData p 𝒱 h).dij.u x = ⊤ ∧ h.uSub p.τ x < h.n * p.τ then none
        else some (max (h.uSub p.τ x) (min (h.n * p.τ) (((anbHeapStepData p 𝒱 h).dij.u x).untopD
          (h.n * p.τ)))))
    else h.uTilde x := rfl

theorem mem_updated (x : X) : x ∈ (anbHeapStepData p 𝒱 h).updated ↔
    x ∈ h.bandPrev ∨ (anbHeapStepData p 𝒱 h).dij.count x ≠ h.dij.count x ∨
      x ∈ (h.S.entriesIco (((h.n : ℝ) - 1) * p.τ) (h.n * p.τ)).1 := by
  classical
  change x ∈ h.bandPrev ∪ Finset.univ.filter (fun y => (anbHeapStepData p 𝒱 h).dij.count y ≠
    h.dij.count y) ∪ (h.S.entriesIco (((h.n : ℝ) - 1) * p.τ) (h.n * p.τ)).1 ↔ _
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, or_assoc]

theorem ld_uTildeInit (x : X) : (anbLazyStepData p l).uTildeInit x =
    if (anbLazyStepData p l).uCheck x = ⊤ ∧ l.uSub p.τ x < l.n * p.τ then none
    else some (max (l.uSub p.τ x) (min (((anbLazyStepData p l).uCheck x).untopD (l.n * p.τ))
      (l.n * p.τ))) := rfl

omit [Fintype X] [LinearOrder X] in
/-- The key `max {ū, g}` (if `< c`) does not change when `ū` becomes `max {ū, min {T, c}}`,
provided it is `≥ T` when present. -/
theorem key_step (T : ℝ) (b g c : WithTop ℝ) (hkey : max b g < c → (T : WithTop ℝ) ≤ max b g) :
    (if max b g < c then some (max b g) else none) =
      (if max (max b (min (T : WithTop ℝ) c)) g < c then
        some (max (max b (min (T : WithTop ℝ) c)) g) else none) := by
  rcases lt_or_ge c (T : WithTop ℝ) with hc | hc
  · rw [min_eq_right hc.le]
    have h1 : ¬max (max b c) g < c := not_lt.2 ((le_max_right b c).trans (le_max_left _ g))
    have h2 : ¬max b g < c := fun h => absurd ((hkey h).trans_lt (h.trans hc)) (lt_irrefl _)
    simp only [h1, h2, ↓reduceIte]
  · rw [min_eq_left hc]
    have hT : (T : WithTop ℝ) ≤ max b g := by
      by_cases h : max b g < c
      · exact hkey h
      · exact hc.trans (not_lt.1 h)
    rw [max_right_comm, max_eq_left hT]

section Step

variable (hst : Global.Ext.HasStencil 𝒱 (Global.monotoneExtension p.Γ))
  (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x)) (hτ : 0 < p.τ)
  (hrel : HRel p h l) (hrelA : Rel p.τ a l)
  (hinit : anbHatOp p.Γ a.uSub (a.n * p.τ) a.uHatInit ≤ a.uHatInit)
include hst hΓmono hΓcaus hrel hrelA hinit

/-- A point not selected by Dijkstra's method keeps its value `ǔ`. -/
theorem dij_u_of_not_count {x : X}
    (hx : (anbHeapStepData p 𝒱 h).dij.count x = h.dij.count x) :
    (anbHeapStepData p 𝒱 h).dij.u x = h.dij.u x := by
  obtain ⟨hDu, hDc, -, -⟩ := dij_facts hst hΓmono hΓcaus hrel hrelA hinit
  have hc0 : (anbLazyStepData p l).checkRun.count x = 0 := by
    have := congrFun hDc x
    simp only [Pi.add_apply] at this
    omega
  rw [hDu, hrel.uCheck_eq]
  exact dijkstraRun_u_of_count_eq_zero (causal_anbCheckOp hΓmono hΓcaus _ _) _ _ hc0

omit hst in
/-- At `n = 0`, the Dijkstra step of the ANB with a placeholder leaves `ǔ = ∞`. -/
theorem ld_uCheck_zero (h0 : h.n = 0) (x : X) : (anbLazyStepData p l).uCheck x = ⊤ := by
  obtain ⟨hc, hhat, -⟩ := lazy_facts hΓmono hΓcaus hrelA hinit
  obtain ⟨-, -, -, hl0, -⟩ := hrel.zero h0
  have hl : (l.n : ℝ) * p.τ = 0 := by rw [← hrel.n_eq, h0]; simp
  rw [hc x]
  apply cutoffLt_of_le
  rw [hhat x, hl, hl0 x]
  exact le_max_left _ _

include hτ in
/-- After line anb_lazy:olu_gets_hatu, `ũ^{⋄→T}` is that of the ANB with a placeholder, and so is
`ũ` from the first effective iteration on. -/
theorem uTildeInit_eq :
    (∀ x, ((anbHeapStepData p 𝒱 h).uTildeInit x).getD (l.n * p.τ) =
      ((anbLazyStepData p l).uTildeInit x).getD (l.n * p.τ)) ∧
    (0 < h.n → (anbHeapStepData p 𝒱 h).uTildeInit = (anbLazyStepData p l).uTildeInit) := by
  obtain ⟨hDu, -, -, -⟩ := dij_facts hst hΓmono hΓcaus hrel hrelA hinit
  set T : ℝ := l.n * p.τ with hT
  have hTh : (h.n : ℝ) * p.τ = T := by rw [hrel.n_eq]
  rcases Nat.eq_zero_or_pos h.n with h0 | hpos
  · obtain ⟨hU0, -, -, hl0, -⟩ := hrel.zero h0
    have hT0 : T = 0 := by rw [← hTh, h0]; simp
    have hc0 := ld_uCheck_zero hΓmono hΓcaus hrel hrelA hinit h0
    refine ⟨fun x => ?_, fun h' => absurd h0 h'.ne'⟩
    have hsub : h.uSub p.τ x < 0 := by
      change (h.uTilde x).getD (((h.n : ℝ) - 1) * p.τ) < _
      rw [hU0 x, h0]; simp [hτ]
    rw [hd_uTildeInit, ld_uTildeInit, hDu, hc0 x, hl0 x, hTh, hT0]
    by_cases hP : x ∈ (anbHeapStepData p 𝒱 h).updated
    · have hl : (l.n : ℝ) * p.τ = 0 := hT0
      simp [hP, hsub, hl]
    · have hl : (l.n : ℝ) * p.τ = 0 := hT0
      simp [hP, hU0 x, hl]
  · have hsub := hrel.uSub_eq hpos
    have heq : (anbHeapStepData p 𝒱 h).uTildeInit = (anbLazyStepData p l).uTildeInit := by
      funext x
      rw [hd_uTildeInit, hDu, hsub, hTh]
      by_cases hP : x ∈ (anbHeapStepData p 𝒱 h).updated
      · simp only [hP, ↓reduceIte]
        rw [ld_uTildeInit, ← hT, min_comm]
      · simp only [hP, ↓reduceIte]
        rw [ld_uTildeInit, ← hT]
        rw [mem_updated] at hP
        simp only [not_or, not_not] at hP
        obtain ⟨hB, hc, hW⟩ := hP
        have hcx : (anbLazyStepData p l).uCheck x = h.dij.u x := by
          rw [← hDu]; exact dij_u_of_not_count hst hΓmono hΓcaus hrel hrelA hinit hc
        cases hux : h.uTilde x with
        | none =>
          have hsx : l.uSub p.τ x < T := by
            rw [← hsub]
            change (h.uTilde x).getD (((h.n : ℝ) - 1) * p.τ) < T
            rw [hux, Option.getD_none, ← hTh]; linarith
          rw [hcx, hrel.top_imp x hux]
          simp [hsx]
        | some r =>
          have hsx : l.uSub p.τ x = r := by
            rw [← hsub]
            change (h.uTilde x).getD (((h.n : ℝ) - 1) * p.τ) = r
            rw [hux, Option.getD_some]
          rw [mem_entriesIco_iff' _ hrel.S_eq, hux] at hW
          simp only [Option.some.injEq, exists_eq_left', not_and, not_lt] at hW
          rw [hsx]
          rcases lt_or_ge r T with hrT | hrT
          · have hr1 : r < ((h.n : ℝ) - 1) * p.τ := by
              by_contra hge
              exact absurd (hW (not_lt.1 hge)) (not_le.2 (hTh ▸ hrT))
            rw [hcx, hrel.below x r hux hB hr1]
            simp [hrT, min_eq_left hrT.le]
          · have hle : min (((anbLazyStepData p l).uCheck x).untopD T) T ≤ r :=
              (min_le_right _ _).trans hrT
            simp only [not_lt.2 hrT, and_false, ↓reduceIte, max_eq_left hle]
    exact ⟨fun x => by rw [heq], fun _ => heq⟩

omit hst hΓmono hΓcaus hrelA hinit in
/-- The keys of `M` after line anb_lazy:olu_gets_hatu. -/
theorem M₁_v : (h.M.set (anbHeapStepData p 𝒱 h).updated
    (anbKeyM p.ε (anbHeapStepData p 𝒱 h).uTildeInit h.uSup)).v =
      anbKeyM p.ε (anbHeapStepData p 𝒱 h).uTildeInit h.uSup := by
  funext x
  rw [set_v]
  dsimp only
  split_ifs with hx
  · rfl
  · have hux : (anbHeapStepData p 𝒱 h).uTildeInit x = h.uTilde x := by
      rw [hd_uTildeInit]; simp only [hx, ↓reduceIte]
    rw [hrel.M_eq]; simp only [anbKeyM, hux]

omit hst hΓmono hΓcaus hrelA hinit in
theorem S₁_v : ((h.S.entriesIco (((h.n : ℝ) - 1) * p.τ) (h.n * p.τ)).2.set
    (anbHeapStepData p 𝒱 h).updated (anbKeyS (anbHeapStepData p 𝒱 h).uTildeInit)).v =
      anbKeyS (anbHeapStepData p 𝒱 h).uTildeInit := by
  funext x
  rw [set_v, entriesIco_snd]
  dsimp only
  split_ifs with hx
  · rfl
  · have hux : (anbHeapStepData p 𝒱 h).uTildeInit x = h.uTilde x := by
      rw [hd_uTildeInit]; simp only [hx, ↓reduceIte]
    rw [hrel.S_eq]; simp only [anbKeyS, hux]

omit hst hΓmono hΓcaus hrelA hinit in
theorem hd_Sc_v : (anbHeapStepData p 𝒱 h).Sc.v =
    anbKeySc (anbHeapStepData p 𝒱 h).uTildeInit h.uSup := by
  funext x
  change (h.Sc.set (anbHeapStepData p 𝒱 h).updated
    (anbKeySc (anbHeapStepData p 𝒱 h).uTildeInit h.uSup)).v x = _
  rw [set_v]
  dsimp only
  split_ifs with hx
  · rfl
  · have hux : (anbHeapStepData p 𝒱 h).uTildeInit x = h.uTilde x := by
      rw [hd_uTildeInit]; simp only [hx, ↓reduceIte]
    rw [hrel.Sc_eq]; simp only [anbKeySc, hux]

omit hst hΓmono hΓcaus hrelA hinit in
theorem hd_M_v : (anbHeapStepData p 𝒱 h).M.v =
    anbKeyM p.ε (anbHeapStepData p 𝒱 h).uTildeInit h.uSup := by
  change (h.M.set (anbHeapStepData p 𝒱 h).updated
    (anbKeyM p.ε (anbHeapStepData p 𝒱 h).uTildeInit h.uSup)).bot.2.v = _
  rw [bot_snd]
  exact M₁_v hrel

omit hst hΓmono hΓcaus hrelA hinit in
theorem hd_t : (anbHeapStepData p 𝒱 h).t = anbLazyLevel p.ε (h.n * p.τ)
    (anbHeapStepData p 𝒱 h).uTildeInit h.uSup := by
  rw [← level_eq, ← M₁_v hrel]
  rfl

omit hst hΓmono hΓcaus hrelA hinit in
theorem mem_hd_band (x : X) : x ∈ (anbHeapStepData p 𝒱 h).band ↔
    (h.n * p.τ - 2 * (h.n * p.τ - (anbHeapStepData p 𝒱 h).t) ≤
      ((anbHeapStepData p 𝒱 h).uTildeInit x).getD (h.n * p.τ) ∧
    ((anbHeapStepData p 𝒱 h).uTildeInit x).getD (h.n * p.τ) < h.n * p.τ) :=
  mem_entriesIco_iff _ (S₁_v hrel) _ _ x

omit hst hΓmono hΓcaus hrelA hinit in
theorem hd_S_v : (anbHeapStepData p 𝒱 h).S.v = anbKeyS (anbHeapStepData p 𝒱 h).uTildeInit := by
  change ((((h.S.entriesIco (((h.n : ℝ) - 1) * p.τ) (h.n * p.τ)).2.set
    (anbHeapStepData p 𝒱 h).updated (anbKeyS (anbHeapStepData p 𝒱 h).uTildeInit)).entriesIco
      _ _).2).v = _
  rw [entriesIco_snd]
  exact S₁_v hrel

include hτ in
/-- The quantities of the iteration coincide with those of the ANB with a placeholder. -/
theorem data_eq :
    (fun x => ((anbHeapStepData p 𝒱 h).uTildeInit x).getD (l.n * p.τ)) =
      (anbLazyStepData p l).uHat ∧
    (anbHeapStepData p 𝒱 h).t = (anbLazyStepData p l).t ∧
    (anbHeapStepData p 𝒱 h).Δ = (anbLazyStepData p l).Δ ∧
    ((anbHeapStepData p 𝒱 h).band : Set X) = (anbLazyStepData p l).band ∧
    (anbHeapStepData p 𝒱 h).η = (anbLazyStepData p l).η ∧
    (anbHeapStepData p 𝒱 h).vSub = (anbLazyStepData p l).vSub ∧
    (anbHeapStepData p 𝒱 h).vSup = (anbLazyStepData p l).vSup := by
  have hU := (uTildeInit_eq hst hΓmono hΓcaus hτ hrel hrelA hinit).1
  have hTh : (h.n : ℝ) * p.τ = l.n * p.τ := by rw [hrel.n_eq]
  have hhat : (fun x => ((anbHeapStepData p 𝒱 h).uTildeInit x).getD (l.n * p.τ)) =
      (anbLazyStepData p l).uHat := funext hU
  have ht : (anbHeapStepData p 𝒱 h).t = (anbLazyStepData p l).t := by
    rw [hd_t hrel, lazyLevel_eq_getD, hTh, hrel.uSup_eq]
    change _ = anbLazyLevel p.ε (l.n * p.τ) (anbLazyStepData p l).uTildeInit l.uSup
    rw [lazyLevel_eq_getD]
    congr 1
  have hΔ : (anbHeapStepData p 𝒱 h).Δ = (anbLazyStepData p l).Δ := by
    change (h.n : ℝ) * p.τ - (anbHeapStepData p 𝒱 h).t = l.n * p.τ - (anbLazyStepData p l).t
    rw [hTh, ht]
  refine ⟨hhat, ht, hΔ, ?_, ?_, ?_, ?_⟩
  · ext x
    rw [Finset.mem_coe, mem_hd_band hrel, hTh, ht, hU x]
    change _ ↔ ∃ r, (anbLazyStepData p l).uTildeInit x = some r ∧
      l.n * p.τ - 2 * (l.n * p.τ - (anbLazyStepData p l).t) ≤ r ∧ r < l.n * p.τ
    rw [exists_iff_getD]
  · change (1 - p.ρ) * Real.exp (-(h.n * p.τ) / p.α) = (1 - p.ρ) * Real.exp (-(l.n * p.τ) / p.α)
    rw [hTh]
  · funext x
    change kruzkov (1 / p.α) ((((anbHeapStepData p 𝒱 h).uTildeInit x).getD
      ((h.n : ℝ) * p.τ) : ℝ) : WithTop ℝ) =
        kruzkov (1 / p.α) ((anbLazyStepData p l).uHat x : WithTop ℝ)
    rw [hTh, ← hhat]
  · funext x
    change kruzkov (1 / p.α) (h.uSup x) = kruzkov (1 / p.α) (l.uSup x)
    rw [hrel.uSup_eq]

omit hst hΓmono hΓcaus hrel hrelA hinit in
open Classical in
theorem hp_uTilde (S : AnbInnerSolver X) (x : X) : (anbHeapStepWith S p 𝒱 h).uTilde x =
    if x ∈ (anbHeapStepData p 𝒱 h).band then ((-p.α * Real.log (-(bandExtend
      ((anbHeapStepData p 𝒱 h).band : Set X) (anbHeapStepData p 𝒱 h).vSub
      (S.subResult ((anbHeapStepData p 𝒱 h).band : Set X) (anbHeapStepData p 𝒱 h).ΦSub
        (anbHeapStepData p 𝒱 h).η fun y => (anbHeapStepData p 𝒱 h).vSub y)) x) : ℝ) : WithTop ℝ)
    else (anbHeapStepData p 𝒱 h).uTildeInit x := rfl

omit hst hΓmono hΓcaus hrel hrelA hinit in
open Classical in
theorem lp_uTilde (S : AnbInnerSolver X) (x : X) : (anbLazyStepWith S p l).uTilde x =
    if x ∈ (anbLazyStepData p l).band then ((-p.α * Real.log (-(bandExtend
      (anbLazyStepData p l).band (anbLazyStepData p l).vSub
      (S.subResult (anbLazyStepData p l).band (anbLazyStepData p l).ΦSub
        (anbLazyStepData p l).η fun y => (anbLazyStepData p l).vSub y)) x) : ℝ) : WithTop ℝ)
    else (anbLazyStepData p l).uTildeInit x := rfl

omit hst hΓmono hΓcaus hrel hrelA hinit in
theorem hp_uSup (S : AnbInnerSolver X) (x : X) : (anbHeapStepWith S p 𝒱 h).uSup x =
    kruzkovInv p.α (bandExtend ((anbHeapStepData p 𝒱 h).band : Set X)
      (anbHeapStepData p 𝒱 h).vSup (S.supResult ((anbHeapStepData p 𝒱 h).band : Set X)
        (anbHeapStepData p 𝒱 h).ΦSup (anbHeapStepData p 𝒱 h).η
          fun y => (anbHeapStepData p 𝒱 h).vSup y) x) := rfl

omit hst hΓmono hΓcaus hrel hrelA hinit in
open Classical in
theorem hp_dij_u (S : AnbInnerSolver X) : (anbHeapStepWith S p 𝒱 h).dij.u =
    fun x => if x ∈ (anbHeapStepData p 𝒱 h).band then ⊤ else (anbHeapStepData p 𝒱 h).dij.u x :=
  rfl

omit hst hΓmono hΓcaus hrel hrelA hinit in
open Classical in
theorem hp_dij_L (S : AnbInnerSolver X) : (anbHeapStepWith S p 𝒱 h).dij.L =
    (anbHeapStepData p 𝒱 h).dij.L.set ((anbHeapStepData p 𝒱 h).band ∪
      (anbHeapStepData p 𝒱 h).band.biUnion (Global.Ext.revStencil 𝒱))
      (dijkstraKey (anbHeapOp p.Γ fun x => ((anbHeapStepWith S p 𝒱 h).uTilde x).getD
        (h.n * p.τ)) (anbHeapStepWith S p 𝒱 h).dij.u) := rfl

omit hst hΓmono hΓcaus hrel hrelA hinit in
theorem hp_uTilde_of_notMem (S : AnbInnerSolver X) {x : X}
    (hx : x ∉ (anbHeapStepData p 𝒱 h).band) :
    (anbHeapStepWith S p 𝒱 h).uTilde x = (anbHeapStepData p 𝒱 h).uTildeInit x := by
  rw [hp_uTilde]; simp only [hx, ↓reduceIte]

omit hst hΓmono hΓcaus hrel hrelA hinit in
theorem hp_uSup_of_notMem (S : AnbInnerSolver X) (hα : 0 < p.α) {x : X}
    (hx : x ∉ (anbHeapStepData p 𝒱 h).band) :
    (anbHeapStepWith S p 𝒱 h).uSup x = h.uSup x := by
  rw [hp_uSup, bandExtend_of_notMem _ _ _ (by simpa using hx)]
  exact kruzkovInv_kruzkov hα.ne' _

include hτ in
/-- One iteration preserves the relation. -/
theorem step_hrel (S : AnbInnerSolver X) (hα : 0 < p.α) :
    HRel p (anbHeapStepWith S p 𝒱 h) (anbLazyStepWith S p l) := by
  classical
  obtain ⟨hDu, hDc, hDL, hDkey⟩ := dij_facts hst hΓmono hΓcaus hrel hrelA hinit
  obtain ⟨hU, hU1⟩ := uTildeInit_eq hst hΓmono hΓcaus hτ hrel hrelA hinit
  obtain ⟨hhat, ht, hΔ, hB, hη, hvSub, hvSup⟩ :=
    data_eq hst hΓmono hΓcaus hτ hrel hrelA hinit
  obtain ⟨LF1, LF2, -⟩ := lazy_facts hΓmono hΓcaus hrelA hinit
  have hlhat := uHat_lazy_eq hΓmono hΓcaus hrelA hinit
  set T : ℝ := l.n * p.τ with hT
  have hTh : (h.n : ℝ) * p.τ = T := by rw [hrel.n_eq]
  have hmemB : ∀ x, x ∈ (anbHeapStepData p 𝒱 h).band ↔ x ∈ (anbLazyStepData p l).band :=
    fun x => by rw [← hB, Finset.mem_coe]
  -- the inner loops act on the same data
  have hwSub : bandExtend ((anbHeapStepData p 𝒱 h).band : Set X) (anbHeapStepData p 𝒱 h).vSub
      (S.subResult ((anbHeapStepData p 𝒱 h).band : Set X) (anbHeapStepData p 𝒱 h).ΦSub
        (anbHeapStepData p 𝒱 h).η fun y => (anbHeapStepData p 𝒱 h).vSub y) =
      bandExtend (anbLazyStepData p l).band (anbLazyStepData p l).vSub
      (S.subResult (anbLazyStepData p l).band (anbLazyStepData p l).ΦSub
        (anbLazyStepData p l).η fun y => (anbLazyStepData p l).vSub y) := by
    change bandExtend ((anbHeapStepData p 𝒱 h).band : Set X) (anbHeapStepData p 𝒱 h).vSub
      (S.subResult ((anbHeapStepData p 𝒱 h).band : Set X) (bandOp (Global.kruzkovOp p.α p.Λ)
        ((anbHeapStepData p 𝒱 h).band : Set X) (anbHeapStepData p 𝒱 h).vSub)
        (anbHeapStepData p 𝒱 h).η fun y => (anbHeapStepData p 𝒱 h).vSub y) =
      bandExtend (anbLazyStepData p l).band (anbLazyStepData p l).vSub
      (S.subResult (anbLazyStepData p l).band (bandOp (Global.kruzkovOp p.α p.Λ)
        (anbLazyStepData p l).band (anbLazyStepData p l).vSub)
        (anbLazyStepData p l).η fun y => (anbLazyStepData p l).vSub y)
    rw [hB, hvSub, hη]
  have hwSup : bandExtend ((anbHeapStepData p 𝒱 h).band : Set X) (anbHeapStepData p 𝒱 h).vSup
      (S.supResult ((anbHeapStepData p 𝒱 h).band : Set X) (anbHeapStepData p 𝒱 h).ΦSup
        (anbHeapStepData p 𝒱 h).η fun y => (anbHeapStepData p 𝒱 h).vSup y) =
      bandExtend (anbLazyStepData p l).band (anbLazyStepData p l).vSup
      (S.supResult (anbLazyStepData p l).band (anbLazyStepData p l).ΦSup
        (anbLazyStepData p l).η fun y => (anbLazyStepData p l).vSup y) := by
    change bandExtend ((anbHeapStepData p 𝒱 h).band : Set X) (anbHeapStepData p 𝒱 h).vSup
      (S.supResult ((anbHeapStepData p 𝒱 h).band : Set X) (bandOp (Global.kruzkovOp p.α p.Λ)
        ((anbHeapStepData p 𝒱 h).band : Set X) (anbHeapStepData p 𝒱 h).vSup)
        (anbHeapStepData p 𝒱 h).η fun y => (anbHeapStepData p 𝒱 h).vSup y) =
      bandExtend (anbLazyStepData p l).band (anbLazyStepData p l).vSup
      (S.supResult (anbLazyStepData p l).band (bandOp (Global.kruzkovOp p.α p.Λ)
        (anbLazyStepData p l).band (anbLazyStepData p l).vSup)
        (anbLazyStepData p l).η fun y => (anbLazyStepData p l).vSup y)
    rw [hB, hvSup, hη]
  -- the next `ū`
  have hsub' : (fun x => ((anbHeapStepWith S p 𝒱 h).uTilde x).getD (h.n * p.τ)) =
      (anbLazyStepWith S p l).uSub p.τ := funext fun x => by
    have hn1 : ((((l.n + 1 : ℕ) : ℝ)) - 1) * p.τ = T := by push_cast; ring
    change _ = ((anbLazyStepWith S p l).uTilde x).getD (((((l.n + 1 : ℕ) : ℝ)) - 1) * p.τ)
    rw [hn1, hTh, hp_uTilde, lp_uTilde, hwSub]
    by_cases hx : x ∈ (anbHeapStepData p 𝒱 h).band
    · simp only [hx, (hmemB x).1 hx, ↓reduceIte]
    · simp only [hx, mt (hmemB x).2 hx, ↓reduceIte]
      exact hU x
  have hn1h : ((((h.n + 1 : ℕ) : ℝ)) - 1) * p.τ = h.n * p.τ := by push_cast; ring
  have hsubh : (anbHeapStepWith S p 𝒱 h).uSub p.τ = (anbLazyStepWith S p l).uSub p.τ := by
    rw [← hsub']
    funext x
    change ((anbHeapStepWith S p 𝒱 h).uTilde x).getD (((((h.n + 1 : ℕ) : ℝ)) - 1) * p.τ) = _
    rw [hn1h]
  -- a point not updated by Dijkstra's method
  have hnotsel : ∀ x, (anbHeapStepData p 𝒱 h).dij.count x = h.dij.count x →
      (anbHeapStepData p 𝒱 h).dij.u x = h.dij.u x :=
    fun x hx => dij_u_of_not_count hst hΓmono hΓcaus hrel hrelA hinit hx
  refine ⟨?_, ?_, ?_, fun _ => hsubh, ?_, ?_, ?_, ?_, ?_, ?_, fun h0 => absurd h0 (by
    change h.n + 1 ≠ 0; omega), ?_, ?_, ?_⟩
  · change h.n + 1 = l.n + 1
    rw [hrel.n_eq]
  · funext x
    rw [hp_uSup, hwSup]
    rfl
  · -- `ǔ` is reset on the band
    funext x
    rw [hp_dij_u]
    change _ = cutoffLt (T - 2 * (anbLazyStepData p l).Δ) ((anbLazyStepData p l).uCheck x)
    have hmem : x ∈ (anbHeapStepData p 𝒱 h).band ↔ (T - 2 * (anbLazyStepData p l).Δ ≤
        (anbStepData p a).uHat x ∧ (anbStepData p a).uHat x < T) := by
      rw [hmemB, ← hlhat]
      change (∃ r, (anbLazyStepData p l).uTildeInit x = some r ∧
        T - 2 * (T - (anbLazyStepData p l).t) ≤ r ∧ r < T) ↔ _
      rw [exists_iff_getD]
      rfl
    dsimp only
    rw [hDu, LF1 x]
    by_cases hx : x ∈ (anbHeapStepData p 𝒱 h).band
    · obtain ⟨h1, h2⟩ := hmem.1 hx
      simp only [hx, ↓reduceIte]
      rw [cutoffLt_of_lt (WithTop.coe_lt_coe.2 h2)]
      exact (cutoffLt_of_le (WithTop.coe_le_coe.2 h1)).symm
    · simp only [hx, ↓reduceIte]
      rcases lt_or_ge ((anbStepData p a).uHat x) T with h2 | h2
      · have h1 : (anbStepData p a).uHat x < T - 2 * (anbLazyStepData p l).Δ :=
          not_le.1 fun h1 => hx (hmem.2 ⟨h1, h2⟩)
        rw [cutoffLt_of_lt (WithTop.coe_lt_coe.2 h2), cutoffLt_of_lt (WithTop.coe_lt_coe.2 h1)]
      · rw [cutoffLt_of_le (WithTop.coe_le_coe.2 h2), cutoffLt_of_le le_top]
  · -- the keys of `L`
    funext y
    rw [hp_dij_L, set_v, hsub']
    dsimp only
    split_ifs with hyR
    · rfl
    · simp only [Finset.mem_union, Finset.mem_biUnion, not_or, not_exists, not_and] at hyR
      obtain ⟨hyB, hyS⟩ := hyR
      have hu' : ∀ z, z ∉ (anbHeapStepData p 𝒱 h).band →
          (anbHeapStepWith S p 𝒱 h).dij.u z = (anbHeapStepData p 𝒱 h).dij.u z := fun z hz => by
        rw [hp_dij_u]; simp only [hz, ↓reduceIte]
      have hg : Global.monotoneExtension p.Γ (anbHeapStepWith S p 𝒱 h).dij.u y =
          Global.monotoneExtension p.Γ (anbHeapStepData p 𝒱 h).dij.u y :=
        hst y _ _ fun z hz => hu' z fun hzB => hyS z hzB (DijkstraHeapProof.mem_revStencil.2 hz)
      have hsy : (anbLazyStepWith S p l).uSub p.τ y = (anbStepData p a).uHat y := by
        rw [← hsub', ← hlhat]
        dsimp only
        rw [hp_uTilde_of_notMem S hyB, hTh]
        exact hU y
      rw [hDL]
      unfold dijkstraKey anbHeapOp
      rw [hu' y hyB, hg, hsy, LF2 y, hDu]
      exact key_step T _ _ _ fun hact => by
        exact hDkey y _ (by
          rw [hDL, hDu]; unfold dijkstraKey anbHeapOp; simp only [hact, ↓reduceIte])
  · -- `M`
    funext x
    change ((anbHeapStepData p 𝒱 h).M.set (anbHeapStepData p 𝒱 h).band
      (anbKeyM p.ε (anbHeapStepWith S p 𝒱 h).uTilde (anbHeapStepWith S p 𝒱 h).uSup)).v x = _
    rw [set_v]
    dsimp only
    split_ifs with hx
    · rfl
    · rw [hd_M_v hrel]
      simp only [anbKeyM, hp_uTilde_of_notMem S hx, hp_uSup_of_notMem S hα hx]
  · -- `S`
    funext x
    change ((anbHeapStepData p 𝒱 h).S.set (anbHeapStepData p 𝒱 h).band
      (anbKeyS (anbHeapStepWith S p 𝒱 h).uTilde)).v x = _
    rw [set_v]
    dsimp only
    split_ifs with hx
    · rfl
    · rw [hd_S_v hrel]
      simp only [anbKeyS, hp_uTilde_of_notMem S hx]
  · -- `Sc`
    funext x
    change ((anbHeapStepData p 𝒱 h).Sc.set (anbHeapStepData p 𝒱 h).band
      (anbKeySc (anbHeapStepWith S p 𝒱 h).uTilde (anbHeapStepWith S p 𝒱 h).uSup)).v x = _
    rw [set_v]
    dsimp only
    split_ifs with hx
    · rfl
    · rw [hd_Sc_v hrel]
      simp only [anbKeySc, hp_uTilde_of_notMem S hx, hp_uSup_of_notMem S hα hx]
  · -- `ǔ = ∞` at the placeholders
    intro x hx
    have hxB : x ∉ (anbHeapStepData p 𝒱 h).band := fun hxB => by
      rw [hp_uTilde] at hx; simp only [hxB, ↓reduceIte] at hx; exact Option.some_ne_none _ hx
    rw [hp_uTilde_of_notMem S hxB, hd_uTildeInit] at hx
    rw [hp_dij_u]
    simp only [hxB, ↓reduceIte]
    split_ifs at hx with hP hc
    · exact hc.1
    · rw [mem_updated] at hP
      simp only [not_or, not_not] at hP
      rw [hnotsel x hP.2.1]
      exact hrel.top_imp x hx
  · -- `ǔ = ũ` at the real values below `(n-1)τ` outside the band
    intro x r hx hxB hr
    change x ∉ (anbHeapStepData p 𝒱 h).band at hxB
    have hrT : r < T := by
      rw [← hTh, ← hn1h]
      exact hr
    rw [hp_uTilde_of_notMem S hxB, hd_uTildeInit] at hx
    rw [hp_dij_u]
    simp only [hxB, ↓reduceIte]
    split_ifs at hx with hP hc
    · -- updated point: `ǔ` is real, and equals `ũ`
      have hD := hDu ▸ congrFun (rfl : (anbHeapStepData p 𝒱 h).dij.u =
        (anbHeapStepData p 𝒱 h).dij.u) x
      rw [hTh] at hx
      induction hDx : (anbHeapStepData p 𝒱 h).dij.u x using WithTop.recTopCoe with
      | top =>
        rw [hDx, WithTop.untopD_top, min_self, Option.some.injEq] at hx
        exact absurd (hx ▸ le_max_right _ _) (not_le.2 hrT)
      | coe c =>
        have hpos : 0 < h.n := by
          rcases Nat.eq_zero_or_pos h.n with h0 | h0
          · have := ld_uCheck_zero hΓmono hΓcaus hrel hrelA hinit h0 x
            rw [← hDu, hDx] at this
            exact absurd this WithTop.coe_ne_top
          · exact h0
        have hcx : ((anbStepData p a).uHat x : WithTop ℝ) < T ∧
            (c : WithTop ℝ) = (anbStepData p a).uHat x := by
          have h1 := LF1 x
          rw [← hDu, hDx] at h1
          rcases lt_or_ge ((anbStepData p a).uHat x : WithTop ℝ) (T : WithTop ℝ) with h2 | h2
          · rw [cutoffLt_of_lt h2] at h1; exact ⟨h2, h1⟩
          · rw [cutoffLt_of_le h2] at h1; exact absurd h1 WithTop.coe_ne_top
        have hcT : c < T := by
          have := hcx.1; rw [← hcx.2] at this; exact WithTop.coe_lt_coe.1 this
        have hsc : l.uSub p.τ x ≤ c := by
          have h2 := LF2 x
          rw [← hDu, hDx, ← hcx.2, min_eq_right (WithTop.coe_le_coe.2 hcT.le)] at h2
          exact WithTop.coe_le_coe.1 (h2 ▸ le_max_left _ _)
        rw [hDx, WithTop.untopD_coe, min_eq_right hcT.le, hrel.uSub_eq hpos,
          max_eq_right hsc, Option.some.injEq] at hx
        rw [hx]
    · rw [mem_updated] at hP
      simp only [not_or, not_not] at hP
      obtain ⟨hB0, hc, hW⟩ := hP
      rw [mem_entriesIco_iff' _ hrel.S_eq, hx] at hW
      simp only [Option.some.injEq, exists_eq_left', not_and, not_lt] at hW
      have hr1 : r < ((h.n : ℝ) - 1) * p.τ := by
        by_contra hge
        exact absurd (hW (not_lt.1 hge)) (not_le.2 (hTh ▸ hrT))
      rw [hnotsel x hc]
      exact hrel.below x r hx hB0 hr1
  · funext x
    change h.countSub x + (if x ∈ (anbHeapStepData p 𝒱 h).band then S.subCount
      ((anbHeapStepData p 𝒱 h).band : Set X) (bandOp (Global.kruzkovOp p.α p.Λ)
        ((anbHeapStepData p 𝒱 h).band : Set X) (anbHeapStepData p 𝒱 h).vSub)
        (anbHeapStepData p 𝒱 h).η (fun y => (anbHeapStepData p 𝒱 h).vSub y) x else 0) =
      l.countSub x + (if x ∈ (anbLazyStepData p l).band then S.subCount
        (anbLazyStepData p l).band (bandOp (Global.kruzkovOp p.α p.Λ)
          (anbLazyStepData p l).band (anbLazyStepData p l).vSub)
        (anbLazyStepData p l).η (fun y => (anbLazyStepData p l).vSub y) x else 0)
    rw [hrel.countSub_eq]
    by_cases hx : x ∈ (anbHeapStepData p 𝒱 h).band
    · simp only [hx, (hmemB x).1 hx, ↓reduceIte]
      rw [hB, hvSub, hη]
    · simp only [hx, mt (hmemB x).2 hx, ↓reduceIte]
  · funext x
    change h.countSup x + (if x ∈ (anbHeapStepData p 𝒱 h).band then S.supCount
      ((anbHeapStepData p 𝒱 h).band : Set X) (bandOp (Global.kruzkovOp p.α p.Λ)
        ((anbHeapStepData p 𝒱 h).band : Set X) (anbHeapStepData p 𝒱 h).vSup)
        (anbHeapStepData p 𝒱 h).η (fun y => (anbHeapStepData p 𝒱 h).vSup y) x else 0) =
      l.countSup x + (if x ∈ (anbLazyStepData p l).band then S.supCount
        (anbLazyStepData p l).band (bandOp (Global.kruzkovOp p.α p.Λ)
          (anbLazyStepData p l).band (anbLazyStepData p l).vSup)
        (anbLazyStepData p l).η (fun y => (anbLazyStepData p l).vSup y) x else 0)
    rw [hrel.countSup_eq]
    by_cases hx : x ∈ (anbHeapStepData p 𝒱 h).band
    · simp only [hx, (hmemB x).1 hx, ↓reduceIte]
      rw [hB, hvSup, hη]
    · simp only [hx, mt (hmemB x).2 hx, ↓reduceIte]
  · change (anbHeapStepData p 𝒱 h).dij.count = l.countHat + (anbLazyStepData p l).checkRun.count
    rw [hDc, hrel.count_eq]

end Step

/-! ### The runs -/

section Run

variable (S : AnbInnerSolver X) {p : AnbParams X} {𝒱 : X → Set X}

theorem hrel_init (p : AnbParams X) : HRel p (anbHeapInit p.Γ : AnbHeapState X) anbLazyInit := by
  classical
  refine ⟨rfl, rfl, rfl, fun h => absurd h (lt_irrefl 0), ?_, ?_, ?_, ?_, fun _ _ => rfl,
    fun x r h => absurd h.symm WithTop.coe_ne_top, fun _ => ⟨fun _ => rfl, rfl, fun _ => rfl,
      fun x => by simp [AnbLazyState.uSub, anbLazyInit], fun _ => rfl⟩, rfl, rfl, rfl⟩
  · funext x
    have h0 : anbLazyInit.uSub p.τ = (0 : X → ℝ) := by
      funext y; simp [AnbLazyState.uSub, anbLazyInit]
    rw [h0]
    change (if x ∈ Finset.univ then _ else none) = _
    simp only [Finset.mem_univ, ↓reduceIte]
    rfl
  · funext x; simp [anbHeapInit, anbKeyM]
  · funext x; simp [anbHeapInit, anbKeyS]
  · funext x
    change (if x ∈ Finset.univ then _ else none) = _
    simp only [Finset.mem_univ, ↓reduceIte]
    rfl

theorem heapRun_succ (p : AnbParams X) (𝒱 : X → Set X) (k : ℕ) :
    anbHeapRunWith S p 𝒱 (k + 1) = anbHeapStepWith S p 𝒱 (anbHeapRunWith S p 𝒱 k) :=
  Function.iterate_succ_apply' _ _ _

theorem hrel_run (hst : Global.Ext.HasStencil 𝒱 (Global.monotoneExtension p.Γ))
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x)) (hα : 0 < p.α)
    (hτ : 0 < p.τ) (k : ℕ) : HRel p (anbHeapRunWith S p 𝒱 k) (anbLazyRunWith S p k) := by
  induction k with
  | zero => exact hrel_init p
  | succ k ih =>
    rw [heapRun_succ, lazyRun_succ]
    exact step_hrel hst hΓmono hΓcaus hτ ih (rel_run S hΓmono hΓcaus hα hτ.le k)
      (guess_run (S := S) hΓmono hΓcaus hα hτ.le k) S hα

omit [Fintype X] [LinearOrder X] in
theorem uSub_le_iff {h : AnbHeapState X} {p : AnbParams X} (c : WithTop ℝ) (x : X) :
    ((∀ r : ℝ, h.uTilde x = some r → c ≤ (((1 + p.ε) * r : ℝ) : WithTop ℝ)) ∧
      (h.uTilde x = none → c ≤ (((1 + p.ε) * (((h.n : ℝ) - 1) * p.τ) : ℝ) : WithTop ℝ))) ↔
      c ≤ (((1 + p.ε) * h.uSub p.τ x : ℝ) : WithTop ℝ) := by
  unfold AnbHeapState.uSub
  cases h.uTilde x with
  | none => simp
  | some r => simp

/-- The stopping test with the lists `M` and `Sc` is `(1 + ε) ū ≥ u̲~`. -/
theorem heapDone_iff {h : AnbHeapState X} {l : AnbLazyState X} (hrel : HRel p h l) :
    anbHeapDone p h ↔ ∀ x, h.uSup x ≤ (((1 + p.ε) * h.uSub p.τ x : ℝ) : WithTop ℝ) := by
  unfold anbHeapDone
  rw [hrel.M_eq, hrel.Sc_eq, sc_iff]
  simp only [anbKeyM_eq_none]
  constructor
  · rintro ⟨h1, h2⟩ x
    exact (uSub_le_iff _ x).1 ⟨h1 x, h2 x⟩
  · intro h
    exact ⟨fun x => ((uSub_le_iff _ x).2 (h x)).1, fun x => ((uSub_le_iff _ x).2 (h x)).2⟩

theorem done_iff {h : AnbHeapState X} {l : AnbLazyState X} (hrel : HRel p h l) :
    anbHeapDone p h ↔ anbLazyDone p l := by
  rw [heapDone_iff hrel]
  unfold anbLazyDone
  rcases Nat.eq_zero_or_pos h.n with h0 | hpos
  · obtain ⟨hU0, -, -, hl0, hs0⟩ := hrel.zero h0
    rw [hrel.uSup_eq]
    simp only [hs0, top_le_iff, WithTop.coe_ne_top]
  · rw [hrel.uSup_eq, hrel.uSub_eq hpos]

theorem heapRun_n (p : AnbParams X) (𝒱 : X → Set X) (k : ℕ) :
    (anbHeapRunWith S p 𝒱 k).n = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [heapRun_succ]
    exact congrArg (· + 1) ih

/-- The ANB with sorted lists is equivalent to the ANB with a placeholder. -/
theorem equiv (hst : Global.Ext.HasStencil 𝒱 (Global.monotoneExtension p.Γ))
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x)) (hα : 0 < p.α)
    (hτ : 0 < p.τ) :
    (∀ k : ℕ,
      (anbHeapRunWith S p 𝒱 k).uSup = (anbLazyRunWith S p k).uSup ∧
      (0 < k → (anbHeapRunWith S p 𝒱 k).uSub p.τ = (anbLazyRunWith S p k).uSub p.τ) ∧
      (anbHeapRunWith S p 𝒱 k).dij.u = (anbLazyRunWith S p k).uCheckInit ∧
      (anbHeapRunDataWith S p 𝒱 k).dij.u = (anbLazyRunDataWith S p k).uCheck ∧
      (fun x => ((anbHeapRunDataWith S p 𝒱 k).uTildeInit x).getD (k * p.τ)) =
        (anbLazyRunDataWith S p k).uHat ∧
      (0 < k → (anbHeapRunDataWith S p 𝒱 k).uTildeInit = (anbLazyRunDataWith S p k).uTildeInit) ∧
      (anbHeapRunDataWith S p 𝒱 k).t = (anbLazyRunDataWith S p k).t ∧
      (anbHeapRunDataWith S p 𝒱 k).Δ = (anbLazyRunDataWith S p k).Δ ∧
      ((anbHeapRunDataWith S p 𝒱 k).band : Set X) = (anbLazyRunDataWith S p k).band ∧
      (anbHeapRunDataWith S p 𝒱 k).η = (anbLazyRunDataWith S p k).η ∧
      (anbHeapRunWith S p 𝒱 k).countSub = (anbLazyRunWith S p k).countSub ∧
      (anbHeapRunWith S p 𝒱 k).countSup = (anbLazyRunWith S p k).countSup ∧
      (anbHeapRunWith S p 𝒱 k).dij.count = (anbLazyRunWith S p k).countHat ∧
      (anbHeapRunWith S p 𝒱 k).dij.L.v = dijkstraKey
        (anbHeapOp p.Γ ((anbLazyRunWith S p k).uSub p.τ)) (anbHeapRunWith S p 𝒱 k).dij.u ∧
      (anbHeapRunWith S p 𝒱 k).M.v =
        anbKeyM p.ε (anbHeapRunWith S p 𝒱 k).uTilde (anbHeapRunWith S p 𝒱 k).uSup ∧
      (anbHeapRunWith S p 𝒱 k).S.v = anbKeyS (anbHeapRunWith S p 𝒱 k).uTilde ∧
      (anbHeapRunWith S p 𝒱 k).Sc.v =
        anbKeySc (anbHeapRunWith S p 𝒱 k).uTilde (anbHeapRunWith S p 𝒱 k).uSup) ∧
    anbHeapStopIndexWith S p 𝒱 = anbLazyStopIndexWith S p := by
  classical
  refine ⟨fun k => ?_, ?_⟩
  · have hrel := hrel_run S hst hΓmono hΓcaus hα hτ k
    have hrelA := rel_run S hΓmono hΓcaus hα hτ.le k
    have hinit := guess_run (S := S) hΓmono hΓcaus hα hτ.le k
    have hn : ((anbLazyRunWith S p k).n : ℝ) * p.τ = k * p.τ := by
      rw [hrelA.n_eq, anbRun_n]
    have hk : (anbHeapRunWith S p 𝒱 k).n = k := heapRun_n S p 𝒱 k
    obtain ⟨hDu, -, -, -⟩ := dij_facts hst hΓmono hΓcaus hrel hrelA hinit
    obtain ⟨-, hU1⟩ := uTildeInit_eq hst hΓmono hΓcaus hτ hrel hrelA hinit
    obtain ⟨hhat, ht, hΔ, hB, hη, -, -⟩ := data_eq hst hΓmono hΓcaus hτ hrel hrelA hinit
    rw [hn] at hhat
    exact ⟨hrel.uSup_eq, fun hk0 => hrel.uSub_eq (by rw [hk]; exact hk0), hrel.uCheck_eq, hDu, hhat,
      fun hk0 => hU1 (by rw [hk]; exact hk0), ht, hΔ, hB, hη, hrel.countSub_eq, hrel.countSup_eq,
      hrel.count_eq, hrel.L_eq, hrel.M_eq, hrel.S_eq, hrel.Sc_eq⟩
  · have hiff : ∀ k, anbHeapDone p (anbHeapRunWith S p 𝒱 k) ↔
        anbLazyDone p (anbLazyRunWith S p k) :=
      fun k => done_iff (hrel_run S hst hΓmono hΓcaus hα hτ k)
    unfold anbHeapStopIndexWith anbLazyStopIndexWith
    by_cases h : ∃ k, anbLazyDone p (anbLazyRunWith S p k)
    · have h' : ∃ k, anbHeapDone p (anbHeapRunWith S p 𝒱 k) :=
        let ⟨k, hk⟩ := h; ⟨k, (hiff k).2 hk⟩
      simp only [h, h', ↓reduceDIte, Nat.cast_inj]
      exact le_antisymm (Nat.find_min' h' ((hiff _).2 (Nat.find_spec h)))
        (Nat.find_min' h ((hiff _).1 (Nat.find_spec h')))
    · have h' : ¬∃ k, anbHeapDone p (anbHeapRunWith S p 𝒱 k) :=
        fun ⟨k, hk⟩ => h ⟨k, (hiff k).1 hk⟩
      simp only [h, h', ↓reduceDIte]

end Run

end GuaranteedSubsol.AnbHeapProof
