/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.AnbLazy
public import LeanHJBAutoformalisation.GuaranteedSubsol.AnbMaxWidthProof
public import LeanHJBAutoformalisation.GuaranteedSubsol.ULessTProof
public import LeanHJBAutoformalisation.GuaranteedSubsol.CausalExtProof

/-!
# The ANB with a placeholder is equivalent to the ANB: proof

Provider proof for the frozen anchor `GuaranteedSubsol.anbLazyRun_equiv`, see `ANCHORS.md`
(Papers/AnbEquivalence). By induction on the iterations, for any inner solver `S`, the states of the
two programs are related by `u̲~ = u̲`, `ũ^{⋄→(n-1)τ} = ū`, `ǔ^init = (û^init)^{<nτ}` and
`û^init = min {ǔ^init, max {ū, nτ}}`, with the same counters (`Rel`). In each iteration:
* the guess `ǔ^init = (û^init)^{<T}` is a super-solution of `max {ū, Γ}^{<T}`, by causality, and
  `û^{<T}` is a fixed point of this operator (as in Lemma lem:u_less_t); fixed points are unique
  by the comparison principle for causal operators, so Dijkstra's method yields `ǔ = û^{<T}`
  (`uCheck_eq`);
* then `(ũ^init)^{⋄→T} = û`, and `t_n`, `Δ_n`, `B_n`, `η_n` coincide (`step_data`);
* the inner loops act on the same band, with the same operators and inputs; outside the band, both
  programs keep `û` (with the placeholder `⋄ = none` for `nτ` where `û = nτ > ū`) and `u̲`;
* Dijkstra's method updates a point at most once, exactly when its value decreases below the
  guess; `û(x) < û^init(x)` iff `û(x)^{<T} < û^init(x)^{<T}`, so the counters coincide.
-/

@[expose] public section

namespace GuaranteedSubsol.AnbLazyProof

open AnbProof AnbMaxWidthProof

variable {X : Type*}

/-! ### Cutoffs -/

theorem cutoffLt_mono {T : ℝ} {a b : WithTop ℝ} (h : a ≤ b) : cutoffLt T a ≤ cutoffLt T b := by
  rcases lt_or_ge b T with hb | hb
  · rw [cutoffLt_of_lt hb, cutoffLt_of_lt (h.trans_lt hb)]
    exact h
  · rw [cutoffLt_of_le hb]
    exact le_top

/-- `max {a, b^{<T}}^{<T} = max {a, b}^{<T}`. -/
theorem cutoffLt_max_cutoffLt (T : ℝ) (a b : WithTop ℝ) :
    cutoffLt T (max a (cutoffLt T b)) = cutoffLt T (max a b) := by
  rcases lt_or_ge b T with hb | hb
  · rw [cutoffLt_of_lt hb]
  · rw [cutoffLt_of_le hb, max_eq_right le_top, cutoffLt_of_le le_top,
      cutoffLt_of_le (hb.trans (le_max_right _ _))]

/-- `max {a, min {T, b}}^{<T} = max {a, b}^{<T}`. -/
theorem cutoffLt_max_min' (T : ℝ) (a b : WithTop ℝ) :
    cutoffLt T (max a (min (T : WithTop ℝ) b)) = cutoffLt T (max a b) := by
  rcases lt_or_ge b T with hb | hb
  · rw [min_eq_right hb.le]
  · rw [min_eq_left hb, cutoffLt_of_le (le_max_right _ _),
      cutoffLt_of_le (hb.trans (le_max_right _ _))]

/-- `(a^{<T})^{≤t} = (a^{≤t})^{<T}`. -/
theorem cutoffLe_cutoffLt (t T : ℝ) (a : WithTop ℝ) :
    cutoffLe t (cutoffLt T a) = cutoffLt T (cutoffLe t a) := by
  rcases le_or_gt a t with ht | ht
  · rw [cutoffLe_of_le ht]
    rcases lt_or_ge a T with hT | hT
    · rw [cutoffLt_of_lt hT, cutoffLe_of_le ht]
    · rw [cutoffLt_of_le hT, cutoffLe_of_lt (WithTop.coe_lt_top t)]
  · rw [cutoffLe_of_lt ht, cutoffLt_of_le le_top]
    rcases lt_or_ge a T with hT | hT
    · rw [cutoffLt_of_lt hT, cutoffLe_of_lt ht]
    · rw [cutoffLt_of_le hT, cutoffLe_of_lt (WithTop.coe_lt_top t)]

/-- The cutoff of a causal operator is causal. -/
theorem causal_cutoffLt {F : (X → WithTop ℝ) → WithTop ℝ} (hF : Ext.Causal F) (T : ℝ) :
    Ext.Causal fun u => cutoffLt T (F u) := by
  rw [ExtCausalCutoffProof.causal_iff_cutoff] at hF ⊢
  intro u v t h
  rw [cutoffLe_cutoffLt, cutoffLe_cutoffLt, hF u v t h]

/-- With `T ≤ a → b ≤ a`: `a < b ↔ a^{<T} < b^{<T}`. -/
theorem lt_iff_cutoffLt_lt {T : ℝ} {a b : WithTop ℝ} (h : (T : WithTop ℝ) ≤ a → b ≤ a) :
    a < b ↔ cutoffLt T a < cutoffLt T b := by
  rcases lt_or_ge a T with ha | ha
  · rw [cutoffLt_of_lt ha]
    rcases lt_or_ge b T with hb | hb
    · rw [cutoffLt_of_lt hb]
    · rw [cutoffLt_of_le hb]
      exact ⟨fun _ => ha.trans (WithTop.coe_lt_top T), fun _ => ha.trans_le hb⟩
  · rw [cutoffLt_of_le ha]
    exact ⟨fun hab => absurd (h ha) (not_le.2 hab), fun hc => absurd hc (not_lt.2 le_top)⟩

/-! ### The Dijkstra step -/

theorem monotone_anbCheckOp (Γ : (X → ℝ) → X → ℝ) (c : X → ℝ) (T : ℝ) :
    Monotone (anbCheckOp Γ c T) := fun _ _ h _ =>
  cutoffLt_mono (max_le_max le_rfl (KruzkovProof.monotone_monotoneExtension _ h))

theorem causal_anbCheckOp [Finite X] {Γ : (X → ℝ) → X → ℝ} (hΓmono : ∀ x, Monotone (Γ · x))
    (hΓcaus : ∀ x, Causal (Γ · x)) (c : X → ℝ) (T : ℝ) (x : X) :
    Ext.Causal (anbCheckOp Γ c T · x) :=
  causal_cutoffLt (ExtCausalMixProof.causal_max (ULessTProof.causal_const _)
    ((hΓcaus x).ext (hΓmono x))) T

/-- `Γ_∞ u` and `Γ_∞ (u^{<T})` have the same cutoff at `T` (causality). -/
theorem cutoffLt_apply_cutoffLt [Finite X] {Γ : (X → ℝ) → X → ℝ}
    (hΓmono : ∀ x, Monotone (Γ · x)) (hΓcaus : ∀ x, Causal (Γ · x)) (T : ℝ)
    {u v : X → WithTop ℝ} (huv : ∀ y, cutoffLt T (u y) = cutoffLt T (v y)) (x : X) :
    cutoffLt T (Global.monotoneExtension Γ u x) = cutoffLt T (Global.monotoneExtension Γ v x) := by
  have h := (ExtCausalCutoffProof.causal_iff_cutoff _).mp ((hΓcaus x).ext (hΓmono x)) u v T huv
  rw [← ULessTProof.cutoffLt_cutoffLe, ← ULessTProof.cutoffLt_cutoffLe T
    (Global.monotoneExtension Γ v x)]
  exact congrArg (cutoffLt T) h

/-- `max {c, Γ_∞ u}^{<T} = max {c, min {T, Γ_∞ v}}^{<T}` when `u^{<T} = v^{<T}`. -/
theorem anbCheckOp_eq [Finite X] {Γ : (X → ℝ) → X → ℝ} (hΓmono : ∀ x, Monotone (Γ · x))
    (hΓcaus : ∀ x, Causal (Γ · x)) (c : X → ℝ) (T : ℝ) {u v : X → WithTop ℝ}
    (huv : ∀ y, cutoffLt T (u y) = cutoffLt T (v y)) (x : X) :
    anbCheckOp Γ c T u x = cutoffLt T (anbHatOp Γ c T v x) := by
  unfold anbCheckOp anbHatOp
  rw [cutoffLt_max_min', ← cutoffLt_max_cutoffLt, cutoffLt_apply_cutoffLt hΓmono hΓcaus T huv,
    cutoffLt_max_cutoffLt]

/-- Fixed points of a monotone causal operator on `ℝ_∞^X` are unique. -/
theorem eq_of_fixed [Finite X] {G : (X → WithTop ℝ) → X → WithTop ℝ} (hmono : Monotone G)
    (hcaus : ∀ x, Ext.Causal (G · x)) {u v : X → WithTop ℝ} (hu : G u = u) (hv : G v = v) :
    u = v := by
  have h1 : u ≤ v := CausalExtProof.le_of_causal_ext (I := Set.univ) (fun x _ _ _ h => hmono h x)
    (fun x _ => hcaus x) (fun x _ => (congrFun hu x).ge) (fun x _ => (congrFun hv x).le)
    (fun x hx => absurd (Set.mem_univ x) hx)
  have h2 : v ≤ u := CausalExtProof.le_of_causal_ext (I := Set.univ) (fun x _ _ _ h => hmono h x)
    (fun x _ => hcaus x) (fun x _ => (congrFun hv x).ge) (fun x _ => (congrFun hu x).le)
    (fun x hx => absurd (Set.mem_univ x) hx)
  exact le_antisymm h1 h2

/-! ### The level `t_n` -/

section Level

variable [Fintype X]

theorem lazyLevel_le_of_mem {ε T : ℝ} {u : X → Option ℝ} {uSup : X → WithTop ℝ} {x : X}
    (hx : u x ≠ none) (hlt : (((1 + ε) * (u x).getD T : ℝ) : WithTop ℝ) < uSup x) :
    anbLazyLevel ε T u uSup ≤ (u x).getD T := by
  classical
  have hmem : x ∈ Finset.univ.filter fun y =>
      u y ≠ none ∧ (((1 + ε) * (u y).getD T : ℝ) : WithTop ℝ) < uSup y :=
    Finset.mem_filter.2 ⟨Finset.mem_univ x, hx, hlt⟩
  unfold anbLazyLevel
  dsimp only
  split_ifs with hS
  · exact (min_le_right _ _).trans (Finset.inf'_le _ hmem)
  · exact absurd ⟨x, hmem⟩ hS

theorem le_lazyLevel {ε T c : ℝ} {u : X → Option ℝ} {uSup : X → WithTop ℝ} (hcT : c ≤ T)
    (h : ∀ x, u x ≠ none → (((1 + ε) * (u x).getD T : ℝ) : WithTop ℝ) < uSup x →
      c ≤ (u x).getD T) :
    c ≤ anbLazyLevel ε T u uSup := by
  classical
  unfold anbLazyLevel
  dsimp only
  split_ifs with hS
  · exact le_min hcT (Finset.le_inf' _ _ fun x hx =>
      h x (Finset.mem_filter.1 hx).2.1 (Finset.mem_filter.1 hx).2.2)
  · exact hcT

theorem lazyLevel_le (ε T : ℝ) (u : X → Option ℝ) (uSup : X → WithTop ℝ) :
    anbLazyLevel ε T u uSup ≤ T := by
  classical
  unfold anbLazyLevel
  dsimp only
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-- The two definitions of `t_n` agree when `u^{⋄→T} = û`, the placeholder standing for `T`. -/
theorem lazyLevel_eq {ε T : ℝ} {u : X → Option ℝ} {uSup : X → WithTop ℝ} {uHat : X → ℝ}
    (hu : ∀ x, (u x = none ∧ uHat x = T) ∨ u x = some (uHat x)) :
    anbLazyLevel ε T u uSup = anbLevel ε T uHat uSup := by
  classical
  apply le_antisymm
  · unfold anbLevel
    dsimp only
    split_ifs with hS
    · refine le_min (lazyLevel_le ε T u uSup) (Finset.le_inf' _ _ fun x hx => ?_)
      have hlt := (Finset.mem_filter.1 hx).2
      rcases hu x with ⟨_, hT⟩ | he
      · rw [hT]; exact lazyLevel_le ε T u uSup
      · have h := lazyLevel_le_of_mem (ε := ε) (T := T) (u := u) (uSup := uSup) (x := x)
          (by rw [he]; exact Option.some_ne_none _) (by rw [he, Option.getD_some]; exact hlt)
        rwa [he, Option.getD_some] at h
    · exact lazyLevel_le ε T u uSup
  · refine le_lazyLevel (anbLevel_le ε T uHat uSup) fun x hne hlt => ?_
    rcases hu x with ⟨htop, _⟩ | he
    · exact absurd htop hne
    · rw [he, Option.getD_some] at hlt ⊢
      exact anbLevel_le_of_mem hlt

end Level

/-! ### One iteration -/

variable [Fintype X] [LinearOrder X]

/-- The relation between the states of the ANB and of the ANB with a placeholder. -/
structure Rel (τ : ℝ) (s : AnbState X) (l : AnbLazyState X) : Prop where
  n_eq : l.n = s.n
  uSup_eq : l.uSup = s.uSup
  uSub_eq : l.uSub τ = s.uSub
  uCheckInit_eq : l.uCheckInit = fun x => cutoffLt (s.n * τ) (s.uHatInit x)
  uHatInit_eq : s.uHatInit = l.uHatInit τ
  countSub_eq : l.countSub = s.countSub
  countSup_eq : l.countSup = s.countSup
  countHat_eq : l.countHat = s.countHat

section Step

variable {p : AnbParams X} {s : AnbState X} {l : AnbLazyState X}

omit [Fintype X] in
/-- The fixed point of line anb:hatu: `ū ≤ û`, and `û = max {ū, T}` when `û ≥ T`. -/
theorem uHat_props {T c u u' : ℝ} (h : u = max c (min T u')) :
    c ≤ u ∧ (T ≤ u → u = max c T) := by
  refine ⟨h ▸ le_max_left _ _, fun hT => le_antisymm ?_ (max_le ?_ hT)⟩
  · rw [h]; exact max_le_max le_rfl (min_le_left _ _)
  · rw [h]; exact le_max_left _ _

/-- Dijkstra's method yields `ǔ = û^{<T}`. -/
theorem uCheck_eq (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x))
    (hrel : Rel p.τ s l)
    (hinit : anbHatOp p.Γ s.uSub (s.n * p.τ) s.uHatInit ≤ s.uHatInit) :
    (anbLazyStepData p l).uCheck =
      fun x => cutoffLt (s.n * p.τ) ((anbStepData p s).uHat x : WithTop ℝ) := by
  set T : ℝ := s.n * p.τ with hT
  have hTl : (l.n : ℝ) * p.τ = T := by rw [hrel.n_eq]
  have hG : anbCheckOp p.Γ (l.uSub p.τ) (l.n * p.τ) = anbCheckOp p.Γ s.uSub T := by
    rw [hrel.uSub_eq, hTl]
  change (dijkstraRun (anbCheckOp p.Γ (l.uSub p.τ) (l.n * p.τ)) l.uCheckInit (Nat.card X)).u = _
  rw [hG, hrel.uCheckInit_eq]
  have hmono := monotone_anbCheckOp p.Γ s.uSub T
  have hcaus := causal_anbCheckOp hΓmono hΓcaus s.uSub T
  have hg : anbCheckOp p.Γ s.uSub T (fun x => cutoffLt T (s.uHatInit x)) ≤
      fun x => cutoffLt T (s.uHatInit x) := fun x => by
    rw [anbCheckOp_eq hΓmono hΓcaus s.uSub T (fun y => ULessTProof.cutoffLt_cutoffLt T _) x]
    exact cutoffLt_mono (hinit x)
  have hfixD := dijkstraRun_card_fixed hmono hcaus hg
  have hU := uHat_eq hΓmono hΓcaus hinit
  have hfixA : anbHatOp p.Γ s.uSub T (fun x => ((anbStepData p s).uHat x : WithTop ℝ)) =
      fun x => ((anbStepData p s).uHat x : WithTop ℝ) := funext fun x => by
    change max _ (min _ (monotoneExtension (p.Γ · x) _)) = _
    rw [MonotoneExtension.coe_eq (hΓmono x), ← WithTop.coe_min, ← WithTop.coe_max]
    exact congrArg _ (hU x).2.symm
  have hc : anbCheckOp p.Γ s.uSub T (fun x => cutoffLt T ((anbStepData p s).uHat x)) =
      fun x => cutoffLt T ((anbStepData p s).uHat x) := funext fun x => by
    rw [anbCheckOp_eq hΓmono hΓcaus s.uSub T (v := fun y => ((anbStepData p s).uHat y : WithTop ℝ))
      (fun y => ULessTProof.cutoffLt_cutoffLt T _) x, congrFun hfixA x]
  exact eq_of_fixed hmono hcaus hfixD hc

omit [Fintype X] [LinearOrder X] in
theorem nτ_eq (hrel : Rel p.τ s l) :
    (l.n : ℝ) * p.τ = s.n * p.τ := by
  rw [hrel.n_eq]

section Data

variable (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x))
  (hrel : Rel p.τ s l) (hinit : anbHatOp p.Γ s.uSub (s.n * p.τ) s.uHatInit ≤ s.uHatInit)
include hΓmono hΓcaus hrel hinit

/-- `ũ^init = ⋄` where `û ≥ T > ū` (then `û = T`), and `ũ^init = û` elsewhere. -/
theorem uTildeInit_eq (x : X) :
    (anbLazyStepData p l).uTildeInit x =
      if (s.n * p.τ : ℝ) ≤ (anbStepData p s).uHat x ∧ s.uSub x < s.n * p.τ then none
      else some ((anbStepData p s).uHat x) := by
  have hc := congrFun (uCheck_eq hΓmono hΓcaus hrel hinit) x
  have hsub : l.uSub p.τ x = s.uSub x := congrFun hrel.uSub_eq x
  obtain ⟨hle, hge⟩ := uHat_props (uHat_eq hΓmono hΓcaus hinit x).2
  change (if (anbLazyStepData p l).uCheck x = ⊤ ∧ l.uSub p.τ x < l.n * p.τ then none
    else some (max (l.uSub p.τ x) (min (((anbLazyStepData p l).uCheck x).untopD (l.n * p.τ))
      (l.n * p.τ)))) = _
  rw [hc, hsub, nτ_eq hrel]
  by_cases hT : (s.n * p.τ : ℝ) ≤ (anbStepData p s).uHat x
  · rw [cutoffLt_of_le (WithTop.coe_le_coe.2 hT)]
    by_cases hlt : s.uSub x < s.n * p.τ
    · simp only [hT, hlt, and_self, ↓reduceIte]
    · simp only [hT, hlt, and_false, ↓reduceIte, WithTop.untopD_top, min_self]
      rw [← hge hT]
  · rw [cutoffLt_of_lt (WithTop.coe_lt_coe.2 (not_le.1 hT))]
    simp only [WithTop.coe_ne_top, false_and, hT, ↓reduceIte, WithTop.untopD_coe]
    rw [min_eq_left (not_le.1 hT).le, max_eq_right hle]

theorem uTildeInit_cases (x : X) :
    ((anbLazyStepData p l).uTildeInit x = none ∧ (anbStepData p s).uHat x = s.n * p.τ) ∨
      (anbLazyStepData p l).uTildeInit x = some ((anbStepData p s).uHat x) := by
  obtain ⟨-, hge⟩ := uHat_props (uHat_eq hΓmono hΓcaus hinit x).2
  rw [uTildeInit_eq hΓmono hΓcaus hrel hinit x]
  split_ifs with h
  · exact Or.inl ⟨rfl, by rw [hge h.1, max_eq_right h.2.le]⟩
  · exact Or.inr rfl

/-- `(ũ^init)^{⋄→T} = û`. -/
theorem uHat_lazy_eq : (anbLazyStepData p l).uHat = (anbStepData p s).uHat := funext fun x => by
  change ((anbLazyStepData p l).uTildeInit x).getD (l.n * p.τ) = _
  rw [nτ_eq hrel]
  rcases uTildeInit_cases hΓmono hΓcaus hrel hinit x with ⟨h, hT⟩ | h
  · rw [h, Option.getD_none, hT]
  · rw [h, Option.getD_some]

theorem t_lazy_eq : (anbLazyStepData p l).t = (anbStepData p s).t := by
  change anbLazyLevel p.ε (l.n * p.τ) (anbLazyStepData p l).uTildeInit l.uSup = _
  rw [nτ_eq hrel, hrel.uSup_eq, lazyLevel_eq (uTildeInit_cases hΓmono hΓcaus hrel hinit),
    anbStepData_t]

theorem Δ_lazy_eq : (anbLazyStepData p l).Δ = (anbStepData p s).Δ := by
  change (l.n : ℝ) * p.τ - (anbLazyStepData p l).t = _
  rw [nτ_eq hrel, t_lazy_eq hΓmono hΓcaus hrel hinit, anbStepData_Δ]

theorem band_lazy_eq : (anbLazyStepData p l).band = (anbStepData p s).band := by
  ext x
  change (∃ r, (anbLazyStepData p l).uTildeInit x = some r ∧
    l.n * p.τ - 2 * (l.n * p.τ - (anbLazyStepData p l).t) ≤ r ∧ r < l.n * p.τ) ↔ _
  rw [nτ_eq hrel, t_lazy_eq hΓmono hΓcaus hrel hinit, anbStepData_band]
  simp only [anbBand, Set.mem_ofPred_eq, anbStepData_Δ]
  rcases uTildeInit_cases hΓmono hΓcaus hrel hinit x with ⟨h, hT⟩ | h
  · rw [h, hT]
    simp
  · rw [h]
    simp

theorem vSub_lazy_eq : (anbLazyStepData p l).vSub = (anbStepData p s).vSub := funext fun x => by
  change kruzkov (1 / p.α) ((anbLazyStepData p l).uHat x : WithTop ℝ) =
    kruzkov (1 / p.α) ((anbStepData p s).uHat x : WithTop ℝ)
  rw [uHat_lazy_eq hΓmono hΓcaus hrel hinit]

end Data

omit [LinearOrder X] in
theorem η_lazy_eq [LinearOrder X] (hrel : Rel p.τ s l) :
    (anbLazyStepData p l).η = (anbStepData p s).η := by
  change (1 - p.ρ) * Real.exp (-(l.n * p.τ) / p.α) = _
  rw [nτ_eq hrel, anbStepData_η]

theorem vSup_lazy_eq (hrel : Rel p.τ s l) :
    (anbLazyStepData p l).vSup = (anbStepData p s).vSup := funext fun x => by
  change kruzkov (1 / p.α) (l.uSup x) = kruzkov (1 / p.α) (s.uSup x)
  rw [hrel.uSup_eq]

section StepRel

variable (S : AnbInnerSolver X) (hΓmono : ∀ x, Monotone (p.Γ · x))
  (hΓcaus : ∀ x, Causal (p.Γ · x)) (hrel : Rel p.τ s l)
  (hinit : anbHatOp p.Γ s.uSub (s.n * p.τ) s.uHatInit ≤ s.uHatInit)
include hΓmono hΓcaus hrel hinit

/-- The inner loop for `ū` acts on the same band, operator and input as in the ANB. -/
theorem wSub_lazy_eq :
    bandExtend (anbLazyStepData p l).band (anbLazyStepData p l).vSub
      (S.subResult (anbLazyStepData p l).band (anbLazyStepData p l).ΦSub
        (anbLazyStepData p l).η fun x => (anbLazyStepData p l).vSub x) = wSub S p s := by
  change bandExtend (anbLazyStepData p l).band (anbLazyStepData p l).vSub
      (S.subResult (anbLazyStepData p l).band
        (bandOp (Global.kruzkovOp p.α p.Λ) (anbLazyStepData p l).band (anbLazyStepData p l).vSub)
        (anbLazyStepData p l).η fun x => (anbLazyStepData p l).vSub x) =
    bandExtend (anbStepData p s).band (anbStepData p s).vSub
      (S.subResult (anbStepData p s).band
        (bandOp (Global.kruzkovOp p.α p.Λ) (anbStepData p s).band (anbStepData p s).vSub)
        (anbStepData p s).η fun x => (anbStepData p s).vSub x)
  rw [band_lazy_eq hΓmono hΓcaus hrel hinit, vSub_lazy_eq hΓmono hΓcaus hrel hinit,
    η_lazy_eq hrel]

theorem wSup_lazy_eq :
    bandExtend (anbLazyStepData p l).band (anbLazyStepData p l).vSup
      (S.supResult (anbLazyStepData p l).band (anbLazyStepData p l).ΦSup
        (anbLazyStepData p l).η fun x => (anbLazyStepData p l).vSup x) = wSup S p s := by
  change bandExtend (anbLazyStepData p l).band (anbLazyStepData p l).vSup
      (S.supResult (anbLazyStepData p l).band
        (bandOp (Global.kruzkovOp p.α p.Λ) (anbLazyStepData p l).band (anbLazyStepData p l).vSup)
        (anbLazyStepData p l).η fun x => (anbLazyStepData p l).vSup x) =
    bandExtend (anbStepData p s).band (anbStepData p s).vSup
      (S.supResult (anbStepData p s).band
        (bandOp (Global.kruzkovOp p.α p.Λ) (anbStepData p s).band (anbStepData p s).vSup)
        (anbStepData p s).η fun x => (anbStepData p s).vSup x)
  rw [band_lazy_eq hΓmono hΓcaus hrel hinit, vSup_lazy_eq hrel, η_lazy_eq hrel]

theorem subCount_lazy_eq :
    S.subCount (anbLazyStepData p l).band (anbLazyStepData p l).ΦSub (anbLazyStepData p l).η
        (fun y => (anbLazyStepData p l).vSub y) =
      S.subCount (anbStepData p s).band (anbStepData p s).ΦSub (anbStepData p s).η
        (fun y => (anbStepData p s).vSub y) := by
  change S.subCount (anbLazyStepData p l).band
      (bandOp (Global.kruzkovOp p.α p.Λ) (anbLazyStepData p l).band (anbLazyStepData p l).vSub)
      (anbLazyStepData p l).η (fun y => (anbLazyStepData p l).vSub y) =
    S.subCount (anbStepData p s).band
      (bandOp (Global.kruzkovOp p.α p.Λ) (anbStepData p s).band (anbStepData p s).vSub)
      (anbStepData p s).η (fun y => (anbStepData p s).vSub y)
  rw [band_lazy_eq hΓmono hΓcaus hrel hinit, vSub_lazy_eq hΓmono hΓcaus hrel hinit,
    η_lazy_eq hrel]

theorem supCount_lazy_eq :
    S.supCount (anbLazyStepData p l).band (anbLazyStepData p l).ΦSup (anbLazyStepData p l).η
        (fun y => (anbLazyStepData p l).vSup y) =
      S.supCount (anbStepData p s).band (anbStepData p s).ΦSup (anbStepData p s).η
        (fun y => (anbStepData p s).vSup y) := by
  change S.supCount (anbLazyStepData p l).band
      (bandOp (Global.kruzkovOp p.α p.Λ) (anbLazyStepData p l).band (anbLazyStepData p l).vSup)
      (anbLazyStepData p l).η (fun y => (anbLazyStepData p l).vSup y) =
    S.supCount (anbStepData p s).band
      (bandOp (Global.kruzkovOp p.α p.Λ) (anbStepData p s).band (anbStepData p s).vSup)
      (anbStepData p s).η (fun y => (anbStepData p s).vSup y)
  rw [band_lazy_eq hΓmono hΓcaus hrel hinit, vSup_lazy_eq hrel, η_lazy_eq hrel]

/-- Dijkstra's method updates the same points in the two programs. -/
theorem hatCount_lazy_eq (x : X) :
    (anbLazyStepData p l).checkRun.count x = (anbStepData p s).hatRun.count x := by
  have hTl := nτ_eq hrel
  have hG : anbCheckOp p.Γ (l.uSub p.τ) (l.n * p.τ) = anbCheckOp p.Γ s.uSub (s.n * p.τ) := by
    rw [hrel.uSub_eq, hTl]
  have hl1 : (anbLazyStepData p l).checkRun.count x ≤ 1 := by
    change (dijkstraRun (anbCheckOp p.Γ (l.uSub p.τ) (l.n * p.τ)) l.uCheckInit
      (Nat.card X)).count x ≤ 1
    exact DijkstraProof.count_le_one (causal_anbCheckOp hΓmono hΓcaus _ _) _ _ x
  have hl : (anbLazyStepData p l).checkRun.count x = 1 ↔
      (anbLazyStepData p l).uCheck x < l.uCheckInit x := by
    change (dijkstraRun (anbCheckOp p.Γ (l.uSub p.τ) (l.n * p.τ)) l.uCheckInit
      (Nat.card X)).count x = 1 ↔ (dijkstraRun (anbCheckOp p.Γ (l.uSub p.τ) (l.n * p.τ))
        l.uCheckInit (Nat.card X)).u x < l.uCheckInit x
    exact DijkstraProof.count_eq_one_iff (causal_anbCheckOp hΓmono hΓcaus _ _) _ _ x
  have ha1 : (anbStepData p s).hatRun.count x ≤ 1 := by
    rw [anbStepData_hatRun]
    exact DijkstraProof.count_le_one (causal_anbHatOp hΓmono hΓcaus _ _) _ _ x
  have ha : (anbStepData p s).hatRun.count x = 1 ↔
      (anbStepData p s).hatRun.u x < s.uHatInit x := by
    rw [anbStepData_hatRun]
    exact DijkstraProof.count_eq_one_iff (causal_anbHatOp hΓmono hΓcaus _ _) _ _ x
  obtain ⟨-, hge⟩ := uHat_props (uHat_eq hΓmono hΓcaus hinit x).2
  have hkey : ((anbStepData p s).uHat x : WithTop ℝ) < s.uHatInit x ↔
      cutoffLt (s.n * p.τ) ((anbStepData p s).uHat x : WithTop ℝ) <
        cutoffLt (s.n * p.τ) (s.uHatInit x) := by
    refine lt_iff_cutoffLt_lt fun hT => ?_
    rw [congrFun hrel.uHatInit_eq x, hge (WithTop.coe_le_coe.1 hT)]
    change min _ _ ≤ _
    rw [congrFun hrel.uSub_eq x, hTl]
    exact min_le_right _ _
  rw [congrFun (uCheck_eq hΓmono hΓcaus hrel hinit) x, congrFun hrel.uCheckInit_eq x] at hl
  rw [(uHat_eq hΓmono hΓcaus hinit x).1] at ha
  have : (anbLazyStepData p l).checkRun.count x = 1 ↔ (anbStepData p s).hatRun.count x = 1 := by
    rw [hl, ha, hkey]
  omega

end StepRel

/-- One iteration preserves the relation. -/
theorem step_rel (S : AnbInnerSolver X) (hΓmono : ∀ x, Monotone (p.Γ · x))
    (hΓcaus : ∀ x, Causal (p.Γ · x)) (hα : 0 < p.α) (hτ : 0 ≤ p.τ) (hrel : Rel p.τ s l)
    (hinit : anbHatOp p.Γ s.uSub (s.n * p.τ) s.uHatInit ≤ s.uHatInit) :
    Rel p.τ (anbStepWith S p s) (anbLazyStepWith S p l) := by
  classical
  have hTl := nτ_eq hrel
  have hB := band_lazy_eq hΓmono hΓcaus hrel hinit
  set T : ℝ := s.n * p.τ with hT
  set T' : ℝ := ((s.n + 1 : ℕ) : ℝ) * p.τ with hT'
  have hTT' : T ≤ T' := by rw [hT, hT']; push_cast; nlinarith
  have hn' : (((l.n + 1 : ℕ) : ℝ) - 1) * p.τ = T := by rw [hT, hrel.n_eq]; push_cast; ring
  have htT : (anbStepData p s).t ≤ T := by rw [anbStepData_t]; exact anbLevel_le _ _ _ _
  have hΔ : (anbStepData p s).Δ = T - (anbStepData p s).t := anbStepData_Δ p s
  have htm : (anbStepData p s).tMinus = T - 2 * (anbStepData p s).Δ := by
    rw [AnbStepData.tMinus_def, hΔ]; ring
  have htmT : (anbStepData p s).tMinus ≤ T := by rw [htm, hΔ]; linarith
  -- the next `ū`
  have hsub : (anbLazyStepWith S p l).uSub p.τ = (anbStepWith S p s).uSub := funext fun x => by
    change ((if x ∈ (anbLazyStepData p l).band then
        some (-p.α * Real.log (-(bandExtend (anbLazyStepData p l).band (anbLazyStepData p l).vSub
          (S.subResult (anbLazyStepData p l).band (anbLazyStepData p l).ΦSub
            (anbLazyStepData p l).η fun x => (anbLazyStepData p l).vSub x)) x))
        else (anbLazyStepData p l).uTildeInit x)).getD ((((l.n + 1 : ℕ) : ℝ) - 1) * p.τ) = _
    rw [hn', wSub_lazy_eq S hΓmono hΓcaus hrel hinit]
    by_cases hx : x ∈ (anbLazyStepData p l).band
    · simp only [hx, ↓reduceIte, Option.getD_some]
      rfl
    · simp only [hx, ↓reduceIte]
      rw [(eq_of_notMem_band hα (hB ▸ hx)).1, ← uHat_lazy_eq hΓmono hΓcaus hrel hinit]
      change _ = ((anbLazyStepData p l).uTildeInit x).getD (l.n * p.τ)
      rw [hTl]
  -- the next guess
  have hguess : ∀ x, (anbStepWith S p s).uHatInit x = anbDijkstraGuess T'
      (anbStepData p s).tMinus (anbStepData p s).uHat (anbStepWith S p s).uSub x := fun x => rfl
  have hcheck : (anbLazyStepWith S p l).uCheckInit =
      fun x => cutoffLt T' ((anbStepWith S p s).uHatInit x) := funext fun x => by
    change cutoffLt (l.n * p.τ - 2 * (anbLazyStepData p l).Δ) ((anbLazyStepData p l).uCheck x) = _
    rw [hTl, Δ_lazy_eq hΓmono hΓcaus hrel hinit, congrFun (uCheck_eq hΓmono hΓcaus hrel hinit) x,
      hguess x, ← htm]
    unfold anbDijkstraGuess
    by_cases h : (anbStepData p s).uHat x < (anbStepData p s).tMinus
    · have h1 : (anbStepData p s).uHat x < T := h.trans_le htmT
      simp only [h, ↓reduceIte]
      rw [cutoffLt_of_lt (WithTop.coe_lt_coe.2 h1), cutoffLt_of_lt (WithTop.coe_lt_coe.2 h),
        cutoffLt_of_lt (WithTop.coe_lt_coe.2 (h1.trans_le hTT'))]
    · simp only [h, ↓reduceIte]
      rw [cutoffLt_of_le (WithTop.coe_le_coe.2 (le_max_right _ _))]
      apply cutoffLt_of_le
      rcases lt_or_ge ((anbStepData p s).uHat x) T with h1 | h1
      · rw [cutoffLt_of_lt (WithTop.coe_lt_coe.2 h1)]
        exact WithTop.coe_le_coe.2 (not_lt.1 h)
      · rw [cutoffLt_of_le (WithTop.coe_le_coe.2 h1)]
        exact le_top
  refine ⟨?_, ?_, hsub, ?_, ?_, ?_, ?_, ?_⟩
  · change l.n + 1 = s.n + 1
    rw [hrel.n_eq]
  · funext x
    change kruzkovInv p.α (bandExtend (anbLazyStepData p l).band (anbLazyStepData p l).vSup
      (S.supResult (anbLazyStepData p l).band (anbLazyStepData p l).ΦSup
        (anbLazyStepData p l).η fun x => (anbLazyStepData p l).vSup x) x) =
      kruzkovInv p.α (wSup S p s x)
    rw [wSup_lazy_eq S hΓmono hΓcaus hrel hinit]
  · exact hcheck
  · funext x
    change _ = min ((anbLazyStepWith S p l).uCheckInit x)
      ((max ((anbLazyStepWith S p l).uSub p.τ x) (((l.n + 1 : ℕ) : ℝ) * p.τ) : ℝ) : WithTop ℝ)
    have hn1 : ((l.n + 1 : ℕ) : ℝ) * p.τ = T' := by rw [hT', hrel.n_eq]
    rw [hcheck, hsub, hn1]
    beta_reduce
    rw [hguess x]
    unfold anbDijkstraGuess
    by_cases h : (anbStepData p s).uHat x < (anbStepData p s).tMinus
    · have h1 : (anbStepData p s).uHat x < T' := (h.trans_le htmT).trans_le hTT'
      simp only [h, ↓reduceIte]
      rw [cutoffLt_of_lt (WithTop.coe_lt_coe.2 h1), min_eq_left (WithTop.coe_le_coe.2
        (h1.le.trans (le_max_right _ _)))]
    · simp only [h, ↓reduceIte]
      rw [cutoffLt_of_le (WithTop.coe_le_coe.2 (le_max_right _ _)), min_eq_right le_top]
  · funext x
    change l.countSub x + (if x ∈ (anbLazyStepData p l).band then
      S.subCount (anbLazyStepData p l).band (anbLazyStepData p l).ΦSub (anbLazyStepData p l).η
        (fun y => (anbLazyStepData p l).vSub y) x else 0) = s.countSub x +
      (if x ∈ (anbStepData p s).band then S.subCount (anbStepData p s).band
        (anbStepData p s).ΦSub (anbStepData p s).η (fun y => (anbStepData p s).vSub y) x else 0)
    rw [subCount_lazy_eq S hΓmono hΓcaus hrel hinit, hrel.countSub_eq, hB]
  · funext x
    change l.countSup x + (if x ∈ (anbLazyStepData p l).band then
      S.supCount (anbLazyStepData p l).band (anbLazyStepData p l).ΦSup (anbLazyStepData p l).η
        (fun y => (anbLazyStepData p l).vSup y) x else 0) = s.countSup x +
      (if x ∈ (anbStepData p s).band then S.supCount (anbStepData p s).band
        (anbStepData p s).ΦSup (anbStepData p s).η (fun y => (anbStepData p s).vSup y) x else 0)
    rw [supCount_lazy_eq S hΓmono hΓcaus hrel hinit, hrel.countSup_eq, hB]
  · funext x
    change l.countHat x + (anbLazyStepData p l).checkRun.count x =
      s.countHat x + (anbStepData p s).hatRun.count x
    rw [hrel.countHat_eq, hatCount_lazy_eq hΓmono hΓcaus hrel hinit]

/-- `û = max {ū, min {T, ǔ}}`. -/
theorem uHat_of_check (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x))
    (hrel : Rel p.τ s l) (hinit : anbHatOp p.Γ s.uSub (s.n * p.τ) s.uHatInit ≤ s.uHatInit)
    (x : X) :
    ((anbStepData p s).uHat x : WithTop ℝ) =
      max (l.uSub p.τ x : WithTop ℝ)
        (min ((s.n * p.τ : ℝ) : WithTop ℝ) ((anbLazyStepData p l).uCheck x)) := by
  obtain ⟨hle, hge⟩ := uHat_props (uHat_eq hΓmono hΓcaus hinit x).2
  rw [congrFun (uCheck_eq hΓmono hΓcaus hrel hinit) x, congrFun hrel.uSub_eq x]
  rcases lt_or_ge ((anbStepData p s).uHat x) (s.n * p.τ) with h | h
  · rw [cutoffLt_of_lt (WithTop.coe_lt_coe.2 h), min_eq_right (WithTop.coe_le_coe.2 h.le),
      max_eq_right (WithTop.coe_le_coe.2 hle)]
  · rw [cutoffLt_of_le (WithTop.coe_le_coe.2 h), min_eq_left le_top, hge h, WithTop.coe_max]

end Step

/-! ### The runs -/

section Run

variable (S : AnbInnerSolver X) {p : AnbParams X}

omit [Fintype X] [LinearOrder X] in
theorem rel_init (p : AnbParams X) :
    Rel p.τ (anbInit : AnbState X) (anbLazyInit : AnbLazyState X) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · funext x
    simp [AnbLazyState.uSub, anbLazyInit, anbInit]
  · funext x
    simp [anbLazyInit, anbInit, cutoffLt]
  · funext x
    simp [AnbLazyState.uHatInit, AnbLazyState.uSub, anbLazyInit, anbInit]

theorem lazyRun_succ (p : AnbParams X) (k : ℕ) :
    anbLazyRunWith S p (k + 1) = anbLazyStepWith S p (anbLazyRunWith S p k) :=
  Function.iterate_succ_apply' _ _ _

theorem rel_run (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x))
    (hα : 0 < p.α) (hτ : 0 ≤ p.τ) (k : ℕ) :
    Rel p.τ (anbRunWith S p k) (anbLazyRunWith S p k) := by
  induction k with
  | zero => exact rel_init p
  | succ k ih =>
    rw [anbRun_succ, lazyRun_succ]
    exact step_rel S hΓmono hΓcaus hα hτ ih (guess_run (S := S) hΓmono hΓcaus hα hτ k)

omit [Fintype X] [LinearOrder X] in
theorem done_iff {s : AnbState X} {l : AnbLazyState X} (hrel : Rel p.τ s l) :
    anbLazyDone p l ↔ anbDone p s := by
  unfold anbLazyDone anbDone
  rw [hrel.uSup_eq, hrel.uSub_eq]

/-- The ANB with a placeholder is equivalent to the ANB, for any inner solver. -/
theorem equiv (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x))
    (hα : 0 < p.α) (hτ : 0 ≤ p.τ) :
    (∀ k : ℕ,
      (anbLazyRunWith S p k).uSup = (anbRunWith S p k).uSup ∧
      (anbLazyRunWith S p k).uSub p.τ = (anbRunWith S p k).uSub ∧
      (anbLazyRunWith S p k).uCheckInit =
        (fun x => cutoffLt (k * p.τ) ((anbRunWith S p k).uHatInit x)) ∧
      (anbRunWith S p k).uHatInit = (anbLazyRunWith S p k).uHatInit p.τ ∧
      (anbLazyRunDataWith S p k).uCheck =
        (fun x => cutoffLt (k * p.τ) ((anbRunDataWith S p k).uHat x : WithTop ℝ)) ∧
      (∀ x, ((anbRunDataWith S p k).uHat x : WithTop ℝ) =
        max ((anbLazyRunWith S p k).uSub p.τ x : WithTop ℝ)
          (min ((k * p.τ : ℝ) : WithTop ℝ) ((anbLazyRunDataWith S p k).uCheck x))) ∧
      (anbLazyRunDataWith S p k).uHat = (anbRunDataWith S p k).uHat ∧
      (anbLazyRunDataWith S p k).t = (anbRunDataWith S p k).t ∧
      (anbLazyRunDataWith S p k).Δ = (anbRunDataWith S p k).Δ ∧
      (anbLazyRunDataWith S p k).band = (anbRunDataWith S p k).band ∧
      (anbLazyRunDataWith S p k).η = (anbRunDataWith S p k).η ∧
      (anbLazyRunWith S p k).countSub = (anbRunWith S p k).countSub ∧
      (anbLazyRunWith S p k).countSup = (anbRunWith S p k).countSup ∧
      (anbLazyRunWith S p k).countHat = (anbRunWith S p k).countHat) ∧
    anbLazyStopIndexWith S p = anbStopIndexWith S p := by
  classical
  refine ⟨fun k => ?_, ?_⟩
  · have hrel := rel_run S hΓmono hΓcaus hα hτ k
    have hinit := guess_run (S := S) hΓmono hΓcaus hα hτ k
    have hn : ((anbRunWith S p k).n : ℝ) * p.τ = k * p.τ := by rw [anbRun_n]
    have hc := uCheck_eq hΓmono hΓcaus hrel hinit
    rw [hn] at hc hinit
    refine ⟨hrel.uSup_eq, hrel.uSub_eq, ?_, hrel.uHatInit_eq, hc, fun x => ?_,
      uHat_lazy_eq hΓmono hΓcaus hrel ?_, t_lazy_eq hΓmono hΓcaus hrel ?_,
      Δ_lazy_eq hΓmono hΓcaus hrel ?_, band_lazy_eq hΓmono hΓcaus hrel ?_, η_lazy_eq hrel,
      hrel.countSub_eq, hrel.countSup_eq, hrel.countHat_eq⟩
    · rw [hrel.uCheckInit_eq, hn]
    · have h := uHat_of_check hΓmono hΓcaus hrel (by rw [hn]; exact hinit) x
      rwa [hn] at h
    all_goals rw [hn]; exact hinit
  · have hiff : ∀ k, anbLazyDone p (anbLazyRunWith S p k) ↔ anbDone p (anbRunWith S p k) :=
      fun k => done_iff (rel_run S hΓmono hΓcaus hα hτ k)
    unfold anbLazyStopIndexWith anbStopIndexWith
    by_cases h : ∃ k, anbDone p (anbRunWith S p k)
    · have h' : ∃ k, anbLazyDone p (anbLazyRunWith S p k) :=
        let ⟨k, hk⟩ := h; ⟨k, (hiff k).2 hk⟩
      simp only [h, h', ↓reduceDIte, Nat.cast_inj]
      exact le_antisymm (Nat.find_min' h' ((hiff _).2 (Nat.find_spec h)))
        (Nat.find_min' h ((hiff _).1 (Nat.find_spec h')))
    · have h' : ¬∃ k, anbLazyDone p (anbLazyRunWith S p k) :=
        fun ⟨k, hk⟩ => h ⟨k, (hiff k).1 hk⟩
      simp only [h, h', ↓reduceDIte]

/-! ### Where the placeholder sits -/

section Placeholder

variable {p : AnbParams X} {s : AnbState X} {l : AnbLazyState X}

open Classical in
/-- After one iteration, `ũ = ⋄` exactly where `û = T` and `ū < T`, and `ũ = ū'` elsewhere. -/
theorem uTilde_step (S : AnbInnerSolver X) (hΓmono : ∀ x, Monotone (p.Γ · x))
    (hΓcaus : ∀ x, Causal (p.Γ · x)) (hα : 0 < p.α) (hrel : Rel p.τ s l)
    (hinit : anbHatOp p.Γ s.uSub (s.n * p.τ) s.uHatInit ≤ s.uHatInit) (x : X) :
    (anbLazyStepWith S p l).uTilde x =
      if (anbStepData p s).uHat x = s.n * p.τ ∧ s.uSub x < s.n * p.τ then none
      else some ((anbStepWith S p s).uSub x) := by
  obtain ⟨-, hge⟩ := uHat_props (uHat_eq hΓmono hΓcaus hinit x).2
  have hB := band_lazy_eq hΓmono hΓcaus hrel hinit
  change (if x ∈ (anbLazyStepData p l).band then
      some (-p.α * Real.log (-(bandExtend (anbLazyStepData p l).band (anbLazyStepData p l).vSub
        (S.subResult (anbLazyStepData p l).band (anbLazyStepData p l).ΦSub
          (anbLazyStepData p l).η fun x => (anbLazyStepData p l).vSub x)) x))
      else (anbLazyStepData p l).uTildeInit x) = _
  rw [wSub_lazy_eq S hΓmono hΓcaus hrel hinit]
  by_cases hx : x ∈ (anbLazyStepData p l).band
  · have hlt : (anbStepData p s).uHat x < s.n * p.τ := by
      have h := ((mem_band_iff p s x).1 (hB ▸ hx)).2
      exact h
    simp only [hx, ↓reduceIte, hlt.ne, false_and]
    rfl
  · simp only [hx, ↓reduceIte]
    rw [uTildeInit_eq hΓmono hΓcaus hrel hinit x, (eq_of_notMem_band hα (hB ▸ hx)).1]
    by_cases h : (s.n * p.τ : ℝ) ≤ (anbStepData p s).uHat x ∧ s.uSub x < s.n * p.τ
    · have he : (anbStepData p s).uHat x = s.n * p.τ := by rw [hge h.1, max_eq_right h.2.le]
      simp only [h, he, le_refl, and_self, ↓reduceIte]
    · have h' : ¬((anbStepData p s).uHat x = s.n * p.τ ∧ s.uSub x < s.n * p.τ) :=
        fun h' => h ⟨h'.1.ge, h'.2⟩
      simp only [h, h', ↓reduceIte]

end Placeholder

open Classical in
/-- The location of the placeholder: `ũ_0 = ū_0`, and `ũ_{k+1} = ⋄` exactly where `û_k = kτ`
and `ū_k < kτ`, `ũ_{k+1} = ū_{k+1}` elsewhere. -/
theorem placeholder (S : AnbInnerSolver X) {p : AnbParams X}
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x)) (hα : 0 < p.α)
    (hτ : 0 ≤ p.τ) :
    (∀ x, (anbLazyRunWith S p 0).uTilde x = some ((anbRunWith S p 0).uSub x)) ∧
      ∀ (k : ℕ) (x : X), (anbLazyRunWith S p (k + 1)).uTilde x =
        if (anbRunDataWith S p k).uHat x = k * p.τ ∧ (anbRunWith S p k).uSub x < k * p.τ then none
        else some ((anbRunWith S p (k + 1)).uSub x) := by
  refine ⟨fun x => rfl, fun k x => ?_⟩
  have hrel := rel_run S hΓmono hΓcaus hα hτ k
  have hinit := guess_run (S := S) hΓmono hΓcaus hα hτ k
  have hn : ((anbRunWith S p k).n : ℝ) * p.τ = k * p.τ := by rw [anbRun_n]
  have h := uTilde_step S hΓmono hΓcaus hα hrel hinit x
  rw [hn] at h
  rw [lazyRun_succ, anbRun_succ]
  exact h

end Run

end GuaranteedSubsol.AnbLazyProof
