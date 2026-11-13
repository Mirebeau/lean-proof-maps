/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.AnbHeapProof

/-!
# The cost of the ANB with sorted lists: proof

Provider proofs for the frozen anchors `GuaranteedSubsol.anbHeapRun_cost` and
`GuaranteedSubsol.anbHeapRun_cost_le`, see `ANCHORS.md` (Prop. prop:complexity_lazy). In iteration
`n`, with `c(x) ∈ {0, 1}` the acceptances of Dijkstra's method, `P` the points updated in line
anb_lazy:olu_gets_hatu, `W` the points of `S` in `[(n-1)τ, nτ[`, `B = B_n` and
`R = B ∪ ⋃_{x ∈ B} 𝒱̃(x)` (`step_counts`):
* `L`: `1 + ∑ₓ c(x) (2 + #𝒱̃(x)) + #R` operations (Dijkstra's method, line anb_lazy:L);
* `M`: `#P + 1 + #B`; `S`: `2 + #W + #P + 2 #B`; `Sc`: `#P + #B`;
* `Γ`: `∑ₓ c(x) #𝒱̃(x) + #R` evaluations;
with `#P ≤ #B_{n-1} + ∑ₓ c(x) + #W` and `#R ≤ ∑_{x ∈ B} (1 + #𝒱̃(x))`. A point is in `W` at most as
many times as it was in an earlier band (`credit`): after it is in `W`, it becomes a placeholder or
gets a value `< nτ` (it is then selected by Dijkstra's method), so a new real value `≥ nτ` can only
come from a later band.
-/

@[expose] public section

namespace GuaranteedSubsol.AnbHeapCostProof

open OrderedPartialMap OrderedPartialMapProof AnbProof AnbLazyProof AnbHeapProof

variable {X : Type*} [Fintype X] [LinearOrder X]
variable {p : AnbParams X} {a : AnbState X} {l : AnbLazyState X} {𝒱 : X → Set X}
  {h : AnbHeapState X}

/-- The costs of Dijkstra's method with the list `L` in one iteration. -/
theorem dij_costs (hst : Global.Ext.HasStencil 𝒱 (Global.monotoneExtension p.Γ))
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x)) (hrel : HRel p h l)
    (hrelA : Rel p.τ a l) (hinit : anbHatOp p.Γ a.uSub (a.n * p.τ) a.uHatInit ≤ a.uHatInit) :
    (anbHeapStepData p 𝒱 h).dij.L.count = h.dij.L.count + 1 +
      ∑ x, (anbLazyStepData p l).checkRun.count x * (2 + (Global.Ext.revStencil 𝒱 x).card) ∧
    (anbHeapStepData p 𝒱 h).dij.evalCount = h.dij.evalCount +
      ∑ x, (anbLazyStepData p l).checkRun.count x * (Global.Ext.revStencil 𝒱 x).card := by
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
    rw [hD, hloop, hlrun]
    simp [dijkstraInit]
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
    obtain ⟨-, -, -, -, -, he, hLc⟩ :=
      DijkstraHeapProof.loop_spec hstG (T : WithTop ℝ) h.dij hrel.L_eq (Nat.card X) hN
    rw [dijkstraCutOp_anbHeapOp, hrel.uCheck_eq, ← hrun] at he hLc
    rw [hD, hG, hTh]
    refine ⟨?_, he⟩
    rw [hLc]
    have : ∀ x, (anbLazyStepData p l).checkRun.count x * (2 + (Global.Ext.revStencil 𝒱 x).card) =
        (anbLazyStepData p l).checkRun.count x +
          (anbLazyStepData p l).checkRun.count x * (1 + (Global.Ext.revStencil 𝒱 x).card) :=
      fun x => by ring
    simp only [this, Finset.sum_add_distrib]
    omega

/-! ### The counters in one iteration -/

section Counts

variable (S : AnbInnerSolver X)

open Classical in
theorem hp_L_count : (anbHeapStepWith S p 𝒱 h).dij.L.count =
    (anbHeapStepData p 𝒱 h).dij.L.count + ((anbHeapStepData p 𝒱 h).band ∪
      (anbHeapStepData p 𝒱 h).band.biUnion (Global.Ext.revStencil 𝒱)).card := rfl

open Classical in
theorem hp_evalCount : (anbHeapStepWith S p 𝒱 h).dij.evalCount =
    (anbHeapStepData p 𝒱 h).dij.evalCount + ((anbHeapStepData p 𝒱 h).band ∪
      (anbHeapStepData p 𝒱 h).band.biUnion (Global.Ext.revStencil 𝒱)).card := rfl

theorem hp_M_count : (anbHeapStepWith S p 𝒱 h).M.count =
    h.M.count + (anbHeapStepData p 𝒱 h).updated.card + 1 + (anbHeapStepData p 𝒱 h).band.card :=
  rfl

theorem hp_S_count : (anbHeapStepWith S p 𝒱 h).S.count =
    h.S.count + 1 + (h.S.entriesIco (((h.n : ℝ) - 1) * p.τ) (h.n * p.τ)).1.card +
      (anbHeapStepData p 𝒱 h).updated.card + 1 + (anbHeapStepData p 𝒱 h).band.card +
      (anbHeapStepData p 𝒱 h).band.card := rfl

theorem hp_Sc_count : (anbHeapStepWith S p 𝒱 h).Sc.count =
    h.Sc.count + (anbHeapStepData p 𝒱 h).updated.card + (anbHeapStepData p 𝒱 h).band.card := rfl

theorem hp_count : (anbHeapStepWith S p 𝒱 h).dij.count = (anbHeapStepData p 𝒱 h).dij.count :=
  rfl

end Counts

omit [LinearOrder X] in
/-- `#(B ∪ ⋃_{x ∈ B} 𝒱̃(x)) ≤ ∑_{x ∈ B} (1 + #𝒱̃(x))`. -/
theorem card_R_le [DecidableEq X] (B : Finset X) :
    (B ∪ B.biUnion (Global.Ext.revStencil 𝒱)).card ≤
      ∑ x ∈ B, (1 + (Global.Ext.revStencil 𝒱 x).card) := by
  refine (Finset.card_union_le _ _).trans ?_
  rw [Finset.sum_add_distrib, Finset.card_eq_sum_ones B]
  exact Nat.add_le_add_left Finset.card_biUnion_le _

/-- `#P ≤ #B_{n-1} + ∑ₓ c(x) + #W`. -/
theorem card_updated_le (hst : Global.Ext.HasStencil 𝒱 (Global.monotoneExtension p.Γ))
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x)) (hrel : HRel p h l)
    (hrelA : Rel p.τ a l) (hinit : anbHatOp p.Γ a.uSub (a.n * p.τ) a.uHatInit ≤ a.uHatInit) :
    (anbHeapStepData p 𝒱 h).updated.card ≤ h.bandPrev.card +
      ∑ x, (anbLazyStepData p l).checkRun.count x +
      (h.S.entriesIco (((h.n : ℝ) - 1) * p.τ) (h.n * p.τ)).1.card := by
  classical
  obtain ⟨-, hDc, -, -⟩ := dij_facts hst hΓmono hΓcaus hrel hrelA hinit
  have hsel : (Finset.univ.filter fun x => (anbHeapStepData p 𝒱 h).dij.count x ≠
      h.dij.count x).card ≤ ∑ x, (anbLazyStepData p l).checkRun.count x := by
    rw [Finset.card_eq_sum_ones]
    refine (Finset.sum_le_sum fun x hx => ?_).trans
      (Finset.sum_le_sum_of_subset (Finset.subset_univ _))
    have hx' := (Finset.mem_filter.1 hx).2
    rw [hDc] at hx'
    simp only [Pi.add_apply, ne_eq] at hx'
    omega
  change (h.bandPrev ∪ Finset.univ.filter (fun x => (anbHeapStepData p 𝒱 h).dij.count x ≠
    h.dij.count x) ∪ (h.S.entriesIco (((h.n : ℝ) - 1) * p.τ) (h.n * p.τ)).1).card ≤ _
  refine (Finset.card_union_le _ _).trans ?_
  have := (Finset.card_union_le h.bandPrev (Finset.univ.filter fun x =>
    (anbHeapStepData p 𝒱 h).dij.count x ≠ h.dij.count x))
  omega

/-- After Dijkstra's method, a real value of `ǔ` is `< nτ`. -/
theorem dij_u_lt (hst : Global.Ext.HasStencil 𝒱 (Global.monotoneExtension p.Γ))
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x)) (hrel : HRel p h l)
    (hrelA : Rel p.τ a l) (hinit : anbHatOp p.Γ a.uSub (a.n * p.τ) a.uHatInit ≤ a.uHatInit)
    {x : X} {c : ℝ} (hc : (anbHeapStepData p 𝒱 h).dij.u x = c) : c < h.n * p.τ := by
  obtain ⟨hDu, -, -, -⟩ := dij_facts hst hΓmono hΓcaus hrel hrelA hinit
  obtain ⟨LF1, -, -⟩ := lazy_facts hΓmono hΓcaus hrelA hinit
  have h1 := LF1 x
  rw [← hDu, hc, ← hrel.n_eq] at h1
  rcases lt_or_ge ((anbStepData p a).uHat x : WithTop ℝ) ((h.n * p.τ : ℝ) : WithTop ℝ) with h2 | h2
  · rw [cutoffLt_of_lt h2] at h1
    rw [← h1] at h2
    exact WithTop.coe_lt_coe.1 h2
  · rw [cutoffLt_of_le h2] at h1
    exact absurd h1 WithTop.coe_ne_top

/-! ### The runs -/

omit [Fintype X] [LinearOrder X] in
theorem card_filter_range_succ (P : ℕ → Prop) [DecidablePred P] (K : ℕ) :
    ((Finset.range (K + 1)).filter P).card =
      ((Finset.range K).filter P).card + if P K then 1 else 0 := by
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with hK
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rw [add_zero]

omit [LinearOrder X] in
theorem sum_add_ite_mul [DecidableEq X] (b f : X → ℕ) (B : Finset X) :
    ∑ x, (b x + if x ∈ B then 1 else 0) * f x = ∑ x, b x * f x + ∑ x ∈ B, f x := by
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

omit [LinearOrder X] in
theorem sum_add_mul (b c f : X → ℕ) :
    ∑ x, (b x + c x) * f x = ∑ x, b x * f x + ∑ x, c x * f x := by
  simp only [add_mul, Finset.sum_add_distrib]

omit [LinearOrder X] in
theorem sum_add_ite [DecidableEq X] (b : X → ℕ) (B : Finset X) :
    ∑ x, (b x + if x ∈ B then 1 else 0) = ∑ x, b x + B.card := by
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.card_eq_sum_ones]

section Run

variable (S : AnbInnerSolver X)

/-- The number of iterations `k < K` in which `x` is in the band. -/
noncomputable def bandCount (p : AnbParams X) (𝒱 : X → Set X) (K : ℕ) (x : X) : ℕ :=
  ((Finset.range K).filter fun k => x ∈ (anbHeapRunDataWith S p 𝒱 k).band).card

/-- The number of iterations `k < K` in which `x` is a point of `S` in `[(k-1)τ, kτ[`. -/
noncomputable def wCount (p : AnbParams X) (𝒱 : X → Set X) (K : ℕ) (x : X) : ℕ :=
  ((Finset.range K).filter fun k => x ∈ ((anbHeapRunWith S p 𝒱 k).S.entriesIco
    ((((anbHeapRunWith S p 𝒱 k).n : ℝ) - 1) * p.τ) ((anbHeapRunWith S p 𝒱 k).n * p.τ)).1).card

/-- `x` has a real value `≥ (K-1)τ` at the start of iteration `K`. -/
def Pending (p : AnbParams X) (𝒱 : X → Set X) (K : ℕ) (x : X) : Prop :=
  ∃ r : ℝ, (anbHeapRunWith S p 𝒱 K).uTilde x = some r ∧ ((K : ℝ) - 1) * p.τ ≤ r

variable (hst : Global.Ext.HasStencil 𝒱 (Global.monotoneExtension p.Γ))
  (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x)) (hα : 0 < p.α)
  (hτ : 0 < p.τ)
include hst hΓmono hΓcaus hα hτ

open Classical in
/-- A point is in `W` at most as many times as it was in an earlier band; and one time less if it
has a pending real value `≥ (K-1)τ`. -/
theorem credit (K : ℕ) (x : X) :
    wCount S p 𝒱 K x + (if Pending S p 𝒱 K x then 1 else 0) ≤ bandCount S p 𝒱 K x := by
  induction K with
  | zero =>
    have : ¬Pending S p 𝒱 0 x := fun ⟨r, hr, _⟩ => Option.some_ne_none r hr.symm
    simp [wCount, bandCount, this]
  | succ K ih =>
    have hrel := hrel_run S hst hΓmono hΓcaus hα hτ K
    have hrelA := rel_run S hΓmono hΓcaus hα hτ.le K
    have hinit := guess_run (S := S) hΓmono hΓcaus hα hτ.le K
    have hn : (anbHeapRunWith S p 𝒱 K).n = K := heapRun_n S p 𝒱 K
    set h := anbHeapRunWith S p 𝒱 K with hh
    have hdata : anbHeapRunDataWith S p 𝒱 K = anbHeapStepData p 𝒱 h := rfl
    have hW : x ∈ (h.S.entriesIco (((h.n : ℝ) - 1) * p.τ) (h.n * p.τ)).1 ↔
        ∃ r : ℝ, h.uTilde x = some r ∧ ((h.n : ℝ) - 1) * p.τ ≤ r ∧ r < h.n * p.τ :=
      mem_entriesIco_iff' _ hrel.S_eq _ _ x
    have hb : bandCount S p 𝒱 (K + 1) x = bandCount S p 𝒱 K x +
        if x ∈ (anbHeapStepData p 𝒱 h).band then 1 else 0 := by
      unfold bandCount; rw [card_filter_range_succ, hdata]
    have hw : wCount S p 𝒱 (K + 1) x = wCount S p 𝒱 K x +
        if x ∈ (h.S.entriesIco (((h.n : ℝ) - 1) * p.τ) (h.n * p.τ)).1 then 1 else 0 := by
      unfold wCount; rw [card_filter_range_succ]
    have hpend : Pending S p 𝒱 K x ↔ ∃ r : ℝ, h.uTilde x = some r ∧ ((h.n : ℝ) - 1) * p.τ ≤ r := by
      rw [hn]; rfl
    have hpend' : Pending S p 𝒱 (K + 1) x ↔ ∃ r : ℝ, (anbHeapStepWith S p 𝒱 h).uTilde x = some r ∧
        (h.n : ℝ) * p.τ ≤ r := by
      unfold Pending
      rw [heapRun_succ, ← hh, hn]
      push_cast
      simp only [add_sub_cancel_right]
    have hTpos : ((h.n : ℝ) - 1) * p.τ ≤ h.n * p.τ := by nlinarith
    -- the value after line anb_lazy:olu_gets_hatu, outside the band
    have hout : x ∉ (anbHeapStepData p 𝒱 h).band → ∀ v : ℝ,
        (anbHeapStepData p 𝒱 h).uTildeInit x = some v → (h.n : ℝ) * p.τ ≤ v →
        ∃ r : ℝ, h.uTilde x = some r ∧ (h.n : ℝ) * p.τ ≤ r := by
      intro _ v hv hvT
      rw [hd_uTildeInit] at hv
      split_ifs at hv with hP hc
      · rw [Option.some.injEq] at hv
        have hsub : (h.n : ℝ) * p.τ ≤ h.uSub p.τ x := by
          induction hDx : (anbHeapStepData p 𝒱 h).dij.u x using WithTop.recTopCoe with
          | top =>
            rw [hDx] at hc
            exact not_lt.1 fun hlt => hc ⟨rfl, hlt⟩
          | coe c =>
            have hcT := dij_u_lt hst hΓmono hΓcaus hrel hrelA hinit hDx
            rw [hDx, WithTop.untopD_coe, min_eq_right hcT.le] at hv
            rcases le_total (h.uSub p.τ x) c with h1 | h1
            · rw [max_eq_right h1] at hv; linarith
            · rw [max_eq_left h1] at hv; linarith
        cases hux : h.uTilde x with
        | none =>
          change (h.uTilde x).getD (((h.n : ℝ) - 1) * p.τ) ≥ _ at hsub
          rw [hux, Option.getD_none] at hsub
          linarith
        | some r =>
          change (h.uTilde x).getD (((h.n : ℝ) - 1) * p.τ) ≥ _ at hsub
          rw [hux, Option.getD_some] at hsub
          exact ⟨r, rfl, hsub⟩
      · exact ⟨v, hv, hvT⟩
    by_cases hB : x ∈ (anbHeapStepData p 𝒱 h).band
    · rw [hb, hw]
      simp only [hB, ↓reduceIte]
      by_cases hxW : x ∈ (h.S.entriesIco (((h.n : ℝ) - 1) * p.τ) (h.n * p.τ)).1
      · have hp : Pending S p 𝒱 K x := by
          obtain ⟨r, hr, h1, -⟩ := hW.1 hxW
          exact hpend.2 ⟨r, hr, h1⟩
        simp only [hp, hxW, ↓reduceIte] at ih ⊢
        split_ifs <;> omega
      · simp only [hxW, ↓reduceIte]
        split_ifs at ih ⊢ <;> omega
    · rw [hb, hw]
      simp only [hB, ↓reduceIte, add_zero]
      have hmono : Pending S p 𝒱 (K + 1) x → Pending S p 𝒱 K x := by
        intro hp
        obtain ⟨v, hv, hvT⟩ := hpend'.1 hp
        rw [hp_uTilde_of_notMem S hB] at hv
        obtain ⟨r, hr, hrT⟩ := hout hB v hv hvT
        exact hpend.2 ⟨r, hr, hTpos.trans hrT⟩
      by_cases hxW : x ∈ (h.S.entriesIco (((h.n : ℝ) - 1) * p.τ) (h.n * p.τ)).1
      · obtain ⟨r, hr, h1, h2⟩ := hW.1 hxW
        have hp : Pending S p 𝒱 K x := hpend.2 ⟨r, hr, h1⟩
        have hnp : ¬Pending S p 𝒱 (K + 1) x := by
          intro hp'
          obtain ⟨v, hv, hvT⟩ := hpend'.1 hp'
          rw [hp_uTilde_of_notMem S hB] at hv
          obtain ⟨r', hr', hrT⟩ := hout hB v hv hvT
          rw [hr, Option.some.injEq] at hr'
          linarith
        simp only [hp, hnp, hxW, ↓reduceIte] at ih ⊢
        omega
      · simp only [hxW, ↓reduceIte, add_zero]
        by_cases hp' : Pending S p 𝒱 (K + 1) x
        · simp only [hp', hmono hp', ↓reduceIte] at ih ⊢
          exact ih
        · simp only [hp', ↓reduceIte, add_zero]
          split_ifs at ih <;> omega

theorem wCount_le (K : ℕ) (x : X) : wCount S p 𝒱 K x ≤ bandCount S p 𝒱 K x := by
  classical
  have := credit S hst hΓmono hΓcaus hα hτ K x
  split_ifs at this <;> omega

/-- The state and data of iteration `K`, and the costs of the iteration. -/
theorem iter_facts (K : ℕ) :
    (anbHeapRunWith S p 𝒱 (K + 1)).dij.count = (anbHeapRunWith S p 𝒱 K).dij.count +
      (anbLazyRunDataWith S p K).checkRun.count ∧
    (anbHeapRunWith S p 𝒱 (K + 1)).dij.evalCount = (anbHeapRunWith S p 𝒱 K).dij.evalCount +
      ∑ x, (anbLazyRunDataWith S p K).checkRun.count x * (Global.Ext.revStencil 𝒱 x).card +
      ((anbHeapRunDataWith S p 𝒱 K).band ∪
        (anbHeapRunDataWith S p 𝒱 K).band.biUnion (Global.Ext.revStencil 𝒱)).card ∧
    (anbHeapRunWith S p 𝒱 (K + 1)).dij.L.count + (anbHeapRunWith S p 𝒱 (K + 1)).M.count +
      (anbHeapRunWith S p 𝒱 (K + 1)).S.count + (anbHeapRunWith S p 𝒱 (K + 1)).Sc.count =
    (anbHeapRunWith S p 𝒱 K).dij.L.count + (anbHeapRunWith S p 𝒱 K).M.count +
      (anbHeapRunWith S p 𝒱 K).S.count + (anbHeapRunWith S p 𝒱 K).Sc.count + 4 +
      ∑ x, (anbLazyRunDataWith S p K).checkRun.count x * (2 + (Global.Ext.revStencil 𝒱 x).card) +
      ((anbHeapRunDataWith S p 𝒱 K).band ∪
        (anbHeapRunDataWith S p 𝒱 K).band.biUnion (Global.Ext.revStencil 𝒱)).card +
      3 * (anbHeapRunDataWith S p 𝒱 K).updated.card +
      ((anbHeapRunWith S p 𝒱 K).S.entriesIco ((((anbHeapRunWith S p 𝒱 K).n : ℝ) - 1) * p.τ)
        ((anbHeapRunWith S p 𝒱 K).n * p.τ)).1.card +
      4 * (anbHeapRunDataWith S p 𝒱 K).band.card ∧
    (anbHeapRunDataWith S p 𝒱 K).updated.card ≤ (anbHeapRunWith S p 𝒱 K).bandPrev.card +
      ∑ x, (anbLazyRunDataWith S p K).checkRun.count x +
      ((anbHeapRunWith S p 𝒱 K).S.entriesIco ((((anbHeapRunWith S p 𝒱 K).n : ℝ) - 1) * p.τ)
        ((anbHeapRunWith S p 𝒱 K).n * p.τ)).1.card ∧
    (anbHeapRunWith S p 𝒱 (K + 1)).bandPrev = (anbHeapRunDataWith S p 𝒱 K).band := by
  classical
  have hrel := hrel_run S hst hΓmono hΓcaus hα hτ K
  have hrelA := rel_run S hΓmono hΓcaus hα hτ.le K
  have hinit := guess_run (S := S) hΓmono hΓcaus hα hτ.le K
  obtain ⟨-, hDc, -, -⟩ := dij_facts hst hΓmono hΓcaus hrel hrelA hinit
  obtain ⟨hLc, he⟩ := dij_costs hst hΓmono hΓcaus hrel hrelA hinit
  have hP := card_updated_le hst hΓmono hΓcaus hrel hrelA hinit
  rw [heapRun_succ]
  refine ⟨by rw [hp_count]; exact hDc, by rw [hp_evalCount, he]; rfl, ?_, hP, rfl⟩
  rw [hp_L_count, hp_M_count, hp_S_count, hp_Sc_count, hLc]
  have hd : anbHeapStepData p 𝒱 (anbHeapRunWith S p 𝒱 K) = anbHeapRunDataWith S p 𝒱 K := rfl
  have hl : anbLazyStepData p (anbLazyRunWith S p K) = anbLazyRunDataWith S p K := rfl
  simp only [hd, hl]
  omega

theorem eval_le (K : ℕ) :
    (anbHeapRunWith S p 𝒱 K).dij.evalCount ≤ Fintype.card X +
      ∑ x, (anbHeapRunWith S p 𝒱 K).dij.count x * (Global.Ext.revStencil 𝒱 x).card +
      ∑ x, bandCount S p 𝒱 K x * (1 + (Global.Ext.revStencil 𝒱 x).card) := by
  classical
  induction K with
  | zero =>
    change Fintype.card X ≤ Fintype.card X + ∑ x, 0 * _ + ∑ x, bandCount S p 𝒱 0 x * _
    simp
  | succ K ih =>
    obtain ⟨hc, he, -, -, -⟩ := iter_facts S hst hΓmono hΓcaus hα hτ K
    have hb : ∀ x, bandCount S p 𝒱 (K + 1) x = bandCount S p 𝒱 K x +
        if x ∈ (anbHeapRunDataWith S p 𝒱 K).band then 1 else 0 := fun x => by
      unfold bandCount; rw [card_filter_range_succ]
    have hR := card_R_le (𝒱 := 𝒱) (anbHeapRunDataWith S p 𝒱 K).band
    simp only [hb, hc, Pi.add_apply]
    rw [sum_add_ite_mul, sum_add_mul]
    omega

theorem ops_le (K : ℕ) :
    (anbHeapRunWith S p 𝒱 K).dij.L.count + (anbHeapRunWith S p 𝒱 K).M.count +
      (anbHeapRunWith S p 𝒱 K).S.count + (anbHeapRunWith S p 𝒱 K).Sc.count +
      3 * (anbHeapRunWith S p 𝒱 K).bandPrev.card ≤ 2 * Fintype.card X + 4 * K +
      ∑ x, (anbHeapRunWith S p 𝒱 K).dij.count x * (5 + (Global.Ext.revStencil 𝒱 x).card) +
      ∑ x, bandCount S p 𝒱 K x * (8 + (Global.Ext.revStencil 𝒱 x).card) +
      4 * ∑ x, wCount S p 𝒱 K x := by
  classical
  induction K with
  | zero =>
    change 0 + Finset.univ.card + 0 + 0 + (0 + Finset.univ.card) + 3 * 0 ≤
      2 * Fintype.card X + 4 * 0 + ∑ x, 0 * _ + ∑ x, bandCount S p 𝒱 0 x * _ +
        4 * ∑ x, wCount S p 𝒱 0 x
    simp only [Finset.card_univ, zero_mul, Finset.sum_const_zero]
    omega
  | succ K ih =>
    obtain ⟨hc, -, hops, hP, hbp⟩ := iter_facts S hst hΓmono hΓcaus hα hτ K
    have hn : (anbHeapRunWith S p 𝒱 K).n = K := heapRun_n S p 𝒱 K
    have hb : ∀ x, bandCount S p 𝒱 (K + 1) x = bandCount S p 𝒱 K x +
        if x ∈ (anbHeapRunDataWith S p 𝒱 K).band then 1 else 0 := fun x => by
      unfold bandCount; rw [card_filter_range_succ]
    have hw : ∀ x, wCount S p 𝒱 (K + 1) x = wCount S p 𝒱 K x +
        if x ∈ ((anbHeapRunWith S p 𝒱 K).S.entriesIco
          ((((anbHeapRunWith S p 𝒱 K).n : ℝ) - 1) * p.τ)
          ((anbHeapRunWith S p 𝒱 K).n * p.τ)).1 then 1 else 0 := fun x => by
      unfold wCount; rw [card_filter_range_succ]
    have hR := card_R_le (𝒱 := 𝒱) (anbHeapRunDataWith S p 𝒱 K).band
    have hB8 : ∑ x ∈ (anbHeapRunDataWith S p 𝒱 K).band, (8 + (Global.Ext.revStencil 𝒱 x).card) =
        ∑ x ∈ (anbHeapRunDataWith S p 𝒱 K).band, (1 + (Global.Ext.revStencil 𝒱 x).card) +
          7 * (anbHeapRunDataWith S p 𝒱 K).band.card := by
      rw [Finset.card_eq_sum_ones, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    have hc5 : ∑ x, (anbLazyRunDataWith S p K).checkRun.count x *
        (5 + (Global.Ext.revStencil 𝒱 x).card) = ∑ x, (anbLazyRunDataWith S p K).checkRun.count x *
          (2 + (Global.Ext.revStencil 𝒱 x).card) +
        3 * ∑ x, (anbLazyRunDataWith S p K).checkRun.count x := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hbp]
    simp only [hb, hw, hc, Pi.add_apply]
    rw [sum_add_ite_mul, sum_add_ite, sum_add_mul]
    omega

/-- Prop. prop:complexity_lazy, cost accounting: the evaluations of `Γ` and the operations on the
lists after `K` iterations, in terms of `countB'` (the selections by Dijkstra's method) and `countB`
(the iterations in the band). -/
theorem cost (K : ℕ) :
    (anbHeapRunWith S p 𝒱 K).dij.evalCount ≤ Fintype.card X +
      ∑ x, anbHeapCountB' S p 𝒱 K x * (Global.Ext.revStencil 𝒱 x).card +
      ∑ x, anbHeapCountB S p 𝒱 K x * (1 + (Global.Ext.revStencil 𝒱 x).card) ∧
    (anbHeapRunWith S p 𝒱 K).dij.L.count + (anbHeapRunWith S p 𝒱 K).M.count +
      (anbHeapRunWith S p 𝒱 K).S.count + (anbHeapRunWith S p 𝒱 K).Sc.count ≤
      2 * Fintype.card X + 4 * K +
      ∑ x, anbHeapCountB' S p 𝒱 K x * (5 + (Global.Ext.revStencil 𝒱 x).card) +
      ∑ x, anbHeapCountB S p 𝒱 K x * (12 + (Global.Ext.revStencil 𝒱 x).card) := by
  refine ⟨eval_le S hst hΓmono hΓcaus hα hτ K, ?_⟩
  have h := ops_le S hst hΓmono hΓcaus hα hτ K
  have hw : ∑ x, wCount S p 𝒱 K x ≤ ∑ x, bandCount S p 𝒱 K x :=
    Finset.sum_le_sum fun x _ => wCount_le S hst hΓmono hΓcaus hα hτ K x
  have h12 : ∑ x, bandCount S p 𝒱 K x * (12 + (Global.Ext.revStencil 𝒱 x).card) =
      ∑ x, bandCount S p 𝒱 K x * (8 + (Global.Ext.revStencil 𝒱 x).card) +
        4 * ∑ x, bandCount S p 𝒱 K x := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  change _ ≤ _ + ∑ x, (anbHeapRunWith S p 𝒱 K).dij.count x *
    (5 + (Global.Ext.revStencil 𝒱 x).card) +
    ∑ x, bandCount S p 𝒱 K x * (12 + (Global.Ext.revStencil 𝒱 x).card)
  omega

/-- Prop. prop:complexity_lazy with uniform bounds: if `countB' ≤ N_Γ`, `countB ≤ N'_Λ`, each point
is updated at most `N_Λ` times by each of the two inner loops (in total), and the method stops
within `Kmax` iterations, then at termination there are at most `2 #X N_Λ` updates by the inner
loops, `#X + Ñ N_Γ + (#X + Ñ) N'_Λ` evaluations of `Γ`, and
`2 #X + 4 Kmax + N_Γ (5 #X + Ñ) + N'_Λ (12 #X + Ñ)` operations on the lists, with
`Ñ := ∑ₓ #𝒱̃(x)`. -/
theorem cost_le (NΓ NΛ' NΛ Kmax : ℕ) (hcountB' : ∀ K x, anbHeapCountB' S p 𝒱 K x ≤ NΓ)
    (hcountB : ∀ K x, anbHeapCountB S p 𝒱 K x ≤ NΛ')
    (hcountΛ : ∀ K x, (anbHeapRunWith S p 𝒱 K).countSub x ≤ NΛ ∧
      (anbHeapRunWith S p 𝒱 K).countSup x ≤ NΛ)
    (hstop : anbHeapStopIndexWith S p 𝒱 ≤ Kmax) :
    ∑ x, ((anbHeapRunWith S p 𝒱 (anbHeapStopIndexWith S p 𝒱).toNat).countSub x +
        (anbHeapRunWith S p 𝒱 (anbHeapStopIndexWith S p 𝒱).toNat).countSup x) ≤
      ((2 * Fintype.card X * NΛ : ℕ) : ℕ∞) ∧
    (anbHeapRunWith S p 𝒱 (anbHeapStopIndexWith S p 𝒱).toNat).dij.evalCount ≤
      Fintype.card X + (∑ x, (Global.Ext.revStencil 𝒱 x).card) * NΓ +
        (Fintype.card X + ∑ x, (Global.Ext.revStencil 𝒱 x).card) * NΛ' ∧
    (anbHeapRunWith S p 𝒱 (anbHeapStopIndexWith S p 𝒱).toNat).dij.L.count +
      (anbHeapRunWith S p 𝒱 (anbHeapStopIndexWith S p 𝒱).toNat).M.count +
      (anbHeapRunWith S p 𝒱 (anbHeapStopIndexWith S p 𝒱).toNat).S.count +
      (anbHeapRunWith S p 𝒱 (anbHeapStopIndexWith S p 𝒱).toNat).Sc.count ≤
      2 * Fintype.card X + 4 * Kmax +
        NΓ * (5 * Fintype.card X + ∑ x, (Global.Ext.revStencil 𝒱 x).card) +
        NΛ' * (12 * Fintype.card X + ∑ x, (Global.Ext.revStencil 𝒱 x).card) := by
  classical
  set K := (anbHeapStopIndexWith S p 𝒱).toNat with hK
  have hKK : K ≤ Kmax := by
    have hne : anbHeapStopIndexWith S p 𝒱 ≠ ⊤ :=
      ne_top_of_le_ne_top (ENat.natCast_ne_top Kmax) hstop
    have := ENat.natCast_toNat hne
    rw [← this] at hstop
    exact_mod_cast hstop
  obtain ⟨he, hops⟩ := cost S hst hΓmono hΓcaus hα hτ K
  have hsumN : ∀ (m : ℕ) (f : X → ℕ), ∑ x, (m + f x) = m * Fintype.card X + ∑ x, f x :=
    fun m f => by rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      mul_comm]
  have h1 : ∑ x, anbHeapCountB' S p 𝒱 K x * (Global.Ext.revStencil 𝒱 x).card ≤
      (∑ x, (Global.Ext.revStencil 𝒱 x).card) * NΓ := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun x _ => by
      rw [mul_comm]; exact Nat.mul_le_mul_left _ (hcountB' K x)
  have h2 : ∑ x, anbHeapCountB S p 𝒱 K x * (1 + (Global.Ext.revStencil 𝒱 x).card) ≤
      (Fintype.card X + ∑ x, (Global.Ext.revStencil 𝒱 x).card) * NΛ' := by
    have : Fintype.card X + ∑ x, (Global.Ext.revStencil 𝒱 x).card =
        ∑ x, (1 + (Global.Ext.revStencil 𝒱 x).card) := by rw [hsumN, one_mul]
    rw [this, Finset.sum_mul]
    exact Finset.sum_le_sum fun x _ => by
      rw [mul_comm]; exact Nat.mul_le_mul_left _ (hcountB K x)
  have h3 : ∑ x, anbHeapCountB' S p 𝒱 K x * (5 + (Global.Ext.revStencil 𝒱 x).card) ≤
      NΓ * (5 * Fintype.card X + ∑ x, (Global.Ext.revStencil 𝒱 x).card) := by
    rw [← hsumN, Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => Nat.mul_le_mul_right _ (hcountB' K x)
  have h4 : ∑ x, anbHeapCountB S p 𝒱 K x * (12 + (Global.Ext.revStencil 𝒱 x).card) ≤
      NΛ' * (12 * Fintype.card X + ∑ x, (Global.Ext.revStencil 𝒱 x).card) := by
    rw [← hsumN, Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => Nat.mul_le_mul_right _ (hcountB K x)
  refine ⟨?_, by omega, by omega⟩
  calc ∑ x, ((anbHeapRunWith S p 𝒱 K).countSub x + (anbHeapRunWith S p 𝒱 K).countSup x)
      ≤ ∑ _x : X, ((NΛ : ℕ∞) + NΛ) :=
        Finset.sum_le_sum fun x _ => add_le_add (hcountΛ K x).1 (hcountΛ K x).2
    _ = ((2 * Fintype.card X * NΛ : ℕ) : ℕ∞) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        push_cast
        ring

end Run

end GuaranteedSubsol.AnbHeapCostProof
