/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.AnbMaxWidthProof

/-!
# ANB: Corollary corol:NGamma, proofs

Provider proofs for the frozen anchors of Corollary corol:NGamma, see `ANCHORS.md`.

* `band_subset`, `dijkstraBand_subset`: the bounds of corol:Bn_comp, with `t⁻_n ≥ nτ - 2Δ_max`
  and `t⁺_n ≤ nτ + Δ⁺_max`, which uses `t_n ≤ ‖u_*‖_∞` when `E_n = {(1 + ε) û_n < u̲_n}` is
  nonempty. For `B'_n`, a point outside `E_n` is handled directly: `u_* ≤ u̲_n ≤ (1 + ε) û_n`.
* `card_band_le`, `card_dijkstraBand_le`: the integers `k` with `kτ - A ≤ u < kτ + B` are at most
  `⌈(A + B)/τ⌉` (`card_le_of_window`).
* `countHat_le`: Dijkstra's method updates each point at most once per iteration, and only at the
  points of `B'_n` (Prop. prop:Dijkstra_band).
* The proofs are written for a generic width threshold `Dm` (`WidthHyp`, with `dPlus`, `nΛ'` in
  place of `Δ⁺_max`, `N'_Λ`; suffix `_of`), so that they also serve the unknown-constants version
  (`AnbWithUnknownProof`); the versions under `Hyp` instantiate `Dm = Δ_max`.
-/

@[expose] public section

namespace GuaranteedSubsol.AnbNGammaProof

open AnbProof AnbBnCompProof AnbMaxWidthProof

variable {X : Type*}

/-- The natural numbers `k` with `kτ - A ≤ u < kτ + B` are at most `⌈(A + B) / τ⌉` many. -/
theorem card_le_of_window {S : Finset ℕ} {τ A B u : ℝ} (hτ : 0 < τ)
    (hS : ∀ k ∈ S, (k : ℝ) * τ - A ≤ u ∧ u < (k : ℝ) * τ + B) :
    S.card ≤ ⌈(A + B) / τ⌉₊ := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  set m := S.min' hne
  set M := S.max' hne
  have hm := hS m (S.min'_mem hne)
  have hM := hS M (S.max'_mem hne)
  have hmM : m ≤ M := S.min'_le M (S.max'_mem hne)
  have hlt : ((M - m : ℕ) : ℝ) < ⌈(A + B) / τ⌉₊ := by
    rw [Nat.cast_sub hmM]
    refine lt_of_lt_of_le ?_ (Nat.le_ceil _)
    rw [lt_div_iff₀ hτ, sub_mul]
    linarith [hM.1, hm.2]
  have hlt' : M - m < ⌈(A + B) / τ⌉₊ := by exact_mod_cast hlt
  have hsub : S ⊆ Finset.Icc m M := fun k hk =>
    Finset.mem_Icc.2 ⟨S.min'_le k hk, S.le_max' k hk⟩
  calc S.card ≤ (Finset.Icc m M).card := Finset.card_le_card hsub
    _ = M + 1 - m := Nat.card_Icc m M
    _ ≤ ⌈(A + B) / τ⌉₊ := by omega

variable [Fintype X] [LinearOrder X] {p : AnbParams X} {I : Set X} {ubd : X → ℝ} {CΓ CΓ' : ℝ}
  {uFix : X → ℝ} {Dm : ℝ}
  {S : AnbInnerSolver X} [S.Valid]

omit [S.Valid] in
theorem Δ_eq (S : AnbInnerSolver X) (p : AnbParams X) (k : ℕ) :
    (anbRunDataWith S p k).Δ = (k : ℝ) * p.τ - (anbRunDataWith S p k).t := by
  rw [anbRunDataWith_def, anbStepData_Δ, anbRun_n]

/-- `Δ⁺_max` for a generic width threshold `Dm` (`AnbParams.ΔplusMax` for `Dm = Δ_max`). -/
noncomputable def dPlus (p : AnbParams X) (Cpast CΓ CΓ' : ℝ) (uFix : X → ℝ) (Dm : ℝ) : ℝ :=
  (CΓ - 1) * Dm + p.ε * ‖uFix‖ + Cpast + CΓ'

/-- `N'_Λ` for a generic width threshold `Dm` (`AnbParams.NΛ'` for `Dm = Δ_max`). -/
noncomputable def nΛ' (p : AnbParams X) (Cpast CΓ CΓ' : ℝ) (uFix : X → ℝ) (Dm : ℝ) : ℕ :=
  ⌈(2 * Dm + dPlus p Cpast CΓ CΓ' uFix Dm) / p.τ⌉₊

/-! ### For a generic width threshold -/

/-- `t⁻_n ≥ nτ - 2Δ_max`. -/
theorem tMinus_ge_of (h : WidthHyp S p I ubd CΓ CΓ' uFix Dm) (k : ℕ) :
    (k : ℝ) * p.τ - 2 * Dm ≤ (anbRunDataWith S p k).tMinus := by
  rw [AnbStepData.tMinus_def]
  linarith [Δ_lt_of h k, Δ_eq S p k]

/-- `t_n ≤ ‖u_*‖_∞` when `t_n < nτ` (then `E_n ≠ ∅`). -/
theorem t_le_norm_of (h : WidthHyp S p I ubd CΓ CΓ' uFix Dm) (k : ℕ)
    (hlt : (anbRunDataWith S p k).t < (k : ℝ) * p.τ) : (anbRunDataWith S p k).t ≤ ‖uFix‖ := by
  have ht : (anbRunDataWith S p k).t =
      anbLevel p.ε ((k : ℝ) * p.τ) (anbRunDataWith S p k).uHat (anbRunWith S p k).uSup := by
    rw [anbRunDataWith_def, anbStepData_t, anbRun_n]
  obtain ⟨x1, hx1⟩ := exists_of_anbLevel_lt (ht ▸ hlt)
  have h1 : (anbRunDataWith S p k).t ≤ (anbRunDataWith S p k).uHat x1 := by
    rw [ht]; exact anbLevel_le_of_mem hx1
  linarith [h.uHat_le k x1, Hyp.le_norm uFix x1]

/-- `t⁺_n ≤ nτ + Δ⁺_max` when `t_n ≤ ‖u_*‖_∞`. -/
theorem tPlus_le_of (h : WidthHyp S p I ubd CΓ CΓ' uFix Dm) {Cpast : ℝ} (k : ℕ)
    (ht : (anbRunDataWith S p k).t ≤ ‖uFix‖) :
    (anbRunDataWith S p k).tPlus p.ε Cpast CΓ CΓ' ≤
      (k : ℝ) * p.τ + dPlus p Cpast CΓ CΓ' uFix Dm := by
  have e1 : p.ε * (anbRunDataWith S p k).t ≤ p.ε * ‖uFix‖ := mul_le_mul_of_nonneg_left ht h.hε.le
  have e2 : (CΓ - 1) * (anbRunDataWith S p k).Δ ≤ (CΓ - 1) * Dm :=
    mul_le_mul_of_nonneg_left (Δ_lt_of h k).le (by linarith [h.hCΓ])
  have e3 : (1 + p.ε) * (anbRunDataWith S p k).t + CΓ * (anbRunDataWith S p k).Δ =
      (k : ℝ) * p.τ + p.ε * (anbRunDataWith S p k).t + (CΓ - 1) * (anbRunDataWith S p k).Δ := by
    rw [Δ_eq S p k]; ring
  rw [AnbStepData.tPlus_def, dPlus]
  linarith

/-- The inclusion `B_n ⊂ {nτ - 2Δ_max ≤ u_* < nτ + Δ⁺_max}`. -/
theorem band_subset_of (h : WidthHyp S p I ubd CΓ CΓ' uFix Dm) {Cpast : ℝ} (hCpast : 0 ≤ Cpast)
    (hCΓ' : 0 ≤ CΓ') (hmem : ∀ x ∈ I, HasMemory Cpast (p.Λ · x)) (k : ℕ) {x : X}
    (hx : x ∈ (anbRunDataWith S p k).band) :
    (k : ℝ) * p.τ - 2 * Dm ≤ uFix x ∧
      uFix x < (k : ℝ) * p.τ + dPlus p Cpast CΓ CΓ' uFix Dm := by
  have bb := band_bounds h.hΛbd h.hΓbd hCpast h.hCΓ hCΓ' h.hΛmono h.hΛ0 h.hadd hmem
    h.hcmp h.hΓmono h.hΓcaus h.hΓΛ h.hcomp h.hfix h.hα h.hτ.le h.hε k hx
  have hb := (mem_band_iff p (anbRunWith S p k) x).1 hx
  rw [anbRun_n, AnbStepData.tMinus_def] at hb
  have hlt : (anbRunDataWith S p k).t < (k : ℝ) * p.τ := by
    have := Δ_eq S p k
    change (anbRunDataWith S p k).t - (anbRunDataWith S p k).Δ ≤ (anbRunDataWith S p k).uHat x ∧
      (anbRunDataWith S p k).uHat x < (k : ℝ) * p.τ at hb
    linarith [hb.1, hb.2]
  exact ⟨(tMinus_ge_of h k).trans bb.1, bb.2.trans_le (tPlus_le_of h k (t_le_norm_of h k hlt))⟩

/-- The inclusion `B'_n ⊂ {(n-1)τ - 2Δ_max ≤ u_* < nτ + Δ⁺_max}`, with `n = k + 1`. -/
theorem dijkstraBand_subset_of (h : WidthHyp S p I ubd CΓ CΓ' uFix Dm) {Cpast : ℝ}
    (hCpast : 0 ≤ Cpast) (hCΓ' : 0 ≤ CΓ') (hmem : ∀ x ∈ I, HasMemory Cpast (p.Λ · x))
    {k : ℕ} {x : X}
    (hx : x ∈ anbDijkstraBand (anbRunDataWith S p k).tMinus (((k + 1 : ℕ) : ℝ) * p.τ)
      (anbRunDataWith S p k).uHat (anbRunDataWith S p (k + 1)).uHat) :
    (k : ℝ) * p.τ - 2 * Dm ≤ uFix x ∧
      uFix x < ((k + 1 : ℕ) : ℝ) * p.τ + dPlus p Cpast CΓ CΓ' uFix Dm := by
  have bb := dijkstraBand_bounds h.hΛbd h.hΓbd hCpast h.hCΓ hCΓ' h.hΛmono h.hΛ0 h.hadd
    hmem h.hcmp h.hΓmono h.hΓcaus h.hΓΛ h.hcomp h.hfix h.hα h.hτ.le h.hε hx
  refine ⟨(tMinus_ge_of h k).trans bb.1, ?_⟩
  have hxT : (anbRunDataWith S p (k + 1)).uHat x < ((k + 1 : ℕ) : ℝ) * p.τ := hx.2
  by_cases hE : (((1 + p.ε) * (anbRunDataWith S p (k + 1)).uHat x : ℝ) : WithTop ℝ) <
      (anbRunWith S p (k + 1)).uSup x
  · -- `x ∈ E_{k+1}`, so `t_{k+1} ≤ û_{k+1}(x) < (k + 1)τ`
    have ht : (anbRunDataWith S p (k + 1)).t ≤ (anbRunDataWith S p (k + 1)).uHat x := by
      have : (anbRunDataWith S p (k + 1)).t = anbLevel p.ε (((k + 1 : ℕ) : ℝ) * p.τ)
          (anbRunDataWith S p (k + 1)).uHat (anbRunWith S p (k + 1)).uSup := by
        rw [anbRunDataWith_def, anbStepData_t, anbRun_n]
      rw [this]
      exact anbLevel_le_of_mem hE
    exact bb.2.trans_le (tPlus_le_of h (k + 1) (t_le_norm_of h (k + 1) (ht.trans_lt hxT)))
  · -- `x ∉ E_{k+1}`: `u_* ≤ u̲ ≤ (1 + ε) û < (k + 1)τ + ε ‖u_*‖_∞`
    have h1 := (uFix_le_uSup h.hΛmono h.hcomp h.hfix (h.always (k + 1)).uSup_ge x).trans
      (not_lt.1 hE)
    have h2 : uFix x ≤ (1 + p.ε) * (anbRunDataWith S p (k + 1)).uHat x := WithTop.coe_le_coe.1 h1
    have hu : (anbRunDataWith S p (k + 1)).uHat x ≤ ‖uFix‖ :=
      (h.uHat_le (k + 1) x).trans (Hyp.le_norm uFix x)
    have e1 : p.ε * (anbRunDataWith S p (k + 1)).uHat x ≤ p.ε * ‖uFix‖ :=
      mul_le_mul_of_nonneg_left hu h.hε.le
    have e2 : 0 ≤ (CΓ - 1) * Dm :=
      mul_nonneg (by linarith [h.hCΓ]) h.Dm_pos.le
    rw [dPlus]
    nlinarith

/-- `#{n | x ∈ B_n} ≤ N'_Λ`. -/
theorem card_band_le_of (h : WidthHyp S p I ubd CΓ CΓ' uFix Dm) {Cpast : ℝ} (hCpast : 0 ≤ Cpast)
    (hCΓ' : 0 ≤ CΓ') (hmem : ∀ x ∈ I, HasMemory Cpast (p.Λ · x)) (x : X) {F : Finset ℕ}
    (hS : ∀ k ∈ F, x ∈ (anbRunDataWith S p k).band) :
    F.card ≤ nΛ' p Cpast CΓ CΓ' uFix Dm :=
  card_le_of_window h.hτ fun k hk => band_subset_of h hCpast hCΓ' hmem k (hS k hk)

/-- `#{n | x ∈ B'_n} ≤ N_Γ`. -/
theorem card_dijkstraBand_le_of (h : WidthHyp S p I ubd CΓ CΓ' uFix Dm) {Cpast : ℝ}
    (hCpast : 0 ≤ Cpast) (hCΓ' : 0 ≤ CΓ') (hmem : ∀ x ∈ I, HasMemory Cpast (p.Λ · x))
    (x : X) {F : Finset ℕ}
    (hS : ∀ k ∈ F, x ∈ anbDijkstraBand (anbRunDataWith S p k).tMinus (((k + 1 : ℕ) : ℝ) * p.τ)
      (anbRunDataWith S p k).uHat (anbRunDataWith S p (k + 1)).uHat) :
    F.card ≤ (nΛ' p Cpast CΓ CΓ' uFix Dm + 1) := by
  have hwin := card_le_of_window (A := 2 * Dm)
    (B := p.τ + dPlus p Cpast CΓ CΓ' uFix Dm) (u := uFix x) h.hτ fun k hk => by
      have := dijkstraBand_subset_of h hCpast hCΓ' hmem (hS k hk)
      push_cast at this
      exact ⟨this.1, by linarith [this.2]⟩
  have hpos : 0 ≤ (2 * Dm + dPlus p Cpast CΓ CΓ' uFix Dm) / p.τ := by
    have : 0 ≤ dPlus p Cpast CΓ CΓ' uFix Dm := by
      rw [dPlus]
      have := mul_nonneg (show (0 : ℝ) ≤ CΓ - 1 by linarith [h.hCΓ]) h.Dm_pos.le
      have := mul_nonneg h.hε.le (norm_nonneg uFix)
      linarith
    exact div_nonneg (by linarith [h.Dm_pos]) h.hτ.le
  have heq : (2 * Dm + (p.τ + dPlus p Cpast CΓ CΓ' uFix Dm)) / p.τ =
      (2 * Dm + dPlus p Cpast CΓ CΓ' uFix Dm) / p.τ + 1 := by
    field_simp [h.hτ.ne']
    ring
  rw [heq, Nat.ceil_add_one hpos] at hwin
  exact hwin

/-- At most `N_Γ` updates `û(x) ← Γ û(x)` at any point, over the whole run. -/
theorem countHat_le_of (h : WidthHyp S p I ubd CΓ CΓ' uFix Dm) {Cpast : ℝ} (hCpast : 0 ≤ Cpast)
    (hCΓ' : 0 ≤ CΓ') (hmem : ∀ x ∈ I, HasMemory Cpast (p.Λ · x)) (k : ℕ) (x : X) :
    (anbRunWith S p k).countHat x ≤ (nΛ' p Cpast CΓ CΓ' uFix Dm + 1) := by
  classical
  let P : ℕ → Prop := fun i => x ∈ anbDijkstraBand (anbRunDataWith S p i).tMinus
    (((i + 1 : ℕ) : ℝ) * p.τ) (anbRunDataWith S p i).uHat (anbRunDataWith S p (i + 1)).uHat
  have key : ∀ m, (anbRunWith S p (m + 1)).countHat x ≤ ((Finset.range m).filter P).card := by
    intro m
    induction m with
    | zero =>
      have h0 := congrFun (zero_vacuous (S := S) p).2.2.2.2.2.2.2.2.2 x
      rw [h0]
      simp
    | succ m ih =>
      have hstep : (anbRunWith S p (m + 1 + 1)).countHat x =
          (anbRunWith S p (m + 1)).countHat x + (anbRunDataWith S p (m + 1)).hatRun.count x := by
        rw [anbRun_succ p (m + 1), anbStep_eq]
        rfl
      have hle1 : (anbRunDataWith S p (m + 1)).hatRun.count x ≤ 1 := by
        rw [anbRunDataWith_def, anbStepData_hatRun]
        exact DijkstraProof.count_le_one (causal_anbHatOp h.hΓmono h.hΓcaus _ _) _ _ x
      rw [hstep, Finset.range_add_one, Finset.filter_insert]
      by_cases hP : P m
      · simp only [hP, ↓reduceIte]
        rw [Finset.card_insert_of_notMem (by simp)]
        omega
      · simp only [hP, ↓reduceIte]
        have h0 : (anbRunDataWith S p (m + 1)).hatRun.count x = 0 := by
          by_contra hne
          exact hP (hatRun_count_mem (S := S) h.hΓmono h.hΓcaus h.hα h.hτ.le hne)
        omega
  rcases k with _ | m
  · change (anbInit : AnbState X).countHat x ≤ _
    simp [anbInit]
  · exact (key m).trans
      (card_dijkstraBand_le_of h hCpast hCΓ' hmem x fun i hi => (Finset.mem_filter.1 hi).2)


/-! ### The known parameters: `Φ_α` is `ρ`-sub-additive -/

/-- `t⁻_n ≥ nτ - 2Δ_max`. -/
theorem tMinus_ge (h : Hyp p I ubd CΓ CΓ' uFix) (k : ℕ) :
    (k : ℝ) * p.τ - 2 * p.Δmax ≤ (anbRunData p k).tMinus :=
  tMinus_ge_of h.toWidth k

/-- The inclusion `B_n ⊂ {nτ - 2Δ_max ≤ u_* < nτ + Δ⁺_max}`. -/
theorem band_subset (h : Hyp p I ubd CΓ CΓ' uFix) {Cpast : ℝ} (hCpast : 0 ≤ Cpast)
    (hCΓ' : 0 ≤ CΓ') (hmem : ∀ x ∈ I, HasMemory Cpast (p.Λ · x)) (k : ℕ) {x : X}
    (hx : x ∈ (anbRunData p k).band) :
    (k : ℝ) * p.τ - 2 * p.Δmax ≤ uFix x ∧
      uFix x < (k : ℝ) * p.τ + p.ΔplusMax Cpast CΓ CΓ' uFix :=
  band_subset_of h.toWidth hCpast hCΓ' hmem k hx

/-- The inclusion `B'_n ⊂ {(n-1)τ - 2Δ_max ≤ u_* < nτ + Δ⁺_max}`, with `n = k + 1`. -/
theorem dijkstraBand_subset (h : Hyp p I ubd CΓ CΓ' uFix) {Cpast : ℝ} (hCpast : 0 ≤ Cpast)
    (hCΓ' : 0 ≤ CΓ') (hmem : ∀ x ∈ I, HasMemory Cpast (p.Λ · x)) {k : ℕ} {x : X}
    (hx : x ∈ anbDijkstraBand (anbRunData p k).tMinus (((k + 1 : ℕ) : ℝ) * p.τ)
      (anbRunData p k).uHat (anbRunData p (k + 1)).uHat) :
    (k : ℝ) * p.τ - 2 * p.Δmax ≤ uFix x ∧
      uFix x < ((k + 1 : ℕ) : ℝ) * p.τ + p.ΔplusMax Cpast CΓ CΓ' uFix :=
  dijkstraBand_subset_of h.toWidth hCpast hCΓ' hmem hx

/-- `#{n | x ∈ B_n} ≤ N'_Λ`. -/
theorem card_band_le (h : Hyp p I ubd CΓ CΓ' uFix) {Cpast : ℝ} (hCpast : 0 ≤ Cpast)
    (hCΓ' : 0 ≤ CΓ') (hmem : ∀ x ∈ I, HasMemory Cpast (p.Λ · x)) (x : X) {S : Finset ℕ}
    (hS : ∀ k ∈ S, x ∈ (anbRunData p k).band) :
    S.card ≤ p.NΛ' Cpast CΓ CΓ' uFix :=
  card_band_le_of h.toWidth hCpast hCΓ' hmem x hS

/-- `#{n | x ∈ B'_n} ≤ N_Γ`. -/
theorem card_dijkstraBand_le (h : Hyp p I ubd CΓ CΓ' uFix) {Cpast : ℝ} (hCpast : 0 ≤ Cpast)
    (hCΓ' : 0 ≤ CΓ') (hmem : ∀ x ∈ I, HasMemory Cpast (p.Λ · x)) (x : X) {S : Finset ℕ}
    (hS : ∀ k ∈ S, x ∈ anbDijkstraBand (anbRunData p k).tMinus (((k + 1 : ℕ) : ℝ) * p.τ)
      (anbRunData p k).uHat (anbRunData p (k + 1)).uHat) :
    S.card ≤ p.NΓ Cpast CΓ CΓ' uFix :=
  card_dijkstraBand_le_of h.toWidth hCpast hCΓ' hmem x hS

/-- At most `N_Γ` updates `û(x) ← Γ û(x)` at any point, over the whole run. -/
theorem countHat_le (h : Hyp p I ubd CΓ CΓ' uFix) {Cpast : ℝ} (hCpast : 0 ≤ Cpast)
    (hCΓ' : 0 ≤ CΓ') (hmem : ∀ x ∈ I, HasMemory Cpast (p.Λ · x)) (k : ℕ) (x : X) :
    (anbRun p k).countHat x ≤ p.NΓ Cpast CΓ CΓ' uFix :=
  countHat_le_of h.toWidth hCpast hCΓ' hmem k x

end GuaranteedSubsol.AnbNGammaProof
