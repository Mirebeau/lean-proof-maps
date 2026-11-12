/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AnbNGammaProof

/-!
# ANB: Prop. prop:niter_while and the bound `N_Λ`, proofs

Provider proofs for the frozen anchors `GuaranteedSubsol.anbRunData_passes_le` and
`GuaranteedSubsol.anbRun_countSub_countSup_le`, see `ANCHORS.md`.

* `passes_le` (Prop. prop:niter_while): the number of passes of each inner loop is bounded by the
  termination result of the global iteration (`globalIterSubRun_terminates`,
  `globalIterRun_terminates`), applied to the band operator on the subtype `B_n`, with the
  initial residual `C := exp((2Δ_max - nτ)/α)` (on `B_n`, `û_n ≥ nτ - 2Δ_max`) and
  `η_n = (1 - ρ) exp(-nτ/α)`, so that `ln (C / η_n) = 2Δ_max / α - ln (1 - ρ)`.
* `countSub_countSup_le` (Theorem th:complexity): the counters increase by at most `N''_Λ` in each
  iteration with `x ∈ B_n`, which happens at most `N'_Λ` times (Corollary corol:NGamma).
-/

namespace GuaranteedSubsol.AnbNiterProof

open AnbProof AnbBnCompProof AnbMaxWidthProof AnbNGammaProof

variable {X : Type*}

/-- The number of passes of the global iteration (sub-solution variant) is at most any index at
which the stopping criterion holds. -/
theorem subPasses_le {Y : Type*} {Ψ : (Y → ℝ) → Y → ℝ} {η : ℝ} {v : Y → ℝ} {n : ℕ}
    (hn : ∀ y, Ψ (globalIterSubRun Ψ η v n) y - globalIterSubRun Ψ η v n y ≤ η) :
    globalIterSubPasses Ψ η v ≤ (n : ℕ∞) := by
  classical
  have h : ∃ n, ∀ y, Ψ (globalIterSubRun Ψ η v n) y - globalIterSubRun Ψ η v n y ≤ η := ⟨n, hn⟩
  unfold globalIterSubPasses
  simp only [h, ↓reduceDIte, Nat.cast_le]
  convert Nat.find_min' h hn

/-- The number of passes of the global iteration (super-solution version) is at most any index at
which the stopping criterion holds. -/
theorem passes_le_of {Y : Type*} {Ψ : (Y → ℝ) → Y → ℝ} {η : ℝ} {v : Y → ℝ} {n : ℕ}
    (hn : ∀ y, globalIterRun Ψ η v n y - Ψ (globalIterRun Ψ η v n) y ≤ η) :
    globalIterPasses Ψ η v ≤ (n : ℕ∞) := by
  classical
  have h : ∃ n, ∀ y, globalIterRun Ψ η v n y - Ψ (globalIterRun Ψ η v n) y ≤ η := ⟨n, hn⟩
  unfold globalIterPasses
  simp only [h, ↓reduceDIte, Nat.cast_le]
  convert Nat.find_min' h hn

/-- `ln (exp((2Δ - T)/α) / ((1 - ρ) exp(-T/α))) = 2Δ/α - ln (1 - ρ)`. -/
theorem log_ratio {α ρ T Δ : ℝ} (hα : 0 < α) (hρ1 : ρ < 1) :
    Real.log (Real.exp ((2 * Δ - T) / α) / ((1 - ρ) * Real.exp (-T / α))) =
      2 * Δ / α - Real.log (1 - ρ) := by
  have h1 : Real.exp ((2 * Δ - T) / α) / ((1 - ρ) * Real.exp (-T / α)) =
      Real.exp (2 * Δ / α) / (1 - ρ) := by
    rw [div_mul_eq_div_div, div_right_comm, ← Real.exp_sub]
    congr 2
    field_simp
    ring
  rw [h1, Real.log_div (Real.exp_pos _).ne' (by linarith), Real.log_exp]

variable [Fintype X] [LinearOrder X] {p : AnbParams X} {I : Set X} {ubd : X → ℝ} {CΓ CΓ' : ℝ}
  {uFix : X → ℝ}

/-- Prop. prop:niter_while: the two inner loops of iteration `k` perform at most `N''_Λ` passes;
in particular they stop (the number of passes is `⊤` for a loop that never stops). -/
theorem passes_le (h : Hyp p I ubd CΓ CΓ' uFix) (hρ : 0 < p.ρ) (k : ℕ) :
    (anbRunData p k).passesSub ≤ (p.NΛ'' : ℕ∞) ∧
      (anbRunData p k).passesSup ≤ (p.NΛ'' : ℕ∞) := by
  classical
  set s := anbRunWith anbGlobalIter p k with hs
  set d := anbStepData p s with hd
  have hdk : anbRunData p k = d := rfl
  rw [hdk]
  have hα := h.hα
  have hAS := h.always (S := anbGlobalIter) k
  set T : ℝ := (k : ℝ) * p.τ with hT
  set C : ℝ := Real.exp ((2 * p.Δmax - T) / p.α) with hC
  have hη_eq : d.η = (1 - p.ρ) * Real.exp (-T / p.α) := by rw [hd, anbStepData_η, hs, anbRun_n]
  have hη : 0 < d.η := by rw [hη_eq]; exact mul_pos (by linarith [h.hρ1]) (Real.exp_pos _)
  have hN : ⌈Real.log (C / d.η) / (-Real.log p.ρ)⌉₊ = p.NΛ'' := by
    rw [hη_eq, hC, log_ratio hα h.hρ1]
    rfl
  -- on `B_k`, `û_k ≥ kτ - 2Δ_max`, so `-E_α û_k ≤ C`
  have hband : ∀ y ∈ d.band, -d.vSub y ≤ C := fun y hy => by
    have h1 := ((mem_band_iff p s y).1 hy).1
    have h2 : T - 2 * p.Δmax ≤ d.tMinus := tMinus_ge h k
    change -(-Real.exp (-(1 / p.α) * d.uHat y)) ≤ C
    rw [neg_neg, hC]
    apply Real.exp_le_exp.2
    rw [le_div_iff₀ hα]
    have : -(1 / p.α) * d.uHat y * p.α = -d.uHat y := by field_simp
    linarith
  have hmonoΦ := ParallelAgsiKruzkovProof.monotone_global_kruzkovOp (Λ := p.Λ) hα
  have hmonoB : ∀ x ∈ d.band, Monotone (Global.kruzkovOp p.α p.Λ · x) :=
    fun x _ _ _ hab => hmonoΦ hab x
  have hΦneg : ∀ v y, Global.kruzkovOp p.α p.Λ v y ≤ 0 := fun v y => kruzkov_nonpos _ _
  -- `E_α û_k ≤ Φ_α (E_α û_k)` and `Φ_α (E_α u̲_k) ≤ E_α u̲_k`, and `E_α û_k ≤ E_α u̲_k`
  have hvΦ : ∀ y, d.vSub y ≤ Global.kruzkovOp p.α p.Λ d.vSub y := fun y => by
    have hvdef : d.vSub = fun z => kruzkov (1 / p.α) ((d.uHat z : ℝ) : WithTop ℝ) := rfl
    change d.vSub y ≤ kruzkovOp p.α (p.Λ · y) d.vSub
    rw [hvdef, ComparisonLambdaProof.kruzkovOp_kruzkov hα.ne' (h.hΛmono y)]
    exact (ComparisonLambdaProof.kruzkov_coe_le_iff hα _ _).2 (hAS.uHat_le y)
  have hvΦ' : ∀ y, Global.kruzkovOp p.α p.Λ d.vSup y ≤ d.vSup y := fun y => by
    have hvdef : d.vSup = fun z => kruzkov (1 / p.α) (s.uSup z) := rfl
    change kruzkovOp p.α (p.Λ · y) d.vSup ≤ d.vSup y
    rw [hvdef, kruzkovOp_kruzkov_ext hα.ne']
    exact (kruzkov_le_iff hα _ _).2 (hAS.uSup_ge y)
  have hvv : d.vSub ≤ d.vSup := fun y => by
    change kruzkov (1 / p.α) ((d.uHat y : ℝ) : WithTop ℝ) ≤ kruzkov (1 / p.α) (s.uSup y)
    rw [kruzkov_le_iff hα]
    exact (WithTop.coe_le_coe.2 (h.uHat_le (S := anbGlobalIter) k y)).trans
      (uFix_le_uSup h.hΛmono h.comp h.hfix hAS.uSup_ge y)
  -- the band operators
  have hext : ∀ w : X → ℝ, bandExtend d.band w (fun y => w y) = w := bandExtend_restrict d.band
  constructor
  · have hΨ : Monotone d.ΦSub := BandProof.monotone_bandOp hmonoB
    have hsubΨ : ∀ y : d.band, SubAdditive p.ρ (d.ΦSub · y) := fun y =>
      BandProof.subAdditive_bandOp y.2 (hmonoB y y.2) (h.hsubB d.band y y.2)
    have hv : (fun y : d.band => d.vSub y) ≤ d.ΦSub fun y => d.vSub y := fun y => by
      change d.vSub y ≤ Global.kruzkovOp p.α p.Λ (bandExtend d.band d.vSub fun y => d.vSub y) y
      rw [hext]; exact hvΦ y
    have hvC : ∀ y : d.band, d.ΦSub (fun y => d.vSub y) y - d.vSub y ≤ C := fun y => by
      change Global.kruzkovOp p.α p.Λ (bandExtend d.band d.vSub fun y => d.vSub y) y -
        d.vSub y ≤ C
      rw [hext]
      linarith [hΦneg d.vSub y, hband y y.2]
    obtain ⟨n, hn, hcrit⟩ := GlobalIterationProof.subRun_terminates hΨ hρ h.hρ1 hsubΨ hη hv hvC
    exact (subPasses_le hcrit).trans (Nat.cast_le.2 (hN ▸ hn))
  · have hΨ : Monotone d.ΦSup := BandProof.monotone_bandOp hmonoB
    have hsubΨ : ∀ y : d.band, SubAdditive p.ρ (d.ΦSup · y) := fun y =>
      BandProof.subAdditive_bandOp y.2 (hmonoB y y.2) (h.hsubB d.band y y.2)
    have hv : (d.ΦSup fun y : d.band => d.vSup y) ≤ fun y : d.band => d.vSup y := fun y => by
      change Global.kruzkovOp p.α p.Λ (bandExtend d.band d.vSup fun y => d.vSup y) y ≤ d.vSup y
      rw [hext]; exact hvΦ' y
    have hvC : ∀ y : d.band, d.vSup y - d.ΦSup (fun y => d.vSup y) y ≤ C := fun y => by
      change d.vSup y - Global.kruzkovOp p.α p.Λ (bandExtend d.band d.vSup fun y => d.vSup y) y
        ≤ C
      rw [hext]
      have e1 : Global.kruzkovOp p.α p.Λ d.vSub y ≤ Global.kruzkovOp p.α p.Λ d.vSup y :=
        hmonoΦ hvv y
      linarith [hvΦ y, hband y y.2, kruzkov_nonpos (1 / p.α) (s.uSup y),
        show d.vSup y = kruzkov (1 / p.α) (s.uSup y) from rfl]
    obtain ⟨n, hn, hcrit⟩ := GlobalIterationProof.terminates hΨ hρ h.hρ1 hsubΨ hη hv hvC
    exact (passes_le_of hcrit).trans (Nat.cast_le.2 (hN ▸ hn))

/-- Theorem th:complexity: at most `N_Λ = N'_Λ N''_Λ` updates `ū(x) ← Λ ū(x)` (resp.
`u̲(x) ← Λ u̲(x)`) at any point, over the whole run; in particular the counters are finite, i.e.
all the inner loops involving `x` stop. -/
theorem countSub_countSup_le_of {S : AnbInnerSolver X} [S.Valid] {Dm : ℝ}
    (h : WidthHyp S p I ubd CΓ CΓ' uFix Dm) {N : ℕ}
    (hN : ∀ k, ∀ x ∈ (anbRunDataWith S p k).band,
      anbSubCount S p (anbRunWith S p k) x ≤ (N : ℕ∞) ∧
        anbSupCount S p (anbRunWith S p k) x ≤ (N : ℕ∞))
    {Cpast : ℝ} (hCpast : 0 ≤ Cpast) (hCΓ' : 0 ≤ CΓ') (hmem : ∀ x ∈ I, HasMemory Cpast (p.Λ · x))
    (k : ℕ) (x : X) :
    (anbRunWith S p k).countSub x ≤ ((nΛ' p Cpast CΓ CΓ' uFix Dm * N : ℕ) : ℕ∞) ∧
      (anbRunWith S p k).countSup x ≤ ((nΛ' p Cpast CΓ CΓ' uFix Dm * N : ℕ) : ℕ∞) := by
  classical
  let P : ℕ → Prop := fun i => x ∈ (anbRunDataWith S p i).band
  have key : ∀ m, (anbRunWith S p m).countSub x ≤
        ((((Finset.range m).filter P).card * N : ℕ) : ℕ∞) ∧
      (anbRunWith S p m).countSup x ≤
        ((((Finset.range m).filter P).card * N : ℕ) : ℕ∞) := by
    intro m
    induction m with
    | zero =>
      have h0 : (anbRunWith S p 0).countSub x = 0 ∧ (anbRunWith S p 0).countSup x = 0 := ⟨rfl, rfl⟩
      rw [h0.1, h0.2]
      exact ⟨by simp, by simp⟩
    | succ m ih =>
      have hsub : (anbRunWith S p (m + 1)).countSub x = (anbRunWith S p m).countSub x +
          if x ∈ (anbRunDataWith S p m).band then anbSubCount S p (anbRunWith S p m) x else 0 := by
        rw [anbRun_succ, anbStep_eq]
        rfl
      have hsup : (anbRunWith S p (m + 1)).countSup x = (anbRunWith S p m).countSup x +
          if x ∈ (anbRunDataWith S p m).band then anbSupCount S p (anbRunWith S p m) x else 0 := by
        rw [anbRun_succ, anbStep_eq]
        rfl
      rw [hsub, hsup, Finset.range_add_one, Finset.filter_insert]
      by_cases hP : P m
      · have hP' : x ∈ (anbRunDataWith S p m).band := hP
        obtain ⟨hp1, hp2⟩ := hN m x hP'
        simp only [hP, hP', ↓reduceIte]
        rw [Finset.card_insert_of_notMem (by simp), add_mul, one_mul, Nat.cast_add]
        exact ⟨add_le_add ih.1 hp1, add_le_add ih.2 hp2⟩
      · have hP' : x ∉ (anbRunDataWith S p m).band := hP
        simp only [hP, hP', ↓reduceIte, add_zero]
        exact ih
  have hcard := card_band_le_of h hCpast hCΓ' hmem x
    (F := (Finset.range k).filter P) fun i hi => (Finset.mem_filter.1 hi).2
  have hmul : ((((Finset.range k).filter P).card * N : ℕ) : ℕ∞) ≤
      ((nΛ' p Cpast CΓ CΓ' uFix Dm * N : ℕ) : ℕ∞) :=
    Nat.cast_le.2 (Nat.mul_le_mul_right N hcard)
  exact ⟨(key k).1.trans hmul, (key k).2.trans hmul⟩

/-- Theorem th:complexity: at most `N_Λ = N'_Λ N''_Λ` updates `ū(x) ← Λ ū(x)` (resp.
`u̲(x) ← Λ u̲(x)`) at any point, over the whole run. -/
theorem countSub_countSup_le (h : Hyp p I ubd CΓ CΓ' uFix) (hρ : 0 < p.ρ) {Cpast : ℝ}
    (hCpast : 0 ≤ Cpast) (hCΓ' : 0 ≤ CΓ') (hmem : ∀ x ∈ I, HasMemory Cpast (p.Λ · x)) (k : ℕ)
    (x : X) :
    (anbRun p k).countSub x ≤ ((p.NΛ' Cpast CΓ CΓ' uFix * p.NΛ'' : ℕ) : ℕ∞) ∧
      (anbRun p k).countSup x ≤
        ((p.NΛ' Cpast CΓ CΓ' uFix * p.NΛ'' : ℕ) : ℕ∞) :=
  countSub_countSup_le_of h.toWidth (fun k _ _ => passes_le h hρ k) hCpast hCΓ' hmem k x

end GuaranteedSubsol.AnbNiterProof
