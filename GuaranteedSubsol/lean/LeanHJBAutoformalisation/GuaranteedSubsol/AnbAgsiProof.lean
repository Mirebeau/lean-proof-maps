/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AnbComplexityProof
import LeanHJBAutoformalisation.GuaranteedSubsol.ParallelAgsiSubProof
import LeanHJBAutoformalisation.GuaranteedSubsol.ParallelAgsiResultProof

/-!
# ANB with the parallel AGSI: Theorem th:complexity_with_agsi, proof

Provider proof for the frozen anchor `GuaranteedSubsol.anbAgsiRun_complexity`, see `ANCHORS.md`.
The variant of algo:anb whose inner loops (lines anb:while_sub and anb:while_sup) are parallel AGSI
on the band `B_n` (`anbAgsi`) is analysed as algo:anb (`AnbProof`, ..., `AnbNiterProof`, written
for any valid inner solver), replacing Prop. prop:niter_while with Prop. prop:cplx_agsi_parallel:
* on the band, the operator `Φ_α` with frozen values outside is monotone and `ρ`-sub-additive
  (`BandProof`), so the parallel AGSI performs at most
  `⌈ln((1 - ρ) C / η)/(-ln ρ)⌉ + 2/(1 - ρ)²` updates at each point
  (`ParallelAgsiCplxProof.count_le_of_subAdditive` and its sub-solution variant), and therefore
  stops (`band_subCount_le`, `band_count_le`);
* with a crude constant `C`, this shows that the inner loops stop, and the induction of
  corol:max_width applies (`toWidthAgsi`);
* with `C = exp((2Δ_max - nτ)/α)` (from `û_n ≥ nτ - 2Δ_max` on `B_n`) and `η = (1 - ρ) exp(-nτ/α)`,
  the bound is `N''_Λ = ⌈2Δ_max/(-α ln ρ)⌉ + ⌊2/(1 - ρ)²⌋` (`counts_le_NΛ''agsi`).

The AGSI bounds the number of updates at each point of the band, not the number of passes of the
inner loops: a pass may update a single point.
-/

namespace GuaranteedSubsol.AnbAgsiProof

open AnbProof AnbBnCompProof AnbMaxWidthProof AnbNGammaProof AnbNiterProof AnbComplexityProof

variable {X : Type*}

/-- A natural number below `A + r` (with `A` natural) is at most `A + ⌊r⌋`. -/
theorem le_add_floor {c A : ℕ} {r : ℝ} (h : (c : ℝ) ≤ A + r) : c ≤ A + ⌊r⌋₊ := by
  rcases le_or_gt c A with hcA | hcA
  · omega
  · have h1 : ((c - A : ℕ) : ℝ) ≤ r := by rw [Nat.cast_sub hcA.le]; linarith
    have := Nat.le_floor h1
    omega

/-! ### The parallel AGSI on the band -/

section Band

variable {Φ : (X → ℝ) → X → ℝ} {B : Set X} {w : X → ℝ} {ρ η C : ℝ}

/-- Prop. prop:cplx_agsi_parallel on the band, sub-solution variant: the loop stops, and performs at
most `⌈ln((1 - ρ) C / η)/(-ln ρ)⌉ + ⌊2/(1 - ρ)²⌋` updates at each point. -/
theorem band_subCount_le [Finite X] (hmono : ∀ x ∈ B, Monotone (Φ · x))
    (hsub : ∀ x ∈ B, SubAdditive ρ (Φ · x)) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hη : 0 < η)
    (hv : ∀ x ∈ B, w x ≤ Φ w x) (hvC : ∀ x ∈ B, Φ w x - w x ≤ C) :
    parallelAgsiSubPasses (bandOp Φ B w) η (fun y => w y) < ⊤ ∧ ∀ y,
      parallelAgsiSubCount (bandOp Φ B w) η (fun y => w y) y ≤
        ((⌈Real.log ((1 - ρ) * C / η) / (-Real.log ρ)⌉₊ + ⌊2 / (1 - ρ) ^ 2⌋₊ : ℕ) : ℕ∞) := by
  have hΨ : Monotone (bandOp Φ B w) := BandProof.monotone_bandOp hmono
  have hsubΨ : ∀ y : B, SubAdditive ρ (bandOp Φ B w · y) := fun y =>
    BandProof.subAdditive_bandOp y.2 (hmono y y.2) (hsub y y.2)
  have hr0 : (fun y : B => w y) ≤ bandOp Φ B w fun y => w y := fun y => by
    change w y ≤ Φ (bandExtend B w fun y => w y) y
    rw [bandExtend_restrict]
    exact hv y y.2
  have hrC : ∀ y : B, bandOp Φ B w (fun y => w y) y - w y ≤ C := fun y => by
    change Φ (bandExtend B w fun y => w y) y - w y ≤ C
    rw [bandExtend_restrict]
    exact hvC y y.2
  have hb : ∀ n y, ((parallelAgsiSubRun (bandOp Φ B w) η (fun y => w y) n).count y : ℝ) ≤
      ⌈Real.log ((1 - ρ) * C / η) / (-Real.log ρ)⌉₊ + 2 / (1 - ρ) ^ 2 := fun n y =>
    ParallelAgsiSubProof.count_le_of_subAdditive hΨ hρ0 hρ1 hsubΨ hη hr0 hrC n y
  have hp := ParallelAgsiResultProof.subPasses_lt_top_of_count_le hb
  refine ⟨hp, fun y => ?_⟩
  rw [ParallelAgsiResultProof.subCount_eq hp]
  exact Nat.cast_le.2 (le_add_floor (hb _ y))

/-- Prop. prop:cplx_agsi_parallel on the band, super-solution version. -/
theorem band_count_le [Finite X] (hmono : ∀ x ∈ B, Monotone (Φ · x))
    (hsub : ∀ x ∈ B, SubAdditive ρ (Φ · x)) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hη : 0 < η)
    (hv : ∀ x ∈ B, Φ w x ≤ w x) (hvC : ∀ x ∈ B, w x - Φ w x ≤ C) :
    parallelAgsiPasses (bandOp Φ B w) η (fun y => w y) < ⊤ ∧ ∀ y,
      parallelAgsiCount (bandOp Φ B w) η (fun y => w y) y ≤
        ((⌈Real.log ((1 - ρ) * C / η) / (-Real.log ρ)⌉₊ + ⌊2 / (1 - ρ) ^ 2⌋₊ : ℕ) : ℕ∞) := by
  have hΨ : Monotone (bandOp Φ B w) := BandProof.monotone_bandOp hmono
  have hsubΨ : ∀ y : B, SubAdditive ρ (bandOp Φ B w · y) := fun y =>
    BandProof.subAdditive_bandOp y.2 (hmono y y.2) (hsub y y.2)
  have hr0 : (bandOp Φ B w fun y : B => w y) ≤ fun y : B => w y := fun y => by
    change Φ (bandExtend B w fun y => w y) y ≤ w y
    rw [bandExtend_restrict]
    exact hv y y.2
  have hrC : ∀ y : B, w y - bandOp Φ B w (fun y => w y) y ≤ C := fun y => by
    change w y - Φ (bandExtend B w fun y => w y) y ≤ C
    rw [bandExtend_restrict]
    exact hvC y y.2
  have hb : ∀ n y, ((parallelAgsiRun (bandOp Φ B w) η (fun y => w y) n).count y : ℝ) ≤
      ⌈Real.log ((1 - ρ) * C / η) / (-Real.log ρ)⌉₊ + 2 / (1 - ρ) ^ 2 := fun n y =>
    ParallelAgsiCplxProof.count_le_of_subAdditive hΨ hρ0 hρ1 hsubΨ hη hr0 hrC n y
  have hp := ParallelAgsiResultProof.passes_lt_top_of_count_le hb
  refine ⟨hp, fun y => ?_⟩
  rw [ParallelAgsiResultProof.count_eq hp]
  exact Nat.cast_le.2 (le_add_floor (hb _ y))

end Band

/-! ### The inner loops of the ANB with the parallel AGSI -/

variable [Fintype X] [LinearOrder X] {p : AnbParams X} {I : Set X} {ubd : X → ℝ} {CΓ CΓ' : ℝ}
  {uFix : X → ℝ}

omit [Fintype X] [LinearOrder X] in
theorem subCount_eq [Fintype X] [LinearOrder X] (p : AnbParams X) (s : AnbState X) {x : X}
    (hx : x ∈ (anbStepData p s).band) :
    anbSubCount anbAgsi p s x = parallelAgsiSubCount (anbStepData p s).ΦSub (anbStepData p s).η
      (fun y => (anbStepData p s).vSub y) ⟨x, hx⟩ := by
  simp only [anbSubCount, anbAgsi, hx, ↓reduceDIte]

omit [Fintype X] [LinearOrder X] in
theorem supCount_eq [Fintype X] [LinearOrder X] (p : AnbParams X) (s : AnbState X) {x : X}
    (hx : x ∈ (anbStepData p s).band) :
    anbSupCount anbAgsi p s x = parallelAgsiCount (anbStepData p s).ΦSup (anbStepData p s).η
      (fun y => (anbStepData p s).vSup y) ⟨x, hx⟩ := by
  simp only [anbSupCount, anbAgsi, hx, ↓reduceDIte]

/-- In iteration `k`, the two inner loops perform at most
`⌈ln((1 - ρ) C / η)/(-ln ρ)⌉ + ⌊2/(1 - ρ)²⌋` updates at each point of the band, for any `C` such
that `E_α û ≥ -C` on the band. -/
theorem counts_le (h : Hyp p I ubd CΓ CΓ' uFix) (hρ0 : 0 < p.ρ) (k : ℕ) {C : ℝ}
    (hC : ∀ y ∈ (anbRunDataWith anbAgsi p k).band, -C ≤ (anbRunDataWith anbAgsi p k).vSub y) :
    ∀ x ∈ (anbRunDataWith anbAgsi p k).band,
      anbSubCount anbAgsi p (anbRunWith anbAgsi p k) x ≤
        ((⌈Real.log ((1 - p.ρ) * C / (anbRunDataWith anbAgsi p k).η) / (-Real.log p.ρ)⌉₊ +
          ⌊2 / (1 - p.ρ) ^ 2⌋₊ : ℕ) : ℕ∞) ∧
      anbSupCount anbAgsi p (anbRunWith anbAgsi p k) x ≤
        ((⌈Real.log ((1 - p.ρ) * C / (anbRunDataWith anbAgsi p k).η) / (-Real.log p.ρ)⌉₊ +
          ⌊2 / (1 - p.ρ) ^ 2⌋₊ : ℕ) : ℕ∞) := by
  intro x hx
  set s := anbRunWith anbAgsi p k with hs
  set d := anbStepData p s with hd
  have hdk : anbRunDataWith anbAgsi p k = d := rfl
  rw [hdk] at hx hC ⊢
  have hα := h.hα
  have hAS := h.always (S := anbAgsi) k
  have hη : 0 < d.η := by
    rw [hd, anbStepData_η]
    exact mul_pos (by linarith [h.hρ1]) (Real.exp_pos _)
  have hmonoΦ := ParallelAgsiKruzkovProof.monotone_global_kruzkovOp (Λ := p.Λ) hα
  have hmonoB : ∀ x ∈ d.band, Monotone (Global.kruzkovOp p.α p.Λ · x) :=
    fun x _ _ _ hab => hmonoΦ hab x
  have hΦneg : ∀ v y, Global.kruzkovOp p.α p.Λ v y ≤ 0 := fun v y => kruzkov_nonpos _ _
  -- `E_α û ≤ Φ_α (E_α û)`, `Φ_α (E_α u̲) ≤ E_α u̲` and `E_α û ≤ E_α u̲`
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
    exact (WithTop.coe_le_coe.2 (h.uHat_le (S := anbAgsi) k y)).trans
      (uFix_le_uSup h.hΛmono h.comp h.hfix hAS.uSup_ge y)
  have hsubC : ∀ y ∈ d.band, Global.kruzkovOp p.α p.Λ d.vSub y - d.vSub y ≤ C := fun y hy => by
    linarith [hΦneg d.vSub y, hC y hy]
  have hsupC : ∀ y ∈ d.band, d.vSup y - Global.kruzkovOp p.α p.Λ d.vSup y ≤ C := fun y hy => by
    have e1 : Global.kruzkovOp p.α p.Λ d.vSub y ≤ Global.kruzkovOp p.α p.Λ d.vSup y :=
      hmonoΦ hvv y
    linarith [hvΦ y, hC y hy, kruzkov_nonpos (1 / p.α) (s.uSup y),
      show d.vSup y = kruzkov (1 / p.α) (s.uSup y) from rfl]
  refine ⟨?_, ?_⟩
  · rw [subCount_eq p s hx]
    exact (band_subCount_le hmonoB (h.hsubB d.band) hρ0 h.hρ1 hη (fun y _ => hvΦ y) hsubC).2
      ⟨x, hx⟩
  · rw [supCount_eq p s hx]
    exact (band_count_le hmonoB (h.hsubB d.band) hρ0 h.hρ1 hη (fun y _ => hvΦ' y) hsupC).2
      ⟨x, hx⟩

/-- The hypotheses of Corollary corol:max_width give the ingredients `WidthHyp` for the ANB with
the parallel AGSI: the inner loops stop (with a crude constant `C`). -/
theorem toWidthAgsi (h : Hyp p I ubd CΓ CΓ' uFix) (hρ0 : 0 < p.ρ) :
    WidthHyp anbAgsi p I ubd CΓ CΓ' uFix p.Δmax := by
  refine h.toWidthOf fun k x hx => ?_
  have hb := counts_le h hρ0 k (C := ∑ y, -(anbRunDataWith anbAgsi p k).vSub y) (fun y _ => by
    rw [neg_le]
    exact Finset.single_le_sum (f := fun z => -(anbRunDataWith anbAgsi p k).vSub z)
      (fun z _ => neg_nonneg.2
        (kruzkov_nonpos (1 / p.α) ((anbRunDataWith anbAgsi p k).uHat z : ℝ)))
      (Finset.mem_univ y)) x hx
  exact ⟨hb.1.trans_lt (ENat.natCast_lt_top _), hb.2.trans_lt (ENat.natCast_lt_top _)⟩

/-- In each iteration, the two inner loops perform at most `N''_Λ` updates at each point of the
band. -/
theorem counts_le_NΛ''agsi (h : Hyp p I ubd CΓ CΓ' uFix) (hρ0 : 0 < p.ρ) (k : ℕ) :
    ∀ x ∈ (anbRunDataWith anbAgsi p k).band,
      anbSubCount anbAgsi p (anbRunWith anbAgsi p k) x ≤ (p.NΛ''agsi : ℕ∞) ∧
      anbSupCount anbAgsi p (anbRunWith anbAgsi p k) x ≤ (p.NΛ''agsi : ℕ∞) := by
  have hW := toWidthAgsi h hρ0
  have hα := h.hα
  set d := anbRunDataWith anbAgsi p k with hd
  set T : ℝ := (k : ℝ) * p.τ with hT
  set C : ℝ := Real.exp ((2 * p.Δmax - T) / p.α) with hC
  have h1ρ : 0 < 1 - p.ρ := by linarith [h.hρ1]
  have hη_eq : d.η = (1 - p.ρ) * Real.exp (-T / p.α) := by
    rw [hd, anbRunDataWith_def, anbStepData_η, anbRun_n]
  have hN : ⌈Real.log ((1 - p.ρ) * C / d.η) / (-Real.log p.ρ)⌉₊ + ⌊2 / (1 - p.ρ) ^ 2⌋₊ =
      p.NΛ''agsi := by
    have e : (1 - p.ρ) * C / d.η = Real.exp (2 * p.Δmax / p.α) := by
      rw [hη_eq, hC, mul_div_mul_left _ _ h1ρ.ne', ← Real.exp_sub]
      congr 1
      field_simp
      ring
    rw [e, Real.log_exp]
    unfold AnbParams.NΛ''agsi
    congr 2
    rw [div_div, mul_neg]
  -- on `B_k`, `û_k ≥ kτ - 2Δ_max`, so `-E_α û_k ≤ C`
  have hband : ∀ y ∈ d.band, -C ≤ d.vSub y := fun y hy => by
    have h1 := ((mem_band_iff p (anbRunWith anbAgsi p k) y).1 hy).1
    have h2 : T - 2 * p.Δmax ≤ d.tMinus := tMinus_ge_of hW k
    rw [neg_le]
    change -(-Real.exp (-(1 / p.α) * d.uHat y)) ≤ C
    rw [neg_neg, hC]
    apply Real.exp_le_exp.2
    rw [le_div_iff₀ hα]
    have : -(1 / p.α) * d.uHat y * p.α = -d.uHat y := by field_simp
    have h1' : d.tMinus ≤ d.uHat y := h1
    linarith
  intro x hx
  have hb := counts_le h hρ0 k hband x hx
  rw [hN] at hb
  exact hb

/-- In each iteration, the counters increase by at most `N''_Λ` at each point. -/
theorem countSub_countSup_step (h : Hyp p I ubd CΓ CΓ' uFix) (hρ0 : 0 < p.ρ) (k : ℕ) (x : X) :
    (anbRunWith anbAgsi p (k + 1)).countSub x ≤
        (anbRunWith anbAgsi p k).countSub x + (p.NΛ''agsi : ℕ∞) ∧
      (anbRunWith anbAgsi p (k + 1)).countSup x ≤
        (anbRunWith anbAgsi p k).countSup x + (p.NΛ''agsi : ℕ∞) := by
  classical
  have hsub : (anbRunWith anbAgsi p (k + 1)).countSub x = (anbRunWith anbAgsi p k).countSub x +
      if x ∈ (anbRunDataWith anbAgsi p k).band then
        anbSubCount anbAgsi p (anbRunWith anbAgsi p k) x else 0 := by
    rw [anbRun_succ, anbStep_eq]
    rfl
  have hsup : (anbRunWith anbAgsi p (k + 1)).countSup x = (anbRunWith anbAgsi p k).countSup x +
      if x ∈ (anbRunDataWith anbAgsi p k).band then
        anbSupCount anbAgsi p (anbRunWith anbAgsi p k) x else 0 := by
    rw [anbRun_succ, anbStep_eq]
    rfl
  rw [hsub, hsup]
  by_cases hx : x ∈ (anbRunDataWith anbAgsi p k).band
  · simp only [hx, ↓reduceIte]
    obtain ⟨h1, h2⟩ := counts_le_NΛ''agsi h hρ0 k x hx
    exact ⟨add_le_add le_rfl h1, add_le_add le_rfl h2⟩
  · simp only [hx, ↓reduceIte, add_zero]
    exact ⟨le_self_add, le_self_add⟩

/-! ### Theorem th:complexity_with_agsi -/

theorem complexity {p : AnbParams X}
    {I : Set X} {ubd : X → ℝ} (hΛbd : ∀ u, ∀ x ∉ I, p.Λ u x = ubd x)
    (hΓbd : ∀ u, ∀ x ∉ I, p.Γ u x = ubd x) {Cpast CΓ CΓ' : ℝ} (hCpast : 0 ≤ Cpast)
    (hCΓ : 1 ≤ CΓ) (hCΓ' : 0 ≤ CΓ') (hΛmono : ∀ x, Monotone (p.Λ · x))
    (hadd : ∀ x ∈ I, AdditivelyInvariant (p.Λ · x)) (hmem : ∀ x ∈ I, HasMemory Cpast (p.Λ · x))
    {w : X → ℝ} (hw : p.Λ w ≤ w) (hΓmono : ∀ x, Monotone (p.Γ · x))
    (hΓcaus : ∀ x, Causal (p.Γ · x)) (hΓadd : ∀ x ∈ I, AdditivelyInvariant (p.Γ · x))
    (hΓΛ : ∀ u, p.Γ u ≤ p.Λ u) (hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (p.Λ · x) (p.Γ · x))
    (hsub : ∀ x ∈ I, SubAdditive p.ρ (kruzkovOp p.α (p.Λ · x))) (hα : 0 < p.α)
    (hρ0 : 0 < p.ρ) (hρ1 : p.ρ < 1) (hτ : 0 < p.τ) (hε : 0 < p.ε)
    (hbd : ∀ x ∉ I, 2 * p.Δmax ≤ ubd x) :
    ∃ uFix : X → ℝ, p.Λ uFix = uFix ∧ (∀ v, p.Λ v = v → v = uFix) ∧
      (∀ J : Set X, HasComparisonPrinciple J p.Λ) ∧
      (p.ε ≤ p.εmax uFix →
        anbAgsiStopIndex p ≤ ((⌈p.nMax uFix⌉₊ + 1 : ℕ) : ℕ∞) ∧
        ((anbAgsiRun p (anbAgsiStopIndex p).toNat).uSub ≤
            p.Λ (anbAgsiRun p (anbAgsiStopIndex p).toNat).uSub ∧
          Global.monotoneExtension p.Λ (anbAgsiRun p (anbAgsiStopIndex p).toNat).uSup ≤
            (anbAgsiRun p (anbAgsiStopIndex p).toNat).uSup ∧
          anbDone p (anbAgsiRun p (anbAgsiStopIndex p).toNat)) ∧
        (∀ k, (anbAgsiRunData p k).Δ < p.Δmax) ∧
        (∀ (k : ℕ) (x : X),
          (anbAgsiRun p (k + 1)).countSub x ≤ (anbAgsiRun p k).countSub x + (p.NΛ''agsi : ℕ∞) ∧
          (anbAgsiRun p (k + 1)).countSup x ≤ (anbAgsiRun p k).countSup x + (p.NΛ''agsi : ℕ∞)) ∧
        (∀ (x : X) (S : Finset ℕ), (∀ k ∈ S, x ∈ (anbAgsiRunData p k).band) →
          S.card ≤ p.NΛ' Cpast CΓ CΓ' uFix) ∧
        (∀ (k : ℕ) (x : X),
          (anbAgsiRun p k).countSub x ≤ ((p.NΛ' Cpast CΓ CΓ' uFix * p.NΛ''agsi : ℕ) : ℕ∞) ∧
          (anbAgsiRun p k).countSup x ≤ ((p.NΛ' Cpast CΓ CΓ' uFix * p.NΛ''agsi : ℕ) : ℕ∞) ∧
          (anbAgsiRun p k).countHat x ≤ p.NΓ Cpast CΓ CΓ' uFix)) := by
  have hsubAll : ∀ x, SubAdditive p.ρ (kruzkovOp p.α (p.Λ · x)) := fun x => by
    by_cases hx : x ∈ I
    · exact hsub x hx
    · exact subAdditive_kruzkovOp_const (fun u => hΛbd u x hx) hρ0.le
  obtain ⟨uFix, hfix, huniq, -⟩ :=
    ComparisonLambdaProof.existsUnique_fixedPoint_of_kruzkov hα hρ1 hΛmono hsubAll hw
  refine ⟨uFix, hfix, huniq, hasComparisonPrinciple hΛbd hΛmono hα hρ1 hsub, fun hεmax => ?_⟩
  have h : Hyp p I ubd CΓ CΓ' uFix := ⟨hΛbd, hΓbd, hCΓ, hΛmono, hadd, hcmp, hΓmono, hΓcaus,
    hΓadd, hΓΛ, hsub, hα, hρ0.le, hρ1, hτ, hfix, hε, hεmax, hbd⟩
  have hW := toWidthAgsi h hρ0
  have hAS := h.always (S := anbAgsi) (anbAgsiStopIndex p).toNat
  refine ⟨stopIndex_le_of hW, ⟨hAS.uSub_le, hAS.uSup_ge, done_stopIndex ⟨_, done_of hW⟩⟩,
    Δ_lt_of hW, countSub_countSup_step h hρ0,
    fun x F hF => card_band_le_of hW hCpast hCΓ' hmem x hF, fun k x => ?_⟩
  obtain ⟨h1, h2⟩ :=
    countSub_countSup_le_of hW (counts_le_NΛ''agsi h hρ0) hCpast hCΓ' hmem k x
  exact ⟨h1, h2, countHat_le_of hW hCpast hCΓ' hmem k x⟩

end GuaranteedSubsol.AnbAgsiProof
