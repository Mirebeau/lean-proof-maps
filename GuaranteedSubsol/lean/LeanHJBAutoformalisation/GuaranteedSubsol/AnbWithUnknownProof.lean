/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AnbComplexityProof
import LeanHJBAutoformalisation.GuaranteedSubsol.GlobalIterKruzkovProof
import LeanHJBAutoformalisation.GuaranteedSubsol.TAdvancesWithUnknownProof

/-!
# ANB with a small parameter `α`: proofs

Provider proofs for Corollary corol:max_width_withUnknown and Prop. prop:niter_while_withUnknown
(Complexity.tex), see `ANCHORS.md`. Here `Φ_β` (not `Φ_α`) is `σ`-sub-additive, for unknown
constants `β ≥ α` and `σ < 1` (`AnbParams.WithUnknown`).

* On the band `B_n`, the band operator built from `Φ_α` is conjugate, through `v ↦ -(-v)^(α/β)`,
  to the band operator built from `Φ_β`, with the frozen values transformed accordingly
  (`band_conj`). The bound of `GlobalIterKruzkovProof` on the passes then applies
  (`band_passes_le`), with any constant `C` such that `E_α û_n ≥ -C` on `B_n`.
* With a crude `C`, this shows that the inner loops stop, and the induction of
  corol:max_width applies (`AnbMaxWidthProof.WidthHyp`), the advance property being given by
  Prop. prop:t_advances_withUnknown.
* With `C = exp((2Δ_max - nτ)/α)`, from `û_n ≥ nτ - 2Δ_max` on `B_n`, the bound is `N''_Λ`.
* Corollary corol:NGamma with the modified `Δ_max`, and the update counts, follow from the
  generic versions in `AnbNGammaProof` and `AnbNiterProof`; Theorem th:complexity_withUnknown
  assembles these results (`complexity`).
-/

namespace GuaranteedSubsol.AnbWithUnknownProof

open AnbProof AnbBnCompProof AnbMaxWidthProof GlobalIterKruzkovProof

variable {X : Type*}

/-! ### Conjugation of the band operators -/

section Conj

variable {Λ : (X → ℝ) → X → ℝ} {α β : ℝ} {B : Set X}

/-- `-(-·)^(α/β)` commutes with the extension by frozen values. -/
theorem bandExtend_rpow (w : X → ℝ) (v : B → ℝ) (r : ℝ) :
    (fun y => -(-bandExtend B w v y) ^ r) =
      bandExtend B (fun y => -(-w y) ^ r) (fun y => -(-v y) ^ r) := by
  classical
  funext y
  by_cases hy : y ∈ B
  · rw [bandExtend_of_mem _ _ _ hy, bandExtend_of_mem _ _ _ hy]
  · simp only [bandExtend, hy, ↓reduceDIte]

/-- The band operators built from `Φ_α` and `Φ_β` are conjugate. -/
theorem band_conj (hα : 0 < α) (hβ : 0 < β) {w w' : X → ℝ} (hw : ∀ y, w y ≤ 0)
    (hw' : ∀ y, w' y = -(-w y) ^ (α / β)) (v : B → ℝ) (hv : ∀ y, v y ≤ 0) (y : B) :
    bandOp (Global.kruzkovOp α Λ) B w v y =
      -(-bandOp (Global.kruzkovOp β Λ) B w' (fun z => -(-v z) ^ (α / β)) y) ^ (β / α) := by
  classical
  have hext : ∀ z, bandExtend B w v z ≤ 0 := fun z => by
    by_cases hz : z ∈ B
    · rw [bandExtend_of_mem _ _ _ hz]; exact hv _
    · simp only [bandExtend, hz, ↓reduceDIte]; exact hw z
  have hw'' : w' = fun y => -(-w y) ^ (α / β) := funext hw'
  change Global.kruzkovOp α Λ (bandExtend B w v) y =
    -(-Global.kruzkovOp β Λ (bandExtend B w' fun z => -(-v z) ^ (α / β)) y) ^ (β / α)
  rw [conj hα hβ _ hext, bandExtend_rpow, hw'']

end Conj

/-! ### The passes of the inner loops -/

variable [Fintype X] [LinearOrder X]

/-- The two inner loops of iteration `k` perform at most `⌈(ln (C/η) + ln (β/α))/(-ln σ)⌉` passes
(lem:cplx_global_iteration_withUnknown on the band, with the constant of lem:pow_cvx), when `Φ_β` is
`σ`-sub-additive and `E_α û ≥ -C` on the band. -/
theorem band_passes_le {p : AnbParams X} {β σ : ℝ} (hΛmono : ∀ x, Monotone (p.Λ · x))
    (hα : 0 < p.α) (hαβ : p.α ≤ β) (hρ1 : p.ρ < 1) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hsubB : ∀ x, SubAdditive σ (fun v => Global.kruzkovOp β p.Λ v x)) {s : AnbState X}
    (hAS : AnbAlwaysSubsol p s)
    (hle : ∀ y, (((anbStepData p s).uHat y : ℝ) : WithTop ℝ) ≤ s.uSup y) {C : ℝ}
    (hC : ∀ y ∈ (anbStepData p s).band, -C ≤ (anbStepData p s).vSub y) :
    (anbStepData p s).passesSub ≤
        (⌈(Real.log (C / (anbStepData p s).η) + Real.log (β / p.α)) / (-Real.log σ)⌉₊ : ℕ∞) ∧
      (anbStepData p s).passesSup ≤
        (⌈(Real.log (C / (anbStepData p s).η) + Real.log (β / p.α)) / (-Real.log σ)⌉₊ : ℕ∞) := by
  set d := anbStepData p s with hd
  have hβ : 0 < β := hα.trans_le hαβ
  have hη : 0 < d.η := by
    rw [hd, anbStepData_η]
    exact mul_pos (by linarith) (Real.exp_pos _)
  have hmonoβ := ParallelAgsiKruzkovProof.monotone_global_kruzkovOp (Λ := p.Λ) hβ
  have hmonoB : ∀ x ∈ d.band, Monotone (Global.kruzkovOp β p.Λ · x) :=
    fun x _ _ _ hab => hmonoβ hab x
  have hext : ∀ w : X → ℝ, bandExtend d.band w (fun y => w y) = w := bandExtend_restrict d.band
  -- the `β`-coordinates of `û` and `ū`
  set wHat : X → ℝ := fun y => kruzkov (1 / β) ((d.uHat y : ℝ) : WithTop ℝ) with hwHat
  set wSup : X → ℝ := fun y => kruzkov (1 / β) (s.uSup y) with hwSup
  have hwHatΦ : wHat ≤ Global.kruzkovOp β p.Λ wHat := fun y => by
    change _ ≤ kruzkovOp β (p.Λ · y) _
    rw [ComparisonLambdaProof.kruzkovOp_kruzkov hβ.ne' (hΛmono y)]
    exact (ComparisonLambdaProof.kruzkov_coe_le_iff hβ _ _).2 (hAS.uHat_le y)
  have hwSupΦ : Global.kruzkovOp β p.Λ wSup ≤ wSup := fun y => by
    change kruzkovOp β (p.Λ · y) _ ≤ _
    rw [kruzkovOp_kruzkov_ext hβ.ne']
    exact (kruzkov_le_iff hβ _ _).2 (hAS.uSup_ge y)
  have hwle : wHat ≤ wSup := fun y => (kruzkov_le_iff hβ _ _).2 (hle y)
  have hneg : ∀ (w' : X → ℝ) (v : d.band → ℝ) y,
      bandOp (Global.kruzkovOp β p.Λ) d.band w' v y ≤ 0 := fun _ _ _ => kruzkov_nonpos _ _
  have hsubΨ : ∀ (w' : X → ℝ) (y : d.band),
      SubAdditive σ (bandOp (Global.kruzkovOp β p.Λ) d.band w' · y) := fun _ y =>
    BandProof.subAdditive_bandOp y.2 (hmonoB y y.2) (hsubB y)
  have hconjα : ∀ a : WithTop ℝ, kruzkov (1 / p.α) a = -(-kruzkov (1 / β) a) ^ (β / p.α) :=
    kruzkov_rpow hβ hα
  have hconjβ : ∀ a : WithTop ℝ, kruzkov (1 / β) a = -(-kruzkov (1 / p.α) a) ^ (p.α / β) :=
    kruzkov_rpow hα hβ
  have hC' : ∀ y : d.band, -C ≤ d.vSub y := fun y => hC y y.2
  constructor
  · -- line anb:while_sub
    have hw0 : (fun y : d.band => wHat y) ≤
        bandOp (Global.kruzkovOp β p.Λ) d.band wHat fun y => wHat y := fun y => by
      change wHat y ≤ Global.kruzkovOp β p.Λ (bandExtend d.band wHat fun y => wHat y) y
      rw [hext]; exact hwHatΦ y
    exact core_subPasses_le (BandProof.monotone_bandOp hmonoB) (hsubΨ wHat) hσ0 hσ1 (hneg wHat)
      hα hαβ (band_conj hα hβ (fun y => kruzkov_nonpos _ _) (fun y => hconjβ _))
      (fun y => hconjα _) hw0 (fun y => kruzkov_nonpos _ _) hC' hη
  · -- line anb:while_sup
    have hw0 : (fun y : d.band => wHat y) ≤
        bandOp (Global.kruzkovOp β p.Λ) d.band wSup fun y => wHat y := fun y => by
      change wHat y ≤ Global.kruzkovOp β p.Λ (bandExtend d.band wSup fun y => wHat y) y
      refine (hwHatΦ y).trans (hmonoβ (fun z => ?_) y)
      by_cases hz : z ∈ d.band
      · rw [bandExtend_of_mem _ _ _ hz]
      · classical
        simp only [bandExtend, hz, ↓reduceDIte]; exact hwle z
    have hw1 : (bandOp (Global.kruzkovOp β p.Λ) d.band wSup fun y => wSup y) ≤
        fun y : d.band => wSup y := fun y => by
      change Global.kruzkovOp β p.Λ (bandExtend d.band wSup fun y => wSup y) y ≤ wSup y
      rw [hext]; exact hwSupΦ y
    exact core_passes_le_sup (BandProof.monotone_bandOp hmonoB) (hsubΨ wSup) hσ0 hσ1
      (hneg wSup) hα hαβ (band_conj hα hβ (fun y => kruzkov_nonpos _ _) (fun y => hconjβ _))
      (fun y => hconjα _) (fun y => hconjα _) hw0 hw1 (fun y => kruzkov_nonpos _ _)
      (fun y => kruzkov_nonpos _ _) (fun y => hwle y) hC' hη

/-! ### The hypotheses with unknown constants `β`, `σ` -/

/-- The hypotheses of Corollary corol:max_width_withUnknown and
Prop. prop:niter_while_withUnknown (see the anchors). -/
structure HypU (q : AnbParams.WithUnknown X) (I : Set X) (ubd : X → ℝ) (CΓ CΓ' : ℝ)
    (uFix : X → ℝ) : Prop where
  hΛbd : ∀ u, ∀ x ∉ I, q.p.Λ u x = ubd x
  hΓbd : ∀ u, ∀ x ∉ I, q.p.Γ u x = ubd x
  hCΓ : 1 ≤ CΓ
  hΛmono : ∀ x, Monotone (q.p.Λ · x)
  hadd : ∀ x ∈ I, AdditivelyInvariant (q.p.Λ · x)
  hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (q.p.Λ · x) (q.p.Γ · x)
  hΓmono : ∀ x, Monotone (q.p.Γ · x)
  hΓcaus : ∀ x, Causal (q.p.Γ · x)
  hΓadd : ∀ x ∈ I, AdditivelyInvariant (q.p.Γ · x)
  hΓΛ : ∀ u, q.p.Γ u ≤ q.p.Λ u
  hsub : ∀ x ∈ I, SubAdditive q.σ (kruzkovOp q.β (q.p.Λ · x))
  hα : 0 < q.p.α
  hαβ : q.p.α ≤ q.β
  hσ0 : 0 < q.σ
  hσ1 : q.σ < 1
  hρ1 : q.p.ρ < 1
  hρσ : (1 - q.σ) ^ q.β ≤ (1 - q.p.ρ) ^ q.p.α
  hτ : 0 < q.p.τ
  hfix : q.p.Λ uFix = uFix
  hε : 0 < q.p.ε
  hεmax : q.p.ε ≤ q.εmax uFix
  hbd : ∀ x ∉ I, 2 * q.Δmax ≤ ubd x

namespace HypU

variable {q : AnbParams.WithUnknown X} {I : Set X} {ubd : X → ℝ} {CΓ CΓ' : ℝ} {uFix : X → ℝ}

omit [LinearOrder X] in
theorem hβ (h : HypU q I ubd CΓ CΓ' uFix) : 0 < q.β := h.hα.trans_le h.hαβ

omit [LinearOrder X] in
/-- `C ≥ 1`, from `(1 - σ)^β ≤ (1 - ρ)^α`. -/
theorem one_le_C (h : HypU q I ubd CΓ CΓ' uFix) : 1 ≤ q.C := by
  have hβ := h.hβ
  have hσ : 0 < 1 - q.σ := by linarith [h.hσ1]
  have hρ : 0 < 1 - q.p.ρ := by linarith [h.hρ1]
  have h1 := Real.rpow_le_rpow (Real.rpow_nonneg hσ.le _) h.hρσ (inv_nonneg.2 hβ.le)
  rw [Real.rpow_rpow_inv hσ.le hβ.ne', ← Real.rpow_mul hρ.le] at h1
  unfold AnbParams.WithUnknown.C
  rw [le_div_iff₀ hσ, one_mul]
  convert h1 using 2
  rw [div_eq_mul_inv]

omit [LinearOrder X] in
theorem log_ge_one (h : HypU q I ubd CΓ CΓ' uFix) :
    1 ≤ Real.log (2 * Real.exp 1 * q.C / q.p.ε) := by
  have hε2 : q.p.ε ≤ 2 := h.hεmax.trans (min_le_right _ _)
  have hC := h.one_le_C
  rw [Real.le_log_iff_exp_le (div_pos (by positivity) h.hε), le_div_iff₀ h.hε]
  nlinarith [Real.exp_pos 1]

omit [Fintype X] [LinearOrder X] in
theorem Δmax_eq (q : AnbParams.WithUnknown X) :
    q.Δmax = 2 * q.β * Real.log (2 * Real.exp 1 * q.C / q.p.ε) + 2 * q.p.τ := rfl

omit [LinearOrder X] in
theorem two_τ_lt (h : HypU q I ubd CΓ CΓ' uFix) : 2 * q.p.τ < q.Δmax := by
  have := mul_pos (mul_pos two_pos h.hβ) (lt_of_lt_of_le one_pos h.log_ge_one)
  rw [Δmax_eq]
  linarith

omit [LinearOrder X] in
theorem ubd_nonneg (h : HypU q I ubd CΓ CΓ' uFix) : ∀ x ∉ I, 0 ≤ ubd x := fun x hx => by
  linarith [h.hbd x hx, h.two_τ_lt, h.hτ]

omit [LinearOrder X] in
theorem hsubB (h : HypU q I ubd CΓ CΓ' uFix) :
    ∀ x, SubAdditive q.σ (fun v => Global.kruzkovOp q.β q.p.Λ v x) := fun x => by
  by_cases hx : x ∈ I
  · exact h.hsub x hx
  · exact subAdditive_kruzkovOp_const (fun u => h.hΛbd u x hx) h.hσ0.le

omit [LinearOrder X] in
theorem apply_zero (h : HypU q I ubd CΓ CΓ' uFix) : 0 ≤ q.p.Λ 0 :=
  apply_zero_nonneg h.hΛbd h.ubd_nonneg h.hΛmono h.hadd h.hβ h.hσ0.le h.hσ1 h.hsub

omit [LinearOrder X] in
theorem comp (h : HypU q I ubd CΓ CΓ' uFix) (J : Set X) : HasComparisonPrinciple J q.p.Λ :=
  hasComparisonPrinciple h.hΛbd h.hΛmono h.hβ h.hσ1 h.hsub J

theorem always (h : HypU q I ubd CΓ CΓ' uFix) (k : ℕ) : AnbAlwaysSubsol q.p (anbRun q.p k) :=
  always_subsol h.hΛmono h.apply_zero h.hΓmono h.hΓcaus h.hΓΛ h.hα h.hτ.le k

/-- `û ≤ ū` in every iteration, through `û ≤ u_* ≤ ū`. -/
theorem uHat_le_uSup (h : HypU q I ubd CΓ CΓ' uFix) (k : ℕ) (y : X) :
    (((anbRunData q.p k).uHat y : ℝ) : WithTop ℝ) ≤ (anbRun q.p k).uSup y :=
  (WithTop.coe_le_coe.2 (uHat_le_uFix h.hΛmono h.apply_zero h.hΓmono h.hΓcaus h.hΓΛ h.comp
    h.hfix h.hα h.hτ.le k y)).trans (uFix_le_uSup h.hΛmono h.comp h.hfix (h.always k).uSup_ge y)

/-- The bound of `band_passes_le` in iteration `k`. -/
theorem passes_le_of (h : HypU q I ubd CΓ CΓ' uFix) (k : ℕ) {C : ℝ}
    (hC : ∀ y ∈ (anbRunData q.p k).band, -C ≤ (anbRunData q.p k).vSub y) :
    (anbRunData q.p k).passesSub ≤ (⌈(Real.log (C / (anbRunData q.p k).η) +
        Real.log (q.β / q.p.α)) / (-Real.log q.σ)⌉₊ : ℕ∞) ∧
      (anbRunData q.p k).passesSup ≤ (⌈(Real.log (C / (anbRunData q.p k).η) +
        Real.log (q.β / q.p.α)) / (-Real.log q.σ)⌉₊ : ℕ∞) :=
  band_passes_le h.hΛmono h.hα h.hαβ h.hρ1 h.hσ0 h.hσ1 h.hsubB (h.always k) (h.uHat_le_uSup k)
    hC

/-- The hypotheses of corol:max_width_withUnknown give the ingredients `WidthHyp` of the
induction of corol:max_width, with `Δ_max = 2β ln(2eC/ε) + 2τ`. -/
theorem toWidth (h : HypU q I ubd CΓ CΓ' uFix) :
    WidthHyp anbGlobalIter q.p I ubd CΓ CΓ' uFix q.Δmax := by
  refine ⟨h.hΛbd, h.hΓbd, h.hCΓ, h.hΛmono, h.hcmp, h.hΓmono, h.hΓcaus, h.hΓadd, h.hΓΛ,
    h.apply_zero, h.comp, h.hα, h.hρ1, h.hτ, h.hfix, h.hε, h.hεmax.trans (min_le_left _ _),
    h.two_τ_lt, h.hbd, fun k x _ => ?_, ?_, h.hadd⟩
  · -- the inner loops stop, with the crude bound `-E_α û ≤ ∑_y -E_α û(y)`
    have hb := h.passes_le_of k (C := ∑ y, -(anbRunData q.p k).vSub y) fun y _ => by
      rw [neg_le]
      exact Finset.single_le_sum (f := fun z => -(anbRunData q.p k).vSub z)
        (fun z _ => neg_nonneg.2 (kruzkov_nonpos (1 / q.p.α) ((anbRunData q.p k).uHat z : ℝ)))
        (Finset.mem_univ y)
    exact ⟨hb.1.trans_lt (ENat.natCast_lt_top _), hb.2.trans_lt (ENat.natCast_lt_top _)⟩
  · -- the advance property: Prop. prop:t_advances_withUnknown
    intro uSub vsub vsup Tm Tp ξ t Δ hvsub hvsup hTm hξ ht hΔ ha1 ha2 hb hc hξT hεT hΔl
    have hL := h.log_ge_one
    have hΔl' : 2 * q.β * max 1 (Real.log (2 * Real.exp 1 * q.C / q.p.ε)) ≤ Δ := by
      rw [max_eq_right hL]
      have := Δmax_eq q
      linarith [h.hτ]
    exact TAdvancesWithUnknownProof.t_advances_withUnknown h.hΛbd h.hα h.hβ
      (mul_one_div_cancel h.hα.ne') h.hρ1 h.hσ0.le h.hσ1 rfl ((div_le_one h.hβ).2 h.hαβ) rfl
      h.one_le_C h.hadd h.hsub hvsub hvsup hTm hξ h.hε ht hΔ ha1 ha2 hb hc hξT hεT hΔl'

end HypU

/-! ### Corollary corol:max_width_withUnknown and Prop. prop:niter_while_withUnknown -/

variable {q : AnbParams.WithUnknown X} {I : Set X} {ubd : X → ℝ} {CΓ CΓ' : ℝ} {uFix : X → ℝ}

/-- Corollary corol:max_width_withUnknown, first claim: `Δ_n < Δ_max`. -/
theorem Δ_lt (h : HypU q I ubd CΓ CΓ' uFix) (k : ℕ) : (anbRunData q.p k).Δ < q.Δmax :=
  Δ_lt_of h.toWidth k

/-- Corollary corol:max_width_withUnknown, termination: the stopping index is at most
`⌈n_max⌉₊ + 1`. -/
theorem stopIndex_le (h : HypU q I ubd CΓ CΓ' uFix) :
    anbStopIndex q.p ≤ ((⌈q.nMax uFix⌉₊ + 1 : ℕ) : ℕ∞) :=
  stopIndex_le_of h.toWidth

/-- Prop. prop:niter_while_withUnknown (V1): the two inner loops of iteration `k` perform at most
`⌈(2Δ_max/α + ln(β/α) - ln(1-ρ))/(-ln σ)⌉` passes (constant of lem:pow_cvx). -/
theorem passes_le (h : HypU q I ubd CΓ CΓ' uFix) (k : ℕ) :
    (anbRunData q.p k).passesSub ≤ (q.NΛ'' : ℕ∞) ∧
      (anbRunData q.p k).passesSup ≤ (q.NΛ'' : ℕ∞) := by
  set d := anbRunData q.p k with hd
  have hα := h.hα
  set T : ℝ := (k : ℝ) * q.p.τ with hT
  set C : ℝ := Real.exp ((2 * q.Δmax - T) / q.p.α) with hC
  have hη_eq : d.η = (1 - q.p.ρ) * Real.exp (-T / q.p.α) := by
    rw [hd, anbRunData_def, anbRun_eq_with, anbStepData_η, anbRun_n]
  have hN : ⌈(Real.log (C / d.η) + Real.log (q.β / q.p.α)) / (-Real.log q.σ)⌉₊ = q.NΛ'' := by
    rw [hη_eq, hC, AnbNiterProof.log_ratio hα h.hρ1]
    unfold AnbParams.WithUnknown.NΛ''
    congr 2
    ring
  -- on `B_k`, `û_k ≥ kτ - 2Δ_max`, so `-E_α û_k ≤ C`
  have htm : T - 2 * q.Δmax ≤ d.tMinus := by
    rw [AnbStepData.tMinus_def]
    have hΔe : (anbRunData q.p k).Δ = (k : ℝ) * q.p.τ - (anbRunData q.p k).t :=
      AnbNGammaProof.Δ_eq anbGlobalIter q.p k
    linarith [Δ_lt h k, hΔe]
  have hband : ∀ y ∈ d.band, -C ≤ d.vSub y := fun y hy => by
    have h1 := ((mem_band_iff q.p (anbRun q.p k) y).1 hy).1
    rw [neg_le]
    change -(-Real.exp (-(1 / q.p.α) * d.uHat y)) ≤ C
    rw [neg_neg, hC]
    apply Real.exp_le_exp.2
    rw [le_div_iff₀ hα]
    have : -(1 / q.p.α) * d.uHat y * q.p.α = -d.uHat y := by field_simp
    have h1' : d.tMinus ≤ d.uHat y := h1
    linarith
  have hb := h.passes_le_of k hband
  rw [hN] at hb
  exact hb

/-! ### Corollary corol:NGamma with the modified `Δ_max` -/

/-- Corollary corol:NGamma with the modified `Δ_max` (last sentence of
corol:max_width_withUnknown): the inclusions of `B_n` and `B'_n` in windows of `u_*`, and the
bounds `N'_Λ` and `N_Γ` on the numbers of iterations whose band contains a given point. -/
theorem nGamma (h : HypU q I ubd CΓ CΓ' uFix) {Cpast : ℝ} (hCpast : 0 ≤ Cpast)
    (hCΓ' : 0 ≤ CΓ') (hmem : ∀ x ∈ I, HasMemory Cpast (q.p.Λ · x)) :
    (∀ (k : ℕ) (x : X), x ∈ (anbRunData q.p k).band →
      (k : ℝ) * q.p.τ - 2 * q.Δmax ≤ uFix x ∧
        uFix x < (k : ℝ) * q.p.τ + q.ΔplusMax Cpast CΓ CΓ' uFix) ∧
    (∀ (k : ℕ) (x : X), x ∈ anbDijkstraBand (anbRunData q.p k).tMinus
        (((k + 1 : ℕ) : ℝ) * q.p.τ) (anbRunData q.p k).uHat (anbRunData q.p (k + 1)).uHat →
      (k : ℝ) * q.p.τ - 2 * q.Δmax ≤ uFix x ∧
        uFix x < ((k + 1 : ℕ) : ℝ) * q.p.τ + q.ΔplusMax Cpast CΓ CΓ' uFix) ∧
    (∀ (x : X) (S : Finset ℕ), (∀ k ∈ S, x ∈ (anbRunData q.p k).band) →
      S.card ≤ q.NΛ' Cpast CΓ CΓ' uFix) ∧
    (∀ (x : X) (S : Finset ℕ), (∀ k ∈ S, x ∈ anbDijkstraBand (anbRunData q.p k).tMinus
        (((k + 1 : ℕ) : ℝ) * q.p.τ) (anbRunData q.p k).uHat (anbRunData q.p (k + 1)).uHat) →
      S.card ≤ q.NΓ Cpast CΓ CΓ' uFix) :=
  ⟨fun k _ hx => AnbNGammaProof.band_subset_of h.toWidth hCpast hCΓ' hmem k hx,
    fun _ _ hx => AnbNGammaProof.dijkstraBand_subset_of h.toWidth hCpast hCΓ' hmem hx,
    fun x _ hS => AnbNGammaProof.card_band_le_of h.toWidth hCpast hCΓ' hmem x hS,
    fun x _ hS => AnbNGammaProof.card_dijkstraBand_le_of h.toWidth hCpast hCΓ' hmem x hS⟩

/-! ### Theorem th:complexity_withUnknown -/

omit [Fintype X] [LinearOrder X] in
theorem hsubAll {q : AnbParams.WithUnknown X} {I : Set X} {ubd : X → ℝ}
    (hΛbd : ∀ u, ∀ x ∉ I, q.p.Λ u x = ubd x) (hσ0 : 0 < q.σ)
    (hsub : ∀ x ∈ I, SubAdditive q.σ (kruzkovOp q.β (q.p.Λ · x))) :
    ∀ x, SubAdditive q.σ (kruzkovOp q.β (q.p.Λ · x)) := fun x => by
  by_cases hx : x ∈ I
  · exact hsub x hx
  · exact subAdditive_kruzkovOp_const (fun u => hΛbd u x hx) hσ0.le

theorem complexity
    (hΛbd : ∀ u, ∀ x ∉ I, q.p.Λ u x = ubd x) (hΓbd : ∀ u, ∀ x ∉ I, q.p.Γ u x = ubd x)
    {Cpast : ℝ} (hCpast : 0 ≤ Cpast) (hCΓ : 1 ≤ CΓ) (hCΓ' : 0 ≤ CΓ')
    (hΛmono : ∀ x, Monotone (q.p.Λ · x)) (hadd : ∀ x ∈ I, AdditivelyInvariant (q.p.Λ · x))
    (hmem : ∀ x ∈ I, HasMemory Cpast (q.p.Λ · x)) {w : X → ℝ} (hw : q.p.Λ w ≤ w)
    (hΓmono : ∀ x, Monotone (q.p.Γ · x)) (hΓcaus : ∀ x, Causal (q.p.Γ · x))
    (hΓadd : ∀ x ∈ I, AdditivelyInvariant (q.p.Γ · x)) (hΓΛ : ∀ u, q.p.Γ u ≤ q.p.Λ u)
    (hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (q.p.Λ · x) (q.p.Γ · x))
    (hsub : ∀ x ∈ I, SubAdditive q.σ (kruzkovOp q.β (q.p.Λ · x))) (hα : 0 < q.p.α)
    (hαβ : q.p.α ≤ q.β) (hσ0 : 0 < q.σ) (hσ1 : q.σ < 1) (hρ1 : q.p.ρ < 1)
    (hρσ : (1 - q.σ) ^ q.β ≤ (1 - q.p.ρ) ^ q.p.α) (hτ : 0 < q.p.τ) (hε : 0 < q.p.ε)
    (hbd : ∀ x ∉ I, 2 * q.Δmax ≤ ubd x) :
    ∃ uFix : X → ℝ, q.p.Λ uFix = uFix ∧ (∀ v, q.p.Λ v = v → v = uFix) ∧
      (∀ J : Set X, HasComparisonPrinciple J q.p.Λ) ∧
      (q.p.ε ≤ q.εmax uFix →
        anbStopIndex q.p ≤ ((⌈q.nMax uFix⌉₊ + 1 : ℕ) : ℕ∞) ∧
        ((anbRun q.p (anbStopIndex q.p).toNat).uSub ≤
            q.p.Λ (anbRun q.p (anbStopIndex q.p).toNat).uSub ∧
          Global.monotoneExtension q.p.Λ (anbRun q.p (anbStopIndex q.p).toNat).uSup ≤
            (anbRun q.p (anbStopIndex q.p).toNat).uSup ∧
          anbDone q.p (anbRun q.p (anbStopIndex q.p).toNat)) ∧
        (∀ k, (anbRunData q.p k).Δ < q.Δmax) ∧
        (∀ k, (anbRunData q.p k).passesSub ≤ (q.NΛ'' : ℕ∞) ∧
          (anbRunData q.p k).passesSup ≤ (q.NΛ'' : ℕ∞)) ∧
        (∀ (x : X) (S : Finset ℕ), (∀ k ∈ S, x ∈ (anbRunData q.p k).band) →
          S.card ≤ q.NΛ' Cpast CΓ CΓ' uFix) ∧
        (∀ (k : ℕ) (x : X),
          (anbRun q.p k).countSub x ≤ ((q.NΛ' Cpast CΓ CΓ' uFix * q.NΛ'' : ℕ) : ℕ∞) ∧
          (anbRun q.p k).countSup x ≤ ((q.NΛ' Cpast CΓ CΓ' uFix * q.NΛ'' : ℕ) : ℕ∞) ∧
          (anbRun q.p k).countHat x ≤ q.NΓ Cpast CΓ CΓ' uFix)) := by
  have hβ : 0 < q.β := hα.trans_le hαβ
  obtain ⟨uFix, hfix, huniq, -⟩ := ComparisonLambdaProof.existsUnique_fixedPoint_of_kruzkov hβ
    hσ1 hΛmono (hsubAll hΛbd hσ0 hsub) hw
  refine ⟨uFix, hfix, huniq, hasComparisonPrinciple hΛbd hΛmono hβ hσ1 hsub, fun hεmax => ?_⟩
  have h : HypU q I ubd CΓ CΓ' uFix := ⟨hΛbd, hΓbd, hCΓ, hΛmono, hadd, hcmp, hΓmono, hΓcaus,
    hΓadd, hΓΛ, hsub, hα, hαβ, hσ0, hσ1, hρ1, hρσ, hτ, hfix, hε, hεmax, hbd⟩
  have hW := h.toWidth
  have hAS := h.always (anbStopIndex q.p).toNat
  refine ⟨stopIndex_le h, ⟨hAS.uSub_le, hAS.uSup_ge,
      AnbComplexityProof.done_stopIndex ⟨_, done_of hW⟩⟩, Δ_lt h, passes_le h,
    (nGamma h hCpast hCΓ' hmem).2.2.1, fun k x => ?_⟩
  obtain ⟨h1, h2⟩ :=
    AnbNiterProof.countSub_countSup_le_of hW (fun k _ _ => passes_le h k) hCpast hCΓ' hmem k x
  exact ⟨h1, h2, AnbNGammaProof.countHat_le_of hW hCpast hCΓ' hmem k x⟩

end GuaranteedSubsol.AnbWithUnknownProof
