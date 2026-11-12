/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AnbBnCompProof
import LeanHJBAutoformalisation.GuaranteedSubsol.AnbFirstIterProof
import LeanHJBAutoformalisation.GuaranteedSubsol.TAdvancesProof
import LeanHJBAutoformalisation.GuaranteedSubsol.Lambda0SubaddProof
import LeanHJBAutoformalisation.GuaranteedSubsol.ComparisonLambdaProof

/-!
# ANB: Corollary corol:max_width, proofs

Provider proofs for the frozen anchors `GuaranteedSubsol.anbRunData_Δ_lt_Δmax` and
`GuaranteedSubsol.anbRun_done_of_maxWidth`, see `ANCHORS.md`.

* The global iterations on the band `B` stop (`band_subPasses_lt_top`, `band_passes_lt_top`): the
  band operator, acting on the subtype `B`, is monotone and `ρ`-sub-additive (`BandProof`), so that
  the global iteration bound applies; when they stop, the stopping criterion holds on `B`
  (`subResult_of_lt_top`, `result_of_lt_top`).
* The induction is written for a generic threshold `Dm` (`WidthHyp`, `Δ_lt_of`, `done_of`,
  `stopIndex_le_of`), from the termination of the inner loops and the advance property
  (`Advance`), so that it also serves corol:max_width_withUnknown (`AnbWithUnknownProof`).
* `ρ`-sub-additivity gives `Λ[0] ≥ 0` (prop:cst_subsol, item enum:Lambda0_alpha) and the
  comparison principle (prop:comparison_Lambda, applied on `J ∩ Int X`).
* The induction of the paper: if `Δ_k < Δ_max ≤ Δ_{k+1}`, then `Δ_k ≥ Δ_max - τ`, and
  Prop. prop:t_advances applied to `ū_{k+1}`, `u̲_{k+1}` shows `t_{k+1} ≥ t_k + Δ_k / 2`, hence
  `Δ_{k+1} ≤ Δ_k / 2 + τ < Δ_max / 2 + τ ≤ Δ_max` (this uses `Δ_max ≥ 2τ`).
-/

namespace GuaranteedSubsol.AnbMaxWidthProof

open AnbProof AnbBnCompProof

variable {X : Type*}

/-! ### Global iterations on the band -/

section Band

/-- `ρ^n C ≤ η` for some `n`, when `ρ < 1` and `η > 0`. -/
theorem exists_pow_mul_le {ρ η : ℝ} (hρ1 : ρ < 1) (hη : 0 < η) (C : ℝ) :
    ∃ n : ℕ, ρ ^ n * C ≤ η := by
  rcases le_or_gt C 0 with hC | hC
  · exact ⟨0, by simp only [pow_zero, one_mul]; linarith⟩
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hη hC) hρ1
    exact ⟨n, by rw [lt_div_iff₀ hC] at hn; exact hn.le⟩

variable {Φ : (X → ℝ) → X → ℝ} {B : Set X} {w : X → ℝ} {ρ η : ℝ}

/-- A global iteration (sub-solution variant) whose stopping criterion holds at some iterate
performs finitely many passes. -/
theorem subPasses_lt_top {Y : Type*} {Ψ : (Y → ℝ) → Y → ℝ} {η : ℝ} {v : Y → ℝ}
    (h : ∃ n, ∀ y, Ψ (globalIterSubRun Ψ η v n) y - globalIterSubRun Ψ η v n y ≤ η) :
    globalIterSubPasses Ψ η v < ⊤ := by
  classical
  unfold globalIterSubPasses
  simp only [h, ↓reduceDIte]
  exact ENat.natCast_lt_top _

theorem passes_lt_top {Y : Type*} {Ψ : (Y → ℝ) → Y → ℝ} {η : ℝ} {v : Y → ℝ}
    (h : ∃ n, ∀ y, globalIterRun Ψ η v n y - Ψ (globalIterRun Ψ η v n) y ≤ η) :
    globalIterPasses Ψ η v < ⊤ := by
  classical
  unfold globalIterPasses
  simp only [h, ↓reduceDIte]
  exact ENat.natCast_lt_top _

/-- Line anb:while_sub on the band, when `Φ` is `ρ`-sub-additive on the band: the global iteration
bound (`globalIterSubRun_le_pow_mul`), applied to the band operator on the subtype `B`, shows that
the loop stops. -/
theorem band_subPasses_lt_top [Finite X] (hmono : ∀ x ∈ B, Monotone (Φ · x))
    (hsub : ∀ x ∈ B, SubAdditive ρ (Φ · x)) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hη : 0 < η)
    (hv : ∀ x ∈ B, w x ≤ Φ w x) : globalIterSubPasses (bandOp Φ B w) η (fun y => w y) < ⊤ := by
  classical
  have := Fintype.ofFinite X
  have hΨ : Monotone (bandOp Φ B w) := BandProof.monotone_bandOp hmono
  have hsubΨ : ∀ y : B, SubAdditive ρ (bandOp Φ B w · y) := fun y =>
    BandProof.subAdditive_bandOp y.2 (hmono y y.2) (hsub y y.2)
  have hr0 : (fun y : B => w y) ≤ bandOp Φ B w fun y => w y := fun y => by
    change w y ≤ Φ (bandExtend B w fun y => w y) y
    rw [bandExtend_restrict]
    exact hv y y.2
  set C : ℝ := ∑ y, |Φ w y - w y|
  have hvC : ∀ y : B, bandOp Φ B w (fun y => w y) y - w y ≤ C := fun y => by
    change Φ (bandExtend B w fun y => w y) y - w y ≤ C
    rw [bandExtend_restrict]
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun z => |Φ w z - w z|)
      (fun z _ => abs_nonneg _) (Finset.mem_univ (y : X)))
  obtain ⟨n, hn⟩ := exists_pow_mul_le hρ1 hη C
  exact subPasses_lt_top ⟨n, fun y =>
    (GlobalIterationProof.subRun_le_pow_mul hΨ hρ0 hsubΨ η hr0 hvC n y).trans (max_le hn le_rfl)⟩

/-- Line anb:while_sup on the band, super-solution version of `band_subPasses_lt_top`. -/
theorem band_passes_lt_top [Finite X] (hmono : ∀ x ∈ B, Monotone (Φ · x))
    (hsub : ∀ x ∈ B, SubAdditive ρ (Φ · x)) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hη : 0 < η)
    (hv : ∀ x ∈ B, Φ w x ≤ w x) : globalIterPasses (bandOp Φ B w) η (fun y => w y) < ⊤ := by
  classical
  have := Fintype.ofFinite X
  have hΨ : Monotone (bandOp Φ B w) := BandProof.monotone_bandOp hmono
  have hsubΨ : ∀ y : B, SubAdditive ρ (bandOp Φ B w · y) := fun y =>
    BandProof.subAdditive_bandOp y.2 (hmono y y.2) (hsub y y.2)
  have hr0 : (bandOp Φ B w fun y : B => w y) ≤ fun y : B => w y := fun y => by
    change Φ (bandExtend B w fun y => w y) y ≤ w y
    rw [bandExtend_restrict]
    exact hv y y.2
  set C : ℝ := ∑ y, |w y - Φ w y|
  have hvC : ∀ y : B, w y - bandOp Φ B w (fun y => w y) y ≤ C := fun y => by
    change w y - Φ (bandExtend B w fun y => w y) y ≤ C
    rw [bandExtend_restrict]
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun z => |w z - Φ w z|)
      (fun z _ => abs_nonneg _) (Finset.mem_univ (y : X)))
  obtain ⟨n, hn⟩ := exists_pow_mul_le hρ1 hη C
  exact passes_lt_top ⟨n, fun y =>
    (GlobalIterationProof.le_pow_mul hΨ hρ0 hsubΨ η hr0 hvC n y).trans (max_le hn le_rfl)⟩

end Band

/-! ### Consequences of `ρ`-sub-additivity -/

/-- `Φ_α` of an operator with constant values is constant, hence `ρ`-sub-additive. -/
theorem subAdditive_kruzkovOp_const {Λ : (X → ℝ) → ℝ} {c : ℝ} (hc : ∀ u, Λ u = c) {α ρ : ℝ}
    (hρ : 0 ≤ ρ) : SubAdditive ρ (kruzkovOp α Λ) := by
  have hconst : ∀ v, kruzkovOp α Λ v = kruzkov (1 / α) (c : WithTop ℝ) := fun v => by
    unfold kruzkovOp monotoneExtension
    have := KruzkovProof.nonempty_minorant fun y => kruzkovInv α (v y)
    simp only [hc, ciSup_const]
  intro v t ht
  rw [hconst, hconst]
  linarith [mul_nonneg hρ ht]

/-- `Λ[0] ≥ 0`, from `ρ`-sub-additivity on `Int X` (prop:cst_subsol, item enum:Lambda0_alpha) and
`u_bd ≥ 0`. -/
theorem apply_zero_nonneg {Λ : (X → ℝ) → X → ℝ} {I : Set X} {ubd : X → ℝ}
    (hΛbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) (hubd : ∀ x ∉ I, 0 ≤ ubd x)
    (hΛmono : ∀ x, Monotone (Λ · x)) (hadd : ∀ x ∈ I, AdditivelyInvariant (Λ · x)) {α ρ : ℝ}
    (hα : 0 < α) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hsub : ∀ x ∈ I, SubAdditive ρ (kruzkovOp α (Λ · x))) : 0 ≤ Λ 0 := fun x => by
  by_cases hx : x ∈ I
  · have h := Lambda0SubaddProof.le_apply_zero_of_kruzkov_subAdditive hα (hΛmono x)
      (hadd x hx) (hsub x hx)
    have hlog : Real.log ρ ≤ 0 := Real.log_nonpos hρ0 hρ1.le
    have : 0 ≤ -α * Real.log ρ := by nlinarith
    exact this.trans h
  · rw [Pi.zero_apply, hΛbd 0 x hx]
    exact hubd x hx

/-- The comparison principle on any partition, from `ρ`-sub-additivity on `Int X`
(prop:comparison_Lambda, applied on `J ∩ Int X`; at boundary points the values are prescribed). -/
theorem hasComparisonPrinciple [Finite X] {Λ : (X → ℝ) → X → ℝ} {I : Set X} {ubd : X → ℝ}
    (hΛbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) (hΛmono : ∀ x, Monotone (Λ · x)) {α ρ : ℝ}
    (hα : 0 < α) (hρ1 : ρ < 1) (hsub : ∀ x ∈ I, SubAdditive ρ (kruzkovOp α (Λ · x)))
    (J : Set X) : HasComparisonPrinciple J Λ := by
  intro u v hu hv hbd
  refine ComparisonLambdaProof.le_of_subSolution_superSolution (I := J ∩ I) hα hρ1
    (fun x _ => hΛmono x) (fun x hx => hsub x hx.2) (fun x hx => hu x hx.1)
    (fun x hx => hv x hx.1) (fun x hx => ?_)
  by_cases hxJ : x ∈ J
  · have hxI : x ∉ I := fun h => hx ⟨hxJ, h⟩
    have h1 := hu x hxJ
    have h2 := hv x hxJ
    rw [hΛbd u x hxI] at h1
    rw [hΛbd v x hxI] at h2
    linarith
  · exact hbd x hxJ

/-! ### The level `t_n` -/

theorem anbLevel_le_of_mem [Fintype X] {ε T : ℝ} {uHat : X → ℝ} {uSup : X → WithTop ℝ} {x : X}
    (hx : (((1 + ε) * uHat x : ℝ) : WithTop ℝ) < uSup x) : anbLevel ε T uHat uSup ≤ uHat x := by
  classical
  have hmem : x ∈ Finset.univ.filter fun y => (((1 + ε) * uHat y : ℝ) : WithTop ℝ) < uSup y :=
    Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩
  unfold anbLevel
  dsimp only
  split_ifs with hS
  · exact (min_le_right _ _).trans (Finset.inf'_le uHat hmem)
  · exact absurd ⟨x, hmem⟩ hS

theorem le_anbLevel [Fintype X] {ε T c : ℝ} {uHat : X → ℝ} {uSup : X → WithTop ℝ} (hcT : c ≤ T)
    (h : ∀ x, (((1 + ε) * uHat x : ℝ) : WithTop ℝ) < uSup x → c ≤ uHat x) :
    c ≤ anbLevel ε T uHat uSup := by
  classical
  unfold anbLevel
  dsimp only
  split_ifs with hS
  · exact le_min hcT (Finset.le_inf' _ _ fun x hx => h x (Finset.mem_filter.1 hx).2)
  · exact hcT

theorem exists_of_anbLevel_lt [Fintype X] {ε T : ℝ} {uHat : X → ℝ} {uSup : X → WithTop ℝ}
    (h : anbLevel ε T uHat uSup < T) : ∃ x, (((1 + ε) * uHat x : ℝ) : WithTop ℝ) < uSup x := by
  by_contra hno
  push Not at hno
  exact absurd h (not_lt.2 (le_anbLevel le_rfl fun x hx => absurd hx (not_lt.2 (hno x))))

/-- `E_α a · exp(-ε a / α) = E_α ((1 + ε) a)`. -/
theorem kruzkov_mul_exp (α ε a : ℝ) :
    kruzkov (1 / α) (a : WithTop ℝ) * Real.exp (-ε * (1 / α) * a) =
      kruzkov (1 / α) (((1 + ε) * a : ℝ) : WithTop ℝ) := by
  change -Real.exp (-(1 / α) * a) * Real.exp (-ε * (1 / α) * a) =
    -Real.exp (-(1 / α) * ((1 + ε) * a))
  rw [neg_mul, ← Real.exp_add]
  congr 2
  ring

/-! ### The hypotheses of corol:max_width -/

variable [Fintype X] [LinearOrder X]

/-- The hypotheses of Corollary corol:max_width (see the anchors). -/
structure Hyp (p : AnbParams X) (I : Set X) (ubd : X → ℝ) (CΓ CΓ' : ℝ) (uFix : X → ℝ) :
    Prop where
  hΛbd : ∀ u, ∀ x ∉ I, p.Λ u x = ubd x
  hΓbd : ∀ u, ∀ x ∉ I, p.Γ u x = ubd x
  hCΓ : 1 ≤ CΓ
  hΛmono : ∀ x, Monotone (p.Λ · x)
  hadd : ∀ x ∈ I, AdditivelyInvariant (p.Λ · x)
  hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (p.Λ · x) (p.Γ · x)
  hΓmono : ∀ x, Monotone (p.Γ · x)
  hΓcaus : ∀ x, Causal (p.Γ · x)
  hΓadd : ∀ x ∈ I, AdditivelyInvariant (p.Γ · x)
  hΓΛ : ∀ u, p.Γ u ≤ p.Λ u
  hsub : ∀ x ∈ I, SubAdditive p.ρ (kruzkovOp p.α (p.Λ · x))
  hα : 0 < p.α
  hρ0 : 0 ≤ p.ρ
  hρ1 : p.ρ < 1
  hτ : 0 < p.τ
  hfix : p.Λ uFix = uFix
  hε : 0 < p.ε
  hεmax : p.ε ≤ p.εmax uFix
  hbd : ∀ x ∉ I, 2 * p.Δmax ≤ ubd x

namespace Hyp

variable {p : AnbParams X} {I : Set X} {ubd : X → ℝ} {CΓ CΓ' : ℝ} {uFix : X → ℝ}

omit [LinearOrder X] in
theorem log_ge_one (h : Hyp p I ubd CΓ CΓ' uFix) : 1 ≤ Real.log (2 * Real.exp 1 / p.ε) := by
  have hε2 : p.ε ≤ 2 := h.hεmax.trans (min_le_right _ _)
  rw [Real.le_log_iff_exp_le (div_pos (by positivity) h.hε), le_div_iff₀ h.hε]
  nlinarith [Real.exp_pos 1]

omit [Fintype X] [LinearOrder X] in
theorem Δmax_eq (p : AnbParams X) :
    p.Δmax = 2 * p.α * Real.log (2 * Real.exp 1 / p.ε) + 2 * p.τ := rfl

omit [LinearOrder X] in
theorem Δmax_pos (h : Hyp p I ubd CΓ CΓ' uFix) : 0 < p.Δmax := by
  have := mul_pos (mul_pos two_pos h.hα) (lt_of_lt_of_le one_pos h.log_ge_one)
  rw [Δmax_eq]
  linarith [h.hτ]

omit [LinearOrder X] in
theorem ubd_nonneg (h : Hyp p I ubd CΓ CΓ' uFix) : ∀ x ∉ I, 0 ≤ ubd x := fun x hx => by
  linarith [h.hbd x hx, h.Δmax_pos]

omit [LinearOrder X] in
theorem apply_zero (h : Hyp p I ubd CΓ CΓ' uFix) : 0 ≤ p.Λ 0 :=
  apply_zero_nonneg h.hΛbd h.ubd_nonneg h.hΛmono h.hadd h.hα h.hρ0 h.hρ1 h.hsub

omit [LinearOrder X] in
theorem comp (h : Hyp p I ubd CΓ CΓ' uFix) (J : Set X) : HasComparisonPrinciple J p.Λ :=
  hasComparisonPrinciple h.hΛbd h.hΛmono h.hα h.hρ1 h.hsub J

theorem always {S : AnbInnerSolver X} [S.Valid] (h : Hyp p I ubd CΓ CΓ' uFix) (k : ℕ) :
    AnbAlwaysSubsolWith S p (anbRunWith S p k) :=
  always_subsol h.hΛmono h.apply_zero h.hΓmono h.hΓcaus h.hΓΛ h.hα h.hτ.le k

theorem uHat_le {S : AnbInnerSolver X} [S.Valid] (h : Hyp p I ubd CΓ CΓ' uFix) (k : ℕ) :
    (anbRunDataWith S p k).uHat ≤ uFix :=
  uHat_le_uFix h.hΛmono h.apply_zero h.hΓmono h.hΓcaus h.hΓΛ h.comp h.hfix h.hα h.hτ.le k

omit [LinearOrder X] in
theorem le_norm (uFix : X → ℝ) (x : X) : uFix x ≤ ‖uFix‖ :=
  (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm uFix x)

omit [LinearOrder X] in
theorem hsubB (h : Hyp p I ubd CΓ CΓ' uFix) (B : Set X) :
    ∀ x ∈ B, SubAdditive p.ρ (fun v => Global.kruzkovOp p.α p.Λ v x) := fun x _ => by
  by_cases hx : x ∈ I
  · exact h.hsub x hx
  · exact subAdditive_kruzkovOp_const (fun u => h.hΛbd u x hx) h.hρ0

end Hyp

/-! ### The induction, for a generic width threshold -/

/-- The advance property of Prop. prop:t_advances (or prop:t_advances_withUnknown), for the
parameters `α`, `ρ`, `ε` of algo:anb, the width condition being `Δ ≥ Δ_max - τ`. -/
def Advance (p : AnbParams X) (Dm : ℝ) : Prop :=
  ∀ (uSub vsub vsup : X → ℝ) (Tm Tp ξ t Δ : ℝ),
    (∀ x, vsub x = kruzkov (1 / p.α) (uSub x)) → (∀ x, vsup x ≤ 0) → 0 ≤ Tm → 0 ≤ ξ →
    t = (Tp + Tm) / 2 → Δ = (Tp - Tm) / 2 →
    (∀ x, Tm ≤ uSub x → uSub x < Tp →
      -((1 - p.ρ) * ξ) ≤ vsub x - kruzkovOp p.α (p.Λ · x) vsub) →
    (∀ x, Tm ≤ uSub x → uSub x < Tp → vsup x - kruzkovOp p.α (p.Λ · x) vsup ≤ (1 - p.ρ) * ξ) →
    (∀ x, Tp ≤ uSub x → -ξ ≤ vsub x) →
    (∀ x, uSub x < Tm → vsup x ≤ vsub x * Real.exp (-p.ε * (1 / p.α) * uSub x)) →
    ξ ≤ Real.exp (-(1 / p.α) * Tp) → p.ε * Tp ≤ p.α → Dm - p.τ ≤ Δ →
    ∀ x, t - Δ / 2 ≤ uSub x → uSub x ≤ t + Δ / 2 →
      vsup x ≤ vsub x * Real.exp (-p.ε * (1 / p.α) * uSub x)

/-- The ingredients of the proof of Corollary corol:max_width, for a width threshold `Dm`
(`Δ_max`): the parts of assum:all, `Λ[0] ≥ 0` and the comparison principle, the termination of the
inner loops, and the advance property. -/
structure WidthHyp (S : AnbInnerSolver X) (p : AnbParams X) (I : Set X) (ubd : X → ℝ)
    (CΓ CΓ' : ℝ) (uFix : X → ℝ)
    (Dm : ℝ) : Prop where
  hΛbd : ∀ u, ∀ x ∉ I, p.Λ u x = ubd x
  hΓbd : ∀ u, ∀ x ∉ I, p.Γ u x = ubd x
  hCΓ : 1 ≤ CΓ
  hΛmono : ∀ x, Monotone (p.Λ · x)
  hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (p.Λ · x) (p.Γ · x)
  hΓmono : ∀ x, Monotone (p.Γ · x)
  hΓcaus : ∀ x, Causal (p.Γ · x)
  hΓadd : ∀ x ∈ I, AdditivelyInvariant (p.Γ · x)
  hΓΛ : ∀ u, p.Γ u ≤ p.Λ u
  hΛ0 : 0 ≤ p.Λ 0
  hcomp : ∀ J : Set X, HasComparisonPrinciple J p.Λ
  hα : 0 < p.α
  hρ1 : p.ρ < 1
  hτ : 0 < p.τ
  hfix : p.Λ uFix = uFix
  hε : 0 < p.ε
  hεα : p.ε ≤ p.α / (‖uFix‖ + Dm)
  hDm : 2 * p.τ < Dm
  hbd : ∀ x ∉ I, 2 * Dm ≤ ubd x
  hterm : ∀ k, ∀ x ∈ (anbRunDataWith S p k).band,
    anbSubCount S p (anbRunWith S p k) x < ⊤ ∧ anbSupCount S p (anbRunWith S p k) x < ⊤
  hadv : Advance p Dm
  hadd : ∀ x ∈ I, AdditivelyInvariant (p.Λ · x)

namespace WidthHyp

variable {S : AnbInnerSolver X} [S.Valid] {p : AnbParams X} {I : Set X} {ubd : X → ℝ}
  {CΓ CΓ' : ℝ} {uFix : X → ℝ} {Dm : ℝ}

theorem always (h : WidthHyp S p I ubd CΓ CΓ' uFix Dm) (k : ℕ) :
    AnbAlwaysSubsolWith S p (anbRunWith S p k) :=
  always_subsol (S := S) h.hΛmono h.hΛ0 h.hΓmono h.hΓcaus h.hΓΛ h.hα h.hτ.le k

omit [S.Valid] in
theorem Dm_pos (h : WidthHyp S p I ubd CΓ CΓ' uFix Dm) : 0 < Dm := by
  linarith [h.hDm, h.hτ]

theorem uHat_le (h : WidthHyp S p I ubd CΓ CΓ' uFix Dm) (k : ℕ) :
    (anbRunDataWith S p k).uHat ≤ uFix :=
  uHat_le_uFix (S := S) h.hΛmono h.hΛ0 h.hΓmono h.hΓcaus h.hΓΛ h.hcomp h.hfix h.hα h.hτ.le k

end WidthHyp

variable {S : AnbInnerSolver X} [S.Valid] {p : AnbParams X} {I : Set X} {ubd : X → ℝ}
  {CΓ CΓ' : ℝ} {uFix : X → ℝ} {Dm : ℝ}

/-- If `Δ_k < Δ_max`, then `Δ_{k+1} < Δ_max`. -/
theorem width_step (h : WidthHyp S p I ubd CΓ CΓ' uFix Dm) {k : ℕ}
    (hk : (anbRunDataWith S p k).Δ < Dm) : (anbRunDataWith S p (k + 1)).Δ < Dm := by
  classical
  by_contra hcon
  push Not at hcon
  have hα := h.hα
  have hDm := h.hDm
  set s := anbRunWith S p k with hs
  set d := anbStepData p s with hd
  have hdk : anbRunDataWith S p k = d := rfl
  set s' := anbStepWith S p s with hs'
  have hrun' : anbRunWith S p (k + 1) = s' := anbRun_succ p k
  set d' := anbStepData p s' with hd'
  have hdk' : anbRunDataWith S p (k + 1) = d' := by rw [anbRunDataWith_def, hrun']
  rw [hdk] at hk
  rw [hdk'] at hcon
  have hAS := h.always k
  have hAS' := h.always (k + 1)
  rw [hrun'] at hAS'
  have hn : (s.n : ℝ) = k := by rw [hs, anbRun_n]
  have hn' : (s'.n : ℝ) = k + 1 := by
    change ((s.n + 1 : ℕ) : ℝ) = _
    push_cast
    rw [hn]
  set T : ℝ := k * p.τ with hT
  have hT1 : ((k : ℝ) + 1) * p.τ = T + p.τ := by rw [hT]; ring
  have ht : d.t = anbLevel p.ε T d.uHat s.uSup := by rw [hd, anbStepData_t, hn]
  have ht' : d'.t = anbLevel p.ε (((k : ℝ) + 1) * p.τ) d'.uHat s'.uSup := by
    rw [hd', anbStepData_t, hn']
  have hΔ : d.Δ = T - d.t := by rw [hd, anbStepData_Δ, hn]
  have hΔ' : d'.Δ = ((k : ℝ) + 1) * p.τ - d'.t := by rw [hd', anbStepData_Δ, hn']
  have htT : d.t ≤ T := by rw [ht]; exact anbLevel_le _ _ _ _
  -- monotonicity along the run (Prop. prop:always_subsol)
  have h1 : d.uHat ≤ s'.uSub := hAS.uHat_le_uSub_step
  have h2 : s'.uSub ≤ d'.uHat := hAS'.uSub_le_uHat
  have h3 : s'.uSup ≤ s.uSup := hAS.uSup_step_le
  have h1ε : 0 ≤ 1 + p.ε := by linarith [h.hε]
  -- `E_{k+1} ⊂ E_k ⊂ {û_k ≥ t_k}`
  have hE : ∀ x, (((1 + p.ε) * d'.uHat x : ℝ) : WithTop ℝ) < s'.uSup x →
      (((1 + p.ε) * d.uHat x : ℝ) : WithTop ℝ) < s.uSup x := fun x hx =>
    lt_of_le_of_lt (WithTop.coe_le_coe.2 (mul_le_mul_of_nonneg_left ((h1 x).trans (h2 x)) h1ε))
      (hx.trans_le (h3 x))
  have hEt : ∀ x, (((1 + p.ε) * d'.uHat x : ℝ) : WithTop ℝ) < s'.uSup x → d.t ≤ d.uHat x :=
    fun x hx => by rw [ht]; exact anbLevel_le_of_mem (hE x hx)
  -- `t_{k+1} ≥ t_k`, hence `Δ_k ≥ Δ_{k+1} - τ ≥ Δ_max - τ > 0`
  have htt : d.t ≤ d'.t := by
    rw [ht']
    exact le_anbLevel (by linarith [h.hτ]) fun x hx => (hEt x hx).trans ((h1 x).trans (h2 x))
  have hΔlow : Dm - p.τ ≤ d.Δ := by linarith
  have hΔpos : 0 < d.Δ := by linarith [h.hτ]
  -- `k ≥ 1`, since iteration `0` is vacuous
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    have h0 : (anbRunDataWith S p k).Δ = 0 := hk0' ▸ (zero_vacuous (S := S) p).2.2.1
    rw [hdk] at h0
    linarith
  -- some boundary value is below `kτ` (lem:first_iter), hence `T⁻ = t_k - Δ_k ≥ 0`
  have hbdpt : ∃ x0, x0 ∉ I ∧ ubd x0 < T := by
    by_contra hno
    push Not at hno
    have hfi := AnbFirstIterProof.first_iter (S := S) h.hΓbd h.hCΓ h.hΛ0 h.hΓadd h.hcmp
      h.hΓmono hα h.hτ.le hk1 hno
    have h0 : (anbRunDataWith S p k).Δ = 0 := hfi.2.2.2.2.1
    rw [hdk] at h0
    linarith
  obtain ⟨x0, hx0I, hx0⟩ := hbdpt
  have hTm : 0 ≤ d.t - d.Δ := by linarith [h.hbd x0 hx0I]
  -- `t_k < kτ`, so `E_k ≠ ∅` and `T⁺ = kτ < ‖u_*‖ + Δ_max`
  obtain ⟨x1, hx1⟩ := exists_of_anbLevel_lt (show anbLevel p.ε T d.uHat s.uSup < T by
    rw [← ht]; linarith)
  have hx1t : d.t ≤ d.uHat x1 := by rw [ht]; exact anbLevel_le_of_mem hx1
  have hu1 : d.uHat x1 ≤ uFix x1 := h.uHat_le k x1
  have hTp : T < ‖uFix‖ + Dm := by linarith [Hyp.le_norm uFix x1]
  have hεT : p.ε * T ≤ p.α := by
    have hden : 0 < ‖uFix‖ + Dm := by linarith [norm_nonneg uFix, h.hτ]
    have hεα : p.ε ≤ p.α / (‖uFix‖ + Dm) := h.hεα
    rw [le_div_iff₀ hden] at hεα
    nlinarith [h.hε]
  -- the global iterations on the band stop
  have hhat : d.uHat ≤ p.Λ d.uHat := hAS.uHat_le
  have hη : 0 < d.η := by
    rw [hd, anbStepData_η]
    exact mul_pos (by linarith [h.hρ1]) (Real.exp_pos _)
  set w := wSub S p s with hw
  obtain ⟨-, -, hwneg⟩ := subRun_props S h.hΛmono hα d.band hhat d.η
  have hwres : ∀ x ∈ d.band, kruzkovOp p.α (p.Λ · x) w - w x ≤ d.η := fun x hx => by
    have hcrit := AnbInnerSolver.Valid.subResult_crit d.band d.ΦSub d.η (fun x => d.vSub x)
      (fun y hy => (h.hterm k y hy).1) ⟨x, hx⟩
    have e : w x = S.subResult d.band d.ΦSub d.η (fun x => d.vSub x) ⟨x, hx⟩ :=
      bandExtend_of_mem _ _ _ hx
    rw [e]
    exact hcrit
  have hwu : ∀ x, kruzkov (1 / p.α) ((s'.uSub x : ℝ) : WithTop ℝ) = w x := fun x =>
    ComparisonLambdaProof.kruzkov_coe_log hα.ne' (hwneg x)
  set z := wSup S p s with hz
  obtain ⟨hz0, -⟩ := supRun_props S hα d.band hAS.uSup_ge d.η
  have hzres : ∀ x ∈ d.band, z x - kruzkovOp p.α (p.Λ · x) z ≤ d.η := fun x hx => by
    have hcrit := AnbInnerSolver.Valid.supResult_crit d.band d.ΦSup d.η (fun x => d.vSup x)
      (fun y hy => (h.hterm k y hy).2) ⟨x, hx⟩
    have e : z x = S.supResult d.band d.ΦSup d.η (fun x => d.vSup x) ⟨x, hx⟩ :=
      bandExtend_of_mem _ _ _ hx
    rw [e]
    exact hcrit
  have hzu : ∀ x, kruzkov (1 / p.α) (s'.uSup x) = z x := fun x =>
    kruzkov_kruzkovInv hα.ne' ((hz0 x).trans (kruzkov_nonpos _ _))
  have hband : ∀ x, x ∈ d.band ↔ d.t - d.Δ ≤ d.uHat x ∧ d.uHat x < T := fun x => by
    rw [mem_band_iff p s x, AnbStepData.tMinus_def, hn]
  have hη_eq : d.η = (1 - p.ρ) * Real.exp (-(1 / p.α) * T) := by
    rw [hd, anbStepData_η, hn]
    congr 2
    ring
  have hinB : ∀ x, d.t - d.Δ ≤ s'.uSub x → s'.uSub x < T → x ∈ d.band := fun x ha hb => by
    by_contra hxB
    have e1 := (eq_of_notMem_band (S := S) hα hxB).1
    rw [e1] at ha hb
    exact hxB ((hband x).2 ⟨ha, hb⟩)
  -- the assumptions of Prop. prop:t_advances
  have hvw : (fun x => kruzkov (1 / p.α) ((s'.uSub x : ℝ) : WithTop ℝ)) = w := funext hwu
  have hvz : (fun x => kruzkov (1 / p.α) (s'.uSup x)) = z := funext hzu
  have ha1 : ∀ x, d.t - d.Δ ≤ s'.uSub x → s'.uSub x < T →
      -((1 - p.ρ) * Real.exp (-(1 / p.α) * T)) ≤
        kruzkov (1 / p.α) ((s'.uSub x : ℝ) : WithTop ℝ) -
          kruzkovOp p.α (p.Λ · x) (fun x => kruzkov (1 / p.α) ((s'.uSub x : ℝ) : WithTop ℝ)) := by
    intro x ha hb
    have hxB := hinB x ha hb
    rw [hvw, hwu x, ← hη_eq]
    linarith [hwres x hxB]
  have ha2 : ∀ x, d.t - d.Δ ≤ s'.uSub x → s'.uSub x < T →
      kruzkov (1 / p.α) (s'.uSup x) -
          kruzkovOp p.α (p.Λ · x) (fun x => kruzkov (1 / p.α) (s'.uSup x)) ≤
        (1 - p.ρ) * Real.exp (-(1 / p.α) * T) := by
    intro x ha hb
    have hxB := hinB x ha hb
    rw [hvz, hzu x, ← hη_eq]
    exact hzres x hxB
  have hb : ∀ x, T ≤ s'.uSub x →
      -Real.exp (-(1 / p.α) * T) ≤ kruzkov (1 / p.α) ((s'.uSub x : ℝ) : WithTop ℝ) := by
    intro x hx
    change -Real.exp (-(1 / p.α) * T) ≤ -Real.exp (-(1 / p.α) * s'.uSub x)
    exact neg_le_neg (Real.exp_le_exp.2
      (mul_le_mul_of_nonpos_left hx (neg_nonpos.2 (one_div_pos.2 hα).le)))
  have hc : ∀ x, s'.uSub x < d.t - d.Δ →
      kruzkov (1 / p.α) (s'.uSup x) ≤
        kruzkov (1 / p.α) ((s'.uSub x : ℝ) : WithTop ℝ) *
          Real.exp (-p.ε * (1 / p.α) * s'.uSub x) := by
    intro x hx
    have hxB : x ∉ d.band := fun hxB =>
      absurd ((hband x).1 hxB).1 (not_le.2 ((h1 x).trans_lt hx))
    obtain ⟨e1, e2⟩ := eq_of_notMem_band (S := S) hα hxB
    rw [e1] at hx ⊢
    rw [e2, kruzkov_mul_exp, kruzkov_le_iff hα]
    have hlt : d.uHat x < anbLevel p.ε T d.uHat s.uSup := by rw [← ht]; linarith
    exact le_of_lt_anbLevel hlt
  have hR := h.hadv s'.uSub (fun x => kruzkov (1 / p.α) ((s'.uSub x : ℝ) : WithTop ℝ))
    (fun x => kruzkov (1 / p.α) (s'.uSup x)) (d.t - d.Δ) T (Real.exp (-(1 / p.α) * T)) d.t d.Δ
    (fun x => rfl) (fun x => kruzkov_nonpos _ _) hTm (Real.exp_pos _).le (by linarith)
    (by linarith) ha1 ha2 hb hc le_rfl hεT hΔlow
  -- on `E_{k+1}`, `û_{k+1} > t_k + Δ_k / 2`, hence `t_{k+1} ≥ t_k + Δ_k / 2`
  have hnew : ∀ x, (((1 + p.ε) * d'.uHat x : ℝ) : WithTop ℝ) < s'.uSup x →
      d.t + d.Δ / 2 ≤ d'.uHat x := by
    intro x hx
    have hge : d.t ≤ s'.uSub x := (hEt x hx).trans (h1 x)
    by_contra hcx
    push Not at hcx
    have hle : s'.uSub x ≤ d.t + d.Δ / 2 := (h2 x).trans hcx.le
    have hRx := hR x (by linarith) hle
    rw [kruzkov_mul_exp, kruzkov_le_iff hα] at hRx
    have : s'.uSup x ≤ (((1 + p.ε) * d'.uHat x : ℝ) : WithTop ℝ) :=
      hRx.trans (WithTop.coe_le_coe.2 (mul_le_mul_of_nonneg_left (h2 x) h1ε))
    exact absurd hx (not_lt.2 this)
  have ht'ge : d.t + d.Δ / 2 ≤ d'.t := by
    rw [ht']
    exact le_anbLevel (by linarith [h.hτ]) hnew
  -- `Δ_{k+1} ≤ Δ_k / 2 + τ < Δ_max / 2 + τ ≤ Δ_max`, a contradiction
  linarith

/-- Corollary corol:max_width, first claim, for a generic width threshold. -/
theorem Δ_lt_of (h : WidthHyp S p I ubd CΓ CΓ' uFix Dm) (k : ℕ) :
    (anbRunDataWith S p k).Δ < Dm := by
  induction k with
  | zero =>
    have h0 : (anbRunDataWith S p 0).Δ = 0 := (zero_vacuous (S := S) p).2.2.1
    rw [h0]
    linarith [h.hτ, h.hDm]
  | succ k ih => exact width_step h ih

/-- Corollary corol:max_width, second claim, for a generic width threshold. -/
theorem done_of (h : WidthHyp S p I ubd CΓ CΓ' uFix Dm) :
    anbDone p (anbRunWith S p (⌈(‖uFix‖ + Dm) / p.τ⌉₊ + 1)) := by
  set K := ⌈(‖uFix‖ + Dm) / p.τ⌉₊ with hK
  have hAS := h.always K
  have hnot : ∀ x, ¬(((1 + p.ε) * (anbRunDataWith S p K).uHat x : ℝ) : WithTop ℝ) <
      (anbRunWith S p K).uSup x := by
    intro x hx
    have hlev : (anbRunDataWith S p K).t ≤ (anbRunDataWith S p K).uHat x := anbLevel_le_of_mem hx
    have hu : (anbRunDataWith S p K).uHat x ≤ uFix x := h.uHat_le K x
    have hΔ : (anbRunDataWith S p K).Δ = (K : ℝ) * p.τ - (anbRunDataWith S p K).t := by
      rw [anbRunDataWith_def, anbStepData_Δ, anbRun_n]
    have hlt := Δ_lt_of h K
    have hceil : (‖uFix‖ + Dm) / p.τ ≤ K := Nat.le_ceil _
    have hKτ : ‖uFix‖ + Dm ≤ (K : ℝ) * p.τ := by rwa [div_le_iff₀ h.hτ] at hceil
    linarith [Hyp.le_norm uFix x]
  intro x
  rw [anbRun_succ]
  have h1 := not_lt.1 (hnot x)
  have h1ε : 0 ≤ 1 + p.ε := by linarith [h.hε]
  exact (hAS.uSup_step_le x).trans (h1.trans (WithTop.coe_le_coe.2
    (mul_le_mul_of_nonneg_left (hAS.uHat_le_uSub_step x) h1ε)))

/-- Corollary corol:max_width, termination, for a generic width threshold. -/
theorem stopIndex_le_of (h : WidthHyp S p I ubd CΓ CΓ' uFix Dm) :
    anbStopIndexWith S p ≤ ((⌈(‖uFix‖ + Dm) / p.τ⌉₊ + 1 : ℕ) : ℕ∞) := by
  classical
  have hd := done_of h
  have hex : ∃ k, anbDone p (anbRunWith S p k) := ⟨_, hd⟩
  unfold anbStopIndexWith
  simp only [hex, ↓reduceDIte, Nat.cast_le]
  convert Nat.find_min' hex hd

/-! ### The known parameters: `Φ_α` is `ρ`-sub-additive -/

omit [LinearOrder X] in
/-- The advance property under the hypotheses of Corollary corol:max_width: Prop. prop:t_advances
with `C = 1`, `Δ_max = 2α ln(2e/ε) + 2τ`. -/
theorem Hyp.advance (h : Hyp p I ubd CΓ CΓ' uFix) : Advance p p.Δmax := by
  have hα := h.hα
  have hL := h.log_ge_one
  intro uSub vsub vsup Tm Tp ξ t Δ hvsub hvsup hTm hξ ht hΔ ha1 ha2 hb hc hξT hεT hΔl
  have hΔl' : 2 * p.α * max 1 (Real.log (2 * Real.exp 1 * 1 / p.ε)) ≤ Δ := by
    rw [mul_one, max_eq_right hL]
    have := Hyp.Δmax_eq p
    linarith [h.hτ]
  exact TAdvancesProof.t_advances (Λ := p.Λ) h.hΛbd (αinv := 1 / p.α) hα
    (mul_one_div_cancel hα.ne') h.hρ0 h.hρ1 h.hadd h.hsub hvsub hvsup hTm hξ h.hε le_rfl ht
    hΔ ha1 ha2 hb hc (by rw [one_mul]; exact hξT) hεT hΔl'

/-- The hypotheses of Corollary corol:max_width give the ingredients `WidthHyp`, with
`Δ_max = 2α ln(2e/ε) + 2τ`, for any valid inner solver whose loops stop. -/
theorem Hyp.toWidthOf {S : AnbInnerSolver X} [S.Valid] (h : Hyp p I ubd CΓ CΓ' uFix)
    (hterm : ∀ k, ∀ x ∈ (anbRunDataWith S p k).band,
      anbSubCount S p (anbRunWith S p k) x < ⊤ ∧ anbSupCount S p (anbRunWith S p k) x < ⊤) :
    WidthHyp S p I ubd CΓ CΓ' uFix p.Δmax := by
  have hα := h.hα
  have hL := h.log_ge_one
  have hαL : 0 < 2 * p.α * Real.log (2 * Real.exp 1 / p.ε) :=
    mul_pos (mul_pos two_pos hα) (lt_of_lt_of_le one_pos hL)
  exact ⟨h.hΛbd, h.hΓbd, h.hCΓ, h.hΛmono, h.hcmp, h.hΓmono, h.hΓcaus, h.hΓadd, h.hΓΛ,
    h.apply_zero, h.comp, hα, h.hρ1, h.hτ, h.hfix, h.hε, h.hεmax.trans (min_le_left _ _),
    by rw [Hyp.Δmax_eq]; linarith, h.hbd, hterm, h.advance, h.hadd⟩

/-- The hypotheses of Corollary corol:max_width give the ingredients `WidthHyp`, with
`Δ_max = 2α ln(2e/ε) + 2τ`, for the global iteration. -/
theorem Hyp.toWidth (h : Hyp p I ubd CΓ CΓ' uFix) :
    WidthHyp anbGlobalIter p I ubd CΓ CΓ' uFix p.Δmax := by
  have hα := h.hα
  refine h.toWidthOf fun k x _ => ?_
  -- the inner loops stop: `Φ_α` is `ρ`-sub-additive on the band
  set s := anbRunWith anbGlobalIter p k with hs
  set d := anbStepData p s with hd
  have hAS := h.always (S := anbGlobalIter) k
  have hη : 0 < d.η := by
    rw [hd, anbStepData_η]
    exact mul_pos (by linarith [h.hρ1]) (Real.exp_pos _)
  have hmonoΦ := ParallelAgsiKruzkovProof.monotone_global_kruzkovOp (Λ := p.Λ) hα
  have hmonoB : ∀ x ∈ d.band, Monotone (Global.kruzkovOp p.α p.Λ · x) :=
    fun x _ _ _ hab => hmonoΦ hab x
  have hvΦ : ∀ x ∈ d.band, d.vSub x ≤ Global.kruzkovOp p.α p.Λ d.vSub x := fun x _ => by
    have hvdef : d.vSub = fun y => kruzkov (1 / p.α) ((d.uHat y : ℝ) : WithTop ℝ) := rfl
    change d.vSub x ≤ kruzkovOp p.α (p.Λ · x) d.vSub
    rw [hvdef, ComparisonLambdaProof.kruzkovOp_kruzkov hα.ne' (h.hΛmono x)]
    exact (ComparisonLambdaProof.kruzkov_coe_le_iff hα _ _).2 (hAS.uHat_le x)
  have hvΦ' : ∀ x ∈ d.band, Global.kruzkovOp p.α p.Λ d.vSup x ≤ d.vSup x := fun x _ => by
    have hvdef : d.vSup = fun y => kruzkov (1 / p.α) (s.uSup y) := rfl
    change kruzkovOp p.α (p.Λ · x) d.vSup ≤ d.vSup x
    rw [hvdef, kruzkovOp_kruzkov_ext hα.ne']
    exact (kruzkov_le_iff hα _ _).2 (hAS.uSup_ge x)
  exact ⟨band_subPasses_lt_top hmonoB (h.hsubB d.band) h.hρ0 h.hρ1 hη hvΦ,
    band_passes_lt_top hmonoB (h.hsubB d.band) h.hρ0 h.hρ1 hη hvΦ'⟩

/-- Corollary corol:max_width, first claim. -/
theorem Δ_lt (h : Hyp p I ubd CΓ CΓ' uFix) (k : ℕ) : (anbRunData p k).Δ < p.Δmax :=
  Δ_lt_of h.toWidth k

/-- Corollary corol:max_width, second claim: the stopping test holds at the start of iteration
`⌈n_max⌉₊ + 1`. -/
theorem done (h : Hyp p I ubd CΓ CΓ' uFix) : anbDone p (anbRun p (⌈p.nMax uFix⌉₊ + 1)) :=
  done_of h.toWidth

/-- Corollary corol:max_width, termination: the stopping index (`⊤` if the stopping test never
holds) is at most `⌈n_max⌉₊ + 1`. -/
theorem stopIndex_le (h : Hyp p I ubd CΓ CΓ' uFix) :
    anbStopIndex p ≤ ((⌈p.nMax uFix⌉₊ + 1 : ℕ) : ℕ∞) :=
  stopIndex_le_of h.toWidth

end GuaranteedSubsol.AnbMaxWidthProof
