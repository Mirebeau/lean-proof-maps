/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AnbProof
import LeanHJBAutoformalisation.GuaranteedSubsol.SubsolGrowthProof
import LeanHJBAutoformalisation.GuaranteedSubsol.GraphSubsolProof
import LeanHJBAutoformalisation.GuaranteedSubsol.MaxMinProof
import LeanHJBAutoformalisation.GuaranteedSubsol.MaxMinMonCausalProof
import LeanHJBAutoformalisation.GuaranteedSubsol.CausalFixedPointProof
import LeanHJBAutoformalisation.GuaranteedSubsol.CausalMixProof

/-!
# ANB: Corollary corol:Bn_comp, proofs

Provider proofs for the frozen anchors `GuaranteedSubsol.anbRunData_band_bounds` and
`GuaranteedSubsol.anbRunData_dijkstraBand_bounds`, see `ANCHORS.md`.

* Lower bounds: `û_n ≤ Λ û_n` (Prop. prop:always_subsol), hence `û_n ≤ u_*` by the comparison
  principle.
* Upper bound: the solution `u` of `u = max (ū_n, Γ u)` exists since `u_* + c` is a finite
  super-solution (`exists_eq_max`, from `exists_fixedPoint_of_causal`); it satisfies
  `Γ u ≤ u ≤ Λ u` (lem:graph_subsol), and `û_n = max (ū_n, min (nτ, u))` (lem:max_min, and
  uniqueness of the fixed point of the monotone causal operator `Γ'`). On `{u < t_n}`,
  the definition of `t_n` and `u_* ≤ u̲_n` (`uFix_le_uSup`) give `u_* ≤ (1 + ε) u`, so that
  Prop. prop:olu_ge_ustar applies.
-/

namespace GuaranteedSubsol.AnbBnCompProof

open AnbProof

variable {X : Type*}

/-- The equation `u = max (c, Γ u)` has a finite solution (`exists_fixedPoint_of_causal`), since
`u_* + const` is a finite super-solution. -/
theorem exists_eq_max [Finite X] {Λ Γ : (X → ℝ) → X → ℝ} {I : Set X}
    {ubd : X → ℝ} (hΛbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x)
    (hadd : ∀ x ∈ I, AdditivelyInvariant (Λ · x)) (hΓmono : ∀ x, Monotone (Γ · x))
    (hΓcaus : ∀ x, Causal (Γ · x)) (hΓΛ : ∀ u, Γ u ≤ Λ u) {uFix : X → ℝ} (hfix : Λ uFix = uFix)
    (c : X → ℝ) : ∃ u : X → ℝ, u = fun y => max (c y) (Γ u y) := by
  classical
  have := Fintype.ofFinite X
  -- the finite super-solution `w = u_* + cst`
  set cst : ℝ := ∑ y, |c y - uFix y|
  have hcst : ∀ y, c y - uFix y ≤ cst := fun y =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun z => |c z - uFix z|)
      (fun z _ => abs_nonneg _) (Finset.mem_univ y))
  have hcst0 : 0 ≤ cst := Finset.sum_nonneg fun z _ => abs_nonneg _
  set w : X → ℝ := fun y => uFix y + cst
  have hΛw : ∀ y, Λ w y ≤ w y := fun y => by
    by_cases hy : y ∈ I
    · have h := hadd y hy uFix cst
      change Λ w y = Λ uFix y + cst at h
      rw [h, congrFun hfix y]
    · rw [hΛbd w y hy, ← hΛbd uFix y hy, congrFun hfix y]
      linarith
  obtain ⟨u, hu, -, -⟩ := CausalFixedPointProof.exists_fixedPoint_of_causal
    (Γ := fun v y => max (c y) (Γ v y))
    (fun y _ _ h => max_le_max le_rfl (hΓmono y h))
    (fun y => CausalMixProof.causal_max (MaxMinMonCausalProof.causal_const (c y)) (hΓcaus y))
    (w := w) (fun y => max_le (by linarith [hcst y]) ((hΓΛ w y).trans (hΛw y)))
  exact ⟨u, (funext fun y => congrFun hu y).symm⟩

theorem anbLevel_nonneg [Fintype X] {ε T : ℝ} {uHat : X → ℝ} {uSup : X → WithTop ℝ}
    (hT : 0 ≤ T) (huHat : ∀ x, 0 ≤ uHat x) : 0 ≤ anbLevel ε T uHat uSup := by
  unfold anbLevel
  dsimp only
  split_ifs
  · exact le_min hT (Finset.le_inf' _ _ fun x _ => huHat x)
  · exact hT

/-- Below `t_n`, the stopping test holds: `u̲ ≤ (1 + ε) û`. -/
theorem le_of_lt_anbLevel [Fintype X] {ε T : ℝ} {uHat : X → ℝ} {uSup : X → WithTop ℝ} {x : X}
    (hx : uHat x < anbLevel ε T uHat uSup) : uSup x ≤ (((1 + ε) * uHat x : ℝ) : WithTop ℝ) := by
  classical
  refine not_lt.1 fun h => ?_
  have hmem : x ∈ Finset.univ.filter fun y => (((1 + ε) * uHat y : ℝ) : WithTop ℝ) < uSup y :=
    Finset.mem_filter.2 ⟨Finset.mem_univ x, h⟩
  unfold anbLevel at hx
  dsimp only at hx
  split_ifs at hx with hS
  · exact absurd ((min_le_right _ _).trans (Finset.inf'_le uHat hmem)) (not_le.2 hx)
  · exact hS ⟨x, hmem⟩

/-- A fixed point of `Λ` lies below a super-solution with values in `ℝ_∞`, by the comparison
principle on the partition `{u̲ < ∞} ⊔ {u̲ = ∞}`. -/
theorem uFix_le_uSup [Finite X] {Λ : (X → ℝ) → X → ℝ} (hΛmono : ∀ x, Monotone (Λ · x))
    (hcomp : ∀ J : Set X, HasComparisonPrinciple J Λ) {uFix : X → ℝ} (hfix : Λ uFix = uFix)
    {uSup : X → WithTop ℝ} (hsup : Global.monotoneExtension Λ uSup ≤ uSup) (x : X) :
    (uFix x : WithTop ℝ) ≤ uSup x := by
  classical
  have := Fintype.ofFinite X
  set M : ℝ := ∑ y, |uFix y|
  have hM : ∀ y, uFix y ≤ M := fun y =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun z => |uFix z|)
      (fun z _ => abs_nonneg _) (Finset.mem_univ y))
  set J : Set X := {y | uSup y ≠ ⊤}
  set v : X → ℝ := fun y => if h : uSup y = ⊤ then M else (uSup y).untop h
  have hv : ∀ y ∈ J, (v y : WithTop ℝ) = uSup y := fun y hy => by
    have hy' : ¬uSup y = ⊤ := hy
    simp only [v, hy', ↓reduceDIte, WithTop.coe_untop]
  have hvle : (fun y => (v y : WithTop ℝ)) ≤ uSup := fun y => by
    by_cases h : uSup y = ⊤
    · rw [h]; exact le_top
    · exact (hv y h).le
  have key := hcomp J uFix v (fun y _ => (congrFun hfix y).ge) (fun y hy => ?_) (fun y hy => ?_)
  · by_cases hx : uSup x = ⊤
    · rw [hx]; exact le_top
    · rw [← hv x hx]; exact WithTop.coe_le_coe.2 (key x)
  · rw [← WithTop.coe_le_coe, hv y hy, ← MonotoneExtension.coe_eq (hΛmono y)]
    exact (KruzkovProof.monotone_monotoneExtension (Λ · y) hvle).trans (hsup y)
  · have h : uSup y = ⊤ := not_not.1 hy
    simp only [v, h, ↓reduceDIte]
    exact hM y

variable [Fintype X] [LinearOrder X] {S : AnbInnerSolver X} [S.Valid]

/-- Along the run, `ū ≥ 0`. -/
theorem uSub_nonneg {p : AnbParams X} (hΛmono : ∀ x, Monotone (p.Λ · x)) (hΛ0 : 0 ≤ p.Λ 0)
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x))
    (hΓΛ : ∀ u, p.Γ u ≤ p.Λ u) (hα : 0 < p.α) (hτ : 0 ≤ p.τ) (k : ℕ) :
    0 ≤ (anbRunWith S p k).uSub := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    have h := always_subsol (S := S) hΛmono hΛ0 hΓmono hΓcaus hΓΛ hα hτ k
    rw [anbRun_succ]
    exact (ih.trans h.uSub_le_uHat).trans h.uHat_le_uSub_step

/-- The lower bound `û_n ≤ u_*`. -/
theorem uHat_le_uFix {p : AnbParams X} (hΛmono : ∀ x, Monotone (p.Λ · x)) (hΛ0 : 0 ≤ p.Λ 0)
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x))
    (hΓΛ : ∀ u, p.Γ u ≤ p.Λ u) (hcomp : ∀ J : Set X, HasComparisonPrinciple J p.Λ)
    {uFix : X → ℝ} (hfix : p.Λ uFix = uFix) (hα : 0 < p.α) (hτ : 0 ≤ p.τ) (k : ℕ) :
    (anbRunDataWith S p k).uHat ≤ uFix :=
  hcomp Set.univ _ uFix
    (fun x _ => (always_subsol (S := S) hΛmono hΛ0 hΓmono hΓcaus hΓΛ hα hτ k).uHat_le x)
    (fun x _ => (congrFun hfix x).le) (fun x hx => absurd (Set.mem_univ x) hx)

/-- The upper bound `u_* < t⁺_n` on `{û_n < nτ}` (iteration `n = k`). -/
theorem uFix_lt_tPlus {p : AnbParams X} {I : Set X} {ubd : X → ℝ}
    (hΛbd : ∀ u, ∀ x ∉ I, p.Λ u x = ubd x) (hΓbd : ∀ u, ∀ x ∉ I, p.Γ u x = ubd x)
    {Cpast CΓ CΓ' : ℝ} (hCpast : 0 ≤ Cpast) (hCΓ : 1 ≤ CΓ) (hCΓ' : 0 ≤ CΓ')
    (hΛmono : ∀ x, Monotone (p.Λ · x)) (hΛ0 : 0 ≤ p.Λ 0)
    (hadd : ∀ x ∈ I, AdditivelyInvariant (p.Λ · x)) (hmem : ∀ x ∈ I, HasMemory Cpast (p.Λ · x))
    (hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (p.Λ · x) (p.Γ · x))
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x))
    (hΓΛ : ∀ u, p.Γ u ≤ p.Λ u) (hcomp : ∀ J : Set X, HasComparisonPrinciple J p.Λ)
    {uFix : X → ℝ} (hfix : p.Λ uFix = uFix) (hα : 0 < p.α) (hτ : 0 ≤ p.τ) (hε : 0 < p.ε)
    (k : ℕ) {x : X} (hx : (anbRunDataWith S p k).uHat x < (k : ℝ) * p.τ) :
    uFix x < (anbRunDataWith S p k).tPlus p.ε Cpast CΓ CΓ' := by
  set s := anbRunWith S p k with hs
  have hd : anbRunDataWith S p k = anbStepData p s := rfl
  rw [hd] at hx ⊢
  set d := anbStepData p s with hd'
  have hAS := always_subsol (S := S) hΛmono hΛ0 hΓmono hΓcaus hΓΛ hα hτ k
  have hG := guess_run (S := S) hΓmono hΓcaus hα hτ k
  have hn : (s.n : ℝ) = k := by rw [hs, anbRun_n]
  set T : ℝ := s.n * p.τ with hT
  have hEq : ∀ y, d.uHat y = max (s.uSub y) (min T (p.Γ d.uHat y)) := fun y =>
    (uHat_eq hΓmono hΓcaus hG y).2
  -- the solution `u` of `u = max (ū_n, Γ u)`
  obtain ⟨u, hu⟩ := exists_eq_max hΛbd hadd hΓmono hΓcaus hΓΛ hfix s.uSub
  have huy : ∀ y, u y = max (s.uSub y) (p.Γ u y) := fun y => congrFun hu y
  have hΓu : ∀ y, p.Γ u y ≤ u y := fun y => (huy y).symm ▸ le_max_right _ _
  have huΛ : u ≤ p.Λ u := GraphSubsolProof.subsol_extension (fun _ _ h y => hΛmono y h)
    (fun w => hΓΛ w) hAS.uSub_le hu
  -- `û_n = max (ū_n, min (nτ, u))` (lem:max_min and uniqueness)
  have hmm := MaxMinProof.max_min_fixedPoint hΓcaus s.uSub T hu rfl
  have hhat : d.uHat = fun y => max (s.uSub y) (min T (u y)) := by
    -- both are fixed points of the monotone causal `Γ'`, hence equal
    have h2 : ∀ y, max (s.uSub y) (min T (p.Γ (fun z => max (s.uSub z) (min T (u z))) y)) =
        max (s.uSub y) (min T (u y)) := congrFun hmm.1
    obtain ⟨u0, -, hsub, hsup⟩ := CausalFixedPointProof.exists_fixedPoint_of_causal
      (Γ := fun w y => max (s.uSub y) (min T (p.Γ w y)))
      (fun y _ _ h => max_le_max le_rfl (min_le_min le_rfl (hΓmono y h)))
      (fun y => MaxMinMonCausalProof.causal_max_min (hΓcaus y) (s.uSub y) T)
      (w := d.uHat) (fun y => (hEq y).ge)
    have e1 : d.uHat = u0 := le_antisymm (hsub _ fun y => (hEq y).le) (hsup _ fun y => (hEq y).ge)
    have e2 : (fun y => max (s.uSub y) (min T (u y))) = u0 :=
      le_antisymm (hsub _ fun y => (h2 y).ge) (hsup _ fun y => (h2 y).le)
    exact e1.trans e2.symm
  have hhu : ∀ y, d.uHat y ≤ u y := fun y => by
    rw [hhat]
    exact max_le ((le_max_left _ _).trans (huy y).ge) (min_le_right _ _)
  -- `t_n ≥ 0`
  have hT0 : 0 ≤ T := by rw [hT, hn]; exact mul_nonneg (Nat.cast_nonneg k) hτ
  have hhat0 : ∀ y, 0 ≤ d.uHat y := fun y =>
    (uSub_nonneg hΛmono hΛ0 hΓmono hΓcaus hΓΛ hα hτ k y).trans (hAS.uSub_le_uHat y)
  have ht0 : 0 ≤ d.t := by rw [hd', anbStepData_t]; exact anbLevel_nonneg hT0 hhat0
  have htT : d.t ≤ T := by rw [hd', anbStepData_t]; exact anbLevel_le _ _ _ _
  -- `u_* ≤ (1 + ε) u` on `{u < t_n}`
  have hlow : ∀ y, u y < d.t → uFix y ≤ (1 + p.ε) * u y := fun y hy => by
    have hy' : d.uHat y < anbLevel p.ε T d.uHat s.uSup := by
      rw [← anbStepData_t]; exact (hhu y).trans_lt hy
    have h1 := (uFix_le_uSup hΛmono hcomp hfix hAS.uSup_ge y).trans (le_of_lt_anbLevel hy')
    exact (WithTop.coe_le_coe.1 h1).trans
      (mul_le_mul_of_nonneg_left (hhu y) (by linarith))
  have hgrow := SubsolGrowthProof.subsol_growth hΛbd hΓbd hCpast hCΓ hCΓ' (fun y _ => hΛmono y)
    hadd hmem hcmp hcomp (fun y => (congrFun hfix y).ge) ht0 hε hlow hΓu huΛ
  -- `u(x) < nτ`
  have hxT : d.uHat x < T := by rw [hT, hn]; exact hx
  have hux : u x < T := by
    have h := hxT
    rw [hhat] at h
    rcases min_lt_iff.1 (lt_of_le_of_lt (le_max_right _ _) h) with h' | h'
    · exact absurd h' (lt_irrefl _)
    · exact h'
  have hΔ : d.Δ = T - d.t := by rw [hd', anbStepData_Δ]
  rw [AnbStepData.tPlus_def]
  by_cases hc : d.t ≤ u x
  · have h1 := hgrow x hc
    have h2 : (uFix x - (1 + p.ε) * d.t - Cpast - CΓ') / CΓ < d.Δ := by rw [hΔ]; linarith
    rw [div_lt_iff₀ (by linarith), mul_comm] at h2
    linarith
  · have h1 : uFix x < (1 + p.ε) * d.t :=
      (hlow x (not_le.1 hc)).trans_lt (mul_lt_mul_of_pos_left (not_le.1 hc) (by linarith))
    have h2 : 0 ≤ CΓ * d.Δ := mul_nonneg (by linarith) (by rw [hΔ]; linarith)
    linarith

theorem band_bounds {p : AnbParams X} {I : Set X} {ubd : X → ℝ}
    (hΛbd : ∀ u, ∀ x ∉ I, p.Λ u x = ubd x) (hΓbd : ∀ u, ∀ x ∉ I, p.Γ u x = ubd x)
    {Cpast CΓ CΓ' : ℝ} (hCpast : 0 ≤ Cpast) (hCΓ : 1 ≤ CΓ) (hCΓ' : 0 ≤ CΓ')
    (hΛmono : ∀ x, Monotone (p.Λ · x)) (hΛ0 : 0 ≤ p.Λ 0)
    (hadd : ∀ x ∈ I, AdditivelyInvariant (p.Λ · x)) (hmem : ∀ x ∈ I, HasMemory Cpast (p.Λ · x))
    (hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (p.Λ · x) (p.Γ · x))
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x))
    (hΓΛ : ∀ u, p.Γ u ≤ p.Λ u) (hcomp : ∀ J : Set X, HasComparisonPrinciple J p.Λ)
    {uFix : X → ℝ} (hfix : p.Λ uFix = uFix) (hα : 0 < p.α) (hτ : 0 ≤ p.τ) (hε : 0 < p.ε)
    (k : ℕ) {x : X} (hx : x ∈ (anbRunDataWith S p k).band) :
    (anbRunDataWith S p k).tMinus ≤ uFix x ∧
      uFix x < (anbRunDataWith S p k).tPlus p.ε Cpast CΓ CΓ' := by
  have hx' := (mem_band_iff p (anbRunWith S p k) x).1 hx
  rw [anbRun_n] at hx'
  exact ⟨hx'.1.trans (uHat_le_uFix hΛmono hΛ0 hΓmono hΓcaus hΓΛ hcomp hfix hα hτ k x),
    uFix_lt_tPlus hΛbd hΓbd hCpast hCΓ hCΓ' hΛmono hΛ0 hadd hmem hcmp hΓmono hΓcaus hΓΛ hcomp
      hfix hα hτ hε k hx'.2⟩

theorem dijkstraBand_bounds {p : AnbParams X} {I : Set X} {ubd : X → ℝ}
    (hΛbd : ∀ u, ∀ x ∉ I, p.Λ u x = ubd x) (hΓbd : ∀ u, ∀ x ∉ I, p.Γ u x = ubd x)
    {Cpast CΓ CΓ' : ℝ} (hCpast : 0 ≤ Cpast) (hCΓ : 1 ≤ CΓ) (hCΓ' : 0 ≤ CΓ')
    (hΛmono : ∀ x, Monotone (p.Λ · x)) (hΛ0 : 0 ≤ p.Λ 0)
    (hadd : ∀ x ∈ I, AdditivelyInvariant (p.Λ · x)) (hmem : ∀ x ∈ I, HasMemory Cpast (p.Λ · x))
    (hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (p.Λ · x) (p.Γ · x))
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hΓcaus : ∀ x, Causal (p.Γ · x))
    (hΓΛ : ∀ u, p.Γ u ≤ p.Λ u) (hcomp : ∀ J : Set X, HasComparisonPrinciple J p.Λ)
    {uFix : X → ℝ} (hfix : p.Λ uFix = uFix) (hα : 0 < p.α) (hτ : 0 ≤ p.τ) (hε : 0 < p.ε)
    {k : ℕ} {x : X}
    (hx : x ∈ anbDijkstraBand (anbRunDataWith S p k).tMinus (((k + 1 : ℕ) : ℝ) * p.τ)
      (anbRunDataWith S p k).uHat (anbRunDataWith S p (k + 1)).uHat) :
    (anbRunDataWith S p k).tMinus ≤ uFix x ∧
      uFix x < (anbRunDataWith S p (k + 1)).tPlus p.ε Cpast CΓ CΓ' :=
  ⟨hx.1.trans (uHat_le_uFix hΛmono hΛ0 hΓmono hΓcaus hΓΛ hcomp hfix hα hτ k x),
    uFix_lt_tPlus hΛbd hΓbd hCpast hCΓ hCΓ' hΛmono hΛ0 hadd hmem hcmp hΓmono hΓcaus hΓΛ hcomp
      hfix hα hτ hε (k + 1) hx.2⟩

end GuaranteedSubsol.AnbBnCompProof
