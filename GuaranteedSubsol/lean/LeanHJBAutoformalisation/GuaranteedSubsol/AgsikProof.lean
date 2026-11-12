/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AGSIK
import LeanHJBAutoformalisation.GuaranteedSubsol.AxiomsExt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# AGSIK: proofs

Provider proofs for the frozen anchors `GuaranteedSubsol.agsikStep_superSolution` and
`GuaranteedSubsol.agsikRun_terminates` (Algorithm algo:agsik), see `ANCHORS.md`.

* Invariant: a pass replaces `u(x)` with `Λ u(x) ≤ u(x)` on the selected points, which preserves
  `Λ u ≤ u` by monotonicity (as in Prop. prop:partialMonotone).
* A selected point `x` at level `n` has `Λ u(x) = a` finite, with `a + ε < u(x)` and
  `a ≤ n ln 2 / αinv` (`select_spec`).
* Termination. By the comparison principle, `w ≤ u` throughout. At each point `x`, the first
  update makes `u(x)` finite, and each later one lowers it by more than `ε`, so the counter at `x`
  is bounded along the run. Hence the total number of updates is eventually constant, and from
  then on only `n` grows. If the stopping criterion failed at some `x`, the gap
  `exp(-Λu(x)/α) - exp((ε-u(x))/α) > 0` would eventually exceed `2^{-n}`, and `x` would be
  selected again: a contradiction.
-/

namespace GuaranteedSubsol.AgsikProof

variable {X : Type*} {Λ : (X → WithTop ℝ) → X → WithTop ℝ} {αinv ε : ℝ}

theorem kruzkov_top' : kruzkov αinv ⊤ = 0 := rfl

theorem kruzkov_coe' (a : ℝ) : kruzkov αinv a = -Real.exp (-αinv * a) := rfl

/-- `-kruzkov αinv a = exp(-αinv a)` is nonnegative. -/
theorem neg_kruzkov_nonneg (a : WithTop ℝ) : 0 ≤ -kruzkov αinv a := by
  induction a using WithTop.recTopCoe with
  | top => simp [kruzkov]
  | coe a => simp [kruzkov, (Real.exp_pos _).le]

open Classical in
theorem step_u (s : AgsikState X) (x : X) :
    (agsikStep Λ αinv ε s).u x =
      if agsikSelect Λ αinv ε s.n s.u x then Λ s.u x else s.u x := by
  by_cases h1 : ∃ x, agsikSelect Λ αinv ε s.n s.u x
  · simp only [agsikStep, h1, ↓reduceIte]
  · have hx : ¬agsikSelect Λ αinv ε s.n s.u x := fun h => h1 ⟨x, h⟩
    simp only [agsikStep, h1, hx, ↓reduceIte]
    split_ifs <;> rfl

open Classical in
theorem step_count (s : AgsikState X) (x : X) :
    (agsikStep Λ αinv ε s).count x =
      if agsikSelect Λ αinv ε s.n s.u x then s.count x + 1 else s.count x := by
  by_cases h1 : ∃ x, agsikSelect Λ αinv ε s.n s.u x
  · simp only [agsikStep, h1, ↓reduceIte]
  · have hx : ¬agsikSelect Λ αinv ε s.n s.u x := fun h => h1 ⟨x, h⟩
    simp only [agsikStep, h1, hx, ↓reduceIte]
    split_ifs <;> rfl

/-- Without selected points and before the stopping criterion, the level increases. -/
theorem step_n_of_not (s : AgsikState X) (h1 : ¬∃ x, agsikSelect Λ αinv ε s.n s.u x)
    (h2 : ¬agsikDone Λ ε s.u) : (agsikStep Λ αinv ε s).n = s.n + 1 := by
  simp only [agsikStep, h1, h2, ↓reduceIte]

theorem step_superSolution (hmono : Monotone Λ) {s : AgsikState X} (hs : Λ s.u ≤ s.u) :
    Λ (agsikStep Λ αinv ε s).u ≤ (agsikStep Λ αinv ε s).u := by
  have hle : (agsikStep Λ αinv ε s).u ≤ s.u := fun x => by
    classical
    rw [step_u]; split_ifs
    · exact hs x
    · exact le_rfl
  intro x
  classical
  refine (hmono hle x).trans ?_
  rw [step_u]; split_ifs
  · exact le_rfl
  · exact hs x

theorem superSolution (hmono : Monotone Λ) (αinv ε : ℝ) {s : AgsikState X}
    (hs : Λ s.u ≤ s.u) (k : ℕ) :
    Λ ((agsikStep Λ αinv ε)^[k] s).u ≤ ((agsikStep Λ αinv ε)^[k] s).u := by
  induction k with
  | zero => exact hs
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact step_superSolution hmono ih

/-- `2^{-n} = exp(-n ln 2)`. -/
theorem inv_two_pow (n : ℕ) : (2 : ℝ)⁻¹ ^ n = Real.exp (-(n * Real.log 2)) := by
  rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log two_pos, inv_pow]

/-- A selected point: `Λ u(x) = a` is finite, `a + ε < u(x)` and `a ≤ n ln 2 / αinv`. -/
theorem select_spec (hαinv : 0 < αinv) {n : ℕ} {u : X → WithTop ℝ} {x : X}
    (h : agsikSelect Λ αinv ε n u x) :
    ∃ a : ℝ, Λ u x = a ∧ ((a + ε : ℝ) : WithTop ℝ) < u x ∧ a ≤ n * Real.log 2 / αinv := by
  unfold agsikSelect at h
  have hpos : 0 < (2 : ℝ)⁻¹ ^ n := by positivity
  have hE := mul_nonneg (Real.exp_pos (αinv * ε)).le (neg_kruzkov_nonneg (αinv := αinv) (u x))
  induction hΛ : Λ u x using WithTop.recTopCoe with
  | top => rw [hΛ, kruzkov_top', neg_zero] at h; linarith
  | coe a =>
    rw [hΛ, kruzkov_coe', neg_neg] at h
    refine ⟨a, rfl, ?_, ?_⟩
    · induction hu : u x using WithTop.recTopCoe with
      | top => exact WithTop.coe_lt_top _
      | coe b =>
        rw [hu, kruzkov_coe', neg_neg, ← Real.exp_add] at h
        have : αinv * ε + -αinv * b < -αinv * a := Real.exp_lt_exp.1 (by linarith)
        exact WithTop.coe_lt_coe.2 (by nlinarith)
    · have : -(n * Real.log 2) ≤ -αinv * a := by
        rw [← Real.exp_le_exp, ← inv_two_pow]; linarith [hE]
      rw [le_div_iff₀ hαinv]; linarith

/-- Where the stopping criterion fails, `x` is selected at all large enough levels. -/
theorem select_of_not_done (hαinv : 0 < αinv) {u : X → WithTop ℝ} {x : X}
    (hx : ¬u x ≤ Λ u x + (ε : WithTop ℝ)) : ∃ n0, ∀ n ≥ n0, agsikSelect Λ αinv ε n u x := by
  have hΛ : Λ u x ≠ ⊤ := fun h' => hx (by rw [h', WithTop.top_add]; exact le_top)
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hΛ
  have hg : 0 < Real.exp (-αinv * a) - Real.exp (αinv * ε) * -kruzkov αinv (u x) := by
    induction hu : u x using WithTop.recTopCoe with
    | top => rw [kruzkov_top', neg_zero, mul_zero, sub_zero]; exact Real.exp_pos _
    | coe b =>
      rw [hu, ← ha, ← WithTop.coe_add, WithTop.coe_le_coe, not_le] at hx
      rw [kruzkov_coe', neg_neg, ← Real.exp_add, sub_pos, Real.exp_lt_exp]
      nlinarith
  obtain ⟨n0, hn0⟩ := exists_pow_lt_of_lt_one hg (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨n0, fun n hn => ?_⟩
  have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num) hn
  unfold agsikSelect
  rw [← ha, kruzkov_coe', neg_neg]
  linarith

theorem count_le_step (s : AgsikState X) (x : X) :
    s.count x ≤ (agsikStep Λ αinv ε s).count x := by
  classical
  rw [step_count]; split_ifs <;> omega

/-- One step does not increase the potential `u(x) + ε count(x)`. -/
theorem potential_step (hαinv : 0 < αinv) (s : AgsikState X) (x : X) :
    (agsikStep Λ αinv ε s).u x + ((ε * (agsikStep Λ αinv ε s).count x : ℝ) : WithTop ℝ) ≤
      s.u x + ((ε * s.count x : ℝ) : WithTop ℝ) := by
  classical
  rw [step_u, step_count]
  split_ifs with h
  · obtain ⟨a, ha, hlt, -⟩ := select_spec hαinv h
    rw [ha]
    have e : ((a : ℝ) : WithTop ℝ) + ((ε * ((s.count x + 1 : ℕ) : ℝ) : ℝ) : WithTop ℝ) =
        ((a + ε : ℝ) : WithTop ℝ) + ((ε * s.count x : ℝ) : WithTop ℝ) := by
      rw [← WithTop.coe_add, ← WithTop.coe_add]; congr 1; push_cast; ring
    rw [e]
    exact add_le_add hlt.le le_rfl
  · exact le_rfl

theorem terminates [Finite X] (hmono : Monotone Λ)
    (hcomp : Ext.HasComparisonPrinciple Set.univ Λ) {w : X → ℝ}
    (hw : ∀ x, (w x : WithTop ℝ) ≤ Λ (fun y => (w y : WithTop ℝ)) x)
    (hαinv : 0 < αinv) (hε : 0 < ε) :
    ∃ k, agsikDone Λ ε ((agsikStep Λ αinv ε)^[k] agsikInit).u := by
  classical
  have := Fintype.ofFinite X
  set s : ℕ → AgsikState X := fun k => (agsikStep Λ αinv ε)^[k] agsikInit with hs_def
  have hsucc : ∀ k, s (k + 1) = agsikStep Λ αinv ε (s k) := fun k =>
    Function.iterate_succ_apply' _ _ _
  have hsup : ∀ k, Λ (s k).u ≤ (s k).u := fun k =>
    superSolution hmono αinv ε (s := agsikInit) (fun x => by simp [agsikInit]) k
  have hlow : ∀ k x, (w x : WithTop ℝ) ≤ (s k).u x := fun k =>
    hcomp _ _ (fun x _ => hw x) (fun x _ => hsup k x) (fun x hx => absurd trivial hx)
  by_contra hcon
  push Not at hcon
  have hcmono : ∀ x, Monotone fun k => (s k).count x := fun x =>
    monotone_nat_of_le_succ fun k => by rw [hsucc]; exact count_le_step _ x
  -- the counter at each point is bounded along the run
  have hcb : ∀ x, ∃ B : ℕ, ∀ k, (s k).count x ≤ B := by
    intro x
    by_cases hfin : ∃ k0, (s k0).u x ≠ ⊤
    · obtain ⟨k0, hk0⟩ := hfin
      obtain ⟨b0, hb0⟩ := WithTop.ne_top_iff_exists.1 hk0
      have hpot : ∀ m, (s (k0 + m)).u x + ((ε * (s (k0 + m)).count x : ℝ) : WithTop ℝ) ≤
          (s k0).u x + ((ε * (s k0).count x : ℝ) : WithTop ℝ) := by
        intro m
        induction m with
        | zero => exact le_rfl
        | succ m ih =>
          rw [← add_assoc, hsucc]
          exact (potential_step hαinv _ x).trans ih
      refine ⟨(s k0).count x + ⌈(b0 - w x) / ε⌉₊, fun k => ?_⟩
      rcases le_or_gt k k0 with hk | hk
      · exact (hcmono x hk).trans (Nat.le_add_right _ _)
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk.le
        have h1 := (add_le_add (hlow (k0 + m) x) le_rfl).trans (hpot m)
        rw [← hb0, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at h1
        have h2 : ((s (k0 + m)).count x : ℝ) - (s k0).count x ≤ (b0 - w x) / ε := by
          rw [le_div_iff₀ hε]
          have e : (((s (k0 + m)).count x : ℝ) - (s k0).count x) * ε =
              ε * (s (k0 + m)).count x - ε * (s k0).count x := by ring
          rw [e]; linarith
        have h3 := Nat.le_ceil ((b0 - w x) / ε)
        have h4 : ((s (k0 + m)).count x : ℝ) ≤
            (((s k0).count x + ⌈(b0 - w x) / ε⌉₊ : ℕ) : ℝ) := by
          push_cast; linarith
        exact_mod_cast h4
    · push Not at hfin
      refine ⟨0, fun k => ?_⟩
      induction k with
      | zero => simp [s, agsikInit]
      | succ k ih =>
        rw [hsucc, step_count]
        split_ifs with h
        · obtain ⟨a, ha, -, -⟩ := select_spec hαinv h
          have := hfin (k + 1)
          rw [hsucc, step_u] at this
          simp only [h, ↓reduceIte, ha] at this
          exact absurd this (WithTop.coe_ne_top)
        · exact ih
  choose B hB using hcb
  -- the total number of updates is eventually constant
  set S : ℕ → ℕ := fun k => ∑ x, (s k).count x with hS
  have hSB : ∀ k, S k ≤ ∑ x, B x := fun k => Finset.sum_le_sum fun x _ => hB x k
  have hSmono : Monotone S := fun k k' h => Finset.sum_le_sum fun x _ => hcmono x h
  have hbdd : BddAbove (Set.range S) := ⟨_, Set.forall_mem_range.2 hSB⟩
  obtain ⟨K, hK⟩ := Nat.sSup_mem (Set.range_nonempty S) hbdd
  have hmax : ∀ k, S k ≤ S K := fun k => hK ▸ le_csSup hbdd (Set.mem_range_self k)
  have hnosel : ∀ k ≥ K, ∀ x, ¬agsikSelect Λ αinv ε (s k).n (s k).u x := by
    intro k hk x hx
    have hlt : S k < S (k + 1) := by
      simp only [hS]
      refine Finset.sum_lt_sum (fun y _ => ?_) ⟨x, Finset.mem_univ _, ?_⟩
      · rw [hsucc]; exact count_le_step _ y
      · rw [hsucc, step_count]; simp only [hx, ↓reduceIte]; omega
    have := hmax (k + 1)
    have := hSmono hk
    omega
  -- from then on, only the level grows
  have hlate : ∀ m, (s (K + m)).u = (s K).u ∧ (s (K + m)).n = (s K).n + m := by
    intro m
    induction m with
    | zero => exact ⟨rfl, rfl⟩
    | succ m ih =>
      have h1 : ¬∃ x, agsikSelect Λ αinv ε (s (K + m)).n (s (K + m)).u x :=
        fun ⟨x, hx⟩ => hnosel (K + m) (Nat.le_add_right _ _) x hx
      rw [← add_assoc, hsucc]
      refine ⟨?_, ?_⟩
      · funext x
        have hx' : ¬agsikSelect Λ αinv ε (s (K + m)).n (s (K + m)).u x := fun h => h1 ⟨x, h⟩
        rw [step_u]; simp only [hx', ↓reduceIte]; rw [ih.1]
      · rw [step_n_of_not _ h1 (hcon (K + m)), ih.2]; ring
  obtain ⟨x, hx⟩ : ∃ x, ¬(s K).u x ≤ Λ (s K).u x + (ε : WithTop ℝ) := by
    have := hcon K
    unfold agsikDone at this
    push Not at this
    obtain ⟨x, hx⟩ := this
    exact ⟨x, not_le.2 hx⟩
  obtain ⟨n0, hn0⟩ := select_of_not_done hαinv hx
  have hsel := hn0 ((s K).n + n0) (Nat.le_add_left _ _)
  rw [← (hlate n0).1, ← (hlate n0).2] at hsel
  exact hnosel (K + n0) (Nat.le_add_right _ _) x hsel

end GuaranteedSubsol.AgsikProof
