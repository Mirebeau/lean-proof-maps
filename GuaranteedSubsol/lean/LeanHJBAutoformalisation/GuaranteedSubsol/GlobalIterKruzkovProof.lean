/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AnbProof
import LeanHJBAutoformalisation.GuaranteedSubsol.PowCvxProof
import LeanHJBAutoformalisation.GuaranteedSubsol.KruzkovRpowProof

/-!
# Global iteration for `Φ_α` when `Φ_β` is `σ`-sub-additive: proofs

Provider proof for the frozen anchor `GuaranteedSubsol.globalIterRun_passes_le_withUnknown`
(Lemma lem:cplx_global_iteration_withUnknown), see `ANCHORS.md`. With
`s := β/α ≥ 1`, `v = E_α u` and `w = E_β u` are related by `v = -(-w)^s`, and so are the operators:
`Φ_α v = -(-Φ_β w)^s` (`conj`). The proof follows the paper:
1. the order `E_β ū ≤ E_β u̲`, by the comparison principle (for the super-solution version);
2. the plain iterates of `Φ_α` correspond to those of `Φ_β` (`conj`);
3. in `β`-coordinates, the residual is at most `σ^k C^{α/β}` (`σ`-sub-additivity);
4. in `α`-coordinates, by lem:pow_cvx, the residual is at most `s σ^k C`, hence at most `η` after
   `⌈(ln(C/η) + ln s)/(-ln σ)⌉` iterations.
The core (`sub_resid`, `sup_resid`) is stated for an arbitrary pair of conjugate operators, so that
it also applies to operators acting on a band.
-/

namespace GuaranteedSubsol.GlobalIterKruzkovProof

open AnbProof

/-! ### Real inequalities -/

theorem conj_inv {r s t : ℝ} (hrs : s * r = 1) (ht : t ≤ 0) : -(-(-(-t) ^ s)) ^ r = t := by
  rw [neg_neg, ← Real.rpow_mul (by linarith), hrs, Real.rpow_one, neg_neg]

theorem mul_rpow_sub_one {D s : ℝ} (hD : 0 ≤ D) (hs : 1 ≤ s) : D * D ^ (s - 1) = D ^ s := by
  rcases hD.eq_or_lt with rfl | hD
  · rcases hs.eq_or_lt with rfl | hs'
    · simp
    · rw [Real.zero_rpow (by linarith), Real.zero_rpow (by linarith), mul_zero]
  · rw [Real.rpow_sub_one hD.ne', mul_div_cancel₀ _ hD.ne']

/-- lem:pow_cvx, in the form used below. -/
theorem diff_bound {s a b e D : ℝ} (hs : 1 ≤ s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hbe : b ≤ e)
    (hab : a + b ≤ D) : (a + b) ^ s - a ^ s ≤ s * e * D ^ (s - 1) := by
  have h := PowCvxProof.rpow_le_rpow_add_mul_sub ha (le_add_of_nonneg_right hb) hs
  rw [add_sub_cancel_left] at h
  have hab0 : 0 ≤ a + b := by linarith
  have hp : (a + b) ^ (s - 1) ≤ D ^ (s - 1) := Real.rpow_le_rpow hab0 hab (by linarith)
  have hpos : 0 ≤ (a + b) ^ (s - 1) := Real.rpow_nonneg hab0 _
  have h1 : s * (a + b) ^ (s - 1) * b ≤ s * D ^ (s - 1) * e :=
    mul_le_mul (mul_le_mul_of_nonneg_left hp (by linarith)) hbe hb
      (mul_nonneg (by linarith) (Real.rpow_nonneg (hab0.trans hab) _))
  nlinarith

/-! ### Global iteration and plain iterates -/

section Iterates

variable {Y : Type*} {Φ : (Y → ℝ) → Y → ℝ} {η : ℝ} {v : Y → ℝ}

theorem subRun_eq_iterate (n : ℕ)
    (h : ∀ m < n, ¬∀ y, Φ (globalIterSubRun Φ η v m) y - globalIterSubRun Φ η v m y ≤ η) :
    globalIterSubRun Φ η v n = Φ^[n] v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [GlobalIterationProof.subRun_succ,
      GlobalIterationProof.subStep_of_not _ (h n (Nat.lt_succ_self n)),
      ih fun m hm => h m (by omega), Function.iterate_succ_apply']

theorem run_eq_iterate (n : ℕ)
    (h : ∀ m < n, ¬∀ y, globalIterRun Φ η v m y - Φ (globalIterRun Φ η v m) y ≤ η) :
    globalIterRun Φ η v n = Φ^[n] v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [GlobalIterationProof.run_succ,
      GlobalIterationProof.step_of_not _ (h n (Nat.lt_succ_self n)),
      ih fun m hm => h m (by omega), Function.iterate_succ_apply']

/-- If the stopping criterion holds at the plain iterate `Φ^N v`, the global iteration
(sub-solution variant) performs at most `N` passes. -/
theorem subPasses_le_of_iterate {N : ℕ} (hN : ∀ y, Φ (Φ^[N] v) y - Φ^[N] v y ≤ η) :
    globalIterSubPasses Φ η v ≤ (N : ℕ∞) := by
  classical
  by_cases hex : ∃ m ≤ N, ∀ y, Φ (globalIterSubRun Φ η v m) y - globalIterSubRun Φ η v m y ≤ η
  · obtain ⟨m, hm, hcrit⟩ := hex
    have h : ∃ m, ∀ y, Φ (globalIterSubRun Φ η v m) y - globalIterSubRun Φ η v m y ≤ η :=
      ⟨m, hcrit⟩
    unfold globalIterSubPasses
    simp only [h, ↓reduceDIte, Nat.cast_le]
    exact le_trans (by convert Nat.find_min' h hcrit) hm
  · push Not at hex
    have hrun := subRun_eq_iterate N fun m hm hall => by
      obtain ⟨y, hy⟩ := hex m hm.le
      linarith [hall y]
    obtain ⟨y, hy⟩ := hex N le_rfl
    rw [hrun] at hy
    linarith [hN y]

/-- If the stopping criterion holds at the plain iterate `Φ^N v`, the global iteration
(super-solution version) performs at most `N` passes. -/
theorem passes_le_of_iterate {N : ℕ} (hN : ∀ y, Φ^[N] v y - Φ (Φ^[N] v) y ≤ η) :
    globalIterPasses Φ η v ≤ (N : ℕ∞) := by
  classical
  by_cases hex : ∃ m ≤ N, ∀ y, globalIterRun Φ η v m y - Φ (globalIterRun Φ η v m) y ≤ η
  · obtain ⟨m, hm, hcrit⟩ := hex
    have h : ∃ m, ∀ y, globalIterRun Φ η v m y - Φ (globalIterRun Φ η v m) y ≤ η :=
      ⟨m, hcrit⟩
    unfold globalIterPasses
    simp only [h, ↓reduceDIte, Nat.cast_le]
    exact le_trans (by convert Nat.find_min' h hcrit) hm
  · push Not at hex
    have hrun := run_eq_iterate N fun m hm hall => by
      obtain ⟨y, hy⟩ := hex m hm.le
      linarith [hall y]
    obtain ⟨y, hy⟩ := hex N le_rfl
    rw [hrun] at hy
    linarith [hN y]

end Iterates

/-! ### The core, for two conjugate operators -/

section Core

variable {Y : Type*} {Φ Ψ : (Y → ℝ) → Y → ℝ} {σ r s D : ℝ}

/-- Sub-solution variant: the residual of the `k`-th iterate of `Φ` is at most `s σ^k D^s`,
where `D` bounds the starting map in `β`-coordinates (by lem:pow_cvx). -/
theorem sub_resid (hmono : Monotone Ψ) (hsub : ∀ y, SubAdditive σ (Ψ · y)) (hσ : 0 ≤ σ)
    (hneg : ∀ w y, Ψ w y ≤ 0) (hs : 1 ≤ s) (hrs : s * r = 1)
    (hconj : ∀ v : Y → ℝ, (∀ y, v y ≤ 0) → ∀ y, Φ v y = -(-Ψ (fun z => -(-v z) ^ r) y) ^ s)
    {w0 v0 : Y → ℝ} (hv0 : ∀ y, v0 y = -(-w0 y) ^ s) (hw0 : w0 ≤ Ψ w0)
    (hw00 : ∀ y, w0 y ≤ 0) (hD : ∀ y, -D ≤ w0 y) (k : ℕ) (y : Y) :
    Φ (Φ^[k] v0) y - Φ^[k] v0 y ≤ s * σ ^ k * D ^ s := by
  have hD0 : 0 ≤ D := by linarith [hD y, hw00 y]
  set w : ℕ → Y → ℝ := fun k => Ψ^[k] w0 with hwdef
  have hw_succ : ∀ k, w (k + 1) = Ψ (w k) := fun k => Function.iterate_succ_apply' _ _ _
  have hle0 : ∀ k z, w k z ≤ 0 := by
    intro k
    cases k with
    | zero => exact hw00
    | succ k => intro z; rw [hw_succ]; exact hneg _ _
  have hsubk : ∀ k, w k ≤ Ψ (w k) := by
    intro k
    induction k with
    | zero => exact hw0
    | succ k ih => rw [hw_succ]; exact hmono ih
  have hinc : ∀ k, w0 ≤ w k := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih => rw [hw_succ]; exact ih.trans (hsubk k)
  -- `β`-coordinates: the residual is at most `σ^k D`
  have hres : ∀ k z, Ψ (w k) z - w k z ≤ σ ^ k * D := by
    intro k
    induction k with
    | zero =>
      intro z
      have h1 := hneg w0 z
      have h2 := hD z
      change Ψ w0 z - w0 z ≤ σ ^ 0 * D
      rw [pow_zero, one_mul]
      linarith
    | succ k ih =>
      intro z
      have h := (GlobalIterationProof.step_sub hmono hsub (hsubk k)
        (mul_nonneg (pow_nonneg hσ k) hD0) ih).2 z
      have e : σ * (σ ^ k * D) = σ ^ (k + 1) * D := by ring
      rw [hw_succ]
      linarith
  -- the iterates of `Φ` are those of `Ψ`, transformed
  have hiter : ∀ k, Φ^[k] v0 = fun z => -(-w k z) ^ s := by
    intro k
    induction k with
    | zero => funext z; exact hv0 z
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      funext z
      rw [hconj _ (fun z => neg_nonpos.2 (Real.rpow_nonneg (by linarith [hle0 k z]) _)) z]
      have h : (fun z => -(-(-(-w k z) ^ s)) ^ r) = w k := funext fun z => conj_inv hrs (hle0 k z)
      rw [h, ← hw_succ]
  -- `α`-coordinates, by lem:pow_cvx
  rw [← Function.iterate_succ_apply' Φ, hiter (k + 1), hiter k]
  have hb : 0 ≤ w (k + 1) y - w k y := by rw [hw_succ]; linarith [hsubk k y]
  have hbe : w (k + 1) y - w k y ≤ σ ^ k * D := by rw [hw_succ]; exact hres k y
  have h := diff_bound hs (by linarith [hle0 (k + 1) y]) hb hbe
    (show -w (k + 1) y + (w (k + 1) y - w k y) ≤ D by linarith [hinc k y, hD y])
  have hab : -w (k + 1) y + (w (k + 1) y - w k y) = -w k y := by ring
  rw [hab] at h
  have e : s * (σ ^ k * D) * D ^ (s - 1) = s * σ ^ k * (D * D ^ (s - 1)) := by ring
  rw [mul_rpow_sub_one hD0 hs] at e
  simp only
  linarith

/-- Super-solution version: the residual of the `k`-th iterate of `Φ` is at most `s σ^k D^s`,
where `D` bounds, in `β`-coordinates, a sub-solution `ŵ` below the starting map. -/
theorem sup_resid (hmono : Monotone Ψ) (hsub : ∀ y, SubAdditive σ (Ψ · y)) (hσ : 0 ≤ σ)
    (hneg : ∀ w y, Ψ w y ≤ 0) (hs : 1 ≤ s) (hrs : s * r = 1)
    (hconj : ∀ v : Y → ℝ, (∀ y, v y ≤ 0) → ∀ y, Φ v y = -(-Ψ (fun z => -(-v z) ^ r) y) ^ s)
    {w0 wHat v0 : Y → ℝ} (hv0 : ∀ y, v0 y = -(-w0 y) ^ s) (hw0 : Ψ w0 ≤ w0)
    (hw00 : ∀ y, w0 y ≤ 0) (hHat : wHat ≤ Ψ wHat) (hHatD : ∀ y, -D ≤ wHat y)
    (hHatle : wHat ≤ w0) (k : ℕ) (y : Y) :
    Φ^[k] v0 y - Φ (Φ^[k] v0) y ≤ s * σ ^ k * D ^ s := by
  have hD0 : 0 ≤ D := by linarith [hHatD y, hHatle y, hw00 y]
  set w : ℕ → Y → ℝ := fun k => Ψ^[k] w0 with hwdef
  have hw_succ : ∀ k, w (k + 1) = Ψ (w k) := fun k => Function.iterate_succ_apply' _ _ _
  have hle0 : ∀ k z, w k z ≤ 0 := by
    intro k
    cases k with
    | zero => exact hw00
    | succ k => intro z; rw [hw_succ]; exact hneg _ _
  have hsupk : ∀ k, Ψ (w k) ≤ w k := by
    intro k
    induction k with
    | zero => exact hw0
    | succ k ih => rw [hw_succ]; exact hmono ih
  have hlow : ∀ k, wHat ≤ w k := by
    intro k
    induction k with
    | zero => exact hHatle
    | succ k ih => rw [hw_succ]; exact hHat.trans (hmono ih)
  -- `β`-coordinates: the residual is at most `σ^k D`
  have hres : ∀ k z, w k z - Ψ (w k) z ≤ σ ^ k * D := by
    intro k
    induction k with
    | zero =>
      intro z
      have h1 : Ψ wHat z ≤ Ψ w0 z := hmono hHatle z
      have h2 := hHat z
      have h3 := hHatD z
      have h4 := hw00 z
      change w0 z - Ψ w0 z ≤ σ ^ 0 * D
      rw [pow_zero, one_mul]
      linarith
    | succ k ih =>
      intro z
      have h := (GlobalIterationProof.step_super hmono hsub (hsupk k)
        (mul_nonneg (pow_nonneg hσ k) hD0) ih).2 z
      have e : σ * (σ ^ k * D) = σ ^ (k + 1) * D := by ring
      rw [hw_succ]
      linarith
  have hiter : ∀ k, Φ^[k] v0 = fun z => -(-w k z) ^ s := by
    intro k
    induction k with
    | zero => funext z; exact hv0 z
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      funext z
      rw [hconj _ (fun z => neg_nonpos.2 (Real.rpow_nonneg (by linarith [hle0 k z]) _)) z]
      have h : (fun z => -(-(-(-w k z) ^ s)) ^ r) = w k := funext fun z => conj_inv hrs (hle0 k z)
      rw [h, ← hw_succ]
  rw [← Function.iterate_succ_apply' Φ, hiter (k + 1), hiter k]
  have hb : 0 ≤ w k y - w (k + 1) y := by rw [hw_succ]; linarith [hsupk k y]
  have hbe : w k y - w (k + 1) y ≤ σ ^ k * D := by rw [hw_succ]; exact hres k y
  have h := diff_bound hs (by linarith [hle0 k y]) hb hbe
    (show -w k y + (w k y - w (k + 1) y) ≤ D by linarith [hlow (k + 1) y, hHatD y])
  have hab : -w k y + (w k y - w (k + 1) y) = -w (k + 1) y := by ring
  rw [hab] at h
  have e : s * (σ ^ k * D) * D ^ (s - 1) = s * σ ^ k * (D * D ^ (s - 1)) := by ring
  rw [mul_rpow_sub_one hD0 hs] at e
  simp only
  linarith

end Core

/-! ### Kruzkov transforms with two timescales -/

variable {X : Type*}

/-- `E_β a = -(-E_α a)^(α/β)` on `ℝ_∞`. -/
theorem kruzkov_rpow {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (a : WithTop ℝ) :
    kruzkov (1 / β) a = -(-kruzkov (1 / α) a) ^ (α / β) := by
  induction a using WithTop.recTopCoe with
  | top =>
    change (0 : ℝ) = -(-(0 : ℝ)) ^ (α / β)
    rw [neg_zero, Real.zero_rpow (div_pos hα hβ).ne', neg_zero]
  | coe u =>
    have h := KruzkovRpowProof.kruzkov_mul_eq_neg_rpow (1 / α) (α / β) u
    rwa [show α / β * (1 / α) = 1 / β by field_simp] at h

/-- Conjugation: `Φ_α v = -(-Φ_β (-(-v)^(α/β)))^(β/α)` for `v ≤ 0`. -/
theorem conj {Λ : (X → ℝ) → X → ℝ} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (v : X → ℝ)
    (hv : ∀ y, v y ≤ 0) (y : X) :
    Global.kruzkovOp α Λ v y =
      -(-Global.kruzkovOp β Λ (fun z => -(-v z) ^ (α / β)) y) ^ (β / α) := by
  have key : (fun z => kruzkovInv β (-(-v z) ^ (α / β))) = fun z => kruzkovInv α (v z) :=
    funext fun z => by
      have h1 : v z = kruzkov (1 / α) (kruzkovInv α (v z)) :=
        (kruzkov_kruzkovInv hα.ne' (hv z)).symm
      rw [h1, ← kruzkov_rpow hα hβ, kruzkovInv_kruzkov hβ.ne', kruzkovInv_kruzkov hα.ne']
  change kruzkovOp α (Λ · y) v = -(-kruzkovOp β (Λ · y) (fun z => -(-v z) ^ (α / β))) ^ (β / α)
  unfold kruzkovOp
  rw [key]
  exact kruzkov_rpow hβ hα _

/-- The arithmetic of the bound: `s σ^N max(C, 0) ≤ η` for `N = ⌈(ln(C/η) + ln s)/(-ln σ)⌉₊`. -/
theorem final_le {s σ C η : ℝ} (hs : 0 < s) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hη : 0 < η) :
    s * σ ^ ⌈(Real.log (C / η) + Real.log s) / (-Real.log σ)⌉₊ * max C 0 ≤ η := by
  set N := ⌈(Real.log (C / η) + Real.log s) / (-Real.log σ)⌉₊ with hN
  rcases le_or_gt C 0 with hC0 | hC0
  · rw [max_eq_right hC0, mul_zero]; exact hη.le
  · rw [max_eq_left hC0.le]
    have h := GlobalIterationProof.pow_mul_le hσ0 hσ1 hη (s * C)
    have hlog : Real.log (s * C / η) = Real.log (C / η) + Real.log s := by
      rw [mul_div_assoc, Real.log_mul hs.ne' (div_pos hC0 hη).ne']
      ring
    rw [hlog, ← hN] at h
    have e : s * σ ^ N * C = σ ^ N * (s * C) := by ring
    linarith

/-- `w0 ≥ -max(C, 0)^(α/β)` when `v0 = -(-w0)^(β/α) ≥ -C`. -/
theorem lower_bound {α β C : ℝ} (hα : 0 < α) (hβ : 0 < β) {a b : ℝ} (hab : a = -(-b) ^ (β / α))
    (hb : b ≤ 0) (hC : -C ≤ a) : -(max C 0) ^ (α / β) ≤ b := by
  have hrs : β / α * (α / β) = 1 := by field_simp
  have hw : b = -(-a) ^ (α / β) := by rw [hab]; exact (conj_inv hrs hb).symm
  have ha : a ≤ 0 := by rw [hab]; exact neg_nonpos.2 (Real.rpow_nonneg (by linarith) _)
  rw [hw, neg_le_neg_iff]
  exact Real.rpow_le_rpow (neg_nonneg.2 ha) ((neg_le.1 hC).trans (le_max_left _ _))
    (div_pos hα hβ).le

/-- The bound on the passes of the sub-solution variant, for an arbitrary pair of conjugate
operators `Φ`, `Ψ` (in `α`- and `β`-coordinates), from a sub-solution `w0` of `Ψ`. -/
theorem core_subPasses_le {Y : Type*} {Φ Ψ : (Y → ℝ) → Y → ℝ} {α β σ : ℝ}
    (hmono : Monotone Ψ) (hsub : ∀ y, SubAdditive σ (Ψ · y)) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hneg : ∀ w y, Ψ w y ≤ 0) (hα : 0 < α) (hαβ : α ≤ β)
    (hconj : ∀ v : Y → ℝ, (∀ y, v y ≤ 0) → ∀ y,
      Φ v y = -(-Ψ (fun z => -(-v z) ^ (α / β)) y) ^ (β / α))
    {w0 v0 : Y → ℝ} (hv0 : ∀ y, v0 y = -(-w0 y) ^ (β / α)) (hw0 : w0 ≤ Ψ w0)
    (hw00 : ∀ y, w0 y ≤ 0) {C η : ℝ} (hC : ∀ y, -C ≤ v0 y) (hη : 0 < η) :
    globalIterSubPasses Φ η v0 ≤
      (⌈(Real.log (C / η) + Real.log (β / α)) / (-Real.log σ)⌉₊ : ℕ∞) := by
  have hβ : 0 < β := hα.trans_le hαβ
  have hs : 1 ≤ β / α := (one_le_div hα).2 hαβ
  have hrs : β / α * (α / β) = 1 := by field_simp
  have hDs : ((max C 0) ^ (α / β)) ^ (β / α) = max C 0 := by
    rw [← Real.rpow_mul (le_max_right _ _), show α / β * (β / α) = 1 by field_simp,
      Real.rpow_one]
  refine subPasses_le_of_iterate fun y => ?_
  have h := sub_resid hmono hsub hσ0.le hneg hs hrs hconj hv0 hw0 hw00
    (fun y => lower_bound hα hβ (hv0 y) (hw00 y) (hC y))
    ⌈(Real.log (C / η) + Real.log (β / α)) / (-Real.log σ)⌉₊ y
  rw [hDs] at h
  linarith [final_le (C := C) (div_pos hβ hα) hσ0 hσ1 hη]

/-- The bound on the passes of the super-solution version, for an arbitrary pair of conjugate
operators `Φ`, `Ψ`, from a super-solution `w1` of `Ψ` above a sub-solution `w0`. -/
theorem core_passes_le_sup {Y : Type*} {Φ Ψ : (Y → ℝ) → Y → ℝ} {α β σ : ℝ}
    (hmono : Monotone Ψ) (hsub : ∀ y, SubAdditive σ (Ψ · y)) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hneg : ∀ w y, Ψ w y ≤ 0) (hα : 0 < α) (hαβ : α ≤ β)
    (hconj : ∀ v : Y → ℝ, (∀ y, v y ≤ 0) → ∀ y,
      Φ v y = -(-Ψ (fun z => -(-v z) ^ (α / β)) y) ^ (β / α))
    {w0 v0 w1 v1 : Y → ℝ} (hv0 : ∀ y, v0 y = -(-w0 y) ^ (β / α))
    (hv1 : ∀ y, v1 y = -(-w1 y) ^ (β / α)) (hw0 : w0 ≤ Ψ w0) (hw1 : Ψ w1 ≤ w1)
    (hw00 : ∀ y, w0 y ≤ 0) (hw10 : ∀ y, w1 y ≤ 0) (hle : w0 ≤ w1) {C η : ℝ}
    (hC : ∀ y, -C ≤ v0 y) (hη : 0 < η) :
    globalIterPasses Φ η v1 ≤
      (⌈(Real.log (C / η) + Real.log (β / α)) / (-Real.log σ)⌉₊ : ℕ∞) := by
  have hβ : 0 < β := hα.trans_le hαβ
  have hs : 1 ≤ β / α := (one_le_div hα).2 hαβ
  have hrs : β / α * (α / β) = 1 := by field_simp
  have hDs : ((max C 0) ^ (α / β)) ^ (β / α) = max C 0 := by
    rw [← Real.rpow_mul (le_max_right _ _), show α / β * (β / α) = 1 by field_simp,
      Real.rpow_one]
  refine passes_le_of_iterate fun y => ?_
  have h := sup_resid hmono hsub hσ0.le hneg hs hrs hconj hv1 hw1 hw10 hw0
    (fun y => lower_bound hα hβ (hv0 y) (hw00 y) (hC y)) hle
    ⌈(Real.log (C / η) + Real.log (β / α)) / (-Real.log σ)⌉₊ y
  rw [hDs] at h
  linarith [final_le (C := C) (div_pos hβ hα) hσ0 hσ1 hη]

/-- lem:cplx_global_iteration_withUnknown: the global iteration for `Φ_α` stops within
`⌈(ln(C/η) + ln(β/α))/(-ln σ)⌉` passes when `Φ_β` is `σ`-sub-additive (constant of
lem:pow_cvx). -/
theorem passes_le [Finite X] {Λ : (X → ℝ) → X → ℝ} (hΛmono : ∀ x, Monotone (Λ · x)) {α β σ : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hsub : ∀ x, SubAdditive σ (kruzkovOp β (Λ · x))) {uSub : X → ℝ} {uSup : X → WithTop ℝ}
    (huSub : uSub ≤ Λ uSub) (huSup : Global.monotoneExtension Λ uSup ≤ uSup) {C η : ℝ}
    (hC : ∀ x, -C ≤ kruzkov (1 / α) (uSub x)) (hη : 0 < η) :
    globalIterSubPasses (Global.kruzkovOp α Λ) η (fun x => kruzkov (1 / α) (uSub x)) ≤
        (⌈(Real.log (C / η) + Real.log (β / α)) / (-Real.log σ)⌉₊ : ℕ∞) ∧
      globalIterPasses (Global.kruzkovOp α Λ) η (fun x => kruzkov (1 / α) (uSup x)) ≤
        (⌈(Real.log (C / η) + Real.log (β / α)) / (-Real.log σ)⌉₊ : ℕ∞) := by
  have hβ : 0 < β := hα.trans_le hαβ
  have hmono := ParallelAgsiKruzkovProof.monotone_global_kruzkovOp (Λ := Λ) hβ
  have hneg : ∀ w y, Global.kruzkovOp β Λ w y ≤ 0 := fun w y => kruzkov_nonpos _ _
  -- the order `ū ≤ u̲`, by the comparison principle
  have hcomp := Ext.hasComparisonPrinciple_of_kruzkov hβ hσ1 (I := Set.univ)
    (fun x _ => hsub x) (fun x => ((uSub x : ℝ) : WithTop ℝ)) uSup
    (fun x _ => by
      change ((uSub x : ℝ) : WithTop ℝ) ≤
        monotoneExtension (Λ · x) (fun z => ((uSub z : ℝ) : WithTop ℝ))
      rw [MonotoneExtension.coe_eq (hΛmono x)]
      exact WithTop.coe_le_coe.2 (huSub x))
    (fun x _ => huSup x) (fun x hx => absurd (Set.mem_univ x) hx)
  have hw0 : (fun x => kruzkov (1 / β) ((uSub x : ℝ) : WithTop ℝ)) ≤
      Global.kruzkovOp β Λ (fun x => kruzkov (1 / β) ((uSub x : ℝ) : WithTop ℝ)) := fun y => by
    change _ ≤ kruzkovOp β (Λ · y) _
    rw [ComparisonLambdaProof.kruzkovOp_kruzkov hβ.ne' (hΛmono y)]
    exact (ComparisonLambdaProof.kruzkov_coe_le_iff hβ _ _).2 (huSub y)
  have hw1 : Global.kruzkovOp β Λ (fun x => kruzkov (1 / β) (uSup x)) ≤
      fun x => kruzkov (1 / β) (uSup x) := fun y => by
    change kruzkovOp β (Λ · y) _ ≤ _
    rw [kruzkovOp_kruzkov_ext hβ.ne']
    exact (kruzkov_le_iff hβ _ _).2 (huSup y)
  exact ⟨core_subPasses_le hmono (fun y => hsub y) hσ0 hσ1 hneg hα hαβ
      (fun v hv y => conj hα hβ v hv y) (fun y => kruzkov_rpow hβ hα _) hw0
      (fun y => kruzkov_nonpos _ _) hC hη,
    core_passes_le_sup hmono (fun y => hsub y) hσ0 hσ1 hneg hα hαβ
      (fun v hv y => conj hα hβ v hv y) (fun y => kruzkov_rpow hβ hα _)
      (fun y => kruzkov_rpow hβ hα _) hw0 hw1 (fun y => kruzkov_nonpos _ _)
      (fun y => kruzkov_nonpos _ _) (fun y => (kruzkov_le_iff hβ _ _).2 (hcomp y)) hC hη⟩

end GuaranteedSubsol.GlobalIterKruzkovProof
