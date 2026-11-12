/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.AxiomsExt
import LeanHJBAutoformalisation.GuaranteedSubsol.KruzkovProof

/-!
# Transfer of the scheme axioms to the monotone extension

The scalar axioms of `Axioms.lean`, satisfied by an operator `Λ : (X → ℝ) → ℝ`, transfer to its
monotone extension `Λ_∞ = monotoneExtension Λ : (X → ℝ_∞) → ℝ_∞` (`Kruzkov.lean`), as the
corresponding axioms of `AxiomsExt.lean` (namespace `GuaranteedSubsol.Ext`).

Memory and (strict) causality additionally require `Λ` monotone and `X` finite: then
`Λ_∞ u` is the supremum of `Λ min {u,s}` over `s : ℝ`, and the truncations `min {u,s}` satisfy
the hypotheses of the real axioms. The other axioms transfer for an arbitrary `Λ`, by
transforming the finite minorants in the supremum defining `Λ_∞`.
-/

namespace GuaranteedSubsol

namespace AxiomsExtTransfer

open KruzkovProof

variable {X : Type*}

/-- The truncation `min {u, s}` is a finite minorant of `u`. -/
theorem trunc_le (u : X → WithTop ℝ) (s : ℝ) (y : X) :
    ((min ((u y).untopD s) s : ℝ) : WithTop ℝ) ≤ u y := by
  cases h : u y with
  | top => exact le_top
  | coe r => exact WithTop.coe_le_coe.2 (by simp)

/-- A finite minorant of `u` bounded by `s` lies below the truncation `min {u, s}`. -/
theorem le_trunc {u : X → WithTop ℝ} {w : X → ℝ} (hw : ∀ y, (w y : WithTop ℝ) ≤ u y) {s : ℝ}
    (hs : ∀ y, w y ≤ s) (y : X) : w y ≤ min ((u y).untopD s) s := by
  refine le_min ?_ (hs y)
  have := hw y
  cases h : u y with
  | top => simpa using hs y
  | coe r => rw [h] at this; simpa using WithTop.coe_le_coe.1 this

/-- `Λ min {u, s} ≤ Λ_∞ u`. -/
theorem trunc_le_ext (Λ : (X → ℝ) → ℝ) (u : X → WithTop ℝ) (s : ℝ) :
    ((Λ fun y => min ((u y).untopD s) s : ℝ) : WithTop ℝ) ≤ monotoneExtension Λ u :=
  le_monotoneExtension Λ _ (trunc_le u s)

/-- For monotone `Λ` and finite `X`, a common bound on `Λ min {u, s}` for all `s ≥ s₀`
bounds `Λ_∞ u`. -/
theorem ext_le_of_trunc [Finite X] {Λ : (X → ℝ) → ℝ} (hΛ : Monotone Λ) {u : X → WithTop ℝ}
    {b : WithTop ℝ} (s₀ : ℝ)
    (h : ∀ s, s₀ ≤ s → ((Λ fun y => min ((u y).untopD s) s : ℝ) : WithTop ℝ) ≤ b) :
    monotoneExtension Λ u ≤ b := by
  have := nonempty_minorant u
  refine ciSup_le fun w => ?_
  obtain ⟨M, hM⟩ := (Set.finite_range w.1).bddAbove
  have hwM : ∀ y, w.1 y ≤ max M s₀ := fun y => (hM ⟨y, rfl⟩).trans (le_max_left _ _)
  exact (WithTop.coe_le_coe.2 (hΛ (le_trunc w.2 hwM))).trans (h _ (le_max_right _ _))

/-- For `t ≤ s`, `min {a.untopD s, t} = min {a, t}` in `ℝ_∞`. -/
theorem coe_min_untopD (a : WithTop ℝ) {s t : ℝ} (hts : t ≤ s) :
    ((min (a.untopD s) t : ℝ) : WithTop ℝ) = min a (t : WithTop ℝ) := by
  cases a with
  | top => simpa using hts
  | coe r => simp

/-- For `t ≤ s`, `min {min {a, s}, t} = min {a, t}` in `ℝ_∞`. -/
theorem coe_min_trunc (a : WithTop ℝ) {s t : ℝ} (hts : t ≤ s) :
    ((min (min (a.untopD s) s) t : ℝ) : WithTop ℝ) = min a (t : WithTop ℝ) := by
  rw [min_assoc, min_eq_right hts, coe_min_untopD a hts]

/-- If `max {a, t} = max {b, t}`, the truncations at any level `s` satisfy the same identity. -/
theorem max_trunc_eq {a b : WithTop ℝ} {t : ℝ} (s : ℝ)
    (hab : max a (t : WithTop ℝ) = max b (t : WithTop ℝ)) :
    max (min (a.untopD s) s) t = max (min (b.untopD s) s) t := by
  cases a with
  | top =>
    cases b with
    | top => rfl
    | coe r =>
      rw [← WithTop.coe_max, max_eq_left le_top] at hab
      exact absurd hab WithTop.top_ne_coe
  | coe r =>
    cases b with
    | top =>
      rw [← WithTop.coe_max, max_eq_left (le_top : (t : WithTop ℝ) ≤ ⊤)] at hab
      exact absurd hab WithTop.coe_ne_top
    | coe r' =>
      rw [← WithTop.coe_max, ← WithTop.coe_max, WithTop.coe_inj] at hab
      simp only [WithTop.untopD_coe]
      rw [max_min_distrib_right, max_min_distrib_right, hab]

/-- One inequality for the transfer of (strict) causality: if, for all `s ≥ t`, the truncations
satisfy `min {Λ min {u,s}, c} = min {Λ min {v,s}, c}`, then `min {Λ_∞ u, c} ≤ min {Λ_∞ v, c}`. -/
theorem min_ext_le [Finite X] {Λ : (X → ℝ) → ℝ} (hΛ : Monotone Λ) {u v : X → WithTop ℝ}
    {t c : ℝ}
    (h : ∀ s, t ≤ s → min (Λ fun y => min ((u y).untopD s) s) c =
      min (Λ fun y => min ((v y).untopD s) s) c) :
    min (monotoneExtension Λ u) (c : WithTop ℝ) ≤ min (monotoneExtension Λ v) (c : WithTop ℝ) := by
  rcases le_or_gt (c : WithTop ℝ) (monotoneExtension Λ v) with hc | hc
  · rw [min_eq_right hc]
    exact min_le_right _ _
  · refine min_le_min (ext_le_of_trunc hΛ t fun s hs => ?_) le_rfl
    have hv : (Λ fun y => min ((v y).untopD s) s) < c :=
      WithTop.coe_lt_coe.1 ((trunc_le_ext Λ v s).trans_lt hc)
    have hs' := h s hs
    rw [min_eq_left hv.le] at hs'
    have hu : (Λ fun y => min ((u y).untopD s) s) = Λ fun y => min ((v y).untopD s) s := by
      rcases le_total (Λ fun y => min ((u y).untopD s) s) c with h1 | h1
      · rwa [min_eq_left h1] at hs'
      · rw [min_eq_right h1] at hs'
        linarith
    rw [hu]
    exact trunc_le_ext Λ v s

/-- If `w ≤ a + c` with `w`, `c` finite, then `w - c ≤ a`. -/
theorem sub_le_of_le_add {w c : ℝ} {a : WithTop ℝ} (h : (w : WithTop ℝ) ≤ a + c) :
    ((w - c : ℝ) : WithTop ℝ) ≤ a := by
  cases a with
  | top => exact le_top
  | coe r =>
    rw [← WithTop.coe_add] at h
    exact WithTop.coe_le_coe.2 (by linarith [WithTop.coe_le_coe.1 h])

/-- If `w ≤ c a` with `c > 0` and `w` finite, then `w / c ≤ a`. -/
theorem div_le_of_le_mul {w c : ℝ} {a : WithTop ℝ} (hc : 0 < c) (h : (w : WithTop ℝ) ≤ c * a) :
    ((w / c : ℝ) : WithTop ℝ) ≤ a := by
  cases a with
  | top => exact le_top
  | coe r =>
    rw [← WithTop.coe_mul] at h
    exact WithTop.coe_le_coe.2 ((div_le_iff₀ hc).2 (by linarith [WithTop.coe_le_coe.1 h]))

/-- If `w ≤ a` with `w` finite and `c > 0`, then `c w ≤ c a`. -/
theorem mul_le_mul_of_le {w c : ℝ} {a : WithTop ℝ} (hc : 0 < c) (h : (w : WithTop ℝ) ≤ a) :
    ((c * w : ℝ) : WithTop ℝ) ≤ c * a := by
  cases a with
  | top =>
    rw [WithTop.mul_top (by exact_mod_cast hc.ne')]
    exact le_top
  | coe r =>
    rw [← WithTop.coe_mul]
    exact WithTop.coe_le_coe.2 (mul_le_mul_of_nonneg_left (WithTop.coe_le_coe.1 h) hc.le)

end AxiomsExtTransfer

open AxiomsExtTransfer KruzkovProof

variable {X : Type*} {Λ Γ : (X → ℝ) → ℝ}

/-- Additive invariance transfers to the monotone extension. -/
theorem AdditivelyInvariant.ext (h : AdditivelyInvariant Λ) :
    Ext.AdditivelyInvariant (monotoneExtension Λ) :=
  fun u t => monotoneExtension_add_const h u t

/-- `C_past`-memory transfers to the monotone extension of a monotone operator. -/
theorem HasMemory.ext [Finite X] (hmono : Monotone Λ) {C : ℝ} (h : HasMemory C Λ) :
    Ext.HasMemory C (monotoneExtension Λ) := by
  have key : ∀ (u v : X → WithTop ℝ) (t : ℝ), (∀ y, max (u y) t = max (v y) t) →
      monotoneExtension Λ u ≤ max (monotoneExtension Λ v) ((t + C : ℝ) : WithTop ℝ) := by
    intro u v t huv
    refine ext_le_of_trunc hmono t fun s _ => ?_
    have hs := h (fun y => min ((u y).untopD s) s) (fun y => min ((v y).untopD s) s) t
      (fun y => max_trunc_eq s (huv y))
    calc ((Λ fun y => min ((u y).untopD s) s : ℝ) : WithTop ℝ)
        ≤ ((max (Λ fun y => min ((u y).untopD s) s) (t + C) : ℝ) : WithTop ℝ) :=
          WithTop.coe_le_coe.2 (le_max_left _ _)
      _ = max ((Λ fun y => min ((v y).untopD s) s : ℝ) : WithTop ℝ)
          ((t + C : ℝ) : WithTop ℝ) := by rw [hs, WithTop.coe_max]
      _ ≤ _ := max_le ((trunc_le_ext Λ v s).trans (le_max_left _ _)) (le_max_right _ _)
  intro u v t huv
  exact le_antisymm (max_le (key u v t huv) (le_max_right _ _))
    (max_le (key v u t fun y => (huv y).symm) (le_max_right _ _))

/-- Causality transfers to the monotone extension of a monotone operator. -/
theorem Causal.ext [Finite X] (hmono : Monotone Λ) (h : Causal Λ) :
    Ext.Causal (monotoneExtension Λ) := by
  intro u v t huv
  have hT : (fun y => min ((u y).untopD t) t) = fun y => min ((v y).untopD t) t := by
    funext y
    apply WithTop.coe_injective
    rw [coe_min_untopD _ le_rfl, coe_min_untopD _ le_rfl, huv y]
  -- if `Λ min {u,t} ≤ t`, then `Λ min {u,s} = Λ min {u,t}` for `s ≥ t`, so `Λ_∞ u = Λ min {u,t}`
  have key : ∀ u : X → WithTop ℝ, (Λ fun y => min ((u y).untopD t) t) ≤ t →
      monotoneExtension Λ u = ((Λ fun y => min ((u y).untopD t) t : ℝ) : WithTop ℝ) := by
    intro u ha
    refine le_antisymm (ext_le_of_trunc hmono t fun s hs => le_of_eq ?_) (trunc_le_ext Λ u t)
    obtain ⟨δ, hδ, hs'⟩ := h (fun y => min ((u y).untopD s) s)
      (fun y => min ((u y).untopD t) t) t fun y => by
        apply WithTop.coe_injective
        rw [coe_min_trunc _ hs, coe_min_trunc _ le_rfl]
    rw [min_eq_left (by linarith : (Λ fun y => min ((u y).untopD t) t) ≤ t + δ)] at hs'
    rcases le_total (Λ fun y => min ((u y).untopD s) s) (t + δ) with h1 | h1
    · rw [min_eq_left h1] at hs'
      rw [hs']
    · rw [min_eq_right h1] at hs'
      linarith
  obtain ⟨a, ha⟩ : ∃ a, (Λ fun y => min ((u y).untopD t) t) = a := ⟨_, rfl⟩
  have hav : (Λ fun y => min ((v y).untopD t) t) = a := by rw [← hT, ha]
  rcases le_or_gt a t with hat | hat
  · refine ⟨1, one_pos, ?_⟩
    rw [key u (ha ▸ hat), key v (hav ▸ hat), ha, hav]
  · refine ⟨a - t, sub_pos.2 hat, ?_⟩
    have hta : t + (a - t) = a := by ring
    have hu : ((t + (a - t) : ℝ) : WithTop ℝ) ≤ monotoneExtension Λ u := by
      rw [hta, ← ha]
      exact trunc_le_ext Λ u t
    have hv : ((t + (a - t) : ℝ) : WithTop ℝ) ≤ monotoneExtension Λ v := by
      rw [hta, ← hav]
      exact trunc_le_ext Λ v t
    rw [min_eq_right hu, min_eq_right hv]

/-- `δ`-strict causality transfers to the monotone extension of a monotone operator. -/
theorem StrictlyCausal.ext [Finite X] (hmono : Monotone Λ) {δ : ℝ} (h : StrictlyCausal δ Λ) :
    Ext.StrictlyCausal δ (monotoneExtension Λ) := by
  have key : ∀ (u v : X → WithTop ℝ) (t : ℝ), (∀ y, min (u y) t = min (v y) t) →
      min (monotoneExtension Λ u) ((t + δ : ℝ) : WithTop ℝ) ≤
        min (monotoneExtension Λ v) ((t + δ : ℝ) : WithTop ℝ) := by
    intro u v t huv
    refine min_ext_le hmono (t := t) fun s hs => h _ _ t fun y => ?_
    apply WithTop.coe_injective
    rw [coe_min_trunc _ hs, coe_min_trunc _ hs, huv y]
  intro u v t huv
  exact le_antisymm (key u v t huv) (key v u t fun y => (huv y).symm)

/-- `ν`-sub-multiplicativity transfers to the monotone extension. -/
theorem SubMultiplicative.ext {ν : ℝ} (h : SubMultiplicative ν Λ) :
    Ext.SubMultiplicative ν (monotoneExtension Λ) := by
  intro t ht u
  have h1 : (0 : ℝ) < 1 + t := by linarith
  cases hu : monotoneExtension Λ u with
  | top =>
    rw [WithTop.mul_top (by exact_mod_cast h1.ne')]
    exact le_top
  | coe m =>
    have hle : monotoneExtension Λ (fun y => ((1 + t : ℝ) : WithTop ℝ) * u y) ≤
        (((1 + t) * m - ν * t : ℝ) : WithTop ℝ) := by
      have := nonempty_minorant fun y => ((1 + t : ℝ) : WithTop ℝ) * u y
      refine ciSup_le fun w => ?_
      have hw : ∀ y, ((w.1 y / (1 + t) : ℝ) : WithTop ℝ) ≤ u y :=
        fun y => div_le_of_le_mul h1 (w.2 y)
      have hm := le_monotoneExtension Λ _ hw
      rw [hu] at hm
      have hΛ := h t ht fun y => w.1 y / (1 + t)
      have heq : (fun y => (1 + t) * (w.1 y / (1 + t))) = w.1 := by
        funext y
        field_simp
      rw [heq] at hΛ
      have := mul_le_mul_of_nonneg_left (WithTop.coe_le_coe.1 hm) h1.le
      exact WithTop.coe_le_coe.2 (by linarith)
    calc _ ≤ (((1 + t) * m - ν * t : ℝ) : WithTop ℝ) + ((ν * t : ℝ) : WithTop ℝ) := by gcongr
      _ = ((1 + t : ℝ) : WithTop ℝ) * (m : WithTop ℝ) := by
        rw [← WithTop.coe_add, ← WithTop.coe_mul]
        congr 1
        ring

/-- `ρ`-sub-additivity transfers to the monotone extension. -/
theorem SubAdditive.ext {ρ : ℝ} (h : SubAdditive ρ Λ) :
    Ext.SubAdditive ρ (monotoneExtension Λ) := by
  intro v t ht
  have := nonempty_minorant fun y => v y + (t : WithTop ℝ)
  refine ciSup_le fun w => ?_
  have hw : ∀ y, ((w.1 y - t : ℝ) : WithTop ℝ) ≤ v y := fun y => sub_le_of_le_add (w.2 y)
  have hΛ : Λ w.1 ≤ Λ (fun y => w.1 y - t) + ρ * t := by
    simpa using h (fun y => w.1 y - t) t ht
  calc ((Λ w.1 : ℝ) : WithTop ℝ) ≤ ((Λ (fun y => w.1 y - t) + ρ * t : ℝ) : WithTop ℝ) :=
        WithTop.coe_le_coe.2 hΛ
    _ = ((Λ (fun y => w.1 y - t) : ℝ) : WithTop ℝ) + ((ρ * t : ℝ) : WithTop ℝ) :=
        WithTop.coe_add _ _
    _ ≤ _ := by gcongr; exact le_monotoneExtension Λ _ hw

/-- A stencil of `Λ` is a stencil of its monotone extension. -/
theorem HasStencil.ext {V : Set X} (h : HasStencil V Λ) :
    Ext.HasStencil V (monotoneExtension Λ) := by
  classical
  have key : ∀ u v : X → WithTop ℝ, (∀ y ∈ V, u y = v y) →
      monotoneExtension Λ u ≤ monotoneExtension Λ v := by
    intro u v huv
    have := nonempty_minorant u
    refine ciSup_le fun w => ?_
    let w' : X → ℝ := fun y => if y ∈ V then w.1 y else min ((v y).untopD 0) 0
    have hw' : ∀ y, (w' y : WithTop ℝ) ≤ v y := by
      intro y
      by_cases hy : y ∈ V
      · simp only [w', hy, ↓reduceIte]
        exact (w.2 y).trans (huv y hy).le
      · simp only [w', hy, ↓reduceIte]
        exact trunc_le v 0 y
    rw [h w.1 w' fun y hy => by simp [w', hy]]
    exact le_monotoneExtension Λ w' hw'
  intro u v huv
  exact le_antisymm (key u v huv) (key v u fun y hy => (huv y hy).symm)

/-- `C_past`-dependency transfers to the monotone extension. -/
theorem HasDependency.ext {C : ℝ} {V : Set X} (h : HasDependency C V Λ) :
    Ext.HasDependency C V (monotoneExtension Λ) := by
  refine ⟨HasStencil.ext h.1, fun u y hy => ?_⟩
  cases hu : u y with
  | top =>
    rw [WithTop.add_top]
    exact le_top
  | coe r =>
    have := nonempty_minorant u
    refine ciSup_le fun w => ?_
    have hwy : w.1 y ≤ r := by
      have := w.2 y
      rw [hu] at this
      exact WithTop.coe_le_coe.1 this
    rw [← WithTop.coe_add]
    exact WithTop.coe_le_coe.2 ((h.2 w.1 y hy).trans (by linarith))

/-- `C_Γ,C'_Γ`-comparison transfers to the monotone extensions, for `C > 0`. -/
theorem Comparable.ext {C C' : ℝ} (hC : 0 < C) (h : Comparable C C' Λ Γ) :
    Ext.Comparable C C' (monotoneExtension Λ) (monotoneExtension Γ) := by
  intro u
  constructor
  · cases hm : monotoneExtension Λ (fun y => (C : WithTop ℝ) * u y) with
    | top =>
      rw [WithTop.top_add]
      exact le_top
    | coe m =>
      have hle : monotoneExtension Λ u ≤ (((m + C') / C : ℝ) : WithTop ℝ) := by
        have := nonempty_minorant u
        refine ciSup_le fun w => ?_
        have hw : ∀ y, ((C * w.1 y : ℝ) : WithTop ℝ) ≤ (C : WithTop ℝ) * u y :=
          fun y => mul_le_mul_of_le hC (w.2 y)
        have h1 := le_monotoneExtension Λ _ hw
        rw [hm] at h1
        have h2 := (h w.1).1
        refine WithTop.coe_le_coe.2 ((le_div_iff₀ hC).2 ?_)
        linarith [WithTop.coe_le_coe.1 h1]
      obtain ⟨l, hl⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hle)
      rw [← hl] at hle ⊢
      rw [← WithTop.coe_mul, ← WithTop.coe_add]
      have := (le_div_iff₀ hC).1 (WithTop.coe_le_coe.1 hle)
      exact WithTop.coe_le_coe.2 (by linarith)
  · cases hg : monotoneExtension Γ u with
    | top =>
      rw [WithTop.mul_top (by exact_mod_cast hC.ne')]
      exact le_top
    | coe g =>
      have := nonempty_minorant fun y => (C : WithTop ℝ) * u y
      refine ciSup_le fun w => ?_
      have hw : ∀ y, ((w.1 y / C : ℝ) : WithTop ℝ) ≤ u y := fun y => div_le_of_le_mul hC (w.2 y)
      have h1 := le_monotoneExtension Γ _ hw
      rw [hg] at h1
      have h2 := (h fun y => w.1 y / C).2
      have heq : (fun y => C * (w.1 y / C)) = w.1 := by
        funext y
        field_simp
      rw [heq] at h2
      rw [← WithTop.coe_mul]
      exact WithTop.coe_le_coe.2
        (h2.trans (mul_le_mul_of_nonneg_left (WithTop.coe_le_coe.1 h1) hC.le))

end GuaranteedSubsol
