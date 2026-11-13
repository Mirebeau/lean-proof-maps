/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.Kruzkov
public import Mathlib.Topology.Order.WithTop
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Monotone extension: agreement with the paper

Provider proofs for the frozen anchors `GuaranteedSubsol.monotoneExtension_coe` and
`GuaranteedSubsol.tendsto_monotoneExtension` (see `ANCHORS.md`): for monotone `Λ`, the generalized
`monotoneExtension` (supremum over finite minorants) coincides with `Λ` on finite values, and with
the paper's limit `lim_{t→∞} Λ min {u,t}` (Intro.tex eq. eqdef:monotone_extension) when `X` is
finite.
-/

@[expose] public section

namespace GuaranteedSubsol.MonotoneExtension

open Filter Topology

variable {X : Type*} {Λ : (X → ℝ) → ℝ}

theorem coe_eq (hΛ : Monotone Λ) (u : X → ℝ) :
    monotoneExtension Λ (fun y => (u y : WithTop ℝ)) = (Λ u : WithTop ℝ) := by
  have : Nonempty {w : X → ℝ // ∀ y, (w y : WithTop ℝ) ≤ u y} := ⟨⟨u, fun _ => le_rfl⟩⟩
  exact le_antisymm
    (ciSup_le fun w => WithTop.coe_le_coe.2 (hΛ fun y => WithTop.coe_le_coe.1 (w.2 y)))
    (le_ciSup (f := fun w : {w : X → ℝ // ∀ y, (w y : WithTop ℝ) ≤ u y} =>
      ((Λ w : ℝ) : WithTop ℝ)) (OrderTop.bddAbove _) ⟨u, fun _ => le_rfl⟩)

private theorem trunc_le (u : X → WithTop ℝ) (t : ℝ) (y : X) :
    ((min ((u y).untopD t) t : ℝ) : WithTop ℝ) ≤ u y := by
  cases h : u y with
  | top => exact le_top
  | coe r => exact WithTop.coe_le_coe.2 (by simp)

private theorem trunc_mono (u : X → WithTop ℝ) {t s : ℝ} (hts : t ≤ s) (y : X) :
    min ((u y).untopD t) t ≤ min ((u y).untopD s) s := by
  cases h : u y with
  | top => simpa using hts
  | coe r => simpa using min_le_min_left r hts

theorem tendsto [Finite X] (hΛ : Monotone Λ) (u : X → WithTop ℝ) :
    Tendsto (fun t : ℝ => ((Λ fun y => min ((u y).untopD t) t : ℝ) : WithTop ℝ)) atTop
      (𝓝 (monotoneExtension Λ u)) := by
  set f : ℝ → WithTop ℝ := fun t => ((Λ fun y => min ((u y).untopD t) t : ℝ) : WithTop ℝ)
  have hf : Monotone f := fun t s hts =>
    WithTop.coe_le_coe.2 (hΛ fun y => trunc_mono u hts y)
  suffices h : monotoneExtension Λ u = ⨆ t, f t by
    rw [h]; exact tendsto_atTop_ciSup hf (OrderTop.bddAbove _)
  have : Nonempty {w : X → ℝ // ∀ y, (w y : WithTop ℝ) ≤ u y} :=
    ⟨⟨fun y => min ((u y).untopD 0) 0, trunc_le u 0⟩⟩
  refine le_antisymm (ciSup_le fun w => ?_) (ciSup_le fun t => ?_)
  · obtain ⟨M, hM⟩ := (Set.finite_range w.1).bddAbove
    have hwM : ∀ y, w.1 y ≤ M := fun y => hM ⟨y, rfl⟩
    refine le_trans (WithTop.coe_le_coe.2 (hΛ fun y => le_min ?_ (hwM y)))
      (le_ciSup (f := f) (OrderTop.bddAbove _) M)
    have := w.2 y
    cases h : u y with
    | top => simpa using hwM y
    | coe r => rw [h] at this; simpa using WithTop.coe_le_coe.1 this
  · exact le_ciSup (f := fun w : {w : X → ℝ // ∀ y, (w y : WithTop ℝ) ≤ u y} =>
      ((Λ w : ℝ) : WithTop ℝ)) (OrderTop.bddAbove _) ⟨_, trunc_le u t⟩

end GuaranteedSubsol.MonotoneExtension
