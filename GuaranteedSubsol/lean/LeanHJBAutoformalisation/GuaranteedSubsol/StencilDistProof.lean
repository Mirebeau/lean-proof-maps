/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import LeanHJBAutoformalisation.GuaranteedSubsol.StencilDist
import LeanHJBAutoformalisation.GuaranteedSubsol.Axioms
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Finite.Range
import Mathlib.Tactic.Linarith

/-!
# Super-solution from the distance to the boundary: proofs

Provider proofs for the frozen anchors `GuaranteedSubsol.superSolution_stencilDist` and
`GuaranteedSubsol.exists_superSolution_of_connected` (Prop. prop:constr_Gamma, super-solution
part), see `ANCHORS.md`.

On the boundary, `d_V(x, ∂X) = 0` and `u = M ≥ u_bd = Λ u`. At an interior point `x`, connectivity
makes `d := d_V(x, ∂X)` finite, `d = m + 1`, and some `y ∈ V x` has `d_V(y, ∂X) ≤ m`, so that
`Λ u(x) ≤ C_past + u(y) ≤ C_past (m + 1) + M = u(x)`.
-/

namespace GuaranteedSubsol.StencilDistProof

variable {X : Type*} {I : Set X} {V : X → Set X}

/-- A stencil path from `x` to the boundary gives a finite distance. -/
theorem exists_reach_of_transGen {x z : X} (hz : z ∉ I)
    (h : Relation.TransGen (fun a b => a ∈ I ∧ b ∈ V a) x z) : ∃ n, stencilReach I V n x := by
  induction h using Relation.TransGen.head_induction_on with
  | single hxz => exact ⟨1, hxz.1, z, hxz.2, hz⟩
  | head hxc _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, hxc.1, _, hxc.2, hn⟩

theorem reach_stencilDist {x : X} (h : ∃ n, stencilReach I V n x) :
    stencilReach I V (stencilDist I V x) x := by
  classical
  unfold stencilDist
  split_ifs
  exact Nat.find_spec h

theorem stencilDist_le {x : X} {m : ℕ} (h : stencilReach I V m x) : stencilDist I V x ≤ m := by
  classical
  unfold stencilDist
  split_ifs with h'
  · exact Nat.find_min' _ h
  · exact absurd ⟨m, h⟩ h'

theorem stencilDist_of_notMem {x : X} (hx : x ∉ I) : stencilDist I V x = 0 :=
  Nat.le_zero.1 (stencilDist_le (m := 0) hx)

theorem superSolution_stencilDist {Λ : (X → ℝ) → X → ℝ} {ubd : X → ℝ}
    (hbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) {Cpast M : ℝ} (hCpast : 0 ≤ Cpast)
    (hM : ∀ x ∉ I, ubd x ≤ M) (hdep : ∀ x ∈ I, HasDependency Cpast (V x) (Λ · x))
    (hconn : ∀ x ∈ I, ∃ z ∉ I, Relation.TransGen (fun a b => a ∈ I ∧ b ∈ V a) x z) :
    Λ (fun x => Cpast * stencilDist I V x + M) ≤ fun x => Cpast * stencilDist I V x + M := by
  intro x
  by_cases hx : x ∈ I
  · obtain ⟨z, hz, hxz⟩ := hconn x hx
    have hreach := reach_stencilDist (exists_reach_of_transGen hz hxz)
    obtain ⟨m, hm⟩ : ∃ m, stencilDist I V x = m + 1 := by
      rcases hd : stencilDist I V x with _ | m
      · rw [hd] at hreach; exact absurd hx hreach
      · exact ⟨m, rfl⟩
    rw [hm] at hreach
    obtain ⟨-, y, hy, hyr⟩ := hreach
    have h1 := (hdep x hx).2 (fun x => Cpast * stencilDist I V x + M) y hy
    have h2 : (stencilDist I V y : ℝ) ≤ m := by exact_mod_cast stencilDist_le hyr
    have h3 := mul_le_mul_of_nonneg_left h2 hCpast
    change _ ≤ Cpast * (stencilDist I V x : ℝ) + M
    rw [hm, Nat.cast_succ]
    linarith
  · change _ ≤ Cpast * (stencilDist I V x : ℝ) + M
    rw [hbd _ x hx, stencilDist_of_notMem hx, Nat.cast_zero, mul_zero, zero_add]
    exact hM x hx

theorem exists_superSolution_of_connected [Finite X] {Λ : (X → ℝ) → X → ℝ} {ubd : X → ℝ}
    (hbd : ∀ u, ∀ x ∉ I, Λ u x = ubd x) {Cpast : ℝ} (hCpast : 0 ≤ Cpast)
    (hdep : ∀ x ∈ I, HasDependency Cpast (V x) (Λ · x))
    (hconn : ∀ x ∈ I, ∃ z ∉ I, Relation.TransGen (fun a b => a ∈ I ∧ b ∈ V a) x z) :
    ∃ u : X → ℝ, Λ u ≤ u := by
  obtain ⟨M, hM⟩ := (Set.finite_range ubd).bddAbove
  exact ⟨_, superSolution_stencilDist hbd hCpast (fun x _ => hM ⟨x, rfl⟩) hdep hconn⟩

end GuaranteedSubsol.StencilDistProof
