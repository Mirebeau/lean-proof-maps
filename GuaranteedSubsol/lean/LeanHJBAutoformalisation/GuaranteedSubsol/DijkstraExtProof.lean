/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.DijkstraProof
public import LeanHJBAutoformalisation.GuaranteedSubsol.AxiomsExtTransfer

/-!
# Generalized Dijkstra for the extension of a real causal scheme: proof

Provider proof for the frozen anchor `GuaranteedSubsol.dijkstraRun_ext_of_causal`, see
`ANCHORS.md`. The extension `Γ_∞ = Global.monotoneExtension Γ` is monotone
(`monotone_monotoneExtension`), and causal at each point when `Γ` is monotone and causal there
(`Causal.ext`); the results for an operator on `ℝ_∞` (`DijkstraProof`) then apply.
-/

@[expose] public section

namespace GuaranteedSubsol.DijkstraExtProof

theorem dijkstraRun_ext_of_causal {X : Type*} [LinearOrder X] [Finite X]
    {Γ : (X → ℝ) → X → ℝ} (hmono : ∀ x, Monotone (Γ · x)) (hcaus : ∀ x, Causal (Γ · x))
    {u₀ : X → WithTop ℝ} (hu₀ : Global.monotoneExtension Γ u₀ ≤ u₀) :
    (∀ n x, (dijkstraRun (Global.monotoneExtension Γ) u₀ n).count x ≤ 1 ∧
      ((dijkstraRun (Global.monotoneExtension Γ) u₀ n).count x = 1 ↔
        (dijkstraRun (Global.monotoneExtension Γ) u₀ n).u x < u₀ x)) ∧
    ∃ N ≤ Nat.card X, Global.monotoneExtension Γ (dijkstraRun (Global.monotoneExtension Γ) u₀ N).u =
      (dijkstraRun (Global.monotoneExtension Γ) u₀ N).u := by
  have hmono' : Monotone (Global.monotoneExtension Γ) := fun _ _ h x =>
    KruzkovProof.monotone_monotoneExtension _ h
  have hcaus' : ∀ x, Ext.Causal (Global.monotoneExtension Γ · x) := fun x =>
    (hcaus x).ext (hmono x)
  exact ⟨fun n x => ⟨DijkstraProof.count_le_one hcaus' u₀ n x,
    DijkstraProof.count_eq_one_iff hcaus' u₀ n x⟩, DijkstraProof.fixedPoint hmono' hcaus' hu₀⟩

end GuaranteedSubsol.DijkstraExtProof
