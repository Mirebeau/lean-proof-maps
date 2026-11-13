/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
module

public import LeanHJBAutoformalisation.GuaranteedSubsol.AnbProof

/-!
# ANB: Lemma lem:first_iter, proofs

Provider proof for the frozen anchor `GuaranteedSubsol.anbRun_first_iter`, see `ANCHORS.md`.

For `t ≤ min u_bd` one has `t ≤ Γ[t]` (`le_apply_const`, second part of Prop. prop:cst_subsol). An
iteration started from a state with `u̲ = ∞`, a constant `ū ≤ nτ`, the guess `nτ` for Dijkstra's
method and no update so far (`FirstInv`) makes no update: the guess `nτ` is already the fixed point
of `Γ' = max (ū, min (nτ, Γ))`, so Dijkstra's method stays put and `û_n = nτ`; then
`t_n = nτ`, `Δ_n = 0`, `B_n = ∅`, and the next state again satisfies `FirstInv`, with `ū = nτ` and
the guess `(n + 1)τ` (`step_first`). The initial state satisfies `FirstInv`.
-/

@[expose] public section

namespace GuaranteedSubsol.AnbFirstIterProof

open AnbProof

variable {X : Type*}

theorem dijkstraRun_of_fixed [LinearOrder X] {G : (X → WithTop ℝ) → X → WithTop ℝ}
    {u₀ : X → WithTop ℝ} (h : ∀ x, ¬G u₀ x < u₀ x) (n : ℕ) :
    dijkstraRun G u₀ n = dijkstraInit u₀ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [dijkstraRun, Function.iterate_succ_apply', ← dijkstraRun, ih]
    exact DijkstraProof.step_of_not_select _ fun ⟨x, hx⟩ => h x hx.1

/-- `T ≤ Γ[T]` for `T ≤ min u_bd` (Prop. prop:cst_subsol, second part): on `Int X`,
`Γ[T] = Γ[0] + T` with `Γ[0] ≥ Λ[0] / C_Γ ≥ 0` by comparability; outside, `Γ[T] = u_bd`. -/
theorem le_apply_const {Λ Γ : (X → ℝ) → X → ℝ} {I : Set X} {ubd : X → ℝ}
    (hΓbd : ∀ u, ∀ x ∉ I, Γ u x = ubd x) {CΓ CΓ' : ℝ} (hCΓ : 1 ≤ CΓ) (hΛ0 : 0 ≤ Λ 0)
    (hΓadd : ∀ x ∈ I, AdditivelyInvariant (Γ · x))
    (hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (Λ · x) (Γ · x)) {T : ℝ} (hT : ∀ x ∉ I, T ≤ ubd x)
    (x : X) : T ≤ Γ (fun _ => T) x := by
  by_cases hx : x ∈ I
  · have h1 := (hcmp x hx 0).2
    change Λ (fun y => CΓ * (0 : X → ℝ) y) x ≤ CΓ * Γ 0 x at h1
    have h0 : (fun y => CΓ * (0 : X → ℝ) y) = 0 := funext fun y => by simp
    rw [h0] at h1
    have hΓ0 : 0 ≤ Γ 0 x := by
      by_contra hneg
      have : CΓ * Γ 0 x < 0 := mul_neg_of_pos_of_neg (by linarith) (not_le.1 hneg)
      have h0x : (0 : X → ℝ) x ≤ Λ 0 x := hΛ0 x
      rw [Pi.zero_apply] at h0x
      linarith
    have h2 := hΓadd x hx 0 T
    change Γ (fun y => (0 : X → ℝ) y + T) x = Γ 0 x + T at h2
    have h3 : (fun y => (0 : X → ℝ) y + T) = fun _ => T := funext fun y => by simp
    rw [h3] at h2
    rw [h2]
    linarith
  · rw [hΓbd _ x hx]
    exact hT x hx

variable [Fintype X] [LinearOrder X] {S : AnbInnerSolver X}

/-- A state of the first phase of the ANB: `u̲ = ∞`, the guess for `û` is `nτ`, `ū` is a constant
`≤ nτ`, and no update has been made. -/
def FirstInv (p : AnbParams X) (s : AnbState X) : Prop :=
  s.uSup = (fun _ => ⊤) ∧ s.uHatInit = (fun _ => ((s.n * p.τ : ℝ) : WithTop ℝ)) ∧
    (∃ c, c ≤ s.n * p.τ ∧ s.uSub = fun _ => c) ∧ s.countSub = 0 ∧ s.countSup = 0 ∧
    s.countHat = 0

theorem firstInv_init (p : AnbParams X) : FirstInv p (anbRunWith S p 0) := by
  refine ⟨rfl, funext fun x => ?_, ⟨0, ?_, rfl⟩, rfl, rfl, rfl⟩
  · simp [anbRunWith, anbInit]
  · simp [anbRunWith, anbInit]

/-- One iteration of the first phase. -/
theorem step_first {p : AnbParams X} {I : Set X} {ubd : X → ℝ}
    (hΓbd : ∀ u, ∀ x ∉ I, p.Γ u x = ubd x) {CΓ CΓ' : ℝ} (hCΓ : 1 ≤ CΓ) (hΛ0 : 0 ≤ p.Λ 0)
    (hΓadd : ∀ x ∈ I, AdditivelyInvariant (p.Γ · x))
    (hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (p.Λ · x) (p.Γ · x))
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hα : 0 < p.α) (hτ : 0 ≤ p.τ) {s : AnbState X}
    (hs : FirstInv p s) (hT : ∀ x ∉ I, s.n * p.τ ≤ ubd x) :
    (anbStepData p s).uHat = (fun _ => s.n * p.τ) ∧ (anbStepData p s).hatRun.count = 0 ∧
    (anbStepData p s).t = s.n * p.τ ∧ (anbStepData p s).Δ = 0 ∧
    (anbStepData p s).band = ∅ ∧ (anbStepWith S p s).uSub = (fun _ => s.n * p.τ) ∧
    FirstInv p (anbStepWith S p s) := by
  classical
  obtain ⟨hsup, hinit, ⟨c, hc, hsub⟩, h1, h2, h3⟩ := hs
  set T : ℝ := s.n * p.τ with hTdef
  have hΓT := le_apply_const hΓbd hCΓ hΛ0 hΓadd hcmp hT
  -- the guess `nτ` is a fixed point of `Γ'`: Dijkstra's method makes no update
  have hfix : ∀ x, ¬anbHatOp p.Γ s.uSub T s.uHatInit x < s.uHatInit x := fun x => by
    have hcoe := MonotoneExtension.coe_eq (hΓmono x) (fun _ : X => T)
    have hop : anbHatOp p.Γ (fun _ => c) T (fun _ => (T : WithTop ℝ)) x = (T : WithTop ℝ) := by
      change max _ (min _ (monotoneExtension (p.Γ · x) (fun _ => (T : WithTop ℝ)))) = _
      rw [hcoe, ← WithTop.coe_min, ← WithTop.coe_max, min_eq_left (hΓT x), max_eq_right hc]
    rw [hinit, hsub, hop]
    exact lt_irrefl _
  have hD : (anbStepData p s).hatRun = dijkstraInit s.uHatInit := by
    rw [anbStepData_hatRun]
    exact dijkstraRun_of_fixed hfix _
  have hHat : (anbStepData p s).uHat = fun _ => T := funext fun x => by
    rw [anbStepData_uHat, hD]
    change (s.uHatInit x).untopD 0 = T
    rw [hinit]
    rfl
  have hcount : (anbStepData p s).hatRun.count = 0 := by rw [hD]; rfl
  -- `t_n = nτ`, `Δ_n = 0`, `B_n = ∅`
  have ht : (anbStepData p s).t = T := by
    rw [anbStepData_t, hHat]
    unfold anbLevel
    dsimp only
    split_ifs with h
    · rw [Finset.inf'_const]; exact min_self T
    · rfl
  have hΔ : (anbStepData p s).Δ = 0 := by rw [anbStepData_Δ, ht]; ring
  have hB : (anbStepData p s).band = ∅ := by
    rw [anbStepData_band, hΔ, hHat]
    ext x
    simp [anbBand]
  have hoff : ∀ x, x ∉ (anbStepData p s).band := fun x => by rw [hB]; exact Set.notMem_empty x
  have hsub' : (anbStepWith S p s).uSub = fun _ => T := funext fun x => by
    rw [(eq_of_notMem_band hα (hoff x)).1, hHat]
  have hsup' : (anbStepWith S p s).uSup = fun _ => ⊤ := funext fun x => by
    rw [(eq_of_notMem_band hα (hoff x)).2, hsup]
  have hTT' : T ≤ ((anbStepWith S p s).n : ℝ) * p.τ := by
    change T ≤ ((s.n + 1 : ℕ) : ℝ) * p.τ
    have h : ((s.n + 1 : ℕ) : ℝ) * p.τ = T + p.τ := by rw [hTdef]; push_cast; ring
    rw [h]
    linarith
  refine ⟨hHat, hcount, ht, hΔ, hB, hsub', hsup', funext fun x => ?_, ⟨T, hTT', hsub'⟩,
    funext fun x => ?_, funext fun x => ?_, funext fun x => ?_⟩
  · -- the next guess is `(n + 1)τ`
    change anbDijkstraGuess (((s.n + 1 : ℕ) : ℝ) * p.τ) (anbStepData p s).tMinus
      (anbStepData p s).uHat (anbStepWith S p s).uSub x =
        (((anbStepWith S p s).n * p.τ : ℝ) : WithTop ℝ)
    rw [AnbStepData.tMinus_def, ht, hΔ, hHat, hsub']
    simp only [anbDijkstraGuess, sub_zero, lt_self_iff_false, ↓reduceIte]
    exact congrArg _ (max_eq_right hTT')
  · change s.countSub x + (if x ∈ (anbStepData p s).band then _ else 0) = 0
    simp only [hoff x, ↓reduceIte, h1, Pi.zero_apply, add_zero]
  · change s.countSup x + (if x ∈ (anbStepData p s).band then _ else 0) = 0
    simp only [hoff x, ↓reduceIte, h2, Pi.zero_apply, add_zero]
  · change s.countHat x + (anbStepData p s).hatRun.count x = 0
    rw [hcount, h3]
    rfl

theorem first_iter {p : AnbParams X} {I : Set X} {ubd : X → ℝ}
    (hΓbd : ∀ u, ∀ x ∉ I, p.Γ u x = ubd x) {CΓ CΓ' : ℝ} (hCΓ : 1 ≤ CΓ) (hΛ0 : 0 ≤ p.Λ 0)
    (hΓadd : ∀ x ∈ I, AdditivelyInvariant (p.Γ · x))
    (hcmp : ∀ x ∈ I, Comparable CΓ CΓ' (p.Λ · x) (p.Γ · x))
    (hΓmono : ∀ x, Monotone (p.Γ · x)) (hα : 0 < p.α) (hτ : 0 ≤ p.τ) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : ∀ x ∉ I, (k : ℝ) * p.τ ≤ ubd x) :
    (anbRunWith S p k).uSub = (fun _ => ((k : ℝ) - 1) * p.τ) ∧
    (anbRunWith S p k).uSup = (fun _ => ⊤) ∧
    (anbRunDataWith S p k).uHat = (fun _ => (k : ℝ) * p.τ) ∧ (anbRunDataWith S p k).t = k * p.τ ∧
    (anbRunDataWith S p k).Δ = 0 ∧ (anbRunDataWith S p k).band = ∅ ∧
    (anbRunWith S p (k + 1)).countSub = 0 ∧ (anbRunWith S p (k + 1)).countSup = 0 ∧
    (anbRunWith S p (k + 1)).countHat = 0 := by
  have hT : ∀ j ≤ k, ∀ x ∉ I, ((anbRunWith S p j).n : ℝ) * p.τ ≤ ubd x := fun j hj x hx => by
    rw [anbRun_n]
    exact (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hj) hτ).trans (hk x hx)
  have step := fun {j : ℕ} (hj : j ≤ k) (hinv : FirstInv p (anbRunWith S p j)) =>
    step_first (S := S) hΓbd hCΓ hΛ0 hΓadd hcmp hΓmono hα hτ hinv (hT j hj)
  have hinv : ∀ j ≤ k + 1, FirstInv p (anbRunWith S p j) := by
    intro j
    induction j with
    | zero => exact fun _ => firstInv_init (S := S) p
    | succ j ih =>
      intro hj
      rw [anbRun_succ]
      exact (step (by omega) (ih (by omega))).2.2.2.2.2.2
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hm := step (by omega) (hinv m (by omega))
  have hk' := step le_rfl (hinv (m + 1) (by omega))
  have hnext := hinv (m + 1 + 1) le_rfl
  rw [anbRun_n] at hm hk'
  refine ⟨?_, (hinv (m + 1) (by omega)).1, ?_, hk'.2.2.1, hk'.2.2.2.1, hk'.2.2.2.2.1,
    hnext.2.2.2.1, hnext.2.2.2.2.1, hnext.2.2.2.2.2⟩
  · rw [anbRun_succ, hm.2.2.2.2.2.1]
    funext x
    push_cast
    ring
  · exact hk'.1

end GuaranteedSubsol.AnbFirstIterProof
