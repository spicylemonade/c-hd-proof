import Frontier.CHD.L6.PassB

/-!
# L6 layout facts (agent-10, scratch): coverage and range bounds of the CSR arrays
-/

open scoped NNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM Finset

namespace L6In

variable {I : L6In}

/-- Every virtual vertex index below `off u` lies in a chunk of a kept vertex below `u`. -/
theorem cover (u : ℕ) : ∀ x < I.off u, ∃ v < u, I.keep v ≠ 0 ∧ I.off v ≤ x ∧ x < I.off v + I.cc v := by
  induction u with
  | zero => intro x hx; simp [off] at hx
  | succ u ih =>
    intro x hx
    rw [I.off_succ] at hx
    by_cases hxu : x < I.off u
    · obtain ⟨v, hv, h1, h2, h3⟩ := ih x hxu
      exact ⟨v, by omega, h1, h2, h3⟩
    · have hc : 0 < I.cc u := by omega
      have hk : I.keep u ≠ 0 := fun h => by rw [I.cc_zero h] at hc; omega
      exact ⟨u, by omega, hk, by omega, by omega⟩

/-- Chunk owners are unique. -/
theorem cover_unique {v v' x : ℕ} (h : I.off v ≤ x ∧ x < I.off v + I.cc v)
    (h' : I.off v' ≤ x ∧ x < I.off v' + I.cc v') : v = v' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := off_mono I (show v + 1 ≤ v' by omega)
    rw [I.off_succ] at this; omega
  · have := off_mono I (show v' + 1 ≤ v by omega)
    rw [I.off_succ] at this; omega

theorem off_eq_of_skip {u : ℕ} (hk : I.keep u = 0) : I.off (u + 1) = I.off u := by
  rw [I.off_succ, I.cc_zero hk]; rfl

theorem sl_eq_of_skip {u : ℕ} (hk : I.keep u = 0) : I.sl (u + 1) = I.sl u := by
  rw [I.sl_succ, I.ns_zero hk]; rfl

end L6In

/-- `gSt[off u] = sl u` for every `u ≤ n` (non-kept vertices contribute nothing). -/
theorem st_off {I : L6In} {r : State ℝ≥0} (hF : ∀ v < I.n, I.keep v ≠ 0 → VFacts I v r)
    (hN : r.wa "gSt" (I.off I.n) = I.sl I.n) : ∀ u ≤ I.n, r.wa "gSt" (I.off u) = I.sl u := by
  suffices h : ∀ k u, u + k = I.n → r.wa "gSt" (I.off u) = I.sl u by
    intro u hu; exact h (I.n - u) u (by omega)
  intro k
  induction k with
  | zero => intro u hu; simp at hu; subst hu; exact hN
  | succ k ih =>
    intro u hu
    by_cases hk : I.keep u = 0
    · rw [← L6In.off_eq_of_skip hk, ← L6In.sl_eq_of_skip hk]; exact ih (u + 1) (by omega)
    · have := (hF u (by omega) hk).st 0 (L6In.cc_pos hk)
      simpa using this

/-- The range of chunk `q` of kept `v` is `[gSt x, gSt (x+1))` with `x = off v + q`. -/
theorem st_range {I : L6In} {r : State ℝ≥0} (hF : ∀ v < I.n, I.keep v ≠ 0 → VFacts I v r)
    (hN : r.wa "gSt" (I.off I.n) = I.sl I.n) (hδ : 3 ≤ I.δ) {v q : ℕ} (hv : v < I.n)
    (hk : I.keep v ≠ 0) (hq : q < I.cc v) :
    r.wa "gSt" (I.off v + q) = I.sl v + q * I.δ ∧
    r.wa "gSt" (I.off v + q + 1) = I.sl v + q * I.δ + I.lenF v q := by
  refine ⟨(hF v hv hk).st q hq, ?_⟩
  by_cases hmid : q + 1 < I.cc v
  · have := (hF v hv hk).st (q + 1) hmid
    rw [show I.off v + q + 1 = I.off v + (q + 1) by ring, this, L6In.lenF_mid hmid]; ring
  · have hq' : q + 1 = I.cc v := by omega
    have h1 : I.off v + q + 1 = I.off (v + 1) := by rw [I.off_succ]; omega
    rw [h1, st_off hF hN (v + 1) (by omega), I.sl_succ]
    have hns : I.ns v = I.deg v + I.cc v - 1 := by simp [L6In.ns, hk]
    have hl := L6In.lenF_last hmid
    have hp := L6In.cc_pred_le hk hδ
    have hq2 : q = I.cc v - 1 := by omega
    rw [hl, hns, hq2]
    have h2 := mul_pred_add (I.cc v - 1) I.δ (by omega)
    omega

/-- Range facts for every virtual vertex `x < N`. -/
theorem st_range_any {I : L6In} {r : State ℝ≥0} (hF : ∀ v < I.n, I.keep v ≠ 0 → VFacts I v r)
    (hN : r.wa "gSt" (I.off I.n) = I.sl I.n) (hδ : 3 ≤ I.δ) {x : ℕ} (hx : x < I.off I.n) :
    ∃ v < I.n, I.keep v ≠ 0 ∧ ∃ q < I.cc v, x = I.off v + q ∧
      r.wa "gSt" x = I.sl v + q * I.δ ∧ r.wa "gSt" (x + 1) = I.sl v + q * I.δ + I.lenF v q := by
  obtain ⟨v, hv, hk, h1, h2⟩ := L6In.cover I.n x hx
  refine ⟨v, hv, hk, x - I.off v, by omega, by omega, ?_⟩
  have := st_range hF hN hδ hv hk (show x - I.off v < I.cc v by omega)
  rw [show I.off v + (x - I.off v) = x by omega] at this
  exact this

theorem st_le_succ {I : L6In} {r : State ℝ≥0} (hF : ∀ v < I.n, I.keep v ≠ 0 → VFacts I v r)
    (hN : r.wa "gSt" (I.off I.n) = I.sl I.n) (hδ : 3 ≤ I.δ) {x : ℕ} (hx : x < I.off I.n) :
    r.wa "gSt" x ≤ r.wa "gSt" (x + 1) := by
  obtain ⟨v, _, _, q, _, _, h1, h2⟩ := st_range_any hF hN hδ hx
  omega

theorem st_mono {I : L6In} {r : State ℝ≥0} (hF : ∀ v < I.n, I.keep v ≠ 0 → VFacts I v r)
    (hN : r.wa "gSt" (I.off I.n) = I.sl I.n) (hδ : 3 ≤ I.δ) {x y : ℕ} (hxy : x ≤ y)
    (hy : y ≤ I.off I.n) : r.wa "gSt" x ≤ r.wa "gSt" y := by
  induction hxy with
  | refl => exact le_rfl
  | @step y hxy ih => exact le_trans (ih (by omega)) (st_le_succ hF hN hδ (by omega))

theorem st_le_M {I : L6In} {r : State ℝ≥0} (hF : ∀ v < I.n, I.keep v ≠ 0 → VFacts I v r)
    (hN : r.wa "gSt" (I.off I.n) = I.sl I.n) (hδ : 3 ≤ I.δ) {x : ℕ} (hx : x ≤ I.off I.n) :
    r.wa "gSt" x ≤ I.sl I.n := by
  rw [← hN]; exact st_mono hF hN hδ hx le_rfl

end Frontier.CHD.L6
