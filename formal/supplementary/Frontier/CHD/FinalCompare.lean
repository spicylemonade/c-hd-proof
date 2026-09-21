import Frontier.CHD.Final

/-!
# Frontier.CHD.FinalCompare — the C-HD witness against the known directed bounds (agent-01)

**NON-GATE** (a corollary of the frozen `Frontier.CHD.Final`; this file is outside its import
closure).  Gate C's formal statement compares the witness with `n log n`.  Here the comparison is
made explicit against the three best known deterministic directed comparison–addition bounds, taken
as bound expressions with constant `1`:
* Dijkstra (Fibonacci heaps): `m + n L`;
* DMM+25 (2504.17033): `m L^{2/3}`;
* DMSY26 (2602.07868): `m √L + √(m n L log L)`;
where `L = log (n + 2)`.  `chd_beats_known`: the witness `Final.chdProgram` has a cost bound `T`,
valid on every graph and source, with `T n (μ n) / b n (μ n) → 0` for each of the three
expressions `b`, along the Gate-C profile `μ n = n ⌊L^{3/4}⌋`.  (That no other algorithm with a
better bound is known is the novelty review, not a formal statement.)
-/

open Real Filter Topology

namespace Frontier.CHD.FinalCompare

open Frontier Frontier.RAM Frontier.GateCCalc Frontier.GateCTarget

/-- Dijkstra's bound expression `m + n L`. -/
noncomputable def bDijkstra (n m : ℕ) : ℝ := (m : ℝ) + (n : ℝ) * L n
/-- DMM+25's bound expression `m L^{2/3}`. -/
noncomputable def bDMM (n m : ℕ) : ℝ := (m : ℝ) * L n ^ ((2 : ℝ) / 3)
/-- DMSY26's bound expression `m √L + √(m n L log L)`. -/
noncomputable def bDMSY (n m : ℕ) : ℝ :=
  (m : ℝ) * Real.sqrt (L n) + Real.sqrt ((m : ℝ) * (n : ℝ) * L n * Real.log (L n))

lemma sqrt_le_rpow23 {x : ℝ} (hx : 1 ≤ x) : Real.sqrt x ≤ x ^ ((2 : ℝ) / 3) := by
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)

/-- Eventually each of the three bound expressions along `μ` is at least `n · L n`. -/
lemma nL_le_known : ∀ᶠ n : ℕ in atTop,
    (n : ℝ) * L n ≤ bDijkstra n (μ n) ∧ (n : ℝ) * L n ≤ bDMM n (μ n) ∧
      (n : ℝ) * L n ≤ bDMSY n (μ n) := by
  filter_upwards [mu_window, eventually_ge_atTop 1] with n hw hn
  have hL1 : 1 ≤ L n := L_ge_one hn
  have hL0 : 0 ≤ L n := le_trans zero_le_one hL1
  have hsq : Real.sqrt (L n) * Real.sqrt (L n) = L n := Real.mul_self_sqrt hL0
  have hw1 : (n : ℝ) * Real.sqrt (L n) ≤ (μ n : ℝ) := hw.1
  have hsq0 : 0 ≤ Real.sqrt (L n) := Real.sqrt_nonneg _
  have hmuSq : (n : ℝ) * L n ≤ (μ n : ℝ) * Real.sqrt (L n) := by
    calc (n : ℝ) * L n = ((n : ℝ) * Real.sqrt (L n)) * Real.sqrt (L n) := by rw [mul_assoc, hsq]
      _ ≤ (μ n : ℝ) * Real.sqrt (L n) := mul_le_mul_of_nonneg_right hw1 hsq0
  have hmu0 : (0 : ℝ) ≤ (μ n : ℝ) := Nat.cast_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · unfold bDijkstra; linarith
  · unfold bDMM
    exact le_trans hmuSq (mul_le_mul_of_nonneg_left (sqrt_le_rpow23 hL1) hmu0)
  · unfold bDMSY
    have := Real.sqrt_nonneg ((μ n : ℝ) * (n : ℝ) * L n * Real.log (L n))
    linarith

/-- For every constant `C`, `C · Tdisp F n (μ n)` is `o` of each of the three bound expressions
along `m = μ n`. -/
theorem tdisp_mu_little_o_known (C : ℝ) :
    Tendsto (fun n : ℕ => C * Tdisp F n (μ n) / bDijkstra n (μ n)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => C * Tdisp F n (μ n) / bDMM n (μ n)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => C * Tdisp F n (μ n) / bDMSY n (μ n)) atTop (𝓝 0) := by
  have hq : Tendsto (fun n : ℕ => Tchd n (μ n) / ((n : ℝ) * L n)) atTop (𝓝 0) := tendsto_Tchd_mu
  have hT : ∀ᶠ n : ℕ in atTop, Tdisp F n (μ n) = Tchd n (μ n) := by
    filter_upwards [F_dominates] with n hn
    have hle : μ n ≤ n * F n := by unfold μ; exact Nat.mul_le_mul_left n hn
    simp [Tdisp, hle]
  have key : ∀ b : ℕ → ℝ, (∀ᶠ n : ℕ in atTop, (n : ℝ) * L n ≤ b n) →
      Tendsto (fun n : ℕ => C * Tdisp F n (μ n) / b n) atTop (𝓝 0) := by
    intro b hb
    have h0 : Tendsto (fun n : ℕ => Tchd n (μ n) / b n) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hq ?_ ?_
      · filter_upwards [hb, eventually_ge_atTop 1] with n hbn hn
        have hpos : 0 < (n : ℝ) * L n := mul_pos (by exact_mod_cast hn) (L_pos n)
        exact div_nonneg (Tchd_nonneg _ _) (le_trans hpos.le hbn)
      · filter_upwards [hb, eventually_ge_atTop 1] with n hbn hn
        have hpos : 0 < (n : ℝ) * L n := mul_pos (by exact_mod_cast hn) (L_pos n)
        exact div_le_div_of_nonneg_left (Tchd_nonneg _ _) hpos hbn
    have h1 := h0.const_mul C
    rw [mul_zero] at h1
    refine h1.congr' ?_
    filter_upwards [hT] with n hn
    rw [hn, mul_div_assoc]
  refine ⟨key _ ?_, key _ ?_, key _ ?_⟩
  · filter_upwards [nL_le_known] with n h; exact h.1
  · filter_upwards [nL_le_known] with n h; exact h.2.1
  · filter_upwards [nL_le_known] with n h; exact h.2.2

/-- **The C-HD witness beats the three known bound expressions along the Gate-C profile**: its cost
bound `T` holds on every graph and source, and `T n (μ n)` is `o` of Dijkstra's `m + n L`, of
DMM+25's `m L^{2/3}` and of DMSY26's `m √L + √(m n L log L)` at `m = μ n`. -/
theorem chd_beats_known : ∃ T : ℕ → ℕ → ℝ,
    (∀ (G : Graph) (s : Fin G.n), Final.chdProgram.RunsWithin G s (T G.n G.m)) ∧
    Tendsto (fun n : ℕ => T n (μ n) / bDijkstra n (μ n)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => T n (μ n) / bDMM n (μ n)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => T n (μ n) / bDMSY n (μ n)) atTop (𝓝 0) :=
  ⟨fun n m => (L6.bodyC Final.KcC + 65536 * 9 + 100) * Tdisp F n m, Final.chd_exact_within.2,
    tdisp_mu_little_o_known _⟩

end Frontier.CHD.FinalCompare

#print axioms Frontier.CHD.FinalCompare.tdisp_mu_little_o_known
#print axioms Frontier.CHD.FinalCompare.chd_beats_known
