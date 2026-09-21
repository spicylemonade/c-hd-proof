import Frontier.GateCCalc
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `Tchd (min n (m+1)) m ≤ 2 · Tchd n m` (agent-10; checklist item I11)

The C-HD core computes its parameters from `(cn, cm) = (min(n, m+1), m)`; this lemma turns the core's
`O(Tchd cn m)` bound into the dispatcher's `O(Tchd n m)`.
-/

open Real

namespace Frontier.GateCCalc

theorem log_three_le_two : Real.log 3 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have := Real.add_one_le_exp (2 : ℝ)
  linarith

theorem Tchd_cn_le (n m : ℕ) : Tchd (min n (m + 1)) m ≤ 2 * Tchd n m := by
  have hT0 : 0 ≤ Tchd n m := Tchd_nonneg n m
  by_cases h : n ≤ m + 1
  · rw [min_eq_left h]; linarith
  · push_neg at h
    rw [min_eq_right h.le]
    unfold Tchd
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hn : (m : ℝ) + 2 ≤ n := by exact_mod_cast h
    -- the log term with cn = m + 1 is at most m log 3 ≤ 2 m
    have hq : (m : ℝ) / (((m + 1 : ℕ) : ℝ) + 1) + 2 ≤ 3 := by
      push_cast
      have : (m : ℝ) / ((m : ℝ) + 1 + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      linarith
    have hq0 : 0 < (m : ℝ) / (((m + 1 : ℕ) : ℝ) + 1) + 2 := by positivity
    have hlog1 : Real.log ((m : ℝ) / (((m + 1 : ℕ) : ℝ) + 1) + 2) ≤ 2 :=
      le_trans (Real.log_le_log hq0 hq) log_three_le_two
    have hlog2 : 0 ≤ Real.log ((m : ℝ) / ((n : ℝ) + 1) + 2) := by
      apply Real.log_nonneg
      have : 0 ≤ (m : ℝ) / ((n : ℝ) + 1) := by positivity
      linarith
    -- the root term is monotone in the vertex count
    have hA : ((m + 1 : ℕ) : ℝ) * Real.log (((m + 1 : ℕ) : ℝ) + 2) ≤ (n : ℝ) * Real.log ((n : ℝ) + 2) := by
      push_cast
      have h1 : 0 ≤ Real.log ((m : ℝ) + 1 + 2) := Real.log_nonneg (by linarith)
      have h2 : Real.log ((m : ℝ) + 1 + 2) ≤ Real.log ((n : ℝ) + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      have h3 : (m : ℝ) + 1 ≤ n := by linarith
      calc ((m : ℝ) + 1) * Real.log ((m : ℝ) + 1 + 2) ≤ (n : ℝ) * Real.log ((m : ℝ) + 1 + 2) :=
            mul_le_mul_of_nonneg_right h3 h1
        _ ≤ (n : ℝ) * Real.log ((n : ℝ) + 2) := mul_le_mul_of_nonneg_left h2 (by linarith)
    have hA0 : 0 ≤ ((m + 1 : ℕ) : ℝ) * Real.log (((m + 1 : ℕ) : ℝ) + 2) := by
      apply mul_nonneg (by positivity); apply Real.log_nonneg; push_cast; linarith
    have hB : (((m + 1 : ℕ) : ℝ) * Real.log (((m + 1 : ℕ) : ℝ) + 2)) ^ ((2 : ℝ) / 3) ≤
        ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3) :=
      Real.rpow_le_rpow hA0 hA (by norm_num)
    have hC : (m : ℝ) ^ ((1 : ℝ) / 3) * (((m + 1 : ℕ) : ℝ) * Real.log (((m + 1 : ℕ) : ℝ) + 2)) ^ ((2 : ℝ) / 3) ≤
        (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3) :=
      mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hm0 _)
    have hD : 0 ≤ (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3) := by
      apply mul_nonneg (Real.rpow_nonneg hm0 _)
      apply Real.rpow_nonneg
      apply mul_nonneg (Nat.cast_nonneg n); apply Real.log_nonneg; have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hE : (m : ℝ) * Real.log ((m : ℝ) / (((m + 1 : ℕ) : ℝ) + 1) + 2) ≤ 2 * m := by nlinarith
    have hF : 0 ≤ (m : ℝ) * Real.log ((m : ℝ) / ((n : ℝ) + 1) + 2) := mul_nonneg hm0 hlog2
    push_cast at hE hC ⊢
    nlinarith

/-- The L6 sort cost against `Tchd`: `(n + m)(⌊log₂ δ⌋ + 1) ≤ 8 · Tchd n m` for
`δ ≤ 4 (m/(n+1) + 2)` (true for `δ = max 3 ⌈2m/n⌉`, `n ≥ 1`). -/
theorem nm_log_le (n m δ : ℕ) (hn : 1 ≤ n) (hδ1 : 1 ≤ δ)
    (hδ : (δ : ℝ) ≤ 4 * ((m : ℝ) / ((n : ℝ) + 1) + 2)) :
    ((n + m : ℕ) : ℝ) * ((Nat.log 2 δ : ℝ) + 1) ≤ 8 * Tchd n m := by
  set L := Real.log ((m : ℝ) / ((n : ℝ) + 1) + 2) with hL
  have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hq0 : 0 < (m : ℝ) / ((n : ℝ) + 1) + 2 := by positivity
  have hL0 : 0 ≤ L := by
    apply Real.log_nonneg
    have : 0 ≤ (m : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith
  have hlog2 : 0.69 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  -- ⌊log₂ δ⌋ · log 2 ≤ log δ ≤ 2 log 2 + L
  have h1 : (Nat.log 2 δ : ℝ) * Real.log 2 ≤ Real.log δ := by
    have hp : 2 ^ (Nat.log 2 δ) ≤ δ := Nat.pow_log_le_self 2 (by omega)
    have hp' : ((2 : ℝ) ^ (Nat.log 2 δ)) ≤ (δ : ℝ) := by exact_mod_cast hp
    have := Real.log_le_log (by positivity) hp'
    rwa [Real.log_pow] at this
  have h2 : Real.log δ ≤ 2 * Real.log 2 + L := by
    have hδ0 : (0 : ℝ) < δ := by exact_mod_cast hδ1
    have := Real.log_le_log hδ0 hδ
    rw [Real.log_mul (by norm_num) hq0.ne'] at this
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  have hlogδ : (Nat.log 2 δ : ℝ) ≤ 2 + L / Real.log 2 := by
    have : (Nat.log 2 δ : ℝ) * Real.log 2 ≤ 2 * Real.log 2 + L := le_trans h1 h2
    have hpos : 0 < Real.log 2 := by linarith
    calc (Nat.log 2 δ : ℝ) = (Nat.log 2 δ : ℝ) * Real.log 2 / Real.log 2 := by field_simp
      _ ≤ (2 * Real.log 2 + L) / Real.log 2 := div_le_div_of_nonneg_right this hpos.le
      _ = 2 + L / Real.log 2 := by field_simp
  -- n L ≤ max (m L) (1.1 n)
  have hnL : (n : ℝ) * L ≤ (m : ℝ) * L + 1.2 * n := by
    by_cases hmn : (n : ℝ) ≤ m
    · nlinarith
    · push_neg at hmn
      have hq : (m : ℝ) / ((n : ℝ) + 1) + 2 ≤ 3 := by
        have : (m : ℝ) / ((n : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
        linarith
      have hL3 : L ≤ 1.2 := by
        have := Real.log_le_log hq0 hq
        have he := Real.exp_one_gt_d9
        have hne : 3 / Real.exp 1 ≠ 1 := by
          intro h; rw [div_eq_one_iff_eq (Real.exp_pos 1).ne'] at h
          have := Real.exp_one_lt_d9; linarith
        have h3 : Real.log 3 < 1.2 := by
          have h4 := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 3 / Real.exp 1 by positivity) hne
          rw [Real.log_div (by norm_num) (Real.exp_pos 1).ne', Real.log_exp] at h4
          have h5 : 3 / Real.exp 1 < 1.2 := by
            rw [div_lt_iff₀ (Real.exp_pos 1)]; nlinarith
          linarith
        linarith
      nlinarith
  have hT : (n : ℝ) + m + m * L ≤ Tchd n m := by
    unfold Tchd
    have : 0 ≤ (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3) := by
      apply mul_nonneg (Real.rpow_nonneg hm0 _)
      apply Real.rpow_nonneg
      apply mul_nonneg (by linarith); apply Real.log_nonneg; linarith
    rw [← hL]; linarith
  have hpos : 0 < Real.log 2 := by linarith
  have hk : L / Real.log 2 ≤ L / 0.69 := div_le_div_of_nonneg_left hL0 (by norm_num) hlog2.le
  have hmain : ((n + m : ℕ) : ℝ) * ((Nat.log 2 δ : ℝ) + 1) ≤ ((n : ℝ) + m) * (3 + L / 0.69) := by
    push_cast
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    linarith
  have hexp : ((n : ℝ) + m) * (3 + L / 0.69) = 3 * ((n : ℝ) + m) + ((n : ℝ) * L + (m : ℝ) * L) / 0.69 := by
    ring
  rw [hexp] at hmain
  have : ((n : ℝ) * L + (m : ℝ) * L) / 0.69 ≤ (2 * ((m : ℝ) * L) + 1.2 * n) / 0.69 := by
    apply div_le_div_of_nonneg_right _ (by norm_num); linarith
  have hmL : 0 ≤ (m : ℝ) * L := mul_nonneg hm0 hL0
  have hfin : (2 * ((m : ℝ) * L) + 1.2 * n) / 0.69 ≤ 3 * Tchd n m + 1.75 * n := by
    rw [div_le_iff₀ (by norm_num)]; nlinarith
  nlinarith

end Frontier.GateCCalc
