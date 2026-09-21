import Frontier.CostSkeleton

/-!
# A computable size bound equivalent to `Tchd` (agent-10)

`Tnat cn cm = cn + cm (tF + lg(dd + 1) + 3)` is computable from the core's registers
(`cn`, `cm`, `cp.t`, `cp.dd`) and is within constant factors of `Tchd`:

* `Tchd_le_Tnat : Tchd n m ≤ 6 · Tnat n m` (used to size allocations that must dominate the run);
* `Tnat_le_Tchd : Tnat n m ≤ 33 · Tchd n m` (so allocating `O(Tnat)` cells costs `O(Tchd)`).

The main term uses `tF`'s defining inequality `lgN² ≤ tF³ dd²`: `(m^{1/3} (n log(n+2))^{2/3})³ =
m (n log(n+2))² ≤ 216 tF³ m³`.  NON-GATE (calculus).
-/

namespace Frontier.CostSkeleton

open Frontier.GateCCalc

/-- The computable size bound. -/
def Tnat (n m : ℕ) : ℕ := n + m * (tF n m + Nat.log 2 (dd n m + 1) + 3)

theorem log_n2_le_lgN (n : ℕ) (hn : 1 ≤ n) : Real.log ((n : ℝ) + 2) ≤ 3 * lgN n := by
  set k := Nat.log 2 n with hk
  have hlt : n < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h2 : 2 ≤ 2 ^ (k + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hle : n + 2 ≤ 2 ^ (k + 2) := by
    have : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
    omega
  have hleR : (n : ℝ) + 2 ≤ (2 : ℝ) ^ (k + 2) := by exact_mod_cast hle
  have hlog : Real.log ((n : ℝ) + 2) ≤ Real.log ((2 : ℝ) ^ (k + 2)) :=
    Real.log_le_log (by positivity) hleR
  rw [Real.log_pow] at hlog
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkR : ((k + 2 : ℕ) : ℝ) * Real.log 2 ≤ (k + 2 : ℕ) := by
    have : (0 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hkl : k ≤ lgN n := le_max_right _ _
  have h1l : 1 ≤ lgN n := one_le_lgN n
  have hk3 : k + 2 ≤ 3 * lgN n := by omega
  have hk3R : ((k + 2 : ℕ) : ℝ) ≤ 3 * (lgN n : ℝ) := by exact_mod_cast hk3
  linarith

theorem log_ratio_le (n m : ℕ) (hn : 1 ≤ n) :
    Real.log ((m : ℝ) / ((n : ℝ) + 1) + 2) ≤ Nat.log 2 (dd n m + 1) + 2 := by
  set k := Nat.log 2 (dd n m + 1) with hk
  have hlt : dd n m + 1 < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hle : dd n m + 2 ≤ 2 ^ (k + 2) := by
    have : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
    omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hdiv : (m : ℝ) / ((n : ℝ) + 1) ≤ dd n m := by
    have h1 : (m : ℝ) / ((n : ℝ) + 1) ≤ (m : ℝ) / n :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg m) hn0 (by linarith)
    have h2 : (m : ℝ) / n < ((m / n : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hn0]
      have := Nat.lt_div_mul_add (a := m) (b := n) (by omega)
      have h3 : ((m : ℕ) : ℝ) < (((m / n) * n + n : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h3
      linarith
    have : ((dd n m : ℕ) : ℝ) = ((m / n : ℕ) : ℝ) + 1 := by unfold dd; push_cast; ring
    linarith
  have hx : (m : ℝ) / ((n : ℝ) + 1) + 2 ≤ (2 : ℝ) ^ (k + 2) := by
    have : ((dd n m + 2 : ℕ) : ℝ) ≤ ((2 ^ (k + 2) : ℕ) : ℝ) := by exact_mod_cast hle
    push_cast at this
    linarith
  have hpos : 0 < (m : ℝ) / ((n : ℝ) + 1) + 2 := by positivity
  have hlog := Real.log_le_log hpos hx
  rw [Real.log_pow] at hlog
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkR : ((k + 2 : ℕ) : ℝ) * Real.log 2 ≤ (k + 2 : ℕ) := by
    have : (0 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  push_cast at hkR hlog
  linarith

theorem main_le_tm (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ m + 1) :
    (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3) ≤
      6 * tF n m * m := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hlog0 : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith)
  set Y : ℝ := (n : ℝ) * Real.log ((n : ℝ) + 2) with hYdef
  have hY0 : 0 ≤ Y := by positivity
  set Z : ℝ := (m : ℝ) ^ ((1 : ℝ) / 3) * Y ^ ((2 : ℝ) / 3) with hZdef
  have hZ0 : 0 ≤ Z := by positivity
  have hZ3 : Z ^ 3 = (m : ℝ) * Y ^ 2 := by
    rw [hZdef, mul_pow]
    have e1 : ((m : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (m : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hm0]; norm_num
    have e2 : (Y ^ ((2 : ℝ) / 3)) ^ 3 = Y ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hY0]
      norm_num
    rw [e1, e2]
  have hlogl := log_n2_le_lgN n hn
  have hY : Y ≤ 3 * n * lgN n := by
    rw [hYdef]
    have := mul_le_mul_of_nonneg_left hlogl (le_of_lt hn0)
    linarith
  have hspec : (lgN n : ℝ) ^ 2 ≤ (tF n m : ℝ) ^ 3 * (dd n m : ℝ) ^ 2 := by
    exact_mod_cast tF_spec n m
  have hndd : (n : ℝ) * dd n m ≤ 3 * m := by
    have hnat : n * dd n m ≤ m + n := by
      unfold dd
      have := Nat.div_mul_le_self m n
      nlinarith [Nat.mul_comm (m / n) n]
    have : ((n * dd n m : ℕ) : ℝ) ≤ (m : ℝ) + n := by exact_mod_cast hnat
    have hnm' : (n : ℝ) ≤ m + 1 := by exact_mod_cast hnm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    push_cast at this
    linarith
  have ht0 : (0 : ℝ) ≤ tF n m := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ dd n m := Nat.cast_nonneg _
  have hl0 : (0 : ℝ) ≤ lgN n := Nat.cast_nonneg _
  have hY2 : Y ^ 2 ≤ 81 * (tF n m : ℝ) ^ 3 * (m : ℝ) ^ 2 := by
    have h1 : Y ^ 2 ≤ (3 * n * lgN n) ^ 2 := pow_le_pow_left₀ hY0 hY 2
    have h2 : ((n : ℝ) * dd n m) ^ 2 ≤ (3 * m) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hndd 2
    have h3 : (3 * (n : ℝ) * lgN n) ^ 2 = 9 * (n : ℝ) ^ 2 * (lgN n : ℝ) ^ 2 := by ring
    have h4 : 9 * (n : ℝ) ^ 2 * (lgN n : ℝ) ^ 2 ≤ 9 * (n : ℝ) ^ 2 * ((tF n m : ℝ) ^ 3 * (dd n m : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hspec (by positivity)
    have h5 : 9 * (n : ℝ) ^ 2 * ((tF n m : ℝ) ^ 3 * (dd n m : ℝ) ^ 2) =
        9 * (tF n m : ℝ) ^ 3 * ((n : ℝ) * dd n m) ^ 2 := by ring
    have h6 : 9 * (tF n m : ℝ) ^ 3 * ((n : ℝ) * dd n m) ^ 2 ≤ 9 * (tF n m : ℝ) ^ 3 * (3 * m) ^ 2 :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith
  have hZ3le : Z ^ 3 ≤ (6 * tF n m * m) ^ 3 := by
    rw [hZ3]
    have : (m : ℝ) * Y ^ 2 ≤ (m : ℝ) * (81 * (tF n m : ℝ) ^ 3 * (m : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hY2 hm0
    have e : (6 * (tF n m : ℝ) * m) ^ 3 = 216 * (tF n m : ℝ) ^ 3 * (m : ℝ) ^ 3 := by ring
    rw [e]
    have : 0 ≤ (tF n m : ℝ) ^ 3 * (m : ℝ) ^ 3 := by positivity
    nlinarith
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hZ3le

/-- `Tchd ≤ 6 Tnat`. -/
theorem Tchd_le_Tnat (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ m + 1) :
    Tchd n m ≤ 6 * (Tnat n m : ℝ) := by
  have h1 := log_ratio_le n m hn
  have h2 := main_le_tm n m hn hm hnm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h3 : (m : ℝ) * Real.log ((m : ℝ) / ((n : ℝ) + 1) + 2) ≤
      m * ((Nat.log 2 (dd n m + 1) : ℝ) + 2) := mul_le_mul_of_nonneg_left h1 hm0
  unfold Tchd Tnat
  push_cast
  have ht0 : (0 : ℝ) ≤ tF n m := Nat.cast_nonneg _
  have hl0 : (0 : ℝ) ≤ Nat.log 2 (dd n m + 1) := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- `Tnat ≤ 33 Tchd`. -/
theorem Tnat_le_Tchd (n m : ℕ) (hn : 1 ≤ n) : (Tnat n m : ℝ) ≤ 33 * Tchd n m := by
  have h1 := n_le_Tchd n m
  have h2 := m_le_Tchd n m
  have h3 := term_mtF n m hn
  have h4 := term_mlogdd n m hn
  unfold Tnat
  push_cast
  nlinarith

end Frontier.CostSkeleton

#print axioms Frontier.CostSkeleton.Tchd_le_Tnat
#print axioms Frontier.CostSkeleton.Tnat_le_Tchd
