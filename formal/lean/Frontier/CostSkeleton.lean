import Frontier.GateCCalc

/-!
# Frontier.CostSkeleton — C-HD cost composition skeleton, part 1: parameter calculus (owner: agent-06)

**NON-GATE.**  Pure `ℕ`/`ℝ` arithmetic.  Nothing here is about any algorithm; it proves that, for the
integer-computable C-HD parameters defined below, every cost TERM that appears in the (DMSY26 Lemma 3.9 at
degree `δ = Θ(m/n)`) accounting of the C-HD candidate is `O(Tchd n m)`, where `Tchd` is agent-10's target
shape (`Frontier.GateCCalc.Tchd`).  Because the final cost lemma of the paper will be a finite nonnegative
combination of these terms, it composes with this file by linearity.

Parameters (all computable with `O(log n)` word operations):
* `lgN n = max 1 (Nat.log 2 n)`  (safe logarithm),
* `dd n m = m / n + 1`            (density, floor division, `≥ 1`),
* `tpar n m` = the least `t ≥ 1` with `lgN² ≤ t³ · dd²`, i.e. `t = ⌈(lgN/dd)^{2/3}⌉`,
* `kpar n m = Nat.sqrt t + 1`    (so `k > √t ≥ k - 1`),
* `Lpar n m = lgN / t + 1`       (number of recursion levels, `≥ ⌈lgN / t⌉`).

Hypothesis used throughout: `1 ≤ n` and `n ≤ m + 1` (every vertex reachable, as in DMSY26 §2; the algorithm
must be run with parameters computed from the INPUT `(n, m)`, and the reachable part after degree reduction
has `O(n)` vertices, so this is the only form in which the calculus is applied).
-/

open Real

namespace Frontier.CostSkeleton

open Frontier.GateCCalc

/-! ## Parameters -/

/-- Safe base-2 logarithm. -/
def lgN (n : ℕ) : ℕ := max 1 (Nat.log 2 n)

/-- Density `⌊m/n⌋ + 1 ≥ 1`. -/
def dd (n m : ℕ) : ℕ := m / n + 1

theorem one_le_lgN (n : ℕ) : 1 ≤ lgN n := le_max_left _ _

theorem one_le_dd (n m : ℕ) : 1 ≤ dd n m := Nat.le_add_left 1 _

theorem tpar_exists (n m : ℕ) : ∃ t, 1 ≤ t ∧ lgN n ^ 2 ≤ t ^ 3 * dd n m ^ 2 := by
  refine ⟨lgN n, one_le_lgN n, ?_⟩
  have h1 : 1 ≤ lgN n := one_le_lgN n
  have h2 : 1 ≤ dd n m := one_le_dd n m
  calc lgN n ^ 2 = lgN n ^ 2 * 1 * 1 := by ring
    _ ≤ lgN n ^ 2 * lgN n * dd n m ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul le_rfl h1) (Nat.one_le_pow _ _ h2)
    _ = lgN n ^ 3 * dd n m ^ 2 := by ring

/-- `t = ⌈(lgN / dd)^{2/3}⌉`: the least `t ≥ 1` with `lgN² ≤ t³ dd²`. -/
def tpar (n m : ℕ) : ℕ := Nat.find (tpar_exists n m)

/-- `k = ⌊√t⌋ + 1`. -/
def kpar (n m : ℕ) : ℕ := Nat.sqrt (tpar n m) + 1

/-- `L = ⌊lgN / t⌋ + 1` recursion levels. -/
def Lpar (n m : ℕ) : ℕ := lgN n / tpar n m + 1

theorem tpar_spec (n m : ℕ) : 1 ≤ tpar n m ∧ lgN n ^ 2 ≤ tpar n m ^ 3 * dd n m ^ 2 :=
  Nat.find_spec (tpar_exists n m)

theorem one_le_tpar (n m : ℕ) : 1 ≤ tpar n m := (tpar_spec n m).1

theorem tpar_le_lgN (n m : ℕ) : tpar n m ≤ lgN n :=
  Nat.find_min' (tpar_exists n m) ((tpar_exists n m).choose_spec.1 |> fun _ =>
    ⟨one_le_lgN n, by
      have h1 : 1 ≤ lgN n := one_le_lgN n
      have h2 : 1 ≤ dd n m := one_le_dd n m
      calc lgN n ^ 2 = lgN n ^ 2 * 1 * 1 := by ring
        _ ≤ lgN n ^ 2 * lgN n * dd n m ^ 2 :=
            Nat.mul_le_mul (Nat.mul_le_mul le_rfl h1) (Nat.one_le_pow _ _ h2)
        _ = lgN n ^ 3 * dd n m ^ 2 := by ring⟩)

/-- Minimality: `(t - 1)³ dd² < lgN²` (vacuous-free form: for `t ≥ 2`; for `t = 1` the left side is `0`). -/
theorem tpar_pred_cube_lt (n m : ℕ) : (tpar n m - 1) ^ 3 * dd n m ^ 2 < lgN n ^ 2 := by
  by_cases h : tpar n m = 1
  · rw [h]; simp; have := one_le_lgN n; positivity
  · have hlt : tpar n m - 1 < tpar n m := by have := one_le_tpar n m; omega
    have hmin := Nat.find_min (tpar_exists n m) hlt
    simp only [not_and, not_le] at hmin
    exact hmin (by have := one_le_tpar n m; omega)

theorem kpar_sq_gt (n m : ℕ) : tpar n m < kpar n m ^ 2 := by
  unfold kpar
  have := Nat.lt_succ_sqrt (tpar n m)
  nlinarith

theorem kpar_pred_sq_le (n m : ℕ) : (kpar n m - 1) ^ 2 ≤ tpar n m := by
  unfold kpar
  simp only [Nat.add_sub_cancel]
  have := Nat.sqrt_le (tpar n m)
  nlinarith

theorem one_le_kpar (n m : ℕ) : 1 ≤ kpar n m := Nat.le_add_left 1 _

/-! ## Real-number facts -/

/-- `lgN n ≤ 3 log (n + 2)`. -/
theorem lgN_le_log (n : ℕ) : (lgN n : ℝ) ≤ 3 * Real.log ((n : ℝ) + 2) := by
  have hl2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlog2le : Real.log 2 ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  unfold lgN
  rcases le_total (Nat.log 2 n) 1 with h | h
  · rw [max_eq_left h]; push_cast; linarith
  · rw [max_eq_right h]
    have hn : n ≠ 0 := by
      intro h0; subst h0; simp at h
    have hpow : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn
    have hpowR : (2 : ℝ) ^ (Nat.log 2 n) ≤ (n : ℝ) + 2 := by
      have : ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ n := by exact_mod_cast hpow
      push_cast at this; linarith
    have hlog : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log ((n : ℝ) + 2) := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) hpowR
    have hlogpos : 0 ≤ Real.log ((n : ℝ) + 2) := le_trans (by linarith) hlog2le
    nlinarith

theorem log_n2_pos (n : ℕ) : 0 < Real.log ((n : ℝ) + 2) :=
  Real.log_pos (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)

/-- Cube-root extraction: `a³ ≤ b`, `a, b ≥ 0` ⟹ `a ≤ b^{1/3}`. -/
theorem le_rpow_third {a b : ℝ} (ha : 0 ≤ a) (_hb : 0 ≤ b) (h : a ^ 3 ≤ b) : a ≤ b ^ ((1 : ℝ) / 3) := by
  have h1 : (a ^ 3) ^ ((1 : ℝ) / 3) = a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]; norm_num
  calc a = (a ^ 3) ^ ((1 : ℝ) / 3) := h1.symm
    _ ≤ b ^ ((1 : ℝ) / 3) := Real.rpow_le_rpow (by positivity) h (by norm_num)

/-- `(c · m · x²)^{1/3} = c^{1/3} m^{1/3} x^{2/3}` for nonnegative `c, m, x`. -/
theorem rpow_third_eq {c m x : ℝ} (hc : 0 ≤ c) (hm : 0 ≤ m) (hx : 0 ≤ x) :
    (c * m * x ^ 2) ^ ((1 : ℝ) / 3) = c ^ ((1 : ℝ) / 3) * m ^ ((1 : ℝ) / 3) * x ^ ((2 : ℝ) / 3) := by
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hc hm]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

/-- `(n · lgN)^{2/3} ≤ 3 (n log(n+2))^{2/3}`. -/
theorem nlgN_rpow_le (n : ℕ) :
    ((n : ℝ) * lgN n) ^ ((2 : ℝ) / 3) ≤ 3 * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hl0 : 0 ≤ Real.log ((n : ℝ) + 2) := le_of_lt (log_n2_pos n)
  have hle : (n : ℝ) * lgN n ≤ 3 * ((n : ℝ) * Real.log ((n : ℝ) + 2)) := by
    have := lgN_le_log n; nlinarith
  calc ((n : ℝ) * lgN n) ^ ((2 : ℝ) / 3) ≤ (3 * ((n : ℝ) * Real.log ((n : ℝ) + 2))) ^ ((2 : ℝ) / 3) :=
        Real.rpow_le_rpow (by positivity) hle (by norm_num)
    _ = (3 : ℝ) ^ ((2 : ℝ) / 3) * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3) :=
        Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ 3 * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3) := by
        gcongr
        calc (3 : ℝ) ^ ((2 : ℝ) / 3) ≤ (3 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 3 := Real.rpow_one 3

/-- The main term of `Tchd`. -/
noncomputable def mainTerm (n m : ℕ) : ℝ :=
  (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3)

theorem mainTerm_le_Tchd (n m : ℕ) : mainTerm n m ≤ Tchd n m := by
  unfold mainTerm Tchd
  have h1 : 0 ≤ Real.log ((m : ℝ) / ((n : ℝ) + 1) + 2) := by
    apply Real.log_nonneg
    have : 0 ≤ (m : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith
  have : (0 : ℝ) ≤ (m : ℝ) * Real.log ((m : ℝ) / ((n : ℝ) + 1) + 2) := by positivity
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem n_le_Tchd (n m : ℕ) : (n : ℝ) ≤ Tchd n m := by
  have := mainTerm_le_Tchd n m
  unfold Tchd mainTerm at *
  have h1 : 0 ≤ Real.log ((m : ℝ) / ((n : ℝ) + 1) + 2) := by
    apply Real.log_nonneg
    have : 0 ≤ (m : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith
  have : (0 : ℝ) ≤ (m : ℝ) * Real.log ((m : ℝ) / ((n : ℝ) + 1) + 2) := by positivity
  have : (0 : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3) := by
    have := log_n2_pos n; positivity
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem m_le_Tchd (n m : ℕ) : (m : ℝ) ≤ Tchd n m := by
  unfold Tchd
  have h1 : 0 ≤ Real.log ((m : ℝ) / ((n : ℝ) + 1) + 2) := by
    apply Real.log_nonneg
    have : 0 ≤ (m : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith
  have : (0 : ℝ) ≤ (m : ℝ) * Real.log ((m : ℝ) / ((n : ℝ) + 1) + 2) := by positivity
  have : (0 : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3) := by
    have := log_n2_pos n; positivity
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-! ## Term 1: jumps and failed searches, `m · t` -/

/-- Integer core of term 1: `m² (t-1)³ ≤ n² lgN²`. -/
theorem term1_nat (n m : ℕ) (hn : 1 ≤ n) : m ^ 2 * (tpar n m - 1) ^ 3 ≤ n ^ 2 * lgN n ^ 2 := by
  have hmd : m ≤ n * dd n m := by
    unfold dd
    have := Nat.lt_div_mul_add (a := m) (show 0 < n by omega)
    nlinarith [Nat.div_mul_le_self m n]
  have h := tpar_pred_cube_lt n m
  calc m ^ 2 * (tpar n m - 1) ^ 3 ≤ (n * dd n m) ^ 2 * (tpar n m - 1) ^ 3 := by gcongr
    _ = n ^ 2 * ((tpar n m - 1) ^ 3 * dd n m ^ 2) := by ring
    _ ≤ n ^ 2 * lgN n ^ 2 := Nat.mul_le_mul le_rfl (le_of_lt h)

/-- **Term 1.** `m · t ≤ 10 · Tchd n m`. -/
theorem term_mt (n m : ℕ) (hn : 1 ≤ n) : (m : ℝ) * tpar n m ≤ 10 * Tchd n m := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have ht1 : (1 : ℝ) ≤ tpar n m := by exact_mod_cast one_le_tpar n m
  set a : ℝ := (m : ℝ) * ((tpar n m : ℝ) - 1) with ha
  have ha0 : 0 ≤ a := by rw [ha]; nlinarith
  have hcube : a ^ 3 ≤ 1 * (m : ℝ) * ((n : ℝ) * lgN n) ^ 2 := by
    have hnat := term1_nat n m hn
    have hsub : ((tpar n m - 1 : ℕ) : ℝ) = (tpar n m : ℝ) - 1 := by
      rw [Nat.cast_sub (one_le_tpar n m)]; simp
    have hR : (m : ℝ) ^ 2 * ((tpar n m : ℝ) - 1) ^ 3 ≤ (n : ℝ) ^ 2 * (lgN n : ℝ) ^ 2 := by
      rw [← hsub]; exact_mod_cast hnat
    rw [ha]
    have : ((m : ℝ) * ((tpar n m : ℝ) - 1)) ^ 3 = (m : ℝ) * ((m : ℝ) ^ 2 * ((tpar n m : ℝ) - 1) ^ 3) := by ring
    rw [this]
    have : 1 * (m : ℝ) * ((n : ℝ) * lgN n) ^ 2 = (m : ℝ) * ((n : ℝ) ^ 2 * (lgN n : ℝ) ^ 2) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hR hm0
  have hroot := le_rpow_third ha0 (by positivity) hcube
  rw [rpow_third_eq (by norm_num) hm0 (by positivity), Real.one_rpow, one_mul] at hroot
  have hmain := nlgN_rpow_le n
  have hm13 : 0 ≤ (m : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have hstep : a ≤ 3 * mainTerm n m := by
    unfold mainTerm
    calc a ≤ (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * lgN n) ^ ((2 : ℝ) / 3) := hroot
      _ ≤ (m : ℝ) ^ ((1 : ℝ) / 3) * (3 * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3)) :=
          mul_le_mul_of_nonneg_left hmain hm13
      _ = 3 * ((m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3)) := by ring
  have hsplit : (m : ℝ) * tpar n m = a + m := by rw [ha]; ring
  have h1 := mainTerm_le_Tchd n m
  have h2 := m_le_Tchd n m
  rw [hsplit]
  linarith


/-! ## Term 2: per-level work, `n · L · k` and `n · L · (t / k + 1)` -/

/-- `k ≤ √t + 1`. -/
theorem kpar_le_sqrt_add_one (n m : ℕ) : (kpar n m : ℝ) ≤ Real.sqrt (tpar n m) + 1 := by
  have h := kpar_pred_sq_le n m
  have hk1 := one_le_kpar n m
  have hR : (((kpar n m - 1 : ℕ) : ℝ)) ^ 2 ≤ (tpar n m : ℝ) := by exact_mod_cast h
  have hsq : ((kpar n m - 1 : ℕ) : ℝ) ≤ Real.sqrt (tpar n m) :=
    Real.le_sqrt_of_sq_le hR
  have hcast : ((kpar n m - 1 : ℕ) : ℝ) = (kpar n m : ℝ) - 1 := by
    rw [Nat.cast_sub hk1]; simp
  linarith

/-- `√t < k`. -/
theorem sqrt_lt_kpar (n m : ℕ) : Real.sqrt (tpar n m) < kpar n m := by
  have h := kpar_sq_gt n m
  have hR : (tpar n m : ℝ) < (kpar n m : ℝ) ^ 2 := by exact_mod_cast h
  have hk0 : (0 : ℝ) ≤ kpar n m := Nat.cast_nonneg _
  exact (Real.sqrt_lt' (by have := one_le_kpar n m; positivity)).mpr hR

/-- The core estimate: with `s = √t`, `n · lgN / s ≤ 15 · mainTerm` whenever `n ≤ m + 1`, `1 ≤ n`. -/
theorem core_nlgN_div_sqrt (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ m + 1) :
    (n : ℝ) * lgN n / Real.sqrt (tpar n m) ≤ 15 * mainTerm n m := by
  have ht1 : (1 : ℝ) ≤ tpar n m := by exact_mod_cast one_le_tpar n m
  set s : ℝ := Real.sqrt (tpar n m) with hs
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr ht1
  have hs0 : 0 < s := by linarith
  have hss : s ^ 2 = tpar n m := by rw [hs]; exact Real.sq_sqrt (by linarith)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hl1 : (1 : ℝ) ≤ lgN n := by exact_mod_cast one_le_lgN n
  have hd1 : (1 : ℝ) ≤ dd n m := by exact_mod_cast one_le_dd n m
  -- lgN ≤ s³ · dd
  have hspec : (lgN n : ℝ) ^ 2 ≤ (tpar n m : ℝ) ^ 3 * (dd n m : ℝ) ^ 2 := by
    exact_mod_cast (tpar_spec n m).2
  have hlg : (lgN n : ℝ) ≤ s ^ 3 * dd n m := by
    have hsq : (lgN n : ℝ) ^ 2 ≤ (s ^ 3 * dd n m) ^ 2 := by
      rw [← hss] at hspec; nlinarith [hspec]
    have hb0 : (0 : ℝ) ≤ s ^ 3 * dd n m := by positivity
    by_contra hc
    push_neg at hc
    have := mul_lt_mul'' hc hc hb0 hb0
    nlinarith
  -- n · dd ≤ 3 m
  have hndd : (n : ℝ) * dd n m ≤ 3 * m := by
    have hnat : n * dd n m ≤ m + n := by
      unfold dd
      have := Nat.div_mul_le_self m n
      nlinarith [Nat.mul_comm (m / n) n]
    have : ((n * dd n m : ℕ) : ℝ) ≤ (m : ℝ) + n := by exact_mod_cast hnat
    have hnm' : (n : ℝ) ≤ m + 1 := by exact_mod_cast hnm
    push_cast at this
    linarith
  set X : ℝ := (n : ℝ) * lgN n / s with hX
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hX3 : X ^ 3 ≤ 3 * (m : ℝ) * ((n : ℝ) * lgN n) ^ 2 := by
    rw [hX, div_pow]
    rw [div_le_iff₀ (by positivity)]
    have : ((n : ℝ) * lgN n) ^ 3 = ((n : ℝ) * lgN n) ^ 2 * ((n : ℝ) * lgN n) := by ring
    rw [this]
    have key : (n : ℝ) * lgN n ≤ 3 * m * s ^ 3 := by
      calc (n : ℝ) * lgN n ≤ (n : ℝ) * (s ^ 3 * dd n m) := mul_le_mul_of_nonneg_left hlg (le_of_lt hn0)
        _ = s ^ 3 * ((n : ℝ) * dd n m) := by ring
        _ ≤ s ^ 3 * (3 * m) := mul_le_mul_of_nonneg_left hndd (by positivity)
        _ = 3 * m * s ^ 3 := by ring
    have hsq0 : 0 ≤ ((n : ℝ) * lgN n) ^ 2 := by positivity
    calc ((n : ℝ) * lgN n) ^ 2 * ((n : ℝ) * lgN n) ≤ ((n : ℝ) * lgN n) ^ 2 * (3 * m * s ^ 3) :=
          mul_le_mul_of_nonneg_left key hsq0
      _ = 3 * (m : ℝ) * ((n : ℝ) * lgN n) ^ 2 * s ^ 3 := by ring
  have hroot := le_rpow_third hX0 (by positivity) hX3
  rw [rpow_third_eq (by norm_num) (by positivity) (by positivity)] at hroot
  have h3 : (3 : ℝ) ^ ((1 : ℝ) / 3) ≤ 3 := by
    calc (3 : ℝ) ^ ((1 : ℝ) / 3) ≤ (3 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 3 := Real.rpow_one 3
  have hmain := nlgN_rpow_le n
  have hm13 : 0 ≤ (m : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have hx23 : 0 ≤ ((n : ℝ) * lgN n) ^ ((2 : ℝ) / 3) := by positivity
  unfold mainTerm
  calc X ≤ (3 : ℝ) ^ ((1 : ℝ) / 3) * (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * lgN n) ^ ((2 : ℝ) / 3) := hroot
    _ ≤ 3 * (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * lgN n) ^ ((2 : ℝ) / 3) := by gcongr
    _ ≤ 3 * (m : ℝ) ^ ((1 : ℝ) / 3) * (3 * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3)) := by
        gcongr
    _ ≤ 15 * ((m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3)) := by
        have : 0 ≤ (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3) := by
          have := log_n2_pos n; positivity
        nlinarith

/-- `(lgN / t + 1) · (√t + 1) ≤ 2 lgN / √t + 2 √t` (real form of `L · k`). -/
theorem Lk_real (n m : ℕ) :
    ((lgN n / tpar n m : ℕ) + 1 : ℝ) * (Real.sqrt (tpar n m) + 1)
      ≤ 2 * (lgN n / Real.sqrt (tpar n m)) + 2 * Real.sqrt (tpar n m) := by
  have ht1 : (1 : ℝ) ≤ tpar n m := by exact_mod_cast one_le_tpar n m
  set s : ℝ := Real.sqrt (tpar n m) with hs
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr ht1
  have hss : s ^ 2 = tpar n m := by rw [hs]; exact Real.sq_sqrt (by linarith)
  have hdiv : ((lgN n / tpar n m : ℕ) : ℝ) ≤ (lgN n : ℝ) / tpar n m := Nat.cast_div_le
  have hl0 : (0 : ℝ) ≤ lgN n := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) ≤ ((lgN n / tpar n m : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [← hss] at hdiv
  have e1 : (lgN n : ℝ) / s ^ 2 * (s + 1) ≤ 2 * ((lgN n : ℝ) / s) := by
    have hs0 : 0 < s := by linarith
    have h2s : s + 1 ≤ 2 * s := by linarith
    have hq : (0 : ℝ) ≤ (lgN n : ℝ) / s ^ 2 := by positivity
    calc (lgN n : ℝ) / s ^ 2 * (s + 1) ≤ (lgN n : ℝ) / s ^ 2 * (2 * s) := mul_le_mul_of_nonneg_left h2s hq
      _ = 2 * ((lgN n : ℝ) / s) := by field_simp
  calc (((lgN n / tpar n m : ℕ) : ℝ) + 1) * (s + 1)
      = ((lgN n / tpar n m : ℕ) : ℝ) * (s + 1) + (s + 1) := by ring
    _ ≤ (lgN n : ℝ) / s ^ 2 * (s + 1) + (s + 1) := by gcongr
    _ ≤ 2 * ((lgN n : ℝ) / s) + 2 * s := by linarith

/-- `n · t ≤ 16 · Tchd` under `n ≤ m + 1`. -/
theorem term_nt (n m : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m + 1) : (n : ℝ) * tpar n m ≤ 16 * Tchd n m := by
  have h1 := term_mt n m hn
  have hnm' : (n : ℝ) ≤ m + 1 := by exact_mod_cast hnm
  have ht0 : (0 : ℝ) ≤ tpar n m := Nat.cast_nonneg _
  have htl : (tpar n m : ℝ) ≤ lgN n := by exact_mod_cast tpar_le_lgN n m
  have hlog := lgN_le_log n
  have hlogle : Real.log ((n : ℝ) + 2) ≤ (n : ℝ) + 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (n : ℝ) + 2 by positivity); linarith
  have hnT := n_le_Tchd n m
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have htT : (tpar n m : ℝ) ≤ 6 * Tchd n m := by nlinarith
  calc (n : ℝ) * tpar n m ≤ ((m : ℝ) + 1) * tpar n m := mul_le_mul_of_nonneg_right hnm' ht0
    _ = (m : ℝ) * tpar n m + tpar n m := by ring
    _ ≤ 16 * Tchd n m := by linarith

/-- **Term 2a.** `n · L · k ≤ 70 · Tchd` under `1 ≤ n ≤ m + 1`, `1 ≤ m`. -/
theorem term_nLk (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ m + 1) :
    (n : ℝ) * Lpar n m * kpar n m ≤ 70 * Tchd n m := by
  have ht1 : (1 : ℝ) ≤ tpar n m := by exact_mod_cast one_le_tpar n m
  set s : ℝ := Real.sqrt (tpar n m) with hs
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr ht1
  have hst : s ≤ tpar n m := by
    have hss : s ^ 2 = tpar n m := by rw [hs]; exact Real.sq_sqrt (by linarith)
    nlinarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hL : (Lpar n m : ℝ) = ((lgN n / tpar n m : ℕ) : ℝ) + 1 := by unfold Lpar; push_cast; ring
  have hk := kpar_le_sqrt_add_one n m
  have hLk := Lk_real n m
  have hL0 : (0 : ℝ) ≤ Lpar n m := Nat.cast_nonneg _
  have hcore := core_nlgN_div_sqrt n m hn hm hnm
  have hnt := term_nt n m hn hnm
  have hmainT := mainTerm_le_Tchd n m
  calc (n : ℝ) * Lpar n m * kpar n m ≤ (n : ℝ) * Lpar n m * (s + 1) := by gcongr
    _ = (n : ℝ) * ((((lgN n / tpar n m : ℕ) : ℝ) + 1) * (s + 1)) := by rw [hL]; ring
    _ ≤ (n : ℝ) * (2 * (lgN n / s) + 2 * s) := mul_le_mul_of_nonneg_left hLk hn0
    _ = 2 * ((n : ℝ) * lgN n / s) + 2 * ((n : ℝ) * s) := by ring
    _ ≤ 2 * (15 * mainTerm n m) + 2 * ((n : ℝ) * tpar n m) := by
        gcongr
    _ ≤ 70 * Tchd n m := by have := Tchd_nonneg n m; linarith

/-- **Term 2b.** `n · L · (t / k + 1) ≤ 70 · Tchd` (pivot inserts `t/k` per vertex per level). -/
theorem term_nLtk (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ m + 1) :
    (n : ℝ) * Lpar n m * ((tpar n m / kpar n m : ℕ) + 1 : ℝ) ≤ 70 * Tchd n m := by
  have hle : ((tpar n m / kpar n m : ℕ) : ℝ) + 1 ≤ kpar n m := by
    have hk1 := one_le_kpar n m
    have hdiv : tpar n m / kpar n m < kpar n m := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      have := kpar_sq_gt n m; nlinarith
    have : tpar n m / kpar n m + 1 ≤ kpar n m := hdiv
    exact_mod_cast this
  have h := term_nLk n m hn hm hnm
  have hnL : (0 : ℝ) ≤ (n : ℝ) * Lpar n m := by positivity
  calc (n : ℝ) * Lpar n m * (((tpar n m / kpar n m : ℕ) : ℝ) + 1) ≤ (n : ℝ) * Lpar n m * kpar n m :=
        mul_le_mul_of_nonneg_left hle hnL
    _ ≤ 70 * Tchd n m := h

/-- **Term 2c.** the structural per-level term `n · L ≤ 70 · Tchd`. -/
theorem term_nL (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ m + 1) :
    (n : ℝ) * Lpar n m ≤ 70 * Tchd n m := by
  have hk1 : (1 : ℝ) ≤ kpar n m := by exact_mod_cast one_le_kpar n m
  have h := term_nLk n m hn hm hnm
  have hnL : (0 : ℝ) ≤ (n : ℝ) * Lpar n m := by positivity
  nlinarith

/-! ## Term 3: logarithms of the density and of `t` -/

theorem natlog_le_real (x : ℕ) (hx : 1 ≤ x) :
    (Nat.log 2 x : ℝ) * Real.log 2 ≤ Real.log x := by
  have hpow : 2 ^ Nat.log 2 x ≤ x := Nat.pow_log_le_self 2 (by omega)
  have hpowR : (2 : ℝ) ^ (Nat.log 2 x) ≤ x := by exact_mod_cast hpow
  rw [← Real.log_pow]
  exact Real.log_le_log (by positivity) hpowR

/-- **Term 3a.** `m · log₂(dd + 1) ≤ 3 · Tchd` (sorting out-lists, `D` insertions `lg δ`). -/
theorem term_mlogdd (n m : ℕ) (hn : 1 ≤ n) :
    (m : ℝ) * Nat.log 2 (dd n m + 1) ≤ 3 * Tchd n m := by
  have hl2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  set y : ℝ := (m : ℝ) / ((n : ℝ) + 1) + 2 with hy
  have hy2 : 2 ≤ y := by
    have : 0 ≤ (m : ℝ) / ((n : ℝ) + 1) := by positivity
    rw [hy]; linarith
  have hlogy : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy2
  -- dd + 1 ≤ 2 y
  have hdd : ((dd n m + 1 : ℕ) : ℝ) ≤ 2 * y := by
    have hdiv : ((m / n : ℕ) : ℝ) ≤ (m : ℝ) / n := Nat.cast_div_le
    have h2 : (m : ℝ) / n ≤ 2 * ((m : ℝ) / ((n : ℝ) + 1)) := by
      rw [div_le_iff₀ (by linarith), mul_comm, ← mul_assoc]
      rw [mul_div_assoc']
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    unfold dd; push_cast
    rw [hy]; linarith
  have hlogdd : Real.log ((dd n m + 1 : ℕ) : ℝ) ≤ 2 * Real.log y := by
    have hpos : (0 : ℝ) < ((dd n m + 1 : ℕ) : ℝ) := by positivity
    calc Real.log ((dd n m + 1 : ℕ) : ℝ) ≤ Real.log (2 * y) := Real.log_le_log hpos hdd
      _ = Real.log 2 + Real.log y := Real.log_mul (by norm_num) (by linarith)
      _ ≤ 2 * Real.log y := by linarith
  have hnl := natlog_le_real (dd n m + 1) (by omega)
  have hnatlog : (Nat.log 2 (dd n m + 1) : ℝ) ≤ 3 * Real.log y := by
    have hly0 : 0 ≤ Real.log y := le_trans (by linarith) hlogy
    have : (Nat.log 2 (dd n m + 1) : ℝ) * Real.log 2 ≤ 2 * Real.log y := le_trans hnl hlogdd
    nlinarith
  have hT : (m : ℝ) * Real.log y ≤ Tchd n m := by
    unfold Tchd; rw [← hy]
    have : (0 : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3) := by
      have := log_n2_pos n; positivity
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  calc (m : ℝ) * Nat.log 2 (dd n m + 1) ≤ (m : ℝ) * (3 * Real.log y) := mul_le_mul_of_nonneg_left hnatlog hm0
    _ = 3 * ((m : ℝ) * Real.log y) := by ring
    _ ≤ 3 * Tchd n m := by linarith

/-- `log₂(t + 1) ≤ t` for `t ≥ 1`. -/
theorem natlog_succ_le (t : ℕ) (ht : 1 ≤ t) : Nat.log 2 (t + 1) ≤ t := by
  have h : t + 1 < 2 ^ (t + 1) := Nat.lt_two_pow_self
  have h2 : Nat.log 2 (t + 1) < t + 1 := Nat.log_lt_of_lt_pow (by omega) h
  omega

/-- **Term 3b.** `m · log₂(t + 1) ≤ 10 · Tchd` (local heap / BST depth inside searches and base cases). -/
theorem term_mlogt (n m : ℕ) (hn : 1 ≤ n) :
    (m : ℝ) * Nat.log 2 (tpar n m + 1) ≤ 10 * Tchd n m := by
  have h := natlog_succ_le (tpar n m) (one_le_tpar n m)
  have hR : (Nat.log 2 (tpar n m + 1) : ℝ) ≤ tpar n m := by exact_mod_cast h
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  calc (m : ℝ) * Nat.log 2 (tpar n m + 1) ≤ (m : ℝ) * tpar n m := mul_le_mul_of_nonneg_left hR hm0
    _ ≤ 10 * Tchd n m := term_mt n m hn

/-- `log₂ (x·y) ≤ log₂ x + log₂ y + 1`. -/
theorem natlog_mul_le (x y : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    Nat.log 2 (x * y) ≤ Nat.log 2 x + Nat.log 2 y + 1 := by
  have hx' : x < 2 ^ (Nat.log 2 x + 1) := Nat.lt_pow_succ_log_self (by norm_num) x
  have hy' : y < 2 ^ (Nat.log 2 y + 1) := Nat.lt_pow_succ_log_self (by norm_num) y
  have hxy : x * y < 2 ^ (Nat.log 2 x + Nat.log 2 y + 2) := by
    calc x * y < 2 ^ (Nat.log 2 x + 1) * 2 ^ (Nat.log 2 y + 1) := Nat.mul_lt_mul'' hx' hy'
      _ = 2 ^ (Nat.log 2 x + Nat.log 2 y + 2) := by rw [← pow_add]; ring_nf
  have := Nat.log_lt_of_lt_pow (by positivity) hxy
  omega


/-! ## Side conditions on the window `m ≤ n · F n` (`F` = agent-10's integer threshold `⌊(log₂ n)^{3/4}⌋`) -/

/-- On the window, `dd ≤ F n + 1`. -/
theorem dd_le_F (n m : ℕ) (hn : 1 ≤ n) (hw : m ≤ n * Frontier.GateCCalc.F n) :
    dd n m ≤ Frontier.GateCCalc.F n + 1 := by
  unfold dd
  have : m / n ≤ Frontier.GateCCalc.F n := by
    rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
    nlinarith
  omega

/-- `(F n)⁴ ≤ (log₂ n)³`. -/
theorem F_pow_four_le (n : ℕ) : Frontier.GateCCalc.F n ^ 4 ≤ Nat.log 2 n ^ 3 := by
  unfold Frontier.GateCCalc.F
  set a := Nat.log 2 n ^ 3
  have h1 : Nat.sqrt (Nat.sqrt a) * Nat.sqrt (Nat.sqrt a) ≤ Nat.sqrt a := Nat.sqrt_le _
  have h2 : Nat.sqrt a * Nat.sqrt a ≤ a := Nat.sqrt_le _
  have h3 : Nat.sqrt (Nat.sqrt a) ^ 4 = (Nat.sqrt (Nat.sqrt a) * Nat.sqrt (Nat.sqrt a)) ^ 2 := by ring
  rw [h3]
  calc (Nat.sqrt (Nat.sqrt a) * Nat.sqrt (Nat.sqrt a)) ^ 2 ≤ (Nat.sqrt a) ^ 2 := Nat.pow_le_pow_left h1 2
    _ = Nat.sqrt a * Nat.sqrt a := by ring
    _ ≤ a := h2

/-- **`t` is uniformly large on the window.**  For every `A`, if `256 · A¹² < lgN²` then `A ≤ t` for all
`m ≤ n · F n`.  (So every side condition of the form `t ≥ const` holds for all `n ≥ n₀(const)`.) -/
theorem tpar_ge_of_large (A n m : ℕ) (hn : 1 ≤ n) (hw : m ≤ n * Frontier.GateCCalc.F n)
    (hbig : 256 * A ^ 12 < lgN n ^ 2) : A ≤ tpar n m := by
  by_contra hlt
  push_neg at hlt
  have ht : tpar n m ≤ A := le_of_lt hlt
  set f := Frontier.GateCCalc.F n
  have hdd := dd_le_F n m hn hw
  have hspec := (tpar_spec n m).2
  -- lgN² ≤ A³ (f+1)²
  have h1 : lgN n ^ 2 ≤ A ^ 3 * (f + 1) ^ 2 :=
    le_trans hspec (Nat.mul_le_mul (Nat.pow_le_pow_left ht 3) (Nat.pow_le_pow_left hdd 2))
  -- (f+1)⁴ ≤ 16 lgN³
  have hl1 : 1 ≤ lgN n := one_le_lgN n
  have hlog_le : Nat.log 2 n ≤ lgN n := le_max_right _ _
  have hf4 : f ^ 4 ≤ lgN n ^ 3 := le_trans (F_pow_four_le n) (Nat.pow_le_pow_left hlog_le 3)
  have hf1 : (f + 1) ^ 4 ≤ 16 * lgN n ^ 3 := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0]; have : 1 ≤ lgN n ^ 3 := Nat.one_le_pow _ _ hl1; omega
    · have : f + 1 ≤ 2 * f := by omega
      calc (f + 1) ^ 4 ≤ (2 * f) ^ 4 := Nat.pow_le_pow_left this 4
        _ = 16 * f ^ 4 := by ring
        _ ≤ 16 * lgN n ^ 3 := by omega
  -- square h1 and combine: lgN⁴ ≤ A⁶ (f+1)⁴ ≤ 16 A⁶ lgN³, so lgN ≤ 16 A⁶, so lgN² ≤ 256 A¹²
  have h2 : lgN n ^ 4 ≤ A ^ 6 * (f + 1) ^ 4 := by
    have := Nat.pow_le_pow_left h1 2
    calc lgN n ^ 4 = (lgN n ^ 2) ^ 2 := by ring
      _ ≤ (A ^ 3 * (f + 1) ^ 2) ^ 2 := this
      _ = A ^ 6 * (f + 1) ^ 4 := by ring
  have h3 : lgN n ^ 4 ≤ A ^ 6 * (16 * lgN n ^ 3) := le_trans h2 (Nat.mul_le_mul le_rfl hf1)
  have h4 : lgN n ≤ 16 * A ^ 6 := by
    have hpos : 0 < lgN n ^ 3 := by positivity
    have : lgN n * lgN n ^ 3 ≤ (16 * A ^ 6) * lgN n ^ 3 := by
      calc lgN n * lgN n ^ 3 = lgN n ^ 4 := by ring
        _ ≤ A ^ 6 * (16 * lgN n ^ 3) := h3
        _ = (16 * A ^ 6) * lgN n ^ 3 := by ring
    exact Nat.le_of_mul_le_mul_right this hpos
  have h5 : lgN n ^ 2 ≤ 256 * A ^ 12 := by
    calc lgN n ^ 2 ≤ (16 * A ^ 6) ^ 2 := Nat.pow_le_pow_left h4 2
      _ = 256 * A ^ 12 := by ring
  omega

/-- `3 k ≤ t` once `t ≥ 16`. -/
theorem three_kpar_le (n m : ℕ) (h16 : 16 ≤ tpar n m) : 3 * kpar n m ≤ tpar n m := by
  unfold kpar
  set t := tpar n m
  have hs : Nat.sqrt t * Nat.sqrt t ≤ t := Nat.sqrt_le t
  have hs4 : 4 ≤ Nat.sqrt t := by
    rw [Nat.le_sqrt]; omega
  nlinarith

/-- `k ≤ t` always. -/
theorem kpar_le_tpar (n m : ℕ) : kpar n m ≤ tpar n m + 1 := by
  unfold kpar
  have := Nat.sqrt_le_self (tpar n m)
  omega


/-! ## Floored parameters (COORD G2-4 decision D2): `t = max 16 tpar`, `k = ⌈√t⌉`

The program computes these.  The floor `t ≥ 16` gives `3k ≤ t`, `2 ≤ k ≤ t` for every input, so the size facts
(B1)/(B2) of the recursion hold unconditionally; the term menu is re-proved for them below (constants larger). -/

/-- `t = max 16 tpar`. -/
def tF (n m : ℕ) : ℕ := max 16 (tpar n m)

/-- `k = ⌈√t⌉` (integer ceiling square root). -/
def kF (n m : ℕ) : ℕ :=
  Nat.sqrt (tF n m) + (if Nat.sqrt (tF n m) * Nat.sqrt (tF n m) = tF n m then 0 else 1)

/-- `L = ⌊lgN / t⌋ + 1`. -/
def LF (n m : ℕ) : ℕ := lgN n / tF n m + 1

theorem sixteen_le_tF (n m : ℕ) : 16 ≤ tF n m := le_max_left _ _

theorem tpar_le_tF (n m : ℕ) : tpar n m ≤ tF n m := le_max_right _ _

theorem tF_le (n m : ℕ) : tF n m ≤ 16 + lgN n := by
  unfold tF; have := tpar_le_lgN n m; omega

theorem tF_spec (n m : ℕ) : lgN n ^ 2 ≤ tF n m ^ 3 * dd n m ^ 2 :=
  le_trans (tpar_spec n m).2 (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (tpar_le_tF n m) 3))

theorem four_le_sqrt_tF (n m : ℕ) : 4 ≤ Nat.sqrt (tF n m) := by
  rw [Nat.le_sqrt]; have := sixteen_le_tF n m; omega

theorem kF_le_sqrt_succ (n m : ℕ) : kF n m ≤ Nat.sqrt (tF n m) + 1 := by
  unfold kF; split_ifs <;> omega

theorem sqrt_le_kF (n m : ℕ) : Nat.sqrt (tF n m) ≤ kF n m := by
  unfold kF; split_ifs <;> omega

/-- `t ≤ k²` (ceiling). -/
theorem tF_le_kF_sq (n m : ℕ) : tF n m ≤ kF n m ^ 2 := by
  unfold kF
  set t := tF n m
  split_ifs with h
  · simp only [Nat.add_zero, pow_two]; rw [h]
  · have := Nat.lt_succ_sqrt t
    nlinarith

theorem two_le_kF (n m : ℕ) : 2 ≤ kF n m := le_trans (by have := four_le_sqrt_tF n m; omega) (sqrt_le_kF n m)

theorem three_kF_le_tF (n m : ℕ) : 3 * kF n m ≤ tF n m := by
  have h1 := kF_le_sqrt_succ n m
  have h4 := four_le_sqrt_tF n m
  have hs : Nat.sqrt (tF n m) * Nat.sqrt (tF n m) ≤ tF n m := Nat.sqrt_le _
  nlinarith

theorem kF_le_tF (n m : ℕ) : kF n m ≤ tF n m := by
  have := three_kF_le_tF n m; omega

/-- **Base-call heap size in `hbase` form.**  A base call's heap holds at most
`K = t(3k+1) + δ t³ + 2` vertices (`|S| ≤ t(3k+1)`, at most `τ₀ = t³` extractions each pushing `≤ δ`); with the
L6 out-degree bound `δ ≤ 5 dd`, `log₂(K+1) ≤ 3 log₂(t+1) + log₂(dd+1) + 6` — so IHeap's `O(log K)` per operation
fits `CostFinal.total_le_Tchd`'s `hbase` (constant factor `3`). -/
theorem heap_log_le (n m δ : ℕ) (hδ : δ ≤ 5 * dd n m) :
    Nat.log 2 (tF n m * (3 * kF n m + 1) + δ * tF n m ^ 3 + 3) ≤
      3 * Nat.log 2 (tF n m + 1) + Nat.log 2 (dd n m + 1) + 6 := by
  set t := tF n m with ht
  set k := kF n m with hk
  set d := dd n m with hd
  have ht16 : 16 ≤ t := sixteen_le_tF n m
  have hkt : k ≤ t := kF_le_tF n m
  have hd1 : 1 ≤ d := one_le_dd n m
  set Lt := Nat.log 2 (t + 1) with hLt
  set Ld := Nat.log 2 (d + 1) with hLd
  have h1 : t + 1 < 2 ^ (Lt + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : d + 1 < 2 ^ (Ld + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  -- `X ≤ 6 d t³`
  have hX : t * (3 * k + 1) + δ * t ^ 3 + 3 ≤ 6 * d * t ^ 3 := by
    have e1 : t * (3 * k + 1) ≤ t * (3 * t + 1) := Nat.mul_le_mul_left _ (by omega)
    have e2 : δ * t ^ 3 ≤ 5 * d * t ^ 3 := Nat.mul_le_mul_right _ hδ
    have e3 : t * (3 * t + 1) + 3 ≤ t ^ 3 := by
      have h16 : 16 * (t * t) ≤ t * (t * t) := Nat.mul_le_mul_right _ ht16
      have htt : 1 ≤ t * t := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have e : t ^ 3 = t * (t * t) := by ring
      have e' : t * (3 * t + 1) = 3 * (t * t) + t := by ring
      rw [e, e']
      nlinarith
    have e4 : t ^ 3 ≤ d * t ^ 3 := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith
  -- `6 d t³ < 2^(3 Lt + Ld + 7)`
  have hP : 6 * d * t ^ 3 < 2 ^ (3 * Lt + Ld + 7) := by
    have h3 : (t + 1) ^ 3 < (2 ^ (Lt + 1)) ^ 3 := Nat.pow_lt_pow_left h1 (by norm_num)
    have e5 : 6 * d * t ^ 3 < 8 * (d + 1) * (t + 1) ^ 3 := by
      have hlt3 : t ^ 3 < (t + 1) ^ 3 := Nat.pow_lt_pow_left (by omega) (by norm_num)
      have hA : (d + 1) * t ^ 3 ≤ (d + 1) * (t + 1) ^ 3 := Nat.mul_le_mul_left _ hlt3.le
      have hB : 0 < (d + 1) * (t + 1) ^ 3 := by positivity
      have hdt : d * t ^ 3 ≤ (d + 1) * t ^ 3 := Nat.mul_le_mul_right _ (by omega)
      calc 6 * d * t ^ 3 = 6 * (d * t ^ 3) := by ring
        _ < 8 * ((d + 1) * (t + 1) ^ 3) := by omega
        _ = 8 * (d + 1) * (t + 1) ^ 3 := by ring
    have e6 : 8 * (d + 1) * (t + 1) ^ 3 ≤ 8 * 2 ^ (Ld + 1) * (2 ^ (Lt + 1)) ^ 3 := by
      apply Nat.mul_le_mul (Nat.mul_le_mul_left _ h2.le) h3.le
    have e7 : 8 * 2 ^ (Ld + 1) * (2 ^ (Lt + 1)) ^ 3 = 2 ^ (3 * Lt + Ld + 7) := by
      rw [← pow_mul]
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add, ← pow_add]
      congr 1; ring
    omega
  have hlt : Nat.log 2 (t * (3 * k + 1) + δ * t ^ 3 + 3) < 3 * Lt + Ld + 7 :=
    Nat.log_lt_of_lt_pow (by omega) (lt_of_le_of_lt hX hP)
  omega

/-- `3k + 1 ≤ t` (the level-`l` partial-call condition `τ(l-1) ≥ t·M_l·(3k+1)` for `Λ = t³2^{lt}`,
`M_l = t 2^{(l-1)t}` reduces to it; asked by agent-01 for `partial_S`). -/
theorem three_kF_add_one_le_tF (n m : ℕ) : 3 * kF n m + 1 ≤ tF n m := by
  have h1 := kF_le_sqrt_succ n m
  have h4 := four_le_sqrt_tF n m
  have hs : Nat.sqrt (tF n m) * Nat.sqrt (tF n m) ≤ tF n m := Nat.sqrt_le _
  nlinarith

/-- The parameter fact behind `Valid.partial_S` with the paper's caps: for every level `l`,
`t · M_{l+1} · (3k+1) ≤ Λ_l` where `M_{l+1} = t 2^{lt}` and `Λ_l = t³ 2^{lt}`. -/
theorem tau_ge_tM (n m l : ℕ) :
    tF n m * (tF n m * 2 ^ (l * tF n m)) * (3 * kF n m + 1) ≤ tF n m ^ 3 * 2 ^ (l * tF n m) := by
  have h := three_kF_add_one_le_tF n m
  have e : tF n m ^ 3 * 2 ^ (l * tF n m) = tF n m * (tF n m * 2 ^ (l * tF n m)) * tF n m := by ring
  rw [e]
  exact Nat.mul_le_mul_left _ h

/-- Real forms. -/
theorem kF_le_real (n m : ℕ) : (kF n m : ℝ) ≤ Real.sqrt (tF n m) + 1 := by
  have h := kF_le_sqrt_succ n m
  have hs : ((Nat.sqrt (tF n m) : ℕ) : ℝ) ≤ Real.sqrt (tF n m) := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    have := Nat.sqrt_le' (tF n m)
    exact_mod_cast this
  have : (kF n m : ℝ) ≤ ((Nat.sqrt (tF n m) : ℕ) : ℝ) + 1 := by exact_mod_cast h
  linarith

theorem sqrt_tF_le_kF (n m : ℕ) : Real.sqrt (tF n m) ≤ kF n m := by
  have h := tF_le_kF_sq n m
  have hR : (tF n m : ℝ) ≤ (kF n m : ℝ) ^ 2 := by exact_mod_cast h
  exact Real.sqrt_le_iff.mpr ⟨Nat.cast_nonneg _, hR⟩

/-! ### Generic versions of the core estimates (any `t ≥ 1` with `lgN² ≤ t³ dd²`) -/

theorem core_gen (n m t : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ m + 1) (ht : 1 ≤ t)
    (hspec : lgN n ^ 2 ≤ t ^ 3 * dd n m ^ 2) :
    (n : ℝ) * lgN n / Real.sqrt t ≤ 15 * mainTerm n m := by
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  set s : ℝ := Real.sqrt t with hs
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr ht1
  have hs0 : 0 < s := by linarith
  have hss : s ^ 2 = t := by rw [hs]; exact Real.sq_sqrt (by linarith)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hl1 : (1 : ℝ) ≤ lgN n := by exact_mod_cast one_le_lgN n
  have hd1 : (1 : ℝ) ≤ dd n m := by exact_mod_cast one_le_dd n m
  have hspecR : (lgN n : ℝ) ^ 2 ≤ (t : ℝ) ^ 3 * (dd n m : ℝ) ^ 2 := by exact_mod_cast hspec
  have hlg : (lgN n : ℝ) ≤ s ^ 3 * dd n m := by
    have hsq : (lgN n : ℝ) ^ 2 ≤ (s ^ 3 * dd n m) ^ 2 := by
      rw [← hss] at hspecR; nlinarith [hspecR]
    have hb0 : (0 : ℝ) ≤ s ^ 3 * dd n m := by positivity
    by_contra hc
    push_neg at hc
    have := mul_lt_mul'' hc hc hb0 hb0
    nlinarith
  have hndd : (n : ℝ) * dd n m ≤ 3 * m := by
    have hnat : n * dd n m ≤ m + n := by
      unfold dd
      have := Nat.div_mul_le_self m n
      nlinarith [Nat.mul_comm (m / n) n]
    have : ((n * dd n m : ℕ) : ℝ) ≤ (m : ℝ) + n := by exact_mod_cast hnat
    have hnm' : (n : ℝ) ≤ m + 1 := by exact_mod_cast hnm
    push_cast at this
    linarith
  set X : ℝ := (n : ℝ) * lgN n / s with hX
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hX3 : X ^ 3 ≤ 3 * (m : ℝ) * ((n : ℝ) * lgN n) ^ 2 := by
    rw [hX, div_pow, div_le_iff₀ (by positivity)]
    have : ((n : ℝ) * lgN n) ^ 3 = ((n : ℝ) * lgN n) ^ 2 * ((n : ℝ) * lgN n) := by ring
    rw [this]
    have key : (n : ℝ) * lgN n ≤ 3 * m * s ^ 3 := by
      calc (n : ℝ) * lgN n ≤ (n : ℝ) * (s ^ 3 * dd n m) := mul_le_mul_of_nonneg_left hlg (le_of_lt hn0)
        _ = s ^ 3 * ((n : ℝ) * dd n m) := by ring
        _ ≤ s ^ 3 * (3 * m) := mul_le_mul_of_nonneg_left hndd (by positivity)
        _ = 3 * m * s ^ 3 := by ring
    have hsq0 : 0 ≤ ((n : ℝ) * lgN n) ^ 2 := by positivity
    calc ((n : ℝ) * lgN n) ^ 2 * ((n : ℝ) * lgN n) ≤ ((n : ℝ) * lgN n) ^ 2 * (3 * m * s ^ 3) :=
          mul_le_mul_of_nonneg_left key hsq0
      _ = 3 * (m : ℝ) * ((n : ℝ) * lgN n) ^ 2 * s ^ 3 := by ring
  have hroot := le_rpow_third hX0 (by positivity) hX3
  rw [rpow_third_eq (by norm_num) (by positivity) (by positivity)] at hroot
  have h3 : (3 : ℝ) ^ ((1 : ℝ) / 3) ≤ 3 := by
    calc (3 : ℝ) ^ ((1 : ℝ) / 3) ≤ (3 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 3 := Real.rpow_one 3
  have hmain := nlgN_rpow_le n
  have hm13 : 0 ≤ (m : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have hx23 : 0 ≤ ((n : ℝ) * lgN n) ^ ((2 : ℝ) / 3) := by positivity
  unfold mainTerm
  calc X ≤ (3 : ℝ) ^ ((1 : ℝ) / 3) * (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * lgN n) ^ ((2 : ℝ) / 3) := hroot
    _ ≤ 3 * (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * lgN n) ^ ((2 : ℝ) / 3) := by gcongr
    _ ≤ 3 * (m : ℝ) ^ ((1 : ℝ) / 3) * (3 * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3)) := by
        gcongr
    _ ≤ 15 * ((m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3)) := by
        have : 0 ≤ (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3) := by
          have := log_n2_pos n; positivity
        nlinarith

theorem Lk_gen (n t : ℕ) (ht : 1 ≤ t) :
    ((lgN n / t : ℕ) + 1 : ℝ) * (Real.sqrt t + 1) ≤ 2 * (lgN n / Real.sqrt t) + 2 * Real.sqrt t := by
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  set s : ℝ := Real.sqrt t with hs
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr ht1
  have hss : s ^ 2 = t := by rw [hs]; exact Real.sq_sqrt (by linarith)
  have hdiv : ((lgN n / t : ℕ) : ℝ) ≤ (lgN n : ℝ) / t := Nat.cast_div_le
  have hl0 : (0 : ℝ) ≤ lgN n := Nat.cast_nonneg _
  rw [← hss] at hdiv
  have e1 : (lgN n : ℝ) / s ^ 2 * (s + 1) ≤ 2 * ((lgN n : ℝ) / s) := by
    have hs0 : 0 < s := by linarith
    have h2s : s + 1 ≤ 2 * s := by linarith
    have hq : (0 : ℝ) ≤ (lgN n : ℝ) / s ^ 2 := by positivity
    calc (lgN n : ℝ) / s ^ 2 * (s + 1) ≤ (lgN n : ℝ) / s ^ 2 * (2 * s) := mul_le_mul_of_nonneg_left h2s hq
      _ = 2 * ((lgN n : ℝ) / s) := by field_simp
  calc (((lgN n / t : ℕ) : ℝ) + 1) * (s + 1)
      = ((lgN n / t : ℕ) : ℝ) * (s + 1) + (s + 1) := by ring
    _ ≤ (lgN n : ℝ) / s ^ 2 * (s + 1) + (s + 1) := by gcongr
    _ ≤ 2 * ((lgN n : ℝ) / s) + 2 * s := by linarith

/-! ### Term menu for the floored parameters -/

theorem term_mtF (n m : ℕ) (hn : 1 ≤ n) : (m : ℝ) * tF n m ≤ 26 * Tchd n m := by
  have h1 := term_mt n m hn
  have hle : (tF n m : ℝ) ≤ 16 + tpar n m := by
    have : tF n m ≤ 16 + tpar n m := by unfold tF; omega
    exact_mod_cast this
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmT := m_le_Tchd n m
  calc (m : ℝ) * tF n m ≤ (m : ℝ) * (16 + tpar n m) := mul_le_mul_of_nonneg_left hle hm0
    _ = 16 * m + m * tpar n m := by ring
    _ ≤ 26 * Tchd n m := by linarith

theorem term_ntF (n m : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m + 1) : (n : ℝ) * tF n m ≤ 60 * Tchd n m := by
  have h1 := term_mtF n m hn
  have hnm' : (n : ℝ) ≤ m + 1 := by exact_mod_cast hnm
  have ht0 : (0 : ℝ) ≤ tF n m := Nat.cast_nonneg _
  have hle : (tF n m : ℝ) ≤ 16 + lgN n := by exact_mod_cast tF_le n m
  have hlog := lgN_le_log n
  have hlogle : Real.log ((n : ℝ) + 2) ≤ (n : ℝ) + 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (n : ℝ) + 2 by positivity); linarith
  have hnT := n_le_Tchd n m
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have htT : (tF n m : ℝ) ≤ 34 * Tchd n m := by nlinarith
  calc (n : ℝ) * tF n m ≤ ((m : ℝ) + 1) * tF n m := mul_le_mul_of_nonneg_right hnm' ht0
    _ = (m : ℝ) * tF n m + tF n m := by ring
    _ ≤ 60 * Tchd n m := by linarith

theorem term_nLkF (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ m + 1) :
    (n : ℝ) * LF n m * kF n m ≤ 160 * Tchd n m := by
  have ht1 : 1 ≤ tF n m := le_trans (by norm_num) (sixteen_le_tF n m)
  have ht1R : (1 : ℝ) ≤ tF n m := by exact_mod_cast ht1
  set s : ℝ := Real.sqrt (tF n m) with hs
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr ht1R
  have hst : s ≤ tF n m := by
    have hss : s ^ 2 = tF n m := by rw [hs]; exact Real.sq_sqrt (by linarith)
    nlinarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hL : (LF n m : ℝ) = ((lgN n / tF n m : ℕ) : ℝ) + 1 := by unfold LF; push_cast; ring
  have hk := kF_le_real n m
  have hLk := Lk_gen n (tF n m) ht1
  have hL0 : (0 : ℝ) ≤ LF n m := Nat.cast_nonneg _
  have hcore := core_gen n m (tF n m) hn hm hnm ht1 (tF_spec n m)
  have hnt := term_ntF n m hn hnm
  have hmainT := mainTerm_le_Tchd n m
  calc (n : ℝ) * LF n m * kF n m ≤ (n : ℝ) * LF n m * (s + 1) := by gcongr
    _ = (n : ℝ) * ((((lgN n / tF n m : ℕ) : ℝ) + 1) * (s + 1)) := by rw [hL]; ring
    _ ≤ (n : ℝ) * (2 * (lgN n / s) + 2 * s) := mul_le_mul_of_nonneg_left hLk hn0
    _ = 2 * ((n : ℝ) * lgN n / s) + 2 * ((n : ℝ) * s) := by ring
    _ ≤ 2 * (15 * mainTerm n m) + 2 * ((n : ℝ) * tF n m) := by gcongr
    _ ≤ 160 * Tchd n m := by have := Tchd_nonneg n m; linarith

theorem term_nLtkF (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ m + 1) :
    (n : ℝ) * LF n m * ((tF n m / kF n m : ℕ) + 1 : ℝ) ≤ 160 * Tchd n m := by
  -- `t / k ≤ √t ≤ k`, so `t / k + 1 ≤ k + 1`; bound via `n L (√t + 1)` as in `term_nLkF`
  have hk2 := two_le_kF n m
  have hq : ((tF n m / kF n m : ℕ) : ℝ) ≤ Real.sqrt (tF n m) := by
    have hdiv : ((tF n m / kF n m : ℕ) : ℝ) ≤ (tF n m : ℝ) / kF n m := Nat.cast_div_le
    have hsk := sqrt_tF_le_kF n m
    have hkpos : (0 : ℝ) < kF n m := by exact_mod_cast (show 0 < kF n m by omega)
    have hs0 : 0 ≤ Real.sqrt (tF n m) := Real.sqrt_nonneg _
    have hss : Real.sqrt (tF n m) ^ 2 = tF n m := Real.sq_sqrt (Nat.cast_nonneg _)
    calc ((tF n m / kF n m : ℕ) : ℝ) ≤ (tF n m : ℝ) / kF n m := hdiv
      _ ≤ Real.sqrt (tF n m) := by
          rw [div_le_iff₀ hkpos]; nlinarith
  have ht1 : 1 ≤ tF n m := le_trans (by norm_num) (sixteen_le_tF n m)
  have ht1R : (1 : ℝ) ≤ tF n m := by exact_mod_cast ht1
  set s : ℝ := Real.sqrt (tF n m) with hs
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr ht1R
  have hst : s ≤ tF n m := by
    have hss : s ^ 2 = tF n m := by rw [hs]; exact Real.sq_sqrt (by linarith)
    nlinarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hL : (LF n m : ℝ) = ((lgN n / tF n m : ℕ) : ℝ) + 1 := by unfold LF; push_cast; ring
  have hLk := Lk_gen n (tF n m) ht1
  have hL0 : (0 : ℝ) ≤ LF n m := Nat.cast_nonneg _
  have hcore := core_gen n m (tF n m) hn hm hnm ht1 (tF_spec n m)
  have hnt := term_ntF n m hn hnm
  have hmainT := mainTerm_le_Tchd n m
  calc (n : ℝ) * LF n m * (((tF n m / kF n m : ℕ) : ℝ) + 1) ≤ (n : ℝ) * LF n m * (s + 1) := by gcongr
    _ = (n : ℝ) * ((((lgN n / tF n m : ℕ) : ℝ) + 1) * (s + 1)) := by rw [hL]; ring
    _ ≤ (n : ℝ) * (2 * (lgN n / s) + 2 * s) := mul_le_mul_of_nonneg_left hLk hn0
    _ = 2 * ((n : ℝ) * lgN n / s) + 2 * ((n : ℝ) * s) := by ring
    _ ≤ 2 * (15 * mainTerm n m) + 2 * ((n : ℝ) * tF n m) := by gcongr
    _ ≤ 160 * Tchd n m := by have := Tchd_nonneg n m; linarith

theorem term_mlogtF (n m : ℕ) (hn : 1 ≤ n) : (m : ℝ) * Nat.log 2 (tF n m + 1) ≤ 26 * Tchd n m := by
  have h := natlog_succ_le (tF n m) (le_trans (by norm_num) (sixteen_le_tF n m))
  have hR : (Nat.log 2 (tF n m + 1) : ℝ) ≤ tF n m := by exact_mod_cast h
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  calc (m : ℝ) * Nat.log 2 (tF n m + 1) ≤ (m : ℝ) * tF n m := mul_le_mul_of_nonneg_left hR hm0
    _ ≤ 26 * Tchd n m := term_mtF n m hn

end Frontier.CostSkeleton
