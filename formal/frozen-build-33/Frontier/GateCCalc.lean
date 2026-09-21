import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Frontier.GateCCalc — parameter calculus for the Gate-C target bound (owner: agent-10)

NON-GATE: pure real analysis. It proves that the explicit C-HD running-time SHAPE is o(n log n)
along a density profile inside the Gate-C window. It says nothing about any algorithm.

`Tchd n m = n + m + m * log (m/(n+1) + 2) + m^(1/3) * (n log(n+2))^(2/3)`.
Along the density profile `μ n = n * ⌊log(n+2)^(3/4)⌋₊` it is `o(n log n)`.
-/

open Real Filter Topology

noncomputable section

namespace Frontier.GateCCalc

/-- The explicit running-time shape of the C-HD candidate. -/
def Tchd (n m : ℕ) : ℝ :=
  (n : ℝ) + m + m * Real.log ((m : ℝ) / ((n : ℝ) + 1) + 2)
    + (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3)

/-- `L n = log (n + 2)`. -/
def L (n : ℕ) : ℝ := Real.log ((n : ℝ) + 2)

/-- The density multiplier `s n = ⌊L n ^ (3/4)⌋₊`. -/
def s (n : ℕ) : ℕ := ⌊(L n) ^ ((3 : ℝ) / 4)⌋₊

/-- The density profile `μ n = n * s n`. -/
def μ (n : ℕ) : ℕ := n * s n

lemma L_ge_one {n : ℕ} (hn : 1 ≤ n) : 1 ≤ L n := by
  unfold L
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : Real.exp 1 ≤ (n : ℝ) + 2 := by
    have := Real.exp_one_lt_d9
    linarith
  calc (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
    _ ≤ Real.log ((n : ℝ) + 2) := Real.log_le_log (Real.exp_pos 1) hexp

lemma L_pos (n : ℕ) : 0 < L n := by
  unfold L
  apply Real.log_pos
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

lemma tendsto_L : Tendsto L atTop atTop := by
  unfold L
  have h : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  exact Real.tendsto_log_atTop.comp h

lemma s_le (n : ℕ) : (s n : ℝ) ≤ (L n) ^ ((3 : ℝ) / 4) :=
  Nat.floor_le (Real.rpow_nonneg (le_of_lt (L_pos n)) _)

lemma rpow34_le (x : ℝ) (hx : 1 ≤ x) : x ^ ((3 : ℝ) / 4) ≤ x := by
  calc x ^ ((3 : ℝ) / 4) ≤ x ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    _ = x := Real.rpow_one x

lemma s_le_L {n : ℕ} (hn : 1 ≤ n) : (s n : ℝ) ≤ L n :=
  le_trans (s_le n) (rpow34_le _ (L_ge_one hn))


/-- The majorant `g x = x⁻¹ + x^(-1/4) (1 + log 3 + log x) + x^(-1/12)`. -/
def g (x : ℝ) : ℝ :=
  x⁻¹ + x ^ (-((1 : ℝ) / 4)) * (1 + Real.log 3 + Real.log x) + x ^ (-((1 : ℝ) / 12))

lemma tendsto_g : Tendsto g atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h2 : Tendsto (fun x : ℝ => x ^ (-((1 : ℝ) / 4))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have h3 : Tendsto (fun x : ℝ => x ^ (-((1 : ℝ) / 12))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  -- log x / x^(1/4) → 0
  have hlo := isLittleO_log_rpow_rpow_atTop (1 : ℝ) (show (0 : ℝ) < 1 / 4 by norm_num)
  have h4 : Tendsto (fun x : ℝ => Real.log x ^ (1 : ℝ) / x ^ ((1 : ℝ) / 4)) atTop (𝓝 0) :=
    hlo.tendsto_div_nhds_zero
  have h4' : Tendsto (fun x : ℝ => x ^ (-((1 : ℝ) / 4)) * Real.log x) atTop (𝓝 0) := by
    refine h4.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.rpow_one, Real.rpow_neg (le_of_lt hx), div_eq_inv_mul]
  have h5 : Tendsto (fun x : ℝ => x ^ (-((1 : ℝ) / 4)) * (1 + Real.log 3 + Real.log x)) atTop (𝓝 0) := by
    have := (h2.mul_const (1 + Real.log 3)).add h4'
    simpa [mul_add] using this
  have := (h1.add h5).add h3
  unfold g
  simpa using this

/-- Main pointwise majorization, for `n ≥ 1`. -/
lemma Tchd_mu_le {n : ℕ} (hn : 1 ≤ n) :
    Tchd n (μ n) ≤ ((n : ℝ) * L n) * g (L n) := by
  have hL1 : 1 ≤ L n := L_ge_one hn
  have hL0 : 0 < L n := L_pos n
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set x := L n with hx
  have hsx : (s n : ℝ) ≤ x ^ ((3 : ℝ) / 4) := s_le n
  have hs0 : (0 : ℝ) ≤ s n := Nat.cast_nonneg _
  have hmu : ((μ n : ℕ) : ℝ) = (n : ℝ) * s n := by simp [μ]
  -- useful rpow identities
  have e1 : x ^ ((3 : ℝ) / 4) = x * x ^ (-((1 : ℝ) / 4)) := by
    rw [← Real.rpow_one_add' (le_of_lt hL0) (by norm_num)]; norm_num
  have e2 : x ^ ((11 : ℝ) / 12) = x * x ^ (-((1 : ℝ) / 12)) := by
    rw [← Real.rpow_one_add' (le_of_lt hL0) (by norm_num)]; norm_num
  have ex1 : x * x⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hL0)
  -- term 2: m ≤ n x^(3/4)
  have t2 : (n : ℝ) * s n ≤ (n : ℝ) * x ^ ((3 : ℝ) / 4) :=
    mul_le_mul_of_nonneg_left hsx (le_of_lt hn0)
  -- term 3: log (m/(n+1) + 2) ≤ log 3 + log x
  have harg : (n : ℝ) * s n / ((n : ℝ) + 1) + 2 ≤ 3 * x := by
    have h1 : (n : ℝ) * s n / ((n : ℝ) + 1) ≤ s n := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have h2 : (s n : ℝ) ≤ x := s_le_L hn
    linarith
  have hargpos : 0 < (n : ℝ) * s n / ((n : ℝ) + 1) + 2 := by
    have : 0 ≤ (n : ℝ) * s n / ((n : ℝ) + 1) := by positivity
    linarith
  have hlog : Real.log ((n : ℝ) * s n / ((n : ℝ) + 1) + 2) ≤ Real.log 3 + Real.log x := by
    rw [← Real.log_mul (by norm_num) (ne_of_gt hL0)]
    exact Real.log_le_log hargpos harg
  have hlog0 : 0 ≤ Real.log ((n : ℝ) * s n / ((n : ℝ) + 1) + 2) := by
    apply Real.log_nonneg; have : 0 ≤ (n : ℝ) * s n / ((n : ℝ) + 1) := by positivity
    linarith
  have t3 : (n : ℝ) * s n * Real.log ((n : ℝ) * s n / ((n : ℝ) + 1) + 2)
      ≤ (n : ℝ) * x ^ ((3 : ℝ) / 4) * (Real.log 3 + Real.log x) :=
    mul_le_mul t2 hlog hlog0 (by positivity)
  -- term 4: (n s)^(1/3) (n x)^(2/3) ≤ n x^(11/12)
  have t4 : ((n : ℝ) * s n) ^ ((1 : ℝ) / 3) * ((n : ℝ) * x) ^ ((2 : ℝ) / 3)
      ≤ (n : ℝ) * x ^ ((11 : ℝ) / 12) := by
    have hs13 : (s n : ℝ) ^ ((1 : ℝ) / 3) ≤ x ^ ((1 : ℝ) / 4) := by
      calc (s n : ℝ) ^ ((1 : ℝ) / 3) ≤ (x ^ ((3 : ℝ) / 4)) ^ ((1 : ℝ) / 3) :=
            Real.rpow_le_rpow hs0 hsx (by norm_num)
        _ = x ^ ((1 : ℝ) / 4) := by
            rw [← Real.rpow_mul (le_of_lt hL0)]; norm_num
    rw [Real.mul_rpow (le_of_lt hn0) hs0, Real.mul_rpow (le_of_lt hn0) (le_of_lt hL0)]
    have hn13 : (0 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 3) := by positivity
    have hn23 : (0 : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 3) := by positivity
    have hx23 : (0 : ℝ) ≤ x ^ ((2 : ℝ) / 3) := by positivity
    calc (n : ℝ) ^ ((1 : ℝ) / 3) * (s n : ℝ) ^ ((1 : ℝ) / 3) *
          ((n : ℝ) ^ ((2 : ℝ) / 3) * x ^ ((2 : ℝ) / 3))
        ≤ (n : ℝ) ^ ((1 : ℝ) / 3) * x ^ ((1 : ℝ) / 4) *
          ((n : ℝ) ^ ((2 : ℝ) / 3) * x ^ ((2 : ℝ) / 3)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left hs13 hn13
      _ = ((n : ℝ) ^ ((1 : ℝ) / 3) * (n : ℝ) ^ ((2 : ℝ) / 3)) *
          (x ^ ((1 : ℝ) / 4) * x ^ ((2 : ℝ) / 3)) := by ring
      _ = (n : ℝ) * x ^ ((11 : ℝ) / 12) := by
            rw [← Real.rpow_add hn0, ← Real.rpow_add hL0]; norm_num
  -- assemble
  unfold Tchd
  rw [hmu]
  have hLdef : Real.log ((n : ℝ) + 2) = x := by rw [hx]; rfl
  rw [hLdef]
  unfold g
  rw [e1] at t2 t3
  rw [e2] at t4
  have expand : ((n : ℝ) * x) * (x⁻¹ + x ^ (-((1 : ℝ) / 4)) * (1 + Real.log 3 + Real.log x)
      + x ^ (-((1 : ℝ) / 12)))
      = (n : ℝ) * (x * x⁻¹) + (n : ℝ) * (x * x ^ (-((1 : ℝ) / 4)))
        + (n : ℝ) * (x * x ^ (-((1 : ℝ) / 4))) * (Real.log 3 + Real.log x)
        + (n : ℝ) * (x * x ^ (-((1 : ℝ) / 12))) := by ring
  rw [expand, ex1]
  linarith


lemma Tchd_nonneg (n m : ℕ) : 0 ≤ Tchd n m := by
  unfold Tchd
  have h1 : 0 ≤ Real.log ((m : ℝ) / ((n : ℝ) + 1) + 2) := by
    apply Real.log_nonneg
    have : 0 ≤ (m : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith
  have h2 : 0 ≤ (n : ℝ) * Real.log ((n : ℝ) + 2) := by
    have : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith)
    positivity
  positivity

/-- `Tchd` along the profile is `o(n log (n+2))`. -/
lemma tendsto_Tchd_mu :
    Tendsto (fun n : ℕ => Tchd n (μ n) / ((n : ℝ) * Real.log ((n : ℝ) + 2))) atTop (𝓝 0) := by
  have hg : Tendsto (fun n : ℕ => g (L n)) atTop (𝓝 0) := tendsto_g.comp tendsto_L
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    apply div_nonneg (Tchd_nonneg _ _)
    have : 0 < L n := L_pos n
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    exact le_of_lt (mul_pos hn0 this)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hpos : 0 < (n : ℝ) * L n := mul_pos (by exact_mod_cast hn) (L_pos n)
    have hLd : Real.log ((n : ℝ) + 2) = L n := rfl
    rw [hLd, div_le_iff₀ hpos]
    have := Tchd_mu_le hn
    linarith [this]

/-- Eventually `L n ≥ 16`. -/
lemma eventually_L_ge : ∀ᶠ n : ℕ in atTop, (16 : ℝ) ≤ L n :=
  tendsto_L.eventually_ge_atTop 16

lemma sqrt_le_s {n : ℕ} (h16 : (16 : ℝ) ≤ L n) : Real.sqrt (L n) ≤ (s n : ℝ) := by
  have hL0 : 0 < L n := L_pos n
  set x := L n with hx
  -- x^(1/4) ≥ 2
  have h14 : (2 : ℝ) ≤ x ^ ((1 : ℝ) / 4) := by
    have : (16 : ℝ) ^ ((1 : ℝ) / 4) = 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [← this]
    exact Real.rpow_le_rpow (by norm_num) h16 (by norm_num)
  have hsq : Real.sqrt x = x ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow x
  have h12 : (4 : ℝ) ≤ x ^ ((1 : ℝ) / 2) := by
    have : (16 : ℝ) ^ ((1 : ℝ) / 2) = 4 := by
      rw [show (16 : ℝ) = 4 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [← this]
    exact Real.rpow_le_rpow (by norm_num) h16 (by norm_num)
  have h34 : x ^ ((3 : ℝ) / 4) = x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_add hL0]; norm_num
  have hfl : x ^ ((3 : ℝ) / 4) < (s n : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [hsq]
  nlinarith

/-- The profile `μ` lies in the Gate-C window eventually. -/
lemma mu_window : ∀ᶠ n : ℕ in atTop,
    (n : ℝ) * Real.sqrt (Real.log ((n : ℝ) + 2)) ≤ (μ n : ℝ) ∧
    (μ n : ℝ) ≤ (n : ℝ) * Real.log ((n : ℝ) + 2) := by
  filter_upwards [eventually_L_ge, eventually_ge_atTop 1] with n h16 hn
  have hmu : ((μ n : ℕ) : ℝ) = (n : ℝ) * s n := by simp [μ]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨?_, ?_⟩
  · rw [hmu]
    exact mul_le_mul_of_nonneg_left (sqrt_le_s h16) hn0
  · rw [hmu]
    exact mul_le_mul_of_nonneg_left (s_le_L hn) hn0


/-! ### An integer-computable density threshold -/

/-- The program-side threshold `F n = ⌊(log₂ n)^(3/4)⌋`, computed as `Nat.sqrt (Nat.sqrt (a^3))`,
`a = Nat.log 2 n` (O(log n) word operations). -/
def F (n : ℕ) : ℕ := Nat.sqrt (Nat.sqrt ((Nat.log 2 n) ^ 3))

lemma le_sqrt_sqrt_of_real {r a : ℕ} (h : (r : ℝ) ≤ (a : ℝ) ^ ((3 : ℝ) / 4)) :
    r ≤ Nat.sqrt (Nat.sqrt (a ^ 3)) := by
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have h4 : (r : ℝ) ^ 4 ≤ (a : ℝ) ^ 3 := by
    have h1 := pow_le_pow_left₀ hr0 h 4
    have h2 : ((a : ℝ) ^ ((3 : ℝ) / 4)) ^ 4 = (a : ℝ) ^ 3 := by
      rw [← Real.rpow_natCast ((a : ℝ) ^ ((3 : ℝ) / 4)) 4, ← Real.rpow_mul ha0]
      norm_num
    linarith [h1, h2]
  have h4' : r ^ 4 ≤ a ^ 3 := by exact_mod_cast h4
  apply Nat.le_sqrt.mpr
  apply Nat.le_sqrt.mpr
  calc r * r * (r * r) = r ^ 4 := by ring
    _ ≤ a ^ 3 := h4'

lemma log_le_natLog {n : ℕ} (hn : 32 ≤ n) : Real.log ((n : ℝ) + 2) ≤ (Nat.log 2 n : ℝ) := by
  set a := Nat.log 2 n with ha
  have ha5 : 5 ≤ a := by
    have h32 : Nat.log 2 32 = 5 := by
      rw [show (32 : ℕ) = 2 ^ 5 by norm_num, Nat.log_pow (by norm_num)]
    calc 5 = Nat.log 2 32 := h32.symm
      _ ≤ a := Nat.log_mono_right hn
  have hlt : n < 2 ^ (a + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hnat : n + 2 ≤ 2 ^ (a + 2) := by
    have h1 : 2 ≤ 2 ^ (a + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (a + 2) = 2 ^ (a + 1) + 2 ^ (a + 1) := by rw [pow_succ]; ring
    omega
  have h2 : (n : ℝ) + 2 ≤ (2 : ℝ) ^ (a + 2) := by exact_mod_cast hnat
  have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hlog : Real.log ((n : ℝ) + 2) ≤ ((a : ℝ) + 2) * Real.log 2 := by
    calc Real.log ((n : ℝ) + 2) ≤ Real.log ((2 : ℝ) ^ (a + 2)) := Real.log_le_log hpos h2
      _ = ((a : ℝ) + 2) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
  have hl2 := Real.log_two_lt_d9
  have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha5' : (5 : ℝ) ≤ a := by exact_mod_cast ha5
  nlinarith

/-- The integer threshold eventually dominates the profile multiplier. -/
lemma F_dominates : ∀ᶠ n : ℕ in atTop, s n ≤ F n := by
  filter_upwards [eventually_ge_atTop 32] with n hn
  unfold s F
  apply le_sqrt_sqrt_of_real
  calc (⌊L n ^ ((3 : ℝ) / 4)⌋₊ : ℝ) ≤ L n ^ ((3 : ℝ) / 4) :=
        Nat.floor_le (Real.rpow_nonneg (le_of_lt (L_pos n)) _)
    _ ≤ (Nat.log 2 n : ℝ) ^ ((3 : ℝ) / 4) :=
        Real.rpow_le_rpow (le_of_lt (L_pos n)) (log_le_natLog hn) (by norm_num)

end Frontier.GateCCalc
