import Frontier.GateC
import Frontier.AuditBridge

/-!
# Frontier.AuditGateC — L6 audit link for the C-HD target (owner: agent-09)

NON-GATE (pure analysis + bridging).  Proves that agent-10's frozen C-HD target
`CHDTarget GateCCalc.F` implies agent-09's INDEPENDENT strong-form gate `Audit.GateC` for the RAM
machine: `o(n lg n)` for ALL graphs with `m ≤ n f(n)`, `f(n) = max 1 (F n) ≥ sqlg n`
(audit finding F-v2-3).  Nothing here is proved about an algorithm.
-/

open Real Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace Frontier.AuditGateC

open Frontier Frontier.RAM Frontier.GateCCalc Frontier.GateCTarget Frontier.Audit

/-- Majorant for all `m ≤ 2 n x^{3/4}`. -/
def g2 (x : ℝ) : ℝ :=
  x⁻¹ + 2 * x ^ (-((1 : ℝ) / 4)) * (1 + Real.log 4 + Real.log x) + 2 * x ^ (-((1 : ℝ) / 12))

lemma tendsto_g2 : Tendsto g2 atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h2 : Tendsto (fun x : ℝ => x ^ (-((1 : ℝ) / 4))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have h3 : Tendsto (fun x : ℝ => x ^ (-((1 : ℝ) / 12))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hlo := isLittleO_log_rpow_rpow_atTop (1 : ℝ) (show (0 : ℝ) < 1 / 4 by norm_num)
  have h4 : Tendsto (fun x : ℝ => Real.log x ^ (1 : ℝ) / x ^ ((1 : ℝ) / 4)) atTop (𝓝 0) :=
    hlo.tendsto_div_nhds_zero
  have h4' : Tendsto (fun x : ℝ => x ^ (-((1 : ℝ) / 4)) * Real.log x) atTop (𝓝 0) := by
    refine h4.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.rpow_one, Real.rpow_neg (le_of_lt hx), div_eq_inv_mul]
  have h5 : Tendsto (fun x : ℝ => 2 * x ^ (-((1 : ℝ) / 4)) * (1 + Real.log 4 + Real.log x))
      atTop (𝓝 0) := by
    have := ((h2.mul_const (1 + Real.log 4)).add h4').const_mul 2
    rw [zero_mul, zero_add, mul_zero] at this
    refine this.congr' ?_
    filter_upwards with x
    ring
  have h6 : Tendsto (fun x : ℝ => 2 * x ^ (-((1 : ℝ) / 12))) atTop (𝓝 0) := by
    simpa using h3.const_mul 2
  have := (h1.add h5).add h6
  unfold g2
  simpa using this

/-- Pointwise majorization: for `n ≥ 1`, `x = L n`, and `m ≤ 2 n x^{3/4}`,
`Tchd n m ≤ n x g2(x)`. -/
lemma Tchd_le_g2 {n m : ℕ} (hn : 1 ≤ n)
    (hm : (m : ℝ) ≤ 2 * (n : ℝ) * (L n) ^ ((3 : ℝ) / 4)) :
    Tchd n m ≤ ((n : ℝ) * L n) * g2 (L n) := by
  have hL1 : 1 ≤ L n := L_ge_one hn
  have hL0 : 0 < L n := L_pos n
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set x := L n with hx
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have e1 : x ^ ((3 : ℝ) / 4) = x * x ^ (-((1 : ℝ) / 4)) := by
    rw [← Real.rpow_one_add' (le_of_lt hL0) (by norm_num)]; norm_num
  have e2 : x ^ ((11 : ℝ) / 12) = x * x ^ (-((1 : ℝ) / 12)) := by
    rw [← Real.rpow_one_add' (le_of_lt hL0) (by norm_num)]; norm_num
  have ex1 : x * x⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hL0)
  have hx34le : x ^ ((3 : ℝ) / 4) ≤ x := rpow34_le x hL1
  have hx34pos : 0 ≤ x ^ ((3 : ℝ) / 4) := by positivity
  -- term 3: log (m/(n+1) + 2) ≤ log 4 + log x
  have harg : (m : ℝ) / ((n : ℝ) + 1) + 2 ≤ 4 * x := by
    have h1 : (m : ℝ) / ((n : ℝ) + 1) ≤ 2 * x ^ ((3 : ℝ) / 4) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hargpos : 0 < (m : ℝ) / ((n : ℝ) + 1) + 2 := by
    have : 0 ≤ (m : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith
  have hlog : Real.log ((m : ℝ) / ((n : ℝ) + 1) + 2) ≤ Real.log 4 + Real.log x := by
    rw [← Real.log_mul (by norm_num) (ne_of_gt hL0)]
    exact Real.log_le_log hargpos harg
  have hlog0 : 0 ≤ Real.log ((m : ℝ) / ((n : ℝ) + 1) + 2) := by
    apply Real.log_nonneg; have : 0 ≤ (m : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith
  have t3 : (m : ℝ) * Real.log ((m : ℝ) / ((n : ℝ) + 1) + 2)
      ≤ 2 * (n : ℝ) * x ^ ((3 : ℝ) / 4) * (Real.log 4 + Real.log x) :=
    mul_le_mul hm hlog hlog0 (by positivity)
  -- term 4
  have t4 : (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * x) ^ ((2 : ℝ) / 3)
      ≤ 2 * ((n : ℝ) * x ^ ((11 : ℝ) / 12)) := by
    have hm13 : (m : ℝ) ^ ((1 : ℝ) / 3) ≤ (2 * (n : ℝ) * x ^ ((3 : ℝ) / 4)) ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow hm0 hm (by norm_num)
    have hsplit : (2 * (n : ℝ) * x ^ ((3 : ℝ) / 4)) ^ ((1 : ℝ) / 3)
        = (2 : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) ^ ((1 : ℝ) / 3) * x ^ ((1 : ℝ) / 4)) := by
      rw [Real.mul_rpow (by positivity) hx34pos, Real.mul_rpow (by norm_num) (le_of_lt hn0),
        ← Real.rpow_mul (le_of_lt hL0)]
      norm_num
      ring
    have h213 : (2 : ℝ) ^ ((1 : ℝ) / 3) ≤ 2 := by
      calc (2 : ℝ) ^ ((1 : ℝ) / 3) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    rw [Real.mul_rpow (le_of_lt hn0) (le_of_lt hL0)]
    have hA : 0 ≤ (n : ℝ) ^ ((2 : ℝ) / 3) * x ^ ((2 : ℝ) / 3) := by positivity
    calc (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) ^ ((2 : ℝ) / 3) * x ^ ((2 : ℝ) / 3))
        ≤ (2 * (n : ℝ) * x ^ ((3 : ℝ) / 4)) ^ ((1 : ℝ) / 3) *
            ((n : ℝ) ^ ((2 : ℝ) / 3) * x ^ ((2 : ℝ) / 3)) := mul_le_mul_of_nonneg_right hm13 hA
      _ = (2 : ℝ) ^ ((1 : ℝ) / 3) * (((n : ℝ) ^ ((1 : ℝ) / 3) * (n : ℝ) ^ ((2 : ℝ) / 3)) *
            (x ^ ((1 : ℝ) / 4) * x ^ ((2 : ℝ) / 3))) := by rw [hsplit]; ring
      _ = (2 : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * x ^ ((11 : ℝ) / 12)) := by
            rw [← Real.rpow_add hn0, ← Real.rpow_add hL0]; norm_num
      _ ≤ 2 * ((n : ℝ) * x ^ ((11 : ℝ) / 12)) :=
            mul_le_mul_of_nonneg_right h213 (by positivity)
  -- assemble
  unfold Tchd
  have hLdef : Real.log ((n : ℝ) + 2) = x := by rw [hx]; rfl
  rw [hLdef]
  unfold g2
  rw [e1] at hm t3
  rw [e2] at t4
  have expand : ((n : ℝ) * x) * (x⁻¹ + 2 * x ^ (-((1 : ℝ) / 4)) * (1 + Real.log 4 + Real.log x)
      + 2 * x ^ (-((1 : ℝ) / 12)))
      = (n : ℝ) * (x * x⁻¹) + 2 * (n : ℝ) * (x * x ^ (-((1 : ℝ) / 4)))
        + 2 * (n : ℝ) * (x * x ^ (-((1 : ℝ) / 4))) * (Real.log 4 + Real.log x)
        + 2 * ((n : ℝ) * (x * x ^ (-((1 : ℝ) / 12)))) := by ring
  rw [expand, ex1]
  linarith

/-- `F n ≤ 2 (L n)^{3/4}` for `n ≥ 1`. -/
lemma F_le {n : ℕ} (hn : 1 ≤ n) : (F n : ℝ) ≤ 2 * (L n) ^ ((3 : ℝ) / 4) := by
  set a := Nat.log 2 n with ha
  have hL0 : 0 < L n := L_pos n
  -- (F n)^4 ≤ a^3
  have h4 : (F n) ^ 4 ≤ a ^ 3 := by
    have h1 := Nat.sqrt_le' (Nat.sqrt (a ^ 3))
    have h2 := Nat.sqrt_le' (a ^ 3)
    unfold F
    rw [← ha]
    calc Nat.sqrt (Nat.sqrt (a ^ 3)) ^ 4 = (Nat.sqrt (Nat.sqrt (a ^ 3)) ^ 2) ^ 2 := by ring
      _ ≤ (Nat.sqrt (a ^ 3)) ^ 2 := Nat.pow_le_pow_left h1 2
      _ ≤ a ^ 3 := h2
  have h4R : ((F n : ℝ)) ^ 4 ≤ (a : ℝ) ^ 3 := by exact_mod_cast h4
  -- a ≤ 2 L n
  have haL : (a : ℝ) ≤ 2 * L n := by
    have hpow : 2 ^ a ≤ n := Nat.pow_log_le_self 2 (by omega)
    have hpowR : (2 : ℝ) ^ a ≤ (n : ℝ) + 2 := by
      have : ((2 ^ a : ℕ) : ℝ) ≤ n := by exact_mod_cast hpow
      push_cast at this; linarith
    have hlog : (a : ℝ) * Real.log 2 ≤ L n := by
      have := Real.log_le_log (by positivity) hpowR
      rw [Real.log_pow] at this
      unfold L; linarith
    have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    nlinarith
  -- F ≤ a^{3/4} ≤ (2L)^{3/4} ≤ 2 L^{3/4}
  have hF0 : (0 : ℝ) ≤ F n := Nat.cast_nonneg _
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hFa : (F n : ℝ) ≤ (a : ℝ) ^ ((3 : ℝ) / 4) := by
    have key : ((F n : ℝ) ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) ≤ ((a : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 4) := by
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      have e1 : (F n : ℝ) ^ (4 : ℝ) = (F n : ℝ) ^ (4 : ℕ) := by norm_cast
      have e2 : (a : ℝ) ^ (3 : ℝ) = (a : ℝ) ^ (3 : ℕ) := by norm_cast
      rw [e1, e2]; exact h4R
    rw [← Real.rpow_mul hF0, ← Real.rpow_mul ha0] at key
    norm_num at key
    exact key
  calc (F n : ℝ) ≤ (a : ℝ) ^ ((3 : ℝ) / 4) := hFa
    _ ≤ (2 * L n) ^ ((3 : ℝ) / 4) := Real.rpow_le_rpow ha0 haL (by norm_num)
    _ = (2 : ℝ) ^ ((3 : ℝ) / 4) * (L n) ^ ((3 : ℝ) / 4) := Real.mul_rpow (by norm_num) (le_of_lt hL0)
    _ ≤ 2 * (L n) ^ ((3 : ℝ) / 4) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        calc (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2

/-- The program threshold dominates `√log`: `sqlg n ≤ max 1 (F n)` for all `n`. -/
lemma sqlg_le_maxF (n : ℕ) : sqlg n ≤ max 1 (F n) := by
  unfold sqlg F
  apply max_le_max le_rfl
  set a := Nat.log 2 n
  -- Nat.sqrt a ≤ Nat.sqrt (Nat.sqrt (a^3))
  apply Nat.sqrt_le_sqrt
  apply Nat.le_sqrt.mpr
  rcases Nat.eq_zero_or_pos a with h | h
  · simp [h]
  · calc a * a ≤ a * a * a := Nat.le_mul_of_pos_right _ h
      _ = a ^ 3 := by ring

lemma F_pos {n : ℕ} (hn : 2 ≤ n) : 1 ≤ F n := by
  unfold F
  have ha : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by simpa using hn)
  apply Nat.le_sqrt.mpr
  apply Nat.le_sqrt.mpr
  simpa using Nat.one_le_pow 3 _ ha

/-- **L6 link (strong form).** agent-10's frozen C-HD target implies agent-09's independent
`Audit.GateC` for the RAM machine: exact, and `o(n lg n)` worst case on ALL graphs with
`m ≤ n · max 1 (F n)`, where `max 1 (F n) ≥ √lg n` (so the regime contains Dijkstra's winning window
`m ≈ n (lg n)^{3/4}`). -/
theorem chdTarget_imp_auditGateC : CHDTarget F → Frontier.Audit.GateC ramModel := by
  rintro ⟨P, hP, C, hC⟩
  refine ⟨P, solves_of_exact hP, fun n => max 1 (F n), ⟨1, one_pos, fun n => by simpa using sqlg_le_maxF n⟩, ?_⟩
  intro K
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  -- eventually K C' g2(L n) ≤ 1
  have hg : Tendsto (fun n : ℕ => (K : ℝ) * C' * g2 (L n)) atTop (𝓝 0) := by
    have := (tendsto_g2.comp tendsto_L).const_mul ((K : ℝ) * C')
    simpa using this
  have hev : ∀ᶠ n : ℕ in atTop, (K : ℝ) * C' * g2 (L n) ≤ 1 :=
    hg.eventually (ge_mem_nhds (by norm_num))
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hev
  refine ⟨max N0 32, fun G s hN hm => ?_⟩
  have hn32 : 32 ≤ G.n := le_trans (le_max_right _ _) hN
  have hnN0 : N0 ≤ G.n := le_trans (le_max_left _ _) hN
  have hn1 : 1 ≤ G.n := by omega
  have hF1 : 1 ≤ F G.n := F_pos (by omega)
  have hmF : G.m ≤ G.n * F G.n := by simpa [max_eq_right hF1] using hm
  -- the unique run costs at most C * Tchd
  have hrun := hC (toGraph G) s
  have hT : Tdisp F G.n G.m = Tchd G.n G.m := by simp [Tdisp, hmF]
  have ht : (ramModel.time P G s : ℝ) ≤ C * Tchd G.n G.m := by
    have := time_le_of_runsWithin hrun
    simpa [hT] using this
  have hTnn : 0 ≤ Tchd G.n G.m := Tchd_nonneg _ _
  have ht' : (ramModel.time P G s : ℝ) ≤ C' * Tchd G.n G.m :=
    ht.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hTnn)
  -- majorize Tchd
  have hmR : (G.m : ℝ) ≤ 2 * (G.n : ℝ) * (L G.n) ^ ((3 : ℝ) / 4) := by
    have h1 : (G.m : ℝ) ≤ (G.n : ℝ) * F G.n := by exact_mod_cast hmF
    have h2 := F_le hn1 (n := G.n)
    have hn0 : (0 : ℝ) ≤ G.n := Nat.cast_nonneg _
    nlinarith
  have hmaj := Tchd_le_g2 hn1 hmR
  have hK := hN0 G.n hnN0
  have hLnat : L G.n ≤ (Nat.log 2 G.n : ℝ) := log_le_natLog hn32
  have hlg : (Nat.log 2 G.n : ℝ) ≤ (lg G.n : ℝ) := by exact_mod_cast le_max_right 1 (Nat.log 2 G.n)
  have hnL : 0 ≤ (G.n : ℝ) * L G.n := mul_nonneg (Nat.cast_nonneg _) (le_of_lt (L_pos _))
  have hg2 : 0 ≤ g2 (L G.n) := by
    unfold g2
    have hx : 0 < L G.n := L_pos _
    have hlogx : 0 ≤ Real.log (L G.n) := Real.log_nonneg (L_ge_one hn1)
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  have key : (K : ℝ) * (ramModel.time P G s : ℝ) ≤ (G.n : ℝ) * (lg G.n : ℝ) := by
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    calc (K : ℝ) * (ramModel.time P G s : ℝ) ≤ (K : ℝ) * (C' * Tchd G.n G.m) :=
          mul_le_mul_of_nonneg_left ht' hK0
      _ ≤ (K : ℝ) * (C' * (((G.n : ℝ) * L G.n) * g2 (L G.n))) := by
          apply mul_le_mul_of_nonneg_left _ hK0
          exact mul_le_mul_of_nonneg_left hmaj hC'0
      _ = ((K : ℝ) * C' * g2 (L G.n)) * ((G.n : ℝ) * L G.n) := by ring
      _ ≤ 1 * ((G.n : ℝ) * L G.n) := mul_le_mul_of_nonneg_right hK hnL
      _ = (G.n : ℝ) * L G.n := one_mul _
      _ ≤ (G.n : ℝ) * (lg G.n : ℝ) := by
          apply mul_le_mul_of_nonneg_left (hLnat.trans hlg) (Nat.cast_nonneg _)
  exact_mod_cast key

end Frontier.AuditGateC

#print axioms Frontier.AuditGateC.chdTarget_imp_auditGateC
