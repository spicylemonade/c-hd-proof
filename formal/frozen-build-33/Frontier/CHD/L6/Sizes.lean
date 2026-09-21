import Frontier.CHD.L6.Final
import Frontier.CostSkeleton

/-!
# L6 size bounds (agent-10, scratch): `gN ≤ 2 cn`, `gM ≤ 2 m`, `δ ≤ 5 dd(cn, m)`
-/

open scoped NNReal

namespace Frontier.CHD.L6

open Frontier Finset

theorem sum_cntk (s : ℕ → ℕ) (m : ℕ) : ∀ k, ∑ v ∈ range k, cntk s m v = pfx s m k := by
  intro k
  induction k with
  | zero => simp [pfx]
  | succ k ih => rw [sum_range_succ, ih, pfx_succ]

theorem pfx_le_m (s : ℕ → ℕ) (m k : ℕ) : pfx s m k ≤ m := by
  rw [pfx_eq_count]
  calc ((List.range m).filter _).length ≤ (List.range m).length := List.length_filter_le _ _
    _ = m := List.length_range

namespace L6In

variable (I : L6In)

theorem sum_deg_le : ∑ v ∈ range I.n, I.deg v ≤ I.m := by
  calc ∑ v ∈ range I.n, I.deg v ≤ ∑ v ∈ range I.n, cntk I.src I.m v :=
        sum_le_sum fun v _ => by rw [← I.grp_length]; exact I.deg_le v
    _ = pfx I.src I.m I.n := sum_cntk _ _ _
    _ ≤ I.m := pfx_le_m _ _ _

theorem keep_01 (v : ℕ) : I.keep v = 0 ∨ I.keep v = 1 := by
  unfold keep keepF
  by_cases hv : v = I.s
  · subst hv; simp
  · rw [Function.update_of_ne hv]; unfold keepArr; split_ifs <;> simp

/-- The kept vertices. -/
noncomputable def keptSet : Finset ℕ := (range I.n).filter (fun v => I.keep v ≠ 0)

theorem keptSet_card_le_n : I.keptSet.card ≤ I.n := by
  unfold keptSet; exact le_trans (card_filter_le _ _) (by simp)

/-- At most `m + 1` kept vertices: `s` and heads of non-loop edges. -/
theorem keptSet_card_le_m (hsn : I.s < I.n) : I.keptSet.card ≤ I.m + 1 := by
  have hsub : I.keptSet ⊆ insert I.s ((range I.m).image I.dst) := by
    intro v hv
    simp only [keptSet, mem_filter, mem_range] at hv
    have : I.keep v = 1 := by
      rcases I.keep_01 v with h | h
      · exact absurd h hv.2
      · exact h
    rcases (keepF_eq_one I.src I.dst I.m I.s v).mp this with h | ⟨e, he, hd, -⟩
    · rw [h]; exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_image.mpr ⟨e, mem_range.mpr he, hd⟩)
  calc I.keptSet.card ≤ (insert I.s ((range I.m).image I.dst)).card := card_le_card hsub
    _ ≤ ((range I.m).image I.dst).card + 1 := card_insert_le _ _
    _ ≤ (range I.m).card + 1 := by have := card_image_le (s := range I.m) (f := I.dst); omega
    _ = I.m + 1 := by simp

theorem cc_le_div (u : ℕ) (hδ : 3 ≤ I.δ) :
    I.cc u ≤ (if I.keep u = 0 then 0 else 1) + I.deg u / (I.δ - 1) := by
  unfold cc; split_ifs with h
  · exact Nat.zero_le _
  · refine max_le (by have := Nat.zero_le (I.deg u / (I.δ - 1)); omega) ?_
    have hd : 0 < I.δ - 1 := by omega
    have h1 : (I.deg u + (I.δ - 2)) / (I.δ - 1) ≤ I.deg u / (I.δ - 1) + 1 := by
      rw [Nat.div_le_iff_le_mul_add_pred hd]
      have := Nat.lt_mul_div_succ (I.deg u) hd
      omega
    omega

theorem off_n_le (hδ : 3 ≤ I.δ) :
    I.off I.n ≤ I.keptSet.card + I.m / (I.δ - 1) := by
  have h1 : I.off I.n ≤ ∑ v ∈ range I.n, ((if I.keep v = 0 then 0 else 1) + I.deg v / (I.δ - 1)) :=
    sum_le_sum fun v _ => I.cc_le_div v hδ
  rw [sum_add_distrib] at h1
  have h2 : ∑ v ∈ range I.n, (if I.keep v = 0 then 0 else 1) = I.keptSet.card := by
    rw [keptSet, card_filter]; apply sum_congr rfl; intro v _; split_ifs <;> simp_all
  have h3 : ∑ v ∈ range I.n, I.deg v / (I.δ - 1) ≤ (∑ v ∈ range I.n, I.deg v) / (I.δ - 1) := by
    rw [Nat.le_div_iff_mul_le (by omega), sum_mul]
    exact sum_le_sum fun v _ => Nat.div_mul_le_self _ _
  have h4 : (∑ v ∈ range I.n, I.deg v) / (I.δ - 1) ≤ I.m / (I.δ - 1) :=
    Nat.div_le_div_right I.sum_deg_le
  omega

/-- `m ≤ n (δ - 1)` (the choice `δ = max 3 ⌈2m/n⌉`). -/
theorem m_le_n_delta (hn1 : 1 ≤ I.n) : I.m ≤ I.n * (I.δ - 1) := by
  simp only [δ, deltaF]
  by_cases hmn : I.m < I.n
  · have : 2 ≤ max 3 ((I.m + I.m + (I.n - 1)) / I.n) - 1 := by omega
    nlinarith
  · have h1 : I.m + I.m ≤ (I.m + I.m + (I.n - 1)) / I.n * I.n := by
      have := Nat.lt_div_mul_add (a := I.m + I.m + (I.n - 1)) (show 0 < I.n by omega)
      omega
    have h2 : (I.m + I.m + (I.n - 1)) / I.n ≤ max 3 ((I.m + I.m + (I.n - 1)) / I.n) := le_max_right _ _
    have h3 : I.n * ((I.m + I.m + (I.n - 1)) / I.n) ≤ I.n * max 3 ((I.m + I.m + (I.n - 1)) / I.n) :=
      Nat.mul_le_mul_left _ h2
    have h4 : I.n * (max 3 ((I.m + I.m + (I.n - 1)) / I.n) - 1) =
        I.n * max 3 ((I.m + I.m + (I.n - 1)) / I.n) - I.n := by
      rw [Nat.mul_sub_one]
    have h5 : I.n * ((I.m + I.m + (I.n - 1)) / I.n) = (I.m + I.m + (I.n - 1)) / I.n * I.n := by ring
    omega

/-- **Vertex bound**: `gN ≤ 2 · min(n, m+1)`. -/
theorem off_n_le_cn (hδ : 3 ≤ I.δ) (hsn : I.s < I.n) : I.off I.n ≤ 2 * min I.n (I.m + 1) := by
  have h1 := I.off_n_le hδ
  have hk1 := I.keptSet_card_le_n
  have hk2 := I.keptSet_card_le_m hsn
  have hd : 2 ≤ I.δ - 1 := by omega
  have hq1 : I.m / (I.δ - 1) ≤ I.n := by
    rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
    have := I.m_le_n_delta (by omega); nlinarith
  have hq2 : I.m / (I.δ - 1) ≤ I.m + 1 := le_trans (Nat.div_le_self _ _) (by omega)
  have : I.keptSet.card ≤ min I.n (I.m + 1) := le_min hk1 hk2
  have : I.m / (I.δ - 1) ≤ min I.n (I.m + 1) := le_min hq1 hq2
  omega

theorem ns_le_div (u : ℕ) (hδ : 3 ≤ I.δ) : I.ns u ≤ I.deg u + I.deg u / (I.δ - 1) := by
  unfold ns; split_ifs with h
  · exact Nat.zero_le _
  · have := I.cc_le_div u hδ; rw [if_neg h] at this
    generalize I.deg u / (I.δ - 1) = D at this ⊢
    omega

/-- **Edge bound**: `gM ≤ 2 m`. -/
theorem sl_n_le (hδ : 3 ≤ I.δ) : I.sl I.n ≤ 2 * I.m := by
  have h1 : I.sl I.n ≤ ∑ v ∈ range I.n, (I.deg v + I.deg v / (I.δ - 1)) :=
    sum_le_sum fun v _ => I.ns_le_div v hδ
  rw [sum_add_distrib] at h1
  have h3 : ∑ v ∈ range I.n, I.deg v / (I.δ - 1) ≤ ∑ v ∈ range I.n, I.deg v :=
    sum_le_sum fun v _ => Nat.div_le_self _ _
  have := I.sum_deg_le
  omega

/-- **Degree bound**: `δ ≤ 5 · dd(cn, m)` with `cn = min(n, m+1)`. -/
theorem delta_le_dd (hn1 : 1 ≤ I.n) : I.δ ≤ 5 * CostSkeleton.dd (min I.n (I.m + 1)) I.m := by
  simp only [δ, deltaF, CostSkeleton.dd]
  have hcn : 1 ≤ min I.n (I.m + 1) := le_min hn1 (by omega)
  have hle : I.m / I.n ≤ I.m / min I.n (I.m + 1) := Nat.div_le_div_left (min_le_left _ _) hcn
  generalize min I.n (I.m + 1) = c at hcn hle ⊢
  refine max_le (by have := Nat.zero_le (I.m / c); omega) ?_
  have h1 : (I.m + I.m + (I.n - 1)) / I.n ≤ 2 * (I.m / I.n) + 2 := by
    rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
    have := Nat.lt_mul_div_succ I.m (show 0 < I.n by omega)
    have h2 : I.n * (2 * (I.m / I.n) + 2) = 2 * (I.n * (I.m / I.n + 1)) := by ring
    omega
  omega

end L6In

end Frontier.CHD.L6
