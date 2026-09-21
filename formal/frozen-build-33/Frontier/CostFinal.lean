import Frontier.CostAggregate
import Frontier.CostSkeleton

/-!
# Frontier.CostFinal — C-HD cost composition skeleton, part 4: the bridge to `Tchd` (owner: agent-06)

**NON-GATE.**  Combines the abstract aggregation `CallCounters.total_cost_le` (part 3) with the parameter term
menu (part 1): if the call counters of an execution are `Valid` for the C-HD parameters `t = tF n m`,
`k = kF n m` (decision D2), with `O(n)` vertices, `O(m)` edges, depth `≤ 2 LF - 1` and merge total `O(n LF + m)`,
then the total charged cost is at most `K · Tchd n m` with an explicit `K`.  What remains for the full cost
theorem is to construct the `CallCounters` of the real execution and prove `Valid` (L2–L4 + Layer B).
-/

namespace Frontier.CostFinal

open Finset Frontier.CostCharging Frontier.CostAggregate Frontier.CostSkeleton Frontier.GateCCalc

variable {ι V E α : Type*} [Fintype ι] [Fintype V] [Fintype E] [DecidableEq ι] [DecidableEq V]
  [DecidableEq E] [LinearOrder α]

/-- **Bridge, recursive calls.**  Valid counters for the C-HD parameters give total cost of the non-base
calls `≤ 5000 · c · a · Tchd n m` (parameters `t = tF`, `k = kF` of decision D2). -/
theorem nonbase_le_Tchd (C : CallCounters ι V E α) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ m + 1)
    {c Lmax M0 a : ℕ} {inE : V → Finset E} {wit : ι → V → E} {src : V}
    (h : C.Valid (tF n m) (kF n m) c Lmax M0 inE wit src)
    (hV : Fintype.card V ≤ a * n) (hE : Fintype.card E ≤ a * m) (hL : Lmax + 1 ≤ 2 * LF n m)
    (hM0 : M0 ≤ a * (n * LF n m + m)) :
    ((∑ X ∈ univ.filter (fun X => C.base X = false), C.cost X : ℕ) : ℝ) ≤ 5000 * c * a * Tchd n m := by
  set t := tF n m with ht
  set k := kF n m with hk
  set L := LF n m with hLdef
  have hk2 : 2 ≤ k := h.two_le_k
  have hagg := CallCounters.total_cost_le h
  set N := (Lmax + 1) * Fintype.card V with hN
  -- real versions of the basic bounds
  have hNR : (N : ℝ) ≤ 2 * a * ((n : ℝ) * L) := by
    have : N ≤ 2 * L * (a * n) := by
      rw [hN]; exact Nat.mul_le_mul hL hV
    have : (N : ℝ) ≤ ((2 * L * (a * n) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; nlinarith
  have hER : (Fintype.card E : ℝ) ≤ a * m := by exact_mod_cast hE
  -- `a ≥ 1` since `V` contains the source
  have ha1 : 1 ≤ a := by
    have hV1 : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨src⟩
    by_contra ha
    have : a = 0 := by omega
    rw [this, zero_mul] at hV
    omega
  have hER1 : ((Fintype.card E + 1 : ℕ) : ℝ) ≤ 2 * a * m := by
    have h0 : Fintype.card E + 1 ≤ 2 * a * m := by
      have : 1 ≤ a * m := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      nlinarith
    exact_mod_cast h0
  have hMR : (M0 : ℝ) ≤ a * ((n : ℝ) * L + m) := by
    have : (M0 : ℝ) ≤ ((a * (n * L + m) : ℕ) : ℝ) := by exact_mod_cast hM0
    push_cast at this; linarith
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hk1R : (1 : ℝ) ≤ (k : ℝ) - 1 := by linarith
  -- the term menu
  have T1 := term_mtF n m hn
  have T2 := term_nLkF n m hn hm hnm
  have T3 := term_nLtkF n m hn hm hnm
  have hT0 := Tchd_nonneg n m
  have hmT := m_le_Tchd n m
  -- t/(k-1) ≤ 2 (t/k + 1)   (real vs Nat division)
  have htk : (t : ℝ) ≤ 2 * ((k : ℝ) - 1) * (((t / k : ℕ) : ℝ) + 1) := by
    have hdiv : (t : ℝ) < k * (((t / k : ℕ) : ℝ) + 1) := by
      have h1 : t < k * (t / k + 1) := by
        have := Nat.lt_div_mul_add (a := t) (show 0 < k by omega)
        nlinarith [Nat.mul_comm (t / k) k]
      exact_mod_cast h1
    have hq0 : (0 : ℝ) ≤ ((t / k : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  -- cast the aggregation inequality
  have haggR : ((k : ℝ) - 1) * ((∑ X ∈ univ.filter (fun X => C.base X = false), C.cost X : ℕ) : ℝ) ≤
      c * (((k : ℝ) - 1) * ((3 * k + 8) * N + 6 * t * (Fintype.card E + 1) + M0) + 3 * t * N) := by
    have := hagg
    have hcast : (((k - 1) * ∑ X ∈ univ.filter (fun X => C.base X = false), C.cost X : ℕ) : ℝ) ≤
        ((c * ((k - 1) * ((3 * k + 8) * N + 6 * t * (Fintype.card E + 1) + M0) + 3 * t * N) : ℕ) : ℝ) := by
      exact_mod_cast this
    have hsub : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    push_cast at hcast
    rw [hsub] at hcast
    push_cast
    linarith
  -- divide by (k - 1)
  set S : ℝ := ((∑ X ∈ univ.filter (fun X => C.base X = false), C.cost X : ℕ) : ℝ) with hS
  have hS0 : 0 ≤ S := Nat.cast_nonneg _
  have hmain : S ≤ c * ((3 * k + 8) * N + 6 * t * (Fintype.card E + 1) + M0
      + 6 * t / (2 * ((k : ℝ) - 1)) * N) := by
    have hpos : (0 : ℝ) < (k : ℝ) - 1 := by linarith
    have : ((k : ℝ) - 1) * S ≤ ((k : ℝ) - 1) * (c * ((3 * k + 8) * N + 6 * t * (Fintype.card E + 1) + M0
        + 6 * t / (2 * ((k : ℝ) - 1)) * N)) := by
      have e : ((k : ℝ) - 1) * (c * ((3 * k + 8) * N + 6 * t * (Fintype.card E + 1) + M0
          + 6 * t / (2 * ((k : ℝ) - 1)) * N))
          = c * (((k : ℝ) - 1) * ((3 * k + 8) * N + 6 * t * (Fintype.card E + 1) + M0) + 3 * t * N) := by
        field_simp; ring
      rw [e]; exact haggR
    exact le_of_mul_le_mul_left this hpos
  -- bound each piece by Tchd
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hnL0 : (0 : ℝ) ≤ (n : ℝ) * L := by positivity
  have p1 : (3 * (k : ℝ) + 8) * N ≤ 14 * a * ((n : ℝ) * L * k) := by
    have : (3 * (k : ℝ) + 8) ≤ 7 * k := by linarith
    calc (3 * (k : ℝ) + 8) * N ≤ 7 * k * N := mul_le_mul_of_nonneg_right this hN0
      _ ≤ 7 * k * (2 * a * ((n : ℝ) * L)) := mul_le_mul_of_nonneg_left hNR (by positivity)
      _ = 14 * a * ((n : ℝ) * L * k) := by ring
  have p2 : 6 * (t : ℝ) * ((Fintype.card E : ℝ) + 1) ≤ 12 * a * ((m : ℝ) * t) := by
    have e : ((Fintype.card E + 1 : ℕ) : ℝ) = (Fintype.card E : ℝ) + 1 := by push_cast; ring
    rw [e] at hER1
    calc 6 * (t : ℝ) * ((Fintype.card E : ℝ) + 1) ≤ 6 * t * (2 * a * m) :=
          mul_le_mul_of_nonneg_left hER1 (by positivity)
      _ = 12 * a * ((m : ℝ) * t) := by ring
  have p3 : 6 * (t : ℝ) / (2 * ((k : ℝ) - 1)) * N ≤ 12 * a * ((n : ℝ) * L * (((t / k : ℕ) : ℝ) + 1)) := by
    have hpos : (0 : ℝ) < 2 * ((k : ℝ) - 1) := by linarith
    have hq : 6 * (t : ℝ) / (2 * ((k : ℝ) - 1)) ≤ 6 * (((t / k : ℕ) : ℝ) + 1) := by
      rw [div_le_iff₀ hpos]; linarith [htk]
    calc 6 * (t : ℝ) / (2 * ((k : ℝ) - 1)) * N ≤ 6 * (((t / k : ℕ) : ℝ) + 1) * N :=
          mul_le_mul_of_nonneg_right hq hN0
      _ ≤ 6 * (((t / k : ℕ) : ℝ) + 1) * (2 * a * ((n : ℝ) * L)) :=
          mul_le_mul_of_nonneg_left hNR (by positivity)
      _ = 12 * a * ((n : ℝ) * L * (((t / k : ℕ) : ℝ) + 1)) := by ring
  have hbr : (3 * k + 8) * N + 6 * t * (Fintype.card E + 1) + M0 + 6 * t / (2 * ((k : ℝ) - 1)) * N
      ≤ 5000 * a * Tchd n m := by
    have q1 : 14 * a * ((n : ℝ) * L * k) ≤ 14 * a * (160 * Tchd n m) := mul_le_mul_of_nonneg_left T2 (by positivity)
    have q2 : 12 * a * ((m : ℝ) * t) ≤ 12 * a * (26 * Tchd n m) := mul_le_mul_of_nonneg_left T1 (by positivity)
    have q3 : 12 * a * ((n : ℝ) * L * (((t / k : ℕ) : ℝ) + 1)) ≤ 12 * a * (160 * Tchd n m) :=
      mul_le_mul_of_nonneg_left T3 (by positivity)
    have hnLle : (n : ℝ) * L ≤ (n : ℝ) * L * k := le_mul_of_one_le_right hnL0 (by linarith)
    have q4 : (a : ℝ) * ((n : ℝ) * L + m) ≤ a * (160 * Tchd n m + Tchd n m) :=
      mul_le_mul_of_nonneg_left (by linarith) ha0
    have haT : 0 ≤ (a : ℝ) * Tchd n m := mul_nonneg ha0 hT0
    linarith [p1, p2, p3, hMR, q1, q2, q3, q4, haT]
  calc S ≤ c * ((3 * k + 8) * N + 6 * t * (Fintype.card E + 1) + M0 + 6 * t / (2 * ((k : ℝ) - 1)) * N) := hmain
    _ ≤ c * (5000 * a * Tchd n m) := mul_le_mul_of_nonneg_left hbr hc0
    _ = 5000 * c * a * Tchd n m := by ring

/-- **Bridge, all calls.**  Adding the base cases (each costs `c (lg + 1)(|U| + |Eout|)` with
`lg = log₂(t+1) + log₂(dd+1) + 1`, the BST depth `O(log(t·δ))`), the WHOLE recursion costs
`≤ 5100 · c · a · Tchd n m`. -/
theorem total_le_Tchd (C : CallCounters ι V E α) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ m + 1)
    {c Lmax M0 a : ℕ} {inE : V → Finset E} {wit : ι → V → E} {src : V}
    (h : C.Valid (tF n m) (kF n m) c Lmax M0 inE wit src)
    (hV : Fintype.card V ≤ a * n) (hE : Fintype.card E ≤ a * m) (hL : Lmax + 1 ≤ 2 * LF n m)
    (hM0 : M0 ≤ a * (n * LF n m + m))
    (hbase : ∀ X, C.base X = true → C.cost X ≤
      c * (Nat.log 2 (tF n m + 1) + Nat.log 2 (dd n m + 1) + 1 + 1) * ((C.F.U X).card + (C.Eout X).card)) :
    ((∑ X, C.cost X : ℕ) : ℝ) ≤ 5100 * c * a * Tchd n m := by
  classical
  have h1 := nonbase_le_Tchd C n m hn hm hnm h hV hE hL hM0
  have h2 := CallCounters.base_total_le (lg := Nat.log 2 (tF n m + 1) + Nat.log 2 (dd n m + 1) + 1) h hbase
  have hsplit : ∑ X, C.cost X = ∑ X ∈ univ.filter (fun X => C.base X = true), C.cost X
      + ∑ X ∈ univ.filter (fun X => ¬ C.base X = true), C.cost X :=
    (Finset.sum_filter_add_sum_filter_not univ (fun X => C.base X = true) C.cost).symm
  have hfilt : univ.filter (fun X => ¬ C.base X = true) = univ.filter (fun X => C.base X = false) := by
    ext X; simp
  rw [hfilt] at hsplit
  -- the base part in reals
  set lg := Nat.log 2 (tF n m + 1) + Nat.log 2 (dd n m + 1) + 1 with hlg
  have hVE : ((Fintype.card V + Fintype.card E : ℕ) : ℝ) ≤ a * ((n : ℝ) + m) := by
    have h0 : Fintype.card V + Fintype.card E ≤ a * (n + m) := by nlinarith
    have h1 : ((Fintype.card V + Fintype.card E : ℕ) : ℝ) ≤ ((a * (n + m) : ℕ) : ℝ) := by exact_mod_cast h0
    push_cast at h1 ⊢
    linarith
  have hbaseR : ((∑ X ∈ univ.filter (fun X => C.base X = true), C.cost X : ℕ) : ℝ)
      ≤ c * ((lg : ℝ) + 1) * (a * ((n : ℝ) + m)) := by
    have hcast : ((∑ X ∈ univ.filter (fun X => C.base X = true), C.cost X : ℕ) : ℝ)
        ≤ ((c * (lg + 1) * (Fintype.card V + Fintype.card E) : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at hcast
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    have hlg0 : (0 : ℝ) ≤ (lg : ℝ) + 1 := by positivity
    calc _ ≤ (c : ℝ) * ((lg : ℝ) + 1) * ((Fintype.card V : ℝ) + Fintype.card E) := by
          push_cast at hcast ⊢; linarith
      _ ≤ c * ((lg : ℝ) + 1) * (a * ((n : ℝ) + m)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := hVE; push_cast at this; linarith
  -- (lg + 1)(n + m) ≤ 60 Tchd
  have hT1 := term_mlogtF n m hn
  have hT2 := term_mlogdd n m hn
  have hmT := m_le_Tchd n m
  have hT0 := Tchd_nonneg n m
  have hlgm : ((lg : ℝ) + 1) * ((n : ℝ) + m) ≤ 100 * Tchd n m := by
    have hnm' : (n : ℝ) ≤ m + 1 := by exact_mod_cast hnm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hl0 : (0 : ℝ) ≤ (lg : ℝ) + 1 := by positivity
    have hle : ((lg : ℝ) + 1) * ((n : ℝ) + m) ≤ ((lg : ℝ) + 1) * (3 * m) := by
      apply mul_le_mul_of_nonneg_left _ hl0; linarith
    have hlgR : (lg : ℝ) + 1 = (Nat.log 2 (tF n m + 1) : ℝ) + Nat.log 2 (dd n m + 1) + 2 := by
      rw [hlg]; push_cast; ring
    rw [hlgR] at hle
    nlinarith
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hbase2 : ((∑ X ∈ univ.filter (fun X => C.base X = true), C.cost X : ℕ) : ℝ) ≤ 100 * c * a * Tchd n m := by
    calc _ ≤ c * ((lg : ℝ) + 1) * (a * ((n : ℝ) + m)) := hbaseR
      _ = c * a * (((lg : ℝ) + 1) * ((n : ℝ) + m)) := by ring
      _ ≤ c * a * (100 * Tchd n m) := mul_le_mul_of_nonneg_left hlgm (by positivity)
      _ = 100 * c * a * Tchd n m := by ring
  rw [hsplit]
  push_cast at h1 hbase2 ⊢
  linarith

end Frontier.CostFinal
