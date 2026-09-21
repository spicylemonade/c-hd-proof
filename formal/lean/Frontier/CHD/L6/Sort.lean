import Frontier.CHD.L6.Layout
import Frontier.CHD.MergeSort

/-!
# L6 sort pass (agent-10, scratch): every range `[gSt x, gSt (x+1))` sorted by `(gW, gHead)`

Uses agent-06's verified `MergeSort.sortRange_spec_real`.
-/

open scoped NNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM WExpr Stmt Finset
open Frontier.CHD.MergeSort (sortRange srcFn segL keyLe msRegs sortRange_spec_real)

/-- The `(value, head)` list of range `x` of state `t`, with bounds read from `t0`'s `gSt`. -/
def rangeL (t0 t : State ℝ≥0) (x : ℕ) : List (ℝ≥0 × ℕ) :=
  segL (srcFn "gW" "gHead" (t0.wa "gSt" x) t) (t0.wa "gSt" (x + 1) - t0.wa "gSt" x)

def sortWR : List String := msRegs ++ ["g_x", "ms_a", "ms_b"]

structure SPInv (I : L6In) (t0 : State ℝ≥0) (x : ℕ) (t : State ℝ≥0) : Prop where
  gx : t.w "g_x" = x
  sorted : ∀ y < x, (rangeL t0 t y).Pairwise (fun a b => keyLe realOps.le a b = true) ∧
    (rangeL t0 t y).Perm (rangeL t0 t0 y)
  rest : ∀ p, t0.wa "gSt" x ≤ p → t.va "gW" p = t0.va "gW" p ∧ t.wa "gHead" p = t0.wa "gHead" p
  wL : t.vlen "gW" = t0.vlen "gW"
  hL : t.wlen "gHead" = t0.wlen "gHead"
  U : Unchanged t0 t ["gHead", "ms_H"] ["gW", "ms_W"] sortWR []
  c : t.cost ≤ t0.cost + 5 * x + 40 * (t0.wa "gSt" x + x) * (Nat.log 2 I.δ + 1)

theorem rangeL_congr {t0 t t' : State ℝ≥0} {x : ℕ}
    (h : ∀ p, t0.wa "gSt" x ≤ p → p < t0.wa "gSt" (x + 1) →
      t'.va "gW" p = t.va "gW" p ∧ t'.wa "gHead" p = t.wa "gHead" p) :
    rangeL t0 t' x = rangeL t0 t x := by
  unfold rangeL segL
  apply List.map_congr_left
  intro p hp
  simp at hp
  have := h (t0.wa "gSt" x + p) (by omega) (by omega)
  simp [srcFn, this.1, this.2]

theorem sortLoop_runs (I : L6In) (t0 : State ℝ≥0) (hpost : BPost I t0 t0) (hδ : 3 ≤ I.δ)
    (hcap : 8 * (I.n + I.m) + 16 < t0.cap) (hx0 : t0.w "g_x" = 0) :
    Runs realOps (.while (lt (var "g_x") (var "gN")) (sortBody (sortRange "gW" "gHead"))) t0
      (fun r => ∃ t, SPInv I t0 (I.off I.n) t ∧ r = t.charge 1) := by
  have hF := hpost.F
  have hN := hpost.stN
  have hsln : I.sl I.n ≤ 2 * I.m := by
    have := I.sl_le hδ I.n; rw [pfx_total _ _ _ hpost.E.A.hsrc] at this; exact this
  have hoffn : I.off I.n ≤ I.n + I.m := by
    have := I.off_le hδ I.n; rw [pfx_total _ _ _ hpost.E.A.hsrc] at this; omega
  have hst0 : t0.wa "gSt" 0 = 0 := by
    have := st_off hF hN 0 (Nat.zero_le _); simpa [L6In.off, L6In.sl] using this
  refine runs_while (fun x t => SPInv I t0 x t) (I.off I.n) _ ?_ ?_ t0
    ⟨hx0, fun y hy => absurd hy (Nat.not_lt_zero _), fun p _ => ⟨rfl, rfl⟩, rfl, rfl, by simp,
     by simp [hst0]⟩
  · intro x hx t hI
    have hU := hI.U
    have htcap : t.cap = t0.cap := hU.cap
    have htN : t.w "gN" = I.off I.n := by rw [hU.wreg _ (by simp [sortWR, msRegs])]; exact hpost.E.gN
    have htSt : t.wa "gSt" = t0.wa "gSt" := (hU.warr _ (by simp)).1
    have htStL : t.wlen "gSt" = I.off I.n + 1 := by rw [(hU.warr _ (by simp)).2]; exact hpost.lSt
    obtain ⟨v, hv, hk, q, hq, hxq, ha, hb⟩ := st_range_any hF hN hδ hx
    set a := t0.wa "gSt" x with hadef
    set b := t0.wa "gSt" (x + 1) with hbdef
    have hab : a ≤ b := by omega
    have hbM : b ≤ I.sl I.n := st_le_M hF hN hδ (by omega)
    have hlen : b - a ≤ I.δ := by
      have := L6In.lenF_le hk hδ hq; omega
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of (x := x) (y := I.off I.n) (by rw [evalW_var, hI.gx]) (by rw [evalW_var, htN])
        (by omega)]
      simp [hx]
    · unfold sortBody
      refine runs_seq (runs_wset (a := a) (by
        rw [evalW_load_of (j := x) (by simp [hI.gx]) (by simp [htStL]; omega)]; simp [htSt, hadef]) ?_)
      refine runs_seq (runs_wset (a := b) (by
        rw [evalW_load_of (j := x + 1) (evalW_add_of (by simp [hI.gx]) (evalW_lit_of (by simp [htcap]; omega))
          (by simp [htcap]; omega)) (by simp [htStL]; omega)]; simp [htSt, hbdef]) ?_)
      refine runs_seq ((sortRange_spec_real "gW" "gHead" (by decide) (by decide) _ a b (by simp) (by simp)
        hab (by simp [hI.wL, hpost.lW]; omega) (by simp [hI.hL, hpost.lHead]; omega)
        (by simp [htcap]; omega)).mono ?_)
      rintro r ⟨hsort, hperm, hout, hrW, hrH, hrU, hrc⟩
      refine runs_wset (a := x + 1) (evalW_add_of (by
          rw [evalW_var, hrU.wreg _ (by simp [msRegs])]; simp [hI.gx])
        (evalW_lit_of (by rw [hrU.cap]; simp [htcap]; omega)) (by rw [hrU.cap]; simp [htcap]; omega)) ?_
      -- the two register updates before sortRange do not touch arrays
      have hout' : ∀ p, p < a ∨ b ≤ p → r.va "gW" p = t.va "gW" p ∧ r.wa "gHead" p = t.wa "gHead" p := by
        intro p hp; have := hout p hp; simpa using this
      refine ⟨by simp, fun y hy => ?_, fun p hp => ?_, ?_, ?_, ?_, ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hy with hy | rfl
        · -- earlier ranges are untouched
          have hyle : t0.wa "gSt" (y + 1) ≤ a := st_mono hF hN hδ (by omega) (by omega)
          have hcong : rangeL t0 ((r.setW "g_x" (x + 1)).charge 1) y = rangeL t0 t y :=
            rangeL_congr (fun p _ hp2 => by simpa using hout' p (Or.inl (by omega)))
          rw [hcong]; exact hI.sorted y hy
        · -- the range just sorted
          have e1 : rangeL t0 ((r.setW "g_x" (y + 1)).charge 1) y =
              segL (srcFn "gW" "gHead" a r) (b - a) := by
            have : srcFn "gW" "gHead" a ((r.setW "g_x" (y + 1)).charge 1) = srcFn "gW" "gHead" a r := by
              funext p; simp [srcFn]
            unfold rangeL; rw [← hadef, ← hbdef, this]
          have e2 : segL (srcFn "gW" "gHead" a ((((((t.charge 1).setW "ms_a" a).charge 1).setW "ms_b" b).charge 1)))
              (b - a) = rangeL t0 t0 y := by
            unfold rangeL segL
            simp only [← hadef, ← hbdef]
            apply List.map_congr_left
            intro p hp
            simp at hp
            have := hI.rest (a + p) (by omega)
            simp [srcFn, this.1, this.2]
          rw [e1]
          exact ⟨hsort, hperm.trans (by rw [e2])⟩
      · have hbp : b ≤ p := by
          have : t0.wa "gSt" (x + 1) ≤ p := hp
          omega
        have h1 := hout' p (Or.inr hbp)
        have h2 := hI.rest p (by omega)
        simp; rw [h1.1, h1.2]; exact h2
      · simp [hrW, hI.wL]
      · simp [hrH, hI.hL]
      · have h1 : Unchanged t0 t ["gHead", "ms_H"] ["gW", "ms_W"] sortWR [] := hU
        have h2 : Unchanged t ((((((t.charge 1).setW "ms_a" a).charge 1).setW "ms_b" b).charge 1))
            ["gHead", "ms_H"] ["gW", "ms_W"] sortWR [] := by simp [sortWR]
        have h3 := hrU.mono (List.Subset.refl _) (List.Subset.refl _)
          (show msRegs ⊆ sortWR by simp [sortWR]) (List.Subset.refl _)
        have := h1.trans (h2.trans h3)
        simpa [sortWR] using this
      · -- cost
        have hc := hI.c
        have hlog : Nat.log 2 (b - a) ≤ Nat.log 2 I.δ := Nat.log_mono_right hlen
        have hmul : 40 * (b - a + 1) * (Nat.log 2 (b - a) + 1) ≤ 40 * (b - a + 1) * (Nat.log 2 I.δ + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        have hsplit : 40 * (b + (x + 1)) * (Nat.log 2 I.δ + 1) =
            40 * (a + x) * (Nat.log 2 I.δ + 1) + 40 * (b - a + 1) * (Nat.log 2 I.δ + 1) := by
          have : b + (x + 1) = (a + x) + (b - a + 1) := by omega
          rw [this]; ring
        simp only [State.charge_cost, State.setW_cost] at hrc ⊢
        rw [← hadef] at hc
        rw [← hbdef, hsplit]
        omega
  · intro t hI
    have htcap : t.cap = t0.cap := hI.U.cap
    have htN : t.w "gN" = I.off I.n := by rw [hI.U.wreg _ (by simp [sortWR, msRegs])]; exact hpost.E.gN
    refine ⟨?_, t, hI, rfl⟩
    rw [evalW_lt_of (x := I.off I.n) (y := I.off I.n) (by rw [evalW_var, hI.gx])
      (by rw [evalW_var, htN]) (by omega)]
    simp

end Frontier.CHD.L6
