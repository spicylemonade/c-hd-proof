import Frontier.CHD.L6.SpineTop
import Frontier.CHD.L6.Tnat
import Frontier.CHD.AllocList

/-!
# The spine prologue, part 1: sizes and capacities (agent-10)

* `logLoop x r`: `r := r + ⌊log₂ x⌋` by halving (generic registers);
* `tnProg`: `pr.tn := Tnat cn cm = cn + cm (tF + lg(dd+1) + 3)` from the registers of `paramsProg`;
* `capProg Cw`: the D-layer capacities `ad.ec = ad.bc = ad.sc := Cw · Tnat`, `ad.lc := LF + 3`;
* `sizeProg`: `n := gN`, `sp.zl := LF + 2` (level tables), `sp.zr := (LF + 2) n` (rows),
  `sp.zs := 4 (LF + 2)` (bound slots, `slotB l = 4 l`, …).
NON-GATE (Layer B, spine prologue).
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V}

/-! ## A generic halving loop -/

/-- One halving step. -/
def logBody (x r : String) : Stmt := seq (wset x (div (var x) (lit 2))) (inc r)

/-- `while 1 < x: x := x / 2; r := r + 1`. -/
def logLoop (x r : String) : Stmt := .while (lt (lit 1) (var x)) (logBody x r)

structure LogInv (x r : String) (st : State V) (X r0 : ℕ) (j : ℕ) (t : State V) : Prop where
  vx : t.w x = X / 2 ^ j
  vr : t.w r = r0 + j
  U : Unchanged st t [] [] [x, r] []
  c : t.cost = st.cost + 3 * j

theorem logLoop_runs (x r : String) (hxr : x ≠ r) (st : State V) (X r0 : ℕ) (hx : st.w x = X)
    (hr : st.w r = r0) (hX : 1 ≤ X) (hcap : X + r0 + 2 < st.cap) :
    Runs ops (logLoop x r) st (fun t' => ∃ t, LogInv x r st X r0 (Nat.log 2 X) t ∧ t' = t.charge 1) := by
  refine runs_while (fun j t => LogInv x r st X r0 j t) (Nat.log 2 X) _ ?_ ?_ st
    ⟨by simp [hx], by simp [hr], by simp, by simp⟩
  · intro j hj t hI
    have htcap : t.cap = st.cap := hI.U.cap
    have h1 : 1 < X / 2 ^ j := Dispatch.one_lt_div_pow_of_lt_log hj
    have hle : X / 2 ^ j ≤ X := Nat.div_le_self _ _
    have hlog : Nat.log 2 X ≤ X := Nat.log_le_self 2 X
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of (x := 1) (y := X / 2 ^ j) (evalW_lit_of (by rw [htcap]; omega))
        (by rw [evalW_var, hI.vx]) (by rw [htcap]; omega)]
      simp [h1]
    · have hrx : r ≠ x := fun h => hxr h.symm
      unfold logBody inc
      refine runs_seq (runs_wset (a := X / 2 ^ j / 2) ?_ ?_)
      · simp [hI.vx, fit, htcap, show 2 < st.cap by omega]
      · refine runs_wset (a := r0 + j + 1) ?_ ?_
        · simp [hI.vr, hrx, fit, htcap, show 1 < st.cap by omega,
            show r0 + j + 1 < st.cap by omega]
        · refine ⟨?_, ?_, ?_, ?_⟩
          · simp [hxr, Nat.div_div_eq_div_mul, pow_succ]
          · simp; ring
          · rw [unchanged_charge_iff, unchanged_setW_iff (by simp), unchanged_charge_iff,
              unchanged_setW_iff (by simp), unchanged_charge_iff]
            exact hI.U
          · simp [hI.c]; ring
  · intro t hI
    have htcap : t.cap = st.cap := hI.U.cap
    have h2 : X / 2 ^ Nat.log 2 X < 2 := Dispatch.div_pow_log_lt_two X
    refine ⟨?_, t, hI, rfl⟩
    rw [evalW_lt_of (x := 1) (y := X / 2 ^ Nat.log 2 X) (evalW_lit_of (by rw [htcap]; omega))
      (by rw [evalW_var, hI.vx]) (by rw [htcap]; omega)]
    have : ¬ (1 < X / 2 ^ Nat.log 2 X) := by omega
    simp [this]


/-! ## `pr.tn := Tnat cn cm` -/

/-- `pr.tn := cn + cm (cp.t + lg(cp.dd + 1) + 3)`. -/
def tnProg : Stmt :=
  seq (wset "pr.x" (add (var "cp.dd") (lit 1)))
  (seq (wset "pr.lg" (lit 0))
  (seq (logLoop "pr.x" "pr.lg")
       (wset "pr.tn" (add (var "cn") (mul (var "cm") (add (add (var "cp.t") (var "pr.lg")) (lit 3)))))))

/-- Registers written by `tnProg`. -/
def tnWR : List String := ["pr.x", "pr.lg", "pr.tn"]

theorem tnProg_runs (st : State V) (cn cm : ℕ) (hcn : st.w "cn" = cn) (hcm : st.w "cm" = cm)
    (hdd : st.w "cp.dd" = CostSkeleton.dd cn cm) (ht : st.w "cp.t" = CostSkeleton.tF cn cm)
    (hcm1 : 1 ≤ cm) (hcap : CostSkeleton.Tnat cn cm + CostSkeleton.dd cn cm + 4 < st.cap) :
    Runs ops tnProg st (fun r => r.w "pr.tn" = CostSkeleton.Tnat cn cm ∧
      Unchanged st r [] [] tnWR [] ∧
      r.cost ≤ st.cost + 3 * Nat.log 2 (CostSkeleton.dd cn cm + 1) + 5) := by
  set D := CostSkeleton.dd cn cm with hD
  set T := CostSkeleton.tF cn cm with hT
  set g := Nat.log 2 (D + 1) with hg
  have hgD : g ≤ D + 1 := Nat.log_le_self 2 (D + 1)
  have hTn : CostSkeleton.Tnat cn cm = cn + cm * (T + g + 3) := rfl
  have hsum : T + g + 3 ≤ CostSkeleton.Tnat cn cm := by
    rw [hTn]; nlinarith
  have hprod : cm * (T + g + 3) ≤ CostSkeleton.Tnat cn cm := by
    rw [hTn]; exact Nat.le_add_left _ _
  have c1 : 1 < st.cap := by omega
  have c2 : D + 1 < st.cap := by omega
  have c3 : 3 < st.cap := by omega
  have c4 : T + g + 3 < st.cap := by omega
  have c5 : cm * (T + g + 3) < st.cap := by omega
  have c6 : cn + cm * (T + g + 3) < st.cap := by rw [← hTn]; omega
  unfold tnProg
  refine runs_seq (runs_wset (a := D + 1) (by simp [hdd, fit, c1, c2]) ?_)
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by simp only [State.charge_cap, State.setW_cap]; omega)) ?_)
  set s2 := ((((st.setW "pr.x" (D + 1)).charge 1).setW "pr.lg" 0).charge 1) with hs2
  have hs2cap : s2.cap = st.cap := by rw [hs2]; simp
  refine runs_seq ((logLoop_runs (ops := ops) "pr.x" "pr.lg" (by decide) s2 (D + 1) 0
    (by rw [hs2]; simp) (by rw [hs2]; simp) (by omega) (by rw [hs2cap]; omega)).mono ?_)
  rintro _ ⟨t, hI, rfl⟩
  have htcap : t.cap = st.cap := by rw [hI.U.cap, hs2cap]
  have hw : ∀ x, x ∉ ["pr.x", "pr.lg"] → t.w x = st.w x := by
    intro x hx
    rw [hI.U.wreg x hx, hs2]
    simp at hx
    simp [hx.1, hx.2]
  have htcn : t.w "cn" = cn := by rw [hw _ (by simp)]; exact hcn
  have htcm : t.w "cm" = cm := by rw [hw _ (by simp)]; exact hcm
  have htt : t.w "cp.t" = T := by rw [hw _ (by simp)]; exact ht
  have htg : t.w "pr.lg" = g := by rw [hI.vr]; simp [hg]
  refine runs_wset (a := CostSkeleton.Tnat cn cm) ?_ ?_
  · have c7 : T + g < st.cap := by omega
    simp [htcn, htcm, htt, htg, fit, htcap, c3, c4, c5, c6, c7, hTn]
  · refine ⟨by simp, ?_, ?_⟩
    · have h0 : Unchanged st s2 [] [] tnWR [] := by rw [hs2]; simp [tnWR]
      have h1 : Unchanged s2 t [] [] tnWR [] :=
        hI.U.mono (by simp) (by simp) (by simp [tnWR]) (by simp)
      have h2 := h0.trans h1
      rw [unchanged_charge_iff, unchanged_setW_iff (by simp [tnWR])]
      exact h2.trans (Unchanged.charge t 1 [] [] tnWR [])
    · have hc := hI.c
      have : s2.cost = st.cost + 2 := by rw [hs2]; simp
      simp only [State.charge_cost, State.setW_cost]
      omega

/-! ## Sizes: `n := gN` and the size registers of the spine arrays -/

/-- `n := gN`, `sp.zl := LF + 2`, `sp.zr := (LF + 2) n`, `sp.zs := 4 (LF + 2)`. -/
def sizeProg : Stmt :=
  seq (wset "n" (var "gN"))
  (seq (wset "sp.zl" (add (var "cp.L") (lit 2)))
  (seq (wset "sp.zr" (mul (var "sp.zl") (var "n")))
       (wset "sp.zs" (mul (lit 4) (var "sp.zl")))))

/-- Registers written by `sizeProg`. -/
def sizeWR : List String := ["n", "sp.zl", "sp.zr", "sp.zs"]

theorem sizeProg_runs (st : State V) (N L : ℕ) (hN : st.w "gN" = N) (hL : st.w "cp.L" = L)
    (hcap : 4 * ((L + 2) * (N + 1)) < st.cap) :
    Runs ops sizeProg st (fun r => r.w "n" = N ∧ r.w "sp.zl" = L + 2 ∧
      r.w "sp.zr" = (L + 2) * N ∧ r.w "sp.zs" = 4 * (L + 2) ∧ Unchanged st r [] [] sizeWR [] ∧
      r.cost = st.cost + 4) := by
  have h1 : L + 2 < st.cap := by nlinarith
  have h2 : (L + 2) * N < st.cap := by nlinarith
  have h3 : 4 * (L + 2) < st.cap := by nlinarith
  have h0 : 2 < st.cap := by omega
  have h4 : 4 < st.cap := by omega
  unfold sizeProg
  refine runs_seq (runs_wset (a := N) (by simp [hN]) ?_)
  refine runs_seq (runs_wset (a := L + 2) (by simp [hL, fit, h0, h1]) ?_)
  refine runs_seq (runs_wset (a := (L + 2) * N) (by simp [fit, h2]) ?_)
  refine runs_wset (a := 4 * (L + 2)) (by simp [fit, h3, h4]) ?_
  refine ⟨by simp, by simp, by simp, by simp, ?_, by simp⟩
  simp [sizeWR]

end Frontier.CHD.L6
