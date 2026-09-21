import Frontier.CHD.L6.Prologue
import Frontier.CHD.RamSlot

/-!
# The spine prologue, part 2: the top-level `Blow` slot and the top frame (agent-10)

* `blowProg`: slot `slotBlow LF = 4 LF + 1` := the machine label of the empty walk at `gS`
  (`len 0`, `hops 0`, vertex `gS`, no last edge, version `0`), flag `1`; it represents
  `initLabels src src` (`blowProg_runs`, via agent-02/08's `storeSlot_spec`).
* `frameProg`: `S[LF·n] := gS`, `S.len[LF] := 1`, `lvl := LF`.
NON-GATE (Layer B, spine prologue).
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD.LabTab Frontier.CHD.MLab WExpr Stmt

/-- The register block of the top-level `Blow` label (spine scratch registers). -/
def blowK : LReg := ⟨"pr.bl", "sp.i", "sp.j", "sp.q", "sp.qe"⟩

/-- `slot[4 LF + 1] := (0, 0, gS, none, 0)`, flag `1`. -/
def blowProg : Stmt :=
  seq (vset "pr.bl" .zero) (seq (wset "sp.i" (lit 0)) (seq (wset "sp.j" (var "gS"))
  (seq (wset "sp.q" (lit 0)) (seq (wset "sp.qe" (lit 0)) (seq (wset "sp.b" (lit 1))
  (seq (wset "sl.i" (add (mul (lit 4) (var "cp.L")) (lit 1))) (storeSlot blowK "sp.b")))))))

/-- Word registers written by `blowProg`. -/
def blowWR : List String := ["sp.i", "sp.j", "sp.q", "sp.qe", "sp.b", "sl.i"]
/-- Value registers written by `blowProg`. -/
def blowVR : List String := ["pr.bl"]

theorem initLabels_src {H : Graph} (src : Fin H.n) :
    BM.initLabels src src = (((toW ([] : List (Fin H.m))) : WalkOrd H src) : WLab H src) := by
  show (if src = src then _ else ⊤) = _
  rw [if_pos rfl]

theorem blowProg_runs {H : Graph} (src : Fin H.n) (st : State ℝ≥0) (L : ℕ) (hS : st.w "gS" = src)
    (hL : st.w "cp.L" = L) (hlen : SlotLens st (4 * L + 1)) (hcap : 4 * L + 6 < st.cap) :
    Runs realOps blowProg st (fun r =>
      SlotHolds (s := src) r (4 * L + 1) (H0 (G := H)) (vc (G := H) st) (BM.initLabels src src) ∧
      (∀ j, j ≠ 4 * L + 1 → r.va "sl.l" j = st.va "sl.l" j ∧ ∀ a ∈ slotW, r.wa a j = st.wa a j) ∧
      Unchanged st r slotW ["sl.l"] blowWR blowVR ∧ r.cost = st.cost + 13) := by
  have c1 : 1 < st.cap := by omega
  have c4 : 4 < st.cap := by omega
  have c4L : 4 * L < st.cap := by omega
  have c41 : 4 * L + 1 < st.cap := by omega
  unfold blowProg
  refine runs_seq (runs_vset (a := 0) rfl ?_)
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by simp; omega)) ?_)
  refine runs_seq (runs_wset (a := src) (by simp [hS]) ?_)
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by simp; omega)) ?_)
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by simp; omega)) ?_)
  refine runs_seq (runs_wset (a := 1) (evalW_lit_of (by simp; omega)) ?_)
  refine runs_seq (runs_wset (a := 4 * L + 1) (by simp [hL, fit, c1, c4, c4L, c41]) ?_)
  set s7 := ((((((((((((((st.setV "pr.bl" 0).charge 1).setW "sp.i" 0).charge 1).setW "sp.j" src).charge 1).setW
    "sp.q" 0).charge 1).setW "sp.qe" 0).charge 1).setW "sp.b" 1).charge 1).setW "sl.i" (4 * L + 1)).charge 1)
    with hs7
  have hU7 : Unchanged st s7 [] [] blowWR blowVR := by rw [hs7]; simp [blowWR, blowVR]
  have hlen7 : SlotLens s7 (4 * L + 1) := by
    obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hlen
    exact ⟨by rw [hs7]; simpa using l1, by rw [hs7]; simpa using l2, by rw [hs7]; simpa using l3,
      by rw [hs7]; simpa using l4, by rw [hs7]; simpa using l5, by rw [hs7]; simpa using l6⟩
  have hvc : vc (G := H) s7 = vc (G := H) st := by
    funext v; show s7.wa "vcnt" v = st.wa "vcnt" v; rw [hs7]; simp
  have hW : WHolds (s := src) s7 blowK "sp.b" (H0 (G := H)) (vc (G := H) st) (BM.initLabels src src) := by
    refine ⟨?_, fun q hq => ?_⟩
    · have h1 : s7.w "sp.b" = 1 := by rw [hs7]; simp
      rw [h1, initLabels_src]
      simp
    · rw [initLabels_src] at hq
      have hq' : q = [] := (WithTop.coe_inj.mp hq).symm
      subst hq'
      refine ⟨⟨0, 0, src, none, 0⟩, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · show s7.v "pr.bl" = 0; rw [hs7]; simp
        · show s7.w "sp.i" = 0; rw [hs7]; simp
        · show s7.w "sp.j" = src; rw [hs7]; simp
        · show s7.w "sp.q" = encE none; rw [hs7]; simp [encE]
        · show s7.w "sp.qe" = 0; rw [hs7]; simp
      · refine ⟨rfl, by simp [Graph.len], rfl, rfl, fun _ => rfl, fun e he => ?_⟩
        cases he
  refine (storeSlot_spec (s := src) blowK "sp.b" s7 (i := 4 * L + 1) (by rw [hs7]; simp) hlen7 hW).mono ?_
  rintro r ⟨hSl, hoth, hU, hc⟩
  refine ⟨hSl, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨h1, h2⟩ := hoth j hj
    refine ⟨by rw [h1, hs7]; simp, fun a ha => by rw [h2 a ha, hs7]; simp⟩
  · exact (hU7.mono (by simp) (by simp) (by simp) (by simp)).trans
      (hU.mono (by simp) (by simp) (by simp) (by simp))
  · rw [hc, hs7]; simp

/-! ## The top frame: `S` row `LF` = `[gS]`, `lvl := LF` -/

def frameProg : Stmt :=
  seq (wstore "S" (mul (var "cp.L") (var "n")) (var "gS"))
  (seq (wstore "S.len" (var "cp.L") (lit 1))
       (wset "lvl" (var "cp.L")))

theorem frameProg_runs {V : Type} {ops : VOps V} (st : State V) (N L src : ℕ) (hn : st.w "n" = N)
    (hL : st.w "cp.L" = L) (hS : st.w "gS" = src) (hN : 0 < N) (hSl : (L + 1) * N ≤ st.wlen "S")
    (hSL : L < st.wlen "S.len") (hcap : (L + 1) * N + 2 < st.cap) :
    Runs ops frameProg st (fun r => r.wa "S" (L * N) = src ∧
      (∀ i, i ≠ L * N → r.wa "S" i = st.wa "S" i) ∧ r.wa "S.len" L = 1 ∧
      (∀ j, j ≠ L → r.wa "S.len" j = st.wa "S.len" j) ∧ r.w "lvl" = L ∧
      Unchanged st r ["S", "S.len"] [] ["lvl"] [] ∧ r.cost = st.cost + 3) := by
  have hLN : L * N < (L + 1) * N := by nlinarith
  have hc1 : L * N < st.cap := by omega
  have hc2 : 1 < st.cap := by omega
  unfold frameProg
  refine runs_seq (runs_wstore (j := L * N) (a := src) (by simp [hn, hL, fit, hc1])
    (by simp [hS]) (by omega) ?_)
  refine runs_seq (runs_wstore (j := L) (a := 1) (by simp [hL])
    (evalW_lit_of (by simp; omega)) (by simp; omega) ?_)
  refine runs_wset (a := L) (by simp [hL]) ?_
  refine ⟨by simp, fun i hi => by simp [State.storeW, hi], by simp,
    fun j hj => by simp [State.storeW, hj], by simp, ?_, by simp⟩
  rw [unchanged_charge_iff, unchanged_setW_iff (by simp), unchanged_charge_iff,
    unchanged_storeW_iff (by simp), unchanged_charge_iff, unchanged_storeW_iff (by simp)]
  exact Unchanged.refl _ _ _ _ _

end Frontier.CHD.L6

#print axioms Frontier.CHD.L6.blowProg_runs
