import Frontier.CHD.L6.Body
import Frontier.CHD.LabRAM
import Frontier.CHD.TraceFits

/-!
# From the core's final label table to `CoreOut` (agent-10)

If the label arrays represent (`LabAt`, agent-02) labels `d` that are all complete (the Layer-A
top-level exactness `bmsspDL_top`), then the table decodes to the exact distances, i.e. `CoreOut`.
NON-GATE (a bridge lemma of the core's final step).
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD.LabTab

theorem coreOut_of_labAt {H : Graph} {src : Fin H.n} {st : State ℝ≥0} {d : Labels H src}
    {Hh : Fin H.n → ℕ → List (Fin H.m)} {c0 : ℕ} (hL : LabAt (s := src) st d Hh c0)
    (hc : ∀ v, Complete d v) : CoreOut H src st where
  finL := hL.lens.fin
  lenL := hL.lens.len
  exact x := by
    have hrep := hL.rep
    by_cases hr : H.Reachable src x
    · have hd : d x = ((toW (path (s := src) x) : WalkOrd H src) : WLab H src) := by
        rw [hc x, dis_of_reachable hr]
      have hfin : st.wa "dfin" x ≠ 0 := by
        intro h0
        have := (hrep.fin_iff x).mp h0
        rw [hd] at this; exact WithTop.coe_ne_top this
      have hR := hrep.rep x _ hd
      have hlen : st.va "dlen" x = H.len (path (s := src) x) := hR.2.1
      rw [if_neg hfin, hlen]
      exact len_path hr
    · have hd : d x = ⊤ := by rw [hc x, dis_of_not_reachable hr]
      have hfin : st.wa "dfin" x = 0 := (hrep.fin_iff x).mpr hd
      rw [if_pos hfin]
      exact (Graph.dist_eq_top_iff.mpr hr).symm

/-! ## Exactness of a top-level C-HD run over L6's out-lists -/

theorem delInv_empty (H : Graph) (src : Fin H.n) : DelInv H src ∅ := by
  intro e he; simp at he

/-- The top level `LF` has capacity above the vertex count: `gN ≤ 2 cn < τ_{LF}`. -/
theorem tau_top_gt (cn cm N : ℕ) (hN : N ≤ 2 * cn) :
    N < BM.chdTau (CostSkeleton.tF cn cm) (CostSkeleton.LF cn cm) := by
  set t := CostSkeleton.tF cn cm with htdef
  set L := CostSkeleton.LF cn cm with hLdef
  have ht16 : 16 ≤ t := CostSkeleton.sixteen_le_tF cn cm
  have hLt : CostSkeleton.lgN cn + 1 ≤ L * t := by
    rw [hLdef, CostSkeleton.LF, ← htdef]
    have h1 := Nat.div_add_mod (CostSkeleton.lgN cn) t
    have h2 := Nat.mod_lt (CostSkeleton.lgN cn) (show 0 < t by omega)
    have : (CostSkeleton.lgN cn / t + 1) * t = t * (CostSkeleton.lgN cn / t) + t := by ring
    omega
  have hlog : cn < 2 ^ (CostSkeleton.lgN cn + 1) := by
    have h1 : cn < 2 ^ (Nat.log 2 cn + 1) := Nat.lt_pow_succ_log_self (by norm_num) cn
    have h2 : Nat.log 2 cn ≤ CostSkeleton.lgN cn := le_max_right _ _
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h2 : 2 ^ (CostSkeleton.lgN cn + 1) ≤ 2 ^ (L * t) := Nat.pow_le_pow_right (by norm_num) hLt
  have h3 : 2 ≤ t ^ 3 := by
    calc 2 ≤ 16 ^ 3 := by norm_num
      _ ≤ t ^ 3 := Nat.pow_le_pow_left ht16 3
  unfold BM.chdTau
  calc N ≤ 2 * cn := hN
    _ < 2 * 2 ^ (L * t) := by omega
    _ ≤ t ^ 3 * 2 ^ (L * t) := Nat.mul_le_mul_right _ h3

/-- **Exactness of the top-level run**: a `BMSSPD` derivation of the top call (source `src`,
bound `⊤`, level `LF`) over the out-lists `outL H` with the C-HD parameters of `(cn, cm)` ends with
complete labels — given L6's sortedness and simplicity facts. -/
theorem complete_of_topRun {H : Graph} {src : Fin H.n} {cn cm : ℕ} {hins hext : ℕ}
    (hsort : ∀ x, (outL H x).Pairwise (SortedRel H src))
    (hsimp : ∀ x, ((outL H x).map H.dst).Nodup) (hN : H.n ≤ 2 * cn)
    {DCb : BM.DCost} {T : ℕ → ℕ} {Blow : WLab H src} (hlow : Blow ≤ BM.initLabels src src)
    {φ' : Finset (Fin H.m)} {res : BM.ResultD H src} {gE : BM.DGl H src}
    {lg : BM.Log H src (FPData H src)}
    (hrel : BM.BMSSPD H src (BM.dlOps H src) (fpC H src (outL H) (CostSkeleton.kF cn cm) hins hext)
      DCb T (BM.chdM (CostSkeleton.tF cn cm)) (BM.chdTau (CostSkeleton.tF cn cm))
      (CostSkeleton.LF cn cm) Blow ⊤ {src} (BM.initLabels src) ∅ BM.DGl.init res φ' gE lg) :
    ∀ v, Complete res.2.2.2 v := by
  have hk : 2 ≤ CostSkeleton.kF cn cm := by
    have h16 := CostSkeleton.sixteen_le_tF cn cm
    unfold CostSkeleton.kF
    have : 4 ≤ Nat.sqrt (CostSkeleton.tF cn cm) := by
      rw [Nat.le_sqrt]; omega
    split_ifs <;> omega
  have hFPC := fpC_sound (G := H) (s := src) (out := outL H) (hins := hins) (hext := hext)
    (fun u e => outL_mem) hsort hsimp hk
  exact (BM.bmsspDL_top hFPC _ (BM.chdM_pos (by have := CostSkeleton.sixteen_le_tF cn cm; omega))
    (CostSkeleton.LF cn cm) (tau_top_gt cn cm H.n hN) hlow (delInv_empty H src) hrel).1

end Frontier.CHD.L6

#print axioms Frontier.CHD.L6.complete_of_topRun

#print axioms Frontier.CHD.L6.coreOut_of_labAt
