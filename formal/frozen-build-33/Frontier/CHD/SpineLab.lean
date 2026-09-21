import Frontier.CHD.RamSlot
import Frontier.CHD.RamLevel
import Frontier.CHD.LabRAM
import Frontier.CHD.BM
import Frontier.CHD.LabI

/-!
# SpineLab — label steps of the BMSSP spine (agent-02, for B-L4, NON-GATE)

S1 = BM.8: `B'_0 := min(B, min_j d[p_j])` (Layer A: `BM.initB'`).  The bound `B` is read from slot
`b8.sB`, the pivots from the group table (`sp.gp[lvl * gN + j]`, agent-08's `RamLevel.GrpRep` rows, with the
row width in register `gN` = the core graph's vertex count, per reviewer #1's O28), and
the result is stored in slot `b8.sBp` (agent-08's `RamSlot`).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.SpineLab

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.MLab Frontier.CHD.LabTab
  WExpr Stmt

variable {G : Graph} {s : Fin G.n}

/-- Running-minimum block and scratch block of BM.8. -/
def K8 : LReg := ⟨"b8.kl", "b8.kh", "b8.kv", "b8.ke", "b8.kr"⟩
def Y8 : LReg := ⟨"b8.yl", "b8.yh", "b8.yv", "b8.ye", "b8.yr"⟩

/-- One BM.8 iteration: `x := piv[j]`; if `d[x] < K` then `K := d[x]`; `j := j + 1`. -/
def b8Body : Stmt :=
  seq (wset "b8.x" (load "sp.gp" (add (mul (var "lvl") (var "gN")) (var "b8.j"))))
  (seq (headLtB "b8.x" Y8 K8 "b8.yf" "b8.kf" "b8.c1" "b8.c2" "b8.lt")
  (seq (ite (var "b8.lt") (loadLab "b8.x" K8 "b8.kf") skip)
       (wset "b8.j" (add (var "b8.j") (lit 1)))))

/-- BM.8: `slot[b8.sBp] := min(slot[b8.sB], min_{j < b8.p} d[piv j])`. -/
def b8Prog : Stmt :=
  seq (wset "sl.i" (var "b8.sB"))
  (seq (loadSlot K8 "b8.kf")
  (seq (wset "b8.j" (lit 0))
  (seq (.while (lt (var "b8.j") (var "b8.p")) b8Body)
  (seq (wset "sl.i" (var "b8.sBp")) (storeSlot K8 "b8.kf")))))

/-- The partial minimum after `j` pivots. -/
noncomputable def pmin {p : ℕ} (B : WLab G s) (d : Labels G s) (piv : Fin p → Fin G.n) (j : ℕ) :
    WLab G s :=
  min B ((Finset.univ.filter (fun i : Fin p => (i : ℕ) < j)).inf fun i => d (piv i))

theorem pmin_zero {p : ℕ} (B : WLab G s) (d : Labels G s) (piv : Fin p → Fin G.n) :
    pmin B d piv 0 = B := by
  simp [pmin]

theorem pmin_succ {p : ℕ} (B : WLab G s) (d : Labels G s) (piv : Fin p → Fin G.n) (j : ℕ)
    (hj : j < p) : pmin B d piv (j + 1) = min (pmin B d piv j) (d (piv ⟨j, hj⟩)) := by
  unfold pmin
  have hset : (Finset.univ.filter (fun i : Fin p => (i : ℕ) < j + 1)) =
      insert ⟨j, hj⟩ (Finset.univ.filter (fun i : Fin p => (i : ℕ) < j)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h; rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · rintro (h | h)
      · rw [h]; exact Nat.lt_succ_self j
      · exact Nat.lt_succ_of_lt h
  rw [hset, Finset.inf_insert]
  show min B (min (d (piv ⟨j, hj⟩)) _) = _
  rw [min_comm (d (piv ⟨j, hj⟩)), ← min_assoc]

theorem pmin_full {p : ℕ} (B : WLab G s) (d : Labels G s) (piv : Fin p → Fin G.n) :
    pmin B d piv p = BM.initB' B d piv := by
  unfold pmin BM.initB'
  congr 1
  congr 1
  ext i; simp [i.isLt]

/-- A loaded table entry, as a flagged block, holds the walk label `d v`. -/
theorem Loaded.wholds {st : State ℝ≥0} {T : Tab G} {X : LReg} {xf : String} {v : Fin G.n}
    {d : Labels G s} {H : Fin G.n → ℕ → List (Fin G.m)} (hLd : Loaded st T X xf v)
    (hR : Represents (s := s) T d H) : WHolds st X xf H T.vcnt (d v) := by
  refine ⟨by rw [hLd.2.2.2.2.2]; exact hR.fin_iff v, fun q hq => ?_⟩
  have hv : d v ≠ ⊤ := by rw [hq]; exact WithTop.coe_ne_top
  exact ⟨T.lab v, Loaded.holds hLd hR hv, hR.rep v q hq⟩

theorem WHolds.charge' {st : State ℝ≥0} {X : LReg} {xf : String}
    {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {b : WLab G s}
    (h : WHolds st X xf H V b) (k : ℕ) : WHolds (st.charge k) X xf H V b := h

/-- The registers BM.8 writes. -/
def b8W : List String :=
  ["sl.i", "b8.kh", "b8.kv", "b8.ke", "b8.kr", "b8.kf", "b8.j", "b8.x", "b8.yh", "b8.yv", "b8.ye",
   "b8.yr", "b8.yf", "b8.c1", "b8.c2", "b8.lt"]
/-- The value registers BM.8 writes. -/
def b8V : List String := ["b8.kl", "b8.yl"]

open Classical in
/-- One iteration of BM.8. -/
theorem b8Body_spec (st : State ℝ≥0) (d : Labels G s) (H : Fin G.n → ℕ → List (Fin G.m))
    (c0 : ℕ) (hL : LabAt st d H c0) {p : ℕ} (piv : Fin p → Fin G.n) (l n j : ℕ)
    (hj : j < p) (hl : st.w "lvl" = l) (hn : st.w "gN" = n) (hjr : st.w "b8.j" = j)
    (hpv : st.wa "sp.gp" (l * n + j) = piv ⟨j, hj⟩) (hgp : l * n + j < st.wlen "sp.gp")
    (B : WLab G s) (hK : WHolds st K8 "b8.kf" H (vc st) (pmin B d piv j))
    (hcap : l * n + p + 2 < st.cap) :
    Runs realOps b8Body st (fun r => WHolds r K8 "b8.kf" H (vc st) (pmin B d piv (j + 1)) ∧
      r.w "b8.j" = j + 1 ∧ Unchanged st r [] [] b8W b8V ∧ st.cost + 1 ≤ r.cost ∧
      r.cost ≤ st.cost + 32) := by
  have hR := hL.rep
  have hcap1 : 1 < st.cap := by omega
  apply runs_seq
  apply wp_sound
  rw [wp_wset_of (a := (piv ⟨j, hj⟩ : ℕ)) (by
    have h1 : l * n < st.cap := by omega
    simp [hl, hn, hjr, fit_of_lt h1, fit_of_lt (show l * n + j < st.cap by omega), hgp, hpv])]
  set q1 := (st.setW "b8.x" (piv ⟨j, hj⟩ : ℕ)).charge 1 with hq1
  have hU1 : Unchanged st q1 [] [] ["b8.x"] [] := by simp [hq1, unch_setW]
  have hL1 : LabAt q1 d H c0 := hL.of_unchanged hU1 (by decide) (by decide) (by simp [hq1])
  have hvc1 : vc (G := G) q1 = vc st := vc_of_unchanged hU1 (by decide)
  have hK1 : WHolds q1 K8 "b8.kf" H (vc st) (pmin B d piv j) :=
    hK.of_unchanged hU1 (by decide) (by decide) (by decide)
  apply runs_seq
  have hW := headLtB_wp "b8.x" Y8 K8 "b8.yf" "b8.kf" "b8.c1" "b8.c2" "b8.lt"
    ⟨by decide, by decide⟩ ⟨by decide, by decide, by decide, by decide, by decide⟩
    (by decide) (by decide) (by decide) q1 d H c0 hL1 (piv ⟨j, hj⟩) (by simp [hq1])
    (pmin B d piv j) (by rw [hvc1]; exact hK1) (by simp [hq1]; exact hcap1)
  refine (Frontier.CHD.LabIInst.Runs.cost_ge (wp_sound (ops := realOps) _ _ _ hW)).mono ?_
  rintro r2 ⟨⟨hlt2, hU2, hc2⟩, hc2lo⟩
  have hU12 := hU1.comp hU2
  have hL2 : LabAt r2 d H c0 := hL.of_unchanged hU12 (by decide) (by decide) (by simp [hq1] at hc2lo; omega)
  have hK2 : WHolds r2 K8 "b8.kf" H (vc st) (pmin B d piv j) :=
    hK.of_unchanged hU12 (by decide) (by decide) (by decide)
  have hx2 : r2.w "b8.x" = piv ⟨j, hj⟩ := by rw [hU2.wreg "b8.x" (by decide)]; simp [hq1]
  have hj2 : r2.w "b8.j" = j := by rw [hU12.wreg "b8.j" (by decide)]; exact hjr
  have hcap2 : 1 < r2.cap := by rw [hU12.cap]; exact hcap1
  have hLt : r2.w "b8.lt" = if d (piv ⟨j, hj⟩) < pmin B d piv j then 1 else 0 := hlt2
  have hc2' : r2.cost ≤ st.cost + 1 + 22 := by simp [hq1] at hc2; omega
  have hc2lo' : st.cost + 1 ≤ r2.cost := by simp [hq1] at hc2lo; omega
  apply runs_seq
  by_cases hlt : d (piv ⟨j, hj⟩) < pmin B d piv j
  · -- new minimum: load it
    have h1 : r2.w "b8.lt" = 1 := by rw [hLt, if_pos hlt]
    apply runs_ite_true (by simp [h1] : evalW r2 (WExpr.var "b8.lt") = some 1) one_ne_zero
    apply wp_sound
    refine wp_mono _ ?_ _ (loadLab_wp "b8.x" K8 "b8.kf" ⟨by decide, by decide⟩ (r2.charge 1)
      (piv ⟨j, hj⟩) (hL2.lens.charge 1) (by simpa using hx2))
    rintro r3 ⟨hLd3, hU3, hc3⟩
    have hT : tabOf (G := G) (r2.charge 1) = tabOf st :=
      (tabOf_of_unchanged (G := G) hU12 (by decide) (by decide)).1
    rw [hT] at hLd3
    have hK3 : WHolds r3 K8 "b8.kf" H (vc st) (d (piv ⟨j, hj⟩)) := Loaded.wholds hLd3 hL.rep
    have hj3 : r3.w "b8.j" = j := by rw [hU3.wreg "b8.j" (by decide)]; simpa using hj2
    have hcap3 : j + 1 < r3.cap := by rw [hU3.cap]; simp [hU12.cap]; omega
    apply wp_sound
    rw [wp_wset_of (a := j + 1) (by
      simp [hj3, fit_of_lt hcap3, fit_of_lt (show 1 < r3.cap by omega)])]
    have hU4 : Unchanged r3 ((r3.setW "b8.j" (j + 1)).charge 1) [] [] ["b8.j"] [] := by
      simp [unch_setW]
    refine ⟨?_, by simp, ?_, ?_, ?_⟩
    · rw [pmin_succ B d piv j hj, min_eq_right (le_of_lt hlt)]
      exact hK3.of_unchanged hU4 (by decide) (by decide) (by decide)
    · exact (((hU12.comp (Unchanged.charge r2 1 [] [] [] [])).comp hU3).comp hU4).mono
        (by simp) (by simp) (by decide) (by decide)
    · simp [hc3]; omega
    · simp [hc3]; omega
  · -- keep the running minimum
    have h0 : r2.w "b8.lt" = 0 := by rw [hLt, if_neg hlt]
    apply runs_ite_false (by simp [h0])
    apply wp_sound
    rw [wp_skip]
    apply wp_sound
    rw [wp_wset_of (a := j + 1) (by
      have h1 : j + 1 < r2.cap := by rw [hU12.cap]; omega
      simp [hj2, fit_of_lt h1, fit_of_lt hcap2])]
    have hU4 : Unchanged r2 ((((r2.charge 1).charge 1).setW "b8.j" (j + 1)).charge 1) [] []
        ["b8.j"] [] := by simp [unch_setW]
    refine ⟨?_, by simp, ?_, ?_, ?_⟩
    · rw [pmin_succ B d piv j hj, min_eq_left (not_lt.mp hlt)]
      exact hK2.of_unchanged hU4 (by decide) (by decide) (by decide)
    · exact (hU12.comp hU4).mono (by simp) (by simp) (by decide) (by decide)
    · simp; omega
    · simp; omega

open Classical in
/-- **BM.8** (`B'_0 := min(B, min_j d[p_j])`, Layer A `BM.initB'`): from slot `b8.sB` holding `B`
and the pivots in the group table row, slot `b8.sBp` ends up holding `initB' B d piv`. -/
theorem b8Prog_spec (st : State ℝ≥0) (d : Labels G s) (H : Fin G.n → ℕ → List (Fin G.m))
    (c0 : ℕ) (hL : LabAt st d H c0) {p : ℕ} (piv : Fin p → Fin G.n) (l n : ℕ)
    (hl : st.w "lvl" = l) (hn : st.w "gN" = n) (hpr : st.w "b8.p" = p)
    (hpv : ∀ j (hj : j < p), st.wa "sp.gp" (l * n + j) = piv ⟨j, hj⟩)
    (hgp : l * n + p ≤ st.wlen "sp.gp") (iB iBp : ℕ) (hiB : st.w "b8.sB" = iB)
    (hiBp : st.w "b8.sBp" = iBp) (hlB : SlotLens st iB) (hlBp : SlotLens st iBp)
    (B : WLab G s) (hB : SlotHolds st iB H (vc st) B) (hcap : l * n + p + 2 < st.cap) :
    Runs realOps b8Prog st (fun r => SlotHolds r iBp H (vc st) (BM.initB' B d piv) ∧
      LabAt r d H c0 ∧
      (∀ j, j ≠ iBp → r.va "sl.l" j = st.va "sl.l" j ∧ ∀ a ∈ slotW, r.wa a j = st.wa a j) ∧
      Unchanged st r slotW ["sl.l"] b8W b8V ∧ r.cost ≤ st.cost + 17 + 33 * p) := by
  have hcap1 : 1 < st.cap := by omega
  -- sl.i := b8.sB
  apply runs_seq
  apply wp_sound
  rw [wp_wset_of (a := iB) (by simp [hiB])]
  set q1 := (st.setW "sl.i" iB).charge 1 with hq1
  have hU1 : Unchanged st q1 [] [] b8W b8V := by simp [hq1, unch_setW, b8W]
  -- K8 := slot[iB]
  apply runs_seq
  refine (loadSlot_spec K8 "b8.kf" ⟨by decide⟩ q1 (by simp [hq1])
    ⟨by simpa [hq1] using hlB.l, by simpa [hq1] using hlB.h, by simpa [hq1] using hlB.v,
      by simpa [hq1] using hlB.e, by simpa [hq1] using hlB.r, by simpa [hq1] using hlB.f⟩
    (hB.of_unchanged hU1 (by decide) (by decide))).mono ?_
  rintro q2 ⟨hK2, hU2, hc2⟩
  have hU12 : Unchanged st q2 [] [] b8W b8V :=
    (hU1.comp hU2).mono (by simp) (by simp) (by decide) (by decide)
  -- b8.j := 0
  apply runs_seq
  apply wp_sound
  rw [wp_wset_of (a := 0) (by simp [fit, show 0 < q2.cap by rw [hU12.cap]; omega])]
  set q3 := (q2.setW "b8.j" 0).charge 1 with hq3
  have hU13 : Unchanged st q3 [] [] b8W b8V :=
    (hU12.comp (by simp [hq3, unch_setW] : Unchanged q2 q3 [] [] ["b8.j"] [])).mono (by simp)
      (by simp) (by decide) (by decide)
  have hK3 : WHolds q3 K8 "b8.kf" H (vc st) (pmin B d piv 0) := by
    rw [pmin_zero]
    exact hK2.of_unchanged (by simp [hq3, unch_setW] : Unchanged q2 q3 [] [] ["b8.j"] [])
      (by decide) (by decide) (by decide)
  -- the loop
  apply runs_seq
  have hw0 : ∀ a ∈ ([] : List String), a ∉ labW := by simp
  let I : ℕ → State ℝ≥0 → Prop := fun k q => q.w "b8.j" = k ∧
    WHolds q K8 "b8.kf" H (vc st) (pmin B d piv k) ∧ Unchanged st q [] [] b8W b8V ∧
    st.cost ≤ q.cost ∧ q.cost ≤ q3.cost + 33 * k
  have hq3c : q3.cost = st.cost + 8 := by simp [hq3, hc2, hq1]
  refine runs_while I p _ (fun k hk q ⟨hj, hK, hU, hclo, hchi⟩ => ?_) (fun q ⟨hj, hK, hU, hclo, hchi⟩ => ?_) q3
    ⟨by simp [hq3], hK3, hU13, by omega, by simp⟩
  · have hcapq : 1 < q.cap := by rw [hU.cap]; exact hcap1
    refine ⟨1, by simp [hj, (hU.wreg "b8.p" (by decide)).trans hpr, hk, fit_of_lt hcapq],
      one_ne_zero, ?_⟩
    have hLq : LabAt (q.charge 1) d H c0 := hL.of_unchanged (hU.comp (Unchanged.charge q 1 [] [] [] []))
      (by decide) (by decide) (by simp; omega)
    have hvcq : vc (G := G) (q.charge 1) = vc st := vc_of_unchanged
      (hU.comp (Unchanged.charge q 1 [] [] [] [])) (by decide)
    refine (b8Body_spec (q.charge 1) d H c0 hLq piv l n k hk
      (by simp [(hU.wreg "lvl" (by decide)).trans hl]) (by simp [(hU.wreg "gN" (by decide)).trans hn])
      (by simp [hj]) (by simp [(hU.warr "sp.gp" (by simp)).1, hpv k hk])
      (by simp [(hU.warr "sp.gp" (by simp)).2]; omega) B (by rw [hvcq]; exact hK)
      (by simp [hU.cap]; omega)).mono ?_
    rintro r ⟨hKr, hjr, hUr, hcr1, hcr2⟩
    rw [hvcq] at hKr
    refine ⟨hjr, hKr, ((hU.comp (Unchanged.charge q 1 [] [] [] [])).comp hUr).mono (by simp)
      (by simp) (by intro a; simp) (by intro a; simp), by simp at hcr1; omega, ?_⟩
    simp at hcr2; rw [Nat.mul_succ]; omega
  · refine ⟨by simp [hj, (hU.wreg "b8.p" (by decide)).trans hpr, fit, show 0 < q.cap by
      rw [hU.cap]; omega], ?_⟩
    -- sl.i := b8.sBp; slot := K8
    apply runs_seq
    apply wp_sound
    rw [wp_wset_of (a := iBp) (by simp [(hU.wreg "b8.sBp" (by decide)).trans hiBp])]
    set q5 := ((q.charge 1).setW "sl.i" iBp).charge 1 with hq5
    have hU5 : Unchanged st q5 [] [] b8W b8V :=
      ((hU.comp (Unchanged.charge q 1 [] [] [] [])).comp (by simp [hq5, unch_setW] :
        Unchanged (q.charge 1) q5 [] [] ["sl.i"] [])).mono (by simp) (by simp) (by decide)
        (by decide)
    have hK5 : WHolds q5 K8 "b8.kf" H (vc st) (pmin B d piv p) :=
      (WHolds.charge' hK 1).of_unchanged (by simp [hq5, unch_setW] : Unchanged (q.charge 1) q5 [] []
        ["sl.i"] []) (by decide) (by decide) (by decide)
    have hlBp5 : SlotLens q5 iBp := by
      have e := fun a (ha : a ∈ slotW) => (hU5.warr a (by simp)).2
      exact ⟨by rw [(hU5.varr "sl.l" (by simp)).2]; exact hlBp.l,
        by rw [e "sl.h" (by simp [slotW])]; exact hlBp.h, by rw [e "sl.v" (by simp [slotW])]; exact hlBp.v,
        by rw [e "sl.e" (by simp [slotW])]; exact hlBp.e, by rw [e "sl.r" (by simp [slotW])]; exact hlBp.r,
        by rw [e "sl.f" (by simp [slotW])]; exact hlBp.f⟩
    refine (storeSlot_spec K8 "b8.kf" q5 (by simp [hq5]) hlBp5 hK5).mono ?_
    rintro r ⟨hSr, hoth, hUr, hcr⟩
    rw [pmin_full] at hSr
    have hUst : Unchanged st r slotW ["sl.l"] b8W b8V :=
      (hU5.comp hUr).mono (by simp) (by simp) (by simp) (by simp)
    refine ⟨hSr, hL.of_unchanged hUst (by decide) (by decide) (by simp [hq5] at hcr ⊢; omega),
      fun j hj => ?_, hUst, ?_⟩
    · obtain ⟨h1, h2⟩ := hoth j hj
      refine ⟨by rw [h1, (hU5.varr "sl.l" (by simp)).1], fun a ha => by
        rw [h2 a ha, (hU5.warr a (by simp)).1]⟩
    · simp [hq5] at hcr; omega

end Frontier.CHD.SpineLab
