import Frontier.CHD.WinScanF

/-!
# RelW — BM.27–28 for the level body (agent-01's `RelWB` black box; agent-02, NON-GATE)

`relW ins` loads the bound slots `B[lvl]` (block `KWb`) and `B'[lvl]` (the `lo` bound `B'_f`,
block `KWl`), sets `lab.uselo := 1`, and runs the head-start scan `wScanD` on the `W'` row
(`Wp`/`Wp.len`, row `lvl`).  `relW_spec` gives agent-01's `RelWB` post (Layer-A list `L` =
the full CSR ranges of `W'`, an enumeration of their out-edges) under the premises that make it
true: completeness of `W'` (else a later relaxation into an already scanned `W'` vertex would
stale its pointer), sorted CSR ranges, the graph/CSR representation, and the static budget.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.WinScan

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.MLab Frontier.CHD.LabTab
  Frontier.CHD.DIns Frontier.CHD.RelaxIns Frontier.CHD.RamBaseCase WExpr Stmt

variable {G : Graph} {s : Fin G.n}

/-- The bound block `B` of the `W'` relaxation. -/
def KWb : LReg := ⟨"rw.bl", "rw.bh", "rw.bv", "rw.be", "rw.br"⟩
/-- The `lo` block `B'_f` of the `W'` relaxation. -/
def KWl : LReg := ⟨"rw.ll", "rw.lh", "rw.lv", "rw.le", "rw.lr"⟩

/-- `lvl * n + e` (current row). -/
def crw (e : WExpr) : WExpr := add (mul (var "lvl") (var "n")) e

/-- **BM.27–28** as the level body calls it. -/
def relW (ins : Stmt) : Stmt :=
  seq (wset "sl.i" (mul (lit 4) (var "lvl")))
  (seq (loadSlot KWb "rw.bf")
  (seq (wset "sl.i" (add (mul (lit 4) (var "lvl")) (lit 2)))
  (seq (loadSlot KWl "rw.lf")
  (seq (wset "lab.uselo" (lit 1))
       (wScanD (load "Wp.len" (var "lvl")) (load "Wp" (crw (var "sp.i"))) ins KWb "rw.bf" KWl
         "rw.lf")))))

/-- Registers `relW` writes besides the D layer's. -/
def relWRegs : List String :=
  allW ++ ["sl.i", "lab.uselo", "rw.bl", "rw.bh", "rw.bv", "rw.be", "rw.br", "rw.bf", "rw.ll",
    "rw.lh", "rw.lv", "rw.le", "rw.lr", "rw.lf"]

theorem SlotLens.of_len {st r : State ℝ≥0} {i : ℕ} (h : SlotLens st i)
    (hw : r.wlen = st.wlen) (hv : r.vlen = st.vlen) : SlotLens r i :=
  ⟨by rw [hv]; exact h.l, by rw [hw]; exact h.h, by rw [hw]; exact h.v, by rw [hw]; exact h.e,
    by rw [hw]; exact h.r, by rw [hw]; exact h.f⟩

set_option maxHeartbeats 1000000 in
open Classical in
/-- **BM.27–28 for the level body.** -/
theorem relW_spec {T : ℕ → ℕ} (DI : DInsI G s T) (hsort : CSRSorted G s)
    (hWd : "Wp" ∉ DI.dWA ∧ "Wp.len" ∉ DI.dWA)
    (hKd : ∀ a ∈ ["rw.bl", "rw.bh", "rw.bv", "rw.be", "rw.br", "rw.bf", "rw.ll", "rw.lh", "rw.lv",
      "rw.le", "rw.lr", "rw.lf", "sl.i"], a ∉ DI.dWR)
    (hKdl : "rw.bl" ∉ DI.dVR ∧ "rw.ll" ∉ DI.dVR)
    (st : State ℝ≥0) (l : ℕ) (B B'f : WLab G s) (d : Labels G s) (g : BM.DGl G s)
    (Dc : BM.DStrM G s) (Ds : ℕ → BM.DStrM G s) (H : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ)
    (lW : List (Fin G.n)) (hlv : st.w "lvl" = l) (hn : st.w "n" = G.n) (hL : LabAt st d H c0)
    (hw : WalkInv d) (hD : DI.DR st H g (Function.update Ds l Dc) l)
    (hWp : RamLevel.RowRep st "Wp" "Wp.len" G.n l (lW.map Fin.val)) (hnd : lW.Nodup)
    (hB : SlotHolds st (slotB l) H (vc st) B) (hBf : SlotHolds st (slotBp l) H (vc st) B'f)
    (hsl : SlotLens st (slotB l) ∧ SlotLens st (slotBp l))
    (hcomp : ∀ u ∈ lW, d u = dis (s := s) u ∧ d u ≠ ⊤)
    (hg : GraphAt st G) (hcsr : CSRAt st G)
    (hptrl : G.n ≤ st.wlen "sp.ptr") (hncap : G.n + 2 ≤ st.cap) (hm : G.m + 2 ≤ st.cap)
    (hrow : (l + 1) * G.n < st.cap) (hsli : 4 * l + 8 < st.cap)
    (hbud : st.cost + 30 + (lW.length + 1) * ((G.m + 1) * CED DI.K Dc.blocks.length + 101) ≤
      c0 + st.cap) (hBd : Dc.Bd = B)
    (hUse : ∀ L : List (Fin G.m), BM.Enumerates G L lW.toFinset →
      DI.use st + (L.foldl (BM.relaxInsCc (BM.dlOps G s) (T l) B (some B'f)) ⟨d, g, Dc, 0⟩).c ≤
        DI.ucap) :
    Runs realOps (relW DI.ins) st (fun r => ∃ (L : List (Fin G.m))
      (H' : Fin G.n → ℕ → List (Fin G.m)),
      BM.Enumerates G L lW.toFinset ∧
      LabAt r (L.foldl (BM.relaxInsCc (BM.dlOps G s) (T l) B (some B'f)) ⟨d, g, Dc, 0⟩).d H' c0 ∧
      HExt H (vc st) H' (vc r) ∧
      DI.DR r H' (L.foldl (BM.relaxInsCc (BM.dlOps G s) (T l) B (some B'f)) ⟨d, g, Dc, 0⟩).g
        (Function.update Ds l
          (L.foldl (BM.relaxInsCc (BM.dlOps G s) (T l) B (some B'f)) ⟨d, g, Dc, 0⟩).Dc) l ∧
      (∀ u ∈ lW, PtrAt r
        ((L.foldl (BM.relaxInsCc (BM.dlOps G s) (T l) B (some B'f)) ⟨d, g, Dc, 0⟩).d u) u B) ∧
      (∀ x : Fin G.n, x ∉ lW → r.wa "sp.ptr" x = st.wa "sp.ptr" x) ∧
      Unchanged st r (labW ++ DI.dWA ++ ["sp.ptr"]) (labV ++ DI.dVA) (relWRegs ++ DI.dWR)
        (relaxV ++ ["rw.bl", "rw.ll"] ++ DI.dVR) ∧
      r.wlen = st.wlen ∧ r.vlen = st.vlen ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + (113 + DI.K) *
        ((L.foldl (BM.relaxInsCc (BM.dlOps G s) (T l) B (some B'f)) ⟨d, g, Dc, 0⟩).c + 1) +
        38 * (lW.length + 1) + 30 ∧
      DI.use r ≤ DI.use st +
        (L.foldl (BM.relaxInsCc (BM.dlOps G s) (T l) B (some B'f)) ⟨d, g, Dc, 0⟩).c) := by
  have h1c : 1 < st.cap := by omega
  have hxl : lW.length ≤ G.n := by
    have := hnd.length_le_card; rwa [Fintype.card_fin] at this
  -- `sl.i := 4 lvl`
  apply runs_seq
  refine runs_wset_val (evalW_mul_of' (x := 4) (y := l) (evalW_lit_of (by omega))
    (by rw [evalW_var, hlv]) (by omega)) (fun q1 hsl1 hU1 hc1 => ?_)
  -- load `B`
  apply runs_seq
  have hlen1 := lenEq_of_unch hU1
  refine (loadSlot_spec KWb "rw.bf" ⟨by decide⟩ q1 hsl1 (SlotLens.of_len hsl.1 hlen1.1 hlen1.2)
    (hB.of_unchanged hU1 (by simp) (by simp))).mono ?_
  rintro q2 ⟨hKb2, hU2, hc2⟩
  have hlen2 := lenEq_of_unch hU2
  -- `sl.i := 4 lvl + 2`
  apply runs_seq
  have hlv2 : q2.w "lvl" = l := by
    rw [hU2.wreg "lvl" (by decide), hU1.wreg "lvl" (by decide)]; exact hlv
  have hcap2 : q2.cap = st.cap := hU2.cap.trans hU1.cap
  refine runs_wset_val (evalW_add_of (x := 4 * l) (y := 2) (evalW_mul_of' (x := 4) (y := l)
    (evalW_lit_of (by omega)) (by rw [evalW_var, hlv2]) (by omega)) (evalW_lit_of (by omega))
    (by omega)) (fun q3 hsl3 hU3 hc3 => ?_)
  -- load `B'f`
  apply runs_seq
  have hlen3 := lenEq_of_unch hU3
  have hU13 : Unchanged st q3 [] [] (["sl.i"] ++ ("rw.bf" :: KWb.ws) ++ ["sl.i"]) ([] ++ [KWb.l] ++ []) :=
    (hU1.comp hU2).comp hU3
  refine (loadSlot_spec KWl "rw.lf" ⟨by decide⟩ q3 hsl3
    (SlotLens.of_len hsl.2 (hlen3.1.trans (hlen2.1.trans hlen1.1))
      (hlen3.2.trans (hlen2.2.trans hlen1.2)))
    (hBf.of_unchanged hU13 (by simp) (by simp))).mono ?_
  rintro q4 ⟨hKl4, hU4, hc4⟩
  -- `lab.uselo := 1`
  apply runs_seq
  have hcap4 : q4.cap = st.cap := hU4.cap.trans (hU3.cap.trans hcap2)
  refine runs_wset_val (evalW_lit_of (by rw [hcap4]; omega)) (fun q5 hul5 hU5 hc5 => ?_)
  -- the start of the scan
  have hU05 : Unchanged st q5 [] [] (["sl.i"] ++ ("rw.bf" :: KWb.ws) ++ ["sl.i"] ++
      ("rw.lf" :: KWl.ws) ++ ["lab.uselo"]) ([] ++ [KWb.l] ++ [] ++ [KWl.l] ++ []) :=
    (hU13.comp hU4).comp hU5
  have hlen5 : q5.wlen = st.wlen ∧ q5.vlen = st.vlen := lenEq_of_unch hU05
  have hvc5 : vc (G := G) q5 = vc st := vc_of_unchanged hU05 (by simp)
  have hc5' : q5.cost = st.cost + 15 := by omega
  have hlab : ∀ a ∈ (["sl.i"] ++ ("rw.bf" :: KWb.ws) ++ ["sl.i"] ++ ("rw.lf" :: KWl.ws) ++
      ["lab.uselo"]), a ∉ DI.dWR := by
    intro a ha hd
    have : a ∈ ["rw.bl", "rw.bh", "rw.bv", "rw.be", "rw.br", "rw.bf", "rw.ll", "rw.lh", "rw.lv",
        "rw.le", "rw.lr", "rw.lf", "sl.i"] ∨ a = "lab.uselo" := by
      simp only [KWb, KWl, LReg.ws, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at ha ⊢
      tauto
    rcases this with h | h
    · exact hKd a h hd
    · subst h; exact DI.hwr _ hd (by decide)
  have hlabV : ∀ a ∈ ([] ++ [KWb.l] ++ [] ++ [KWl.l] ++ []), a ∉ DI.dVR := by
    intro a ha hd
    simp only [KWb, KWl, List.nil_append, List.append_nil, List.cons_append, List.mem_cons,
      List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact hKdl.1 hd
    · exact hKdl.2 hd
  have hR5 : RepsD DI l Ds c0 B B'f KWb "rw.bf" KWl "rw.lf" q5 ⟨d, g, Dc, 0⟩ H :=
    ⟨hL.of_unchanged hU05 (by simp) (by simp) (by omega),
      DI.frame st q5 H H g _ l [] [] _ _ hD hU05 (by simp) (by simp) hlab hlabV
        (by rw [hvc5]; exact HExt.refl _ _), hw,
      graphAt_of_unchanged hU05 (by simp) (by simp) hg, CSRAt.of_unchanged hcsr hU05 (by simp),
      by
        rw [hvc5]
        exact hKb2.of_unchanged ((hU3.comp hU4).comp hU5) (by decide) (by decide) (by decide),
      by
        rw [hvc5]
        exact hKl4.of_unchanged hU5 (by decide) (by decide) (by decide),
      by rw [hul5]; exact one_ne_zero,
      by rw [hU05.wreg "lvl" (by decide)]; exact hlv, by rw [hU05.wreg "n" (by decide)]; exact hn,
      hBd⟩
  have hy : BlkHygD DI KWb "rw.bf" KWl "rw.lf" :=
    ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
      fun a ha => ⟨by revert a; decide, fun hd => hKd a (by
        simp only [KWb, KWl, LReg.ws, List.mem_append, List.mem_cons, List.not_mem_nil,
          or_false] at ha ⊢; tauto) hd⟩, hKdl⟩
  have hcap5 : q5.cap = st.cap := hU05.cap
  -- the row expressions
  have hlenE : ∀ r, FrameWD DI q5 r → evalW r (load "Wp.len" (var "lvl")) = some lW.length := by
    intro r hr
    have hlv' : r.w "lvl" = l := by rw [hr.reg (by decide) (by decide), hU05.wreg "lvl" (by decide)]; exact hlv
    have hWl := hr.arr (a := "Wp.len") (by decide) hWd.2
    have hWl0 := hU05.warr "Wp.len" (by simp)
    rw [evalW_load_of (j := l) (by rw [evalW_var, hlv']) (by rw [hWl.2, hWl0.2]; exact hWp.2.2.1),
      hWl.1, hWl0.1, hWp.2.2.2.1, List.length_map]
  have helemE : ∀ r (i : ℕ) (hi : i < lW.length), FrameWD DI q5 r → r.w "sp.i" = i →
      evalW r (load "Wp" (crw (var "sp.i"))) = some (lW[i] : ℕ) := by
    intro r i hi hr hri
    have hlv' : r.w "lvl" = l := by rw [hr.reg (by decide) (by decide), hU05.wreg "lvl" (by decide)]; exact hlv
    have hn' : r.w "n" = G.n := by rw [hr.reg (by decide) (by decide), hU05.wreg "n" (by decide)]; exact hn
    have hWa := hr.arr (a := "Wp") (by decide) hWd.1
    have hWa0 := hU05.warr "Wp" (by simp)
    have hcapr : r.cap = st.cap := (Unchanged.cap hr).trans hcap5
    have hwW : (l + 1) * G.n ≤ st.wlen "Wp" := hWp.2.1
    have hsplit : (l + 1) * G.n = l * G.n + G.n := Nat.succ_mul l G.n
    have e2 : evalW r (mul (var "lvl") (var "n")) = some (l * G.n) :=
      evalW_mul_of' (by rw [evalW_var, hlv']) (by rw [evalW_var, hn']) (by omega)
    have e3 : evalW r (crw (var "sp.i")) = some (l * G.n + i) :=
      evalW_add_of e2 (by rw [evalW_var, hri]) (by omega)
    rw [evalW_load_of e3 (by rw [hWa.2, hWa0.2]; omega), hWa.1, hWa0.1,
      hWp.2.2.2.2 i (by simpa using hi), List.getElem_map]
  have huse5 : DI.use q5 = DI.use st := DI.use_frame st q5 _ _ _ _ hU05 hlab
  refine (wScanD_spec DI hy hsort _ _ q5 ⟨d, g, Dc, 0⟩ H hR5 lW hnd hlenE helemE hcomp
    (by rw [(hU05.warr "sp.ptr" (by simp)).2]; exact hptrl) (by rw [hcap5]; exact hncap)
    (by rw [hcap5, hc5']; simp only; omega) (by rw [hcap5]; exact hm)
    (fun L hL => by rw [huse5]; simpa using hUse L hL)).mono ?_
  rintro r ⟨H', hE, hR, hptr, hrest, hwl, hFW, hclo, hrel, hwL, hvL, huR⟩
  have hg5 : q5.wa "gSt" = st.wa "gSt" := (hU05.warr "gSt" (by simp)).1
  have hptr5 : q5.wa "sp.ptr" = st.wa "sp.ptr" := (hU05.warr "sp.ptr" (by simp)).1
  obtain ⟨-, -, hstab⟩ := foldl_invs' (T := T l) (B := B) (lo := some B'f)
    (lW.flatMap (fun u : Fin G.n => slots G (q5.wa "gSt" u) (q5.wa "gSt" ((u : ℕ) + 1))))
    ⟨d, g, Dc, 0⟩ hw
  refine ⟨lW.flatMap (fun u : Fin G.n => slots G (q5.wa "gSt" u) (q5.wa "gSt" ((u : ℕ) + 1))),
    H', fullSlots_enum (CSRAt.of_unchanged hcsr hU05 (by simp)) hnd, hR.lab,
    by rw [← hvc5]; exact hE, hR.dr, fun u hu => ?_, fun x hx => by rw [hrest x hx, hptr5],
    ?_, by rw [hwL, hlen5.1], by rw [hvL, hlen5.2], by omega, ?_,
    by rw [huse5] at huR; simpa using huR⟩
  · rw [hstab u (hcomp u hu).1]; exact hptr u hu
  · refine (hU05.comp hFW).mono ?_ ?_ ?_ ?_
    · intro a ha; simp only [List.mem_append, List.nil_append] at ha ⊢; tauto
    · intro a ha; simp only [List.mem_append, List.nil_append] at ha ⊢; tauto
    · intro a ha
      simp only [relWRegs, KWb, KWl, LReg.ws, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at ha ⊢
      tauto
    · intro a ha
      simp only [KWb, KWl, List.mem_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false, List.append_nil] at ha ⊢
      tauto
  · set F := (lW.flatMap (fun u : Fin G.n => slots G (q5.wa "gSt" u)
      (q5.wa "gSt" ((u : ℕ) + 1)))).foldl (BM.relaxInsCc (BM.dlOps G s) (T l) B (some B'f))
      ⟨d, g, Dc, 0⟩ with hF
    have hmul : (113 + DI.K) * (F.c + 1) = (113 + DI.K) * F.c + (113 + DI.K) := by ring
    have h0c : (113 + DI.K) * (⟨d, g, Dc, 0⟩ : BM.RSt G s).c = 0 := by simp
    omega

end Frontier.CHD.WinScan
