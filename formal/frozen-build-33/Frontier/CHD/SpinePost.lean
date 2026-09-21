import Frontier.CHD.SpineIter
import Frontier.CHD.SpineA
import Frontier.CHD.ReselectRAM
import Frontier.CHD.WinScanF

/-!
# SpinePost — the second half of an iteration of the main loop (agent-06, B-L4, NON-GATE)

From agent-08's hand-off state `PostCall` (after the recursive call and `lvlUp`), the program
`merge ; removeU delB gDel ; scan ; reselect cmp ins ; appendU copyBp ; empty` (BM.14–BM.24 and
BM.9's emptiness bit) ends in `LoopRep` of the successor configuration `⟨i+1, nextD …, φ1⟩`, with the
remaining premises of `SpineBridgeD.IterRelD` (the lists `lUi`, `L'`, `lres` and `Reselect`).

* `postA`: the Layer-A facts this half needs, from the sub-call's `SimSub`/`GoodSub` (as in
  agent-01's `stepD_inv`): the returned vertices are complete and finite, disjoint from `U`, the old
  `U` keeps its labels, the child's labels are walks below the loop labels.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamSpine

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.RamLevel
  Frontier.CHD.BM Frontier.CHD.RamBaseCase Frontier.CHD.LabTab WExpr Stmt

/-! ## Layer A -/

section layerA

variable {G : Graph} {s : Fin G.n} {ops : DOps G s} {Φ Ω : Type}
  {B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {p : ℕ}
  {P0 : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {B'0 : WLab G s}

/-- **The Layer-A facts of the second half** of an iteration. -/
theorem postA (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W)
    {τ : ℕ → ℕ} {Inv : Φ → Prop} {Mf : ℕ → ℕ}
    {subD : SubRelD G s Φ Ω} {subC : SubRelC G s Φ Ω} {l : ℕ}
    (hsimsub : SimSub G s ops τ Inv Mf l subD subC) (hsubC : GoodSub G s τ Inv l subC)
    {f0 : ℕ} {L0 : LiveM G s} {c : LoopCfgD G s Φ p}
    (hA : ALoop ops Inv Mf l B S d0 d1 P0 B'0 f0 L0 c) (hne : ¬ (c.cs.g.view c.cs.Dc).IsEmpty)
    {T : ℕ} {ks : List (Fin G.n)} {Bi : WLab G s} {g1 : DGl G s} {Dc1 : DStrM G s} {cp : ℕ}
    (hpull : pullC ops T c.cs.g c.cs.Dc = (ks, Bi, g1, Dc1, cp))
    {B'i : WLab G s} {Ui : Finset (Fin G.n)} {Dci : DStrM G s} {d1' : Labels G s} {φ1 : Φ}
    {g2 : DGl G s} {lg : Log G s Ω}
    (hsubD : subD c.cs.B' Bi (BM.expand c.cs.lit ks.toFinset Bi) c.cs.d c.φ g1 (B'i, Ui, Dci, d1') φ1 g2 lg) :
    (∀ u ∈ Ui, d1' u = dis (s := s) u ∧ d1' u ≠ ⊤) ∧ Disjoint Ui c.cs.U ∧
      (∀ u ∈ c.cs.U, d1' u = c.cs.d u) ∧ WalkInv d1' ∧ (∀ v, d1' v ≤ c.cs.d v) ∧ Bi ≤ B ∧
      (∀ j, ∀ y ∈ c.cs.P j, d1' y < B) ∧
      (∀ e ∈ DB.liveVals g2.L Dc1.blocks, Dci.Bd ≤ e.val) ∧
      (∀ b ∈ Dc1.blocks.tail, ((Dci.Bd : WLab G s) : WithBot (WLab G s)) < b.sep) ∧
      Dci.Bd ≤ Dc1.Bd ∧ (ops.merge T Dc1 Dci).1.Bd = B := by
  obtain ⟨hsp, hlowdis, hBle, hK1, habove, -⟩ :=
    childPre (T := T) hpre hfp hA.linv hA.sinv hA.kinj hne hpull
  obtain ⟨hPS, -, hS1, -, -, -, hlive1, hsep1, -, -⟩ := BM.pull_sim hA.sinv hA.kinj hpull
  have hPS' : PullSpec c.cs.lit.D B ks.toFinset Bi (g1.view Dc1) := hPS
  obtain ⟨lgi, hsubCi, -, hDP⟩ := hsimsub c.cs.B' Bi (BM.expand c.cs.lit ks.toFinset Bi) c.cs.d c.φ g1
    (B'i, Ui, Dci, d1') φ1 g2 lg hsp hA.inv hlowdis hBle hK1 habove hsubD
  have hfc : DB.FreshChange g1.fresh g1.L g2.L := hDP.chg.freshChange
  have hm1 : ∀ e ∈ DB.liveVals g2.L Dc1.blocks, Dci.Bd ≤ e.val := by
    intro e he
    rw [hDP.sinv.Bd]
    obtain ⟨⟨b, hb, heb⟩, hl⟩ := DB.mem_liveVals.mp he
    have hid : e.id < g1.fresh := hS1.fr e (DB.mem_allEnts.mpr ⟨b, hb, heb⟩)
    exact hlive1 e (DB.mem_liveVals.mpr ⟨⟨b, hb, heb⟩, isLive_of_freshChange hfc hid hl⟩)
  have hm2 : ∀ b ∈ Dc1.blocks.tail, ((Dci.Bd : WLab G s) : WithBot (WLab G s)) < b.sep := by
    rw [hDP.sinv.Bd]; exact hsep1
  have hm3 : Dci.Bd ≤ Dc1.Bd := by rw [hDP.sinv.Bd, hS1.Bd]; exact hPS.bound
  have hm4 : (ops.merge T Dc1 Dci).1.Bd = B := by rw [(ops.merge_M T Dc1 Dci).2, hS1.Bd]
  have hsubCi' : subC c.cs.lit.B' Bi (BM.expand c.cs.lit ks.toFinset Bi) c.cs.lit.d c.φ
      (B'i, Ui, g2.view Dci, d1') φ1 lgi := hsubCi
  obtain ⟨hpost, -, -⟩ := hsubC _ _ _ _ _ _ _ _ hsp hA.inv hlowdis hBle hsubCi'
  have hwalk : WalkInv d1' := hpost.walk
  have hmono : ∀ v, d1' v ≤ c.cs.d v := hpost.mono
  refine ⟨fun u hu => ?_, ?_, fun u hu => ?_, hwalk, hmono, hPS'.bound, fun j y hy => ?_, hm1, hm2, hm3,
    hm4⟩
  · have hc : d1' u = dis (s := s) u := hpost.U_complete u hu
    have hlt : dis (s := s) u < B'i := ((hpost.U_eq u).mp hu).1
    exact ⟨hc, by rw [hc]; exact _root_.ne_top_of_lt hlt⟩
  · rw [Finset.disjoint_left]
    intro v hv hvU
    have hv' : v ∈ Utilde Bi (BM.expand c.cs.lit ks.toFinset Bi : Set (Fin G.n)) :=
      utilde_mono_bound hpost.B'_le ((hpost.U_eq v).mp hv)
    exact (UKi_sub hA.linv hPS' hv').2.1 hvU
  · have hc : c.cs.d u = dis (s := s) u := hA.linv.U_complete u hu
    exact le_antisymm (hmono u) (by rw [hc]; exact hwalk.sound u)
  · have hyS : y ∈ S := (hfp.groups j).2 (hA.linv.Psub j hy)
    exact lt_of_le_of_lt ((hmono y).trans ((hA.linv.mono y).trans (hfp.le y))) (hpre.inRange y hyS)

end layerA

/-! ## Program text of the second half -/

/-- BM.24's slot copy `B'[lvl] := B'[lvl-1]` (the child's returned bound). -/
def copyBp : Stmt :=
  seq (slotAtC 2) (seq (loadSlot KC "sp.cf") (seq (slotAt 2) (storeSlot KC "sp.cf")))

/-- The bound blocks of the window scan: `scB` holds `B`, `scBi` holds `B_i` (the `lo` bound). -/
def scB : LReg := ⟨"sc.bl", "sc.bh", "sc.bv", "sc.be", "sc.br"⟩
def scBi : LReg := ⟨"sc.ol", "sc.oh", "sc.ov", "sc.oe", "sc.or"⟩

/-- The word registers of the scan blocks (flags included). -/
def scRegs : List String :=
  ["sc.bh", "sc.bv", "sc.be", "sc.br", "sc.bf", "sc.oh", "sc.ov", "sc.oe", "sc.or", "sc.of"]

/-- BM.19–21 with its register setup: `scB := slot B[lvl]`, `scBi := slot B_i[lvl]`,
`lab.uselo := 1`, then agent-02's `winScanD`. -/
def scanP (ins : Stmt) : Stmt :=
  seq (slotAt 0) (seq (loadSlot scB "sc.bf") (seq (slotAt 3) (seq (loadSlot scBi "sc.of")
    (seq (wset "lab.uselo" (lit 1)) (WinScan.winScanD ins scB "sc.bf" scBi "sc.of")))))

/-- **The second half of an iteration** (after `lvlUp`): BM.14 merge, BM.15–18, BM.19–21,
BM.23, BM.24, then BM.9's emptiness bit. -/
def postProg (merge delB ins empty cmp : Stmt) : Stmt :=
  seq (seq merge (seq (removeU delB gDel) (seq (scanP ins)
    (seq (reselect cmp ins) (appendU copyBp))))) empty

/-! ## BM.24's slot copy -/

section copyBp

variable {G : Graph} {s : Fin G.n}

/-- **`copyBp`**: slot `B'[l] := B'[l-1]`; all other slots are kept. -/
theorem copyBp_spec (st : State ℝ≥0) {l : ℕ} (hl : st.w "lvl" = l)
    (hsl1 : SlotLens st (slotBp (l - 1))) (hsl2 : SlotLens st (slotBp l)) {H : Hist G}
    {V : Fin G.n → ℕ} {b : WLab G s} (hb : SlotHolds st (slotBp (l - 1)) H V b)
    (hc : 4 * l + 7 < st.cap) :
    Runs realOps copyBp st (fun r => SlotHolds r (slotBp l) H V b ∧
      (∀ j, j ≠ slotBp l → r.va "sl.l" j = st.va "sl.l" j ∧ ∀ a ∈ slotW, r.wa a j = st.wa a j) ∧
      Unchanged st r slotW ["sl.l"] ("sl.i" :: "sp.cf" :: KC.ws) [KC.l] ∧ r.wlen = st.wlen ∧
      r.vlen = st.vlen ∧ r.cost = st.cost + 14) := by
  -- 1–2: `KC := slot B'[l-1]`
  refine runs_seq (runs_wset (a := slotBp (l - 1)) (by
    rw [show slotBp (l - 1) = 4 * (l - 1) + 2 from rfl]
    exact evalW_slotAtC hl (by omega)) ?_)
  set s1 := (st.setW "sl.i" (slotBp (l - 1))).charge 1 with hs1
  have hU1 : Unchanged st s1 [] [] ["sl.i"] [] := unch_setW st _ (by simp)
  refine runs_seq ((loadSlot_spec KC "sp.cf" slotFresh_KC s1 (by simp [hs1, State.setW, State.charge])
    ⟨hsl1.l, hsl1.h, hsl1.v, hsl1.e, hsl1.r, hsl1.f⟩
    (hb.of_unchanged hU1 (by simp) (by simp))).mono ?_)
  rintro s2 ⟨hW2, hU2, hc2⟩
  have hl2 : s2.w "lvl" = l := by
    rw [hU2.wreg _ (by simp [KC, LReg.ws])]; simp [hs1, State.setW, State.charge, hl]
  -- 3–4: `slot B'[l] := KC`
  refine runs_seq (runs_wset (a := slotBp l) (by
    rw [evalW_slotAt hl2 (by rw [hU2.cap, hU1.cap]; omega)]; rfl) ?_)
  set s3 := (s2.setW "sl.i" (slotBp l)).charge 1 with hs3
  have hU3 : Unchanged s2 s3 [] [] ["sl.i"] [] := unch_setW s2 _ (by simp)
  have e2w : s2.wlen = st.wlen :=
    funext fun a => (hU2.warr a (by simp)).2.trans (hU1.warr a (by simp)).2
  have e2v : s2.vlen = st.vlen :=
    funext fun a => (hU2.varr a (by simp)).2.trans (hU1.varr a (by simp)).2
  have hsl3 : SlotLens s3 (slotBp l) := by
    have e : s3.wlen = st.wlen := by rw [show s3.wlen = s2.wlen from rfl, e2w]
    have e' : s3.vlen = st.vlen := by rw [show s3.vlen = s2.vlen from rfl, e2v]
    exact ⟨by rw [e']; exact hsl2.l, by rw [e]; exact hsl2.h, by rw [e]; exact hsl2.v,
      by rw [e]; exact hsl2.e, by rw [e]; exact hsl2.r, by rw [e]; exact hsl2.f⟩
  refine (DGlob.Runs.keep_len (storeSlot_spec KC "sp.cf" s3
    (by simp [hs3, State.setW, State.charge]) hsl3
    (hW2.of_unchanged hU3 (by simp [KC, LReg.ws]) (by simp [KC]) (by simp)))
    (by simp [DGlob.NoAlloc, storeSlot])).mono ?_
  rintro r ⟨⟨hS4, hF4, hU4, hc4⟩, hwl4, hvl4⟩
  refine ⟨hS4, fun j hj => ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨e1, e2⟩ := hF4 j hj
    refine ⟨by rw [e1, show s3.va = s2.va from rfl, (hU2.varr "sl.l" (by simp [KC])).1]; rfl,
      fun a ha => by rw [e2 a ha, show s3.wa = s2.wa from rfl, (hU2.warr a (by simp)).1]; rfl⟩
  · exact (((hU1.mono (by simp) (by simp) (by simp) (by simp)).trans
      (hU2.mono (by simp) (by simp) (by simp) (by simp))).trans
      (hU3.mono (by simp) (by simp) (by simp) (by simp))).trans
      (hU4.mono (List.Subset.refl _) (List.Subset.refl _) (by simp) (by simp))
  · exact funext fun a => (hwl4 a).trans (by rw [show s3.wlen = s2.wlen from rfl, e2w])
  · exact funext fun a => (hvl4 a).trans (by rw [show s3.vlen = s2.vlen from rfl, e2v])
  · rw [hc4]; simp only [hs3, State.charge_cost, State.setW_cost, hc2, hs1]

end copyBp

/-! ## The contract of the second half: hygiene -/

section hyg

variable {G : Graph} {s : Fin G.n} {T : ℕ → ℕ} {Φ : Type}

/-- Register/array hygiene of the second half (facts about names; with `scRegs`, `sp.t`, `sp.y`,
`lab.uselo` and B-LAB's relaxation registers among the spine's reserved names they follow from the
`DLayer`/`PhiI` `_ok` fields). -/
structure PostHyg (DL : DLayer G s T) (PI : PhiI Φ) (CW : List String) : Prop where
  lab : ∀ a ∈ DL.dWR, a ∉ WinScan.rwW ++ ["lab.uselo"]
  vr : ∀ a ∈ DL.dVR, a ∉ relaxV
  blkW : ∀ a ∈ DL.dWR, a ∉ scRegs
  blkV : "sc.bl" ∉ DL.dVR ∧ "sc.ol" ∉ DL.dVR
  CWd : ∀ a ∈ CW, a ∉ DL.dWR ∧ a ∉ spRegs
  gdel : "sp.t" ∉ DL.dWR ∧ "sp.y" ∉ DL.dWR
  pA : ∀ a ∈ PI.pWA, a ∉ DL.dWA
  pR : ∀ a ∈ PI.pWR, a ∉ DL.dWR ++ CW ++ WinScan.allW ++ scRegs ++ ["lab.uselo", "sp.t", "sp.y"]

theorem DLayer.gW (DL : DLayer G s T) : "gW" ∉ DL.dVA := fun h => DL.dVA_ok _ h (by simp)

/-- The scan's `D` interface (agent-02's `DInsI.ofDLayer`). -/
abbrev PostHyg.DI {DL : DLayer G s T} {PI : PhiI Φ} {CW : List String} (hy : PostHyg DL PI CW) :
    WinScan.DInsI G s T :=
  WinScan.DInsI.ofDLayer DL DL.gW hy.lab hy.vr

theorem PostHyg.blk {DL : DLayer G s T} {PI : PhiI Φ} {CW : List String} (hy : PostHyg DL PI CW) :
    WinScan.BlkHygD hy.DI scB "sc.bf" scBi "sc.of" := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, fun a ha => ?_, ?_⟩
  · refine ⟨fun h => ?_, fun h => hy.blkW a h (by simpa [scB, scBi, LReg.ws, scRegs] using ha)⟩
    revert h; revert a; decide
  · exact ⟨hy.blkV.1, hy.blkV.2⟩

/-- Registers written by the scan setup. -/
def setupW : List String :=
  ["sl.i", "sc.bf", "sc.bh", "sc.bv", "sc.be", "sc.br", "sc.of", "sc.oh", "sc.ov", "sc.oe", "sc.or",
    "lab.uselo"]

end hyg

/-! ## BM.19–21 with its setup -/

section scan

variable {G : Graph} {s : Fin G.n} {T : ℕ → ℕ} {Φ : Type}

open Classical in
/-- **`scanP`**: the bound blocks are loaded from the slots `B[l]`, `B_i[l]`, then agent-02's
`winScanD_spec` over the `D` layer. -/
theorem scanP_spec (DL : DLayer G s T) {PI : PhiI Φ} {CW : List String} (hy : PostHyg DL PI CW)
    (hsort : WinScan.CSRSorted G s) {B Bi : WLab G s} (hBiB : Bi ≤ B) {l : ℕ}
    {Ds : ℕ → DStrM G s} {c0 : ℕ} (st : State ℝ≥0) (fs0 : RSt G s) (H0 : Hist G) (hl1 : 1 ≤ l)
    (hlv : st.w "lvl" = l) (hn : st.w "n" = G.n) (hlab : LabAt st fs0.d H0 c0)
    (hdr : DL.DR st H0 fs0.g (Function.update Ds l fs0.Dc) l) (hwk : WalkInv fs0.d)
    (hgr : GraphAt st G) (hcsr : CSRAt st G)
    (hsB : SlotHolds st (slotB l) H0 (vc st) B) (hsBi : SlotHolds st (slotBi l) H0 (vc st) Bi)
    (hslB : SlotLens st (slotB l)) (hslBi : SlotLens st (slotBi l)) (hc : 4 * l + 7 < st.cap)
    (hrow : l * G.n < st.cap) (xs : List (Fin G.n)) (hxs : xs.Nodup)
    (hU : RowRep st "U" "U.len" G.n (l - 1) (xs.map Fin.val))
    (hcomp : ∀ u ∈ xs, fs0.d u = dis (s := s) u ∧ fs0.d u ≠ ⊤)
    (hptr : ∀ u ∈ xs, WinScan.PtrAt st (fs0.d u) u Bi)
    (hptrl : G.n ≤ st.wlen "sp.ptr") (hncap : G.n + 2 ≤ st.cap) (hm : G.m + 2 ≤ st.cap)
    (hB : st.cost + 15 + (xs.length + 1) * ((G.m + 1) * WinScan.CED DL.K fs0.Dc.blocks.length + 101) ≤
      c0 + st.cap) (hBd : fs0.Dc.Bd = B)
    (hUse : ∀ L' : List (Fin G.m), L'.Nodup →
      (∀ e, e ∈ L' ↔ G.src e ∈ xs ∧ Bi ≤ ext (fs0.d (G.src e)) e ∧ ext (fs0.d (G.src e)) e < B) →
      DL.use st + (L'.foldl (relaxInsCc (dlOps G s) (T l) B (some Bi)) fs0).c ≤ DL.ucap + fs0.c) :
    Runs realOps (scanP DL.ins) st (fun r => ∃ (L' : List (Fin G.m)) (H' : Hist G),
      L'.Nodup ∧
      (∀ e, e ∈ L' ↔ G.src e ∈ xs ∧ Bi ≤ ext (fs0.d (G.src e)) e ∧ ext (fs0.d (G.src e)) e < B) ∧
      HExt H0 (vc st) H' (vc r) ∧
      WinScan.RepsD hy.DI l Ds c0 B Bi scB "sc.bf" scBi "sc.of" r
        (L'.foldl (relaxInsCc (dlOps G s) (T l) B (some Bi)) fs0) H' ∧
      (∀ u ∈ xs, WinScan.PtrAt r (fs0.d u) u B) ∧
      (∀ u : Fin G.n, u ∉ xs → r.wa "sp.ptr" u = st.wa "sp.ptr" u) ∧
      Unchanged st r (labW ++ DL.dWA ++ ["sp.ptr"]) (labV ++ DL.dVA)
        (setupW ++ WinScan.allW ++ DL.dWR) ("sc.bl" :: "sc.ol" :: relaxV ++ DL.dVR) ∧
      st.cost ≤ r.cost ∧
      r.cost + (113 + DL.K) * fs0.c ≤ st.cost + 15 +
        (113 + DL.K) * (L'.foldl (relaxInsCc (dlOps G s) (T l) B (some Bi)) fs0).c +
        38 * xs.length + 2 ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen ∧
      DL.use r + fs0.c ≤ DL.use st + (L'.foldl (relaxInsCc (dlOps G s) (T l) B (some Bi)) fs0).c) := by
  -- 1–2: `scB := slot B[l]`
  refine runs_seq (runs_wset (a := slotB l) (by rw [evalW_slotAt hlv (by omega)]; rfl) ?_)
  set s1 := (st.setW "sl.i" (slotB l)).charge 1 with hs1
  have hU1 : Unchanged st s1 [] [] ["sl.i"] [] := unch_setW st _ (by simp)
  refine runs_seq ((loadSlot_spec scB "sc.bf" ⟨by decide⟩ s1 (by simp [hs1, State.setW, State.charge])
    ⟨hslB.l, hslB.h, hslB.v, hslB.e, hslB.r, hslB.f⟩ (hsB.of_unchanged hU1 (by simp) (by simp))).mono ?_)
  rintro s2 ⟨hW2, hU2, hc2⟩
  have hU02 : Unchanged st s2 [] [] setupW ["sc.bl", "sc.ol"] :=
    (hU1.mono (by simp) (by simp) (by simp [setupW]) (by simp)).trans
      (hU2.mono (by simp) (by simp) (by simp [setupW, scB, LReg.ws]) (by simp [scB]))
  have hl2 : s2.w "lvl" = l := by rw [hU02.wreg _ (by decide)]; exact hlv
  -- 3–4: `scBi := slot B_i[l]`
  refine runs_seq (runs_wset (a := slotBi l) (by
    rw [evalW_slotAt hl2 (by rw [hU02.cap]; omega)]; rfl) ?_)
  set s3 := (s2.setW "sl.i" (slotBi l)).charge 1 with hs3
  have hU3 : Unchanged s2 s3 [] [] ["sl.i"] [] := unch_setW s2 _ (by simp)
  have hU03 : Unchanged st s3 [] [] setupW ["sc.bl", "sc.ol"] :=
    hU02.trans (hU3.mono (by simp) (by simp) (by simp [setupW]) (by simp))
  have e3w : s3.wlen = st.wlen := funext fun a => (hU03.warr a (by simp)).2
  have e3v : s3.vlen = st.vlen := funext fun a => (hU03.varr a (by simp)).2
  have hslBi3 : SlotLens s3 (slotBi l) :=
    ⟨by rw [e3v]; exact hslBi.l, by rw [e3w]; exact hslBi.h, by rw [e3w]; exact hslBi.v,
      by rw [e3w]; exact hslBi.e, by rw [e3w]; exact hslBi.r, by rw [e3w]; exact hslBi.f⟩
  refine runs_seq ((loadSlot_spec scBi "sc.of" ⟨by decide⟩ s3 (by simp [hs3, State.setW, State.charge])
    hslBi3 (hsBi.of_unchanged hU03 (by simp) (by simp))).mono ?_)
  rintro s4 ⟨hW4, hU4, hc4⟩
  have hU04 : Unchanged st s4 [] [] setupW ["sc.bl", "sc.ol"] :=
    hU03.trans (hU4.mono (by simp) (by simp) (by simp [setupW, scBi, LReg.ws]) (by simp [scBi]))
  -- 5: `lab.uselo := 1`
  refine runs_seq (runs_wset (evalW_lit_of (by rw [hU04.cap]; omega)) ?_)
  set s5 := (s4.setW "lab.uselo" 1).charge 1 with hs5
  have hU5 : Unchanged s4 s5 [] [] ["lab.uselo"] [] := unch_setW s4 _ (by simp)
  have hU05 : Unchanged st s5 [] [] setupW ["sc.bl", "sc.ol"] :=
    hU04.trans (hU5.mono (by simp) (by simp) (by simp [setupW]) (by simp))
  have hwa5 : s5.wa = st.wa := funext fun a => (hU05.warr a (by simp)).1
  have e5w : s5.wlen = st.wlen := funext fun a => (hU05.warr a (by simp)).2
  have hvc5 : vc (G := G) s5 = vc st := vc_of_unchanged hU05 (by simp)
  have hc5 : s5.cost = st.cost + 15 := by
    simp only [hs5, State.charge_cost, State.setW_cost, hc4, hs3, hc2, hs1]
  have hcap5 : s5.cap = st.cap := hU05.cap
  -- the representation at the scan's entry
  have hR5 : WinScan.RepsD hy.DI l Ds c0 B Bi scB "sc.bf" scBi "sc.of" s5 fs0 H0 := by
    refine ⟨hlab.of_unchanged hU05 (by simp) (by simp) (by omega), ?_, hwk,
      graphAt_of_unchanged hU05 (by simp) (by simp) hgr, CSRAt.of_unchanged hcsr hU05 (by simp),
      ?_, ?_, by simp [hs5], by rw [hU05.wreg _ (by decide)]; exact hlv,
      by rw [hU05.wreg _ (by decide)]; exact hn, hBd⟩
    · exact DL.frame st s5 H0 H0 _ _ l [] [] setupW ["sc.bl", "sc.ol"] hdr hU05 (by simp) (by simp)
        (fun a ha h => by
          have h1 := hy.blkW a ha
          have h2 := hy.lab a ha
          have h3 := DL.dWR_ok a ha
          simp only [setupW, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact h3 (by decide)
          all_goals first | exact h1 (by decide) | exact h2 (by decide))
        (by rw [hvc5]; exact HExt.refl _ _)
    · rw [hvc5]
      have hU25 : Unchanged s2 s5 [] [] ("sl.i" :: "sc.of" :: scBi.ws ++ ["lab.uselo"]) ["sc.ol"] :=
        ((hU3.mono (by simp) (by simp) (by simp) (by simp)).trans
          (hU4.mono (by simp) (by simp) (by simp [scBi, LReg.ws]) (by simp [scBi]))).trans
          (hU5.mono (by simp) (by simp) (by simp) (by simp))
      exact hW2.of_unchanged hU25 (by decide) (by decide) (by decide)
    · rw [hvc5]
      exact hW4.of_unchanged hU5 (by simp [scBi, LReg.ws]) (by simp [scBi]) (by simp)
  have hU5r : RowRep s5 "U" "U.len" G.n (l - 1) (xs.map Fin.val) :=
    RowRep.of_eq hU (by rw [e5w]) (by rw [e5w]) (by rw [hwa5]) (fun q _ => by rw [hwa5])
  have hptr5 : ∀ u ∈ xs, WinScan.PtrAt s5 (fs0.d u) u Bi := fun u hu => by
    have h := hptr u hu
    unfold WinScan.PtrAt WinScan.ScanStop at h ⊢
    rw [hwa5]; exact h
  have eK : hy.DI.K = DL.K := rfl
  have hsetR : ∀ a ∈ setupW, a ∉ DL.dWR := fun a ha h => by
    have h1 := hy.blkW a h
    have h2 := hy.lab a h
    have h3 := DL.dWR_ok a h
    simp only [setupW, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h3 (by decide)
    all_goals first | exact h1 (by decide) | exact h2 (by decide)
  have huse5 : DL.use s5 = DL.use st := DL.use_frame st s5 _ _ _ _ hU05 (fun a ha h => hsetR a h ha)
  refine (WinScan.winScanD_spec hy.DI hy.blk hsort hBiB
    ⟨fun h => DL.dWA_ok _ h (by decide), fun h => DL.dWA_ok _ h (by decide)⟩ s5 fs0 H0 hR5 hl1
    (by rw [hcap5]; exact hrow) xs hxs hU5r hcomp hptr5 (by rw [e5w]; exact hptrl)
    (by rw [hcap5]; exact hncap) (by rw [eK, hcap5, hc5]; omega) (by rw [hcap5]; exact hm)
    (fun L' h1 h2 => by show DL.use s5 + _ ≤ _; rw [huse5]; exact hUse L' h1 h2)).mono ?_
  rintro r ⟨L', H', hnd, hmem, hE, hR, hptrB, hrest, hwl, hFW, hclo, hrel, hwlen, hvlen, huR⟩
  rw [eK] at hrel
  have e5v : s5.vlen = st.vlen := funext fun a => (hU05.varr a (by simp)).2
  refine ⟨L', H', hnd, hmem, by rw [← hvc5]; exact hE, hR, hptrB, fun u hu => by
      rw [hrest u hu, hwa5], ?_, by omega, by omega, hwlen.trans e5w, hvlen.trans e5v,
      by rw [← huse5]; exact huR⟩
  have hFW' : Unchanged s5 r (labW ++ DL.dWA ++ ["sp.ptr"]) (labV ++ DL.dVA) (WinScan.allW ++ DL.dWR)
      (relaxV ++ DL.dVR) := hFW
  exact (hU05.mono (by simp) (by simp) (by simp) (by simp)).trans
    (hFW'.mono (by simp) (by simp) (by simp) (by simp))

end scan


/-! ## Keys and costs -/

section keys

variable {G : Graph} {s : Fin G.n}

/-- The comparison key of vertex `x` under the labels `d` (`⊤` off range). -/
noncomputable def labKey (d : Labels G s) (x : ℕ) : WLab G s :=
  if h : x < G.n then d ⟨x, h⟩ else ⊤

/-- The vertices with a finite label. -/
def labDom (d : Labels G s) (x : ℕ) : Prop := ∃ h : x < G.n, d ⟨x, h⟩ ≠ ⊤

end keys

/-- The cost factor of the second half. -/
def postK (K C : ℕ) : ℕ := C + 3 * K + 200

/-- The crude static slack of the second half (agent-02's scan clock budget and the
re-selection's comparison budget), for `nb` blocks in the level structure. -/
def postS (K C n m nb : ℕ) : ℕ :=
  (n + 1) * ((m + 1) * WinScan.CED K nb + 101) +
    (3 + 8 * n + n * (C + 8) + K * (n * (Nat.log 2 nb + 4)) + n * (K + 3))

/-! ## The contract of the second half -/

section spec

variable {G : Graph} {s : Fin G.n} {T : ℕ → ℕ} {Φ Ω : Type}

/-- The label comparison of BM.23 (`cmp`, B-LAB's `cmpTT`) for every label table in `LabAt`
form: some key representation `KR` holds, `cmp` meets agent-01's `CmpI` at the keys `labKey d`,
and `KR` survives the `D` layer's insertions. -/
def CmpFam (DL : DLayer G s T) (cmp : Stmt) (C : ℕ) (CW CV : List String) (c0 : ℕ) : Prop :=
  ∀ (d : Labels G s) (H : Hist G) (r0 : State ℝ≥0), LabAt r0 d H c0 →
    ∃ KR : State ℝ≥0 → Prop, KR r0 ∧
      RamInit.CmpI realOps cmp KR (labKey d) (labDom d) C (c0 + r0.cap) CW CV [] (RamInit.gmRegs ++ CW) ∧
      (∀ st r, KR st → Unchanged st r ("sp.gp" :: DL.dWA) DL.dVA (RamSpineU.rsRegs ++ DL.dWR) DL.dVR →
        st.cost ≤ r.cost → KR r)

/-- The fold of BM.19–21 (LoopD's `L'.foldl`), from the merged and FIX-STALE-deleted structure. -/
noncomputable abbrev postFold (T : ℕ) (B Bi : WLab G s) (Dc1 Dci : DStrM G s) (d1 : Labels G s)
    (g2 : DGl G s) (lUi : List (Fin G.n)) (L' : List (Fin G.m)) : RSt G s :=
  L'.foldl (relaxInsCc (dlOps G s) T B (some Bi)) ⟨d1, (delC g2 lUi).1, ((dlOps G s).merge T Dc1 Dci).1, 0⟩

/-- The Layer-A cost of the second half up to the window scan. -/
noncomputable def preCost (T : ℕ) (B Bi : WLab G s) (Ui : Finset (Fin G.n)) (Dc1 Dci : DStrM G s)
    (d1 : Labels G s) (g2 : DGl G s) (lUi : List (Fin G.n)) (L' : List (Fin G.m)) : ℕ :=
  ((dlOps G s).merge T Dc1 Dci).2 + (delC g2 lUi).2 + 2 * Ui.card +
    (postFold T B Bi Dc1 Dci d1 g2 lUi L').c

/-- The Layer-A cost of the second half (the part of `IterRelD`'s cost after the sub-call). -/
noncomputable def postCost (T : ℕ) (B : WLab G s) {p : ℕ} (cs : CSt G s p) (Bi : WLab G s)
    (Ui : Finset (Fin G.n)) (Dc1 Dci : DStrM G s) (d1 : Labels G s) (g2 : DGl G s)
    (lUi : List (Fin G.n)) (L' : List (Fin G.m)) (lres : List (Fin G.n)) : ℕ :=
  preCost T B Bi Ui Dc1 Dci d1 g2 lUi L' +
    (∑ j ∈ markedGroups cs.lit Ui, ((cs.P j \ Ui).card + 1)) +
    (insManyC (dlOps G s) T (postFold T B Bi Dc1 Dci d1 g2 lUi L').d lres
      (postFold T B Bi Dc1 Dci d1 g2 lUi L').g (postFold T B Bi Dc1 Dci d1 g2 lUi L').Dc).2.2

open Classical in
/-- **PostSpec: the second half of an iteration** at level `l + 1`, as a statement.  From
`PostCall` (after the recursive call and `lvlUp`) and the Layer-A context of the iteration,
`postProg` realizes the rest of one `IterRelD` step and ends in `LoopRep` of `⟨c.i + 1, nextD …, φ1⟩`,
with the emptiness bit of the new view, at RAM cost `≤ postK · (postCost + 1)`. -/
def PostSpecStmt (DL : DLayer G s T) (PI : PhiI Φ) (LF : ℕ) (body : Stmt) (τf Mf : ℕ → ℕ)
    (cmp : Stmt) (C : ℕ) (CW CV : List String) (Ω : Type) : Prop :=
  ∀ (c0 : ℕ), PostHyg DL PI CW → CmpFam DL cmp C CW CV c0 → WinScan.CSRSorted G s → LF ≤ DL.LT →
  -- the Layer-A context of the iteration
  ∀ {B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {p : ℕ}
    {P0 : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {B'0 : WLab G s},
    CallPre B S d0 → FPContract B S d0 d1 p P0 Q W →
  ∀ {τ : ℕ → ℕ} {Inv : Φ → Prop} {subD : SubRelD G s Φ Ω} {subC : SubRelC G s Φ Ω} {l : ℕ},
    SimSub G s (dlOps G s) τ Inv Mf l subD subC → GoodSub G s τ Inv l subC →
  ∀ {f0 : ℕ} {L0 : LiveM G s} {c : LoopCfgD G s Φ p},
    ALoop (dlOps G s) Inv Mf l B S d0 d1 P0 B'0 f0 L0 c → ¬ (c.cs.g.view c.cs.Dc).IsEmpty →
  ∀ {ks : List (Fin G.n)} {Bi : WLab G s} {g1 : DGl G s} {Dc1 : DStrM G s} {cp : ℕ},
    pullC (dlOps G s) (T (l + 1)) c.cs.g c.cs.Dc = (ks, Bi, g1, Dc1, cp) →
  ∀ {B'i : WLab G s} {Ui : Finset (Fin G.n)} {Dci : DStrM G s} {d1' : Labels G s} {φ1 : Φ}
    {g2 : DGl G s} {lg : Log G s Ω},
    subD c.cs.B' Bi (BM.expand c.cs.lit ks.toFinset Bi) c.cs.d c.φ g1 (B'i, Ui, Dci, d1') φ1 g2 lg →
  -- the machine state
  ∀ {st0 st : State ℝ≥0} {τl : ℕ} {Ds : ℕ → DStrM G s} {H : Hist G},
    PostCall DL PI LF body τf Mf st0 l B τl Ds c0 c Bi Dc1 B'i Ui Dci d1' φ1 g2 H st →
    (∀ (lUi : List (Fin G.n)) (L' : List (Fin G.m)), lUi.Nodup → lUi.toFinset = Ui →
      L'.Nodup → (∀ e, e ∈ L' ↔ G.src e ∈ Ui ∧ Bi ≤ ext (d1' (G.src e)) e ∧
        ext (d1' (G.src e)) e < B) →
      st.cost + postK DL.K C * (preCost (T (l + 1)) B Bi Ui Dc1 Dci d1' g2 lUi L' + 1) +
        postS DL.K C G.n G.m ((dlOps G s).merge (T (l + 1)) Dc1 Dci).1.blocks.length ≤ c0 + st.cap) →
    (∀ (lUi : List (Fin G.n)) (L' : List (Fin G.m)) (piv' : Fin p → Fin G.n) (lres : List (Fin G.n)),
      lUi.Nodup → lUi.toFinset = Ui → L'.Nodup →
      (∀ e, e ∈ L' ↔ G.src e ∈ Ui ∧ Bi ≤ ext (d1' (G.src e)) e ∧ ext (d1' (G.src e)) e < B) →
      Reselect c.cs.lit Ui (postFold (T (l + 1)) B Bi Dc1 Dci d1' g2 lUi L').d piv' →
      lres.Nodup → lres.toFinset = reselected c.cs.lit Ui piv' →
      DL.use st + postCost (T (l + 1)) B c.cs Bi Ui Dc1 Dci d1' g2 lUi L' lres ≤ DL.ucap) →
    Runs realOps (postProg DL.merge DL.delB DL.ins DL.empty cmp) st (fun r =>
      ∃ (lUi : List (Fin G.n)) (L' : List (Fin G.m)) (piv' : Fin p → Fin G.n) (lres : List (Fin G.n))
        (H' : Hist G),
      lUi.Nodup ∧ lUi.toFinset = Ui ∧ L'.Nodup ∧
      (∀ e, e ∈ L' ↔ G.src e ∈ Ui ∧ Bi ≤ ext (d1' (G.src e)) e ∧ ext (d1' (G.src e)) e < B) ∧
      Reselect c.cs.lit Ui (postFold (T (l + 1)) B Bi Dc1 Dci d1' g2 lUi L').d piv' ∧
      lres.Nodup ∧ lres.toFinset = reselected c.cs.lit Ui piv' ∧
      LoopRep DL PI LF body τf Mf r (l + 1) B τl Ds H' c0
        ⟨c.i + 1, nextD (dlOps G s) (T (l + 1)) B c.cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres, φ1⟩ ∧
      (r.w "sp.em" = 0 ↔ ¬ ((nextD (dlOps G s) (T (l + 1)) B c.cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv'
        lres).g.view (nextD (dlOps G s) (T (l + 1)) B c.cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv'
        lres).Dc).IsEmpty) ∧
      HExt H (vc st) H' (vc r) ∧ LFrame st0 r G.n l ∧
      (∀ x : Fin G.n, x ∉ c.cs.U ∪ Ui → r.wa "sp.ptr" x = st0.wa "sp.ptr" x) ∧
      st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + postK DL.K C *
        (postCost (T (l + 1)) B c.cs Bi Ui Dc1 Dci d1' g2 lUi L' lres + 1) ∧
      DL.use r ≤ DL.use st + postCost (T (l + 1)) B c.cs Bi Ui Dc1 Dci d1' g2 lUi L' lres)

/-- `postS` is monotone in the block count. -/
theorem postS_mono (K C n m : ℕ) {nb nb' : ℕ} (h : nb ≤ nb') : postS K C n m nb ≤ postS K C n m nb' := by
  have hl : Nat.log 2 nb ≤ Nat.log 2 nb' := Nat.log_mono_right h
  have hC : WinScan.CED K nb ≤ WinScan.CED K nb' := by
    unfold WinScan.CED; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
  unfold postS
  have h1 : (m + 1) * WinScan.CED K nb ≤ (m + 1) * WinScan.CED K nb' := Nat.mul_le_mul_left _ hC
  have h2 : K * (n * (Nat.log 2 nb + 4)) ≤ K * (n * (Nat.log 2 nb' + 4)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
  have h3 : (n + 1) * ((m + 1) * WinScan.CED K nb + 101) ≤ (n + 1) * ((m + 1) * WinScan.CED K nb' + 101) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

end spec

end Frontier.CHD.RamSpine
