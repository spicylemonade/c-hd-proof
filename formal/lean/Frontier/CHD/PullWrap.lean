import Frontier.CHD.DPull
import Frontier.CHD.DLayerInst

/-!
# Frontier.CHD.PullWrap — the D-layer pull on `DRI` (agent-05, B-L3, NON-GATE)

`pullW` = set `ds.lv / ds.b / ds.M` from `lvl`, `dsl.base`, `dsl.M`; `DPull.pullS 1`; unlink the
pulled keys (row `lvl - 1` of `S`) from the live-key lists.  This file converts agent-04's `DRI`
into `DPull.SplitPre` (plus the extra allocation facts `PullFacts`) and back.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.PullWrap

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.DB Frontier.CHD.DIns
open Frontier.RAM.WExpr Frontier.RAM.Stmt Frontier.CHD.RamLevel Frontier.CHD.DGlob
open Frontier.RAM.SelectRAM Frontier.CHD.MLab

variable {G : Graph} {s : Fin G.n}

/-- the combined capacity fact the pull needs beyond `DRI` (to become a `DLens` field) -/
def CBig (P : DLI.DPar) (st : State ℝ≥0) : Prop :=
  (P.top + 2) * (G.n + 2) + 2 * P.ecap + 300 < st.cap

theorem bd_conv {st : State ℝ≥0} {j : ℕ} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {b : WLab G s} (h : DLI.BdHolds st j H V b) : DPull.BdHolds st j H V b := h

theorem bd_conv' {st : State ℝ≥0} {j : ℕ} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {b : WLab G s} (h : DPull.BdHolds st j H V b) : DLI.BdHolds st j H V b := h

/-- **`DRI` at the lowest active level gives the split/pull invariant** (with the level registers
set) -/
theorem splitPre_of_DRI {P : DLI.DPar} {st : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)}
    {g : BM.DGl G s} {Ds : ℕ → BM.DStrM G s} {l w0 : ℕ} (hD : DLI.DRI P st H g Ds l)
    (hsel : P.sel = selBody entLess P.psel) (hlv : st.w "ds.lv" = l)
    (hb : st.w "ds.b" = base st l) (hM : st.w "ds.M" = (Ds l).M) (hw0 : st.w "sp.w0" = w0) :
    DPull.SplitPre st H (vc st) P.bcap l (base st l) w0 g.L (Ds l)
      (recsFrom st Ds (l + 1) (P.top - l)) P.psel := by
  have hL := hD.lens
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hL.ent
  have hcap := hL.cap
  have hmc := hD.mc l le_rfl hD.lo_le
  have hstkl := hL.stkl
  have hC := hL.rowcap
  refine ⟨by simpa using hD.dl.drep 0 (Nat.zero_le _), hD.dl.recs, hD.dl.live, hD.dl.barr,
    hD.dl.bfresh, hlv, hb, hM, hw0, by rw [← hsel]; exact hD.procs, fun i hi => ?_, fun i hi => ?_,
    by omega, by omega, by omega, hL.selc, by omega, by omega⟩
  · rw [e1] at hi
    exact ⟨by rw [show entA.l = "ent.len" from rfl, e3]; exact hi, by rw [show entA.h = "ent.h" from rfl, e4]; exact hi,
      by rw [show entA.v = "ent.v" from rfl, e5]; exact hi, by rw [show entA.e = "ent.e" from rfl, e6]; exact hi,
      by rw [show entA.r = "ent.r" from rfl, e7]; exact hi⟩
  · rw [e1] at hi
    exact ⟨by rw [e2]; exact hi, lt_of_lt_of_le (hD.keys i hi) hL.live⟩

/-- **the D-layer pull**: level registers, the RAM pull, unlink the pulled keys -/
def pullW (psel : ℕ) : Stmt :=
  seq (wset "ds.lv" (var "lvl"))
  (seq (wset "ds.b" (load "dsl.base" (var "ds.lv")))
  (seq (wset "ds.M" (load "dsl.M" (var "ds.lv")))
  (seq (DPull.pullS psel)
  (seq (wset "ul.off" (mul (sub (var "lvl") (lit 1)) (var "n")))
  (seq (wset "ul.len" (load "S.len" (sub (var "lvl") (lit 1))))
       (DLI.unlinkRow "S"))))))

/-- word arrays written by `pullW` -/
def pwWA : List String := DPull.pullWA ++ ["lk.n", "lk.p"]
/-- value arrays written by `pullW` -/
def pwVA : List String := DPull.pullVA
/-- word registers written by `pullW` -/
def pwWR : List String :=
  DPull.pullWR ++ ["ds.lv", "ds.b", "ds.M", "ul.off", "ul.len", "ul.j", "kl.v", "kl.a", "kl.b"]
/-- value registers written by `pullW` -/
def pwVR : List String := DPull.pullVR

/-- cost constant of `pullW` -/
def Kpw : ℕ := DPull.Kpull + 20

/-- a structure's entry count is at most the pool counter (distinct ids below it) -/
theorem allEnts_len_le {fresh : ℕ} {D : BM.DStrM G s} (hnd : ((allEnts D.blocks).map (·.id)).Nodup)
    (hf : DB.FreshOK fresh D) : (allEnts D.blocks).length ≤ fresh := by
  have hlt : ∀ x ∈ (allEnts D.blocks).map (·.id), x < fresh := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact hf e he
  calc (allEnts D.blocks).length = ((allEnts D.blocks).map (·.id)).length := by simp
    _ = ((allEnts D.blocks).map (·.id)).toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ (Finset.range fresh).card :=
        Finset.card_le_card (fun x hx => by
          simp only [List.mem_toFinset] at hx
          simp only [Finset.mem_range]; exact hlt x hx)
    _ = fresh := Finset.card_range _

theorem pullC_eq (T : ℕ) (g : BM.DGl G s) (D : BM.DStrM G s) :
    BM.pullC (BM.dlOps G s) T g D = ((DL.pullL 1 g.L D).1, (DL.pullL 1 g.L D).2.1,
      ⟨(DL.pullL 1 g.L D).2.2.1, g.fresh⟩, (DL.pullL 1 g.L D).2.2.2.1, (DL.pullL 1 g.L D).2.2.2.2) := rfl

theorem prepCost_le (L : Live (Fin G.n) (WLab G s)) (D : BM.DStrM G s) :
    (DL.prepList L D.M 0 D.blocks).2 ≤ (DL.pullL 1 L D).2.2.2.2 := by
  unfold DL.pullL; dsimp only; omega

/-- the stack slices of the levels above `lo` lie below `lo`'s base -/
theorem base_below {st : State ℝ≥0} {Ds : ℕ → BM.DStrM G s} {lo k : ℕ}
    (hch : ∀ j < k, base st (lo + j) = base st (lo + j + 1) + (Ds (lo + j + 1)).blocks.length) :
    ∀ j, 1 ≤ j → j ≤ k → base st (lo + j) + (Ds (lo + j)).blocks.length ≤ base st lo := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
    intro _ hj
    have hc := hch j (by omega)
    rw [show lo + j + 1 = lo + (j + 1) by omega] at hc
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0; simp at hc ⊢; omega
    · have := ih h0 (by omega)
      omega

/-- the records of level `lo + j` belong to `recsFrom … lo n` -/
theorem mem_recsFrom_of {st : State ℝ≥0} {Ds : ℕ → BM.DStrM G s} :
    ∀ (n lo j : ℕ), j < n → ∀ p ∈ DList.recsOf st (base st (lo + j)) (Ds (lo + j)).blocks,
      p ∈ recsFrom st Ds lo n
  | 0, _, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, lo, j, hj, p, hp => by
    show p ∈ DList.recsOf st (base st lo) (Ds lo).blocks ++ recsFrom st Ds (lo + 1) n
    rcases j with _ | j
    · exact List.mem_append_left _ (by simpa using hp)
    · refine List.mem_append_right _ (mem_recsFrom_of n (lo + 1) j (by omega) p ?_)
      rw [show lo + 1 + j = lo + (j + 1) by omega]; exact hp

/-- transport of a level's representation along cell-level equalities -/
theorem drep_transport {st r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap lv bse : ℕ} {D : BM.DStrM G s} (h : DRep st H V bcap lv bse D)
    (hsz : r.wa "dsl.sz" lv = st.wa "dsl.sz" lv) (hszl : r.wlen "dsl.sz" = st.wlen "dsl.sz")
    (hstkl : r.wlen "dsl.stk" = st.wlen "dsl.stk")
    (hstk : ∀ x, x < bse + D.blocks.length → r.wa "dsl.stk" x = st.wa "dsl.stk" x)
    (hblk : ∀ p ∈ DList.recsOf st bse D.blocks, BlkRep r H V p.1 p.2) : DRep r H V bcap lv bse D := by
  have hs : ∀ i < D.blocks.length, stkId r bse D.blocks.length i = stkId st bse D.blocks.length i := by
    intro i hi; unfold stkId; exact hstk _ (by omega)
  refine ⟨by rw [hsz]; exact h.sz, by rw [hszl]; exact h.szb, by rw [hstkl]; exact h.stkb,
    fun i hi => ?_, fun i j hi hj he => ?_, fun i hi => ?_⟩
  · rw [hs i hi]; exact hblk _ (DList.mem_recsOf st bse D.blocks i hi)
  · rw [hs i hi, hs j hj] at he; exact h.inj i j hi hj he
  · rw [hs i hi]; exact h.bidb i hi

set_option maxHeartbeats 16000000 in
/-- **the D-layer pull on `DRI`** (the shape of `DLI.PullOK` / `DLayer.pull_spec`, with this wrapper's
footprint `pwWA …` and two allocation premises `hsel`, `CBig`) -/
theorem pullW_spec (P : DLI.DPar) (T : ℕ → ℕ) (hsel : P.sel = selBody entLess P.psel)
    (st : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (g : BM.DGl G s) (Ds : ℕ → BM.DStrM G s)
    (l : ℕ) (h1 : 1 ≤ l) (hD : DLI.DRI P st H g Ds l) (hl : st.w "lvl" = l) (hn : st.w "n" = G.n)
    (hS : RowRep st "S" "S.len" G.n (l - 1) []) (hSL : SlotLens st (RamBaseCase.slotBi l))
    (hH : GoodHist (s := s) H (vc st))
    (hu : st.w "ds.fresh" + st.w "blk.fresh" + ((BM.pullC (BM.dlOps G s) (T l) g (Ds l)).2.2.2.2 + 1) ≤
      P.ucap) :
    Runs realOps (pullW P.psel) st (fun r =>
      DLI.DRI P r H (BM.pullC (BM.dlOps G s) (T l) g (Ds l)).2.2.1
        (Function.update Ds l (BM.pullC (BM.dlOps G s) (T l) g (Ds l)).2.2.2.1) l ∧
      RowRep r "S" "S.len" G.n (l - 1) ((BM.pullC (BM.dlOps G s) (T l) g (Ds l)).1.map Fin.val) ∧
      SlotHolds r (RamBaseCase.slotBi l) H (vc r) (BM.pullC (BM.dlOps G s) (T l) g (Ds l)).2.1 ∧
      Unchanged st r pwWA pwVA pwWR pwVR ∧
      (∀ i, (i < (l - 1) * G.n ∨ l * G.n ≤ i) → r.wa "S" i = st.wa "S" i) ∧
      (∀ j, j ≠ l - 1 → r.wa "S.len" j = st.wa "S.len" j) ∧
      (∀ i, i ≠ RamBaseCase.slotBi l → r.va "sl.l" i = st.va "sl.l" i ∧ ∀ a ∈ slotW, r.wa a i = st.wa a i) ∧
      r.wlen = st.wlen ∧ r.vlen = st.vlen ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + Kpw * ((BM.pullC (BM.dlOps G s) (T l) g (Ds l)).2.2.2.2 + 1) ∧
      r.w "ds.fresh" + r.w "blk.fresh" ≤
        st.w "ds.fresh" + st.w "blk.fresh" + ((BM.pullC (BM.dlOps G s) (T l) g (Ds l)).2.2.2.2 + 1)) := by
  rw [pullC_eq] at hu ⊢
  dsimp only at hu ⊢
  have hL := hD.lens
  have htop := hD.lo_le
  have hcap := hL.cap
  have hC := hL.rowcap
  have hbl : l < st.wlen "dsl.base" := by have := hD.dl.basel; omega
  have hMl : l < st.wlen "dsl.M" := by have := hL.M; omega
  have hc1 : 1 < st.cap := by omega
  unfold pullW
  apply runs_seq
  refine runs_wset (a := l) (by simp [hl]) ?_
  apply runs_seq
  refine runs_wset (a := base st l) (by simp [hbl, base]) ?_
  apply runs_seq
  refine runs_wset (a := (Ds l).M) (by simp [hMl, hD.mv l le_rfl htop]) ?_
  set q3 := ((((((st.setW "ds.lv" l).charge 1).setW "ds.b" (base st l)).charge 1).setW "ds.M" (Ds l).M).charge 1)
    with hq3
  have hu3 : Unchanged st q3 [] [] ["ds.lv", "ds.b", "ds.M"] [] := by
    rw [hq3]
    simp only [unch_charge']
    rw [unch_setW' (by simp), unch_charge', unch_setW' (by simp), unch_charge', unch_setW' (by simp)]
    exact Unchanged.refl _ _ _ _ _
  have hD3 : DLI.DRI P q3 H g Ds l :=
    hD.frame_same hu3 (by simp) (by simp) (by simp [DLI.drWR]) (by simp)
  have hvc3 : vc (G := G) q3 = vc st := by funext v; simp [vc, hq3]
  have hbase3 : base q3 l = base st l := by simp [base, hq3]
  have hP3 : DPull.SplitPre q3 H (vc q3) P.bcap l (base st l) (q3.w "sp.w0") g.L (Ds l)
      (recsFrom q3 Ds (l + 1) (P.top - l)) P.psel := by
    have := splitPre_of_DRI hD3 hsel (by simp [hq3])
      (by rw [hbase3]; simp [hq3]) (by simp [hq3]) rfl
    rwa [hbase3] at this
  have hwf := hD.wf l le_rfl htop
  have hne : (Ds l).blocks ≠ [] := hwf.1
  -- sizes
  have hstk0 := DLI.DLRep.stack_le hD.dl
  have hentl : (allEnts (Ds l).blocks).length ≤ g.fresh := by
    refine allEnts_len_le ?_ (hD.fr l le_rfl htop)
    have h := hD.dl.recs.2.2
    have e : recsFrom st Ds l (P.top - l + 1) =
        DList.recsOf st (base st l) (Ds l).blocks ++ recsFrom st Ds (l + 1) (P.top - l) := rfl
    rw [e, List.map_append, DList.entIds_append, DPull.map_snd_recsOf, DPull.entIds_eq_allEnts] at h
    exact (List.nodup_append.mp h).1
  have hpool := hD.dl.pool
  have hfr_ds : st.w "ds.fresh" = g.fresh := hpool.1
  have hprep := prepCost_le g.L (Ds l)
  have hwl3 : q3.wlen = st.wlen := by simp [hq3]
  have hvl3 : q3.vlen = st.vlen := by simp [hq3]
  have hcap3 : q3.cap = st.cap := by simp [hq3]
  have hfc : q3.w "blk.fresh" + (DL.prepList g.L (Ds l).M 0 (Ds l).blocks).2 ≤ P.bcap := by
    simp only [hq3, State.charge_w, State.setW_w]; simp; have := hL.ub; omega
  have hsc : base st l + (Ds l).blocks.length + (DL.prepList g.L (Ds l).M 0 (Ds l).blocks).2 ≤
      q3.wlen "dsl.stk" := by
    rw [hwl3, hL.stkl]; have := hL.ub; omega
  have hpf := hpool.2.1
  have hwc : 6 * (allEnts (Ds l).blocks).length + 60 ≤ q3.wlen "sel.w" := by
    rw [hwl3]; have := hL.selw; omega
  have hmul : l * G.n ≤ (P.top + 2) * (G.n + 2) := Nat.mul_le_mul (by omega) (by omega)
  have hcapS : l * G.n + 2 * (allEnts (Ds l).blocks).length + 2 < q3.cap := by
    rw [hcap3]; have := hL.ue; omega
  have hS3 : RowRep q3 "S" "S.len" G.n (l - 1) [] :=
    hS.of_eq (by rw [hwl3]) (by rw [hwl3]) (by simp [hq3]) (fun i _ => by simp [hq3])
  have hBd3 : DPull.BdHolds q3 l H (vc q3) (Ds l).Bd := bd_conv (hD3.bd l le_rfl htop)
  have hBL3 : DPull.BdLens q3 l :=
    ⟨by rw [hvl3]; have := hL.bl; omega, by rw [hwl3]; have := hL.bh; omega,
      by rw [hwl3]; have := hL.bv; omega, by rw [hwl3]; have := hL.be; omega,
      by rw [hwl3]; have := hL.br; omega, by rw [hwl3]; have := hL.bf; omega⟩
  have hSL3 : SlotLens q3 (4 * l + 3) :=
    ⟨by rw [hvl3]; exact hSL.l, by rw [hwl3]; exact hSL.h, by rw [hwl3]; exact hSL.v,
      by rw [hwl3]; exact hSL.e, by rw [hwl3]; exact hSL.r, by rw [hwl3]; exact hSL.f⟩
  have hH3 : GoodHist (s := s) H (vc q3) := by rw [hvc3]; exact hH
  apply runs_seq
  refine (Runs.cost_mono (DPull.pullS_spec hH3 P.psel q3 (M := (Ds l).M) (Bd := (Ds l).Bd)
    (bs := (Ds l).blocks) hP3 hne h1 (by simp [hq3, hn]) hS3 hBd3 hBL3 hSL3 hfc hsc hwc hcapS
    (by rw [hcap3]; omega))).mono (fun r1 ⟨⟨hR1, hc1, hfr1⟩, hcm1⟩ => ?_)
  have eD : (⟨(Ds l).M, (Ds l).Bd, (Ds l).blocks⟩ : BM.DStrM G s) = Ds l := rfl
  rw [eD] at hR1 hc1 hfr1
  set PR := DL.pullL 1 g.L (Ds l) with hPR
  obtain ⟨hks1, hview, hsep, hwf', hL', hM', hBd'⟩ := DL.pullL_spec 1 hwf
  rw [← hPR] at hks1 hview hsep hwf' hL' hM' hBd'
  -- registers and arrays of `r1`
  have hwr1 : ∀ y, y ∉ DPull.pullWR → r1.w y = q3.w y := fun y hy => hR1.unch.wreg y hy
  have hlv1 : r1.w "lvl" = l := by
    rw [hwr1 _ (by simp [DPull.pullWR, DPull.splitWR, DPull.plRegs, DList.walkRegs, myRegs, lessRegs,
      csRegs, selRegs, entLessW, fsX, fsY, LReg.ws, DPull.linkRegs, DList.buildRegs, DPull.sepRegs])]
    simp [hq3, hl]
  have hn1 : r1.w "n" = G.n := by
    rw [hwr1 _ (by simp [DPull.pullWR, DPull.splitWR, DPull.plRegs, DList.walkRegs, myRegs, lessRegs,
      csRegs, selRegs, entLessW, fsX, fsY, LReg.ws, DPull.linkRegs, DList.buildRegs, DPull.sepRegs])]
    simp [hq3, hn]
  have hcapr1 : r1.cap = st.cap := by rw [hR1.unch.cap, hcap3]
  have hwlr1 : r1.wlen = st.wlen := by rw [hR1.wlen, hwl3]
  have hvlr1 : r1.vlen = st.vlen := by rw [hR1.vlen, hvl3]
  obtain ⟨hks_n, hSw1, hSlw1, hSl1, hScell1⟩ := hR1.rowr
  simp only [List.length_map] at hks_n hSl1 hScell1
  have hmul2 : (l - 1) * G.n + G.n ≤ (P.top + 2) * (G.n + 2) := by
    have : (l - 1) * G.n + G.n = l * G.n := by
      rw [show l = (l - 1) + 1 by omega, Nat.add_mul, one_mul]; simp
    rw [this]; exact hmul
  apply runs_seq
  refine runs_wset (a := (l - 1) * G.n) (by
    simp [hlv1, hn1, fit_of_lt (show 1 < r1.cap by rw [hcapr1]; omega),
      fit_of_lt (show (l - 1) * G.n < r1.cap by rw [hcapr1]; omega)]) ?_
  apply runs_seq
  refine runs_wset (a := PR.1.length) (by
    simp [hlv1, fit_of_lt (show 1 < r1.cap by rw [hcapr1]; omega), hSlw1, hSl1]) ?_
  set q5 := ((((r1.setW "ul.off" ((l - 1) * G.n)).charge 1).setW "ul.len" PR.1.length).charge 1) with hq5
  obtain ⟨K, hK, hKk⟩ := hD.kl
  have hlk : ∀ a ∈ ["lk.n", "lk.p"], q5.wa a = st.wa a := by
    intro a ha
    simp only [hq5, State.charge_wa, State.setW_wa]
    rw [(hR1.unch.warr a (by simp at ha; rcases ha with rfl | rfl <;>
      simp [DPull.pullWA, DPull.splitWA, slotW])).1]
    simp [hq3]
  have hK5 : KL.LL (q5.wa "lk.n") (q5.wa "lk.p") G.n l P.top K := by
    rw [hlk _ (by simp), hlk _ (by simp)]; exact hK
  have hsp5 : DList.Spells q5 "S" ((l - 1) * G.n) (PR.1.map Fin.val) := by
    intro i hi
    simp only [hq5, State.charge_wa, State.setW_wa]
    simpa using hScell1 i (by simpa using hi)
  have hwl5 : q5.wlen = st.wlen := by simp [hq5, hwlr1]
  have hcap5 : q5.cap = st.cap := by simp [hq5, hcapr1]
  refine (DLI.unlinkRow_spec (ops := realOps) (G := G) q5 "S" (PR.1.map Fin.val) ((l - 1) * G.n) l P.top K
    hK5 hsp5 (by simp [hq5]) (by simp [hq5]) (by rw [hwl5]; rw [hwlr1] at hSw1; simp; nlinarith)
    (fun x hx => by obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx; exact v.isLt)
    (by rw [hwl5]; exact hL.lkn) (by rw [hwl5]; exact hL.lkp) (by rw [hcap5]; simp; omega)
    (by decide)).mono (fun r ⟨⟨K', hK', hK'm⟩, hU6, hwl6, hc6⟩ => ?_)
  -- the frame r1 → r
  have hu1r : Unchanged r1 r ["lk.n", "lk.p"] [] ["ul.off", "ul.len", "ul.j", "kl.v", "kl.a", "kl.b"] [] := by
    have u : Unchanged r1 q5 ["lk.n", "lk.p"] [] ["ul.off", "ul.len", "ul.j", "kl.v", "kl.a", "kl.b"] [] := by
      rw [hq5, unch_charge', unch_setW' (by simp), unch_charge', unch_setW' (by simp)]
      exact Unchanged.refl _ _ _ _ _
    exact u.trans (hU6.mono (List.Subset.refl _) (List.Subset.refl _) (fun y hy => by simp at hy ⊢; tauto)
      (List.Subset.refl _))
  have hwlr : r.wlen = st.wlen := by rw [hwl6, hwl5]
  have hvlr : r.vlen = st.vlen := by
    funext a; rw [(hu1r.varr a (by simp)).2, hvlr1]
  have hcapr : r.cap = st.cap := by rw [hu1r.cap, hcapr1]
  have hvcr : vc (G := G) r = vc q3 := by
    funext v; unfold vc
    rw [(hu1r.warr "vcnt" (by simp)).1, (hR1.unch.warr "vcnt" (by simp [DPull.pullWA, DPull.splitWA, slotW])).1]
  have hwa3 : ∀ a, a ∉ DPull.pullWA → r1.wa a = st.wa a := fun a ha => by
    rw [(hR1.unch.warr a ha).1]; simp [hq3]
  have hbase1 : ∀ j, base r1 j = base st j := fun j => by
    unfold base; rw [hwa3 _ (by simp [DPull.pullWA, DPull.splitWA, slotW])]
  have hrecs3 : ∀ (bse : ℕ) (P' : List (Block (Fin G.n) (WLab G s))),
      DList.recsOf q3 bse P' = DList.recsOf st bse P' := fun bse P' => rfl
  have hrecsFrom3 : ∀ n j, recsFrom q3 Ds j n = recsFrom st Ds j n := by
    intro n
    induction n with
    | zero => intro j; rfl
    | succ n ih =>
      intro j
      show DList.recsOf q3 (base q3 j) (Ds j).blocks ++ recsFrom q3 Ds (j + 1) n =
        DList.recsOf st (base st j) (Ds j).blocks ++ recsFrom st Ds (j + 1) n
      rw [hrecs3, ih, show base q3 j = base st j by simp [base, hq3]]
  set Ds' := Function.update Ds l PR.2.2.2.1 with hDs'
  have hDs'l : Ds' l = PR.2.2.2.1 := by simp [hDs']
  have hDs'o : ∀ j, j ≠ l → Ds' j = Ds j := fun j hj => by simp [hDs', hj]
  have hch := hD.dl.chain
  have hbelow := base_below (Ds := Ds) (st := st) (lo := l) (k := P.top - l) hch
  have hstk1 : ∀ x, x < base st l → r1.wa "dsl.stk" x = st.wa "dsl.stk" x := fun x hx => by
    rw [hR1.stk x hx]; simp [hq3]
  have hrf1 : recsFrom r1 Ds' (l + 1) (P.top - l) = recsFrom q3 Ds (l + 1) (P.top - l) := by
    refine DGlob.recsFrom_congr q3 r1 Ds Ds' (P.top - l) (l + 1) (fun l' h1' h2' => ?_)
    refine ⟨hDs'o l' (by omega), by rw [hbase1]; simp [base, hq3], fun x hx1 hx2 => ?_⟩
    have hb := hbelow (l' - l) (by omega) (by omega)
    rw [show l + (l' - l) = l' by omega] at hb
    have e : base q3 l' = base st l' := rfl
    rw [e] at hx2
    rw [hstk1 x (by omega)]; rfl
  have hfresh1 : r1.w "ds.fresh" = g.fresh := by
    rw [hwr1 _ (by simp [DPull.pullWR, DPull.splitWR, DPull.plRegs, DList.walkRegs, myRegs, lessRegs,
      csRegs, selRegs, entLessW, fsX, fsY, LReg.ws, DPull.linkRegs, DList.buildRegs, DPull.sepRegs])]
    simp [hq3, hfr_ds]
  have hbf1 : r1.w "blk.fresh" ≤ st.w "blk.fresh" + PR.2.2.2.2 := by
    have := hfr1; simp [hq3] at this; exact this
  have hDL1 : DLRep r1 H (vc q3) P.ecap P.bcap PR.2.2.1 g.fresh Ds' l (P.top - l) := by
    obtain ⟨_, hpf', a1, a2, a3, a4, a5, a6, a7⟩ := hpool
    refine ⟨hR1.live, ⟨hfresh1, hpf', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hR1.barr, ?_, ?_, fun j hj => ?_,
      fun j hj => ?_, ?_, ?_, ?_⟩
    · rw [hwlr1]; exact a1
    · rw [hwlr1]; exact a2
    · rw [hvlr1]; exact a3
    · rw [hwlr1]; exact a4
    · rw [hwlr1]; exact a5
    · rw [hwlr1]; exact a6
    · rw [hwlr1]; exact a7
    · rw [hwlr1]; exact hD.dl.basel
    · rw [hbase1]; exact hD.dl.base0
    · rw [hbase1, hbase1, hDs'o _ (by omega)]; exact hch j hj
    · rcases Nat.eq_zero_or_pos j with h0 | h0
      · subst h0; simp only [add_zero]; rw [hDs'l, hbase1]; exact hR1.drep
      · rw [hDs'o _ (by omega), hbase1, hvc3]
        have hb := hbelow j h0 hj
        refine drep_transport (hD.dl.drep j hj) ?_ (by rw [hwlr1]) (by rw [hwlr1])
          (fun x hx => hstk1 x (by omega)) (fun p hp => ?_)
        · rw [hR1.sz (l + j) (by omega)]; rfl
        · have hp' : p ∈ recsFrom q3 Ds (l + 1) (P.top - l) := by
            rw [hrecsFrom3]
            refine mem_recsFrom_of (P.top - l) (l + 1) (j - 1) (by omega) p ?_
            rw [show l + 1 + (j - 1) = l + j by omega]; exact hp
          have := hR1.recs.2.1 p (List.mem_append_right _ hp')
          rwa [hvc3] at this
    · show DList.RecsOK r1 H (vc q3) (DList.recsOf r1 (base r1 l) (Ds' l).blocks ++
        recsFrom r1 Ds' (l + 1) (P.top - l))
      rw [hrf1, hDs'l, hbase1]; exact hR1.recs
    · intro p hp
      have hp' : p ∈ DList.recsOf r1 (base r1 l) (Ds' l).blocks ++ recsFrom r1 Ds' (l + 1) (P.top - l) := hp
      rw [hrf1, hDs'l, hbase1] at hp'
      exact hR1.fresh p hp'
    · have := hL.ub; omega
  -- everything at `r`
  have hDL : DLRep r H (vc r) P.ecap P.bcap PR.2.2.1 g.fresh Ds' l (P.top - l) := by
    rw [hvcr]
    exact DLI.DLRep.of_unch hDL1 hu1r (by decide) (by decide) (by decide)
  have hwar : ∀ a, a ∉ pwWA → r.wa a = st.wa a := fun a ha => by
    rw [(hu1r.warr a (fun h => ha (by simp [pwWA] at h ⊢; right; exact h))).1,
      hwa3 a (fun h => ha (by simp only [pwWA, List.mem_append]; left; exact h))]
  have hvar : ∀ a, a ∉ pwVA → r.va a = st.va a := fun a ha => by
    rw [(hu1r.varr a (by simp)).1, (hR1.unch.varr a ha).1]; simp [hq3]
  have hwrr : ∀ y, y ∉ pwWR → r.w y = st.w y := fun y hy => by
    rw [hu1r.wreg y (fun h => hy (by simp [pwWR] at h ⊢; tauto)),
      hwr1 y (fun h => hy (by simp only [pwWR, List.mem_append]; left; exact h))]
    exact hu3.wreg y (fun h => hy (by simp [pwWR] at h ⊢; tauto))
  have hbf_r : r.w "blk.fresh" = r1.w "blk.fresh" := hu1r.wreg _ (by simp)
  have hdf_r : r.w "ds.fresh" = st.w "ds.fresh" := hwrr _ (by
    simp [pwWR, DPull.pullWR, DPull.splitWR, DPull.plRegs, DList.walkRegs, myRegs, lessRegs, csRegs,
      selRegs, entLessW, fsX, fsY, LReg.ws, DPull.linkRegs, DList.buildRegs, DPull.sepRegs])
  have hmemks : ∀ v : Fin G.n, ((v : ℕ) ∈ PR.1.map Fin.val) ↔ v ∈ PR.1 := fun v =>
    ⟨fun h => by obtain ⟨w, hw, e⟩ := List.mem_map.mp h; exact (Fin.ext e) ▸ hw,
      fun h => List.mem_map_of_mem h⟩
  have hkey_view : ∀ (L0 : Live (Fin G.n) (WLab G s)) (D0 : BM.DStrM G s) (v : Fin G.n),
      DB.HasKey L0 D0 v ↔ DB.view L0 D0 v ≠ none := fun L0 D0 v => by
    rw [Ne, DB.view_eq_none]; tauto
  refine ⟨⟨htop, hDL, fun j hj1 hj2 => ?_, fun j hj1 hj2 => ?_, ⟨K', ?_, fun j hj1 hj2 v => ?_⟩,
    fun j hj1 hj2 => ?_, fun j hj1 hj2 => ?_, fun u i a hua => ?_, ?_,
    hL.of_len hwlr hvlr hcapr, fun j hj => ?_, by rw [hu1r.procs, hR1.unch.procs]; simp [hq3]; exact hD.procs,
    fun i hi => ?_, fun j hj1 hj2 => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, hwlr, hvlr, ?_, ?_, ?_⟩
  · -- bd
    have hb : (Ds' j).Bd = (Ds j).Bd := by
      by_cases hjl : j = l
      · subst hjl; rw [hDs'l, hBd']
      · rw [hDs'o j hjl]
    rw [hb, hvcr, hvc3]
    exact bd_conv' (DPull.BdHolds.of_eq (bd_conv (hD.bd j hj1 hj2))
      (fun a ha => hwar a (by simp at ha; rcases ha with rfl | rfl | rfl | rfl | rfl <;>
        simp [pwWA, DPull.pullWA, DPull.splitWA, slotW]))
      (hvar _ (by simp [pwVA, DPull.pullVA])))
  · -- mv
    rw [hwar _ (by simp [pwWA, DPull.pullWA, DPull.splitWA, slotW]), hD.mv j hj1 hj2]
    by_cases hjl : j = l
    · subst hjl; rw [hDs'l, hM']
    · rw [hDs'o j hjl]
  · exact hK'
  · -- kl
    rw [hK'm j hj1 hj2 v, hKk j hj1 hj2 v, hmemks]
    by_cases hjl : j = l
    · subst hjl
      rw [hDs'l, hkey_view, hkey_view, hview v]
      by_cases hv : v ∈ PR.1 <;> simp [hv]
    · rw [hDs'o j hjl, hL', DLI.hasKey_clearKeys]
  · -- wf
    by_cases hjl : j = l
    · subst hjl; rw [hDs'l]; exact hwf'
    · rw [hDs'o j hjl, hL']; exact (DB.deleteKeys_spec (ks := PR.1) (hD.wf j hj1 hj2)).2
  · -- fr
    by_cases hjl : j = l
    · subst hjl; rw [hDs'l]
      intro x hx
      exact hD.fr j hj1 hj2 x (BM.dlPull_ents g.L (Ds j) x hx)
    · rw [hDs'o j hjl]; exact hD.fr j hj1 hj2
  · -- lf
    rw [hL'] at hua
    simp only [DB.clearKeys] at hua
    split_ifs at hua
    exact hD.lf u i a hua
  · -- use
    rw [hdf_r, hbf_r]; omega
  · -- hib
    rw [hDs'o j (by omega)]; exact hD.hib j hj
  · -- keys
    rw [hwar _ (by simp [pwWA, DPull.pullWA, DPull.splitWA, slotW])]; exact hD.keys i hi
  · -- mc
    rw [hcapr]
    by_cases hjl : j = l
    · subst hjl; rw [hDs'l, hM']; exact hD.mc j hj1 hj2
    · rw [hDs'o j hjl]; exact hD.mc j hj1 hj2
  · -- the S row
    exact hR1.rowr.of_eq (by rw [(hu1r.warr "S" (by simp)).2]) (by rw [(hu1r.warr "S.len" (by simp)).2])
      (by rw [(hu1r.warr "S.len" (by simp)).1]) (fun i _ => by rw [(hu1r.warr "S" (by simp)).1])
  · -- the slot
    rw [hvcr]
    exact hR1.slot.of_slot_eq (by rw [(hu1r.varr _ (by simp)).1])
      (fun a ha => by rw [(hu1r.warr a (by simp [slotW] at ha ⊢; rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp)).1])
  · -- the frame
    have u0 : Unchanged st q3 pwWA pwVA pwWR pwVR :=
      hu3.mono (by simp) (by simp) (fun y hy => by simp at hy; simp [pwWR]; tauto) (by simp)
    have u1 : Unchanged q3 r1 pwWA pwVA pwWR pwVR :=
      hR1.unch.mono (fun a ha => by simp only [pwWA, List.mem_append]; left; exact ha) (List.Subset.refl _)
        (fun a ha => by simp only [pwWR, List.mem_append]; left; exact ha) (List.Subset.refl _)
    have u2 : Unchanged r1 r pwWA pwVA pwWR pwVR :=
      hu1r.mono (by simp [pwWA]) (by simp) (fun y hy => by simp at hy; simp [pwWR]; tauto) (by simp)
    exact u0.trans (u1.trans u2)
  · -- S outside row l - 1
    intro i hi
    have e : (l - 1 + 1) * G.n = l * G.n := by rw [show l - 1 + 1 = l by omega]
    rw [(hu1r.warr "S" (by simp)).1, hR1.Sout i (by rw [e]; exact hi)]; rfl
  · intro j hj
    rw [(hu1r.warr "S.len" (by simp)).1, hR1.Slen j hj]; rfl
  · intro i hi
    have hi' : i ≠ 4 * l + 3 := hi
    refine ⟨by rw [(hu1r.varr _ (by simp)).1, (hR1.slots i hi').1]; rfl, fun a ha => ?_⟩
    rw [(hu1r.warr a (by simp [slotW] at ha ⊢; rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp)).1,
      (hR1.slots i hi').2 a ha]; rfl
  · -- cost monotone
    have h5 : q5.cost = r1.cost + 2 := by simp [hq5]
    have h3 : q3.cost = st.cost + 3 := by simp [hq3]
    omega
  · -- cost bound
    have h5 : q5.cost = r1.cost + 2 := by simp [hq5]
    have h3 : q3.cost = st.cost + 3 := by simp [hq3]
    have hk := DPull.pullL_keys_le g.L (Ds l)
    rw [← hPR] at hk
    simp only [List.length_map] at hc6
    have hKpw : Kpw = 23031 := rfl
    have hKp : DPull.Kpull = 23011 := rfl
    rw [hKp] at hc1
    rw [hKpw]
    omega
  · -- use
    rw [hdf_r, hbf_r]; omega

/-- **agent-04's pull contract `DLI.PullOK` holds for `pullW`**, for any name lists containing this
wrapper's footprint and any `K ≥ Kpw` -/
theorem pullOK_of (P : DLI.DPar) (T : ℕ → ℕ) (hsel : P.sel = selBody entLess P.psel)
    (wa va wr vr : List String) (K : ℕ) (hK : Kpw ≤ K)
    (hwa : ∀ a ∈ pwWA, a ∈ wa ++ ["S", "S.len"] ++ slotW) (hva : ∀ a ∈ pwVA, a ∈ va ++ ["sl.l"])
    (hwr : ∀ a ∈ pwWR, a ∈ wr) (hvr : ∀ a ∈ pwVR, a ∈ vr) :
    DLI.PullOK (G := G) (s := s) P T (pullW P.psel) wa va wr vr K := by
  intro st H g Ds l h1 hD hl hn hS hSL hH hu
  refine (pullW_spec P T hsel st H g Ds l h1 hD hl hn hS hSL hH hu).mono
    (fun r ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ =>
      ⟨a1, a2, a3, a4.mono hwa hva hwr hvr, a5, a6, a7, a8, a9, a10, le_trans a11 ?_, a12⟩)
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hK) _

/-! ## Names: the wrapper's footprint avoids the spine's names -/

/-- extra word arrays of the pull beyond `DLI.drWA` (and `S`, `S.len`, slot arrays) -/
def pullXWA : List String := ["sel.w"]
/-- extra value arrays of the pull -/
def pullXVA : List String := []

set_option maxRecDepth 100000 in
theorem pwWR_ok : ∀ a ∈ pwWR, a ∉ RamSpine.spRegs := by decide
set_option maxRecDepth 100000 in
theorem pwVR_ok : ∀ a ∈ pwVR, a ∉ RamSpine.spVRegs := by decide
set_option maxRecDepth 100000 in
theorem pullXWA_ok : ∀ a ∈ pullXWA, a ∉ RamSpine.spArrs := by decide
theorem pullXVA_ok : ∀ a ∈ pullXVA, a ∉ "sl.l" :: "gW" :: labV := by decide
set_option maxRecDepth 100000 in
theorem pwWA_sub : ∀ a ∈ pwWA, a ∈ (DLI.drWA ++ pullXWA) ++ ["S", "S.len"] ++ slotW := by decide
set_option maxRecDepth 100000 in
theorem pwVA_sub : ∀ a ∈ pwVA, a ∈ (DLI.drVA ++ pullXVA) ++ ["sl.l"] := by decide

/-- **`PullOK` on agent-04's name lists** (`DLI.dnames_of`): any extra lists containing the pull's
extra names -/
theorem pullOK_inst (P : DLI.DPar) (T : ℕ → ℕ) (hsel : P.sel = selBody entLess P.psel)
    (xWA xVA xWR xVR : List String) (hxa : ∀ a ∈ pullXWA, a ∈ xWA) (hxv : ∀ a ∈ pullXVA, a ∈ xVA)
    (hxr : ∀ a ∈ pwWR, a ∈ xWR) (hxvr : ∀ a ∈ pwVR, a ∈ xVR) (K : ℕ) (hK : Kpw ≤ K) :
    DLI.PullOK (G := G) (s := s) P T (pullW P.psel) (DLI.drWA ++ xWA) (DLI.drVA ++ xVA)
      (DLI.wrD ++ xWR) (DLI.vrD ++ xVR) K := by
  refine pullOK_of P T hsel _ _ _ _ K hK (fun a ha => ?_) (fun a ha => ?_) (fun a ha => ?_) (fun a ha => ?_)
  · have h := pwWA_sub a ha
    simp only [List.mem_append] at h ⊢
    rcases h with ((h | h) | h) | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr (hxa a h)))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  · have h := pwVA_sub a ha
    simp only [List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (hxv a h))
    · exact Or.inr h
  · exact List.mem_append_right _ (hxr a ha)
  · exact List.mem_append_right _ (hxvr a ha)

end Frontier.CHD.PullWrap
