import Frontier.CHD.DLayerInst
import Frontier.CHD.RamBodyFinDefs

/-!
# Frontier.CHD.DDelW — the deletion of the `W'` keys (BM.29) on the spine's D layer (owner: agent-01)

**NON-GATE** (B-L3/B-L4 glue).  `dsDelW` is agent-04's `dsDelB` reading the `Wp` row of the
current level `lvl` instead of the `U` row of level `lvl - 1`: the keys of the row leave the live
map (`delS`) and the per-level live-key lists (`unlinkRow`).  `delWBU_mkDL`: on every D layer built
by `DLI.mkDL`, `dsDelW` satisfies agent-03's `DelWBU` (the `hDel` input of `fin_spec`), with no
further hypotheses — its write sets are those of `dsDelB`, which `DNames.del` already covers.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.DDelW

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.DB Frontier.CHD.DIns
  Frontier.CHD.DList Frontier.CHD.DGlob Frontier.CHD.MLab Frontier.CHD.LabTab Frontier.CHD.BM
  Frontier.CHD.DLI
open Frontier.RAM.WExpr Frontier.RAM.Stmt Frontier.CHD.RamBaseCase Frontier.CHD.RamLevel

variable {G : Graph} {s : Fin G.n}

/-- BM.29: the keys of the level-`lvl` `Wp` row leave the live map and the live-key lists -/
def dsDelW : Stmt :=
  seq (wset "dd.off" (mul (var "lvl") (var "n")))
  (seq (wset "dd.len" (load "Wp.len" (var "lvl")))
  (seq (delS "Wp")
  (seq (wset "ul.off" (var "dd.off"))
  (seq (wset "ul.len" (var "dd.len")) (unlinkRow "Wp")))))

theorem dsDelW_noalloc : NoAlloc dsDelW := by
  simp [NoAlloc, dsDelW, delS, delLoop, delBody, unlinkRow, ulLoop, ulBody, KL.klUnlink]

theorem sWA_dsDelW : sWA dsDelW = sWA dsDelB := by decide
theorem sVA_dsDelW : sVA dsDelW = sVA dsDelB := by decide
theorem sWR_dsDelW : sWR dsDelW = sWR dsDelB := by decide
theorem sVR_dsDelW : sVR dsDelW = sVR dsDelB := by decide

theorem dsDelW_main {ops : VOps ℝ≥0} (P : DPar) (st : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m))
    (g : DGl G s) (Ds : ℕ → DStrM G s) (l : ℕ) (lU : List (Fin G.n))
    (hD : DRI P st H g Ds l) (hl : st.w "lvl" = l) (hn : st.w "n" = G.n)
    (hU : RowRep st "Wp" "Wp.len" G.n l (lU.map Fin.val)) :
    Runs ops dsDelW st (fun r => DRI P r H (BM.delC g lU).1 Ds l ∧
      r.cost ≤ st.cost + 13 * lU.length + 9) := by
  have hc := hD.lens.cap
  have hrc := hD.lens.rowcap
  have htop := hD.lo_le
  have hLn := hD.lens
  obtain ⟨hUlen, hUarr, hUl, hUv, hUs⟩ := hU
  simp only [List.length_map] at hUlen hUv hUs
  set off := l * G.n with hoff
  have hmul1 : l * G.n ≤ P.top * G.n := Nat.mul_le_mul_right _ htop
  have hmul2 : P.top * G.n + G.n + 1 ≤ (P.top + 2) * (G.n + 2) := by nlinarith
  have hoffc : off + lU.length + 1 < st.cap := by omega
  have h1c : 1 < st.cap := by omega
  refine runs_seq (runs_wset (a := off) (by simp [hl, hn, fit, h1c]; omega) ?_)
  set q1 := (st.setW "dd.off" off).charge 1 with hq1
  refine runs_seq (runs_wset (a := lU.length) (by
    simp [hq1, hl, fit, h1c, hUl, hUv]) ?_)
  set q2 := (q1.setW "dd.len" lU.length).charge 1 with hq2
  have hU2 : Unchanged st q2 [] [] ["dd.off", "dd.len"] [] := by
    rw [hq2, unch_charge, unch_setW (by simp), hq1, unch_charge, unch_setW (by simp)]
    exact Unchanged.refl _ _ _ _ _
  have hdl2 : DLRep q2 H (vc st) P.ecap P.bcap g.L g.fresh Ds l (P.top - l) :=
    DLRep.of_unch hD.dl hU2 (by simp) (by simp) (by simp [drWR])
  have hsp : Spells q2 "Wp" off (lU.map Fin.val) := by
    intro r hr; simp only [hq2, hq1, State.charge_wa, State.setW_wa]; simpa using hUs r (by simpa using hr)
  have hsucc : (l + 1) * G.n = off + G.n := by rw [hoff, Nat.succ_mul]
  have harr0 : off + lU.length ≤ st.wlen "Wp" := by omega
  have harr : off + lU.length ≤ q2.wlen "Wp" := by
    simp only [hq2, hq1, State.charge_wlen, State.setW_wlen]; exact harr0
  refine runs_seq ((Runs.sframe (delDL (ops := ops) q2 H (vc st) P.ecap P.bcap g.L g.fresh Ds l
    (P.top - l) hdl2 "Wp" lU off hsp (by simp [hq2, hq1]) (by simp [hq2]) harr
    (by simp [hq2, hq1]; omega) (by decide)) (by simp [NoAlloc, delS, delLoop, delBody])).mono
    (fun r3 hr3 => ?_))
  obtain ⟨⟨hDL3, hU3, hc3⟩, hU3', hwl3, hvl3⟩ := hr3
  refine runs_seq (runs_wset (a := off) (by
    simp only [evalW]; rw [hU3.wreg _ (by simp)]; simp [hq2, hq1]) ?_)
  set q4 := (r3.setW "ul.off" off).charge 1 with hq4
  refine runs_seq (runs_wset (a := lU.length) (by
    simp only [evalW, hq4, State.charge_w, State.setW_w]; rw [hU3.wreg _ (by simp)]; simp [hq2]) ?_)
  set q5 := (q4.setW "ul.len" lU.length).charge 1 with hq5
  have hU45 : Unchanged r3 q5 [] [] ["ul.off", "ul.len"] [] := by
    rw [hq5, unch_charge, unch_setW (by simp), hq4, unch_charge, unch_setW (by simp)]
    exact Unchanged.refl _ _ _ _ _
  obtain ⟨K, hK, hKk⟩ := hD.kl
  have hq5a : ∀ a, a ≠ "live" → q5.wa a = st.wa a := by
    intro a ha
    rw [(hU45.warr a (by simp)).1, (hU3.warr a (by simpa using ha)).1, (hU2.warr a (by simp)).1]
  have hq5wl : q5.wlen = st.wlen := by
    rw [show q5.wlen = r3.wlen by simp [hq5, hq4], hwl3]; simp [hq2, hq1]
  have hq5c : q5.cap = st.cap := by rw [hU45.cap, hU3.cap, hU2.cap]
  have hK5 : KL.LL (q5.wa "lk.n") (q5.wa "lk.p") G.n l P.top K := by
    rw [hq5a _ (by simp), hq5a _ (by simp)]; exact hK
  have hsp5 : Spells q5 "Wp" off (lU.map Fin.val) := by
    intro r hr; rw [hq5a _ (by simp)]; simpa using hUs r (by simpa using hr)
  refine (Runs.sframe (unlinkRow_spec (ops := ops) q5 "Wp" (lU.map Fin.val) off l P.top K hK5 hsp5
    (by simp [hq5, hq4]) (by simp [hq5]) (by rw [hq5wl]; simpa using harr0)
    (fun x hx => by obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx; exact v.isLt)
    (by rw [hq5wl]; exact hLn.lkn) (by rw [hq5wl]; exact hLn.lkp) (by rw [hq5c]; simpa using hoffc)
    (by decide)) (by simp [NoAlloc, unlinkRow, ulLoop, ulBody, KL.klUnlink])).mono ?_
  rintro r ⟨⟨⟨K', hK', hK'm⟩, hU6, hwl6, hc6⟩, hU6', hwl6', hvl6'⟩
  have hUall : Unchanged r3 r ["lk.n", "lk.p"] [] (["ul.off", "ul.len"] ++ ["ul.j", "kl.v", "kl.a", "kl.b"]) [] :=
    (hU45.comp hU6).mono (by simp) (by simp) (by simp) (by simp)
  have hra : ∀ a, a ≠ "lk.n" → a ≠ "lk.p" → r.wa a = q5.wa a := by
    intro a h1 h2; exact (hU6.warr a (by simp [h1, h2])).1
  have hrva : r.va = st.va := by
    funext a; rw [(hU6.varr a (by simp)).1, (hU45.varr a (by simp)).1, (hU3.varr a (by simp)).1,
      (hU2.varr a (by simp)).1]
  have hrwl : r.wlen = st.wlen := by rw [hwl6, hq5wl]
  have hrvl : r.vlen = st.vlen := by
    rw [hvl6', show q5.vlen = r3.vlen by simp [hq5, hq4], hvl3]; simp [hq2, hq1]
  have hrc : r.cap = st.cap := by rw [hU6.cap, hq5c]
  have hvc : vc (G := G) r = vc st := by
    funext v; unfold vc; rw [hra _ (by simp) (by simp), hq5a _ (by simp)]
  have hrw : ∀ x ∈ drWR, r.w x = st.w x := by
    intro x hx; simp [drWR] at hx
    rcases hx with rfl | rfl <;>
    · rw [hU6.wreg _ (by simp), hU45.wreg _ (by simp), hU3.wreg _ (by simp), hU2.wreg _ (by simp)]
  have hbdeq : ∀ a ∈ ["dsl.bf", "dsl.bh", "dsl.bv", "dsl.be", "dsl.br", "dsl.M"], r.wa a = st.wa a := by
    intro a ha; rw [hra a (by intro e; subst e; simp at ha) (by intro e; subst e; simp at ha),
      hq5a a (by intro e; subst e; simp at ha)]
  refine ⟨⟨htop, ?_, fun j h1 h2 => ?_, fun j h1 h2 => ?_, ⟨K', hK', fun j h1 h2 v => ?_⟩,
      fun j h1 h2 => ?_, fun j h1 h2 => hD.fr j h1 h2, ?_, ?_, hLn.of_len hrwl hrvl hrc, hD.hib,
      by rw [hU6.procs, hU45.procs, hU3.procs, hU2.procs]; exact hD.procs,
      fun i hi => by rw [hra _ (by decide) (by decide), hq5a _ (by decide)]; exact hD.keys i hi,
      fun j h1 h2 => by rw [hrc]; exact hD.mc j h1 h2⟩, ?_⟩
  · rw [hvc, delC_L, delC_fresh]
    exact DLRep.of_unch hDL3 hUall (by decide) (by decide) (by decide)
  · rw [hvc]
    exact (hD.bd j h1 h2).of_eq (by rw [hbdeq _ (by simp)]) (by rw [hrva])
      (by rw [hbdeq _ (by simp)]) (by rw [hbdeq _ (by simp)]) (by rw [hbdeq _ (by simp)])
      (by rw [hbdeq _ (by simp)])
  · rw [hbdeq _ (by simp)]; exact hD.mv j h1 h2
  · rw [hK'm j h1 h2 v, hKk j h1 h2 v, delC_L, hasKey_clearKeys]
    have hm : ((v : ℕ) ∈ lU.map Fin.val) ↔ v ∈ lU :=
      ⟨fun h => by obtain ⟨w, hw, e⟩ := List.mem_map.mp h; exact (Fin.ext e) ▸ hw,
        fun h => List.mem_map_of_mem h⟩
    rw [hm]
  · rw [delC_L]; exact (deleteKeys_spec (hD.wf j h1 h2)).2
  · intro u i a hu
    rw [delC_L] at hu; rw [delC_fresh]
    simp only [DB.clearKeys] at hu
    split_ifs at hu
    exact hD.lf u i a hu
  · rw [hrw _ (by simp [drWR]), hrw _ (by simp [drWR])]; exact hD.use
  · simp only [List.length_map] at hc6
    rw [hc6]
    have hq5c' : q5.cost = r3.cost + 2 := by simp [hq5, hq4]
    have hq2c : q2.cost = st.cost + 2 := by simp [hq2, hq1]
    omega

theorem dsDelW_spec {ops : VOps ℝ≥0} (P : DPar) (st : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m))
    (g : DGl G s) (Ds : ℕ → DStrM G s) (l : ℕ) (lU : List (Fin G.n))
    (hD : DRI P st H g Ds l) (hl : st.w "lvl" = l) (hn : st.w "n" = G.n)
    (hU : RowRep st "Wp" "Wp.len" G.n l (lU.map Fin.val)) :
    Runs ops dsDelW st (fun r => DRI P r H (BM.delC g lU).1 Ds l ∧
      Unchanged st r (sWA dsDelW) (sVA dsDelW) (sWR dsDelW) (sVR dsDelW) ∧ r.wlen = st.wlen ∧
      r.vlen = st.vlen ∧ st.cost ≤ r.cost ∧ r.cost ≤ st.cost + 13 * lU.length + 9) :=
  (Runs.sframe (Runs.cost_mono (dsDelW_main P st H g Ds l lU hD hl hn hU)) dsDelW_noalloc).mono
    (fun _ ⟨⟨⟨h1, h2⟩, h3⟩, hU', hwl, hvl⟩ => ⟨h1, hU', hwl, hvl, h3, h2⟩)

/-- **`dsDelW` is the finalization's `W'`-deletion** on every D layer built by `mkDL`
(agent-03's `DelWBU`, the `hDel` input of `fin_spec`). -/
theorem delWBU_mkDL (P : DPar) (T : ℕ → ℕ) (wa va wr vr : List String) (hN : DNames wa va wr vr)
    (K : ℕ) (hK : 40 ≤ K) (merge pull : Stmt) (hM : MergeOK (G := G) (s := s) P merge wa va wr vr K)
    (hP : PullOK (G := G) (s := s) P T pull wa va wr vr K) :
    Frontier.CHD.RamBody.DelWBU (mkDL P T wa va wr vr hN K hK merge pull hM hP) dsDelW := by
  intro st H g Ds l lW hD hl hn hW
  refine (dsDelW_spec (ops := realOps) P st H g Ds l lW hD hl hn hW).mono ?_
  rintro r ⟨a1, a2, a3, a4, a5, a6⟩
  rw [sWA_dsDelW, sVA_dsDelW, sWR_dsDelW, sVR_dsDelW] at a2
  refine ⟨a1, unch_widen a2 hN.del.1 hN.del.2.1 hN.del.2.2.1 hN.del.2.2.2, a3, a4, a5, ?_, ?_⟩
  · show r.cost ≤ st.cost + K * ((BM.delC g lW).2 + lW.length + 1)
    have e : (BM.delC g lW).2 = lW.length + 1 := rfl
    rw [e]
    have := Nat.mul_le_mul_right (lW.length + 1 + lW.length + 1) hK
    omega
  · show r.w "ds.fresh" + r.w "blk.fresh" = st.w "ds.fresh" + st.w "blk.fresh"
    rw [a2.wreg _ (by decide), a2.wreg _ (by decide)]

end Frontier.CHD.DDelW

#print axioms Frontier.CHD.DDelW.delWBU_mkDL
