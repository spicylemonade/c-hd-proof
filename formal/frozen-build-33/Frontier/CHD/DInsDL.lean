import Frontier.CHD.DGlobal
import Frontier.CHD.DInsertB
import Frontier.CHD.DInsertL

/-!
# DInsDL — the RAM insert (agent-02's `insRAM`) on the whole D layer (B-L3 integration, agent-04)

NON-GATE.  `insertDL`: `insRAM` at the deepest active level `lo` takes `DLRep(Ds, lo, k)` to
`DLRep(update Ds lo D', lo, k)` with `(L', fresh', D') = insertNS L fresh (Ds lo) v λ`
(`= DLazy.insertL`'s state part, `DIns.insertL_eq_insertNS`).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.DGlob

open Frontier Frontier.RAM Frontier.CHD Frontier.CHD.DB Frontier.CHD.DIns Frontier.CHD.DList
open Frontier.RAM.LabRAM Frontier.CHD.MLab Frontier.CHD.LabTab

variable {G : Graph} {s : Fin G.n}

/-- the D layer survives state changes that keep every array and both counters -/
theorem DLRep.of_same {st r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {ecap bcap : ℕ} {L : Live (Fin G.n) (WLab G s)} {fresh : ℕ} {Ds : ℕ → DStr (Fin G.n) (WLab G s)}
    {lo k : ℕ} (h : DLRep st H V ecap bcap L fresh Ds lo k) (hwa : ∀ a, r.wa a = st.wa a)
    (hva : ∀ a, r.va a = st.va a) (hwl : ∀ a, r.wlen a = st.wlen a) (hvl : ∀ a, r.vlen a = st.vlen a)
    (hf : r.w "ds.fresh" = st.w "ds.fresh") (hbf : r.w "blk.fresh" = st.w "blk.fresh") :
    DLRep r H V ecap bcap L fresh Ds lo k := by
  have hbase : ∀ l, base r l = base st l := by intro l; unfold base; rw [hwa]
  have hrf : recsFrom r Ds lo (k + 1) = recsFrom st Ds lo (k + 1) :=
    recsFrom_congr st r Ds Ds (k + 1) lo (fun l _ _ => ⟨rfl, hbase l, fun x _ _ => by rw [hwa]⟩)
  refine ⟨liveRep_of_arrays h.live (fun a _ => hwa a) (hva _) (hwl _), poolRep_of h.pool hf hwl hvl,
    blkArrs_of h.barr hwl hvl, by rw [hwl]; exact h.basel, by rw [hbase]; exact h.base0,
    fun j hj => by rw [hbase, hbase]; exact h.chain j hj, fun j hj => ?_, ?_, ?_, by rw [hbf]; exact h.bfcap⟩
  · rw [hbase]
    exact DRep.of_frame (h.drep j hj) (fun x _ _ => by rw [hwa]) (by rw [hwa]) hwl
      (fun i hi => blkRep_of_arrays ((h.drep j hj).blk i hi) (fun a _ => hwa a) (hva _) (hva _) (hwl _))
  · rw [hrf]; exact recsOK_of_arrays h.recs (fun a _ => hwa a) (hva _) (hva _) (hwl _)
  · rw [hrf, hbf]; exact h.bfresh

/-- the skipped insertion writes registers only -/
theorem insRAM_skip (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (hH : GoodHist (s := s) H V) (L : Live (Fin G.n) (WLab G s)) (ecap : ℕ) (st : State ℝ≥0)
    (hLv : LiveRep st H V L) (hEA : EntArrs st ecap)
    (hLf : ∀ u i a, L u = some (i, a) → i < ecap) (v : Fin G.n) (hv : st.w "ds.v" = v)
    (k : MLabel G) (p : List (Fin G.m)) (hK : Holds st KB k) (hKp : Rep (s := s) H V k p)
    (hcap : 1 < st.cap) (hskip : skipIns L v ((toW p : WalkOrd G s) : WLab G s) = true) :
    Runs realOps insRAM st (fun r => Unchanged st r [] [] skipW [YB.l] ∧ r.cost ≤ st.cost + 24) := by
  apply runs_seq
  refine (wp_sound _ _ _ (skipTest_wp H V hH L ecap st hLv hEA hLf v hv k p hK hKp hcap)).mono ?_
  rintro r ⟨hlt, hU, hc1, hc2⟩
  rw [hskip, if_pos rfl] at hlt
  refine runs_ite_false (by simp [hlt]) (runs_skip ?_)
  refine ⟨?_, by simp; omega⟩
  exact ((hU.trans (Unchanged.charge r 1 _ _ _ _)).trans (Unchanged.charge _ 1 _ _ _ _))

theorem entIds_prependAt (e : Entry (Fin G.n) (WLab G s)) :
    ∀ (o : ℕ) (bs : List (Block (Fin G.n) (WLab G s))), o < bs.length →
      (entIds (prependAt e o bs)).Perm (e.id :: entIds bs)
  | _, [], h => absurd h (Nat.not_lt_zero _)
  | 0, b :: bs, _ => by simp [prependAt, entIds]
  | o + 1, b :: bs, h => by
      simp only [prependAt, entIds_cons]
      have ih := entIds_prependAt e o bs (by simp at h; omega)
      exact (List.Perm.append_left _ ih).trans List.perm_middle

/-- **Insert on the whole D layer** (deepest active level `lo`). -/
theorem insertDL (st0 : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (hH : GoodHist (s := s) H V) (ecap bcap : ℕ) (L : Live (Fin G.n) (WLab G s)) (fresh : ℕ)
    (Ds : ℕ → DStr (Fin G.n) (WLab G s)) (lo k : ℕ) (hDL : DLRep st0 H V ecap bcap L fresh Ds lo k)
    (hwf : WF L (Ds lo)) (hfr : FreshOK fresh (Ds lo)) (hid : IdsNodup (Ds lo))
    (hLf : ∀ u i a, L u = some (i, a) → i < fresh)
    (hfam : ∀ x ∈ entIds ((recsFrom st0 Ds lo (k + 1)).map Prod.snd), x < fresh)
    (v : Fin G.n) (hv : st0.w "ds.v" = v) (hlv : st0.w "ds.lv" = lo) (hb : st0.w "ds.b" = base st0 lo)
    (km : MLabel G) (p : List (Fin G.m)) (hK : Holds st0 KB km) (hKp : Rep (s := s) H V km p)
    (hfr1 : fresh + 1 < ecap) (hcap : 2 * (Ds lo).blocks.length + ecap + base st0 lo + 4 < st0.cap) :
    Runs realOps insRAM st0 (fun r =>
      DLRep r H V ecap bcap (insertNS L fresh (Ds lo) v ((toW p : WalkOrd G s) : WLab G s)).1
        (insertNS L fresh (Ds lo) v ((toW p : WalkOrd G s) : WLab G s)).2.1
        (Function.update Ds lo (insertNS L fresh (Ds lo) v ((toW p : WalkOrd G s) : WLab G s)).2.2) lo k ∧
      r.cost ≤ st0.cost + (if skipIns L v ((toW p : WalkOrd G s) : WLab G s) then 24
          else 70 + 35 * (Nat.log 2 ((Ds lo).blocks.length - 1) + 1))) := by
  set lam : WLab G s := ((toW p : WalkOrd G s) : WLab G s) with hlam
  have hc1 : 1 < st0.cap := by omega
  have hEA := hDL.pool.2.2
  have hLf' : ∀ u i a, L u = some (i, a) → i < ecap := fun u i a h => by have := hLf u i a h; omega
  by_cases hskip : skipIns L v lam = true
  · -- nothing changes
    refine (insRAM_skip H V hH L ecap st0 hDL.live hEA hLf' v hv km p hK hKp hc1 hskip).mono ?_
    rintro r ⟨hU, hc⟩
    have hins : insertNS L fresh (Ds lo) v lam = (L, fresh, Ds lo) := by simp [insertNS, hskip]
    rw [hins]
    simp only [Function.update_eq_self, hskip, if_true]
    refine ⟨DLRep.of_same hDL (fun a => (hU.warr a (by simp)).1) (fun a => (hU.varr a (by simp [YB])).1)
      (fun a => (hU.warr a (by simp)).2) (fun a => (hU.varr a (by simp [YB])).2)
      (hU.wreg _ (by simp [skipW])) (hU.wreg _ (by simp [skipW])), hc⟩
  · have hsk : skipIns L v lam = false := by simpa using hskip
    set D := Ds lo with hDdef
    set bse := base st0 lo with hbse
    have hD0 : DRep st0 H V bcap lo bse D := by simpa using hDL.drep 0 (by omega)
    refine (insRAM_spec H V hH bcap ecap lo bse fresh D L st0 hD0 hDL.barr hDL.live hDL.pool hwf hfr hid
      hLf v hv hlv hb km p hK hKp hfr1 hcap).mono ?_
    rintro r ⟨hD', hBA, hLv', hP', hU, hF, hc1', hc2'⟩
    obtain ⟨o, ho, hFo⟩ := hF hsk
    set D' := (insertNS L fresh D v lam).2.2 with hD'def
    have hD'blocks : D'.blocks = prependAt ⟨fresh, v, lam⟩ (ownerIdx lam D.blocks) D.blocks := by
      simp [hD'def, insertNS, hsk, prependOwner_eq]
    have hlen' : D'.blocks.length = D.blocks.length := by rw [hD'blocks, prependAt_length]
    have hstkeq : r.wa "dsl.stk" = st0.wa "dsl.stk" := hFo.stk.1
    have hbaseq : ∀ l, base r l = base st0 l := by
      intro l; unfold base; rw [(hU.warr "dsl.base" (by simp [insWA])).1]
    have hbfr : r.w "blk.fresh" = st0.w "blk.fresh" := hU.wreg _ (by simp [insWR, skipW, probeW])
    set bid := stkId st0 bse D.blocks.length o with hbid
    -- the old family, split into the current level and the others
    have hfamsplit : recsFrom st0 Ds lo (k + 1) = recsOf st0 bse D.blocks ++ recsFrom st0 Ds (lo + 1) k := rfl
    have hR0 := hDL.recs
    rw [hfamsplit] at hR0
    have hothers : ∀ q ∈ recsFrom st0 Ds (lo + 1) k, q.1 ≠ bid := by
      intro q hq heq
      have h1 := hR0.1
      rw [List.map_append, List.nodup_append] at h1
      have hmem : bid ∈ (recsOf st0 bse D.blocks).map Prod.fst := by
        rw [hbid]
        exact List.mem_map.mpr ⟨_, mem_recsOf st0 bse D.blocks o ho, rfl⟩
      exact h1.2.2 _ hmem _ (List.mem_map.mpr ⟨q, hq, rfl⟩) heq.symm
    have hfreshO : ∀ q ∈ recsFrom st0 Ds (lo + 1) k, ∀ x ∈ q.2.ents, x.id ≠ fresh := by
      intro q hq x hx heq
      have := hfam fresh (by
        rw [hfamsplit, List.map_append, entIds_append]
        refine List.mem_append_right _ ?_
        unfold entIds
        exact List.mem_flatMap.mpr ⟨q.2, List.mem_map.mpr ⟨q, hq, rfl⟩,
          List.mem_map.mpr ⟨x, hx, heq⟩⟩)
      omega
    have hothersR : ∀ q ∈ recsFrom st0 Ds (lo + 1) k, BlkRep r H V q.1 q.2 := fun q hq =>
      BlkRep.insert_other hFo (hR0.2.1 q (List.mem_append_right _ hq)) (hothers q hq) (hfreshO q hq)
    have hrest : recsFrom r (Function.update Ds lo D') (lo + 1) k = recsFrom st0 Ds (lo + 1) k := by
      apply recsFrom_congr
      intro l hl1 hl2
      exact ⟨by simp [Function.update_apply, show l ≠ lo by omega], hbaseq l,
        fun x _ _ => by rw [hstkeq]⟩
    have hcur : recsOf r (base r lo) D'.blocks =
        ((List.range D.blocks.length).map (stkId st0 bse D.blocks.length)).zip D'.blocks := by
      unfold recsOf
      rw [hlen', hbaseq]
      congr 2
      funext i
      unfold stkId; rw [hstkeq]
    have hnewfam : recsFrom r (Function.update Ds lo D') lo (k + 1) =
        ((List.range D.blocks.length).map (stkId st0 bse D.blocks.length)).zip D'.blocks ++
          recsFrom st0 Ds (lo + 1) k := by
      show recsOf r (base r lo) ((Function.update Ds lo D') lo).blocks ++
        recsFrom r (Function.update Ds lo D') (lo + 1) k = _
      rw [Function.update_self, hcur, hrest]
    set f := stkId st0 bse D.blocks.length with hf
    have hzipfst : (((List.range D.blocks.length).map f).zip D'.blocks).map Prod.fst =
        (List.range D.blocks.length).map f := by
      rw [List.map_fst_zip]; simp [hlen']
    have hzipsnd : (((List.range D.blocks.length).map f).zip D'.blocks).map Prod.snd = D'.blocks := by
      rw [List.map_snd_zip]; simp [hlen']
    have holdfst : (recsOf st0 bse D.blocks).map Prod.fst = (List.range D.blocks.length).map f := by
      unfold recsOf; rw [List.map_fst_zip]; simp
    have holdsnd : (recsOf st0 bse D.blocks).map Prod.snd = D.blocks := by
      unfold recsOf; rw [List.map_snd_zip]; simp
    have hfreshNot : fresh ∉ entIds ((recsOf st0 bse D.blocks ++ recsFrom st0 Ds (lo + 1) k).map Prod.snd) := by
      intro h; have := hfam fresh (by rw [hfamsplit]; exact h); omega
    have hnewR : RecsOK r H V (((List.range D.blocks.length).map f).zip D'.blocks ++ recsFrom st0 Ds (lo + 1) k) := by
      refine ⟨?_, ?_, ?_⟩
      · have h1 := hR0.1
        rw [List.map_append, holdfst] at h1
        rw [List.map_append, hzipfst]; exact h1
      · intro q hq
        rcases List.mem_append.mp hq with hq | hq
        · obtain ⟨i, hi, hqi⟩ := List.mem_iff_getElem.mp hq
          have hi' : i < D.blocks.length := by simp [List.length_zip, hlen'] at hi; omega
          rw [← hqi]
          simp only [List.getElem_zip, List.getElem_map, List.getElem_range]
          have hb := hD'.blk i (by rw [hlen']; exact hi')
          have hs : stkId r bse D'.blocks.length i = f i := by
            rw [hf, hlen']; unfold stkId; rw [hstkeq]
          rw [hs] at hb
          exact hb
        · exact hothersR q hq
      · rw [List.map_append, hzipsnd, entIds_append]
        have h3 := hR0.2.2
        rw [List.map_append, holdsnd, entIds_append] at h3
        have hperm : (entIds D'.blocks ++ entIds ((recsFrom st0 Ds (lo + 1) k).map Prod.snd)).Perm
            (fresh :: (entIds D.blocks ++ entIds ((recsFrom st0 Ds (lo + 1) k).map Prod.snd))) := by
          rw [hD'blocks]
          exact (List.Perm.append_right _ (entIds_prependAt _ _ _ (ownerIdx_lt lam D.blocks hwf.1)))
        refine hperm.nodup_iff.mpr (List.nodup_cons.mpr ⟨?_, h3⟩)
        rw [List.map_append, holdsnd, entIds_append] at hfreshNot
        exact hfreshNot
    refine ⟨⟨hLv', hP', hBA, by rw [hFo.lens]; exact hDL.basel, by rw [hbaseq]; exact hDL.base0,
      fun j hj => ?_, fun j hj => ?_, by rw [hnewfam]; exact hnewR, ?_, by rw [hbfr]; exact hDL.bfcap⟩,
      by
        split_ifs at hc2' with hh
        · exact absurd hh hskip
        · rw [if_neg hskip]; exact hc2'⟩
    · rw [hbaseq, hbaseq]
      simp only [Function.update_apply, show lo + j + 1 ≠ lo by omega, if_false]
      exact hDL.chain j hj
    · rw [hbaseq]
      rcases Nat.eq_zero_or_pos j with rfl | hjp
      · simpa [Function.update_self] using hD'
      · simp only [Function.update_apply, show lo + j ≠ lo by omega, if_false]
        refine DRep.of_insFacts_other hFo (hDL.drep j hj) (fun i hi => ?_) (fun x hx => ?_)
        · exact hothers _ (mem_recsFrom st0 Ds k (lo + 1) (lo + j) i (by omega) (by omega) hi)
        · obtain ⟨b, hb, hxb⟩ := mem_allEnts.mp hx
          obtain ⟨i, hi, hbi⟩ := List.mem_iff_getElem.mp hb
          have := hfreshO _ (mem_recsFrom st0 Ds k (lo + 1) (lo + j) i (by omega) (by omega) hi)
          exact this x (by simp only; rw [hbi]; exact hxb)
    · rw [hnewfam, hbfr]
      intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · have : q.1 ∈ (List.range D.blocks.length).map f := by
          rw [← hzipfst]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
        obtain ⟨i, hi, hqi⟩ := List.mem_map.mp this
        have hmem := mem_recsOf st0 bse D.blocks i (List.mem_range.mp hi)
        have := hDL.bfresh _ (by rw [hfamsplit]; exact List.mem_append_left _ hmem)
        rw [← hqi]; exact this
      · exact hDL.bfresh q (by rw [hfamsplit]; exact List.mem_append_right _ hq)

end Frontier.CHD.DGlob
