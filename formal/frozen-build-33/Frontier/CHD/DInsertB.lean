import Frontier.CHD.DInsertA

/-!
# DInsertB — the RAM Insert program of DS' and its refinement (B-L3, agent-02, NON-GATE)

Parts 5–7: `insTail` (create the entry, prepend it, update the block record and `live`),
`skipTest`, and the main theorem `insRAM_spec` refining `insertNS` (= DLazy `insertL`'s state).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.DIns

open Frontier Frontier.CHD Frontier.CHD.DB

variable {κ : Type*} [DecidableEq κ] {α : Type*} [LinearOrder α] [Inhabited α]

/-! ## Part 5: the program -/

section Prog

open Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD.MLab Frontier.CHD.LabTab Frontier.RAM.BSearch

variable {G : Graph} {s : Fin G.n}

open WExpr Stmt in
/-- After the search: create entry `fresh`, prepend it to block `stk[ds.b + bs.lo]`, set live. -/
def insTail : Stmt :=
  seq (wset "ins.bid" (load "dsl.stk" (add (var "ds.b") (var "bs.lo"))))
  (seq (wset "ins.id" (var "ds.fresh"))
  (seq (wset "ds.fresh" (add (var "ds.fresh") (lit 1)))
  (seq (storeA entA "ins.id" KB)
  (seq (wstore "ent.key" (var "ins.id") (var "ds.v"))
  (seq (wstore "ent.nxt" (var "ins.id") (load "blk.hd" (var "ins.bid")))
  (seq (wstore "blk.hd" (var "ins.bid") (add (var "ins.id") (lit 1)))
  (seq (ite (load "blk.tl" (var "ins.bid")) skip
         (wstore "blk.tl" (var "ins.bid") (add (var "ins.id") (lit 1))))
  (seq (wstore "blk.cnt" (var "ins.bid") (add (load "blk.cnt" (var "ins.bid")) (lit 1)))
       (wstore "live" (var "ds.v") (add (var "ins.id") (lit 1)))))))))))

/-- Word arrays the insertion writes. -/
def insWA : List String :=
  ["ent.key", "ent.nxt", "ent.h", "ent.v", "ent.e", "ent.r", "blk.hd", "blk.tl", "blk.cnt", "live"]

theorem insTail_spec (st : State ℝ≥0) (bse j bid fid : ℕ) (v : Fin G.n) (k : MLabel G)
    (hb : st.w "ds.b" = bse) (hj : st.w "bs.lo" = j) (hbid : st.wa "dsl.stk" (bse + j) = bid)
    (hstk : bse + j < st.wlen "dsl.stk") (hf : st.w "ds.fresh" = fid) (hv : st.w "ds.v" = v)
    (hK : Holds st KB k) (hbl : bid < st.wlen "blk.hd" ∧ bid < st.wlen "blk.tl" ∧
      bid < st.wlen "blk.cnt") (hel : EntArrs st (fid + 1)) (hlive : (v : ℕ) < st.wlen "live")
    (hcap : bse + j < st.cap ∧ fid + 2 < st.cap ∧ st.wa "blk.cnt" bid + 1 < st.cap) :
    Runs realOps insTail st (fun r => InsFacts (G := G) st r fid bid v k ∧
      r.w "ds.fresh" = fid + 1 ∧
      Unchanged st r insWA [entA.l] ["ins.bid", "ins.id", "ds.fresh"] [] ∧
      st.cost + 1 ≤ r.cost ∧ r.cost ≤ st.cost + 16) := by
  obtain ⟨b1, b2, b3⟩ := hbl
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hel
  obtain ⟨c1, c2, c3⟩ := hcap
  apply wp_sound
  rw [insTail, wp_seq, wp_wset_of (a := bid) (by simp [hb, hj, fit_of_lt c1, hstk, hbid]),
    wp_seq, wp_wset_of (a := fid) (by simp [hf]), wp_seq,
    wp_wset_of (a := fid + 1) (by simp [hf, fit_of_lt (show 1 < st.cap by omega),
      fit_of_lt (show fid + 1 < st.cap by omega)])]
  set q3 := (((((st.setW "ins.bid" bid).charge 1).setW "ins.id" fid).charge 1).setW "ds.fresh"
    (fid + 1)).charge 1 with hq3
  have hK3 : Holds q3 KB k := by
    obtain ⟨k1, k2, k3, k4, k5⟩ := hK
    exact ⟨by simpa [hq3, KB] using k1, by simpa [hq3, KB] using k2, by simpa [hq3, KB] using k3,
      by simpa [hq3, KB] using k4, by simpa [hq3, KB] using k5⟩
  have hInB : entA.InB q3 fid := by
    unfold LArr.InB
    simp only [hq3, State.charge_vlen, State.charge_wlen, State.setW_wlen, State.setW_vlen, entA]
      at e3 e4 e5 e6 e7 ⊢
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  obtain ⟨i1, i2, i3, i4, i5⟩ := hInB
  obtain ⟨k1, k2, k3, k4, k5⟩ := hK3
  have hq3w : ∀ z, z ∉ ["ins.bid", "ins.id", "ds.fresh"] → q3.w z = st.w z := by
    intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    simp [hq3, hz.1, hz.2.1, hz.2.2]
  have hq3id : q3.w "ins.id" = fid := by simp [hq3]
  have hq3bid : q3.w "ins.bid" = bid := by simp [hq3]
  have hq3v : q3.w "ds.v" = v := by rw [hq3w _ (by decide)]; exact hv
  have hq3f : q3.w "ds.fresh" = fid + 1 := by simp [hq3]
  have hkey : fid < q3.wlen "ent.key" := by simp [hq3]; omega
  have hnxt : fid < q3.wlen "ent.nxt" := by simp [hq3]; omega
  have hhd : bid < q3.wlen "blk.hd" := by simp [hq3]; exact b1
  have htl : bid < q3.wlen "blk.tl" := by simp [hq3]; exact b2
  have hcnt : bid < q3.wlen "blk.cnt" := by simp [hq3]; exact b3
  have hlv : (v : ℕ) < q3.wlen "live" := by simp [hq3]; exact hlive
  have hcq : q3.cap = st.cap := by simp [hq3]
  have hq3a : q3.wa = st.wa ∧ q3.va = st.va ∧ q3.wlen = st.wlen ∧ q3.vlen = st.vlen := by
    simp [hq3]
  simp only [entA] at i1 i2 i3 i4 i5
  have hf1 : fit q3.cap 1 = some 1 := fit_of_lt (by rw [hcq]; omega)
  have hf2 : fit q3.cap (fid + 1) = some (fid + 1) := fit_of_lt (by rw [hcq]; omega)
  have hf3 : fit q3.cap (q3.wa "blk.cnt" bid + 1) = some (q3.wa "blk.cnt" bid + 1) :=
    fit_of_lt (by rw [hcq, hq3a.1]; omega)
  simp only [wp_seq, storeA, wp, evalV_var', evalW_var, evalW_load', evalW_add', evalW_lit',
    State.charge_w, State.charge_v, State.charge_wa, State.charge_va, State.charge_wlen,
    State.charge_vlen, State.charge_cap, State.storeV_w, State.storeV_v, State.storeV_wa,
    State.storeV_wlen, State.storeV_vlen, State.storeV_cap, State.storeW_w, State.storeW_v,
    State.storeW_wa, State.storeW_wlen, State.storeW_vlen, State.storeW_cap, State.storeW_va,
    hq3id, hq3bid, hq3v, Option.bind_some, ↓reduceIte, i1, i2, i3, i4, i5, hkey, hnxt, hhd, htl,
    hcnt, hlv, true_and, String.reduceEq, and_false, false_and, entA, and_self, hf1, hf2, hf3,
    k1, k2, k3, k4, k5]
  obtain ⟨hwa, hva, hwl, hvl⟩ := hq3a
  have hq3c : q3.cost = st.cost + 3 := by simp [hq3]
  have hvne : ∀ u : ℕ, u ≠ (v : ℕ) → True := fun _ _ => trivial
  -- the common part of both branches, from per-array descriptions of the final state
  have post : ∀ (r : State ℝ≥0) (tlv : ℕ),
      (tlv = if st.wa "blk.tl" bid = 0 then fid + 1 else st.wa "blk.tl" bid) →
      r.wa "ent.key" = (fun j => if j = fid then (v : ℕ) else st.wa "ent.key" j) →
      r.wa "ent.nxt" = (fun j => if j = fid then st.wa "blk.hd" bid else st.wa "ent.nxt" j) →
      r.wa "ent.h" = (fun j => if j = fid then k.hops else st.wa "ent.h" j) →
      r.wa "ent.v" = (fun j => if j = fid then (k.v : ℕ) else st.wa "ent.v" j) →
      r.wa "ent.e" = (fun j => if j = fid then encE k.e else st.wa "ent.e" j) →
      r.wa "ent.r" = (fun j => if j = fid then k.ver else st.wa "ent.r" j) →
      r.va "ent.len" = (fun j => if j = fid then k.len else st.va "ent.len" j) →
      r.wa "blk.hd" = (fun j => if j = bid then fid + 1 else st.wa "blk.hd" j) →
      r.wa "blk.tl" = (fun j => if j = bid then tlv else st.wa "blk.tl" j) →
      r.wa "blk.cnt" = (fun j => if j = bid then st.wa "blk.cnt" bid + 1 else st.wa "blk.cnt" j) →
      r.wa "live" = (fun j => if j = (v : ℕ) then fid + 1 else st.wa "live" j) →
      (∀ a, a ∉ insWA → r.wa a = st.wa a) → (∀ a, a ≠ "ent.len" → r.va a = st.va a) →
      r.wlen = st.wlen → r.vlen = st.vlen → r.w "ds.fresh" = fid + 1 →
      (∀ z, z ∉ ["ins.bid", "ins.id", "ds.fresh"] → r.w z = st.w z) → r.v = st.v →
      r.cap = st.cap → r.procs = st.procs →
      InsFacts (G := G) st r fid bid v k ∧ r.w "ds.fresh" = fid + 1 ∧
        Unchanged st r insWA [entA.l] ["ins.bid", "ins.id", "ds.fresh"] [] := by
    intro r tlv htlv hkey' hnxt' hh' hv'' he' hr' hl' hhd' htl' hcnt' hlive' hoth hothv hwl' hvl'
      hfr hw' hvr hcap' hpr'
    have oblkA : ∀ a, a ∈ ["blk.bot", "blk.len", "blk.h", "blk.v", "blk.e", "blk.r", "dsl.stk",
        "dsl.sz"] → a ∉ insWA := by decide
    refine ⟨⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun b' hb' => ?_, ?_, ?_, ?_, ?_, fun a => by rw [hwl'], fun a => by rw [hvl']⟩, hfr, ?_⟩
    · rw [hkey']; simp [hj]
    · rw [hnxt']; simp [hj]
    · simp only [entA]
      refine ⟨by rw [hl']; simp [hj], ?_, ?_, ?_, ?_⟩
      · rw [hh']; simp [hj]
      · rw [hv'']; simp [hj]
      · rw [he']; simp [hj]
      · rw [hr']; simp [hj]
    · rw [hkey']; simp
    · rw [hnxt']; simp
    · simp only [AHolds, entA]
      refine ⟨by rw [hl']; simp, by rw [hh']; simp, by rw [hv'']; simp,
        by rw [he']; simp, by rw [hr']; simp⟩
    · rw [hhd']; simp
    · rw [hcnt']; simp
    · rw [htl']; simp [htlv]
    · refine ⟨by rw [hhd']; simp [hb'], by rw [htl']; simp [hb'], by rw [hcnt']; simp [hb']⟩
    · exact hoth _ (oblkA _ (by simp))
    · exact ⟨hothv _ (by decide), hoth _ (oblkA _ (by simp [blkA])), hoth _ (oblkA _ (by simp [blkA])),
        hoth _ (oblkA _ (by simp [blkA])), hoth _ (oblkA _ (by simp [blkA]))⟩
    · exact ⟨hoth _ (oblkA _ (by simp)), hoth _ (oblkA _ (by simp))⟩
    · refine ⟨by rw [hlive']; simp, fun u hu => ?_⟩
      rw [hlive']; simp [hu]
    · refine ⟨fun a ha => ⟨by rw [hoth a ha], by rw [hwl']⟩,
        fun a ha => ⟨by rw [hothv a (by simpa [entA] using ha)], by rw [hvl']⟩, hw',
        fun x _ => by rw [hvr], hcap', hpr'⟩
  have hbt : q3.wa "blk.tl" bid = st.wa "blk.tl" bid := by rw [hwa]
  have hbc : q3.wa "blk.cnt" bid = st.wa "blk.cnt" bid := by rw [hwa]
  have hbh : q3.wa "blk.hd" bid = st.wa "blk.hd" bid := by rw [hwa]
  have hoth_tac : ∀ a, a ∉ insWA → a ∉ ["ent.key", "ent.nxt", "ent.h", "ent.v", "ent.e", "ent.r",
      "blk.hd", "blk.tl", "blk.cnt", "live"] := fun a ha => ha
  refine ⟨fun htl0 => ?_, fun htl0 => ?_⟩
  · have htv : st.wa "blk.tl" bid = (if st.wa "blk.tl" bid = 0 then fid + 1 else
        st.wa "blk.tl" bid) := by rw [if_neg (by rwa [← hbt])]
    refine (fun hP => ⟨hP.1, hP.2.1, hP.2.2, ?_, ?_⟩) (post _ (st.wa "blk.tl" bid) htv
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    all_goals first
      | (funext j; simp [State.storeW, State.storeV, State.charge, hwa, hva, hbc]; done)
      | (funext j; simp [State.storeW, State.storeV, State.charge, hwa, hva, hbc, hbt]; done)
      | (intro a ha; simp only [insWA, List.mem_cons, List.not_mem_nil, or_false, not_or] at ha;
          funext j; simp [State.storeW, State.storeV, State.charge, hwa, ha]; done)
      | (intro a ha; funext j; simp [State.storeW, State.storeV, State.charge, hva, ha]; done)
      | (simp [State.storeW, State.storeV, State.charge, hwl]; done)
      | (simp [State.storeW, State.storeV, State.charge, hvl]; done)
      | (simp [State.storeW, State.storeV, State.charge, hq3f]; done)
      | (intro z hz; simp [State.storeW, State.storeV, State.charge, hq3w z hz]; done)
      | (funext z; simp [State.storeW, State.storeV, State.charge, hq3]; done)
      | (simp [State.storeW, State.storeV, State.charge, hcq]; done)
      | (simp [State.storeW, State.storeV, State.charge, hq3]; done)
      | (simp [State.storeW, State.storeV, State.charge, hq3c]; done)
      | (funext j; simp only [State.storeW, State.storeV, State.charge, hwa, String.reduceEq,
          false_and, if_false]; split_ifs with h <;> simp [h]; done)
  · have htv : fid + 1 = (if st.wa "blk.tl" bid = 0 then fid + 1 else st.wa "blk.tl" bid) := by
      rw [if_pos (by rwa [← hbt])]
    refine (fun hP => ⟨hP.1, hP.2.1, hP.2.2, ?_, ?_⟩) (post _ (fid + 1) htv
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    all_goals first
      | (funext j; simp [State.storeW, State.storeV, State.charge, hwa, hva, hbc]; done)
      | (funext j; simp [State.storeW, State.storeV, State.charge, hwa, hva, hbc, hbt]; done)
      | (intro a ha; simp only [insWA, List.mem_cons, List.not_mem_nil, or_false, not_or] at ha;
          funext j; simp [State.storeW, State.storeV, State.charge, hwa, ha]; done)
      | (intro a ha; funext j; simp [State.storeW, State.storeV, State.charge, hva, ha]; done)
      | (simp [State.storeW, State.storeV, State.charge, hwl]; done)
      | (simp [State.storeW, State.storeV, State.charge, hvl]; done)
      | (simp [State.storeW, State.storeV, State.charge, hq3f]; done)
      | (intro z hz; simp [State.storeW, State.storeV, State.charge, hq3w z hz]; done)
      | (funext z; simp [State.storeW, State.storeV, State.charge, hq3]; done)
      | (simp [State.storeW, State.storeV, State.charge, hcq]; done)
      | (simp [State.storeW, State.storeV, State.charge, hq3]; done)
      | (simp [State.storeW, State.storeV, State.charge, hq3c]; done)
      | (funext j; simp only [State.storeW, State.storeV, State.charge, hwa, String.reduceEq,
          false_and, if_false]; split_ifs with h <;> simp [h]; done)

end Prog

/-! ## Part 6: the skip test -/

section Skip

open Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD.MLab Frontier.CHD.LabTab

variable {G : Graph} {s : Fin G.n}

open WExpr Stmt in
/-- `ins.lt := [λ < old]` if `v` has a live entry of value `old`, else `1` (so `ins.lt = 0` iff
the insertion is skipped). -/
def skipTest : Stmt :=
  seq (wset "ins.e0" (load "live" (var "ds.v")))
  (ite (var "ins.e0")
     (seq (wset "ins.ei" (sub (var "ins.e0") (lit 1)))
     (seq (loadA entA "ins.ei" YB)
          (cmp KB YB "ins.c1" "ins.c2" "ins.lt")))
     (wset "ins.lt" (lit 1)))

/-- Registers the skip test writes. -/
def skipW : List String :=
  ["ins.e0", "ins.ei", "ins.yh", "ins.yv", "ins.ye", "ins.yr", "ins.c1", "ins.c2", "ins.lt"]

open Classical in
theorem skipTest_wp (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (hH : GoodHist (s := s) H V) (L : Live (Fin G.n) (WLab G s)) (ecap : ℕ) (st : State ℝ≥0)
    (hLv : LiveRep st H V L) (hEA : EntArrs st ecap)
    (hLf : ∀ u i a, L u = some (i, a) → i < ecap) (v : Fin G.n) (hv : st.w "ds.v" = v)
    (k : MLabel G) (p : List (Fin G.m)) (hK : Holds st KB k) (hKp : Rep (s := s) H V k p)
    (hcap : 1 < st.cap) :
    wp realOps skipTest (fun r =>
      r.w "ins.lt" = (if skipIns L v ((toW p : WalkOrd G s) : WLab G s) then 0 else 1) ∧
      Unchanged st r [] [] skipW [YB.l] ∧ st.cost + 1 ≤ r.cost ∧ r.cost ≤ st.cost + 22) st := by
  obtain ⟨hlen, hL⟩ := hLv
  obtain ⟨hlw, hLe⟩ := hL v
  have hvl : (v : ℕ) < st.wlen "live" := lt_of_lt_of_le v.isLt hlen
  rw [skipTest, wp_seq, wp_wset_of (a := liveWord (L v)) (by simp [hv, hvl, hlw])]
  set q1 := (st.setW "ins.e0" (liveWord (L v))).charge 1 with hq1
  have hU1 : Unchanged st q1 [] [] skipW [YB.l] := by simp [hq1, unch_setW, skipW]
  rw [wp_ite_var]
  cases hLv' : L v with
  | none =>
    have h0 : q1.w "ins.e0" = 0 := by simp [hq1, hLv', liveWord]
    refine ⟨fun h => absurd h0 h, fun _ => ?_⟩
    refine wp_mono _ ?_ _ (wset_lit_wp (ops := realOps) "ins.lt" 1 (q1.charge 1)
      (by simp [hq1]; exact hcap))
    rintro r ⟨h1, h2, h3⟩
    refine ⟨by rw [h1]; simp [skipIns, hLv'], ((hU1.comp (Unchanged.charge q1 1 [] [] [] [])).comp
      h2).mono (by simp) (by simp) (by simp only [skipW]; decide) (by simp), ?_, ?_⟩
    · simp [hq1] at h3; omega
    · simp [hq1] at h3; omega
  | some ia =>
    obtain ⟨i, a⟩ := ia
    have hne : q1.w "ins.e0" ≠ 0 := by simp [hq1, hLv', liveWord]
    refine ⟨fun _ => ?_, fun h => absurd h hne⟩
    obtain ⟨hkey, m, q, hAm, hRm, ha⟩ := hLe i a hLv'
    have hi : i < ecap := hLf v i a hLv'
    rw [wp_seq, wp_wset_of (a := i) (by
      simp [hq1, hLv', liveWord, fit_of_lt hcap])]
    set q2 := ((q1.charge 1).setW "ins.ei" i).charge 1 with hq2
    have hU2 : Unchanged st q2 [] [] skipW [YB.l] :=
      ((hU1.comp (Unchanged.charge q1 1 [] [] [] [])).comp (by
        simp [hq2, unch_setW, skipW] : Unchanged (q1.charge 1) q2 [] [] skipW [YB.l])).mono
        (by simp) (by simp) (by intro a; simp) (by intro a; simp)
    obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hEA
    have hInB : entA.InB q2 i := by
      unfold LArr.InB
      simp only [hq2, hq1, State.charge_vlen, State.charge_wlen, State.setW_wlen, State.setW_vlen,
        entA] at e3 e4 e5 e6 e7 ⊢
      exact ⟨by omega, by omega, by omega, by omega, by omega⟩
    have hAm2 : AHolds q2 entA i m := by
      obtain ⟨a1, a2, a3, a4, a5⟩ := hAm
      exact ⟨by simpa [hq2, hq1] using a1, by simpa [hq2, hq1] using a2,
        by simpa [hq2, hq1] using a3, by simpa [hq2, hq1] using a4, by simpa [hq2, hq1] using a5⟩
    rw [wp_seq]
    refine wp_mono _ ?_ _ (loadA_wp entA "ins.ei" YB ⟨by decide, by decide⟩ q2 i (by simp [hq2])
      hInB m hAm2)
    rintro r3 ⟨hY3, hU3, hc3⟩
    have hK3 : Holds r3 KB k :=
      (hK.of_unchanged hU2 (by decide) (by decide)).of_unchanged hU3 (by decide) (by decide)
    have hcap3 : 1 < r3.cap := by rw [hU3.cap, hU2.cap]; exact hcap
    refine wp_mono _ ?_ _ (cmp_wp (ops := realOps) (fun a b => rfl) "ins.lt"
      ⟨by decide, by decide, by decide, by decide, by decide⟩ r3 hcap3)
    rintro r ⟨h1, h2, h3, h4⟩
    rw [cbit_eq hK3 hY3] at h1
    have hiff := lt_iff hH hKp hRm
    refine ⟨?_, ((hU2.comp hU3).comp h2).mono (by simp) (by simp)
      (by simp only [skipW, YB, LReg.ws]; decide) (by simp [YB]), ?_, ?_⟩
    · rw [h1]
      simp only [skipIns, hLv', ha]
      by_cases hkm : k.lt m
      · have hlt := hiff.mp hkm
        rw [if_pos hkm, if_neg]
        simp only [decide_eq_true_eq, not_le]
        exact WithTop.coe_lt_coe.mpr hlt
      · rw [if_neg hkm, if_pos]
        simp only [decide_eq_true_eq]
        exact WithTop.coe_le_coe.mpr (not_lt.mp (fun h => hkm (hiff.mpr h)))
    · simp [hq2, hq1] at hc3; omega
    · simp [hq2, hq1] at hc3; omega

end Skip

/-! ## Part 7a: structure-level update lemmas -/

section UpdateD

open Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD.MLab Frontier.CHD.LabTab

variable {G : Graph} {s : Fin G.n}

theorem InsFacts.of_arr_eq {st st' r : State ℝ≥0} {fid bid : ℕ} {v : Fin G.n} {k : MLabel G}
    (h : InsFacts st' r fid bid v k) (hwa : st'.wa = st.wa) (hva : st'.va = st.va)
    (hwl : st'.wlen = st.wlen) (hvl : st'.vlen = st.vlen) : InsFacts st r fid bid v k := by
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, h.nkey, ?_, h.nlab, h.hd, ?_, ?_,
    fun b' hb' => ?_, ?_, ?_, ?_, ?_, fun a => ?_, fun a => ?_⟩
  · rw [h.ekey j hj, hwa]
  · rw [h.enxt j hj, hwa]
  · obtain ⟨e1, e2, e3, e4, e5⟩ := h.eflds j hj
    rw [hva] at e1; rw [hwa] at e2 e3 e4 e5; exact ⟨e1, e2, e3, e4, e5⟩
  · rw [h.nnxt, hwa]
  · rw [h.cnt, hwa]
  · rw [h.tl, hwa]
  · obtain ⟨o1, o2, o3⟩ := h.oblk b' hb'
    rw [hwa] at o1 o2 o3; exact ⟨o1, o2, o3⟩
  · rw [h.bot, hwa]
  · obtain ⟨s1, s2, s3, s4, s5⟩ := h.sep
    rw [hva] at s1; rw [hwa] at s2 s3 s4 s5; exact ⟨s1, s2, s3, s4, s5⟩
  · obtain ⟨t1, t2⟩ := h.stk
    rw [hwa] at t1 t2; exact ⟨t1, t2⟩
  · obtain ⟨l1, l2⟩ := h.live
    exact ⟨l1, fun u hu => (l2 u hu).trans (by rw [hwa])⟩
  · rw [h.lens a, hwl]
  · rw [h.vlens a, hvl]

theorem DRep.insert {st r : State ℝ≥0} {fid bid : ℕ} {v : Fin G.n} {k : MLabel G}
    {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {bcap lv bse : ℕ}
    {D : DStr (Fin G.n) (WLab G s)} {p : List (Fin G.m)} (hF : InsFacts st r fid bid v k)
    (hD : DRep st H V bcap lv bse D) (o : ℕ) (ho : o < D.blocks.length)
    (hbid : bid = stkId st bse D.blocks.length o)
    (hfid : ∀ x ∈ allEnts D.blocks, x.id ≠ fid) (hcap : fid < st.wlen "ent.nxt")
    (hkp : Rep (s := s) H V k p) :
    DRep r H V bcap lv bse
      { D with blocks := prependAt ⟨fid, v, ((toW p : WalkOrd G s) : WLab G s)⟩ o D.blocks } := by
  have hlen := prependAt_length (⟨fid, v, ((toW p : WalkOrd G s) : WLab G s)⟩ :
    Entry (Fin G.n) (WLab G s)) o D.blocks
  have hstk : ∀ i, stkId r bse D.blocks.length i = stkId st bse D.blocks.length i := by
    intro i; unfold stkId; rw [hF.stk.1]
  have hmem : ∀ i (hi : i < D.blocks.length), ∀ x ∈ (D.blocks[i]).ents, x.id ≠ fid :=
    fun i hi x hx => hfid x (mem_allEnts.mpr ⟨_, List.getElem_mem hi, hx⟩)
  refine ⟨?_, ?_, ?_, fun i hi => ?_, fun i j hi hj => ?_, fun i hi => ?_⟩
  · simp only; rw [hlen, hF.stk.2]; exact hD.sz
  · rw [hF.lens]; exact hD.szb
  · simp only; rw [hlen, hF.lens]; exact hD.stkb
  · simp only at hi ⊢
    rw [hlen] at hi
    have hi' : i < D.blocks.length := hi
    rw [show (prependAt ⟨fid, v, ((toW p : WalkOrd G s) : WLab G s)⟩ o D.blocks).length =
      D.blocks.length from hlen, hstk]
    by_cases hio : i = o
    · subst hio
      rw [prependAt_get_self _ i D.blocks hi', ← hbid]
      rw [hbid] at hF
      exact BlkRep.insert_owner (hbid ▸ hF) (hbid ▸ hD.blk i hi') (hmem i hi') hcap hkp
    · rw [prependAt_get_ne _ o D.blocks i hi' hio]
      refine BlkRep.insert_other hF (hD.blk i hi') ?_ (hmem i hi')
      rw [hbid]; exact fun h => hio (hD.inj i o hi' ho h)
  · simp only at hi hj ⊢
    rw [hlen] at hi hj
    rw [show (prependAt ⟨fid, v, ((toW p : WalkOrd G s) : WLab G s)⟩ o D.blocks).length =
      D.blocks.length from hlen, hstk, hstk]
    exact hD.inj i j hi hj
  · simp only at hi ⊢
    rw [hlen] at hi
    rw [show (prependAt ⟨fid, v, ((toW p : WalkOrd G s) : WLab G s)⟩ o D.blocks).length =
      D.blocks.length from hlen, hstk]
    exact hD.bidb i hi

theorem LiveRep.insert {st r : State ℝ≥0} {fid bid : ℕ} {v : Fin G.n} {k : MLabel G}
    {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {L : Live (Fin G.n) (WLab G s)}
    {p : List (Fin G.m)} (hF : InsFacts st r fid bid v k) (hL : LiveRep st H V L)
    (hLf : ∀ u i a, L u = some (i, a) → i ≠ fid) (hkp : Rep (s := s) H V k p) :
    LiveRep r H V (Function.update L v (some (fid, ((toW p : WalkOrd G s) : WLab G s)))) := by
  obtain ⟨hlen, hL'⟩ := hL
  refine ⟨by rw [hF.lens]; exact hlen, fun u => ?_⟩
  by_cases hu : u = v
  · subst hu
    refine ⟨by rw [hF.live.1]; simp [liveWord], fun i a h => ?_⟩
    simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hF.nkey, k, p, hF.nlab, hkp, rfl⟩
  · have hu' : (u : ℕ) ≠ (v : ℕ) := fun h => hu (Fin.ext h)
    obtain ⟨h1, h2⟩ := hL' u
    refine ⟨by rw [hF.live.2 u hu', Function.update_of_ne hu]; exact h1, fun i a h => ?_⟩
    rw [Function.update_of_ne hu] at h
    exact (h2 i a h).of_insFacts hF (hLf u i a h)

/-- **Frame for the other structures**: a DS' structure whose blocks are not the updated block and
whose entries are older than the new entry keeps its representation. -/
theorem DRep.of_insFacts_other {st r : State ℝ≥0} {fid bid : ℕ} {v : Fin G.n} {k : MLabel G}
    {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {bcap lv bse : ℕ}
    {D : DStr (Fin G.n) (WLab G s)} (hF : InsFacts st r fid bid v k)
    (hD : DRep st H V bcap lv bse D)
    (hbid : ∀ i < D.blocks.length, stkId st bse D.blocks.length i ≠ bid)
    (hfid : ∀ x ∈ allEnts D.blocks, x.id ≠ fid) : DRep r H V bcap lv bse D := by
  have hstk : ∀ i, stkId r bse D.blocks.length i = stkId st bse D.blocks.length i := by
    intro i; unfold stkId; rw [hF.stk.1]
  refine ⟨by rw [hF.stk.2]; exact hD.sz, by rw [hF.lens]; exact hD.szb,
    by rw [hF.lens]; exact hD.stkb, fun i hi => ?_, fun i j hi hj => ?_, fun i hi => ?_⟩
  · rw [hstk]
    exact BlkRep.insert_other hF (hD.blk i hi) (hbid i hi)
      (fun x hx => hfid x (mem_allEnts.mpr ⟨_, List.getElem_mem hi, hx⟩))
  · rw [hstk, hstk]; exact hD.inj i j hi hj
  · rw [hstk]; exact hD.bidb i hi

end UpdateD

/-! ## Part 7b: the insertion program and its refinement -/

section Main

open Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD.MLab Frontier.CHD.LabTab Frontier.RAM.BSearch

variable {G : Graph} {s : Fin G.n}

open WExpr Stmt in
/-- Search the owner block and insert. -/
def insBody : Stmt :=
  seq (wset "bs.sz" (load "dsl.sz" (var "ds.lv"))) (seq (bsearch probe) insTail)

open WExpr Stmt in
/-- **DS' Insert** (`insertNS` = the state part of DLazy's `insertL`).  Inputs: `ds.v` (key),
the key block `KB` (value `λ`), `ds.lv` (level), `ds.b` (stack base of the level). -/
def insRAM : Stmt := seq skipTest (ite (var "ins.lt") insBody skip)

/-- Registers the insertion may write. -/
def insWR : List String :=
  skipW ++ ["bs.sz", "bs.lo", "bs.hi", "bs.mid", "bs.p"] ++ probeW ++
    ["ins.bid", "ins.id", "ds.fresh"]

theorem ents_len_le {D : DStr (Fin G.n) (WLab G s)} {fresh : ℕ} (hid : IdsNodup D)
    (hfr : FreshOK fresh D) {b : Block (Fin G.n) (WLab G s)} (hb : b ∈ D.blocks) :
    b.ents.length ≤ fresh := by
  have hsub : (b.ents.map (·.id)).Sublist ((allEnts D.blocks).map (·.id)) := by
    unfold allEnts
    exact (List.sublist_flatten_of_mem (List.mem_map.mpr ⟨b, hb, rfl⟩)).map _
  have hnd := hid.sublist hsub
  have hall : ∀ i ∈ b.ents.map (·.id), i < fresh := by
    intro i hi
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hi
    exact hfr x (mem_allEnts.mpr ⟨b, hb, hx⟩)
  calc b.ents.length = (b.ents.map (·.id)).length := by simp
    _ = (b.ents.map (·.id)).toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ (Finset.range fresh).card := Finset.card_le_card (fun i hi =>
        Finset.mem_range.mpr (hall i (List.mem_toFinset.mp hi)))
    _ = fresh := Finset.card_range fresh

theorem LiveRep.of_unchanged {st r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)}
    {V : Fin G.n → ℕ} {L : Live (Fin G.n) (WLab G s)} {wa va wr vr : List String}
    (h : LiveRep st H V L) (hu : Unchanged st r wa va wr vr) (hw : ∀ a ∈ wa, a ∉ dW)
    (hv : ∀ a ∈ va, a ∉ dV) : LiveRep r H V L := by
  obtain ⟨hlen, hL⟩ := h
  have e := wa_eq hu hw (show "live" ∈ dW by simp [dW])
  refine ⟨by rw [e.2]; exact hlen, fun u => ⟨by rw [e.1]; exact (hL u).1, fun i a hia =>
    ((hL u).2 i a hia).of_unchanged hu hw hv⟩⟩

theorem ProbeCtx.of_unchanged {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap lv bse : ℕ} {D : DStr (Fin G.n) (WLab G s)} {k : MLabel G} {p : List (Fin G.m)}
    {st r : State ℝ≥0} {W : List String} (h : ProbeCtx H V bcap lv bse D k p st)
    (hu : Unchanged st r [] [] W [YB.l]) (hW : "ds.lv" ∉ W ∧ "ds.b" ∉ W ∧ ∀ a ∈ KB.ws, a ∉ W) :
    ProbeCtx H V bcap lv bse D k p r := by
  obtain ⟨hD, hBA, hlv, hb, hK, hKp, hc1, hc2⟩ := h
  have hw0 : ∀ a ∈ ([] : List String), a ∉ dW := by simp
  have hv0 : ∀ a ∈ ([] : List String), a ∉ dV := by simp
  exact ⟨hD.of_unchanged hu hw0 hv0, hBA.of_unchanged hu hw0 hv0, by rw [hu.wreg _ hW.1]; exact hlv,
    by rw [hu.wreg _ hW.2.1]; exact hb, hK.of_unchanged hu hW.2.2 (by simp [KB, YB]), hKp,
    by rw [hu.cap]; exact hc1, by rw [hu.cap]; exact hc2⟩

open Classical in
/-- **Spec of the RAM Insert.**  Refines `insertNS` (= the state part of agent-04's DLazy
`insertL`): afterwards the D structure, the live map and the pool counter represent
`insertNS L fresh D v λ`; only the D arrays `insWA`/`ent.len` and the registers `insWR` are
written; cost `O(log |D.blocks|)`. -/
theorem insRAM_spec (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (hH : GoodHist (s := s) H V) (bcap ecap lv bse fresh : ℕ) (D : DStr (Fin G.n) (WLab G s))
    (L : Live (Fin G.n) (WLab G s)) (st : State ℝ≥0) (hD : DRep st H V bcap lv bse D)
    (hBA : BlkArrs st bcap) (hLv : LiveRep st H V L) (hP : PoolRep st fresh ecap)
    (hwf : WF L D) (hfr : FreshOK fresh D) (hid : IdsNodup D)
    (hLf : ∀ u i a, L u = some (i, a) → i < fresh)
    (v : Fin G.n) (hv : st.w "ds.v" = v) (hlv : st.w "ds.lv" = lv) (hb : st.w "ds.b" = bse)
    (k : MLabel G) (p : List (Fin G.m)) (hK : Holds st KB k) (hKp : Rep (s := s) H V k p)
    (hfr1 : fresh + 1 < ecap) (hcap : 2 * D.blocks.length + ecap + bse + 4 < st.cap) :
    Runs realOps insRAM st (fun r =>
      DRep r H V bcap lv bse (insertNS L fresh D v ((toW p : WalkOrd G s) : WLab G s)).2.2 ∧
      BlkArrs r bcap ∧
      LiveRep r H V (insertNS L fresh D v ((toW p : WalkOrd G s) : WLab G s)).1 ∧
      PoolRep r (insertNS L fresh D v ((toW p : WalkOrd G s) : WLab G s)).2.1 ecap ∧
      Unchanged st r insWA [entA.l] insWR [YB.l] ∧
      (skipIns L v ((toW p : WalkOrd G s) : WLab G s) = false → ∃ o < D.blocks.length,
        InsFacts st r fresh (stkId st bse D.blocks.length o) v k) ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost +
        (if skipIns L v ((toW p : WalkOrd G s) : WLab G s) then 24
          else 70 + 35 * (Nat.log 2 (D.blocks.length - 1) + 1))) := by
  set lam : WLab G s := ((toW p : WalkOrd G s) : WLab G s) with hlam
  set nb := D.blocks.length with hnb
  have hne : D.blocks ≠ [] := hwf.1
  have hnb1 : 1 ≤ nb := List.length_pos_of_ne_nil hne
  have hcap1 : 1 < st.cap := by omega
  have hw0 : ∀ a ∈ ([] : List String), a ∉ dW := by simp
  have hv0 : ∀ a ∈ ([] : List String), a ∉ dV := by simp
  obtain ⟨hPf, hPlt, hEA⟩ := hP
  -- the skip test
  apply runs_seq
  apply wp_sound
  refine wp_mono _ ?_ _ (skipTest_wp H V hH L ecap st hLv hEA
    (fun u i a h => lt_trans (hLf u i a h) (by omega)) v hv k p hK hKp hcap1)
  rintro r1 ⟨hlt1, hU1, hc1lo, hc1hi⟩
  by_cases hsk : skipIns L v lam = true
  · -- skip: nothing changes
    have h0 : r1.w "ins.lt" = 0 := by rw [hlt1, if_pos hsk]
    apply runs_ite_false (by simp [h0])
    apply wp_sound
    rw [wp_skip]
    have hU : Unchanged st ((r1.charge 1).charge 1) [] [] skipW [YB.l] := by
      simpa only [unch_charge] using hU1
    have hins : insertNS L fresh D v lam = (L, fresh, D) := by simp [insertNS, hsk]
    rw [hins]
    refine ⟨hD.of_unchanged hU hw0 hv0, hBA.of_unchanged hU hw0 hv0, hLv.of_unchanged hU hw0 hv0,
      ⟨by rw [hU.wreg _ (by decide)]; exact hPf, hPlt, ?_⟩, hU.mono (by simp) (by simp)
      (by simp only [insWR, skipW, probeW]; decide) (by simp), fun h => absurd h (by simp [hsk]),
      ?_, ?_⟩
    · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hEA
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first
        | (rw [(wa_eq hU hw0 (by simp [dW, entA])).2]; assumption)
        | (rw [(va_eq hU hv0 (by simp [dV, entA])).2]; assumption)
    · simp only [State.charge_cost]; omega
    · rw [if_pos hsk]; simp only [State.charge_cost]; omega
  · -- insert
    have hsk' : skipIns L v lam = false := by simpa using hsk
    have h1 : r1.w "ins.lt" = 1 := by rw [hlt1, if_neg hsk]
    apply runs_ite_true (by simp [h1] : evalW r1 (WExpr.var "ins.lt") = some 1) one_ne_zero
    have hUc : Unchanged st (r1.charge 1) [] [] skipW [YB.l] := by simpa only [unch_charge] using hU1
    set r1c := r1.charge 1 with hr1c
    have hD1 := hD.of_unchanged hUc hw0 hv0
    have hlv1 : r1c.w "ds.lv" = lv := by rw [hUc.wreg _ (by decide)]; exact hlv
    -- the owner index
    have hpw := (sep_pairwise hwf.2).1
    have hfirst : sepLe (D.blocks[0]'(List.length_pos_of_ne_nil hne)).sep lam = true := by
      rw [sep_first hwf.2 hne]; rfl
    set ho := ownerIdx lam D.blocks with hho
    have hho_lt : ho < nb := ownerIdx_lt lam D.blocks hne
    have hPj : ∀ j, j < nb → (Pj D lam j ↔ nb - 1 - j ≤ ho) := by
      intro j hj
      have hi : nb - 1 - j < nb := by omega
      constructor
      · rintro ⟨_, h⟩; exact (ownerIdx_spec lam D.blocks hpw hne hfirst _ hi).mp h
      · intro h; exact ⟨hi, (ownerIdx_spec lam D.blocks hpw hne hfirst _ hi).mpr h⟩
    rw [insBody]
    apply runs_seq
    apply wp_sound
    rw [wp_wset_of (a := nb) (by simp [hlv1, hD1.szb, hD1.sz, hnb])]
    set r2 := (r1c.setW "bs.sz" nb).charge 1 with hr2
    have hU2 : Unchanged st r2 [] [] (skipW ++ ["bs.sz"]) [YB.l] :=
      (hUc.comp (by simp [hr2, unch_setW] : Unchanged r1c r2 [] [] ["bs.sz"] [])).mono
        (by simp) (by simp) (by simp) (by simp)
    apply runs_seq
    -- the binary search
    let W2 : List String := ["bs.lo", "bs.hi", "bs.mid", "bs.p"] ++ probeW
    let X : State ℝ≥0 → Prop := fun q => Unchanged r2 q [] [] W2 [YB.l]
    have hX : ∀ st' r', X st' → Unchanged st' r' [] [] probeW [YB.l] → X r' :=
      fun st' r' h1 h2 => (h1.comp h2).mono (by simp) (by simp)
        (by intro a; simp only [List.mem_append, W2]; tauto) (by simp)
    have hKW : ∀ W : List String, W ⊆ bsRegs ++ probeW → "ds.lv" ∉ W ∧ "ds.b" ∉ W ∧
        ∀ a ∈ KB.ws, a ∉ W := by
      intro W hW
      have h' : "ds.lv" ∉ bsRegs ++ probeW ∧ "ds.b" ∉ bsRegs ++ probeW ∧
          ∀ a ∈ KB.ws, a ∉ bsRegs ++ probeW := by
        refine ⟨by decide, by decide, fun a ha => ?_⟩
        simp only [KB, LReg.ws, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl <;> decide
      exact ⟨fun h => h'.1 (hW h), fun h => h'.2.1 (hW h), fun a ha h => h'.2.2 a ha (hW h)⟩
    have hS : PreStable (fun q => ProbeCtx H V bcap lv bse D k p q ∧ X q) := by
      refine ⟨fun q k' ⟨hc, hx⟩ => ⟨hc.of_unchanged (Unchanged.charge q k' [] [] [] [YB.l])
        (hKW [] (by simp)), (unch_charge k').mpr hx⟩, fun q x a hx ⟨hc, hx'⟩ => ⟨?_, ?_⟩⟩
      · exact hc.of_unchanged ((unch_setW (List.mem_singleton_self x) a).mpr
          (Unchanged.refl q [] [] [x] [YB.l])) (hKW [x] (by
            intro y hy; simp only [List.mem_singleton] at hy; subst hy
            exact List.mem_append_left _ hx))
      · exact (unch_setW (show x ∈ W2 by simp only [W2, List.mem_append]; left; exact hx) a).mpr hx'
    have hpre2 : ProbeCtx H V bcap lv bse D k p r2 ∧ X r2 := by
      refine ⟨⟨hD.of_unchanged hU2 hw0 hv0, hBA.of_unchanged hU2 hw0 hv0,
        by rw [hU2.wreg _ (by decide)]; exact hlv, by rw [hU2.wreg _ (by decide)]; exact hb,
        hK.of_unchanged hU2 (by decide) (by decide), hKp, by rw [hU2.cap]; exact hcap1,
        by rw [hU2.cap]; omega⟩, Unchanged.refl r2 _ _ _ _⟩
    have hbs := bsearch_spec (ops := realOps) probe _ (Pj D lam) nb 30
      (probe_spec H V hH bcap lv bse D k p X hX) hS
      (fun i j hij hj hPi => (hPj j hj).mpr (by have := (hPj i (by omega)).mp hPi; omega))
      hnb1 ((hPj (nb - 1) (by omega)).mpr (by omega)) r2 hpre2 (by simp [hr2])
      (by rw [hU2.cap]; omega)
    refine hbs.mono ?_
    rintro r3 ⟨⟨hC3, hX3⟩, hlo3, hP3, hmin3, hcap3, hc3lo, hc3hi⟩
    set js := r3.w "bs.lo" with hjs
    have hjs_eq : js = nb - 1 - ho := by
      have h1 := (hPj js hlo3).mp hP3
      by_contra hne'
      have hlt : nb - 1 - ho < js := by omega
      exact hmin3 _ hlt ((hPj _ (by omega)).mpr (by omega))
    have hU3 : Unchanged st r3 [] [] (skipW ++ ["bs.sz"] ++ W2) [YB.l] :=
      (hU2.comp hX3).mono (by simp) (by simp) (by intro a; simp) (by simp)
    have hwa3 : r3.wa = st.wa := funext fun a => (hU3.warr a (by simp)).1
    have hva3 : r3.va = st.va := funext fun a => (hU3.varr a (by simp)).1
    have hwl3 : r3.wlen = st.wlen := funext fun a => (hU3.warr a (by simp)).2
    have hvl3 : r3.vlen = st.vlen := funext fun a => (hU3.varr a (by simp)).2
    set bid := st.wa "dsl.stk" (bse + js) with hbid
    have hbid_stk : bid = stkId st bse nb ho := by
      rw [hbid, ← stkId_rev (st := st) (bse := bse) (k := nb) hlo3, hjs_eq]
      congr 1; omega
    have hbl := hD.blk ho hho_lt
    rw [← hbid_stk] at hbl
    have hbidlt : bid < bcap := by rw [hbid_stk]; exact hD.bidb ho hho_lt
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hBA
    obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hEA
    have hcnt : st.wa "blk.cnt" bid ≤ fresh := by
      rw [hbl.2.2.2.1]; exact ents_len_le hid hfr (List.getElem_mem hho_lt)
    have hwr : ∀ z ∈ ["ds.b", "ds.fresh", "ds.v"], z ∉ skipW ++ ["bs.sz"] ++ W2 := by decide
    refine (insTail_spec r3 bse js bid fresh v k (by rw [hU3.wreg _ (hwr _ (by simp))]; exact hb)
      rfl (by rw [hwa3]) (by rw [hwl3]; have := hD.stkb; omega)
      (by rw [hU3.wreg _ (hwr _ (by simp))]; exact hPf) (by rw [hU3.wreg _ (hwr _ (by simp))]; exact hv)
      (hK.of_unchanged hU3 (by decide) (by decide))
      ⟨by rw [hwl3]; omega, by rw [hwl3]; omega, by rw [hwl3]; omega⟩
      ⟨by rw [hwl3]; omega, by rw [hwl3]; omega, by rw [hvl3]; simp [entA] at e3 ⊢; omega,
        by rw [hwl3]; simp [entA] at e4 ⊢; omega, by rw [hwl3]; simp [entA] at e5 ⊢; omega,
        by rw [hwl3]; simp [entA] at e6 ⊢; omega, by rw [hwl3]; simp [entA] at e7 ⊢; omega⟩
      (by rw [hwl3]; exact lt_of_lt_of_le v.isLt hLv.1)
      ⟨by rw [hcap3, hU2.cap]; have := hD.stkb; omega, by rw [hcap3, hU2.cap]; omega,
        by rw [hcap3, hU2.cap, hwa3]; omega⟩).mono ?_
    rintro r ⟨hF3, hfr4, hU4, hc4lo, hc4hi⟩
    have hF : InsFacts st r fresh bid v k := hF3.of_arr_eq hwa3 hva3 hwl3 hvl3
    have hins : insertNS L fresh D v lam = (Function.update L v (some (fresh, lam)), fresh + 1,
        { D with blocks := prependAt ⟨fresh, v, lam⟩ ho D.blocks }) := by
      simp only [insertNS, hsk', Bool.false_eq_true, if_false, prependOwner_eq, hho]
    rw [hins]
    have hUr : Unchanged st r insWA [entA.l] insWR [YB.l] :=
      (hU3.comp hU4).mono (by simp) (by simp) (by simp only [insWR, skipW, probeW, W2]; decide)
        (by simp)
    refine ⟨DRep.insert hF hD ho hho_lt hbid_stk (fun x hx => ne_of_lt (hfr x hx))
      (by omega) hKp, ?_, ?_, ⟨hfr4, hfr1, ?_⟩, hUr, fun _ => ⟨ho, hho_lt, hbid_stk ▸ hF⟩, ?_, ?_⟩
    · exact ⟨by rw [hF.lens]; exact b1, by rw [hF.lens]; exact b2, by rw [hF.lens]; exact b3,
        by rw [hF.lens]; exact b4, by rw [hF.vlens]; exact b5, by rw [hF.lens]; exact b6,
        by rw [hF.lens]; exact b7, by rw [hF.lens]; exact b8, by rw [hF.lens]; exact b9⟩
    · exact LiveRep.insert hF hLv (fun u i a h => ne_of_lt (hLf u i a h)) hKp
    · exact ⟨by rw [hF.lens]; exact e1, by rw [hF.lens]; exact e2, by rw [hF.vlens]; exact e3,
        by rw [hF.lens]; exact e4, by rw [hF.lens]; exact e5, by rw [hF.lens]; exact e6,
        by rw [hF.lens]; exact e7⟩
    · simp only [hr2, hr1c, State.charge_cost, State.setW_cost] at hc3lo; omega
    · rw [if_neg (by rw [hsk']; decide)]
      simp only [hr2, hr1c, State.charge_cost, State.setW_cost] at hc3hi; omega

end Main

end Frontier.CHD.DIns
