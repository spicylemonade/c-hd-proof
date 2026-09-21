import Frontier.CHD.EntLess
import Frontier.CHD.DList
import Frontier.CHD.RamSlot
import Frontier.CHD.RamLevel

/-!
# Frontier.CHD.DPull — RAM `Pull` of the lazy DS' structure (F-SPLIT + F-PULL, B-L3)

Owner: agent-05.  NON-GATE (Layer B).  Refines agent-04's `DL.pullL` = `DL.prepList` followed by
`DB.pull` on the block stack of agent-02's layout (`DRep`), using agent-04's list fragments
(`DList.walkCopy`, `DList.buildList`) and agent-05's verified selection (`SelectRAM.sel_spec`,
`filt_spec`, `filtGe_spec`) with the entry comparison `entLess`.

Stage 1 (this file so far): the program text of one median split of the top block (`splitStep`).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.DPull

open Frontier Frontier.CHD Frontier.RAM WExpr Stmt LabRAM
open Frontier.RAM.SelectRAM

/-! ## Program text -/

/-- `sp.t := ds.b + dsl.sz[ds.lv] - 1` (position of the top block) and its record id `sp.bid` -/
def spTop : Stmt :=
  seq (wset "sp.t" (sub (add (var "ds.b") (load "dsl.sz" (var "ds.lv"))) (lit 1)))
    (wset "sp.bid" (load "dsl.stk" (var "sp.t")))

/-- copy the live ids of the top block to `sel.w[sp.w0, sp.w0 + sp.c)` -/
def spWalk : Stmt :=
  seq (wset "dl.p" (load "blk.hd" (var "sp.bid")))
  (seq (wset "dl.w" (var "sp.w0"))
  (seq DList.walkCopy
       (wset "sp.c" (var "dl.c"))))

/-- select the element of rank `k` of the ids `sel.w[sp.w0, sp.w0 + sp.c)`: `sp.med` -/
def spMedK (k : WExpr) (pSel : ℕ) : Stmt :=
  seq (wset "sel.k" k)
  (seq (wset "sel.lo" (var "sp.w0"))
  (seq (wset "sel.n" (var "sp.c"))
  (seq (wset "sel.top" (add (var "sp.w0") (var "sp.c")))
  (seq (call pSel)
       (wset "sp.med" (var "sel.res"))))))

/-- select the median (rank `c / 2`) of the copied ids: `sp.med` -/
def spMed (pSel : ℕ) : Stmt := spMedK (div (var "sp.c") (lit 2)) pSel

/-- the two halves: `lo` (keys `< med`) to `[w0 + c, w0 + c + a)`, `hi` (keys `≥ med`) above -/
def spHalves : Stmt :=
  seq (wset "sel.lo" (var "sp.w0"))
  (seq (wset "sel.n" (var "sp.c"))
  (seq (wset "sel.p" (var "sp.med"))
  (seq (wset "sel.m" (add (var "sp.w0") (var "sp.c")))
  (seq (filt entLess false "sel.a")
  (seq (wset "sel.m" (add (add (var "sp.w0") (var "sp.c")) (var "sel.a")))
       (filtGe entLess "sel.b"))))))

/-- relink both halves (`sp.hlo`, `sp.hhi` = list heads) -/
def spLink : Stmt :=
  seq (wset "dl.a" (add (var "sp.w0") (var "sp.c")))
  (seq (wset "dl.n" (var "sel.a"))
  (seq DList.buildList
  (seq (wset "sp.hlo" (var "dl.h"))
  (seq (wset "dl.a" (add (add (var "sp.w0") (var "sp.c")) (var "sel.a")))
  (seq (wset "dl.n" (var "sel.b"))
  (seq DList.buildList
       (wset "sp.hhi" (var "dl.h"))))))))

/-- `sel.w[e - 1] + 1`: the tail word of a nonempty id segment ending before `e` -/
def tlE (e : WExpr) : WExpr := add (load "sel.w" (sub e (lit 1))) (lit 1)

/-- the low half keeps record `sp.bid` (and its separator) -/
def spRecLo : Stmt :=
  seq (wstore "blk.hd" (var "sp.bid") (var "sp.hlo"))
  (seq (wstore "blk.tl" (var "sp.bid") (tlE (add (add (var "sp.w0") (var "sp.c")) (var "sel.a"))))
       (wstore "blk.cnt" (var "sp.bid") (var "sel.a")))

/-- the high half gets the fresh record `sp.nb` -/
def spRecHi : Stmt :=
  seq (wset "sp.nb" (var "blk.fresh"))
  (seq (wset "blk.fresh" (add (var "blk.fresh") (lit 1)))
  (seq (wstore "blk.hd" (var "sp.nb") (var "sp.hhi"))
  (seq (wstore "blk.tl" (var "sp.nb")
        (tlE (add (add (add (var "sp.w0") (var "sp.c")) (var "sel.a")) (var "sel.b"))))
  (seq (wstore "blk.cnt" (var "sp.nb") (var "sel.b"))
       (wstore "blk.bot" (var "sp.nb") (lit 0))))))

/-- separator of the high half := the median's label -/
def spRecSep : Stmt := seq (loadA DIns.entA "sp.med" fsX) (storeA DIns.blkA "sp.nb" fsX)

/-- pop the split block, push the high half, push the low half -/
def spPush : Stmt :=
  seq (wstore "dsl.stk" (var "sp.t") (var "sp.nb"))
  (seq (wstore "dsl.stk" (add (var "sp.t") (lit 1)) (var "sp.bid"))
       (wstore "dsl.sz" (var "ds.lv") (add (load "dsl.sz" (var "ds.lv")) (lit 1))))

/-- rewrite the records: `lo` keeps record `sp.bid` (and its separator), `hi` gets the fresh
record `sp.nb` with separator = the median's label; push `lo` above `hi` -/
def spRecs : Stmt := seq spRecLo (seq spRecHi (seq spRecSep spPush))

/-- **One median split of the top block** (DLazy `prep`'s step): split iff more than `2M+1` live
entries and a nonempty lower half; `dsp.go := 1` iff split. -/
def splitStep (pSel : ℕ) : Stmt :=
  seq spTop (seq spWalk
    (ite (lt (add (mul (var "ds.M") (lit 2)) (lit 1)) (var "sp.c"))
      (seq (spMed pSel) (seq spHalves
        (ite (lt (lit 0) (var "sel.a"))
          (seq spLink (seq spRecs (wset "dsp.go" (lit 1))))
          (wset "dsp.go" (lit 0)))))
      (wset "dsp.go" (lit 0))))

/-- **prep**: split the top block while `splitStep` does. -/
def prepTop (pSel : ℕ) : Stmt :=
  seq (wset "dsp.go" (lit 1)) (.while (var "dsp.go") (splitStep pSel))

/-- registers written by the split machinery -/
def spRegs : List String :=
  ["sp.t", "sp.bid", "sp.c", "sp.med", "sp.hlo", "sp.hhi", "sp.nb", "dsp.go", "blk.fresh"]

/-! ## Representation lemmas -/

section Rep

open Frontier.CHD.DIns Frontier.CHD.DB Frontier.CHD.MLab Frontier.CHD.LabTab

variable {G : Graph} {s : Fin G.n}

theorem aholds_unique {st : State ℝ≥0} {A : LArr} {i : ℕ} {x y : MLabel G}
    (hx : AHolds st A i x) (hy : AHolds st A i y) : x = y := by
  obtain ⟨x1, x2, x3, x4, x5⟩ := hx
  obtain ⟨y1, y2, y3, y4, y5⟩ := hy
  have hv : x.v = y.v := Fin.ext (by rw [← x3, ← y3])
  have he : x.e = y.e := encE_injective (by rw [← x4, ← y4])
  cases x; cases y
  simp only [MLabel.mk.injEq] at *
  exact ⟨by rw [← x1, ← y1], by rw [← x2, ← y2], hv, he, by rw [← x5, ← y5]⟩

/-- two representations of the same pool entry agree on the value -/
theorem entRep_val_unique {st : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {i : ℕ} {v v' : Fin G.n} {a a' : WLab G s} (h : EntRep st H V i v a) (h' : EntRep st H V i v' a') :
    a = a' := by
  obtain ⟨-, m, p, hA, hR, rfl⟩ := h
  obtain ⟨-, m', p', hA', hR', rfl⟩ := h'
  have hm : m = m' := aholds_unique hA hA'
  subst hm
  rw [hR.1, hR'.1]

/-- **RAM liveness is Layer-A liveness** for the entries of a represented block. -/
theorem liveW_iff {st : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {L : Live (Fin G.n) (WLab G s)} (hL : LiveRep st H V L) {e : Entry (Fin G.n) (WLab G s)}
    (he : EntRep st H V e.id e.key e.val) : DList.liveW st e.id ↔ e.IsLive L := by
  unfold DList.liveW Entry.IsLive
  rw [he.1, (hL.2 e.key).1]
  constructor
  · intro hw
    cases hLv : L e.key with
    | none => rw [hLv] at hw; simp [liveWord] at hw
    | some q =>
      obtain ⟨i, a⟩ := q
      rw [hLv] at hw
      simp only [liveWord, Nat.add_right_cancel_iff] at hw
      subst hw
      have h2 := (hL.2 e.key).2 _ _ hLv
      rw [entRep_val_unique h2 he]
  · intro h; rw [h]; rfl

end Rep

/-! ## The front part of a split step -/

section Front

open Frontier.CHD.DIns Frontier.CHD.DB

variable {ops : VOps ℝ≥0}

theorem spTop_run (q : State ℝ≥0) {lv bse k : ℕ} (hlv : q.w "ds.lv" = lv) (hb : q.w "ds.b" = bse)
    (hsz : q.wa "dsl.sz" lv = k) (hk : 1 ≤ k) (hszl : lv < q.wlen "dsl.sz")
    (hstk : bse + k ≤ q.wlen "dsl.stk") (hcap : bse + k < q.cap) :
    Runs ops spTop q (fun r => r.w "sp.t" = bse + k - 1 ∧
      r.w "sp.bid" = q.wa "dsl.stk" (bse + k - 1) ∧ RegOnly q r ["sp.t", "sp.bid"] ∧
      r.cost = q.cost + 2) := by
  unfold spTop
  apply runs_seq
  refine runs_wset (a := bse + k - 1) (by
    simp [evalW_add', evalW_sub', hlv, hb, hsz, hszl, fit_of_lt (show bse + k < q.cap by omega),
      fit_of_lt (show 1 < q.cap by omega)]) ?_
  refine runs_wset (a := q.wa "dsl.stk" (bse + k - 1)) (by
    simp [show bse + k - 1 < q.wlen "dsl.stk" by omega]) ?_
  refine ⟨by simp, by simp, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun y hy => ?_⟩, by simp⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  simp [State.setW, hy.1, hy.2]

theorem spWalk_run (q : State ℝ≥0) {bid w0 : ℕ} (ids : List ℕ) (hbid : q.w "sp.bid" = bid)
    (hbl : bid < q.wlen "blk.hd") (hw0 : q.w "sp.w0" = w0) (hL : LList q (q.wa "blk.hd" bid) ids)
    (hkey : ∀ i, i < q.wlen "ent.nxt" → i < q.wlen "ent.key" ∧ q.wa "ent.key" i < q.wlen "live")
    (hcap : q.wlen "sel.w" + 1 < q.cap) (hlen : w0 + ids.length ≤ q.wlen "sel.w") :
    Runs ops spWalk q (fun r => r.w "sp.c" = (ids.filter (DList.liveW q)).length ∧
      DList.Spells r "sel.w" w0 (ids.filter (DList.liveW q)) ∧
      (∀ x, (x < w0 ∨ w0 + (ids.filter (DList.liveW q)).length ≤ x) →
        r.wa "sel.w" x = q.wa "sel.w" x) ∧
      Unchanged q r ["sel.w"] [] (["dl.p", "dl.w", "sp.c"] ++ DList.walkRegs) [] ∧
      r.wlen "sel.w" = q.wlen "sel.w" ∧ r.cost ≤ q.cost + 8 + 7 * ids.length) := by
  unfold spWalk
  apply runs_seq
  refine runs_wset (a := q.wa "blk.hd" bid) (by simp [hbid, hbl]) ?_
  apply runs_seq
  refine runs_wset (a := w0) (by simp [hw0]) ?_
  set q2 := (((q.setW "dl.p" (q.wa "blk.hd" bid)).charge 1).setW "dl.w" w0).charge 1 with hq2
  have hr2 : RegOnly q q2 ["dl.p", "dl.w"] := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun y hy => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [hq2, State.setW, hy.1, hy.2]
  have hlive : ∀ i, DList.liveW q2 i ↔ DList.liveW q i := fun i => by simp [DList.liveW, hq2]
  apply runs_seq
  have hL2 : LList q2 (q2.w "dl.p") ids := by
    have h := hL.frame (st' := q2) (by simp [hq2]) (fun i _ => by simp [hq2])
    have e : q2.w "dl.p" = q.wa "blk.hd" bid := by simp [hq2]
    rw [e]; exact h
  refine (DList.walkCopy_spec (ops := ops) q2 ids hL2
    (by intro i hi; simpa [hq2] using hkey i (by simpa [hq2] using hi)) (by simpa [hq2] using hcap)
    (by simpa [hq2] using hlen)).mono (fun r1 ⟨hW, hc1⟩ => ?_)
  have hfl : ids.filter (DList.liveW q2) = ids.filter (DList.liveW q) := by
    apply List.filter_congr; intro i _; simp [hlive i]
  have hw1 : q2.w "dl.w" = w0 := by simp [hq2]
  refine runs_wset (a := r1.w "dl.c") (by simp) ?_
  refine ⟨by simp [hW.c, hfl], ?_, fun x hx => ?_, ?_, by simp [hW.wlen, hq2], ?_⟩
  · intro r hr
    have := hW.spell
    rw [hw1, hfl] at this
    simpa using this r hr
  · have := hW.out x
    rw [hw1, hfl] at this
    simpa [hq2] using this hx
  · have u1 : Unchanged q q2 ["sel.w"] [] (["dl.p", "dl.w", "sp.c"] ++ DList.walkRegs) [] :=
      (hr2.unch _ _ _).mono (List.Subset.refl _) (List.Subset.refl _)
        (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp) (List.Subset.refl _)
    have u2 : Unchanged q2 r1 ["sel.w"] [] (["dl.p", "dl.w", "sp.c"] ++ DList.walkRegs) [] :=
      hW.unch.mono (List.Subset.refl _) (List.Subset.refl _)
        (fun y hy => List.mem_append_right _ hy) (List.Subset.refl _)
    have u3 : Unchanged r1 ((r1.setW "sp.c" (r1.w "dl.c")).charge 1) ["sel.w"] []
        (["dl.p", "dl.w", "sp.c"] ++ DList.walkRegs) [] := by
      rw [unch_charge', unch_setW' (by simp)]; exact Unchanged.refl _ _ _ _ _
    exact u1.trans (u2.trans u3)
  · simp only [State.charge_cost, State.setW_cost]
    simp only [hq2, State.charge_cost, State.setW_cost] at hc1
    omega

end Front

/-! ## Median and halves -/

section MedHalves

open Frontier.CHD.DIns Frontier.CHD.DB

variable {G : Graph} {s : Fin G.n} {KR : State ℝ≥0 → Prop} {ok : ℕ → Prop} {κ : ℕ → WLab G s}

theorem spMedK_run (hL : LessSpec realOps entLess KR ok κ 23 entLessW entLessV)
    (hKRf : ∀ s r, KR s → (∀ b, b ≠ "sel.w" → r.wa b = s.wa b) → r.wlen = s.wlen → r.va = s.va →
      r.vlen = s.vlen → r.cap = s.cap → KR r) (k : WExpr) (pSel : ℕ)
    (q : State ℝ≥0) (hK : KR q) {w0 c kk : ℕ} (hw0 : q.w "sp.w0" = w0) (hc : q.w "sp.c" = c)
    (hk : evalW q k = some kk) (hkk : kk < c) (hok : ∀ x ∈ seg q w0 c, ok x)
    (hprocs : q.procs[pSel]? = some (selBody entLess pSel))
    (hspace : w0 + c + 5 * c + 60 ≤ q.wlen "sel.w") (hcap : w0 + c + 5 * c + 60 < q.cap)
    (h300 : 300 < q.cap) :
    Runs realOps (spMedK k pSel) q (fun r => KR r ∧ r.w "sp.med" ∈ seg q w0 c ∧
      Frontier.CHD.IsKth ((seg q w0 c).map κ) kk (κ (r.w "sp.med")) ∧
      (∀ x, x < w0 + c → r.wa "sel.w" x = q.wa "sel.w" x) ∧ r.wlen "sel.w" = q.wlen "sel.w" ∧
      Unchanged q r ["sel.w"] [] (myRegs ++ entLessW ++ ["sp.med"]) entLessV ∧
      r.cost ≤ q.cost + 5 + Ksel 23 * c + 100) := by
  unfold spMedK
  apply runs_seq
  refine runs_wset (a := kk) hk ?_
  apply runs_seq
  refine runs_wset (a := w0) (by simp [hw0]) ?_
  apply runs_seq
  refine runs_wset (a := c) (by simp [hc]) ?_
  apply runs_seq
  refine runs_wset (a := w0 + c) (by
    simp [hc, hw0, fit_of_lt (show w0 + c < q.cap by omega)]) ?_
  set q4 := ((((((((q.setW "sel.k" kk).charge 1).setW "sel.lo" w0).charge 1).setW "sel.n" c).charge
    1).setW "sel.top" (w0 + c)).charge 1) with hq4
  have hr4 : RegOnly q q4 ["sel.k", "sel.lo", "sel.n", "sel.top"] := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun y hy => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [hq4, State.setW, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2]
  have hK4 : KR q4 := hL.regs _ _ hK (hr4.mono (by simp [myRegs, selRegs]))
  have hseg4 : seg q4 (q4.w "sel.lo") c = seg q w0 c := by simp [seg, hq4]
  apply runs_seq
  refine (sel_spec hL pSel c q4 ⟨hK4, by rw [hseg4]; exact hok, by simpa [hq4] using hprocs,
    by simp [hq4], by omega, by simp [hq4]; omega, by simp [hq4], by simp [hq4]; omega,
    by simp [hq4]; omega, by simpa [hq4] using h300⟩).mono
    (fun r4 ⟨hKr, hres, hkth, hfp, hlow, hwl, hu, hcr⟩ => ?_)
  rw [hseg4] at hres hkth
  have hk4 : q4.w "sel.k" = kk := by simp [hq4]
  rw [hk4] at hkth
  refine runs_wset (a := r4.w "sel.res") (by simp) ?_
  refine ⟨hKRf _ _ hKr (fun b _ => rfl) rfl rfl rfl rfl, by simpa using hres,
    by simpa using hkth, fun x hx => ?_, by simpa [hq4] using hwl, ?_, ?_⟩
  · have := hlow x (by simpa [hq4] using hx)
    simpa [hq4] using this
  · have u1 : Unchanged q q4 ["sel.w"] [] (myRegs ++ entLessW ++ ["sp.med"]) entLessV :=
      (hr4.unch _ _ _).mono (List.Subset.refl _) (List.Subset.refl _)
        (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl | rfl <;> simp [myRegs, selRegs])
        (List.Subset.refl _)
    have u2 : Unchanged q4 r4 ["sel.w"] [] (myRegs ++ entLessW ++ ["sp.med"]) entLessV :=
      hu.mono (List.Subset.refl _) (List.Subset.refl _)
        (fun y hy => by simp only [List.mem_append] at hy ⊢; tauto) (List.Subset.refl _)
    have u3 : Unchanged r4 ((r4.setW "sp.med" (r4.w "sel.res")).charge 1) ["sel.w"] []
        (myRegs ++ entLessW ++ ["sp.med"]) entLessV := by
      rw [unch_charge', unch_setW' (by simp)]; exact Unchanged.refl _ _ _ _ _
    exact u1.trans (u2.trans u3)
  · simp only [State.charge_cost, State.setW_cost]
    simp only [hq4, State.charge_cost, State.setW_cost] at hcr
    omega

theorem spMed_run (hL : LessSpec realOps entLess KR ok κ 23 entLessW entLessV)
    (hKRf : ∀ s r, KR s → (∀ b, b ≠ "sel.w" → r.wa b = s.wa b) → r.wlen = s.wlen → r.va = s.va →
      r.vlen = s.vlen → r.cap = s.cap → KR r) (pSel : ℕ)
    (q : State ℝ≥0) (hK : KR q) {w0 c : ℕ} (hw0 : q.w "sp.w0" = w0) (hc : q.w "sp.c" = c)
    (hc1 : 1 ≤ c) (hok : ∀ x ∈ seg q w0 c, ok x)
    (hprocs : q.procs[pSel]? = some (selBody entLess pSel))
    (hspace : w0 + c + 5 * c + 60 ≤ q.wlen "sel.w") (hcap : w0 + c + 5 * c + 60 < q.cap)
    (h300 : 300 < q.cap) :
    Runs realOps (spMed pSel) q (fun r => KR r ∧ r.w "sp.med" ∈ seg q w0 c ∧
      Frontier.CHD.IsKth ((seg q w0 c).map κ) (c / 2) (κ (r.w "sp.med")) ∧
      (∀ x, x < w0 + c → r.wa "sel.w" x = q.wa "sel.w" x) ∧ r.wlen "sel.w" = q.wlen "sel.w" ∧
      Unchanged q r ["sel.w"] [] (myRegs ++ entLessW ++ ["sp.med"]) entLessV ∧
      r.cost ≤ q.cost + 5 + Ksel 23 * c + 100) :=
  spMedK_run hL hKRf _ pSel q hK hw0 hc
    (by simp [hc, fit_of_lt (show 2 < q.cap by omega)]) (by omega) hok hprocs hspace hcap h300

/-- registers of the split machinery outside the filters' write sets -/
theorem sp_nf {y cnt : String} (hc : cnt ∈ ["sel.a", "sel.b"])
    (hy : y ∈ ["sp.w0", "sp.c", "sp.med", "sp.t", "sp.bid", "sp.hlo", "sp.hhi", "sp.nb", "dsp.go",
      "ds.lv", "ds.b", "ds.M", "blk.fresh", "ds.fresh"]) : y ∉ filtW cnt entLessW := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc hy
  rcases hc with rfl | rfl <;>
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [filtW, entLessW, fsX, fsY, LReg.ws]

theorem sp_nm {y : String}
    (hy : y ∈ ["sp.w0", "sp.c", "sp.med", "sp.t", "sp.bid", "sp.hlo", "sp.hhi", "sp.nb", "dsp.go",
      "ds.lv", "ds.b", "ds.M", "blk.fresh", "ds.fresh"]) : y ∉ myRegs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [myRegs, lessRegs, csRegs, selRegs]

set_option maxHeartbeats 2000000 in
theorem spHalves_run (hL : LessSpec realOps entLess KR ok κ 23 entLessW entLessV)
    (q : State ℝ≥0) (hK : KR q) {w0 c med : ℕ} (hw0 : q.w "sp.w0" = w0) (hc : q.w "sp.c" = c)
    (hmed : q.w "sp.med" = med) (hok : ∀ x ∈ seg q w0 c, ok x) (hokm : ok med)
    (hspace : w0 + 3 * c ≤ q.wlen "sel.w") (hcap : w0 + 3 * c + 1 < q.cap) :
    Runs realOps spHalves q (fun r => KR r ∧
      seg r (w0 + c) (r.w "sel.a") = (seg q w0 c).filter (fun x => decide (κ x < κ med)) ∧
      seg r (w0 + c + r.w "sel.a") (r.w "sel.b") =
        (seg q w0 c).filter (fun x => decide (κ med ≤ κ x)) ∧
      r.w "sel.a" + r.w "sel.b" = c ∧
      (∀ x, x < w0 + c → r.wa "sel.w" x = q.wa "sel.w" x) ∧
      r.wlen "sel.w" = q.wlen "sel.w" ∧
      Unchanged q r ["sel.w"] [] (myRegs ++ entLessW) entLessV ∧
      r.cost ≤ q.cost + 11 + 2 * (c * (23 + 10))) := by
  unfold spHalves
  apply runs_seq
  refine runs_wset (a := w0) (by simp [hw0]) ?_
  apply runs_seq
  refine runs_wset (a := c) (by simp [hc]) ?_
  apply runs_seq
  refine runs_wset (a := med) (by simp [hmed]) ?_
  apply runs_seq
  refine runs_wset (a := w0 + c) (by simp [hw0, hc, fit_of_lt (show w0 + c < q.cap by omega)]) ?_
  set q1 := ((((((((q.setW "sel.lo" w0).charge 1).setW "sel.n" c).charge 1).setW "sel.p" med).charge
    1).setW "sel.m" (w0 + c)).charge 1) with hq1
  have hr1 : RegOnly q q1 ["sel.lo", "sel.n", "sel.p", "sel.m"] := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun y hy => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [hq1, State.setW, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2]
  have hK1 : KR q1 := hL.regs _ _ hK (hr1.mono (by simp [myRegs, selRegs]))
  have e1 : ∀ y, y ∉ ["sel.lo", "sel.n", "sel.p", "sel.m"] → q1.w y = q.w y := hr1.2.2.2.2.2.2.2
  have hlo1 : q1.w "sel.lo" = w0 := by simp [hq1]
  have hn1 : q1.w "sel.n" = c := by simp [hq1]
  have hp1 : q1.w "sel.p" = med := by simp [hq1]
  have hm1 : q1.w "sel.m" = w0 + c := by simp [hq1]
  have hseg1 : seg q1 w0 c = seg q w0 c := by simp [seg, hq1]
  apply runs_seq
  refine (filt_spec hL false "sel.a" (by simp) q1 hK1 (by rw [hlo1, hn1, hseg1]; exact hok)
    (by rw [hp1]; exact hokm) (by rw [hlo1, hn1, hm1]) (by rw [hm1, hn1]; simp [hq1]; omega)
    (by rw [hm1, hn1]; simp [hq1]; omega)).mono
    (fun q2 ⟨hK2, hsa, hout2, hwl2, hu2, hc2⟩ => ?_)
  rw [hm1, hlo1, hn1, hp1, hseg1] at hsa
  simp only [fP, Bool.false_eq_true, ite_false] at hsa
  rw [hm1, hn1] at hout2
  have hkeep2 : ∀ y, y ∈ ["sel.lo", "sel.n", "sel.p"] → q2.w y = q1.w y := by
    intro y hy
    refine hu2.wreg y (filt_keep hL (by simp) (by simp at hy ⊢; tauto) ?_)
    simp at hy; rcases hy with rfl | rfl | rfl <;> simp
  have hsp2 : ∀ y, y ∈ ["sp.w0", "sp.c", "sp.med", "sp.t", "sp.bid", "sp.hlo", "sp.hhi", "sp.nb", "dsp.go",
      "ds.lv", "ds.b", "ds.M", "blk.fresh", "ds.fresh"] → q2.w y = q.w y := by
    intro y hy
    rw [hu2.wreg y (sp_nf (by simp) hy)]
    exact e1 y (fun h => sp_nm hy (by simp at h; rcases h with rfl | rfl | rfl | rfl <;> simp [myRegs, selRegs]))
  have ha2 : q2.w "sel.a" ≤ c := by
    have := congrArg List.length hsa
    simp only [length_seg] at this
    rw [this]; exact length_filter_seg _ _ _ _
  have hcap2 : q2.cap = q.cap := by rw [hu2.cap]; simp [hq1]
  have hwl2' : q2.wlen "sel.w" = q.wlen "sel.w" := by rw [hwl2]; simp [hq1]
  apply runs_seq
  have hw02 : q2.w "sp.w0" = w0 := by rw [hsp2 _ (by simp), hw0]
  have hc02 : q2.w "sp.c" = c := by rw [hsp2 _ (by simp), hc]
  refine runs_wset (a := w0 + c + q2.w "sel.a")
    (evalW_add_of (evalW_add_of (by rw [evalW_var, hw02]) (by rw [evalW_var, hc02])
      (by rw [hcap2]; omega)) rfl (by rw [hcap2]; omega)) ?_
  set q3 := (q2.setW "sel.m" (w0 + c + q2.w "sel.a")).charge 1 with hq3
  have hr3 : RegOnly q2 q3 ["sel.m"] := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun y hy => ?_⟩
    simp only [List.mem_singleton] at hy
    simp [hq3, State.setW, hy]
  have hK3 : KR q3 := hL.regs _ _ hK2 (hr3.mono (by simp [myRegs, selRegs]))
  have e3 : ∀ y, y ≠ "sel.m" → q3.w y = q2.w y := fun y hy => hr3.2.2.2.2.2.2.2 y (by simpa using hy)
  have hlo3 : q3.w "sel.lo" = w0 := by rw [e3 _ (by simp), hkeep2 _ (by simp), hlo1]
  have hn3 : q3.w "sel.n" = c := by rw [e3 _ (by simp), hkeep2 _ (by simp), hn1]
  have hp3 : q3.w "sel.p" = med := by rw [e3 _ (by simp), hkeep2 _ (by simp), hp1]
  have hm3 : q3.w "sel.m" = w0 + c + q2.w "sel.a" := by simp [hq3]
  have hwl3 : q3.wlen "sel.w" = q.wlen "sel.w" := by simp [hq3, hwl2']
  have hcap3 : q3.cap = q.cap := by simp [hq3, hcap2]
  have hseg3 : seg q3 w0 c = seg q w0 c := by
    rw [← hseg1]
    apply seg_congr
    intro x h1 h2
    simp only [hq3, State.charge_wa, State.setW_wa]
    rw [hout2 x (Or.inl (by omega))]
  refine (filtGe_spec hL "sel.b" (by simp) q3 hK3 (by rw [hlo3, hn3, hseg3]; exact hok)
    (by rw [hp3]; exact hokm) (by rw [hlo3, hn3, hm3]; omega)
    (by rw [hm3, hn3, hwl3]; omega) (by rw [hm3, hn3, hcap3]; omega)).mono
    (fun r ⟨hKr, hsegr, houtr, hwlr, hur, hcr⟩ => ?_)
  rw [hm3, hlo3, hn3, hp3, hseg3] at hsegr
  rw [hm3, hn3] at houtr
  have hra : r.w "sel.a" = q2.w "sel.a" := by
    rw [hur.wreg "sel.a" (by simp [filtW]; intro h; exact hL.disj _ h (by simp [myRegs, selRegs])),
      e3 _ (by simp)]
  have hsum : r.w "sel.a" + r.w "sel.b" = c := by
    have la := congrArg List.length hsa
    have lb := congrArg List.length hsegr
    simp only [length_seg] at la lb
    rw [hra, la, lb, ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    have h := List.length_eq_countP_add_countP (l := seg q w0 c) (fun x => decide (κ x < κ med))
    have h2 : (seg q w0 c).countP (fun a => decide ¬decide (κ a < κ med) = true) =
        (seg q w0 c).countP (fun x => decide (κ med ≤ κ x)) :=
      List.countP_congr (fun x _ => by simp)
    rw [length_seg] at h
    omega
  refine ⟨hKr, ?_, by rw [hra]; exact hsegr, hsum, fun x hx => ?_, by rw [hwlr, hwl3], ?_, ?_⟩
  · rw [hra, ← hsa]
    apply seg_congr
    intro x h1 h2
    rw [houtr x (Or.inl (by omega))]
    simp [hq3]
  · rw [houtr x (Or.inl (by omega))]
    simp only [hq3, State.charge_wa, State.setW_wa]
    rw [hout2 x (Or.inl hx)]
    simp [hq1]
  · have u1 : Unchanged q q1 ["sel.w"] [] (myRegs ++ entLessW) entLessV := (hr1.unch _ _ _).mono
      (List.Subset.refl _) (List.Subset.refl _) (myRegs_sub (by simp [myRegs, selRegs]) _)
      (List.Subset.refl _)
    have u2 : Unchanged q1 q2 ["sel.w"] [] (myRegs ++ entLessW) entLessV := hu2.mono (List.Subset.refl _)
      (List.Subset.refl _) (filtW_sub (by simp) entLessW) (List.Subset.refl _)
    have u3 : Unchanged q2 q3 ["sel.w"] [] (myRegs ++ entLessW) entLessV := (hr3.unch _ _ _).mono
      (List.Subset.refl _) (List.Subset.refl _) (myRegs_sub (by simp [myRegs, selRegs]) _)
      (List.Subset.refl _)
    have u4 : Unchanged q3 r ["sel.w"] [] (myRegs ++ entLessW) entLessV := hur.mono (List.Subset.refl _)
      (List.Subset.refl _) (filtW_sub (by simp) entLessW) (List.Subset.refl _)
    exact u1.trans (u2.trans (u3.trans u4))
  · have hc2' : q2.cost ≤ q.cost + 7 + c * (23 + 10) := by
      rw [hn1] at hc2; simp only [hq1, State.charge_cost, State.setW_cost] at hc2; omega
    have hcr' : r.cost ≤ q2.cost + 4 + c * (23 + 10) := by
      rw [hn3] at hcr; simp only [hq3, State.charge_cost, State.setW_cost] at hcr; omega
    omega

end MedHalves

/-! ## Relinking the halves -/

section Link

open Frontier.CHD.DIns Frontier.CHD.DB

variable {ops : VOps ℝ≥0}

theorem spells_seg (st : State ℝ≥0) (lo n : ℕ) : DList.Spells st "sel.w" lo (seg st lo n) := by
  intro r hr
  simp [seg]

theorem seg_of_spells {st : State ℝ≥0} {lo : ℕ} {l : List ℕ} (h : DList.Spells st "sel.w" lo l) :
    seg st lo l.length = l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [seg, h i h2]

/-- registers written by `spLink` -/
def linkRegs : List String := ["dl.a", "dl.n", "sp.hlo", "sp.hhi"] ++ DList.buildRegs

set_option maxHeartbeats 1000000 in
theorem spLink_run (q : State ℝ≥0) {w0 c a b : ℕ} {lo hi : List ℕ} (hw0 : q.w "sp.w0" = w0)
    (hc : q.w "sp.c" = c) (ha : q.w "sel.a" = a) (hb : q.w "sel.b" = b)
    (hlo : seg q (w0 + c) a = lo) (hhi : seg q (w0 + c + a) b = hi) (hnd : (lo ++ hi).Nodup)
    (hlt : ∀ x ∈ lo ++ hi, x < q.wlen "ent.nxt") (hxc : ∀ x ∈ lo ++ hi, x + 1 < q.cap)
    (hseg : w0 + c + a + b ≤ q.wlen "sel.w") (hcap : w0 + c + a + b + 1 < q.cap) :
    Runs ops spLink q (fun r => LList r (r.w "sp.hlo") lo ∧ LList r (r.w "sp.hhi") hi ∧
      (∀ y, y ∉ lo ++ hi → r.wa "ent.nxt" y = q.wa "ent.nxt" y) ∧
      Unchanged q r ["ent.nxt"] [] linkRegs [] ∧
      r.wlen "ent.nxt" = q.wlen "ent.nxt" ∧ r.cost ≤ q.cost + 12 + 5 * (a + b)) := by
  have hla : lo.length = a := by rw [← hlo]; simp
  have hlb : hi.length = b := by rw [← hhi]; simp
  have hndlo : lo.Nodup := (List.nodup_append.mp hnd).1
  have hndhi : hi.Nodup := (List.nodup_append.mp hnd).2.1
  have hdisj : ∀ x ∈ lo, x ∉ hi := fun x hx hx' => (List.nodup_append.mp hnd).2.2 x hx x hx' rfl
  unfold spLink
  apply runs_seq
  refine runs_wset (a := w0 + c)
    (evalW_add_of (by rw [evalW_var, hw0]) (by rw [evalW_var, hc]) (by omega)) ?_
  apply runs_seq
  refine runs_wset (a := a) (by simp [ha]) ?_
  set q1 := ((((q.setW "dl.a" (w0 + c)).charge 1).setW "dl.n" a).charge 1) with hq1
  have hsp1 : DList.Spells q1 "sel.w" (q1.w "dl.a") lo := by
    have h := spells_seg q1 (w0 + c) a
    rwa [show seg q1 (w0 + c) a = lo by rw [← hlo]; simp [seg, hq1],
      show w0 + c = q1.w "dl.a" by simp [hq1]] at h
  apply runs_seq
  refine (DList.buildList_spec (ops := ops) q1 lo hsp1 (by simp [hq1, hla]) hndlo
    (fun x hx => by simpa [hq1] using hlt x (List.mem_append_left _ hx))
    (by simp [hq1]; omega) (by simp [hq1]; omega)
    (fun x hx => by simpa [hq1] using hxc x (List.mem_append_left _ hx))).mono
    (fun q2 ⟨hL2, hout2, hu2, hnl2, hc2⟩ => ?_)
  have hk2 : ∀ y, y ∉ DList.buildRegs → q2.w y = q1.w y := fun y hy => hu2.wreg y hy
  have hwa2 : ∀ x, x ≠ "ent.nxt" → q2.wa x = q1.wa x := fun x hx => (hu2.warr x (by simpa using hx)).1
  have hwl2 : ∀ x, x ≠ "ent.nxt" → q2.wlen x = q1.wlen x := fun x hx => (hu2.warr x (by simpa using hx)).2
  have hcap2 : q2.cap = q.cap := by rw [hu2.cap]; simp [hq1]
  apply runs_seq
  refine runs_wset (a := q2.w "dl.h") rfl ?_
  apply runs_seq
  have hw02 : q2.w "sp.w0" = w0 := by rw [hk2 _ (by simp [DList.buildRegs])]; simp [hq1, hw0]
  have hc02 : q2.w "sp.c" = c := by rw [hk2 _ (by simp [DList.buildRegs])]; simp [hq1, hc]
  have ha02 : q2.w "sel.a" = a := by rw [hk2 _ (by simp [DList.buildRegs])]; simp [hq1, ha]
  have hb02 : q2.w "sel.b" = b := by rw [hk2 _ (by simp [DList.buildRegs])]; simp [hq1, hb]
  refine runs_wset (a := w0 + c + a)
    (evalW_add_of (evalW_add_of (by simp [hw02]) (by simp [hc02]) (by simp [hcap2]; omega))
      (by simp [ha02]) (by simp [hcap2]; omega)) ?_
  apply runs_seq
  refine runs_wset (a := b) (by simp [hb02]) ?_
  set q3 := ((((((q2.setW "sp.hlo" (q2.w "dl.h")).charge 1).setW "dl.a" (w0 + c + a)).charge 1).setW
    "dl.n" b).charge 1) with hq3
  have hsp3 : DList.Spells q3 "sel.w" (q3.w "dl.a") hi := by
    have h := spells_seg q3 (w0 + c + a) b
    rwa [show seg q3 (w0 + c + a) b = hi by
        rw [← hhi]; simp only [seg, hq3, State.charge_wa, State.setW_wa]
        rw [hwa2 _ (by simp)]; simp [hq1],
      show w0 + c + a = q3.w "dl.a" by simp [hq3]] at h
  have hwl3 : ∀ x, x ≠ "ent.nxt" → q3.wlen x = q.wlen x := by
    intro x hx; simp only [hq3, State.charge_wlen, State.setW_wlen]; rw [hwl2 x hx]; simp [hq1]
  have hnl3 : q3.wlen "ent.nxt" = q.wlen "ent.nxt" := by
    simp only [hq3, State.charge_wlen, State.setW_wlen]; rw [hnl2]; simp [hq1]
  have hcap3 : q3.cap = q.cap := by simp [hq3, hcap2]
  apply runs_seq
  refine (DList.buildList_spec (ops := ops) q3 hi hsp3 (by simp [hq3, hlb]) hndhi
    (fun x hx => by rw [hnl3]; exact hlt x (List.mem_append_right _ hx))
    (by rw [show q3.w "dl.a" = w0 + c + a by simp [hq3], hwl3 _ (by simp)]; omega)
    (by rw [show q3.w "dl.a" = w0 + c + a by simp [hq3], hcap3]; omega)
    (fun x hx => by rw [hcap3]; exact hxc x (List.mem_append_right _ hx))).mono
    (fun q4 ⟨hL4, hout4, hu4, hnl4, hc4⟩ => ?_)
  refine runs_wset (a := q4.w "dl.h") rfl ?_
  have hk4 : ∀ y, y ∉ DList.buildRegs → q4.w y = q3.w y := fun y hy => hu4.wreg y hy
  refine ⟨?_, ?_, fun y hy => ?_, ?_, ?_, ?_⟩
  · have e : ((q4.setW "sp.hhi" (q4.w "dl.h")).charge 1).w "sp.hlo" = q2.w "dl.h" := by
      simp only [State.charge_w, State.setW_w]
      rw [if_neg (by decide), hk4 _ (by simp [DList.buildRegs])]
      simp [hq3]
    rw [e]
    refine (hL2.frame (st' := q3) (by simp [hq3]) (fun i _ => by simp [hq3])).frame
      (st' := (q4.setW "sp.hhi" (q4.w "dl.h")).charge 1) (by simp [hnl4]) ?_
    intro i hi'
    simp only [State.charge_wa, State.setW_wa]
    exact hout4 i (hdisj i hi')
  · have e : ((q4.setW "sp.hhi" (q4.w "dl.h")).charge 1).w "sp.hhi" = q4.w "dl.h" := by simp
    rw [e]
    exact hL4.frame (by simp) (fun i _ => by simp)
  · simp only [List.mem_append, not_or] at hy
    simp only [State.charge_wa, State.setW_wa]
    rw [hout4 y hy.2]
    simp only [hq3, State.charge_wa, State.setW_wa]
    rw [hout2 y hy.1]
    simp [hq1]
  · have u1 : Unchanged q q1 ["ent.nxt"] [] linkRegs [] := by
      rw [hq1, unch_charge', unch_setW' (by simp [linkRegs]), unch_charge',
        unch_setW' (by simp [linkRegs])]
      exact Unchanged.refl _ _ _ _ _
    have u2 : Unchanged q1 q2 ["ent.nxt"] [] linkRegs [] :=
      hu2.mono (List.Subset.refl _) (List.Subset.refl _)
        (fun y hy => List.mem_append_right _ hy) (List.Subset.refl _)
    have u3 : Unchanged q2 q3 ["ent.nxt"] [] linkRegs [] := by
      rw [hq3, unch_charge', unch_setW' (by simp [linkRegs]), unch_charge',
        unch_setW' (by simp [linkRegs]), unch_charge', unch_setW' (by simp [linkRegs])]
      exact Unchanged.refl _ _ _ _ _
    have u4 : Unchanged q3 q4 ["ent.nxt"] [] linkRegs [] :=
      hu4.mono (List.Subset.refl _) (List.Subset.refl _)
        (fun y hy => List.mem_append_right _ hy) (List.Subset.refl _)
    have u5 : Unchanged q4 ((q4.setW "sp.hhi" (q4.w "dl.h")).charge 1) ["ent.nxt"] [] linkRegs [] := by
      rw [unch_charge', unch_setW' (by simp [linkRegs])]
      exact Unchanged.refl _ _ _ _ _
    exact u1.trans (u2.trans (u3.trans (u4.trans u5)))
  · simp [hnl4, hnl3]
  · simp only [State.charge_cost, State.setW_cost]
    simp only [hq3, State.charge_cost, State.setW_cost] at hc4
    simp only [hq1, State.charge_cost, State.setW_cost] at hc2
    rw [hla] at hc2; rw [hlb] at hc4
    omega

end Link


/-! ## Record and stack updates -/

section Recs

open Frontier.CHD.DIns Frontier.CHD.DB Frontier.CHD.MLab Frontier.CHD.LabTab

variable {ops : VOps ℝ≥0} {G : Graph}

theorem evalW_tlE {q : State ℝ≥0} {e : WExpr} {x : ℕ} (he : evalW q e = some x) (hx : 1 ≤ x)
    (hl : x - 1 < q.wlen "sel.w") (h1 : 1 < q.cap) (hc : q.wa "sel.w" (x - 1) + 1 < q.cap) :
    evalW q (tlE e) = some (q.wa "sel.w" (x - 1) + 1) := by
  simp [tlE, he, hl, fit_of_lt h1, fit_of_lt hc]

/-- the low record -/
def recLoSt (q : State ℝ≥0) (bid hlo tl a : ℕ) : State ℝ≥0 :=
  (((((q.storeW "blk.hd" bid hlo).charge 1).storeW "blk.tl" bid tl).charge 1).storeW "blk.cnt" bid a).charge 1

theorem spRecLo_run (q : State ℝ≥0) {bid hlo w0 c a : ℕ} (hbid : q.w "sp.bid" = bid)
    (hhlo : q.w "sp.hlo" = hlo) (hw0 : q.w "sp.w0" = w0) (hc : q.w "sp.c" = c) (ha : q.w "sel.a" = a)
    (ha1 : 1 ≤ a) (hbh : bid < q.wlen "blk.hd") (hbt : bid < q.wlen "blk.tl")
    (hbc : bid < q.wlen "blk.cnt") (hsl : w0 + c + a ≤ q.wlen "sel.w") (hcap : w0 + c + a < q.cap)
    (htl : q.wa "sel.w" (w0 + c + a - 1) + 1 < q.cap) :
    Runs ops spRecLo q (fun r => r = recLoSt q bid hlo (q.wa "sel.w" (w0 + c + a - 1) + 1) a) := by
  unfold spRecLo
  apply runs_seq
  refine runs_wstore (j := bid) (a := hlo) (by simp [hbid]) (by simp [hhlo]) hbh ?_
  apply runs_seq
  refine runs_wstore (j := bid) (a := q.wa "sel.w" (w0 + c + a - 1) + 1) (by simp [hbid])
    (evalW_tlE (x := w0 + c + a) (evalW_add_of (evalW_add_of (by simp [hw0]) (by simp [hc])
      (by simp; omega)) (by simp [ha]) (by simp; omega)) (by omega) (by simp; omega) (by simp; omega)
      (by simpa using htl)) (by simpa using hbt) ?_
  refine runs_wstore (j := bid) (a := a) (by simp [hbid]) (by simp [ha]) (by simpa using hbc) ?_
  rfl

/-- the high record -/
def recHiSt (q : State ℝ≥0) (nb hhi tl b : ℕ) : State ℝ≥0 :=
  (((((((((((q.setW "sp.nb" nb).charge 1).setW "blk.fresh" (nb + 1)).charge 1).storeW "blk.hd" nb
    hhi).charge 1).storeW "blk.tl" nb tl).charge 1).storeW "blk.cnt" nb b).charge 1).storeW "blk.bot"
    nb 0).charge 1

theorem spRecHi_run (q : State ℝ≥0) {nb hhi w0 c a b : ℕ} (hnb : q.w "blk.fresh" = nb)
    (hhhi : q.w "sp.hhi" = hhi) (hw0 : q.w "sp.w0" = w0) (hc : q.w "sp.c" = c) (ha : q.w "sel.a" = a)
    (hb : q.w "sel.b" = b) (hb1 : 1 ≤ b) (hnh : nb < q.wlen "blk.hd") (hnt : nb < q.wlen "blk.tl")
    (hnc : nb < q.wlen "blk.cnt") (hno : nb < q.wlen "blk.bot") (hsl : w0 + c + a + b ≤ q.wlen "sel.w")
    (hcap : w0 + c + a + b < q.cap) (hncap : nb + 1 < q.cap)
    (htl : q.wa "sel.w" (w0 + c + a + b - 1) + 1 < q.cap) :
    Runs ops spRecHi q (fun r => r = recHiSt q nb hhi (q.wa "sel.w" (w0 + c + a + b - 1) + 1) b) := by
  unfold spRecHi
  apply runs_seq
  refine runs_wset (a := nb) (by simp [hnb]) ?_
  apply runs_seq
  refine runs_wset (a := nb + 1) (by simp [hnb, fit_of_lt hncap, fit_of_lt (show 1 < q.cap by omega)]) ?_
  apply runs_seq
  refine runs_wstore (j := nb) (a := hhi) (by simp) (by simp [hhhi]) (by simpa using hnh) ?_
  apply runs_seq
  refine runs_wstore (j := nb) (a := q.wa "sel.w" (w0 + c + a + b - 1) + 1) (by simp)
    (evalW_tlE (x := w0 + c + a + b) (evalW_add_of (evalW_add_of (evalW_add_of (by simp [hw0])
      (by simp [hc]) (by simp; omega)) (by simp [ha]) (by simp; omega)) (by simp [hb]) (by simp; omega))
      (by omega) (by simp; omega) (by simp; omega) (by simpa using htl)) (by simpa using hnt) ?_
  apply runs_seq
  refine runs_wstore (j := nb) (a := b) (by simp) (by simp [hb]) (by simpa using hnc) ?_
  refine runs_wstore (j := nb) (a := 0) (by simp) (by simp [fit_of_lt (show 0 < q.cap by omega)])
    (by simpa using hno) ?_
  rfl

/-- the stack update -/
def pushSt (q : State ℝ≥0) (t nb bid lv k : ℕ) : State ℝ≥0 :=
  (((((q.storeW "dsl.stk" t nb).charge 1).storeW "dsl.stk" (t + 1) bid).charge 1).storeW "dsl.sz" lv
    (k + 1)).charge 1

theorem spPush_run (q : State ℝ≥0) {t nb bid lv k : ℕ} (ht : q.w "sp.t" = t) (hnb : q.w "sp.nb" = nb)
    (hbid : q.w "sp.bid" = bid) (hlv : q.w "ds.lv" = lv) (hk : q.wa "dsl.sz" lv = k)
    (hts : t + 1 < q.wlen "dsl.stk") (hls : lv < q.wlen "dsl.sz") (htc : t + 1 < q.cap)
    (hkc : k + 1 < q.cap) :
    Runs ops spPush q (fun r => r = pushSt q t nb bid lv k) := by
  unfold spPush
  apply runs_seq
  refine runs_wstore (j := t) (a := nb) (by simp [ht]) (by simp [hnb]) (by omega) ?_
  apply runs_seq
  refine runs_wstore (j := t + 1) (a := bid) (by simp [ht, fit_of_lt htc, fit_of_lt (show 1 < q.cap by omega)])
    (by simp [hbid]) (by simpa using hts) ?_
  refine runs_wstore (j := lv) (a := k + 1) (by simp [hlv])
    (by simp [hlv, hls, hk, fit_of_lt hkc, fit_of_lt (show 1 < q.cap by omega)]) (by simpa using hls) ?_
  rfl

/-- the separator copy `blkA[nb] := entA[med]` (through `fs.X`) -/
def sepSt (q : State ℝ≥0) (med nb : ℕ) : State ℝ≥0 :=
  ((((((((((((((((((((q.setV "fs.Xl" (q.va "ent.len" med)).charge 1).setW "fs.Xh" (q.wa "ent.h" med)).charge
    1).setW "fs.Xv" (q.wa "ent.v" med)).charge 1).setW "fs.Xe" (q.wa "ent.e" med)).charge 1).setW "fs.Xr"
    (q.wa "ent.r" med)).charge 1).storeV "blk.len" nb (q.va "ent.len" med)).charge 1).storeW "blk.h" nb
    (q.wa "ent.h" med)).charge 1).storeW "blk.v" nb (q.wa "ent.v" med)).charge 1).storeW "blk.e" nb
    (q.wa "ent.e" med)).charge 1).storeW "blk.r" nb (q.wa "ent.r" med)).charge 1)

theorem spRecSep_run (q : State ℝ≥0) {med nb : ℕ} (hmed : q.w "sp.med" = med) (hnb : q.w "sp.nb" = nb)
    (hbe : entA.InB q med) (hbb : blkA.InB q nb) :
    Runs realOps spRecSep q (fun r => r = sepSt q med nb) := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := hbe
  obtain ⟨b1, b2, b3, b4, b5⟩ := hbb
  simp only [entA] at e1 e2 e3 e4 e5
  simp only [blkA] at b1 b2 b3 b4 b5
  unfold spRecSep loadA storeA
  simp only [entA, blkA, fsX]
  apply runs_seq
  apply runs_seq
  refine runs_vset (a := q.va "ent.len" med) (evalV_load_of (by simp [hmed]) e1) ?_
  apply runs_seq
  refine runs_wset (a := q.wa "ent.h" med) (evalW_load_of (by simp [hmed]) (by simpa using e2)) ?_
  apply runs_seq
  refine runs_wset (a := q.wa "ent.v" med) (evalW_load_of (by simp [hmed]) (by simpa using e3)) ?_
  apply runs_seq
  refine runs_wset (a := q.wa "ent.e" med) (evalW_load_of (by simp [hmed]) (by simpa using e4)) ?_
  refine runs_wset (a := q.wa "ent.r" med) (evalW_load_of (by simp [hmed]) (by simpa using e5)) ?_
  apply runs_seq
  refine runs_vstore (j := nb) (a := q.va "ent.len" med) (by simp [hnb]) (by simp <;> rfl)
    (by simpa using b1) ?_
  apply runs_seq
  refine runs_wstore (j := nb) (a := q.wa "ent.h" med) (by simp [hnb]) (by simp) (by simpa using b2) ?_
  apply runs_seq
  refine runs_wstore (j := nb) (a := q.wa "ent.v" med) (by simp [hnb]) (by simp) (by simpa using b3) ?_
  apply runs_seq
  refine runs_wstore (j := nb) (a := q.wa "ent.e" med) (by simp [hnb]) (by simp) (by simpa using b4) ?_
  refine runs_wstore (j := nb) (a := q.wa "ent.r" med) (by simp [hnb]) (by simp) (by simpa using b5) ?_
  rfl

/-- the state after `spRecs; dsp.go := 1` -/
def recsSt (q : State ℝ≥0) (bid hlo tl1 a nb hhi tl2 b med t lv k : ℕ) : State ℝ≥0 :=
  ((pushSt (sepSt (recHiSt (recLoSt q bid hlo tl1 a) nb hhi tl2 b) med nb) t nb bid lv k).setW
    "dsp.go" 1).charge 1

section RecsSt

variable (q : State ℝ≥0) (bid hlo tl1 a nb hhi tl2 b med t lv k : ℕ)

theorem recsSt_hd (x : ℕ) : (recsSt q bid hlo tl1 a nb hhi tl2 b med t lv k).wa "blk.hd" x =
    if x = nb then hhi else if x = bid then hlo else q.wa "blk.hd" x := by
  simp [recsSt, pushSt, sepSt, recHiSt, recLoSt]

theorem recsSt_tl (x : ℕ) : (recsSt q bid hlo tl1 a nb hhi tl2 b med t lv k).wa "blk.tl" x =
    if x = nb then tl2 else if x = bid then tl1 else q.wa "blk.tl" x := by
  simp [recsSt, pushSt, sepSt, recHiSt, recLoSt]

theorem recsSt_cnt (x : ℕ) : (recsSt q bid hlo tl1 a nb hhi tl2 b med t lv k).wa "blk.cnt" x =
    if x = nb then b else if x = bid then a else q.wa "blk.cnt" x := by
  simp [recsSt, pushSt, sepSt, recHiSt, recLoSt]

theorem recsSt_bot (x : ℕ) : (recsSt q bid hlo tl1 a nb hhi tl2 b med t lv k).wa "blk.bot" x =
    if x = nb then 0 else q.wa "blk.bot" x := by
  simp [recsSt, pushSt, sepSt, recHiSt, recLoSt]

theorem recsSt_stk (x : ℕ) : (recsSt q bid hlo tl1 a nb hhi tl2 b med t lv k).wa "dsl.stk" x =
    if x = t + 1 then bid else if x = t then nb else q.wa "dsl.stk" x := by
  simp [recsSt, pushSt, sepSt, recHiSt, recLoSt]

theorem recsSt_sz (x : ℕ) : (recsSt q bid hlo tl1 a nb hhi tl2 b med t lv k).wa "dsl.sz" x =
    if x = lv then k + 1 else q.wa "dsl.sz" x := by
  simp [recsSt, pushSt, sepSt, recHiSt, recLoSt]

theorem recsSt_blkA (x : ℕ) :
    (recsSt q bid hlo tl1 a nb hhi tl2 b med t lv k).va "blk.len" x =
      (if x = nb then q.va "ent.len" med else q.va "blk.len" x) ∧
    (recsSt q bid hlo tl1 a nb hhi tl2 b med t lv k).wa "blk.h" x =
      (if x = nb then q.wa "ent.h" med else q.wa "blk.h" x) ∧
    (recsSt q bid hlo tl1 a nb hhi tl2 b med t lv k).wa "blk.v" x =
      (if x = nb then q.wa "ent.v" med else q.wa "blk.v" x) ∧
    (recsSt q bid hlo tl1 a nb hhi tl2 b med t lv k).wa "blk.e" x =
      (if x = nb then q.wa "ent.e" med else q.wa "blk.e" x) ∧
    (recsSt q bid hlo tl1 a nb hhi tl2 b med t lv k).wa "blk.r" x =
      (if x = nb then q.wa "ent.r" med else q.wa "blk.r" x) := by
  simp [recsSt, pushSt, sepSt, recHiSt, recLoSt]

theorem recsSt_wa (c : String) (hc : c ∉ ["blk.hd", "blk.tl", "blk.cnt", "blk.bot", "blk.h", "blk.v",
      "blk.e", "blk.r", "dsl.stk", "dsl.sz"]) :
    (recsSt q bid hlo tl1 a nb hhi tl2 b med t lv k).wa c = q.wa c := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hc
  funext x
  simp [recsSt, pushSt, sepSt, recHiSt, recLoSt, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

theorem recsSt_va (c : String) (hc : c ≠ "blk.len") :
    (recsSt q bid hlo tl1 a nb hhi tl2 b med t lv k).va c = q.va c := by
  funext x
  simp [recsSt, pushSt, sepSt, recHiSt, recLoSt, hc]

theorem recsSt_len : (recsSt q bid hlo tl1 a nb hhi tl2 b med t lv k).wlen = q.wlen ∧
    (recsSt q bid hlo tl1 a nb hhi tl2 b med t lv k).vlen = q.vlen ∧
    (recsSt q bid hlo tl1 a nb hhi tl2 b med t lv k).cap = q.cap ∧
    (recsSt q bid hlo tl1 a nb hhi tl2 b med t lv k).procs = q.procs ∧
    (recsSt q bid hlo tl1 a nb hhi tl2 b med t lv k).cost = q.cost + 23 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [recsSt, pushSt, sepSt, recHiSt, recLoSt] <;> ring

theorem recsSt_w (y : String) (hy : y ∉ ["sp.nb", "blk.fresh", "dsp.go", "fs.Xh", "fs.Xv", "fs.Xe", "fs.Xr"]) :
    (recsSt q bid hlo tl1 a nb hhi tl2 b med t lv k).w y = q.w y := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hy
  simp [recsSt, pushSt, sepSt, recHiSt, recLoSt, h1, h2, h3, h4, h5, h6, h7]

theorem recsSt_regs : (recsSt q bid hlo tl1 a nb hhi tl2 b med t lv k).w "sp.nb" = nb ∧
    (recsSt q bid hlo tl1 a nb hhi tl2 b med t lv k).w "blk.fresh" = nb + 1 ∧
    (recsSt q bid hlo tl1 a nb hhi tl2 b med t lv k).w "dsp.go" = 1 := by
  simp [recsSt, pushSt, sepSt, recHiSt, recLoSt]

theorem recsSt_v (y : String) (hy : y ≠ "fs.Xl") :
    (recsSt q bid hlo tl1 a nb hhi tl2 b med t lv k).v y = q.v y := by
  simp [recsSt, pushSt, sepSt, recHiSt, recLoSt, hy]

end RecsSt

set_option maxHeartbeats 1000000 in
theorem spRecsGo_run (q : State ℝ≥0) {bid hlo w0 c a nb hhi b med t lv k : ℕ}
    (hbid : q.w "sp.bid" = bid) (hhlo : q.w "sp.hlo" = hlo) (hw0 : q.w "sp.w0" = w0)
    (hc : q.w "sp.c" = c) (ha : q.w "sel.a" = a) (hb : q.w "sel.b" = b) (hnb : q.w "blk.fresh" = nb)
    (hhhi : q.w "sp.hhi" = hhi) (hmed : q.w "sp.med" = med) (ht : q.w "sp.t" = t)
    (hlv : q.w "ds.lv" = lv) (hk : q.wa "dsl.sz" lv = k) (ha1 : 1 ≤ a) (hb1 : 1 ≤ b)
    (hbA : BlkArrs q (max bid nb + 1)) (hsl : w0 + c + a + b ≤ q.wlen "sel.w")
    (hcap : w0 + c + a + b + 1 < q.cap) (hncap : nb + 1 < q.cap)
    (htl1 : q.wa "sel.w" (w0 + c + a - 1) + 1 < q.cap)
    (htl2 : q.wa "sel.w" (w0 + c + a + b - 1) + 1 < q.cap)
    (hbe : entA.InB q med) (hts : t + 1 < q.wlen "dsl.stk") (hls : lv < q.wlen "dsl.sz")
    (htc : t + 1 < q.cap) (hkc : k + 1 < q.cap) :
    Runs realOps (seq spRecs (wset "dsp.go" (lit 1))) q (fun r =>
      r = recsSt q bid hlo (q.wa "sel.w" (w0 + c + a - 1) + 1) a nb hhi
        (q.wa "sel.w" (w0 + c + a + b - 1) + 1) b med t lv k) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hbA
  simp only [blkA] at a5 a6 a7 a8 a9
  have hbh : bid < q.wlen "blk.hd" := by omega
  have hbt : bid < q.wlen "blk.tl" := by omega
  have hbc : bid < q.wlen "blk.cnt" := by omega
  have hnh : nb < q.wlen "blk.hd" := by omega
  have hnt : nb < q.wlen "blk.tl" := by omega
  have hnc : nb < q.wlen "blk.cnt" := by omega
  have hno : nb < q.wlen "blk.bot" := by omega
  unfold spRecs
  apply runs_seq
  apply runs_seq
  refine (spRecLo_run q hbid hhlo hw0 hc ha ha1 hbh hbt hbc (by omega) (by omega) htl1).mono
    (fun q8 hq8 => ?_)
  subst hq8
  apply runs_seq
  refine (spRecHi_run _ (nb := nb) (hhi := hhi) (w0 := w0) (c := c) (a := a) (b := b)
    (by simp [recLoSt, hnb]) (by simp [recLoSt, hhhi]) (by simp [recLoSt, hw0]) (by simp [recLoSt, hc])
    (by simp [recLoSt, ha]) (by simp [recLoSt, hb]) hb1 (by simpa [recLoSt] using hnh)
    (by simpa [recLoSt] using hnt) (by simpa [recLoSt] using hnc) (by simpa [recLoSt] using hno)
    (by simpa [recLoSt] using hsl) (by simp [recLoSt]; omega) (by simpa [recLoSt] using hncap)
    (by simpa [recLoSt] using htl2)).mono (fun q9 hq9 => ?_)
  subst hq9
  apply runs_seq
  refine (spRecSep_run _ (med := med) (nb := nb) (by simp [recHiSt, recLoSt, hmed])
    (by simp [recHiSt, recLoSt]) ?_ ?_).mono (fun q10 hq10 => ?_)
  · obtain ⟨e1, e2, e3, e4, e5⟩ := hbe
    exact ⟨by simpa [recHiSt, recLoSt] using e1, by simpa [recHiSt, recLoSt] using e2,
      by simpa [recHiSt, recLoSt] using e3, by simpa [recHiSt, recLoSt] using e4,
      by simpa [recHiSt, recLoSt] using e5⟩
  · exact ⟨by simp [recHiSt, recLoSt, blkA]; omega, by simp [recHiSt, recLoSt, blkA]; omega,
      by simp [recHiSt, recLoSt, blkA]; omega, by simp [recHiSt, recLoSt, blkA]; omega,
      by simp [recHiSt, recLoSt, blkA]; omega⟩
  subst hq10
  refine (spPush_run _ (t := t) (nb := nb) (bid := bid) (lv := lv) (k := k)
    (by simp [sepSt, recHiSt, recLoSt, ht]) (by simp [sepSt, recHiSt, recLoSt])
    (by simp [sepSt, recHiSt, recLoSt, hbid]) (by simp [sepSt, recHiSt, recLoSt, hlv])
    (by simp [sepSt, recHiSt, recLoSt, hk]) (by simpa [sepSt, recHiSt, recLoSt] using hts)
    (by simpa [sepSt, recHiSt, recLoSt] using hls) (by simpa [sepSt, recHiSt, recLoSt] using htc)
    (by simpa [sepSt, recHiSt, recLoSt] using hkc)).mono (fun q11 hq11 => ?_)
  subst hq11
  refine runs_wset (a := 1) (by simp [pushSt, sepSt, recHiSt, recLoSt, fit_of_lt (show 1 < q.cap by omega)]) ?_
  have e1 : (recLoSt q bid hlo (q.wa "sel.w" (w0 + c + a - 1) + 1) a).wa "sel.w" = q.wa "sel.w" := by
    funext x; simp [recLoSt]
  rw [e1]
  rfl

end Recs

/-! ## Layer-A facts about one split -/

section LayerA

open Frontier.CHD.DB Frontier.CHD.DL

variable {κ α : Type*} [DecidableEq κ] [LinearOrder α] [Inhabited α]

theorem subperm_nodup {β : Type*} {l₁ l₂ : List β} (h : l₁.Subperm l₂) (hn : l₂.Nodup) : l₁.Nodup := by
  obtain ⟨l, p, s⟩ := h
  exact p.nodup_iff.mp (s.nodup hn)

/-- the value of the entry with id `i` of an entry list -/
def valOf (es : List (Entry κ α)) (i : ℕ) : α :=
  ((es.find? (fun e => decide (e.id = i))).map (·.val)).getD default

theorem valOf_of_mem {es : List (Entry κ α)} (hnd : (es.map (·.id)).Nodup) {e : Entry κ α}
    (he : e ∈ es) : valOf es e.id = e.val := by
  unfold valOf
  have hs : (es.find? (fun x => decide (x.id = e.id))).isSome :=
    List.find?_isSome.mpr ⟨e, he, by simp⟩
  obtain ⟨e', he'⟩ := Option.isSome_iff_exists.mp hs
  have hm := List.mem_of_find?_eq_some he'
  have hp := List.find?_some he'
  simp only [decide_eq_true_eq] at hp
  have := List.inj_on_of_nodup_map hnd hm he hp
  rw [he', this]; rfl

theorem map_valOf_liveOf (L : Live κ α) {es : List (Entry κ α)} (hnd : (es.map (·.id)).Nodup) :
    ((liveOf L es).map (·.id)).map (valOf es) = (liveOf L es).map (·.val) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro e he
  exact valOf_of_mem hnd (List.mem_of_mem_filter he)

/-- the RAM median is `medOf` -/
theorem medOf_eq_of_kth (L : Live κ α) {b : Block κ α} (hnd : (b.ents.map (·.id)).Nodup) {x : α}
    (h : Frontier.CHD.IsKth (((liveOf L b.ents).map (·.id)).map (valOf b.ents))
      ((liveOf L b.ents).length / 2) x) (hpos : 0 < (liveOf L b.ents).length) : x = medOf L b := by
  rw [map_valOf_liveOf L hnd] at h
  exact h.unique (Frontier.CHD.selectC_isKth _ (by simp; omega))

theorem lo_ids (L : Live κ α) {b : Block κ α} (hnd : (b.ents.map (·.id)).Nodup) {med : ℕ}
    (hmed : valOf b.ents med = medOf L b) :
    ((liveOf L b.ents).map (·.id)).filter (fun x => decide (valOf b.ents x < valOf b.ents med)) =
      (loOf L b).map (·.id) := by
  rw [hmed, List.filter_map]
  unfold loOf
  congr 1
  apply List.filter_congr
  intro e he
  simp [valOf_of_mem hnd (List.mem_of_mem_filter he)]

theorem hi_ids (L : Live κ α) {b : Block κ α} (hnd : (b.ents.map (·.id)).Nodup) {med : ℕ}
    (hmed : valOf b.ents med = medOf L b) :
    ((liveOf L b.ents).map (·.id)).filter (fun x => decide (valOf b.ents med ≤ valOf b.ents x)) =
      (hiOf L b).map (·.id) := by
  rw [hmed, List.filter_map]
  unfold hiOf
  congr 1
  apply List.filter_congr
  intro e he
  simp [valOf_of_mem hnd (List.mem_of_mem_filter he)]

theorem lohi_perm (L : Live κ α) (b : Block κ α) :
    ((loOf L b).map (·.id) ++ (hiOf L b).map (·.id)).Perm ((liveOf L b.ents).map (·.id)) := by
  rw [← List.map_append]
  apply List.Perm.map
  unfold loOf hiOf
  have := List.filter_append_perm (fun e : Entry κ α => decide (e.val < medOf L b)) (liveOf L b.ents)
  refine (List.Perm.append_left _ (List.Perm.of_eq ?_)).trans this
  apply List.filter_congr; intro e _
  by_cases h : e.val < medOf L b
  · simp [h, not_le.mpr h]
  · simp [h, not_lt.mp h]

theorem lohi_subperm (L : Live κ α) (b : Block κ α) :
    ((loOf L b).map (·.id) ++ (hiOf L b).map (·.id)).Subperm (b.ents.map (·.id)) :=
  (lohi_perm L b).subperm.trans (List.Sublist.map _ (List.filter_sublist)).subperm

omit [DecidableEq κ] in
theorem lohi_mem {L : Live κ α} {b : Block κ α} {e : Entry κ α} (he : e ∈ loOf L b ∨ e ∈ hiOf L b) :
    e ∈ b.ents := by
  rcases he with he | he
  · exact List.mem_of_mem_filter (List.mem_of_mem_filter he)
  · exact List.mem_of_mem_filter (List.mem_of_mem_filter he)

theorem map_valOf_ids {es : List (Entry κ α)} (hnd : (es.map (·.id)).Nodup) :
    (es.map (·.id)).map (valOf es) = es.map (·.val) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro e he
  exact valOf_of_mem hnd he

theorem filt_ids_lt {es : List (Entry κ α)} (hnd : (es.map (·.id)).Nodup) {med : ℕ} {x : α}
    (hmed : valOf es med = x) :
    (es.map (·.id)).filter (fun y => decide (valOf es y < valOf es med)) =
      (es.filter (fun e => decide (e.val < x))).map (·.id) := by
  rw [hmed, List.filter_map]
  congr 1
  apply List.filter_congr
  intro e he
  simp [valOf_of_mem hnd he]

theorem filt_ids_ge {es : List (Entry κ α)} (hnd : (es.map (·.id)).Nodup) {med : ℕ} {x : α}
    (hmed : valOf es med = x) :
    (es.map (·.id)).filter (fun y => decide (valOf es med ≤ valOf es y)) =
      (es.filter (fun e => decide (x ≤ e.val))).map (·.id) := by
  rw [hmed, List.filter_map]
  congr 1
  apply List.filter_congr
  intro e he
  simp [valOf_of_mem hnd he]

end LayerA

/-! ## The representation after a split (a pure state lemma) -/

section SplitRep

open Frontier.CHD.DIns Frontier.CHD.DB Frontier.CHD.DL Frontier.CHD.MLab Frontier.CHD.LabTab
  Frontier.CHD.DList

variable {G : Graph} {s : Fin G.n}

theorem recsOf_cons (st : State ℝ≥0) (bse : ℕ) (b : Block (Fin G.n) (WLab G s))
    (bs : List (Block (Fin G.n) (WLab G s))) :
    recsOf st bse (b :: bs) = (st.wa "dsl.stk" (bse + bs.length), b) :: recsOf st bse bs := by
  unfold recsOf
  rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.zip_cons_cons]
  refine List.cons_eq_cons.mpr ⟨rfl, ?_⟩
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  simp only [Function.comp, stkId]
  congr 2
  omega

theorem recsOf_congr {st r : State ℝ≥0} (bse : ℕ) (P : List (Block (Fin G.n) (WLab G s)))
    (h : ∀ x, x < bse + P.length → r.wa "dsl.stk" x = st.wa "dsl.stk" x) :
    recsOf r bse P = recsOf st bse P := by
  unfold recsOf
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  unfold stkId
  exact h _ (by omega)

theorem sepRep_holds {st r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bid : ℕ} {sp : WithBot (WLab G s)} (h : SepRep st H V bid sp)
    (hb : r.wa "blk.bot" bid = st.wa "blk.bot" bid)
    (hA : ∀ y : MLabel G, AHolds st blkA bid y → AHolds r blkA bid y) : SepRep r H V bid sp := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [hb]; exact h1, ?_⟩
  rcases h2 with h2 | ⟨m, q, hA', hR, hq⟩
  · exact Or.inl h2
  · exact Or.inr ⟨m, q, hA m hA', hR, hq⟩

/-- the entry pool's key/label arrays and the live map are the same in `r` as in `st` -/
structure EntSame (st r : State ℝ≥0) : Prop where
  key : r.wa "ent.key" = st.wa "ent.key"
  len : r.va "ent.len" = st.va "ent.len"
  hh : r.wa "ent.h" = st.wa "ent.h"
  vv : r.wa "ent.v" = st.wa "ent.v"
  ee : r.wa "ent.e" = st.wa "ent.e"
  rr : r.wa "ent.r" = st.wa "ent.r"
  live : r.wa "live" = st.wa "live"

theorem entRep_same {st r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {i : ℕ} {v : Fin G.n} {a : WLab G s} (h : EntRep st H V i v a) (hE : EntSame st r) :
    EntRep r H V i v a :=
  h.of_eq (by rw [hE.key]) (by rw [show entA.l = "ent.len" from rfl, hE.len])
    (by rw [show entA.h = "ent.h" from rfl, hE.hh]) (by rw [show entA.v = "ent.v" from rfl, hE.vv])
    (by rw [show entA.e = "ent.e" from rfl, hE.ee]) (by rw [show entA.r = "ent.r" from rfl, hE.rr])

theorem liveRep_same {st r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {L : Live (Fin G.n) (WLab G s)} (h : LiveRep st H V L) (hE : EntSame st r)
    (hwl : r.wlen "live" = st.wlen "live") : LiveRep r H V L :=
  ⟨by rw [hwl]; exact h.1, fun v => ⟨by rw [hE.live]; exact (h.2 v).1,
    fun i a hia => entRep_same ((h.2 v).2 i a hia) hE⟩⟩

theorem blkArrs_same {st r : State ℝ≥0} {bcap : ℕ} (h : BlkArrs st bcap) (hwl : r.wlen = st.wlen)
    (hvl : r.vlen = st.vlen) : BlkArrs r bcap := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨by rw [hwl]; exact h1, by rw [hwl]; exact h2, by rw [hwl]; exact h3, by rw [hwl]; exact h4,
    by rw [hvl]; exact h5, by rw [hwl]; exact h6, by rw [hwl]; exact h7, by rw [hwl]; exact h8,
    by rw [hwl]; exact h9⟩

/-- `DRep` of a structure follows from a record family containing its stack records -/
theorem dRep_of_recs {r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap lv bse : ℕ} {D : DStr (Fin G.n) (WLab G s)} {ext : List (ℕ × Block (Fin G.n) (WLab G s))}
    (hR : RecsOK r H V (recsOf r bse D.blocks ++ ext))
    (hid : ∀ p ∈ recsOf r bse D.blocks, p.1 < bcap)
    (hsz : r.wa "dsl.sz" lv = D.blocks.length) (hszb : lv < r.wlen "dsl.sz")
    (hstkb : bse + D.blocks.length ≤ r.wlen "dsl.stk") : DRep r H V bcap lv bse D := by
  have hnd : ((List.range D.blocks.length).map (stkId r bse D.blocks.length)).Nodup := by
    have h1 := hR.1
    rw [List.map_append] at h1
    have h2 := (List.nodup_append.mp h1).1
    unfold recsOf at h2
    rwa [List.map_fst_zip (by simp)] at h2
  refine ⟨hsz, hszb, hstkb, fun i hi => ?_, fun i j hi hj h => ?_, fun i hi => ?_⟩
  · exact hR.2.1 _ (List.mem_append_left _ (mem_recsOf r bse D.blocks i hi))
  · exact List.inj_on_of_nodup_map hnd (List.mem_range.mpr hi) (List.mem_range.mpr hj) h
  · exact hid _ (mem_recsOf r bse D.blocks i hi)

/-- the stack records of a represented structure are below `bcap` -/
theorem recsOf_bound {st : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap lv bse : ℕ} {D : DStr (Fin G.n) (WLab G s)} (hD : DRep st H V bcap lv bse D) :
    ∀ p ∈ recsOf st bse D.blocks, p.1 < bcap := by
  intro p hp
  unfold recsOf at hp
  have h1 := (List.of_mem_zip hp).1
  obtain ⟨i, hi, he⟩ := List.mem_map.mp h1
  rw [← he]
  exact hD.bidb i (List.mem_range.mp hi)

set_option maxHeartbeats 1000000 in
/-- **The representation after one split** (no execution): from the representation of
`b :: bs` in `q` and the cell-level effect of the split on `r`, the records of
`⟨b.sep, lo⟩ :: ⟨sep', hi⟩ :: bs` form a valid family in `r` and `r` represents the split structure. -/
theorem split_reps {q r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap lv bse nb bid : ℕ} {M : ℕ} {Bd : WLab G s} {b : Block (Fin G.n) (WLab G s)}
    {bs : List (Block (Fin G.n) (WLab G s))} {ext : List (ℕ × Block (Fin G.n) (WLab G s))}
    {lo hi : List (Entry (Fin G.n) (WLab G s))} {sep' : WithBot (WLab G s)} {m : MLabel G}
    {pm : List (Fin G.m)}
    (hD : DRep q H V bcap lv bse ⟨M, Bd, b :: bs⟩)
    (hR : RecsOK q H V (recsOf q bse (b :: bs) ++ ext))
    (hfr : ∀ p ∈ recsOf q bse (b :: bs) ++ ext, p.1 < nb) (hnb : nb < bcap)
    (hbid : q.wa "dsl.stk" (bse + bs.length) = bid)
    (hsub : ((lo ++ hi).map (·.id)).Subperm (b.ents.map (·.id)))
    (hmem : ∀ e ∈ lo ++ hi, e ∈ b.ents)
    (hsep : sep' = ((((toW (s := s) pm : WalkOrd G s) : WLab G s)) : WithBot (WLab G s)))
    (hmR : Rep (s := s) H V m pm)
    (hES : EntSame q r) (hnx : ∀ y, y ∉ (lo ++ hi).map (·.id) → r.wa "ent.nxt" y = q.wa "ent.nxt" y)
    (hwl : r.wlen = q.wlen)
    (hhd : ∀ x, x ≠ bid → x ≠ nb → r.wa "blk.hd" x = q.wa "blk.hd" x)
    (htl : ∀ x, x ≠ bid → x ≠ nb → r.wa "blk.tl" x = q.wa "blk.tl" x)
    (hcnt : ∀ x, x ≠ bid → x ≠ nb → r.wa "blk.cnt" x = q.wa "blk.cnt" x)
    (hbot : ∀ x, x ≠ nb → r.wa "blk.bot" x = q.wa "blk.bot" x)
    (hA : ∀ x, x ≠ nb → ∀ y : MLabel G, AHolds q blkA x y → AHolds r blkA x y)
    (hLo : LList r (r.wa "blk.hd" bid) (lo.map (·.id)))
    (hHi : LList r (r.wa "blk.hd" nb) (hi.map (·.id)))
    (hclo : r.wa "blk.cnt" bid = lo.length) (hchi : r.wa "blk.cnt" nb = hi.length)
    (htlo : r.wa "blk.tl" bid = tlWord (lo.map (·.id)))
    (hthi : r.wa "blk.tl" nb = tlWord (hi.map (·.id)))
    (hbnb : r.wa "blk.bot" nb = 0) (hAnb : AHolds r blkA nb m)
    (hstk : ∀ x, x < bse + bs.length → r.wa "dsl.stk" x = q.wa "dsl.stk" x)
    (hs0 : r.wa "dsl.stk" (bse + bs.length) = nb) (hs1 : r.wa "dsl.stk" (bse + bs.length + 1) = bid)
    (hsz : r.wa "dsl.sz" lv = bs.length + 2) (hstkl : bse + bs.length + 2 ≤ q.wlen "dsl.stk") :
    RecsOK r H V (recsOf r bse (⟨b.sep, lo⟩ :: ⟨sep', hi⟩ :: bs) ++ ext) ∧
      DRep r H V bcap lv bse ⟨M, Bd, ⟨b.sep, lo⟩ :: ⟨sep', hi⟩ :: bs⟩ ∧
      (∀ p ∈ recsOf r bse (⟨b.sep, lo⟩ :: ⟨sep', hi⟩ :: bs) ++ ext, p.1 < nb + 1) := by
  set rest := recsOf q bse bs ++ ext with hrest
  have e1 : recsOf q bse (b :: bs) ++ ext = (bid, b) :: rest := by
    rw [recsOf_cons, hbid]; rfl
  have e2 : recsOf r bse (⟨b.sep, lo⟩ :: ⟨sep', hi⟩ :: bs) ++ ext =
      (bid, ⟨b.sep, lo⟩) :: (nb, ⟨sep', hi⟩) :: rest := by
    rw [recsOf_cons, recsOf_cons, recsOf_congr bse bs hstk]
    simp only [List.length_cons, hs0, show bse + (bs.length + 1) = bse + bs.length + 1 by omega, hs1]
    rfl
  rw [e1] at hR hfr
  obtain ⟨hn, hB, he⟩ := hR
  simp only [List.map_cons, List.nodup_cons] at hn
  obtain ⟨hbr, hrn⟩ := hn
  have hbnb' : bid < nb := hfr (bid, b) List.mem_cons_self
  have hrnb : ∀ p ∈ rest, p.1 < nb := fun p hp => hfr p (List.mem_cons_of_mem _ hp)
  have hBb : BlkRep q H V bid b := hB (bid, b) List.mem_cons_self
  have hBr : ∀ p ∈ rest, BlkRep q H V p.1 p.2 := fun p hp => hB p (List.mem_cons_of_mem _ hp)
  simp only [List.map_cons, entIds_cons] at he
  have hdisj : ∀ x ∈ b.ents.map (·.id), x ∉ entIds (rest.map Prod.snd) := by
    intro x hx hx'
    exact (List.nodup_append.mp he).2.2 x hx x hx' rfl
  have hRnew : RecsOK r H V ((bid, ⟨b.sep, lo⟩) :: (nb, ⟨sep', hi⟩) :: rest) := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or]
      refine ⟨⟨by omega, hbr⟩, fun h => ?_, hrn⟩
      obtain ⟨p, hp, hp1⟩ := List.mem_map.mp h
      have := hrnb p hp
      omega
    · intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | rfl | hp
      · obtain ⟨h1, _, h3, _, _⟩ := hBb
        refine ⟨sepRep_holds h1 (hbot _ (by omega)) (hA _ (by omega)), hLo, fun x hx => ?_, hclo, htlo⟩
        exact entRep_same (h3 x (hmem x (List.mem_append_left _ hx))) hES
      · refine ⟨⟨by rw [hbnb, hsep]; simp, Or.inr ⟨m, pm, hAnb, hmR, hsep⟩⟩, hHi, fun x hx => ?_, hchi,
          hthi⟩
        exact entRep_same ((hBb.2.2.1) x (hmem x (List.mem_append_right _ hx))) hES
      · obtain ⟨h1, h2, h3, h4, h5⟩ := hBr p hp
        have hpb : p.1 ≠ bid := fun h => hbr (h ▸ List.mem_map_of_mem hp)
        have hpn : p.1 ≠ nb := by have := hrnb p hp; omega
        refine ⟨sepRep_holds h1 (hbot _ hpn) (hA _ hpn), ?_, fun x hx => entRep_same (h3 x hx) hES,
          by rw [hcnt _ hpb hpn]; exact h4, by rw [htl _ hpb hpn]; exact h5⟩
        rw [hhd _ hpb hpn]
        refine h2.of_eq (fun j hj => hnx j ?_) (le_of_eq (by rw [hwl]))
        intro hj'
        have hjb : j ∈ b.ents.map (·.id) := hsub.subset hj'
        apply hdisj j hjb
        unfold entIds
        exact List.mem_flatMap.mpr ⟨p.2, List.mem_map_of_mem hp, hj⟩
    · simp only [List.map_cons, entIds_cons]
      have hs2 : (lo.map (·.id) ++ (hi.map (·.id) ++ entIds (rest.map Prod.snd))).Subperm
          (b.ents.map (·.id) ++ entIds (rest.map Prod.snd)) := by
        rw [← List.append_assoc, ← List.map_append]
        exact hsub.append (List.Subperm.refl _)
      exact subperm_nodup hs2 he
  have hfr' : ∀ p ∈ (bid, (⟨b.sep, lo⟩ : Block (Fin G.n) (WLab G s))) ::
      (nb, (⟨sep', hi⟩ : Block (Fin G.n) (WLab G s))) :: rest, p.1 < nb + 1 := by
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | rfl | hp
    · show bid < nb + 1; omega
    · show nb < nb + 1; omega
    · have := hrnb p hp; omega
  rw [e2]
  refine ⟨hRnew, ?_, hfr'⟩
  refine dRep_of_recs (ext := ext) (by rw [e2]; exact hRnew) (fun p hp => ?_) (by simpa using hsz)
    (by rw [hwl]; exact hD.szb) (by rw [hwl]; simp; omega)
  have hp' := List.mem_append_left ext hp
  rw [e2] at hp'
  have := hfr' p hp'
  omega

end SplitRep

/-! ## The comparison instance for the entries of a block -/

section Inst

open Frontier.CHD.DIns Frontier.CHD.DB Frontier.CHD.DL Frontier.CHD.MLab Frontier.CHD.LabTab

variable {G : Graph} {s : Fin G.n}

/-- key representation for the entries `es` of the block being split -/
def KRB (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ) (es : List (Entry (Fin G.n) (WLab G s)))
    (st : State ℝ≥0) : Prop :=
  (∀ e ∈ es, EntRep st H V e.id e.key e.val ∧ entA.InB st e.id) ∧ 1 < st.cap

theorem krb_frame {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {es : List (Entry (Fin G.n) (WLab G s))} :
    ∀ s r, KRB H V es s → (∀ b, b ≠ "sel.w" → r.wa b = s.wa b) → r.wlen = s.wlen → r.va = s.va →
      r.vlen = s.vlen → r.cap = s.cap → KRB H V es r := by
  intro s r ⟨hK, hc⟩ hwa hwl hva hvl hcap
  refine ⟨fun e he => ⟨(hK e he).1.of_eq (by rw [hwa _ (by simp)]) (by rw [hva])
    (by rw [hwa _ (by simp [entA])]) (by rw [hwa _ (by simp [entA])]) (by rw [hwa _ (by simp [entA])])
    (by rw [hwa _ (by simp [entA])]), ?_⟩, by rw [hcap]; exact hc⟩
  obtain ⟨b1, b2, b3, b4, b5⟩ := (hK e he).2
  exact ⟨by rw [hvl]; exact b1, by rw [hwl]; exact b2, by rw [hwl]; exact b3, by rw [hwl]; exact b4,
    by rw [hwl]; exact b5⟩

/-- **`entLess` compares the entries of a block by their values** -/
theorem lessB {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} (hH : GoodHist (s := s) H V)
    (es : List (Entry (Fin G.n) (WLab G s))) (hnd : (es.map (·.id)).Nodup) :
    LessSpec realOps entLess (KRB H V es) (fun i => i ∈ es.map (·.id)) (valOf es) 23 entLessW
      entLessV :=
  entLess_spec hH (valOf es) (fun st hK i hi => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
      obtain ⟨⟨_, m, p, hA, hR, hv⟩, hB⟩ := hK.1 e he
      exact ⟨hB, m, p, hA, hR, by rw [valOf_of_mem hnd he, hv]⟩)
    krb_frame (fun _ h => h.2)

end Inst

/-! ## The split step: invariant and frames -/

section Spec

open Frontier.CHD.DIns Frontier.CHD.DB Frontier.CHD.DL Frontier.CHD.MLab Frontier.CHD.LabTab
  Frontier.CHD.DList

variable {G : Graph} {s : Fin G.n}

/-- word registers written by a split step -/
def splitWR : List String :=
  ["sp.t", "sp.bid", "sp.c", "sp.med", "sp.nb", "dsp.go", "blk.fresh", "dl.p", "dl.w"] ++
    DList.walkRegs ++ myRegs ++ entLessW ++ linkRegs

/-- word arrays written by a split step -/
def splitWA : List String :=
  ["sel.w", "ent.nxt", "blk.hd", "blk.tl", "blk.cnt", "blk.bot", "blk.h", "blk.v", "blk.e", "blk.r",
   "dsl.stk", "dsl.sz"]

/-- the registers a split step keeps -/
def keepRegs : List String := ["ds.lv", "ds.b", "ds.M", "sp.w0"]

theorem keep_nw {y : String} (hy : y ∈ keepRegs) : y ∉ splitWR := by
  simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl <;>
    simp [splitWR, DList.walkRegs, myRegs, lessRegs, csRegs, selRegs, entLessW, fsX, fsY, LReg.ws,
      linkRegs, DList.buildRegs]

/-- **the state before a split step** (level `lv`, stack base `bse`, work base `w0`) -/
structure SplitPre (q : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (bcap lv bse w0 : ℕ) (L : Live (Fin G.n) (WLab G s)) (D : DStr (Fin G.n) (WLab G s))
    (ext : List (ℕ × Block (Fin G.n) (WLab G s))) (pSel : ℕ) : Prop where
  drep : DRep q H V bcap lv bse D
  recs : RecsOK q H V (recsOf q bse D.blocks ++ ext)
  live : LiveRep q H V L
  barr : BlkArrs q bcap
  fresh : ∀ p ∈ recsOf q bse D.blocks ++ ext, p.1 < q.w "blk.fresh"
  lv : q.w "ds.lv" = lv
  b : q.w "ds.b" = bse
  M : q.w "ds.M" = D.M
  w0 : q.w "sp.w0" = w0
  procs : q.procs[pSel]? = some (selBody entLess pSel)
  inb : ∀ i, i < q.wlen "ent.nxt" → entA.InB q i
  key : ∀ i, i < q.wlen "ent.nxt" → i < q.wlen "ent.key" ∧ q.wa "ent.key" i < q.wlen "live"
  nxc : q.wlen "ent.nxt" < q.cap
  bc : bcap < q.cap
  stc : q.wlen "dsl.stk" < q.cap
  swc : q.wlen "sel.w" + 1 < q.cap
  Mc : 2 * D.M + 1 < q.cap
  c300 : 300 < q.cap

/-- `SplitPre` survives steps that write only `sel.w` and registers outside `keepRegs` /
`blk.fresh` -/
theorem SplitPre.of_unch' {q r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap lv bse w0 pSel : ℕ} {L : Live (Fin G.n) (WLab G s)} {D : DStr (Fin G.n) (WLab G s)}
    {ext : List (ℕ × Block (Fin G.n) (WLab G s))} {W VR : List String}
    (h : SplitPre q H V bcap lv bse w0 L D ext pSel) (hu : Unchanged q r ["sel.w"] [] W VR)
    (hW : ∀ y ∈ keepRegs, y ∉ W) (hfr : r.w "blk.fresh" = q.w "blk.fresh")
    (hwl : r.wlen "sel.w" = q.wlen "sel.w") :
    SplitPre r H V bcap lv bse w0 L D ext pSel := by
  have hwa : ∀ a, a ≠ "sel.w" → r.wa a = q.wa a := fun a ha => (hu.warr a (by simpa using ha)).1
  have hwl' : r.wlen = q.wlen := by
    funext a
    by_cases ha : a = "sel.w"
    · subst ha; exact hwl
    · exact (hu.warr a (by simpa using ha)).2
  have hva : r.va = q.va := funext fun a => (hu.varr a (by simp)).1
  have hvl : r.vlen = q.vlen := funext fun a => (hu.varr a (by simp)).2
  have hreg : ∀ y ∈ keepRegs, r.w y = q.w y := fun y hy => hu.wreg y (hW y hy)
  have hrecs : recsOf r bse D.blocks = recsOf q bse D.blocks :=
    recsOf_congr bse D.blocks (fun x _ => by rw [hwa _ (by simp)])
  have hES : EntSame q r := ⟨hwa _ (by simp), by rw [hva], hwa _ (by simp), hwa _ (by simp),
    hwa _ (by simp), hwa _ (by simp), hwa _ (by simp)⟩
  refine ⟨h.drep.of_unchanged hu (by simp [dW]) (by simp), ?_, liveRep_same h.live hES
    (by rw [hwl']), blkArrs_same h.barr hwl' hvl, ?_, by rw [hreg _ (by simp [keepRegs])]; exact h.lv,
    by rw [hreg _ (by simp [keepRegs])]; exact h.b, by rw [hreg _ (by simp [keepRegs])]; exact h.M,
    by rw [hreg _ (by simp [keepRegs])]; exact h.w0, by rw [hu.procs]; exact h.procs, fun i hi => ?_,
    fun i hi => ?_, by rw [hwl', hu.cap]; exact h.nxc, by rw [hu.cap]; exact h.bc,
    by rw [hwl', hu.cap]; exact h.stc, by rw [hwl', hu.cap]; exact h.swc, by rw [hu.cap]; exact h.Mc,
    by rw [hu.cap]; exact h.c300⟩
  · rw [hrecs]
    exact recsOK_of_arrays h.recs (fun a ha => hwa a (by intro e; subst e; simp [bArrs] at ha))
      (by rw [hva]) (by rw [hva]) (by rw [hwl'])
  · rw [hrecs, hfr]; exact h.fresh
  · rw [hwl'] at hi
    obtain ⟨b1, b2, b3, b4, b5⟩ := h.inb i hi
    exact ⟨by rw [hvl]; exact b1, by rw [hwl']; exact b2, by rw [hwl']; exact b3, by rw [hwl']; exact b4,
      by rw [hwl']; exact b5⟩
  · rw [hwl'] at hi ⊢
    rw [hwa _ (by simp)]
    exact h.key i hi

/-- `SplitPre` survives `sel.w`/register steps; the work base may change (register `sp.w0`) -/
theorem SplitPre.transfer {q r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap lv bse w0 w0' pSel : ℕ} {L : Live (Fin G.n) (WLab G s)} {D : DStr (Fin G.n) (WLab G s)}
    {ext : List (ℕ × Block (Fin G.n) (WLab G s))} {W VR : List String}
    (h : SplitPre q H V bcap lv bse w0 L D ext pSel) (hu : Unchanged q r ["sel.w"] [] W VR)
    (hW : ∀ y ∈ ["ds.lv", "ds.b", "ds.M"], y ∉ W) (hfr : r.w "blk.fresh" = q.w "blk.fresh")
    (hw0 : r.w "sp.w0" = w0') (hwl : r.wlen "sel.w" = q.wlen "sel.w") :
    SplitPre r H V bcap lv bse w0' L D ext pSel := by
  have hwa : ∀ a, a ≠ "sel.w" → r.wa a = q.wa a := fun a ha => (hu.warr a (by simpa using ha)).1
  have hwl' : r.wlen = q.wlen := by
    funext a
    by_cases ha : a = "sel.w"
    · subst ha; exact hwl
    · exact (hu.warr a (by simpa using ha)).2
  have hva : r.va = q.va := funext fun a => (hu.varr a (by simp)).1
  have hvl : r.vlen = q.vlen := funext fun a => (hu.varr a (by simp)).2
  have hreg : ∀ y ∈ ["ds.lv", "ds.b", "ds.M"], r.w y = q.w y := fun y hy => hu.wreg y (hW y hy)
  have hrecs : recsOf r bse D.blocks = recsOf q bse D.blocks :=
    recsOf_congr bse D.blocks (fun x _ => by rw [hwa _ (by simp)])
  have hES : EntSame q r := ⟨hwa _ (by simp), by rw [hva], hwa _ (by simp), hwa _ (by simp),
    hwa _ (by simp), hwa _ (by simp), hwa _ (by simp)⟩
  refine ⟨h.drep.of_unchanged hu (by simp [dW]) (by simp), ?_, liveRep_same h.live hES
    (by rw [hwl']), blkArrs_same h.barr hwl' hvl, ?_, by rw [hreg _ (by simp)]; exact h.lv,
    by rw [hreg _ (by simp)]; exact h.b, by rw [hreg _ (by simp)]; exact h.M,
    hw0, by rw [hu.procs]; exact h.procs, fun i hi => ?_,
    fun i hi => ?_, by rw [hwl', hu.cap]; exact h.nxc, by rw [hu.cap]; exact h.bc,
    by rw [hwl', hu.cap]; exact h.stc, by rw [hwl', hu.cap]; exact h.swc, by rw [hu.cap]; exact h.Mc,
    by rw [hu.cap]; exact h.c300⟩
  · rw [hrecs]
    exact recsOK_of_arrays h.recs (fun a ha => hwa a (by intro e; subst e; simp [bArrs] at ha))
      (by rw [hva]) (by rw [hva]) (by rw [hwl'])
  · rw [hrecs, hfr]; exact h.fresh
  · rw [hwl'] at hi
    obtain ⟨b1, b2, b3, b4, b5⟩ := h.inb i hi
    exact ⟨by rw [hvl]; exact b1, by rw [hwl']; exact b2, by rw [hwl']; exact b3, by rw [hwl']; exact b4,
      by rw [hwl']; exact b5⟩
  · rw [hwl'] at hi ⊢
    rw [hwa _ (by simp)]
    exact h.key i hi

theorem SplitPre.of_unch {q r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap lv bse w0 pSel : ℕ} {L : Live (Fin G.n) (WLab G s)} {D : DStr (Fin G.n) (WLab G s)}
    {ext : List (ℕ × Block (Fin G.n) (WLab G s))} {W VR : List String}
    (h : SplitPre q H V bcap lv bse w0 L D ext pSel) (hu : Unchanged q r ["sel.w"] [] W VR)
    (hW : ∀ y ∈ "blk.fresh" :: keepRegs, y ∉ W) (hwl : r.wlen "sel.w" = q.wlen "sel.w") :
    SplitPre r H V bcap lv bse w0 L D ext pSel :=
  h.of_unch' hu (fun y hy => hW y (List.mem_cons_of_mem _ hy)) (hu.wreg _ (hW _ (by simp))) hwl

theorem SplitPre.charge {q : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap lv bse w0 pSel : ℕ} {L : Live (Fin G.n) (WLab G s)} {D : DStr (Fin G.n) (WLab G s)}
    {ext : List (ℕ × Block (Fin G.n) (WLab G s))} (h : SplitPre q H V bcap lv bse w0 L D ext pSel)
    (k : ℕ) : SplitPre (q.charge k) H V bcap lv bse w0 L D ext pSel :=
  h.of_unch' ((unch_charge' k).mpr (Unchanged.refl q ["sel.w"] [] [] [])) (fun _ _ => List.not_mem_nil)
    rfl rfl

theorem tlWord_seg (st : State ℝ≥0) (lo n : ℕ) (hn : 1 ≤ n) :
    tlWord (seg st lo n) = st.wa "sel.w" (lo + n - 1) + 1 := by
  have h : (seg st lo n).getLast? = some (st.wa "sel.w" (lo + n - 1)) := by
    rw [List.getLast?_eq_getElem?, length_seg]
    have h1 : n - 1 < n := by omega
    simp only [seg, List.getElem?_map, List.getElem?_range h1, Option.map_some]
    congr 2; omega
  unfold tlWord; rw [h]

theorem blkArrs_mono {st : State ℝ≥0} {bcap bcap' : ℕ} (h : BlkArrs st bcap) (hle : bcap' ≤ bcap) :
    BlkArrs st bcap' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- the ids of the top block are distinct -/
theorem top_nodup {q : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {bse : ℕ}
    {b : Block (Fin G.n) (WLab G s)} {bs : List (Block (Fin G.n) (WLab G s))}
    {ext : List (ℕ × Block (Fin G.n) (WLab G s))} (hR : RecsOK q H V (recsOf q bse (b :: bs) ++ ext)) :
    (b.ents.map (·.id)).Nodup := by
  have h := hR.2.2
  rw [recsOf_cons, List.cons_append, List.map_cons, entIds_cons] at h
  exact (List.nodup_append.mp h).1

/-- the top block's record is represented -/
theorem top_blkRep {q : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap lv bse M : ℕ} {Bd : WLab G s} {b : Block (Fin G.n) (WLab G s)}
    {bs : List (Block (Fin G.n) (WLab G s))} (hD : DRep q H V bcap lv bse ⟨M, Bd, b :: bs⟩) :
    BlkRep q H V (q.wa "dsl.stk" (bse + bs.length)) b ∧ q.wa "dsl.stk" (bse + bs.length) < bcap := by
  have h1 := hD.blk 0 (by simp)
  have h2 := hD.bidb 0 (by simp)
  simp only [stkId, List.length_cons, Nat.add_sub_cancel, Nat.sub_zero, List.getElem_cons_zero] at h1 h2
  exact ⟨h1, h2⟩

/-- after a split -/
def SplitMade (q r : State ℝ≥0) (w0 lv t : ℕ) : Prop :=
  r.w "dsp.go" = 1 ∧ Unchanged q r splitWA ["blk.len"] splitWR entLessV ∧ r.wlen = q.wlen ∧
    r.vlen = q.vlen ∧ (∀ x, x < w0 → r.wa "sel.w" x = q.wa "sel.w" x) ∧
    r.w "blk.fresh" = q.w "blk.fresh" + 1 ∧ (∀ x, x < t → r.wa "dsl.stk" x = q.wa "dsl.stk" x) ∧
    (∀ l, l ≠ lv → r.wa "dsl.sz" l = q.wa "dsl.sz" l)

set_option maxHeartbeats 4000000 in
theorem split_tail (q6 : State ℝ≥0) {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap lv bse w0 M pSel : ℕ} {Bd : WLab G s} {L : Live (Fin G.n) (WLab G s)}
    {b : Block (Fin G.n) (WLab G s)} {bs : List (Block (Fin G.n) (WLab G s))}
    {ext : List (ℕ × Block (Fin G.n) (WLab G s))}
    (hP : SplitPre q6 H V bcap lv bse w0 L ⟨M, Bd, b :: bs⟩ ext pSel)
    (hfb : q6.w "blk.fresh" < bcap) (hstk : bse + bs.length + 2 ≤ q6.wlen "dsl.stk")
    {c a b' med : ℕ} (hc : q6.w "sp.c" = c) (ha : q6.w "sel.a" = a) (hb : q6.w "sel.b" = b')
    (hmed : q6.w "sp.med" = med) (hbid : q6.w "sp.bid" = q6.wa "dsl.stk" (bse + bs.length))
    (ht : q6.w "sp.t" = bse + bs.length)
    (hlo : seg q6 (w0 + c) a = (loOf L b).map (·.id))
    (hhi : seg q6 (w0 + c + a) b' = (hiOf L b).map (·.id))
    (hmv : valOf b.ents med = medOf L b) (hmm : med ∈ b.ents.map (·.id))
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b') (hsl : w0 + c + a + b' ≤ q6.wlen "sel.w") :
    Runs realOps (seq spLink (seq spRecs (wset "dsp.go" (lit 1)))) q6 (fun r =>
      SplitMade q6 r w0 lv (bse + bs.length) ∧
      SplitPre r H V bcap lv bse w0 L
        ⟨M, Bd, ⟨b.sep, loOf L b⟩ :: ⟨((medOf L b : WLab G s) : WithBot (WLab G s)), hiOf L b⟩ :: bs⟩
        ext pSel ∧
      r.cost ≤ q6.cost + 35 + 5 * (a + b')) := by
  set bid := q6.wa "dsl.stk" (bse + bs.length) with hbidd
  set nb := q6.w "blk.fresh" with hnbd
  set t := bse + bs.length with htd
  set loI := (loOf L b).map (·.id) with hloI
  set hiI := (hiOf L b).map (·.id) with hhiI
  obtain ⟨hB0, hbidb⟩ := top_blkRep hP.drep
  have hnd := top_nodup hP.recs
  have hbnb : bid < nb := hP.fresh (bid, b) (by rw [recsOf_cons]; exact List.mem_cons_self)
  have hsub : (loI ++ hiI).Subperm (b.ents.map (·.id)) := lohi_subperm L b
  have hndlh : (loI ++ hiI).Nodup := subperm_nodup hsub hnd
  have hltb : ∀ x ∈ b.ents.map (·.id), x < q6.wlen "ent.nxt" := hB0.2.1.lt_len
  have hlt : ∀ x ∈ loI ++ hiI, x < q6.wlen "ent.nxt" := fun x hx => hltb x (hsub.subset hx)
  have hnxc := hP.nxc
  have hswc := hP.swc
  have hstc := hP.stc
  have hbc := hP.bc
  apply runs_seq
  refine (spLink_run (ops := realOps) q6 (w0 := w0) (c := c) (a := a) (b := b') (lo := loI) (hi := hiI)
    hP.w0 hc ha hb hlo hhi hndlh hlt (fun x hx => by have := hlt x hx; omega) hsl (by omega)).mono
    (fun q7 ⟨hL7lo, hL7hi, hnx7, hu7, hnl7, hc7⟩ => ?_)
  have hw7 : ∀ y, y ∉ linkRegs → q7.w y = q6.w y := fun y hy => hu7.wreg y hy
  have hwa7 : ∀ c', c' ≠ "ent.nxt" → q7.wa c' = q6.wa c' := fun c' h => (hu7.warr c' (by simpa using h)).1
  have hwl7 : q7.wlen = q6.wlen := by
    funext c'
    by_cases h : c' = "ent.nxt"
    · subst h; exact hnl7
    · exact (hu7.warr c' (by simpa using h)).2
  have hva7 : q7.va = q6.va := funext fun c' => (hu7.varr c' (by simp)).1
  have hvl7 : q7.vlen = q6.vlen := funext fun c' => (hu7.varr c' (by simp)).2
  have hcap7 : q7.cap = q6.cap := hu7.cap
  have hlr : ∀ y ∈ ["sp.bid", "sp.w0", "sp.c", "sel.a", "sel.b", "blk.fresh", "sp.med", "sp.t", "ds.lv",
      "ds.b", "ds.M"], y ∉ linkRegs := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [linkRegs, DList.buildRegs]
  have hsw7 : q7.wa "sel.w" = q6.wa "sel.w" := hwa7 _ (by simp)
  have hk6 : q6.wa "dsl.sz" lv = bs.length + 1 := by simpa using hP.drep.sz
  have hmlt : med < q6.wlen "ent.nxt" := hltb med hmm
  have hbe7 : entA.InB q7 med := by
    obtain ⟨e1, e2, e3, e4, e5⟩ := hP.inb med hmlt
    exact ⟨by rw [hvl7]; exact e1, by rw [hwl7]; exact e2, by rw [hwl7]; exact e3, by rw [hwl7]; exact e4,
      by rw [hwl7]; exact e5⟩
  have htl1 : q7.wa "sel.w" (w0 + c + a - 1) + 1 < q7.cap := by
    have hx : q6.wa "sel.w" (w0 + c + a - 1) ∈ loI := by
      rw [← hlo]; simp only [seg, List.mem_map, List.mem_range]; exact ⟨a - 1, by omega, by congr 1; omega⟩
    have := hlt _ (List.mem_append_left _ hx)
    rw [hsw7, hcap7]; omega
  have htl2 : q7.wa "sel.w" (w0 + c + a + b' - 1) + 1 < q7.cap := by
    have hx : q6.wa "sel.w" (w0 + c + a + b' - 1) ∈ hiI := by
      rw [← hhi]; simp only [seg, List.mem_map, List.mem_range]; exact ⟨b' - 1, by omega, by congr 1; omega⟩
    have := hlt _ (List.mem_append_right _ hx)
    rw [hsw7, hcap7]; omega
  refine (spRecsGo_run q7 (bid := bid) (hlo := q7.w "sp.hlo") (w0 := w0) (c := c) (a := a) (nb := nb)
    (hhi := q7.w "sp.hhi") (b := b') (med := med) (t := t) (lv := lv) (k := bs.length + 1)
    (by rw [hw7 _ (hlr _ (by simp))]; exact hbid) rfl (by rw [hw7 _ (hlr _ (by simp))]; exact hP.w0)
    (by rw [hw7 _ (hlr _ (by simp))]; exact hc) (by rw [hw7 _ (hlr _ (by simp))]; exact ha)
    (by rw [hw7 _ (hlr _ (by simp))]; exact hb) (by rw [hw7 _ (hlr _ (by simp))]) rfl
    (by rw [hw7 _ (hlr _ (by simp))]; exact hmed) (by rw [hw7 _ (hlr _ (by simp))]; exact ht)
    (by rw [hw7 _ (hlr _ (by simp))]; exact hP.lv) (by rw [hwa7 _ (by simp)]; exact hk6) ha1 hb1
    (blkArrs_mono (blkArrs_same hP.barr hwl7 hvl7) (by omega)) (by rw [hwl7]; omega)
    (by rw [hcap7]; omega) (by rw [hcap7]; omega) htl1 htl2 hbe7 (by rw [hwl7]; omega)
    (by rw [hwl7]; exact hP.drep.szb) (by rw [hcap7]; omega) (by rw [hcap7]; omega)).mono
    (fun r hr => ?_)
  subst hr
  set hlo7 := q7.w "sp.hlo" with hhlo7
  set hhi7 := q7.w "sp.hhi" with hhhi7
  set tl1 := q7.wa "sel.w" (w0 + c + a - 1) + 1 with htl1d
  set tl2 := q7.wa "sel.w" (w0 + c + a + b' - 1) + 1 with htl2d
  obtain ⟨hFwl, hFvl, hFcap, hFpr, hFc⟩ := recsSt_len q7 bid hlo7 tl1 a nb hhi7 tl2 b' med t lv (bs.length + 1)
  obtain ⟨hFnb, hFfr, hFgo⟩ := recsSt_regs q7 bid hlo7 tl1 a nb hhi7 tl2 b' med t lv (bs.length + 1)
  set F := recsSt q7 bid hlo7 tl1 a nb hhi7 tl2 b' med t lv (bs.length + 1) with hF
  have hFhd := recsSt_hd q7 bid hlo7 tl1 a nb hhi7 tl2 b' med t lv (bs.length + 1)
  have hFtl := recsSt_tl q7 bid hlo7 tl1 a nb hhi7 tl2 b' med t lv (bs.length + 1)
  have hFcnt := recsSt_cnt q7 bid hlo7 tl1 a nb hhi7 tl2 b' med t lv (bs.length + 1)
  have hFbot := recsSt_bot q7 bid hlo7 tl1 a nb hhi7 tl2 b' med t lv (bs.length + 1)
  have hFstk := recsSt_stk q7 bid hlo7 tl1 a nb hhi7 tl2 b' med t lv (bs.length + 1)
  have hFsz := recsSt_sz q7 bid hlo7 tl1 a nb hhi7 tl2 b' med t lv (bs.length + 1)
  have hFA := recsSt_blkA q7 bid hlo7 tl1 a nb hhi7 tl2 b' med t lv (bs.length + 1)
  have hFwa := recsSt_wa q7 bid hlo7 tl1 a nb hhi7 tl2 b' med t lv (bs.length + 1)
  have hFva := recsSt_va q7 bid hlo7 tl1 a nb hhi7 tl2 b' med t lv (bs.length + 1)
  have hFw := recsSt_w q7 bid hlo7 tl1 a nb hhi7 tl2 b' med t lv (bs.length + 1)
  have hFv := recsSt_v q7 bid hlo7 tl1 a nb hhi7 tl2 b' med t lv (bs.length + 1)
  rw [← hF] at hFhd hFtl hFcnt hFbot hFstk hFsz hFA hFwa hFva hFw hFv
  have hwl' : F.wlen = q6.wlen := hFwl.trans hwl7
  have hvl' : F.vlen = q6.vlen := hFvl.trans hvl7
  have hnbid : bid ≠ nb := by omega
  have hwa' : ∀ c', c' ∉ ["blk.hd", "blk.tl", "blk.cnt", "blk.bot", "blk.h", "blk.v", "blk.e", "blk.r",
      "dsl.stk", "dsl.sz", "ent.nxt"] → F.wa c' = q6.wa c' := by
    intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc'
    rw [hFwa c' (by simp; tauto), hwa7 c' hc'.2.2.2.2.2.2.2.2.2.2]
  have hES : EntSame q6 F := ⟨hwa' _ (by simp), by rw [hFva _ (by simp), hva7], hwa' _ (by simp),
    hwa' _ (by simp), hwa' _ (by simp), hwa' _ (by simp), hwa' _ (by simp)⟩
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmm
  obtain ⟨_, m, pm, hAm, hRm, hvm⟩ := hB0.2.2.1 e he
  have hmedv : medOf L b = e.val := by rw [← hmv, valOf_of_mem hnd he]
  have hlen_lo : (loOf L b).length = a := by
    have := congrArg List.length hlo; simp only [length_seg, hloI, List.length_map] at this; omega
  have hlen_hi : (hiOf L b).length = b' := by
    have := congrArg List.length hhi; simp only [length_seg, hhiI, List.length_map] at this; omega
  have hnxF : F.wa "ent.nxt" = q7.wa "ent.nxt" := hFwa _ (by simp)
  obtain ⟨hRn, hDn, hfn⟩ := split_reps (q := q6) (r := F) (nb := nb) (bid := bid) (lo := loOf L b)
    (hi := hiOf L b) (sep' := ((medOf L b : WLab G s) : WithBot (WLab G s))) (m := m) (pm := pm)
    hP.drep hP.recs hP.fresh hfb rfl (by rw [List.map_append]; exact hsub)
    (fun x hx => lohi_mem (List.mem_append.mp hx)) (by rw [hmedv, hvm]) hRm hES
    (fun y hy => by rw [hnxF, hnx7 y (by rw [← List.map_append]; exact hy)]) hwl'
    (fun x h1 h2 => by rw [hFhd, if_neg h2, if_neg h1, hwa7 _ (by simp)])
    (fun x h1 h2 => by rw [hFtl, if_neg h2, if_neg h1, hwa7 _ (by simp)])
    (fun x h1 h2 => by rw [hFcnt, if_neg h2, if_neg h1, hwa7 _ (by simp)])
    (fun x h1 => by rw [hFbot, if_neg h1, hwa7 _ (by simp)])
    (fun x h1 y hy => by
      obtain ⟨y1, y2, y3, y4, y5⟩ := hy
      obtain ⟨f1, f2, f3, f4, f5⟩ := hFA x
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [blkA] at y1 ⊢; rw [f1, if_neg h1, hva7]; exact y1
      · simp only [blkA] at y2 ⊢; rw [f2, if_neg h1, hwa7 _ (by simp)]; exact y2
      · simp only [blkA] at y3 ⊢; rw [f3, if_neg h1, hwa7 _ (by simp)]; exact y3
      · simp only [blkA] at y4 ⊢; rw [f4, if_neg h1, hwa7 _ (by simp)]; exact y4
      · simp only [blkA] at y5 ⊢; rw [f5, if_neg h1, hwa7 _ (by simp)]; exact y5)
    (by
      rw [hFhd, if_neg hnbid, if_pos rfl]
      exact hL7lo.frame (by rw [hFwl]) (fun i _ => by rw [hnxF]))
    (by
      rw [hFhd, if_pos rfl]
      exact hL7hi.frame (by rw [hFwl]) (fun i _ => by rw [hnxF]))
    (by rw [hFcnt, if_neg hnbid, if_pos rfl, hlen_lo]) (by rw [hFcnt, if_pos rfl, hlen_hi])
    (by
      rw [hFtl, if_neg hnbid, if_pos rfl, htl1d, hsw7, ← hloI, ← hlo, tlWord_seg _ _ _ ha1])
    (by
      rw [hFtl, if_pos rfl, htl2d, hsw7, ← hhiI, ← hhi, tlWord_seg _ _ _ hb1])
    (by rw [hFbot, if_pos rfl])
    (by
      obtain ⟨a1, a2, a3, a4, a5⟩ := hAm
      obtain ⟨f1, f2, f3, f4, f5⟩ := hFA nb
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [blkA]; rw [f1, if_pos rfl, hva7]; exact a1
      · simp only [blkA]; rw [f2, if_pos rfl, hwa7 _ (by simp)]; exact a2
      · simp only [blkA]; rw [f3, if_pos rfl, hwa7 _ (by simp)]; exact a3
      · simp only [blkA]; rw [f4, if_pos rfl, hwa7 _ (by simp)]; exact a4
      · simp only [blkA]; rw [f5, if_pos rfl, hwa7 _ (by simp)]; exact a5)
    (fun x hx => by rw [hFstk, if_neg (by omega), if_neg (by omega), hwa7 _ (by simp)])
    (by rw [hFstk, if_neg (by omega), if_pos rfl])
    (by rw [hFstk, if_pos rfl])
    (by rw [hFsz, if_pos rfl]) hstk
  have hkeep : ∀ y ∈ ["ds.lv", "ds.b", "ds.M", "sp.w0"], F.w y = q6.w y := by
    intro y hy
    rw [hFw y (by simp at hy ⊢; rcases hy with rfl | rfl | rfl | rfl <;> simp),
      hw7 y (by simp at hy; rcases hy with rfl | rfl | rfl | rfl <;> simp [linkRegs, DList.buildRegs])]
  refine ⟨⟨hFgo, ?_, hwl', hvl', fun x _ => by rw [hFwa _ (by simp), hsw7], hFfr, fun x hx => ?_,
    fun l hl => ?_⟩, ⟨hDn, hRn, liveRep_same hP.live hES (by rw [hwl']), blkArrs_same hP.barr hwl' hvl',
    by rw [hFfr]; exact hfn, by rw [hkeep _ (by simp)]; exact hP.lv, by rw [hkeep _ (by simp)]; exact hP.b,
    by rw [hkeep _ (by simp)]; exact hP.M, by rw [hkeep _ (by simp)]; exact hP.w0,
    by rw [hFpr, hu7.procs]; exact hP.procs, fun i hi => ?_, fun i hi => ?_,
    by rw [hwl', hFcap, hcap7]; exact hP.nxc, by rw [hFcap, hcap7]; exact hP.bc,
    by rw [hwl', hFcap, hcap7]; exact hP.stc, by rw [hwl', hFcap, hcap7]; exact hP.swc,
    by rw [hFcap, hcap7]; exact hP.Mc, by rw [hFcap, hcap7]; exact hP.c300⟩, ?_⟩
  · have u1 : Unchanged q6 q7 splitWA ["blk.len"] splitWR entLessV :=
      hu7.mono (by simp [splitWA]) (by simp) (fun y hy => by simp [splitWR]; tauto) (by simp)
    have u2 : Unchanged q7 F splitWA ["blk.len"] splitWR entLessV := by
      refine ⟨fun c' hc' => ⟨hFwa c' ?_, by rw [hFwl]⟩, fun c' hc' => ⟨hFva c' (by simpa using hc'),
        by rw [hFvl]⟩, fun y hy => hFw y ?_, fun y hy => hFv y ?_, hFcap, hFpr⟩
      · intro h; apply hc'; simp only [splitWA]; simp at h ⊢; tauto
      · intro h; apply hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [splitWR, DList.walkRegs, myRegs, lessRegs, csRegs, selRegs, entLessW, fsX, fsY, LReg.ws,
            linkRegs, DList.buildRegs]
      · intro h; apply hy; rw [h]; simp [entLessV, fsX]
    exact u1.trans u2
  · rw [hFstk, if_neg (by omega), if_neg (by omega), hwa7 _ (by simp)]
  · rw [hFsz, if_neg hl, hwa7 _ (by simp)]
  · rw [hwl'] at hi
    obtain ⟨b1, b2, b3, b4, b5⟩ := hP.inb i hi
    exact ⟨by rw [hvl']; exact b1, by rw [hwl']; exact b2, by rw [hwl']; exact b3, by rw [hwl']; exact b4,
      by rw [hwl']; exact b5⟩
  · rw [hwl'] at hi ⊢
    rw [hwa' _ (by simp)]
    exact hP.key i hi
  · rw [hFc]
    have : q7.cost ≤ q6.cost + 12 + 5 * (a + b') := hc7
    omega

/-- after a split step that does not split: only `sel.w` (above the live copy) and registers -/
def SplitDone (q r : State ℝ≥0) (w0 : ℕ) (ids : List ℕ) (bid t : ℕ) : Prop :=
  r.w "dsp.go" = 0 ∧ Unchanged q r ["sel.w"] [] splitWR entLessV ∧ r.wlen "sel.w" = q.wlen "sel.w" ∧
    DList.Spells r "sel.w" w0 ids ∧ r.w "sp.c" = ids.length ∧ r.w "sp.bid" = bid ∧ r.w "sp.t" = t ∧
    (∀ x, x < w0 → r.wa "sel.w" x = q.wa "sel.w" x) ∧ r.w "blk.fresh" = q.w "blk.fresh"

theorem medRegs_sub : myRegs ++ entLessW ++ ["sp.med"] ⊆ splitWR := by
  intro y hy
  simp only [List.mem_append, List.mem_singleton] at hy
  unfold splitWR
  rcases hy with (h | h) | h
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))
  · exact List.mem_append_left _ (List.mem_append_right _ h)
  · subst h; simp

theorem krb_of_pre {q : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap lv bse w0 M pSel : ℕ} {Bd : WLab G s} {L : Live (Fin G.n) (WLab G s)}
    {b : Block (Fin G.n) (WLab G s)} {bs : List (Block (Fin G.n) (WLab G s))}
    {ext : List (ℕ × Block (Fin G.n) (WLab G s))}
    (hP : SplitPre q H V bcap lv bse w0 L ⟨M, Bd, b :: bs⟩ ext pSel) : KRB H V b.ents q := by
  obtain ⟨hB0, _⟩ := top_blkRep hP.drep
  refine ⟨fun e he => ⟨hB0.2.2.1 e he, hP.inb _ (hB0.2.1.lt_len _ (List.mem_map_of_mem he))⟩, ?_⟩
  have := hP.c300; omega

theorem liveI_sub {L : Live (Fin G.n) (WLab G s)} {b : Block (Fin G.n) (WLab G s)} {x : ℕ}
    (hx : x ∈ (liveOf L b.ents).map (·.id)) : x ∈ b.ents.map (·.id) := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  exact List.mem_map_of_mem (List.mem_of_mem_filter he)

set_option maxHeartbeats 4000000 in
theorem split_mid (hH : GoodHist (s := s) H V) (pSel : ℕ) (q3 : State ℝ≥0)
    {bcap lv bse w0 M : ℕ} {Bd : WLab G s} {L : Live (Fin G.n) (WLab G s)}
    {b : Block (Fin G.n) (WLab G s)} {bs : List (Block (Fin G.n) (WLab G s))}
    {ext : List (ℕ × Block (Fin G.n) (WLab G s))}
    (hP : SplitPre q3 H V bcap lv bse w0 L ⟨M, Bd, b :: bs⟩ ext pSel)
    (hfb : SplitG L M b → q3.w "blk.fresh" < bcap)
    (hstk : SplitG L M b → bse + bs.length + 2 ≤ q3.wlen "dsl.stk")
    (hsw : w0 + 6 * b.ents.length + 60 ≤ q3.wlen "sel.w")
    (hsp : DList.Spells q3 "sel.w" w0 ((liveOf L b.ents).map (·.id)))
    (hc : q3.w "sp.c" = (liveOf L b.ents).length)
    (hbid : q3.w "sp.bid" = q3.wa "dsl.stk" (bse + bs.length)) (ht : q3.w "sp.t" = bse + bs.length)
    (hg : 2 * M + 1 < (liveOf L b.ents).length) :
    Runs realOps (seq (spMed pSel) (seq spHalves (ite (lt (lit 0) (var "sel.a"))
      (seq spLink (seq spRecs (wset "dsp.go" (lit 1)))) (wset "dsp.go" (lit 0))))) q3 (fun r =>
      (SplitG L M b → SplitMade q3 r w0 lv (bse + bs.length) ∧
        SplitPre r H V bcap lv bse w0 L
          ⟨M, Bd, ⟨b.sep, loOf L b⟩ :: ⟨((medOf L b : WLab G s) : WithBot (WLab G s)), hiOf L b⟩ :: bs⟩
          ext pSel ∧
        r.cost ≤ q3.cost + 152 + (Ksel 23 + 71) * (liveOf L b.ents).length) ∧
      (¬ SplitG L M b → SplitDone q3 r w0 ((liveOf L b.ents).map (·.id)) (q3.wa "dsl.stk" (bse + bs.length))
          (bse + bs.length) ∧
        r.cost ≤ q3.cost + 118 + (Ksel 23 + 66) * (liveOf L b.ents).length)) := by
  set c := (liveOf L b.ents).length with hcd
  set liveI := (liveOf L b.ents).map (·.id) with hliveI
  have hnd := top_nodup hP.recs
  have hL := lessB hH b.ents hnd
  have hK3 := krb_of_pre hP
  have hcl : c ≤ b.ents.length := length_liveOf_le L b.ents
  have hseg3 : seg q3 w0 c = liveI := by
    have := seg_of_spells hsp
    rwa [List.length_map] at this
  have hswc := hP.swc
  apply runs_seq
  refine (spMed_run hL krb_frame pSel q3 hK3 hP.w0 hc (by omega)
    (fun x hx => liveI_sub (L := L) (by rw [hseg3] at hx; exact hx)) hP.procs (by omega) (by omega)
    hP.c300).mono (fun q4 ⟨hK4, hmem4, hkth4, hlow4, hwl4, hu4, hc4⟩ => ?_)
  set med := q4.w "sp.med" with hmedd
  rw [hseg3] at hmem4 hkth4
  have hmv : valOf b.ents med = medOf L b := medOf_eq_of_kth L hnd hkth4 (by omega)
  have hw4 : ∀ y, y ∉ myRegs ++ entLessW ++ ["sp.med"] → q4.w y = q3.w y := fun y hy => hu4.wreg y hy
  have hnot : ∀ y ∈ ["sp.w0", "sp.c", "sp.bid", "sp.t", "blk.fresh", "ds.lv", "ds.b", "ds.M"],
      y ∉ myRegs ++ entLessW ++ ["sp.med"] := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [myRegs, lessRegs, csRegs, selRegs, entLessW, fsX, fsY, LReg.ws]
  have hseg4 : seg q4 w0 c = liveI := by
    rw [← hseg3]; apply seg_congr; intro x _ h2; exact hlow4 x h2
  apply runs_seq
  refine (spHalves_run hL q4 (w0 := w0) (c := c) (med := med) hK4 (by rw [hw4 _ (hnot _ (by simp))]; exact hP.w0)
    (by rw [hw4 _ (hnot _ (by simp))]; exact hc) rfl
    (fun x hx => liveI_sub (L := L) (by rw [hseg4] at hx; exact hx)) (liveI_sub (L := L) hmem4)
    (by rw [hwl4]; omega) (by rw [hu4.cap]; omega)).mono
    (fun q5 ⟨hK5, hlo5, hhi5, hsum5, hlow5, hwl5, hu5, hc5⟩ => ?_)
  rw [hseg4, lo_ids L hnd hmv] at hlo5
  rw [hseg4, hi_ids L hnd hmv] at hhi5
  have hw5 : ∀ y, y ∉ myRegs ++ entLessW → q5.w y = q4.w y := fun y hy => hu5.wreg y hy
  have hnot5 : ∀ y ∈ ["sp.w0", "sp.c", "sp.bid", "sp.t", "blk.fresh", "ds.lv", "ds.b", "ds.M", "sp.med"],
      y ∉ myRegs ++ entLessW := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [myRegs, lessRegs, csRegs, selRegs, entLessW, fsX, fsY, LReg.ws]
  have hreg5 : ∀ y ∈ ["sp.w0", "sp.c", "sp.bid", "sp.t", "blk.fresh", "ds.lv", "ds.b", "ds.M"],
      q5.w y = q3.w y := fun y hy => by
    rw [hw5 y (hnot5 y (by simp at hy ⊢; tauto)), hw4 y (hnot y hy)]
  have hmed5 : q5.w "sp.med" = med := hw5 _ (hnot5 _ (by simp))
  set a := q5.w "sel.a" with had
  set b' := q5.w "sel.b" with hbd
  have hla : (loOf L b).length = a := by
    have := congrArg List.length hlo5; simp only [length_seg, List.length_map] at this; omega
  have hlb : (hiOf L b).length = b' := by
    have := congrArg List.length hhi5; simp only [length_seg, List.length_map] at this; omega
  -- frame q3 → q5
  have u35 : Unchanged q3 q5 ["sel.w"] [] (myRegs ++ entLessW ++ ["sp.med"]) entLessV :=
    hu4.trans (hu5.mono (List.Subset.refl _) (List.Subset.refl _)
      (fun y hy => List.mem_append_left _ hy) (List.Subset.refl _))
  have hwl35 : q5.wlen "sel.w" = q3.wlen "sel.w" := by rw [hwl5, hwl4]
  have hlow35 : ∀ x, x < w0 + c → q5.wa "sel.w" x = q3.wa "sel.w" x := fun x hx => by
    rw [hlow5 x hx, hlow4 x hx]
  have hcap5 : q5.cap = q3.cap := u35.cap
  have hsg : SplitG L M b ↔ 0 < a := by
    unfold SplitG
    constructor
    · rintro ⟨_, h2⟩
      rw [← hla]; exact List.length_pos_of_ne_nil h2
    · intro h
      exact ⟨hg, fun h' => by rw [h'] at hla; simp at hla; omega⟩
  have hg2 : evalW q5 (lt (lit 0) (var "sel.a")) = some (if 0 < a then 1 else 0) :=
    evalW_lt_of (evalW_lit_of (by rw [hcap5]; have := hP.c300; omega)) rfl
      (by rw [hcap5]; have := hP.c300; omega)
  have hwl36 : q5.wlen = q3.wlen := by
    funext x
    by_cases hx : x = "sel.w"
    · subst hx; exact hwl35
    · exact (u35.warr x (by simpa using hx)).2
  have hvl36 : q5.vlen = q3.vlen := funext fun x => (u35.varr x (by simp)).2
  by_cases ha0 : 0 < a
  · refine runs_ite_true (x := 1) (by rw [hg2, if_pos ha0]) one_ne_zero ?_
    have hP6 : SplitPre (q5.charge 1) H V bcap lv bse w0 L ⟨M, Bd, b :: bs⟩ ext pSel :=
      hP.of_unch ((unch_charge' 1).mpr u35) (fun y hy => by
        simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl <;>
          simp [myRegs, lessRegs, csRegs, selRegs, entLessW, fsX, fsY, LReg.ws]) (by simpa using hwl35)
    have hb1 : 1 ≤ b' := by
      have hmh : med ∈ (hiOf L b).map (·.id) := by
        rw [← hi_ids L hnd hmv]; exact List.mem_filter.mpr ⟨hmem4, by simp⟩
      have := List.length_pos_of_mem hmh
      simp only [List.length_map] at this; omega
    have hbid6 : (q5.charge 1).w "sp.bid" = (q5.charge 1).wa "dsl.stk" (bse + bs.length) := by
      simp only [State.charge_w, State.charge_wa]
      rw [hreg5 "sp.bid" (by simp), (u35.warr _ (by simp)).1]
      exact hbid
    refine (split_tail (q5.charge 1) hP6 (by simpa [hreg5 "blk.fresh" (by simp)] using hfb (hsg.mpr ha0))
      (by simp only [State.charge_wlen]; rw [hwl36]; exact hstk (hsg.mpr ha0)) (c := c) (a := a) (b' := b') (med := med)
      (by simpa [hreg5 "sp.c" (by simp)] using hc) rfl rfl (by simpa using hmed5) hbid6
      (by simpa [hreg5 "sp.t" (by simp)] using ht) (by simpa [seg] using hlo5) (by simpa [seg] using hhi5)
      hmv (liveI_sub (L := L) hmem4) ha0 hb1 (by simp only [State.charge_wlen]; rw [hwl35]; omega)).mono
      (fun r ⟨hM, hPr, hcr⟩ => ⟨fun _ => ⟨?_, hPr, ?_⟩, fun h => absurd (hsg.mpr ha0) h⟩)
    · obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8⟩ := hM
      have u36 : Unchanged q3 (q5.charge 1) splitWA ["blk.len"] splitWR entLessV :=
        ((unch_charge' 1).mpr u35).mono (by simp [splitWA]) (by simp) medRegs_sub (List.Subset.refl _)
      refine ⟨m1, u36.trans m2, by rw [m3]; simpa using hwl36, by rw [m4]; simpa using hvl36,
        fun x hx => ?_, by rw [m6]; simp only [State.charge_w]; rw [hreg5 "blk.fresh" (by simp)], fun x hx => ?_,
        fun l hl => ?_⟩
      · rw [m5 x hx]; simp only [State.charge_wa]; exact hlow35 x (by omega)
      · rw [m7 x hx]; simp only [State.charge_wa]; rw [(u35.warr "dsl.stk" (by simp)).1]
      · rw [m8 l hl]; simp only [State.charge_wa]; rw [(u35.warr "dsl.sz" (by simp)).1]
    · have : a + b' = c := hsum5
      have hK : Ksel 23 = 11300 := by simp [Ksel]
      rw [hK] at hc4 ⊢
      simp only [State.charge_cost] at hcr
      omega
  · have ha00 : a = 0 := by omega
    refine runs_ite_false (by rw [hg2, if_neg ha0]) ?_
    refine runs_wset (a := 0) (by simp [fit_of_lt (show 0 < q5.cap by rw [hcap5]; have := hP.c300; omega)]) ?_
    refine ⟨fun h => absurd (hsg.mp h) ha0, fun _ => ⟨⟨by simp, ?_, by simpa using hwl35, fun i hi => ?_,
      by simp only [State.charge_w, State.setW_w]; rw [if_neg (by decide), hreg5 "sp.c" (by simp), hc, hliveI,
        List.length_map],
      by simp only [State.charge_w, State.setW_w]; rw [if_neg (by decide), hreg5 "sp.bid" (by simp)]; exact hbid,
      by simp only [State.charge_w, State.setW_w]; rw [if_neg (by decide), hreg5 "sp.t" (by simp)]; exact ht,
      fun x hx => by simp only [State.charge_wa, State.setW_wa]; exact hlow35 x (by omega),
      by simp only [State.charge_w, State.setW_w]; rw [if_neg (by decide), hreg5 "blk.fresh" (by simp)]⟩,
      ?_⟩⟩
    · rw [unch_charge', unch_setW' (by simp [splitWR]), unch_charge']
      exact u35.mono (List.Subset.refl _) (List.Subset.refl _) medRegs_sub (List.Subset.refl _)
    · simp only [State.charge_wa, State.setW_wa]
      rw [hlow35 _ (by simp [hliveI] at hi; omega)]
      exact hsp i hi
    · have hK : Ksel 23 = 11300 := by simp [Ksel]
      rw [hK] at hc4 ⊢
      simp only [State.charge_cost, State.setW_cost]
      omega

theorem filter_liveW {q : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {L : Live (Fin G.n) (WLab G s)} (hL : LiveRep q H V L) {es : List (Entry (Fin G.n) (WLab G s))}
    (he : ∀ e ∈ es, EntRep q H V e.id e.key e.val) :
    (es.map (·.id)).filter (DList.liveW q) = (liveOf L es).map (·.id) := by
  rw [List.filter_map]
  unfold liveOf
  congr 1
  apply List.filter_congr
  intro e h
  simp only [Function.comp, decide_eq_decide]
  exact liveW_iff hL (he e h)

/-- cost constant of a split -/
def Ksp : ℕ := 5700
/-- cost constant of a split step that does not split -/
def Knc : ℕ := 11500

theorem frontRegs_sub : ["sp.t", "sp.bid"] ++ (["dl.p", "dl.w", "sp.c"] ++ DList.walkRegs) ⊆ splitWR := by
  intro y hy
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, DList.walkRegs] at hy
  rcases hy with (h | h) | ((h | h | h) | (h | h | h | h)) <;> subst h <;> simp [splitWR, DList.walkRegs]

set_option maxHeartbeats 4000000 in
/-- **One RAM split step on the top block** refines `DLazy.prep`'s step: if `SplitG` holds, the
top block `b` is replaced by `⟨b.sep, loOf⟩ :: ⟨medOf, hiOf⟩` (cost `≤ Ksp · splitCost`), else the
structure is unchanged, `dsp.go = 0`, and the live ids of `b` are at `sel.w[w0, w0 + |liveOf b|)`
(cost `≤ Knc · (|b.ents| + 1)`). -/
theorem splitStep_spec (hH : GoodHist (s := s) H V) (pSel : ℕ) (q : State ℝ≥0)
    {bcap lv bse w0 M : ℕ} {Bd : WLab G s} {L : Live (Fin G.n) (WLab G s)}
    {b : Block (Fin G.n) (WLab G s)} {bs : List (Block (Fin G.n) (WLab G s))}
    {ext : List (ℕ × Block (Fin G.n) (WLab G s))}
    (hP : SplitPre q H V bcap lv bse w0 L ⟨M, Bd, b :: bs⟩ ext pSel)
    (hfb : SplitG L M b → q.w "blk.fresh" < bcap)
    (hstk : SplitG L M b → bse + bs.length + 2 ≤ q.wlen "dsl.stk")
    (hsw : w0 + 6 * b.ents.length + 60 ≤ q.wlen "sel.w") :
    Runs realOps (splitStep pSel) q (fun r =>
      (SplitG L M b → SplitMade q r w0 lv (bse + bs.length) ∧
        SplitPre r H V bcap lv bse w0 L
          ⟨M, Bd, ⟨b.sep, loOf L b⟩ :: ⟨((medOf L b : WLab G s) : WithBot (WLab G s)), hiOf L b⟩ :: bs⟩
          ext pSel ∧
        r.cost ≤ q.cost + Ksp * splitCost L b) ∧
      (¬ SplitG L M b → SplitDone q r w0 ((liveOf L b.ents).map (·.id)) (q.wa "dsl.stk" (bse + bs.length))
          (bse + bs.length) ∧
        r.cost ≤ q.cost + Knc * (b.ents.length + 1))) := by
  obtain ⟨hB0, hbidb⟩ := top_blkRep hP.drep
  have hk := hP.drep.sz
  have hkb := hP.drep.stkb
  simp only [List.length_cons] at hk hkb
  have hstc := hP.stc
  have hswc := hP.swc
  have hcl : (liveOf L b.ents).length ≤ b.ents.length := length_liveOf_le L b.ents
  unfold splitStep
  apply runs_seq
  refine (spTop_run (ops := realOps) q (lv := lv) (bse := bse) (k := bs.length + 1) hP.lv hP.b hk
    (by omega) hP.drep.szb hkb (by omega)).mono (fun q1 ⟨ht1, hbid1, hr1, hc1⟩ => ?_)
  have ht1' : q1.w "sp.t" = bse + bs.length := by rw [ht1]; omega
  have hbid1' : q1.w "sp.bid" = q.wa "dsl.stk" (bse + bs.length) := by
    rw [hbid1]; congr 1
  set bid := q.wa "dsl.stk" (bse + bs.length) with hbidd
  have hwa1 : q1.wa = q.wa := hr1.1
  have hwl1 : q1.wlen = q.wlen := hr1.2.1
  have hbl1 : bid < q1.wlen "blk.hd" := by rw [hwl1]; have := hP.barr.1; omega
  have hL1 : DIns.LList q1 (q1.wa "blk.hd" bid) (b.ents.map (·.id)) := by
    rw [hwa1]; exact hB0.2.1.frame (by rw [hwl1]) (fun i _ => by rw [hwa1])
  apply runs_seq
  refine (spWalk_run (ops := realOps) q1 (b.ents.map (·.id)) (bid := bid) (w0 := w0) hbid1' hbl1
    (by rw [hr1.2.2.2.2.2.2.2 _ (by simp)]; exact hP.w0) hL1
    (fun i hi => by rw [hwl1, hwa1] at *; exact hP.key i hi) (by rw [hwl1, hr1.2.2.2.2.2.1]; exact hswc)
    (by rw [hwl1]; simp; omega)).mono (fun q2 ⟨hc2, hsp2, hout2, hu2, hwl2, hcost2⟩ => ?_)
  have hES1 : EntSame q q1 := ⟨by rw [hwa1], by rw [hr1.2.2.1], by rw [hwa1], by rw [hwa1], by rw [hwa1],
    by rw [hwa1], by rw [hwa1]⟩
  have hfl : (b.ents.map (·.id)).filter (DList.liveW q1) = (liveOf L b.ents).map (·.id) :=
    filter_liveW (liveRep_same hP.live hES1 (by rw [hwl1])) (fun e he => entRep_same (hB0.2.2.1 e he) hES1)
  rw [hfl] at hc2 hsp2 hout2
  simp only [List.length_map] at hc2 hout2
  set c := (liveOf L b.ents).length with hcd
  set liveI := (liveOf L b.ents).map (·.id) with hliveI
  -- the frame of the front part
  have uF : Unchanged q q2 ["sel.w"] [] (["sp.t", "sp.bid"] ++ (["dl.p", "dl.w", "sp.c"] ++ DList.walkRegs)) [] :=
    (hr1.unch _ _ _).mono (List.Subset.refl _) (List.Subset.refl _) (fun y hy => List.mem_append_left _ hy)
      (List.Subset.refl _) |>.trans (hu2.mono (List.Subset.refl _) (List.Subset.refl _)
        (fun y hy => List.mem_append_right _ hy) (List.Subset.refl _))
  have hwlF : q2.wlen = q.wlen := by
    funext x
    by_cases hx : x = "sel.w"
    · subst hx; rw [hwl2, hwl1]
    · exact (uF.warr x (by simpa using hx)).2
  have hvlF : q2.vlen = q.vlen := funext fun x => (uF.varr x (by simp)).2
  have hcapF : q2.cap = q.cap := uF.cap
  have hregF : ∀ y ∈ ["ds.M", "sp.w0", "blk.fresh", "ds.lv", "ds.b"], q2.w y = q.w y := by
    intro y hy
    refine uF.wreg y ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp [DList.walkRegs]
  have hbidF : q2.w "sp.bid" = bid := by
    rw [(hu2.wreg _ (by simp [DList.walkRegs]))]; exact hbid1'
  have htF : q2.w "sp.t" = bse + bs.length := by
    rw [(hu2.wreg _ (by simp [DList.walkRegs]))]; exact ht1'
  have hg : evalW q2 (lt (add (mul (var "ds.M") (lit 2)) (lit 1)) (var "sp.c")) =
      some (if M * 2 + 1 < c then 1 else 0) := by
    have hMc : 2 * M + 1 < q.cap := hP.Mc
    have h300 := hP.c300
    refine evalW_lt_of (evalW_add_of (x := M * 2) ?_ (evalW_lit_of (by rw [hcapF]; omega))
      (by rw [hcapF]; omega)) (by simp [hc2]) (by rw [hcapF]; omega)
    simp [hregF "ds.M" (by simp), hP.M, fit_of_lt (show M * 2 < q2.cap by rw [hcapF]; omega),
      fit_of_lt (show 2 < q2.cap by rw [hcapF]; omega)]
  have hP3 : SplitPre (q2.charge 1) H V bcap lv bse w0 L ⟨M, Bd, b :: bs⟩ ext pSel :=
    hP.of_unch ((unch_charge' 1).mpr uF) (fun y hy => by
      simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp [DList.walkRegs]) (by simp [hwl2, hwl1])
  have hsplitCost : b.ents.length + 2 * c + 1 ≤ splitCost L b := by
    unfold splitCost; omega
  have hK : Ksel 23 = 11300 := by simp [Ksel]
  by_cases hg1 : M * 2 + 1 < c
  · refine runs_ite_true (x := 1) (by rw [hg, if_pos hg1]) one_ne_zero ?_
    refine (split_mid hH pSel (q2.charge 1) hP3 (fun h => by simp [hregF "blk.fresh" (by simp), hfb h])
      (fun h => by simp [hwlF, hstk h]) (by simp [hwlF, hsw]) (by intro i hi; exact hsp2 i hi) (by simpa using hc2)
      (by simp [hbidF, (uF.warr "dsl.stk" (by simp)).1, hbidd]) (by simpa using htF) (by omega)).mono
      (fun r ⟨h1, h2⟩ => ⟨fun hs => ?_, fun hs => ?_⟩)
    · obtain ⟨⟨m1, m2, m3, m4, m5, m6, m7, m8⟩, hPr, hcr⟩ := h1 hs
      refine ⟨⟨m1, ((unch_charge' 1).mpr uF |>.mono (by simp [splitWA]) (by simp) frontRegs_sub
        (by simp)).trans m2, by rw [m3]; simp [hwlF], by rw [m4]; simp [hvlF], fun x hx => ?_,
        by rw [m6]; simp [hregF "blk.fresh" (by simp)], fun x hx => ?_, fun l hl => ?_⟩, hPr, ?_⟩
      · rw [m5 x hx]; simp only [State.charge_wa]; rw [hout2 x (Or.inl hx), hwa1]
      · rw [m7 x hx]; simp only [State.charge_wa]; rw [(uF.warr "dsl.stk" (by simp)).1]
      · rw [m8 l hl]; simp only [State.charge_wa]; rw [(uF.warr "dsl.sz" (by simp)).1]
      · rw [hK] at hcr
        simp only [State.charge_cost] at hcr
        have : Ksp * (b.ents.length + 2 * c + 1) ≤ Ksp * splitCost L b := Nat.mul_le_mul_left _ hsplitCost
        simp only [Ksp] at this ⊢
        simp only [List.length_map] at hcost2
        omega
    · obtain ⟨⟨d1, d2, d3, d4, d5, d6, d7, d8, d9⟩, hcr⟩ := h2 hs
      refine ⟨⟨d1, ((unch_charge' 1).mpr uF |>.mono (List.Subset.refl _) (by simp) frontRegs_sub
        (by simp)).trans d2, by rw [d3]; simp [hwl2, hwl1], d4, d5, by rw [d6]; simp [(uF.warr "dsl.stk" (by simp)).1, hbidd],
        d7, fun x hx => by rw [d8 x hx]; simp only [State.charge_wa]; rw [hout2 x (Or.inl hx), hwa1],
        by rw [d9]; simp [hregF "blk.fresh" (by simp)]⟩, ?_⟩
      rw [hK] at hcr
      simp only [State.charge_cost] at hcr
      simp only [List.length_map] at hcost2
      simp only [Knc]
      omega
  · refine runs_ite_false (by rw [hg, if_neg hg1]) ?_
    refine runs_wset (a := 0) (by simp [fit_of_lt (show 0 < q2.cap by rw [hcapF]; have := hP.c300; omega)]) ?_
    refine ⟨fun hs => absurd hs.1 (by omega), fun _ => ⟨⟨by simp, ?_, by simp [hwl2, hwl1],
      fun i hi => hsp2 i hi, by simp [hc2, hliveI, hcd], by simp [hbidF], by simp [htF],
      fun x hx => by simp only [State.charge_wa, State.setW_wa]; rw [hout2 x (Or.inl hx), hwa1],
      by simp [hregF "blk.fresh" (by simp)]⟩, ?_⟩⟩
    · rw [unch_charge', unch_setW' (by simp [splitWR]), unch_charge']
      exact uF.mono (List.Subset.refl _) (List.Subset.refl _) frontRegs_sub (by simp)
    · simp only [State.charge_cost, State.setW_cost, Knc]
      simp only [State.charge_cost, State.setW_cost, List.length_map] at hcost2
      omega

end Spec


/-! ## `prepTop`: split the top block while `SplitG` (refines `DLazy.prep`) -/

section Prep

open Frontier.CHD.DIns Frontier.CHD.DB Frontier.CHD.DL Frontier.CHD.MLab Frontier.CHD.LabTab
  Frontier.CHD.DList

variable {G : Graph} {s : Fin G.n}

/-- the state after preparing the top block: the structure is `b' :: rest'` = `prep`'s result -/
structure PrepOut (q r : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (bcap lv bse w0 M : ℕ) (Bd : WLab G s) (L : Live (Fin G.n) (WLab G s))
    (ext : List (ℕ × Block (Fin G.n) (WLab G s))) (pSel : ℕ) (b' : Block (Fin G.n) (WLab G s))
    (rest' : List (Block (Fin G.n) (WLab G s))) (pc : ℕ) : Prop where
  pre : SplitPre r H V bcap lv bse w0 L ⟨M, Bd, b' :: rest'⟩ ext pSel
  spell : DList.Spells r "sel.w" w0 ((liveOf L b'.ents).map (·.id))
  c : r.w "sp.c" = (liveOf L b'.ents).length
  bid : r.w "sp.bid" = r.wa "dsl.stk" (bse + rest'.length)
  t : r.w "sp.t" = bse + rest'.length
  go : r.w "dsp.go" = 0
  unch : Unchanged q r splitWA ["blk.len"] splitWR entLessV
  wlen : r.wlen = q.wlen
  vlen : r.vlen = q.vlen
  low : ∀ x, x < w0 → r.wa "sel.w" x = q.wa "sel.w" x
  fr1 : q.w "blk.fresh" ≤ r.w "blk.fresh"
  fr2 : r.w "blk.fresh" ≤ q.w "blk.fresh" + pc
  stk : ∀ x, x < bse → r.wa "dsl.stk" x = q.wa "dsl.stk" x
  sz : ∀ l, l ≠ lv → r.wa "dsl.sz" l = q.wa "dsl.sz" l
  cost : r.cost ≤ q.cost + (Ksp + 1) * pc + Knc * (b'.ents.length + 1) + 2

theorem prepOut_done {q r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap lv bse w0 M pSel : ℕ} {Bd : WLab G s} {L : Live (Fin G.n) (WLab G s)}
    {b : Block (Fin G.n) (WLab G s)} {bs : List (Block (Fin G.n) (WLab G s))}
    {ext : List (ℕ × Block (Fin G.n) (WLab G s))}
    (hP : SplitPre q H V bcap lv bse w0 L ⟨M, Bd, b :: bs⟩ ext pSel)
    (hD : SplitDone (q.charge 1) r w0 ((liveOf L b.ents).map (·.id)) (q.wa "dsl.stk" (bse + bs.length))
      (bse + bs.length))
    (hcr : r.cost ≤ (q.charge 1).cost + Knc * (b.ents.length + 1)) :
    PrepOut q (r.charge 1) H V bcap lv bse w0 M Bd L ext pSel b bs 0 := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ := hD
  have u : Unchanged q (r.charge 1) ["sel.w"] [] splitWR entLessV := by
    rw [unch_charge']
    exact ((unch_charge' 1).mpr (Unchanged.refl q ["sel.w"] [] splitWR entLessV)).trans d2
  have hwl : (r.charge 1).wlen = q.wlen := by
    funext x
    by_cases hx : x = "sel.w"
    · subst hx; simpa using d3
    · exact (u.warr x (by simpa using hx)).2
  have hwa : ∀ a, a ≠ "sel.w" → (r.charge 1).wa a = q.wa a := fun a ha => (u.warr a (by simpa using ha)).1
  refine ⟨hP.of_unch' u (fun y hy => keep_nw hy) (by simpa using d9) (by simpa using d3), d4,
    by simpa using d5, by simp only [State.charge_w]; rw [d6, hwa "dsl.stk" (by simp)], by simpa using d7,
    by simpa using d1, u.mono (by simp [splitWA]) (by simp) (List.Subset.refl _) (List.Subset.refl _), hwl,
    funext fun x => (u.varr x (by simp)).2, fun x hx => by simpa using d8 x hx, by simp [d9],
    by simp [d9], fun x _ => by rw [hwa "dsl.stk" (by simp)], fun l _ => by rw [hwa "dsl.sz" (by simp)], ?_⟩
  simp only [State.charge_cost] at hcr ⊢
  omega

theorem prepOut_split {q r r' : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap lv bse w0 M pSel : ℕ} {Bd : WLab G s} {L : Live (Fin G.n) (WLab G s)}
    {b b' : Block (Fin G.n) (WLab G s)} {bs rest' : List (Block (Fin G.n) (WLab G s))}
    {ext : List (ℕ × Block (Fin G.n) (WLab G s))} {pc : ℕ}
    (hM : SplitMade (q.charge 1) r w0 lv (bse + bs.length))
    (hcr : r.cost ≤ (q.charge 1).cost + Ksp * splitCost L b)
    (hO : PrepOut r r' H V bcap lv bse w0 M Bd L ext pSel b' rest' pc) :
    PrepOut q r' H V bcap lv bse w0 M Bd L ext pSel b' rest' (pc + splitCost L b) := by
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8⟩ := hM
  have hsc : 1 ≤ splitCost L b := by unfold splitCost; omega
  have u : Unchanged q r splitWA ["blk.len"] splitWR entLessV :=
    ((unch_charge' 1).mpr (Unchanged.refl q splitWA ["blk.len"] splitWR entLessV)).trans m2
  refine ⟨hO.pre, hO.spell, hO.c, hO.bid, hO.t, hO.go, u.trans hO.unch, by rw [hO.wlen, m3]; rfl,
    by rw [hO.vlen, m4]; rfl, fun x hx => by rw [hO.low x hx, m5 x hx]; rfl,
    by have := hO.fr1; simp at m6; omega, by have := hO.fr2; simp at m6; omega,
    fun x hx => by rw [hO.stk x hx, m7 x (by omega)]; rfl, fun l hl => by rw [hO.sz l hl, m8 l hl]; rfl, ?_⟩
  have h1 := hO.cost
  simp only [State.charge_cost] at hcr
  have : Ksp * splitCost L b + 1 ≤ (Ksp + 1) * splitCost L b := by nlinarith
  nlinarith

theorem prep_cons_split {L : Live (Fin G.n) (WLab G s)} {M : ℕ} {b : Block (Fin G.n) (WLab G s)}
    {bs : List (Block (Fin G.n) (WLab G s))} (h : SplitG L M b) :
    prep L M (b :: bs) = ((prep L M (⟨b.sep, loOf L b⟩ ::
        ⟨((medOf L b : WLab G s) : WithBot (WLab G s)), hiOf L b⟩ :: bs)).1,
      (prep L M (⟨b.sep, loOf L b⟩ :: ⟨((medOf L b : WLab G s) : WithBot (WLab G s)), hiOf L b⟩ :: bs)).2 +
        splitCost L b) := by
  rw [prep, dif_pos h]

theorem prep_cons_nosplit {L : Live (Fin G.n) (WLab G s)} {M : ℕ} {b : Block (Fin G.n) (WLab G s)}
    {bs : List (Block (Fin G.n) (WLab G s))} (h : ¬ SplitG L M b) : prep L M (b :: bs) = (b :: bs, 0) := by
  rw [prep, dif_neg h]

set_option maxHeartbeats 1000000 in
/-- **the split loop** -/
theorem prep_loop (hH : GoodHist (s := s) H V) (pSel : ℕ) {bcap lv bse w0 M : ℕ} {Bd : WLab G s}
    {L : Live (Fin G.n) (WLab G s)} {ext : List (ℕ × Block (Fin G.n) (WLab G s))} :
    ∀ (n : ℕ) (q : State ℝ≥0) (b : Block (Fin G.n) (WLab G s)) (bs : List (Block (Fin G.n) (WLab G s))),
      (liveOf L b.ents).length ≤ n → SplitPre q H V bcap lv bse w0 L ⟨M, Bd, b :: bs⟩ ext pSel →
      q.w "dsp.go" = 1 → q.w "blk.fresh" + (prep L M (b :: bs)).2 ≤ bcap →
      bse + bs.length + 1 + (prep L M (b :: bs)).2 ≤ q.wlen "dsl.stk" →
      w0 + 6 * b.ents.length + 60 ≤ q.wlen "sel.w" →
      Runs realOps (.while (var "dsp.go") (splitStep pSel)) q (fun r => ∃ b' rest',
        (prep L M (b :: bs)).1 = b' :: rest' ∧
        PrepOut q r H V bcap lv bse w0 M Bd L ext pSel b' rest' (prep L M (b :: bs)).2) := by
  intro n
  induction n with
  | zero =>
    intro q b bs hn hP hgo hf hs hw
    have hns : ¬ SplitG L M b := fun h => by unfold SplitG at h; omega
    refine runs_while_step (x := 1) (by simp [hgo]) one_ne_zero ?_
    refine (splitStep_spec hH pSel (q.charge 1) (hP.charge 1) (fun h => absurd h hns) (fun h => absurd h hns)
      (by simpa using hw)).mono
      (fun r ⟨_, h2⟩ => ?_)
    obtain ⟨hD, hcr⟩ := h2 hns
    refine runs_while_exit (by simp [hD.1]) ⟨b, bs, by rw [prep_cons_nosplit hns], ?_⟩
    rw [prep_cons_nosplit hns]
    exact prepOut_done hP (by simpa using hD) hcr
  | succ n ih =>
    intro q b bs hn hP hgo hf hs hw
    refine runs_while_step (x := 1) (by simp [hgo]) one_ne_zero ?_
    have hP1 : SplitPre (q.charge 1) H V bcap lv bse w0 L ⟨M, Bd, b :: bs⟩ ext pSel := hP.charge 1
    refine (splitStep_spec hH pSel (q.charge 1) hP1 (fun h => ?_) (fun h => ?_) (by simpa using hw)).mono
      (fun r ⟨h1, h2⟩ => ?_)
    · rw [prep_cons_split h] at hf
      have : 1 ≤ splitCost L b := by unfold splitCost; omega
      simp; omega
    · rw [prep_cons_split h] at hs
      have : 1 ≤ splitCost L b := by unfold splitCost; omega
      simp; omega
    by_cases hsg : SplitG L M b
    · obtain ⟨hM, hPr, hcr⟩ := h1 hsg
      have hlt : (loOf L b).length < (liveOf L b.ents).length :=
        loOf_length_lt (by unfold SplitG at hsg; omega)
      have hlo : (liveOf L (loOf L b)).length ≤ n := by
        rw [liveOf_all_live loOf_live]; omega
      have hpe := prep_cons_split (bs := bs) hsg
      have hsc : 1 ≤ splitCost L b := by unfold splitCost; omega
      obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8⟩ := hM
      refine (ih r ⟨b.sep, loOf L b⟩ (⟨((medOf L b : WLab G s) : WithBot (WLab G s)), hiOf L b⟩ :: bs)
        hlo hPr m1 ?_ ?_ ?_).mono (fun r' ⟨b', rest', he, hO⟩ => ⟨b', rest', by rw [hpe]; exact he, ?_⟩)
      · rw [hpe] at hf; simp at m6; omega
      · rw [hpe] at hs; rw [m3]; simp; omega
      · rw [m3]; simp
        have : (loOf L b).length ≤ b.ents.length :=
          le_trans hlt.le (length_liveOf_le L b.ents)
        omega
      · rw [hpe]
        exact prepOut_split ⟨m1, m2, m3, m4, m5, m6, m7, m8⟩ hcr hO
    · obtain ⟨hD, hcr⟩ := h2 hsg
      refine runs_while_exit (by simp [hD.1]) ⟨b, bs, by rw [prep_cons_nosplit hsg], ?_⟩
      rw [prep_cons_nosplit hsg]
      exact prepOut_done hP (by simpa using hD) hcr

/-! ## Emitting pulled keys: `S` row and live map -/

section Emit

variable {ops : VOps ℝ≥0}

/-- one key: `k := ent.key[sel.w[pl.lo + pl.i]]`, `live[k] := 0`, `S[pl.rb + pl.i] := k` -/
def emBody : Stmt :=
  seq (wset "pl.id" (load "sel.w" (add (var "pl.lo") (var "pl.i"))))
  (seq (wset "pl.k" (load "ent.key" (var "pl.id")))
  (seq (wstore "live" (var "pl.k") (lit 0))
  (seq (wstore "S" (add (var "pl.rb") (var "pl.i")) (var "pl.k"))
       (wset "pl.i" (add (var "pl.i") (lit 1))))))

/-- emit the keys of the ids `sel.w[pl.lo, pl.lo + pl.n)` to `S[pl.rb, …)`, clear their live
pointers, and set `S.len[pl.row] := pl.n` -/
def emitKeys : Stmt :=
  seq (wset "pl.i" (lit 0))
  (seq (.while (lt (var "pl.i") (var "pl.n")) emBody)
       (wstore "S.len" (var "pl.row") (var "pl.n")))

/-- the keys of the ids `sel.w[lo, lo + n)` -/
def keysOf (q : State ℝ≥0) (lo n : ℕ) : List ℕ := (seg q lo n).map (q.wa "ent.key")

@[simp] theorem length_keysOf (q : State ℝ≥0) (lo n : ℕ) : (keysOf q lo n).length = n := by
  simp [keysOf]

theorem keysOf_get (q : State ℝ≥0) (lo n i : ℕ) (hi : i < n) :
    (keysOf q lo n)[i]'(by simp; exact hi) = q.wa "ent.key" (q.wa "sel.w" (lo + i)) := by
  simp [keysOf, seg]

theorem keysOf_succ (q : State ℝ≥0) (lo k : ℕ) :
    keysOf q lo (k + 1) = keysOf q lo k ++ [q.wa "ent.key" (q.wa "sel.w" (lo + k))] := by
  simp [keysOf, seg, List.range_succ]

/-- loop invariant of `emitKeys` after `k` keys -/
structure EmInv (q : State ℝ≥0) (lo n0 rb row k : ℕ) (st : State ℝ≥0) : Prop where
  ireg : st.w "pl.i" = k
  loreg : st.w "pl.lo" = lo
  nreg : st.w "pl.n" = n0
  rbreg : st.w "pl.rb" = rb
  rowreg : st.w "pl.row" = row
  live : ∀ v, st.wa "live" v = if v ∈ keysOf q lo k then 0 else q.wa "live" v
  Sin : ∀ i < k, st.wa "S" (rb + i) = q.wa "ent.key" (q.wa "sel.w" (lo + i))
  Sout : ∀ x, (x < rb ∨ rb + k ≤ x) → st.wa "S" x = q.wa "S" x
  unch : Unchanged q st ["live", "S"] [] ["pl.i", "pl.id", "pl.k"] []
  wlen : st.wlen = q.wlen
  cost : st.cost = q.cost + 1 + 6 * k

set_option maxHeartbeats 2000000 in
theorem emBody_step (q : State ℝ≥0) {lo n0 rb row k : ℕ} (st : State ℝ≥0)
    (hI : EmInv q lo n0 rb row k st) (hk : k < n0) (hsl : lo + n0 ≤ q.wlen "sel.w")
    (hid : ∀ i < n0, q.wa "sel.w" (lo + i) < q.wlen "ent.key" ∧
      q.wa "ent.key" (q.wa "sel.w" (lo + i)) < q.wlen "live")
    (hS : rb + n0 ≤ q.wlen "S") (hcap : rb + n0 + lo + 2 < q.cap) :
    Runs ops emBody (st.charge 1) (EmInv q lo n0 rb row (k + 1)) := by
  have hcs : st.cap = q.cap := hI.unch.cap
  have hsw : st.wa "sel.w" = q.wa "sel.w" := (hI.unch.warr "sel.w" (by simp)).1
  have hek : st.wa "ent.key" = q.wa "ent.key" := (hI.unch.warr "ent.key" (by simp)).1
  set id := q.wa "sel.w" (lo + k) with hidd
  set key := q.wa "ent.key" id with hkey
  obtain ⟨hid1, hid2⟩ := hid k hk
  unfold emBody
  apply runs_seq
  have e1 : evalW (st.charge 1) (var "pl.lo") = some lo := by
    rw [evalW_var]; congr 1; exact hI.loreg
  have e2 : evalW (st.charge 1) (var "pl.i") = some k := by
    rw [evalW_var]; congr 1; exact hI.ireg
  have c1 : lo + k < (st.charge 1).cap := by
    show lo + k < st.cap; rw [hcs]; omega
  have c2 : lo + k < (st.charge 1).wlen "sel.w" := by
    show lo + k < st.wlen "sel.w"; rw [hI.wlen]; omega
  refine runs_wset (a := id) ?_ ?_
  · rw [evalW_load_of (evalW_add_of e1 e2 c1) c2]
    show some (st.wa "sel.w" (lo + k)) = some id
    rw [hsw]
  apply runs_seq
  refine runs_wset (a := key) ?_ ?_
  · have e3 : evalW (((st.charge 1).setW "pl.id" id).charge 1) (var "pl.id") = some id := by simp
    have c3 : id < (((st.charge 1).setW "pl.id" id).charge 1).wlen "ent.key" := by
      show id < st.wlen "ent.key"; rw [hI.wlen]; exact hid1
    rw [evalW_load_of e3 c3]
    show some (st.wa "ent.key" id) = some key
    rw [hek]
  apply runs_seq
  refine runs_wstore (j := key) (a := 0) (by simp) (by simp [hcs, fit_of_lt (show 0 < q.cap by omega)])
    (by simp [hI.wlen]; exact hid2) ?_
  apply runs_seq
  refine runs_wstore (j := rb + k) (a := key) (evalW_add_of (x := rb) (y := k) (by simp [hI.rbreg])
    (by simp [hI.ireg]) (by simp [hcs]; omega)) (by simp) (by simp [hI.wlen]; omega) ?_
  refine runs_wset (a := k + 1) (evalW_add_of (x := k) (y := 1) (by simp [hI.ireg])
    (evalW_lit_of (by simp [hcs]; omega)) (by simp [hcs]; omega)) ?_
  refine ⟨by simp, by simp [hI.loreg], by simp [hI.nreg], by simp [hI.rbreg], by simp [hI.rowreg], fun v => ?_,
    fun i hi => ?_, fun x hx => ?_, ?_, by simp [hI.wlen], by simp [hI.cost]; ring⟩
  · simp only [State.charge_wa, State.setW_wa, State.storeW_wa]
    rw [keysOf_succ, hI.live v]
    simp only [List.mem_append, List.mem_singleton]
    by_cases hv : v = key
    · simp [hv, ← hkey, ← hidd]
    · have : ¬ ("live" = "S" ∧ v = rb + k) := by simp
      simp [hv, ← hkey, ← hidd]
  · simp only [State.charge_wa, State.setW_wa, State.storeW_wa]
    by_cases hik : i = k
    · subst hik; simp [hkey, hidd]
    · have hi' : i < k := by omega
      simp [show ¬ rb + i = rb + k by omega, hik, hI.Sin i hi']
  · simp only [State.charge_wa, State.setW_wa, State.storeW_wa]
    rw [if_neg (by intro h; rcases hx with hx | hx <;> omega)]
    simp only [show ¬ ("S" = "live") by decide, false_and, if_false]
    exact hI.Sout x (by omega)
  · refine hI.unch.trans ?_
    rw [unch_charge', unch_setW' (by simp), unch_charge', unch_storeW (by simp), unch_charge',
      unch_storeW (by simp), unch_charge', unch_setW' (by simp), unch_charge', unch_setW' (by simp),
      unch_charge']
    exact Unchanged.refl _ _ _ _ _

set_option maxHeartbeats 1000000 in
theorem emitKeys_spec (q : State ℝ≥0) {lo n0 rb row : ℕ} (hlo : q.w "pl.lo" = lo)
    (hn : q.w "pl.n" = n0) (hrb : q.w "pl.rb" = rb) (hrow : q.w "pl.row" = row)
    (hsl : lo + n0 ≤ q.wlen "sel.w")
    (hid : ∀ i < n0, q.wa "sel.w" (lo + i) < q.wlen "ent.key" ∧
      q.wa "ent.key" (q.wa "sel.w" (lo + i)) < q.wlen "live")
    (hS : rb + n0 ≤ q.wlen "S") (hrowl : row < q.wlen "S.len") (hcap : rb + n0 + lo + 2 < q.cap) :
    Runs ops emitKeys q (fun r =>
      (∀ v, r.wa "live" v = if v ∈ keysOf q lo n0 then 0 else q.wa "live" v) ∧
      (∀ i < n0, r.wa "S" (rb + i) = q.wa "ent.key" (q.wa "sel.w" (lo + i))) ∧
      (∀ x, (x < rb ∨ rb + n0 ≤ x) → r.wa "S" x = q.wa "S" x) ∧
      r.wa "S.len" row = n0 ∧ (∀ j, j ≠ row → r.wa "S.len" j = q.wa "S.len" j) ∧
      Unchanged q r ["live", "S", "S.len"] [] ["pl.i", "pl.id", "pl.k"] [] ∧ r.wlen = q.wlen ∧
      r.cost = q.cost + 3 + 6 * n0) := by
  have h0 : 0 < q.cap := by omega
  have h1 : 1 < q.cap := by omega
  unfold emitKeys
  apply runs_seq
  refine runs_wset (a := 0) (by simp [fit_of_lt h0]) ?_
  apply runs_seq
  have hI0 : EmInv q lo n0 rb row 0 ((q.setW "pl.i" 0).charge 1) := by
    refine ⟨by simp, by simp [hlo], by simp [hn], by simp [hrb], by simp [hrow], fun v => by simp [keysOf, seg],
      fun i hi => absurd hi (Nat.not_lt_zero _), fun x _ => by simp, ?_, by simp, by simp⟩
    rw [unch_charge', unch_setW' (by simp)]; exact Unchanged.refl _ _ _ _ _
  refine runs_while (EmInv q lo n0 rb row) n0 _ (fun k hk st hI => ⟨1, ?_, one_ne_zero,
    emBody_step q st hI hk hsl hid hS hcap⟩) (fun st hI => ⟨?_, ?_⟩) _ hI0
  · have hcs : st.cap = q.cap := hI.unch.cap
    rw [evalW_lt_of (x := k) (y := n0) (by simp [hI.ireg]) (by simp [hI.nreg]) (by rw [hcs]; exact h1),
      if_pos hk]
  · have hcs : st.cap = q.cap := hI.unch.cap
    rw [evalW_lt_of (x := n0) (y := n0) (by simp [hI.ireg]) (by simp [hI.nreg]) (by rw [hcs]; exact h1),
      if_neg (lt_irrefl _)]
  · have hcs : st.cap = q.cap := hI.unch.cap
    refine runs_wstore (j := row) (a := n0) (by simp [hI.rowreg]) (by simp [hI.nreg])
      (by simp [hI.wlen]; exact hrowl) ?_
    refine ⟨fun v => by simpa using hI.live v, fun i hi => by simpa [show ¬ ("S" = "S.len") by decide] using hI.Sin i hi,
      fun x hx => by simpa [show ¬ ("S" = "S.len") by decide] using hI.Sout x hx, by simp,
      fun j hj => ?_, ?_, by simp [hI.wlen], by simp [hI.cost]; ring⟩
    · simp only [State.charge_wa, State.storeW_wa]
      rw [if_neg (fun h => hj h.2), (hI.unch.warr "S.len" (by simp)).1]
    · refine (hI.unch.mono (by simp) (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _)).trans ?_
      rw [unch_charge', unch_storeW (by simp), unch_charge']
      exact Unchanged.refl _ _ _ _ _

end Emit

/-- **prepTop** (`dsp.go := 1; while dsp.go splitStep`) refines `DLazy.prep` on the top block -/
theorem prepTop_spec (hH : GoodHist (s := s) H V) (pSel : ℕ) (q : State ℝ≥0)
    {bcap lv bse w0 M : ℕ} {Bd : WLab G s} {L : Live (Fin G.n) (WLab G s)}
    {b : Block (Fin G.n) (WLab G s)} {bs : List (Block (Fin G.n) (WLab G s))}
    {ext : List (ℕ × Block (Fin G.n) (WLab G s))}
    (hP : SplitPre q H V bcap lv bse w0 L ⟨M, Bd, b :: bs⟩ ext pSel)
    (hf : q.w "blk.fresh" + (prep L M (b :: bs)).2 ≤ bcap)
    (hs : bse + bs.length + 1 + (prep L M (b :: bs)).2 ≤ q.wlen "dsl.stk")
    (hw : w0 + 6 * b.ents.length + 60 ≤ q.wlen "sel.w") :
    Runs realOps (prepTop pSel) q (fun r => ∃ b' rest', (prep L M (b :: bs)).1 = b' :: rest' ∧
      PrepOut ((q.setW "dsp.go" 1).charge 1) r H V bcap lv bse w0 M Bd L ext pSel b' rest'
        (prep L M (b :: bs)).2) := by
  unfold prepTop
  apply runs_seq
  refine runs_wset (a := 1) (evalW_lit_of (by have := hP.c300; omega)) ?_
  have u : Unchanged q ((q.setW "dsp.go" 1).charge 1) ["sel.w"] [] ["dsp.go"] [] := by
    rw [unch_charge', unch_setW' (by simp)]; exact Unchanged.refl _ _ _ _ _
  exact prep_loop hH pSel _ _ b bs le_rfl
    (hP.of_unch' u (fun y hy => by
      simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> simp) (by simp) (by simp))
    (by simp) (by simpa using hf) (by simpa using hs) (by simpa using hw)

end Prep

/-! ## Layer-A facts for the collect loop of `pullL` -/

section PullA

open Frontier.CHD.DB Frontier.CHD.DL

variable {κ α : Type*} [DecidableEq κ] [LinearOrder α] [Inhabited α]

theorem splitCost_pos (L : Live κ α) (b : Block κ α) : 1 ≤ splitCost L b := by
  unfold splitCost; omega

theorem prep_length_le (L : Live κ α) (M : ℕ) :
    ∀ bs, (prep L M bs).1.length ≤ bs.length + (prep L M bs).2 := by
  intro bs
  induction bs using prep.induct (L := L) (M := M) with
  | case1 => simp [prep]
  | case2 b bs h ih =>
    rw [prep, dif_pos h]
    have := splitCost_pos L b
    simp only [List.length_cons] at ih ⊢
    omega
  | case3 b bs h =>
    rw [prep, dif_neg h]; simp

theorem prepList_cons_le {L : Live κ α} {M cnt : ℕ} {b b' : Block κ α} {rest bs' : List (Block κ α)}
    (h : ¬ M < cnt) (hp : (prep L M (b :: rest)).1 = b' :: bs') :
    prepList L M cnt (b :: rest) =
      (b' :: (prepList L M (cnt + (liveOf L b'.ents).length) bs').1,
       (prepList L M (cnt + (liveOf L b'.ents).length) bs').2 + (prep L M (b :: rest)).2) := by
  rw [prepList, if_neg h]
  split
  · next hp' => rw [hp] at hp'; exact absurd hp' (List.cons_ne_nil _ _)
  · next b'' bs'' hp' =>
    rw [hp] at hp'
    obtain ⟨rfl, rfl⟩ := List.cons.inj hp'
    rfl

theorem prepList_of_lt {L : Live κ α} {M cnt : ℕ} (h : M < cnt) (bs : List (Block κ α)) :
    prepList L M cnt bs = (bs, 0) := by
  cases bs with
  | nil => simp [prepList]
  | cons b rest => rw [prepList, if_pos h]

theorem prepList_nil' (L : Live κ α) (M cnt : ℕ) : prepList L M cnt ([] : List (Block κ α)) = ([], 0) := by
  simp [prepList]

theorem collect_cons (L : Live κ α) (M : ℕ) (acc : List (Entry κ α)) (b : Block κ α)
    (X : List (Block κ α)) :
    collect L M acc (b :: X) =
      if M < (acc ++ liveOf L b.ents).length then (acc ++ liveOf L b.ents, X, 1, b.ents.length)
      else ((collect L M (acc ++ liveOf L b.ents) X).1, (collect L M (acc ++ liveOf L b.ents) X).2.1,
        (collect L M (acc ++ liveOf L b.ents) X).2.2.1 + 1,
        (collect L M (acc ++ liveOf L b.ents) X).2.2.2 + b.ents.length) := by
  rfl

theorem collect_nil' (L : Live κ α) (M : ℕ) (acc : List (Entry κ α)) :
    collect L M acc ([] : List (Block κ α)) = (acc, [], 0, 0) := rfl

omit [DecidableEq κ] in
theorem allEnts_cons' (b : Block κ α) (bs : List (Block κ α)) :
    allEnts (b :: bs) = b.ents ++ allEnts bs := by simp [allEnts]

theorem prep_allEnts_le (L : Live κ α) (M : ℕ) (bs : List (Block κ α)) :
    (allEnts (prep L M bs).1).length ≤ (allEnts bs).length :=
  (prep_subperm L M bs).length_le

theorem liveVals_len_le (L : Live κ α) : ∀ bs : List (Block κ α), (liveVals L bs).length ≤ (allEnts bs).length
  | [] => by simp [liveVals, allEnts]
  | b :: bs => by
    have ih := liveVals_len_le L bs
    have := length_liveOf_le L b.ents
    simp only [liveVals, allEnts, List.map_cons, List.flatten_cons, List.length_append] at ih ⊢
    omega

theorem collect_len_le (L : Live κ α) (M : ℕ) (X : List (Block κ α)) :
    (collect L M [] X).1.length ≤ (allEnts X).length := by
  obtain ⟨pre, h1, h2, -⟩ := collect_spec L M X []
  rw [h2, List.nil_append]
  have e : allEnts X = allEnts pre ++ allEnts (collect L M [] X).2.1 := by
    conv_lhs => rw [h1]
    simp [allEnts]
  rw [e, List.length_append]
  have := liveVals_len_le L pre
  omega

theorem pullL_cut (L : Live κ α) (M : ℕ) (Bd : α) (bs : List (Block κ α))
    (h : M < (collect L M [] (prepList L M 0 bs).1).1.length) :
    pullL 1 L ⟨M, Bd, bs⟩ =
      ((((collect L M [] (prepList L M 0 bs).1).1.filter (fun e => decide (e.val <
          (selectC ((collect L M [] (prepList L M 0 bs).1).1.map (·.val)) M).1))).map (·.key)),
       (selectC ((collect L M [] (prepList L M 0 bs).1).1.map (·.val)) M).1,
       clearKeys L (((collect L M [] (prepList L M 0 bs).1).1.filter (fun e => decide (e.val <
          (selectC ((collect L M [] (prepList L M 0 bs).1).1.map (·.val)) M).1))).map (·.key)),
       ⟨M, Bd, ⟨⊥, (collect L M [] (prepList L M 0 bs).1).1.filter (fun e => decide
          ((selectC ((collect L M [] (prepList L M 0 bs).1).1.map (·.val)) M).1 ≤ e.val))⟩ ::
          (collect L M [] (prepList L M 0 bs).1).2.1⟩,
       (collect L M [] (prepList L M 0 bs).1).2.2.2 +
          (selectC ((collect L M [] (prepList L M 0 bs).1).1.map (·.val)) M).2 +
          4 * (collect L M [] (prepList L M 0 bs).1).1.length +
          1 * ((collect L M [] (prepList L M 0 bs).1).2.2.1 + 1) + 1 + (prepList L M 0 bs).2) := by
  unfold pullL pull
  dsimp only
  rw [if_neg (not_le.mpr h)]

theorem pullL_all (L : Live κ α) (M : ℕ) (Bd : α) (bs : List (Block κ α))
    (h : ¬ M < (collect L M [] (prepList L M 0 bs).1).1.length) :
    pullL 1 L ⟨M, Bd, bs⟩ =
      ((collect L M [] (prepList L M 0 bs).1).1.map (·.key), Bd,
       clearKeys L ((collect L M [] (prepList L M 0 bs).1).1.map (·.key)), ⟨M, Bd, [⟨⊥, []⟩]⟩,
       (collect L M [] (prepList L M 0 bs).1).2.2.2 + 2 * (collect L M [] (prepList L M 0 bs).1).1.length +
          1 * ((collect L M [] (prepList L M 0 bs).1).2.2.1 + 1) + 1 + (prepList L M 0 bs).2) := by
  unfold pullL pull
  dsimp only
  rw [if_pos (not_lt.mp h)]

theorem collect_rest_nil (L : Live κ α) (M : ℕ) (X : List (Block κ α))
    (h : ¬ M < (collect L M [] X).1.length) : (collect L M [] X).2.1 = [] := by
  obtain ⟨pre, _, _, _, _, h5, _⟩ := collect_spec L M X []
  rcases h5 with h5 | h5
  · exact h5
  · exact absurd h5 h

theorem pullL_keys_le (L : Live κ α) (D : DStr κ α) :
    (pullL 1 L D).1.length ≤ (pullL 1 L D).2.2.2.2 := by
  obtain ⟨M, Bd, bs⟩ := D
  by_cases h : M < (collect L M [] (prepList L M 0 bs).1).1.length
  · rw [pullL_cut L M Bd bs h]
    dsimp only
    have := List.length_filter_le (fun e => decide (e.val <
      (selectC ((collect L M [] (prepList L M 0 bs).1).1.map (·.val)) M).1))
      (collect L M [] (prepList L M 0 bs).1).1
    simp only [List.length_map]
    omega
  · rw [pullL_all L M Bd bs h]
    dsimp only
    simp only [List.length_map]
    omega

end PullA

/-! ## The collect loop of Pull -/

/-- after preparing the top block: count its live ids (already at `sel.w[sp.w0, …)`), pop it,
decide whether to go on (`pl.go := [cnt ≤ M ∧ stack nonempty]`) -/
def colTail : Stmt :=
  seq (wset "pl.cnt" (add (var "pl.cnt") (var "sp.c")))
  (seq (wset "sp.w0" (add (var "pl.base") (var "pl.cnt")))
  (seq (wset "pl.pid" (var "sp.bid"))
  (seq (wstore "dsl.sz" (var "ds.lv") (sub (load "dsl.sz" (var "ds.lv")) (lit 1)))
       (ite (lt (var "ds.M") (var "pl.cnt"))
            (wset "pl.go" (lit 0))
            (wset "pl.go" (lt (lit 0) (load "dsl.sz" (var "ds.lv"))))))))

/-- one round of the collect loop -/
def colBody (pSel : ℕ) : Stmt := seq (prepTop pSel) colTail

/-- the collect loop -/
def colLoop (pSel : ℕ) : Stmt := .while (var "pl.go") (colBody pSel)

/-- registers written by the collect loop besides the split machinery -/
def plRegs : List String := ["pl.cnt", "pl.pid", "pl.go", "sp.w0"]

section Collect

variable {ops : VOps ℝ≥0}

/-- the state after `colTail` -/
def colSt (r : State ℝ≥0) (cnt w0 pid lv k g : ℕ) : State ℝ≥0 :=
  (((((((((r.setW "pl.cnt" cnt).charge 1).setW "sp.w0" w0).charge 1).setW "pl.pid" pid).charge 1).storeW
    "dsl.sz" lv k).charge 1).charge 1).setW "pl.go" g |>.charge 1

set_option maxHeartbeats 1000000 in
theorem colTail_run (r : State ℝ≥0) {cnt c base bid lv k M : ℕ} (hcnt : r.w "pl.cnt" = cnt)
    (hc : r.w "sp.c" = c) (hb : r.w "pl.base" = base) (hbid : r.w "sp.bid" = bid)
    (hlv : r.w "ds.lv" = lv) (hk : r.wa "dsl.sz" lv = k) (hk1 : 1 ≤ k) (hM : r.w "ds.M" = M)
    (hls : lv < r.wlen "dsl.sz") (hcap : base + cnt + c + 2 < r.cap) :
    Runs ops colTail r (fun r' => r' = colSt r (cnt + c) (base + (cnt + c)) bid lv (k - 1)
      (if M < cnt + c then 0 else if 0 < k - 1 then 1 else 0)) := by
  have h1 : 1 < r.cap := by omega
  unfold colTail
  apply runs_seq
  refine runs_wset (a := cnt + c) (evalW_add_of (by simp [hcnt]) (by simp [hc]) (by omega)) ?_
  apply runs_seq
  refine runs_wset (a := base + (cnt + c)) (evalW_add_of (x := base) (y := cnt + c) (by simp [hb])
    (by simp) (by simp; omega)) ?_
  apply runs_seq
  refine runs_wset (a := bid) (by simp [hbid]) ?_
  apply runs_seq
  refine runs_wstore (j := lv) (a := k - 1) (by simp [hlv]) (by simp [hlv, hls, hk, fit_of_lt h1])
    (by simpa using hls) ?_
  set s4 := ((((((((r.setW "pl.cnt" (cnt + c)).charge 1).setW "sp.w0" (base + (cnt + c))).charge
    1).setW "pl.pid" bid).charge 1).storeW "dsl.sz" lv (k - 1)).charge 1) with hs4
  have hs4M : s4.w "ds.M" = M := by simp [hs4, hM]
  have hs4c : s4.w "pl.cnt" = cnt + c := by simp [hs4]
  have hs4cap : s4.cap = r.cap := by simp [hs4]
  have hg : evalW s4 (lt (var "ds.M") (var "pl.cnt")) = some (if M < cnt + c then 1 else 0) :=
    evalW_lt_of (by simp [hs4M]) (by simp [hs4c]) (by rw [hs4cap]; exact h1)
  by_cases hMc : M < cnt + c
  · refine runs_ite_true (x := 1) (by rw [hg, if_pos hMc]) one_ne_zero ?_
    refine runs_wset (a := 0) (evalW_lit_of (by simp [hs4cap]; omega)) ?_
    simp only [colSt, if_pos hMc]; rfl
  · refine runs_ite_false (by rw [hg, if_neg hMc]) ?_
    refine runs_wset (a := if 0 < k - 1 then 1 else 0) ?_ ?_
    · have hsz : s4.wa "dsl.sz" lv = k - 1 := by simp [hs4]
      have hlv4 : s4.w "ds.lv" = lv := by simp [hs4, hlv]
      have hwl4 : lv < s4.wlen "dsl.sz" := by simp [hs4]; exact hls
      have hload : evalW (s4.charge 1) (load "dsl.sz" (var "ds.lv")) = some (k - 1) := by
        rw [evalW_load_of (j := lv) (by simp [hlv4]) (by simpa using hwl4)]
        simp [hsz]
      exact evalW_lt_of (evalW_lit_of (by simp [hs4cap]; omega)) hload (by simp [hs4cap]; exact h1)
    · simp only [colSt, if_neg hMc]; rfl

section ColSt

variable (r : State ℝ≥0) (cnt w0 pid lv k g : ℕ)

theorem colSt_wa (c : String) (hc : c ≠ "dsl.sz") : (colSt r cnt w0 pid lv k g).wa c = r.wa c := by
  funext x; simp [colSt, hc]

theorem colSt_sz (x : ℕ) : (colSt r cnt w0 pid lv k g).wa "dsl.sz" x = if x = lv then k else r.wa "dsl.sz" x := by
  simp [colSt]

theorem colSt_len : (colSt r cnt w0 pid lv k g).wlen = r.wlen ∧ (colSt r cnt w0 pid lv k g).vlen = r.vlen ∧
    (colSt r cnt w0 pid lv k g).va = r.va ∧ (colSt r cnt w0 pid lv k g).v = r.v ∧
    (colSt r cnt w0 pid lv k g).cap = r.cap ∧ (colSt r cnt w0 pid lv k g).procs = r.procs ∧
    (colSt r cnt w0 pid lv k g).cost = r.cost + 6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [colSt] <;> ring

theorem colSt_w (y : String) (hy : y ∉ plRegs) : (colSt r cnt w0 pid lv k g).w y = r.w y := by
  simp only [plRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  simp [colSt, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2]

theorem colSt_regs : (colSt r cnt w0 pid lv k g).w "pl.cnt" = cnt ∧
    (colSt r cnt w0 pid lv k g).w "sp.w0" = w0 ∧ (colSt r cnt w0 pid lv k g).w "pl.pid" = pid ∧
    (colSt r cnt w0 pid lv k g).w "pl.go" = g := by
  simp [colSt]

end ColSt

end Collect

section Pop

open Frontier.CHD.DIns Frontier.CHD.DB Frontier.CHD.DL Frontier.CHD.DList

variable {G : Graph} {s : Fin G.n}

theorem RecsOK.tail {q : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {p : ℕ × Block (Fin G.n) (WLab G s)} {rest : List (ℕ × Block (Fin G.n) (WLab G s))}
    (h : RecsOK q H V (p :: rest)) : RecsOK q H V rest := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨(List.nodup_cons.mp h1).2, fun x hx => h2 x (List.mem_cons_of_mem _ hx), ?_⟩
  simp only [List.map_cons, entIds_cons] at h3
  exact (List.nodup_append.mp h3).2.1

set_option maxHeartbeats 1000000 in
/-- popping the top block keeps the invariant for the rest -/
theorem splitPre_pop {r1 : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap lv bse w0 M pSel : ℕ} {Bd : WLab G s} {L : Live (Fin G.n) (WLab G s)}
    {b' : Block (Fin G.n) (WLab G s)} {bs' : List (Block (Fin G.n) (WLab G s))}
    {ext : List (ℕ × Block (Fin G.n) (WLab G s))}
    (hP : SplitPre r1 H V bcap lv bse w0 L ⟨M, Bd, b' :: bs'⟩ ext pSel) (cnt w0' pid g : ℕ) :
    SplitPre (colSt r1 cnt w0' pid lv bs'.length g) H V bcap lv bse w0' L ⟨M, Bd, bs'⟩ ext pSel := by
  obtain ⟨hwl, hvl, hva, hv, hcap, hpr, _⟩ := colSt_len r1 cnt w0' pid lv bs'.length g
  have hwa := colSt_wa r1 cnt w0' pid lv bs'.length g
  have hsz := colSt_sz r1 cnt w0' pid lv bs'.length g
  have hw := colSt_w r1 cnt w0' pid lv bs'.length g
  obtain ⟨_, hw0, _, _⟩ := colSt_regs r1 cnt w0' pid lv bs'.length g
  set r2 := colSt r1 cnt w0' pid lv bs'.length g with hr2
  have hrecs1 : recsOf r1 bse (b' :: bs') ++ ext =
      (r1.wa "dsl.stk" (bse + bs'.length), b') :: (recsOf r1 bse bs' ++ ext) := by
    rw [recsOf_cons]; rfl
  have hrecs2 : recsOf r2 bse bs' = recsOf r1 bse bs' :=
    recsOf_congr bse bs' (fun x _ => by rw [hwa _ (by simp)])
  have hR1 : RecsOK r1 H V (recsOf r1 bse bs' ++ ext) := by
    have := hP.recs; rw [hrecs1] at this; exact RecsOK.tail this
  have hR2 : RecsOK r2 H V (recsOf r2 bse bs' ++ ext) := by
    rw [hrecs2]
    exact recsOK_of_arrays hR1 (fun a ha => hwa a (by intro e; subst e; simp [bArrs] at ha))
      (by rw [hva]) (by rw [hva]) (by rw [hwl])
  have hfr1 : ∀ p ∈ recsOf r1 bse bs' ++ ext, p.1 < r1.w "blk.fresh" := by
    intro p hp; exact hP.fresh p (by rw [hrecs1]; exact List.mem_cons_of_mem _ hp)
  have hES : EntSame r1 r2 := ⟨hwa _ (by simp), by rw [hva], hwa _ (by simp), hwa _ (by simp),
    hwa _ (by simp), hwa _ (by simp), hwa _ (by simp)⟩
  have hkeep : ∀ y ∈ ["ds.lv", "ds.b", "ds.M", "blk.fresh"], r2.w y = r1.w y := by
    intro y hy
    refine hw y ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl <;> simp [plRegs]
  have hbcap : ∀ p ∈ recsOf r2 bse bs', p.1 < bcap := by
    intro p hp
    rw [hrecs2] at hp
    exact recsOf_bound hP.drep p (by rw [recsOf_cons]; exact List.mem_cons_of_mem _ hp)
  refine ⟨dRep_of_recs hR2 hbcap (by rw [hsz, if_pos rfl]) (by rw [hwl]; exact hP.drep.szb)
      (by rw [hwl]; have := hP.drep.stkb; simp at this ⊢; omega), hR2,
    liveRep_same hP.live hES (by rw [hwl]), blkArrs_same hP.barr hwl hvl,
    by rw [hrecs2, hkeep _ (by simp)]; exact hfr1, by rw [hkeep _ (by simp)]; exact hP.lv,
    by rw [hkeep _ (by simp)]; exact hP.b, by rw [hkeep _ (by simp)]; exact hP.M, hw0,
    by rw [hpr]; exact hP.procs, fun i hi => ?_, fun i hi => ?_, by rw [hwl, hcap]; exact hP.nxc,
    by rw [hcap]; exact hP.bc, by rw [hwl, hcap]; exact hP.stc, by rw [hwl, hcap]; exact hP.swc,
    by rw [hcap]; exact hP.Mc, by rw [hcap]; exact hP.c300⟩
  · rw [hwl] at hi
    obtain ⟨b1, b2, b3, b4, b5⟩ := hP.inb i hi
    exact ⟨by rw [hvl]; exact b1, by rw [hwl]; exact b2, by rw [hwl]; exact b3, by rw [hwl]; exact b4,
      by rw [hwl]; exact b5⟩
  · rw [hwl] at hi ⊢
    have := hP.key i hi
    simpa [hwa "ent.key" (by simp)] using this

end Pop


/-! ## Collect loop: invariant and output -/

section ColLoop

open Frontier.CHD.DIns Frontier.CHD.DB Frontier.CHD.DL Frontier.CHD.MLab Frontier.CHD.LabTab
  Frontier.CHD.DList

variable {G : Graph} {s : Fin G.n}

theorem entIds_eq_allEnts (bs : List (Block (Fin G.n) (WLab G s))) :
    entIds bs = (allEnts bs).map (·.id) := by
  simp [entIds, allEnts, List.flatMap, List.map_flatten, Function.comp_def]

theorem map_snd_recsOf (st : State ℝ≥0) (bse : ℕ) (P : List (Block (Fin G.n) (WLab G s))) :
    (recsOf st bse P).map Prod.snd = P := by
  unfold recsOf; rw [List.map_snd_zip (by simp)]

theorem entIds_recs (st : State ℝ≥0) (bse : ℕ) (P : List (Block (Fin G.n) (WLab G s)))
    (ext : List (ℕ × Block (Fin G.n) (WLab G s))) :
    entIds ((recsOf st bse P ++ ext).map Prod.snd) = entIds P ++ entIds (ext.map Prod.snd) := by
  rw [List.map_append, map_snd_recsOf, entIds_append]

/-- cost constant of one round of the collect loop -/
def Kcol : ℕ := Knc + 11

/-- **invariant of the collect loop** (at the loop test): `acc` collected at `sel.w[base, …)`,
`cur` = the current (unprepared) block list of the structure -/
structure ColInv (q : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (bcap lv bse base M : ℕ) (Bd : WLab G s) (L : Live (Fin G.n) (WLab G s))
    (ext : List (ℕ × Block (Fin G.n) (WLab G s))) (pSel : ℕ) (acc : List (Entry (Fin G.n) (WLab G s)))
    (cur : List (Block (Fin G.n) (WLab G s))) : Prop where
  pre : SplitPre q H V bcap lv bse (base + acc.length) L ⟨M, Bd, cur⟩ ext pSel
  spell : DList.Spells q "sel.w" base (acc.map (·.id))
  cntreg : q.w "pl.cnt" = acc.length
  basereg : q.w "pl.base" = base
  nd : (acc.map (·.id) ++ entIds ((recsOf q bse cur ++ ext).map Prod.snd)).Nodup
  ents : ∀ e ∈ acc, EntRep q H V e.id e.key e.val ∧ e.IsLive L ∧ e.id < q.wlen "ent.nxt"
  fcap : q.w "blk.fresh" + (prepList L M acc.length cur).2 ≤ bcap
  scap : bse + cur.length + (prepList L M acc.length cur).2 ≤ q.wlen "dsl.stk"
  wcap : base + 6 * (acc.length + (allEnts cur).length) + 60 ≤ q.wlen "sel.w"

/-- **output of the collect loop**: `accF` collected, `restF` = the remaining blocks -/
structure ColOut (q r : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (bcap lv bse base M : ℕ) (Bd : WLab G s) (L : Live (Fin G.n) (WLab G s))
    (ext : List (ℕ × Block (Fin G.n) (WLab G s))) (pSel : ℕ)
    (accF : List (Entry (Fin G.n) (WLab G s))) (restF : List (Block (Fin G.n) (WLab G s)))
    (pcost : ℕ) : Prop where
  pre : SplitPre r H V bcap lv bse (base + accF.length) L ⟨M, Bd, restF⟩ ext pSel
  spell : DList.Spells r "sel.w" base (accF.map (·.id))
  cntreg : r.w "pl.cnt" = accF.length
  basereg : r.w "pl.base" = base
  nd : (accF.map (·.id) ++ entIds ((recsOf r bse restF ++ ext).map Prod.snd)).Nodup
  ents : ∀ e ∈ accF, EntRep r H V e.id e.key e.val ∧ e.IsLive L ∧ e.id < r.wlen "ent.nxt"
  pid : r.w "pl.pid" ∉ (recsOf r bse restF ++ ext).map Prod.fst
  pidf : r.w "pl.pid" < r.w "blk.fresh"
  pidb : r.w "pl.pid" < bcap
  wcap : base + 6 * accF.length + 60 ≤ r.wlen "sel.w"
  scap : bse + restF.length + 1 ≤ r.wlen "dsl.stk"
  go : r.w "pl.go" = 0
  unch : Unchanged q r splitWA ["blk.len"] (splitWR ++ plRegs) entLessV
  wlen : r.wlen = q.wlen
  vlen : r.vlen = q.vlen
  low : ∀ x, x < base → r.wa "sel.w" x = q.wa "sel.w" x
  stk : ∀ x, x < bse → r.wa "dsl.stk" x = q.wa "dsl.stk" x
  sz : ∀ l, l ≠ lv → r.wa "dsl.sz" l = q.wa "dsl.sz" l
  fr1 : q.w "blk.fresh" ≤ r.w "blk.fresh"
  fr2 : r.w "blk.fresh" ≤ q.w "blk.fresh" + pcost

theorem subperm_map' {β γ : Type*} (f : β → γ) {l₁ l₂ : List β} (h : l₁.Subperm l₂) :
    (l₁.map f).Subperm (l₂.map f) := by
  obtain ⟨l, hp, hs⟩ := h
  exact ⟨l.map f, hp.map f, hs.map f⟩

theorem spells_append {st : State ℝ≥0} {arr : String} {base : ℕ} {l1 l2 : List ℕ}
    (h1 : DList.Spells st arr base l1) (h2 : DList.Spells st arr (base + l1.length) l2) :
    DList.Spells st arr base (l1 ++ l2) := by
  intro i hi
  by_cases hia : i < l1.length
  · rw [List.getElem_append_left hia]; exact h1 i hia
  · rw [List.getElem_append_right (by omega)]
    have := h2 (i - l1.length) (by simp at hi; omega)
    rw [show base + l1.length + (i - l1.length) = base + i by omega] at this
    exact this

theorem spells_congr {st st' : State ℝ≥0} {arr : String} {base : ℕ} {l : List ℕ}
    (h : ∀ i, i < l.length → st'.wa arr (base + i) = st.wa arr (base + i))
    (hs : DList.Spells st arr base l) : DList.Spells st' arr base l := by
  intro i hi; rw [h i hi]; exact hs i hi

/-- facts after one round of the collect loop -/
structure ColRound (q r : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (bcap lv bse base M : ℕ) (Bd : WLab G s) (L : Live (Fin G.n) (WLab G s))
    (ext : List (ℕ × Block (Fin G.n) (WLab G s))) (pSel : ℕ) (acc : List (Entry (Fin G.n) (WLab G s)))
    (b' : Block (Fin G.n) (WLab G s)) (bs' : List (Block (Fin G.n) (WLab G s))) (pc : ℕ) : Prop where
  pre : SplitPre r H V bcap lv bse (base + (acc ++ liveOf L b'.ents).length) L ⟨M, Bd, bs'⟩ ext pSel
  spell : DList.Spells r "sel.w" base ((acc ++ liveOf L b'.ents).map (·.id))
  cntreg : r.w "pl.cnt" = (acc ++ liveOf L b'.ents).length
  basereg : r.w "pl.base" = base
  nd : ((acc ++ liveOf L b'.ents).map (·.id) ++ entIds ((recsOf r bse bs' ++ ext).map Prod.snd)).Nodup
  ents : ∀ e ∈ acc ++ liveOf L b'.ents, EntRep r H V e.id e.key e.val ∧ e.IsLive L ∧
    e.id < r.wlen "ent.nxt"
  pid : r.w "pl.pid" ∉ (recsOf r bse bs' ++ ext).map Prod.fst
  pidf : r.w "pl.pid" < r.w "blk.fresh"
  pidb : r.w "pl.pid" < bcap
  go : r.w "pl.go" = if M < (acc ++ liveOf L b'.ents).length then 0 else if 0 < bs'.length then 1 else 0
  unch : Unchanged q r splitWA ["blk.len"] (splitWR ++ plRegs) entLessV
  wlen : r.wlen = q.wlen
  vlen : r.vlen = q.vlen
  low : ∀ x, x < base → r.wa "sel.w" x = q.wa "sel.w" x
  stk : ∀ x, x < bse → r.wa "dsl.stk" x = q.wa "dsl.stk" x
  sz : ∀ l, l ≠ lv → r.wa "dsl.sz" l = q.wa "dsl.sz" l
  fr1 : q.w "blk.fresh" ≤ r.w "blk.fresh"
  fr2 : r.w "blk.fresh" ≤ q.w "blk.fresh" + pc
  cost : r.cost ≤ q.cost + (Ksp + 1) * pc + Knc * (b'.ents.length + 1) + 10

theorem plR_nw {y : String} (hy : y ∈ ["pl.cnt", "pl.base", "pl.pid", "pl.go"]) : y ∉ splitWR := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl <;>
    simp [splitWR, DList.walkRegs, myRegs, lessRegs, csRegs, selRegs, entLessW, fsX, fsY, LReg.ws,
      linkRegs, DList.buildRegs]

set_option maxHeartbeats 4000000 in
theorem col_round (hH : GoodHist (s := s) H V) (pSel : ℕ) (q : State ℝ≥0)
    {bcap lv bse base M : ℕ} {Bd : WLab G s} {L : Live (Fin G.n) (WLab G s)}
    {ext : List (ℕ × Block (Fin G.n) (WLab G s))} {acc : List (Entry (Fin G.n) (WLab G s))}
    {b b' : Block (Fin G.n) (WLab G s)} {rest bs' : List (Block (Fin G.n) (WLab G s))}
    (hI : ColInv q H V bcap lv bse base M Bd L ext pSel acc (b :: rest)) (h : ¬ M < acc.length)
    (hp : (prep L M (b :: rest)).1 = b' :: bs') :
    Runs realOps (colBody pSel) (q.charge 1) (fun r =>
      ColRound q r H V bcap lv bse base M Bd L ext pSel acc b' bs' (prep L M (b :: rest)).2) := by
  set pc := (prep L M (b :: rest)).2 with hpcd
  have hPL := prepList_cons_le (cnt := acc.length) h hp
  have hfc := hI.fcap
  have hsc := hI.scap
  have hwc := hI.wcap
  rw [hPL] at hfc hsc
  simp only [allEnts_cons', List.length_append, List.length_cons] at hwc hsc
  have hswc := hI.pre.swc
  unfold colBody
  apply runs_seq
  refine (prepTop_spec hH pSel (q.charge 1) (hI.pre.charge 1) (by simp; omega) (by simp; omega)
    (by simp; omega)).mono (fun r1 ⟨b'', rest'', hp', hO⟩ => ?_)
  rw [hp] at hp'
  obtain ⟨e1, e2⟩ := List.cons.inj hp'
  subst e1 e2
  set q1 := ((q.charge 1).setW "dsp.go" 1).charge 1 with hq1
  set c' := (liveOf L b'.ents).length with hc'd
  set bid' := r1.wa "dsl.stk" (bse + bs'.length) with hbid'd
  have hq1w : ∀ y, y ≠ "dsp.go" → q1.w y = q.w y := fun y hy => by simp [hq1, hy]
  have hr1w : ∀ y ∈ ["pl.cnt", "pl.base", "pl.pid", "pl.go"], r1.w y = q.w y := fun y hy => by
    rw [hO.unch.wreg y (plR_nw hy), hq1w y (by simp at hy; rcases hy with rfl | rfl | rfl | rfl <;> simp)]
  have hcapr1 : r1.cap = q.cap := by rw [hO.unch.cap]; simp [hq1]
  have hwlr1 : r1.wlen = q.wlen := by rw [hO.wlen]; simp [hq1]
  have hvlr1 : r1.vlen = q.vlen := by rw [hO.vlen]; simp [hq1]
  obtain ⟨hB1, hbid1⟩ := top_blkRep hO.pre.drep
  have hsz1 : r1.wa "dsl.sz" lv = bs'.length + 1 := by simpa using hO.pre.drep.sz
  have hc'le : c' ≤ b'.ents.length := length_liveOf_le L b'.ents
  have hAE : (allEnts (b' :: bs')).length ≤ (allEnts (b :: rest)).length := by
    have := prep_allEnts_le L M (b :: rest); rwa [hp] at this
  simp only [allEnts_cons', List.length_append] at hAE
  refine (colTail_run r1 (cnt := acc.length) (c := c') (base := base) (bid := bid') (lv := lv)
    (k := bs'.length + 1) (M := M) (by rw [hr1w _ (by simp)]; exact hI.cntreg) hO.c
    (by rw [hr1w _ (by simp)]; exact hI.basereg) hO.bid hO.pre.lv hsz1 (by omega) hO.pre.M
    hO.pre.drep.szb (by rw [hcapr1]; omega)).mono (fun r2 hr2 => ?_)
  simp only [Nat.add_sub_cancel] at hr2
  subst hr2
  set g := (if M < acc.length + c' then 0 else if 0 < bs'.length then 1 else 0) with hgd
  obtain ⟨hwl2, hvl2, hva2, hv2, hcap2, hpr2, hcost2⟩ :=
    colSt_len r1 (acc.length + c') (base + (acc.length + c')) bid' lv bs'.length g
  have hwa2 := colSt_wa r1 (acc.length + c') (base + (acc.length + c')) bid' lv bs'.length g
  have hsz2 := colSt_sz r1 (acc.length + c') (base + (acc.length + c')) bid' lv bs'.length g
  have hw2 := colSt_w r1 (acc.length + c') (base + (acc.length + c')) bid' lv bs'.length g
  obtain ⟨hcnt2, hw02, hpid2, hgo2⟩ :=
    colSt_regs r1 (acc.length + c') (base + (acc.length + c')) bid' lv bs'.length g
  set r2 := colSt r1 (acc.length + c') (base + (acc.length + c')) bid' lv bs'.length g with hr2d
  have hlen' : (acc ++ liveOf L b'.ents).length = acc.length + c' := by simp [hc'd]
  -- the representation of the popped structure
  have hP2 : SplitPre r2 H V bcap lv bse (base + (acc ++ liveOf L b'.ents).length) L ⟨M, Bd, bs'⟩ ext
      pSel := by
    rw [hlen']; exact splitPre_pop hO.pre _ _ _ _
  -- records
  have hrecs1 : recsOf r1 bse (b' :: bs') ++ ext = (bid', b') :: (recsOf r1 bse bs' ++ ext) := by
    rw [recsOf_cons]; rfl
  have hrecs2 : recsOf r2 bse bs' = recsOf r1 bse bs' :=
    recsOf_congr bse bs' (fun x _ => by rw [hwa2 _ (by simp)])
  have hR1 := hO.pre.recs
  rw [hrecs1] at hR1
  -- entry arrays unchanged q → r2
  have hESq1 : EntSame q r1 := by
    have u := hO.unch
    have hq1a : ∀ c, q1.wa c = q.wa c := fun c => by simp [hq1]
    have hq1v : ∀ c, q1.va c = q.va c := fun c => by simp [hq1]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [(u.warr _ (by simp [splitWA])).1, hq1a]
    · rw [(u.varr _ (by simp)).1, hq1v]
    · rw [(u.warr _ (by simp [splitWA])).1, hq1a]
    · rw [(u.warr _ (by simp [splitWA])).1, hq1a]
    · rw [(u.warr _ (by simp [splitWA])).1, hq1a]
    · rw [(u.warr _ (by simp [splitWA])).1, hq1a]
    · rw [(u.warr _ (by simp [splitWA])).1, hq1a]
  have hES12 : EntSame r1 r2 := ⟨hwa2 _ (by simp), by rw [hva2], hwa2 _ (by simp), hwa2 _ (by simp),
    hwa2 _ (by simp), hwa2 _ (by simp), hwa2 _ (by simp)⟩
  refine ⟨hP2, ?_, by rw [hcnt2, hlen'], by rw [hw2 _ (by simp [plRegs]), hr1w _ (by simp)]; exact hI.basereg,
    ?_, ?_, ?_, ?_, ?_, by rw [hgo2, hgd, hlen'], ?_, by rw [hwl2, hwlr1], by rw [hvl2, hvlr1], ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · -- spell
    rw [List.map_append]
    have hs2 : DList.Spells r1 "sel.w" (base + (acc.map (·.id)).length) ((liveOf L b'.ents).map (·.id)) := by
      rw [List.length_map]; exact hO.spell
    refine spells_append (spells_congr (fun i hi => ?_) hI.spell) (spells_congr (fun i hi => ?_) hs2)
    · rw [hwa2 _ (by simp), hO.low (base + i) (by simp at hi; omega)]; simp [hq1]
    · rw [hwa2 _ (by simp)]
  · -- nd
    rw [hrecs2, entIds_recs]
    have hnd0 := hI.nd
    rw [entIds_recs] at hnd0
    have hsub1 : (entIds (b' :: bs')).Subperm (entIds (b :: rest)) := by
      rw [entIds_eq_allEnts, entIds_eq_allEnts]
      have := prep_subperm L M (b :: rest); rw [hp] at this
      exact subperm_map' _ this
    have hsub2 : ((liveOf L b'.ents).map (·.id) ++ entIds bs').Sublist (entIds (b' :: bs')) := by
      rw [entIds_cons]
      exact (List.Sublist.map _ (List.filter_sublist)).append (List.Sublist.refl _)
    have key : List.Subperm (((liveOf L b'.ents).map (·.id) ++ entIds bs') ++ entIds (ext.map Prod.snd))
        (entIds (b :: rest) ++ entIds (ext.map Prod.snd)) :=
      (hsub2.subperm.trans hsub1).append (List.Subperm.refl _)
    have eT : (acc ++ liveOf L b'.ents).map (·.id) ++ (entIds bs' ++ entIds (ext.map Prod.snd)) =
        acc.map (·.id) ++ (((liveOf L b'.ents).map (·.id) ++ entIds bs') ++ entIds (ext.map Prod.snd)) := by
      simp [List.append_assoc]
    rw [eT]
    exact subperm_nodup ((List.Subperm.refl _).append key) hnd0
  · -- ents
    intro e he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨h1, h2, h3⟩ := hI.ents e he
      exact ⟨entRep_same (entRep_same h1 hESq1) hES12, h2, by rw [hwl2, hwlr1]; exact h3⟩
    · refine ⟨entRep_same (hB1.2.2.1 e (List.mem_of_mem_filter he)) hES12,
        of_decide_eq_true (List.mem_filter.mp he).2, ?_⟩
      rw [hwl2]
      exact hB1.2.1.lt_len e.id (List.mem_map_of_mem (List.mem_of_mem_filter he))
  · -- pid
    rw [hpid2, hrecs2]
    exact (List.nodup_cons.mp hR1.1).1
  · -- pidf
    rw [hpid2, hw2 _ (by simp [plRegs])]
    exact hO.pre.fresh (bid', b') (by rw [hrecs1]; exact List.mem_cons_self)
  · rw [hpid2]; exact hbid1
  · -- unch
    have u0 : Unchanged q q1 splitWA ["blk.len"] (splitWR ++ plRegs) entLessV := by
      rw [hq1, unch_charge', unch_setW' (by simp [splitWR]), unch_charge']
      exact Unchanged.refl _ _ _ _ _
    have u1 : Unchanged q1 r1 splitWA ["blk.len"] (splitWR ++ plRegs) entLessV :=
      hO.unch.mono (List.Subset.refl _) (List.Subset.refl _) (fun y hy => List.mem_append_left _ hy)
        (List.Subset.refl _)
    have u2 : Unchanged r1 r2 splitWA ["blk.len"] (splitWR ++ plRegs) entLessV := by
      refine ⟨fun c hc => ⟨hwa2 c (by intro h; apply hc; rw [h]; simp [splitWA]), by rw [hwl2]⟩,
        fun c _ => ⟨by rw [hva2], by rw [hvl2]⟩, fun y hy => hw2 y ?_, fun y _ => by rw [hv2], hcap2, hpr2⟩
      intro h; apply hy; exact List.mem_append_right _ h
    exact u0.trans (u1.trans u2)
  · intro x hx
    rw [hwa2 _ (by simp), hO.low x (by omega)]; simp [hq1]
  · intro x hx
    rw [hwa2 _ (by simp), hO.stk x hx]; simp [hq1]
  · intro l hl
    rw [hsz2, if_neg hl, hO.sz l hl]; simp [hq1]
  · rw [hw2 _ (by simp [plRegs])]; have := hO.fr1; simp [hq1] at this; exact this
  · rw [hw2 _ (by simp [plRegs])]; have := hO.fr2; simp [hq1] at this; exact this
  · rw [hcost2]
    have := hO.cost
    simp only [hq1, State.charge_cost, State.setW_cost] at this
    simp only [Ksp, Knc] at this ⊢
    omega

/-- a round's facts give the loop output when the loop stops after it -/
theorem colOut_of_round {q r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap lv bse base M pSel : ℕ} {Bd : WLab G s} {L : Live (Fin G.n) (WLab G s)}
    {ext : List (ℕ × Block (Fin G.n) (WLab G s))} {acc : List (Entry (Fin G.n) (WLab G s))}
    {b' : Block (Fin G.n) (WLab G s)} {bs' : List (Block (Fin G.n) (WLab G s))} {pc pcost : ℕ}
    (hR : ColRound q r H V bcap lv bse base M Bd L ext pSel acc b' bs' pc) (hpc : pc ≤ pcost)
    (hgo : r.w "pl.go" = 0)
    (hwc : base + 6 * (acc ++ liveOf L b'.ents).length + 60 ≤ r.wlen "sel.w")
    (hsc : bse + bs'.length + 1 ≤ r.wlen "dsl.stk") :
    ColOut q (r.charge 1) H V bcap lv bse base M Bd L ext pSel (acc ++ liveOf L b'.ents) bs' pcost := by
  refine ⟨hR.pre.charge 1, hR.spell, by simpa using hR.cntreg, by simpa using hR.basereg, hR.nd,
    hR.ents, hR.pid, by simpa using hR.pidf, by simpa using hR.pidb, by simpa using hwc,
    by simpa using hsc, by simpa using hgo, (unch_charge' 1).mpr hR.unch, by simpa using hR.wlen,
    by simpa using hR.vlen, fun x hx => by simpa using hR.low x hx, fun x hx => by simpa using hR.stk x hx,
    fun l hl => by simpa using hR.sz l hl, by simpa using hR.fr1, by have := hR.fr2; simp; omega⟩

set_option maxHeartbeats 4000000 in
/-- **the collect loop** refines `collect` over `prepList` (block by block) -/
theorem col_loop (hH : GoodHist (s := s) H V) (pSel : ℕ) {bcap lv bse base M : ℕ} {Bd : WLab G s}
    {L : Live (Fin G.n) (WLab G s)} {ext : List (ℕ × Block (Fin G.n) (WLab G s))} :
    ∀ (cnt : ℕ) (cur : List (Block (Fin G.n) (WLab G s))) (q : State ℝ≥0)
      (acc : List (Entry (Fin G.n) (WLab G s))), acc.length = cnt → ¬ M < cnt → cur ≠ [] →
      ColInv q H V bcap lv bse base M Bd L ext pSel acc cur → q.w "pl.go" = 1 →
      Runs realOps (colLoop pSel) q (fun r =>
        ColOut q r H V bcap lv bse base M Bd L ext pSel (collect L M acc (prepList L M cnt cur).1).1
          (collect L M acc (prepList L M cnt cur).1).2.1 (prepList L M cnt cur).2 ∧
        r.cost ≤ q.cost + Kcol * ((prepList L M cnt cur).2 +
          (collect L M acc (prepList L M cnt cur).1).2.2.2 +
          (collect L M acc (prepList L M cnt cur).1).2.2.1)) := by
  intro cnt cur
  induction cnt, cur using prepList.induct (L := L) (M := M) with
  | case1 cnt => intro q acc _ _ h; exact absurd rfl h
  | case2 cnt b rest h => intro q acc _ h' _; exact absurd h h'
  | case3 cnt b rest h hp => exact absurd hp (prep_ne_nil L M _ (List.cons_ne_nil _ _))
  | case4 cnt b rest h b' bs' hp ih =>
    intro q acc hlen _ _ hI hgo
    subst hlen
    have hPL := prepList_cons_le (cnt := acc.length) h hp
    set pc := (prep L M (b :: rest)).2 with hpcd
    set c' := (liveOf L b'.ents).length with hc'd
    have hlen' : (acc ++ liveOf L b'.ents).length = acc.length + c' := by simp [hc'd]
    refine runs_while_step (x := 1) (by simp [hgo]) one_ne_zero ?_
    refine (col_round hH pSel q hI h hp).mono (fun r hR => ?_)
    have hfc := hI.fcap
    have hsc := hI.scap
    have hwc := hI.wcap
    rw [hPL] at hfc hsc
    have hLen := prep_length_le L M (b :: rest)
    rw [hp] at hLen
    have hAE : (allEnts (b' :: bs')).length ≤ (allEnts (b :: rest)).length := by
      have := prep_allEnts_le L M (b :: rest); rwa [hp] at this
    simp only [allEnts_cons', List.length_append, List.length_cons] at hAE hwc hsc hLen
    have hc'le : c' ≤ b'.ents.length := length_liveOf_le L b'.ents
    have hwlr := hR.wlen
    have hgoR := hR.go
    rw [hlen'] at hgoR
    have hK : Ksp + 1 ≤ Kcol ∧ Knc + 10 ≤ Kcol := by simp [Ksp, Knc, Kcol]
    by_cases hM' : M < acc.length + c'
    · -- the count exceeds `M`: stop with `bs'` left
      have hgo0 : r.w "pl.go" = 0 := by rw [hgoR, if_pos hM']
      have hX : prepList L M (acc.length + c') bs' = (bs', 0) := prepList_of_lt hM' bs'
      refine runs_while_exit (by simp [hgo0]) ⟨?_, ?_⟩
      · rw [hPL]
        simp only [hX, collect_cons, hlen', if_pos hM']
        exact colOut_of_round hR (by omega) hgo0 (by rw [hwlr, hlen']; omega) (by rw [hwlr]; omega)
      · rw [hPL]
        simp only [hX, collect_cons, hlen', if_pos hM', State.charge_cost]
        have := hR.cost
        simp only [Kcol, Ksp, Knc] at this ⊢; omega
    · by_cases hbs : bs' = []
      · -- the stack is exhausted
        subst hbs
        have hgo0 : r.w "pl.go" = 0 := by rw [hgoR, if_neg hM']; simp
        refine runs_while_exit (by simp [hgo0]) ⟨?_, ?_⟩
        · rw [hPL]
          simp only [prepList_nil', collect_cons, hlen', if_neg hM', collect_nil']
          exact colOut_of_round hR (by omega) hgo0 (by rw [hwlr, hlen']; omega)
            (by rw [hwlr]; first | omega | (simp; omega))
        · rw [hPL]
          simp only [prepList_nil', collect_cons, hlen', if_neg hM', collect_nil', State.charge_cost]
          have := hR.cost
          simp only [Kcol, Ksp, Knc] at this ⊢; omega
      · -- go on
        have hgo1 : r.w "pl.go" = 1 := by
          rw [hgoR, if_neg hM', if_pos (List.length_pos_of_ne_nil hbs)]
        have hI' : ColInv r H V bcap lv bse base M Bd L ext pSel (acc ++ liveOf L b'.ents) bs' := by
          refine ⟨hR.pre, hR.spell, hR.cntreg, hR.basereg, hR.nd, hR.ents, ?_, ?_, ?_⟩
          · have := hR.fr2; rw [hlen']; omega
          · rw [hwlr, hlen']; omega
          · rw [hwlr]; simp only [List.length_append]; omega
        refine (ih r (acc ++ liveOf L b'.ents) hlen' hM' hbs hI' hgo1).mono (fun r' ⟨hO', hc'⟩ => ?_)
        rw [hPL]
        simp only [collect_cons, hlen', if_neg hM']
        refine ⟨?_, ?_⟩
        · obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19,
            o20⟩ := hO'
          refine ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, hR.unch.trans o13, by rw [o14, hR.wlen],
            by rw [o15, hR.vlen], fun x hx => by rw [o16 x hx, hR.low x hx],
            fun x hx => by rw [o17 x hx, hR.stk x hx], fun l hl => by rw [o18 l hl, hR.sz l hl],
            le_trans hR.fr1 o19, ?_⟩
          have := hR.fr2; omega
        · have := hR.cost
          simp only [Kcol, Ksp, Knc] at this hc' ⊢; omega

end ColLoop

/-! ## The separator output: slot `B_i[l]` -/

section Sep

open Frontier.CHD.DIns Frontier.CHD.DB Frontier.CHD.MLab Frontier.CHD.LabTab

variable {G : Graph} {s : Fin G.n}

/-- the level-`l` bound label arrays of D (agent-04's layout) hold the machine label `x` -/
def BdAt (st : State ℝ≥0) (l : ℕ) (x : MLabel G) : Prop :=
  st.va "dsl.bl" l = x.len ∧ st.wa "dsl.bh" l = x.hops ∧ st.wa "dsl.bv" l = x.v ∧
    st.wa "dsl.be" l = encE x.e ∧ st.wa "dsl.br" l = x.ver

/-- the level-`l` bound of D holds the label `b` (flag `dsl.bf[l] = 0` iff `b = ⊤`); same shape as
`SlotHolds` -/
def BdHolds (st : State ℝ≥0) (l : ℕ) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (b : WLab G s) : Prop :=
  (st.wa "dsl.bf" l = 0 ↔ b = ⊤) ∧ ∀ q : List (Fin G.m), b = ((toW q : WalkOrd G s) : WLab G s) →
    ∃ x : MLabel G, BdAt st l x ∧ Rep (s := s) H V x q

/-- the bound arrays are long enough for level `l` -/
structure BdLens (st : State ℝ≥0) (l : ℕ) : Prop where
  bl : l < st.vlen "dsl.bl"
  bh : l < st.wlen "dsl.bh"
  bv : l < st.wlen "dsl.bv"
  be : l < st.wlen "dsl.be"
  br : l < st.wlen "dsl.br"
  bf : l < st.wlen "dsl.bf"

theorem BdHolds.of_eq {st r : State ℝ≥0} {l : ℕ} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {b : WLab G s} (h : BdHolds st l H V b)
    (hw : ∀ a ∈ ["dsl.bh", "dsl.bv", "dsl.be", "dsl.br", "dsl.bf"], r.wa a = st.wa a)
    (hv : r.va "dsl.bl" = st.va "dsl.bl") : BdHolds r l H V b := by
  refine ⟨by rw [hw "dsl.bf" (by simp)]; exact h.1, fun q hq => ?_⟩
  obtain ⟨x, ⟨x1, x2, x3, x4, x5⟩, hx⟩ := h.2 q hq
  exact ⟨x, ⟨by rw [hv]; exact x1, by rw [hw "dsl.bh" (by simp)]; exact x2, by rw [hw "dsl.bv" (by simp)]; exact x3,
    by rw [hw "dsl.be" (by simp)]; exact x4, by rw [hw "dsl.br" (by simp)]; exact x5⟩, hx⟩

/-- `B_i[l] := D.Bd` (exhausted pull; uses the slot index register `sl.i`) -/
def copyBd0 : Stmt :=
  seq (vset "fs.Xl" (.load "dsl.bl" (var "ds.lv")))
  (seq (wset "fs.Xh" (load "dsl.bh" (var "ds.lv")))
  (seq (wset "fs.Xv" (load "dsl.bv" (var "ds.lv")))
  (seq (wset "fs.Xe" (load "dsl.be" (var "ds.lv")))
  (seq (wset "fs.Xr" (load "dsl.br" (var "ds.lv")))
  (seq (wset "pl.f" (load "dsl.bf" (var "ds.lv")))
  (seq (wset "sl.i" (add (mul (var "ds.lv") (lit 4)) (lit 3)))
       (storeSlot fsX "pl.f")))))))

/-- `B_i[l] := label of entry sp.med` (cut pull; uses `sl.i`) -/
def copyMed0 : Stmt :=
  seq (loadA DIns.entA "sp.med" fsX)
  (seq (wset "pl.f" (lit 1))
  (seq (wset "sl.i" (add (mul (var "ds.lv") (lit 4)) (lit 3)))
       (storeSlot fsX "pl.f")))

/-- registers written by the raw separator copies -/
def sepRegs0 : List String := fsX.ws ++ ["pl.f", "sl.i"]

/-- `copyBd0` with `sl.i` (a spine register) saved and restored -/
def copyBd : Stmt := seq (wset "pl.sli" (var "sl.i")) (seq copyBd0 (wset "sl.i" (var "pl.sli")))
/-- `copyMed0` with `sl.i` saved and restored -/
def copyMed : Stmt := seq (wset "pl.sli" (var "sl.i")) (seq copyMed0 (wset "sl.i" (var "pl.sli")))

/-- registers written by the separator copies -/
def sepRegs : List String := fsX.ws ++ ["pl.f", "pl.sli"]

theorem Runs.and' {ops : VOps ℝ≥0} {c : Stmt} {st : State ℝ≥0} {P Q : State ℝ≥0 → Prop}
    (hp : Runs ops c st P) (hq : Runs ops c st Q) : Runs ops c st (fun r => P r ∧ Q r) := by
  obtain ⟨f, r, h1, hP⟩ := hp
  obtain ⟨f', r', h1', hQ⟩ := hq
  have := exec_det ops h1 h1'
  subst this
  exact ⟨f, r, h1, hP, hQ⟩

theorem storeSlot_len (K : LReg) (kf : String) (st : State ℝ≥0) {i : ℕ} (hi : st.w "sl.i" = i)
    (hl : SlotLens st i) :
    Runs realOps (storeSlot K kf) st (fun r => r.wlen = st.wlen ∧ r.vlen = st.vlen) := by
  rw [storeSlot_eq]
  refine runs_seq (runs_vstore (j := i) (a := st.v K.l) (by rw [evalW_var, hi]) (by rw [evalV_var']) hl.l ?_)
  refine (storeSlotW_spec (ops := realOps) K kf _ (i := i) (by simpa using hi) (by simpa using hl.h)
    (by simpa using hl.v) (by simpa using hl.e) (by simpa using hl.r) (by simpa using hl.f)).mono ?_
  rintro r ⟨-, -, -, -, -, -, -, evl, ewl, -⟩
  exact ⟨by rw [ewl]; rfl, by rw [evl]; rfl⟩

set_option maxHeartbeats 1000000 in
theorem copyBd0_spec (q : State ℝ≥0) {lv : ℕ} (hlv : q.w "ds.lv" = lv) (hBL : BdLens q lv)
    {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {b : WLab G s} (hB : BdHolds q lv H V b)
    (hSL : SlotLens q (4 * lv + 3)) (hcap : 4 * lv + 4 < q.cap) :
    Runs realOps copyBd0 q (fun r => SlotHolds r (4 * lv + 3) H V b ∧
      (∀ j, j ≠ 4 * lv + 3 → r.va "sl.l" j = q.va "sl.l" j ∧ ∀ a ∈ slotW, r.wa a j = q.wa a j) ∧
      Unchanged q r slotW ["sl.l"] sepRegs0 [fsX.l] ∧ r.cost = q.cost + 13 ∧ r.wlen = q.wlen ∧
      r.vlen = q.vlen) := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hBL
  unfold copyBd0
  apply runs_seq
  refine runs_vset (a := q.va "dsl.bl" lv) (evalV_load_of (by simp [hlv]) l1) ?_
  apply runs_seq
  refine runs_wset (a := q.wa "dsl.bh" lv) (evalW_load_of (by simp [hlv]) (by simpa using l2)) ?_
  apply runs_seq
  refine runs_wset (a := q.wa "dsl.bv" lv) (evalW_load_of (by simp [hlv]) (by simpa using l3)) ?_
  apply runs_seq
  refine runs_wset (a := q.wa "dsl.be" lv) (evalW_load_of (by simp [hlv]) (by simpa using l4)) ?_
  apply runs_seq
  refine runs_wset (a := q.wa "dsl.br" lv) (evalW_load_of (by simp [hlv]) (by simpa using l5)) ?_
  apply runs_seq
  refine runs_wset (a := q.wa "dsl.bf" lv) (evalW_load_of (by simp [hlv]) (by simpa using l6)) ?_
  apply runs_seq
  refine runs_wset (a := 4 * lv + 3) ?_ ?_
  · have f1 : fit q.cap (lv * 4) = some (lv * 4) := fit_of_lt (by omega)
    have f2 : fit q.cap 3 = some 3 := fit_of_lt (by omega)
    have f3 : fit q.cap 4 = some 4 := fit_of_lt (by omega)
    have f4 : fit q.cap (lv * 4 + 3) = some (lv * 4 + 3) := fit_of_lt (by omega)
    simp [hlv, f1, f2, f3, f4] <;> omega
  set q7 := (((((((((((((q.setV "fs.Xl" (q.va "dsl.bl" lv)).charge 1).setW "fs.Xh" (q.wa "dsl.bh" lv)).charge
    1).setW "fs.Xv" (q.wa "dsl.bv" lv)).charge 1).setW "fs.Xe" (q.wa "dsl.be" lv)).charge 1).setW "fs.Xr"
    (q.wa "dsl.br" lv)).charge 1).setW "pl.f" (q.wa "dsl.bf" lv)).charge 1).setW "sl.i" (4 * lv + 3)).charge 1
    with hq7
  have hW : WHolds q7 fsX "pl.f" H V b := by
    refine ⟨by simpa [hq7] using hB.1, fun p hp => ?_⟩
    obtain ⟨x, ⟨x1, x2, x3, x4, x5⟩, hx⟩ := hB.2 p hp
    exact ⟨x, ⟨by simp [hq7, fsX, x1], by simp [hq7, fsX, x2], by simp [hq7, fsX, x3],
      by simp [hq7, fsX, x4], by simp [hq7, fsX, x5]⟩, hx⟩
  have hSL7 : SlotLens q7 (4 * lv + 3) :=
    ⟨by simpa [hq7] using hSL.l, by simpa [hq7] using hSL.h, by simpa [hq7] using hSL.v,
      by simpa [hq7] using hSL.e, by simpa [hq7] using hSL.r, by simpa [hq7] using hSL.f⟩
  refine (Runs.and' (storeSlot_spec fsX "pl.f" q7 (by simp [hq7]) hSL7 hW)
    (storeSlot_len fsX "pl.f" q7 (by simp [hq7]) hSL7)).mono (fun r ⟨⟨h1, h2, h3, h4⟩, hl1, hl2⟩ => ?_)
  refine ⟨h1, fun j hj => ⟨by rw [(h2 j hj).1]; simp [hq7], fun a ha => by rw [(h2 j hj).2 a ha]; simp [hq7]⟩,
    ?_, by rw [h4]; simp [hq7], by rw [hl1]; simp [hq7], by rw [hl2]; simp [hq7]⟩
  have u : Unchanged q q7 slotW ["sl.l"] sepRegs0 [fsX.l] := by
    rw [hq7]
    simp only [unch_charge']
    rw [unch_setW' (by simp [sepRegs0]), unch_charge', unch_setW' (by simp [sepRegs0]), unch_charge',
      unch_setW' (by simp [sepRegs0, fsX, LReg.ws]), unch_charge', unch_setW' (by simp [sepRegs0, fsX, LReg.ws]),
      unch_charge', unch_setW' (by simp [sepRegs0, fsX, LReg.ws]), unch_charge',
      unch_setW' (by simp [sepRegs0, fsX, LReg.ws])]
    exact ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun y hy => by
      have hy' : y ≠ "fs.Xl" := by simpa [fsX] using hy
      simp [State.setV, hy'], rfl, rfl⟩
  exact u.trans (h3.mono (List.Subset.refl _) (List.Subset.refl _) (by simp) (by simp))

set_option maxHeartbeats 1000000 in
theorem copyMed0_spec (q : State ℝ≥0) {lv med : ℕ} (hlv : q.w "ds.lv" = lv) (hmed : q.w "sp.med" = med)
    (hbe : entA.InB q med) {m : MLabel G} (hm : AHolds q entA med m)
    {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {p : List (Fin G.m)}
    (hR : Rep (s := s) H V m p) (hSL : SlotLens q (4 * lv + 3)) (hcap : 4 * lv + 4 < q.cap) :
    Runs realOps copyMed0 q (fun r =>
      SlotHolds r (4 * lv + 3) H V (((toW (s := s) p : WalkOrd G s) : WLab G s)) ∧
      (∀ j, j ≠ 4 * lv + 3 → r.va "sl.l" j = q.va "sl.l" j ∧ ∀ a ∈ slotW, r.wa a j = q.wa a j) ∧
      Unchanged q r slotW ["sl.l"] sepRegs0 [fsX.l] ∧ r.cost = q.cost + 13 ∧ r.wlen = q.wlen ∧
      r.vlen = q.vlen) := by
  have hFX : LoadAFresh "sp.med" fsX := ⟨by simp [fsX, LReg.ws], by simp [fsX]⟩
  unfold copyMed0
  apply runs_seq
  refine (wp_sound _ _ _ (loadA_wp entA "sp.med" fsX hFX q med hmed hbe m hm)).mono
    (fun r1 ⟨hX1, hu1, hc1⟩ => ?_)
  have hcap1 : r1.cap = q.cap := hu1.cap
  have hlv1 : r1.w "ds.lv" = lv := by rw [hu1.wreg _ (by simp [fsX, LReg.ws])]; exact hlv
  apply runs_seq
  refine runs_wset (a := 1) (evalW_lit_of (by rw [hcap1]; omega)) ?_
  apply runs_seq
  refine runs_wset (a := 4 * lv + 3) ?_ ?_
  · have f1 : fit r1.cap (lv * 4) = some (lv * 4) := fit_of_lt (by rw [hcap1]; omega)
    have f2 : fit r1.cap 3 = some 3 := fit_of_lt (by rw [hcap1]; omega)
    have f3 : fit r1.cap 4 = some 4 := fit_of_lt (by rw [hcap1]; omega)
    have f4 : fit r1.cap (lv * 4 + 3) = some (lv * 4 + 3) := fit_of_lt (by rw [hcap1]; omega)
    simp [hlv1, f1, f2, f3, f4] <;> omega
  set q3 := ((((r1.setW "pl.f" 1).charge 1).setW "sl.i" (4 * lv + 3)).charge 1) with hq3
  have hX3 : Holds q3 fsX m := by
    obtain ⟨x1, x2, x3, x4, x5⟩ := hX1
    exact ⟨by simpa [hq3] using x1, by simpa [hq3, fsX] using x2, by simpa [hq3, fsX] using x3,
      by simpa [hq3, fsX] using x4, by simpa [hq3, fsX] using x5⟩
  have hW : WHolds q3 fsX "pl.f" H V (((toW (s := s) p : WalkOrd G s) : WLab G s)) := by
    refine ⟨by simp [hq3], fun p' hp' => ⟨m, hX3, ?_⟩⟩
    have : p = p' := WithTop.coe_injective hp'
    rw [← this]; exact hR
  have hSL3 : SlotLens q3 (4 * lv + 3) := by
    have e1 : q3.wlen = q.wlen := by
      funext a; rw [show q3.wlen a = r1.wlen a by simp [hq3], (hu1.warr a (by simp)).2]
    have e2 : q3.vlen = q.vlen := by
      funext a; rw [show q3.vlen a = r1.vlen a by simp [hq3], (hu1.varr a (by simp)).2]
    exact ⟨by rw [e2]; exact hSL.l, by rw [e1]; exact hSL.h, by rw [e1]; exact hSL.v,
      by rw [e1]; exact hSL.e, by rw [e1]; exact hSL.r, by rw [e1]; exact hSL.f⟩
  refine (Runs.and' (storeSlot_spec fsX "pl.f" q3 (by simp [hq3]) hSL3 hW)
    (storeSlot_len fsX "pl.f" q3 (by simp [hq3]) hSL3)).mono (fun r ⟨⟨h1, h2, h3, h4⟩, hl1, hl2⟩ => ?_)
  have hva1 : r1.va = q.va := funext fun a => (hu1.varr a (by simp)).1
  have hwa1 : r1.wa = q.wa := funext fun a => (hu1.warr a (by simp)).1
  have hwl1 : r1.wlen = q.wlen := funext fun a => (hu1.warr a (by simp)).2
  have hvl1 : r1.vlen = q.vlen := funext fun a => (hu1.varr a (by simp)).2
  refine ⟨h1, fun j hj => ⟨by rw [(h2 j hj).1]; simp [hq3, hva1],
    fun a ha => by rw [(h2 j hj).2 a ha]; simp [hq3, hwa1]⟩, ?_, by rw [h4]; simp [hq3, hc1],
    by rw [hl1]; simp [hq3, hwl1], by rw [hl2]; simp [hq3, hvl1]⟩
  have u1 : Unchanged q r1 slotW ["sl.l"] sepRegs0 [fsX.l] :=
    hu1.mono (by simp) (by simp) (fun y hy => by simp only [sepRegs0, List.mem_append]; left; exact hy)
      (List.Subset.refl _)
  have u2 : Unchanged r1 q3 slotW ["sl.l"] sepRegs0 [fsX.l] := by
    rw [hq3, unch_charge', unch_setW' (by simp [sepRegs0]), unch_charge', unch_setW' (by simp [sepRegs0])]
    exact Unchanged.refl _ _ _ _ _
  exact u1.trans (u2.trans (h3.mono (List.Subset.refl _) (List.Subset.refl _) (by simp) (by simp)))


theorem restore_frame {q q1 r r' : State ℝ≥0} (hq1 : q1 = (q.setW "pl.sli" (q.w "sl.i")).charge 1)
    (hu : Unchanged q1 r slotW ["sl.l"] sepRegs0 [fsX.l])
    (hr' : r' = (r.setW "sl.i" (r.w "pl.sli")).charge 1) :
    Unchanged q r' slotW ["sl.l"] sepRegs [fsX.l] := by
  subst hq1 hr'
  refine ⟨fun a ha => ?_, fun a ha => ?_, fun y hy => ?_, fun y hy => ?_, ?_, ?_⟩
  · exact ⟨by simp [(hu.warr a ha).1], by simp [(hu.warr a ha).2]⟩
  · exact ⟨by simp [(hu.varr a ha).1], by simp [(hu.varr a ha).2]⟩
  · simp only [State.charge_w, State.setW_w]
    by_cases hyi : y = "sl.i"
    · subst hyi
      rw [if_pos rfl, hu.wreg _ (by simp [sepRegs0, fsX, LReg.ws])]; simp
    · rw [if_neg hyi, hu.wreg y (by
        intro h; simp only [sepRegs0, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
        apply hy; simp only [sepRegs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto)]
      have : y ≠ "pl.sli" := fun h => hy (by simp [sepRegs, h])
      simp [this]
  · simp only [State.charge_v, State.setW_v]; rw [hu.vreg y hy]; simp
  · simp [hu.cap]
  · simp [hu.procs]

set_option maxHeartbeats 1000000 in
theorem copyBd_spec (q : State ℝ≥0) {lv : ℕ} (hlv : q.w "ds.lv" = lv) (hBL : BdLens q lv)
    {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {b : WLab G s} (hB : BdHolds q lv H V b)
    (hSL : SlotLens q (4 * lv + 3)) (hcap : 4 * lv + 4 < q.cap) :
    Runs realOps copyBd q (fun r => SlotHolds r (4 * lv + 3) H V b ∧
      (∀ j, j ≠ 4 * lv + 3 → r.va "sl.l" j = q.va "sl.l" j ∧ ∀ a ∈ slotW, r.wa a j = q.wa a j) ∧
      Unchanged q r slotW ["sl.l"] sepRegs [fsX.l] ∧ r.cost = q.cost + 15 ∧ r.wlen = q.wlen ∧
      r.vlen = q.vlen) := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hBL
  unfold copyBd
  apply runs_seq
  refine runs_wset (a := q.w "sl.i") (by simp) ?_
  set q1 := (q.setW "pl.sli" (q.w "sl.i")).charge 1 with hq1
  apply runs_seq
  refine (copyBd0_spec q1 (lv := lv) (H := H) (V := V) (b := b) (by simp [hq1, hlv]) ⟨by simpa [hq1] using l1, by simpa [hq1] using l2,
    by simpa [hq1] using l3, by simpa [hq1] using l4, by simpa [hq1] using l5, by simpa [hq1] using l6⟩
    ⟨by simpa [hq1] using hB.1, fun p hp => by
      obtain ⟨x, ⟨x1, x2, x3, x4, x5⟩, hx⟩ := hB.2 p hp
      exact ⟨x, ⟨by simpa [hq1] using x1, by simpa [hq1] using x2, by simpa [hq1] using x3,
        by simpa [hq1] using x4, by simpa [hq1] using x5⟩, hx⟩⟩
    ⟨by simpa [hq1] using hSL.l, by simpa [hq1] using hSL.h, by simpa [hq1] using hSL.v,
      by simpa [hq1] using hSL.e, by simpa [hq1] using hSL.r, by simpa [hq1] using hSL.f⟩
    (by simpa [hq1] using hcap)).mono (fun r ⟨h1, h2, h3, h4, h5, h6⟩ => ?_)
  refine runs_wset (a := r.w "pl.sli") (by simp) ?_
  refine ⟨h1, fun j hj => ?_, restore_frame hq1 h3 rfl, by simp [h4, hq1], by simp [h5, hq1], by simp [h6, hq1]⟩
  obtain ⟨e1, e2⟩ := h2 j hj
  exact ⟨by simp [e1, hq1], fun a ha => by simp [e2 a ha, hq1]⟩

set_option maxHeartbeats 1000000 in
theorem copyMed_spec (q : State ℝ≥0) {lv med : ℕ} (hlv : q.w "ds.lv" = lv) (hmed : q.w "sp.med" = med)
    (hbe : entA.InB q med) {m : MLabel G} (hm : AHolds q entA med m)
    {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {p : List (Fin G.m)}
    (hR : Rep (s := s) H V m p) (hSL : SlotLens q (4 * lv + 3)) (hcap : 4 * lv + 4 < q.cap) :
    Runs realOps copyMed q (fun r =>
      SlotHolds r (4 * lv + 3) H V (((toW (s := s) p : WalkOrd G s) : WLab G s)) ∧
      (∀ j, j ≠ 4 * lv + 3 → r.va "sl.l" j = q.va "sl.l" j ∧ ∀ a ∈ slotW, r.wa a j = q.wa a j) ∧
      Unchanged q r slotW ["sl.l"] sepRegs [fsX.l] ∧ r.cost = q.cost + 15 ∧ r.wlen = q.wlen ∧
      r.vlen = q.vlen) := by
  unfold copyMed
  apply runs_seq
  refine runs_wset (a := q.w "sl.i") (by simp) ?_
  set q1 := (q.setW "pl.sli" (q.w "sl.i")).charge 1 with hq1
  obtain ⟨b1, b2, b3, b4, b5⟩ := hbe
  obtain ⟨a1, a2, a3, a4, a5⟩ := hm
  apply runs_seq
  refine (copyMed0_spec q1 (lv := lv) (med := med) (by simp [hq1, hlv]) (by simp [hq1, hmed])
    ⟨by simpa [hq1] using b1, by simpa [hq1] using b2, by simpa [hq1] using b3, by simpa [hq1] using b4,
      by simpa [hq1] using b5⟩
    ⟨by simpa [hq1] using a1, by simpa [hq1] using a2, by simpa [hq1] using a3, by simpa [hq1] using a4,
      by simpa [hq1] using a5⟩ hR
    ⟨by simpa [hq1] using hSL.l, by simpa [hq1] using hSL.h, by simpa [hq1] using hSL.v,
      by simpa [hq1] using hSL.e, by simpa [hq1] using hSL.r, by simpa [hq1] using hSL.f⟩
    (by simpa [hq1] using hcap)).mono (fun r ⟨h1, h2, h3, h4, h5, h6⟩ => ?_)
  refine runs_wset (a := r.w "pl.sli") (by simp) ?_
  refine ⟨h1, fun j hj => ?_, restore_frame hq1 h3 rfl, by simp [h4, hq1], by simp [h5, hq1], by simp [h6, hq1]⟩
  obtain ⟨e1, e2⟩ := h2 j hj
  exact ⟨by simp [e1, hq1], fun a ha => by simp [e2 a ha, hq1]⟩

end Sep

/-! ## Helpers for the finish: entry arrays, keys, live map -/

section FinHelp

open Frontier.CHD.DIns Frontier.CHD.DB Frontier.CHD.MLab Frontier.CHD.LabTab Frontier.CHD.DList

variable {G : Graph} {s : Fin G.n}

/-- the entry pool's key/label arrays are the same (the live map may differ) -/
structure EntArrSame (st r : State ℝ≥0) : Prop where
  key : r.wa "ent.key" = st.wa "ent.key"
  len : r.va "ent.len" = st.va "ent.len"
  hh : r.wa "ent.h" = st.wa "ent.h"
  vv : r.wa "ent.v" = st.wa "ent.v"
  ee : r.wa "ent.e" = st.wa "ent.e"
  rr : r.wa "ent.r" = st.wa "ent.r"

theorem EntArrSame.trans {a b c : State ℝ≥0} (h1 : EntArrSame a b) (h2 : EntArrSame b c) :
    EntArrSame a c :=
  ⟨h2.key.trans h1.key, h2.len.trans h1.len, h2.hh.trans h1.hh, h2.vv.trans h1.vv, h2.ee.trans h1.ee,
    h2.rr.trans h1.rr⟩

theorem EntSame.arr {st r : State ℝ≥0} (h : EntSame st r) : EntArrSame st r :=
  ⟨h.key, h.len, h.hh, h.vv, h.ee, h.rr⟩

theorem entRep_same' {st r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {i : ℕ} {v : Fin G.n} {a : WLab G s} (h : EntRep st H V i v a) (hE : EntArrSame st r) :
    EntRep r H V i v a :=
  h.of_eq (by rw [hE.key]) (by rw [show entA.l = "ent.len" from rfl, hE.len])
    (by rw [show entA.h = "ent.h" from rfl, hE.hh]) (by rw [show entA.v = "ent.v" from rfl, hE.vv])
    (by rw [show entA.e = "ent.e" from rfl, hE.ee]) (by rw [show entA.r = "ent.r" from rfl, hE.rr])

theorem keysOf_eq {st : State ℝ≥0} {base : ℕ} {es : List (Entry (Fin G.n) (WLab G s))}
    (hsp : DList.Spells st "sel.w" base (es.map (·.id)))
    (hk : ∀ e ∈ es, st.wa "ent.key" e.id = e.key) :
    keysOf st base es.length = (es.map (·.key)).map Fin.val := by
  unfold keysOf
  have := seg_of_spells hsp
  rw [List.length_map] at this
  rw [this, List.map_map, List.map_map]
  apply List.map_congr_left
  intro e he
  exact hk e he

theorem keys_nodup {L : Live (Fin G.n) (WLab G s)} {es : List (Entry (Fin G.n) (WLab G s))}
    (hnd : (es.map (·.id)).Nodup) (hl : ∀ e ∈ es, e.IsLive L) : (es.map (·.key)).Nodup := by
  refine List.Nodup.map_on (fun x hx y hy hxy => ?_) (List.Nodup.of_map _ hnd)
  have := live_key_unique (hl x hx) (hl y hy) hxy
  exact List.inj_on_of_nodup_map hnd hx hy this.1

theorem liveRep_clearKeys {st r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {L : Live (Fin G.n) (WLab G s)} (hL : LiveRep st H V L) {ks : List (Fin G.n)}
    (hlive : ∀ v, r.wa "live" v = if v ∈ ks.map Fin.val then 0 else st.wa "live" v)
    (hE : EntArrSame st r) (hwl : r.wlen "live" = st.wlen "live") :
    LiveRep r H V (clearKeys L ks) := by
  refine ⟨by rw [hwl]; exact hL.1, fun v => ⟨?_, fun i a h => ?_⟩⟩
  · rw [hlive]
    unfold clearKeys
    by_cases hv : v ∈ ks
    · rw [if_pos (List.mem_map_of_mem hv), if_pos hv]; rfl
    · rw [if_neg (fun h => hv (by
          obtain ⟨w, hw, he⟩ := List.mem_map.mp h
          rw [Fin.ext he] at hw; exact hw)), if_neg hv]
      exact (hL.2 v).1
  · unfold clearKeys at h
    split_ifs at h with hv
    exact entRep_same' ((hL.2 v).2 i a h) hE

end FinHelp

/-! ## Pushing the new front record (pure) -/

section Push

open Frontier.CHD.DIns Frontier.CHD.DB Frontier.CHD.MLab Frontier.CHD.LabTab Frontier.CHD.DList

variable {G : Graph} {s : Fin G.n}

set_option maxHeartbeats 1000000 in
/-- **push a new front block** `blk` with record `pid` on top of `restF` (no execution) -/
theorem push_reps {q r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap lv bse pid M : ℕ} {Bd : WLab G s} {restF : List (Block (Fin G.n) (WLab G s))}
    {ext : List (ℕ × Block (Fin G.n) (WLab G s))} {blk : Block (Fin G.n) (WLab G s)}
    (hR : RecsOK q H V (recsOf q bse restF ++ ext))
    (hpid : pid ∉ (recsOf q bse restF ++ ext).map Prod.fst) (hpidb : pid < bcap)
    (hbid : ∀ p ∈ recsOf q bse restF, p.1 < bcap)
    (hB : BlkRep r H V pid blk)
    (hent : (blk.ents.map (·.id) ++ entIds ((recsOf q bse restF ++ ext).map Prod.snd)).Nodup)
    (hES : EntArrSame q r)
    (hnx : ∀ y ∈ entIds ((recsOf q bse restF ++ ext).map Prod.snd), r.wa "ent.nxt" y = q.wa "ent.nxt" y)
    (hnl : r.wlen "ent.nxt" = q.wlen "ent.nxt")
    (hhd : ∀ x, x ≠ pid → r.wa "blk.hd" x = q.wa "blk.hd" x)
    (htl : ∀ x, x ≠ pid → r.wa "blk.tl" x = q.wa "blk.tl" x)
    (hcnt : ∀ x, x ≠ pid → r.wa "blk.cnt" x = q.wa "blk.cnt" x)
    (hbot : ∀ x, x ≠ pid → r.wa "blk.bot" x = q.wa "blk.bot" x)
    (hA : ∀ x, x ≠ pid → ∀ y : MLabel G, AHolds q blkA x y → AHolds r blkA x y)
    (hstk : ∀ x, x < bse + restF.length → r.wa "dsl.stk" x = q.wa "dsl.stk" x)
    (hs0 : r.wa "dsl.stk" (bse + restF.length) = pid)
    (hsz : r.wa "dsl.sz" lv = restF.length + 1) (hszb : lv < r.wlen "dsl.sz")
    (hstkb : bse + restF.length + 1 ≤ r.wlen "dsl.stk") :
    RecsOK r H V (recsOf r bse (blk :: restF) ++ ext) ∧ DRep r H V bcap lv bse ⟨M, Bd, blk :: restF⟩ := by
  set rest := recsOf q bse restF ++ ext with hrest
  have e2 : recsOf r bse (blk :: restF) ++ ext = (pid, blk) :: rest := by
    rw [recsOf_cons, recsOf_congr bse restF hstk, hs0]; rfl
  obtain ⟨hn, hBr, he⟩ := hR
  have hRnew : RecsOK r H V ((pid, blk) :: rest) := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.map_cons, List.nodup_cons]; exact ⟨hpid, hn⟩
    · intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hB
      · obtain ⟨h1, h2, h3, h4, h5⟩ := hBr p hp
        have hpp : p.1 ≠ pid := fun h => hpid (h ▸ List.mem_map_of_mem hp)
        refine ⟨sepRep_holds h1 (hbot _ hpp) (hA _ hpp), ?_, fun x hx => entRep_same' (h3 x hx) hES,
          by rw [hcnt _ hpp]; exact h4, by rw [htl _ hpp]; exact h5⟩
        rw [hhd _ hpp]
        refine h2.of_eq (fun j hj => hnx j ?_) (le_of_eq (by rw [hnl]))
        unfold entIds
        exact List.mem_flatMap.mpr ⟨p.2, List.mem_map_of_mem hp, hj⟩
    · simp only [List.map_cons, entIds_cons]; exact hent
  rw [e2]
  refine ⟨hRnew, dRep_of_recs (ext := ext) (by rw [e2]; exact hRnew) (fun p hp => ?_) (by simpa using hsz)
    hszb (by simp; omega)⟩
  rw [recsOf_cons, recsOf_congr bse restF hstk, hs0] at hp
  simp only [List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact hpidb
  · exact hbid p hp

end Push

/-! ## The exhausted finish -/

/-- all collected: emit all keys, `B_i := D.Bd`, the structure becomes `[⟨⊥, []⟩]` (record `pl.pid`) -/
def pullAll : Stmt :=
  seq (wset "pl.lo" (var "pl.base"))
  (seq (wset "pl.n" (var "pl.cnt"))
  (seq emitKeys
  (seq copyBd
  (seq (wstore "blk.hd" (var "pl.pid") (lit 0))
  (seq (wstore "blk.tl" (var "pl.pid") (lit 0))
  (seq (wstore "blk.cnt" (var "pl.pid") (lit 0))
  (seq (wstore "blk.bot" (var "pl.pid") (lit 1))
  (seq (wstore "dsl.stk" (var "ds.b") (var "pl.pid"))
       (wstore "dsl.sz" (var "ds.lv") (lit 1))))))))))

section AllSt

/-- the state after the record stores of `pullAll` -/
def allSt (r : State ℝ≥0) (pid bse lv : ℕ) : State ℝ≥0 :=
  (((((((((((r.storeW "blk.hd" pid 0).charge 1).storeW "blk.tl" pid 0).charge 1).storeW "blk.cnt" pid 0).charge
    1).storeW "blk.bot" pid 1).charge 1).storeW "dsl.stk" bse pid).charge 1).storeW "dsl.sz" lv 1).charge 1

variable (r : State ℝ≥0) (pid bse lv : ℕ)

theorem allSt_blk (x : ℕ) : (allSt r pid bse lv).wa "blk.hd" x = (if x = pid then 0 else r.wa "blk.hd" x) ∧
    (allSt r pid bse lv).wa "blk.tl" x = (if x = pid then 0 else r.wa "blk.tl" x) ∧
    (allSt r pid bse lv).wa "blk.cnt" x = (if x = pid then 0 else r.wa "blk.cnt" x) ∧
    (allSt r pid bse lv).wa "blk.bot" x = (if x = pid then 1 else r.wa "blk.bot" x) ∧
    (allSt r pid bse lv).wa "dsl.stk" x = (if x = bse then pid else r.wa "dsl.stk" x) ∧
    (allSt r pid bse lv).wa "dsl.sz" x = (if x = lv then 1 else r.wa "dsl.sz" x) := by
  simp [allSt]

theorem allSt_wa (c : String) (hc : c ∉ ["blk.hd", "blk.tl", "blk.cnt", "blk.bot", "dsl.stk", "dsl.sz"]) :
    (allSt r pid bse lv).wa c = r.wa c := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
  funext x; simp [allSt, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2]

theorem allSt_len : (allSt r pid bse lv).wlen = r.wlen ∧ (allSt r pid bse lv).vlen = r.vlen ∧
    (allSt r pid bse lv).va = r.va ∧ (allSt r pid bse lv).w = r.w ∧ (allSt r pid bse lv).v = r.v ∧
    (allSt r pid bse lv).cap = r.cap ∧ (allSt r pid bse lv).procs = r.procs ∧
    (allSt r pid bse lv).cost = r.cost + 6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [allSt] <;> ring

end AllSt

/-! ## The result of a pull -/

section PullResS

open Frontier.CHD.DIns Frontier.CHD.DB Frontier.CHD.MLab Frontier.CHD.LabTab Frontier.CHD.DList
  Frontier.CHD.RamLevel

variable {G : Graph} {s : Fin G.n}

/-- word arrays written by a pull -/
def pullWA : List String := splitWA ++ ["live", "S", "S.len"] ++ slotW
/-- value arrays written by a pull -/
def pullVA : List String := ["blk.len", "sl.l"]
/-- word registers written by a pull -/
def pullWR : List String :=
  splitWR ++ plRegs ++ ["pl.lo", "pl.n", "pl.i", "pl.id", "pl.k", "pl.row", "pl.rb", "pl.base"] ++ sepRegs
/-- value registers written by a pull -/
def pullVR : List String := entLessV

/-- **the representation after a pull** (level `lv`, stack base `bse`): the new structure `D'`
and live map `L'`, the pulled keys `ks` in row `row` of `S`, the separator `sep` in slot
`B_i[lv] = 4·lv+3`, and the frame -/
structure PullRes (q r : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (bcap lv bse : ℕ) (L' : Live (Fin G.n) (WLab G s)) (D' : DStr (Fin G.n) (WLab G s))
    (ext : List (ℕ × Block (Fin G.n) (WLab G s))) (row : ℕ) (ks : List (Fin G.n)) (sep : WLab G s) :
    Prop where
  drep : DRep r H V bcap lv bse D'
  recs : RecsOK r H V (recsOf r bse D'.blocks ++ ext)
  live : LiveRep r H V L'
  barr : BlkArrs r bcap
  fresh : ∀ p ∈ recsOf r bse D'.blocks ++ ext, p.1 < r.w "blk.fresh"
  rowr : RowRep r "S" "S.len" G.n row (ks.map Fin.val)
  slot : SlotHolds r (4 * lv + 3) H V sep
  Sout : ∀ i, (i < row * G.n ∨ (row + 1) * G.n ≤ i) → r.wa "S" i = q.wa "S" i
  Slen : ∀ j, j ≠ row → r.wa "S.len" j = q.wa "S.len" j
  slots : ∀ i, i ≠ 4 * lv + 3 → r.va "sl.l" i = q.va "sl.l" i ∧ ∀ a ∈ slotW, r.wa a i = q.wa a i
  unch : Unchanged q r pullWA pullVA pullWR pullVR
  wlen : r.wlen = q.wlen
  vlen : r.vlen = q.vlen
  stk : ∀ x, x < bse → r.wa "dsl.stk" x = q.wa "dsl.stk" x
  sz : ∀ l, l ≠ lv → r.wa "dsl.sz" l = q.wa "dsl.sz" l
  fr : q.w "blk.fresh" ≤ r.w "blk.fresh"
  earr : EntArrSame q r

set_option maxHeartbeats 8000000 in
/-- **the exhausted finish** -/
theorem pullAll_spec (s0 : State ℝ≥0) {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap lv bse base M pSel row : ℕ} {Bd : WLab G s} {L : Live (Fin G.n) (WLab G s)}
    {ext : List (ℕ × Block (Fin G.n) (WLab G s))} {accF : List (Entry (Fin G.n) (WLab G s))}
    (hP : SplitPre s0 H V bcap lv bse (base + accF.length) L ⟨M, Bd, []⟩ ext pSel)
    (hsp : DList.Spells s0 "sel.w" base (accF.map (·.id))) (hcnt : s0.w "pl.cnt" = accF.length)
    (hbase : s0.w "pl.base" = base)
    (hnd : (accF.map (·.id) ++ entIds ((recsOf s0 bse [] ++ ext).map Prod.snd)).Nodup)
    (hents : ∀ e ∈ accF, EntRep s0 H V e.id e.key e.val ∧ e.IsLive L ∧ e.id < s0.wlen "ent.nxt")
    (hpid : s0.w "pl.pid" ∉ (recsOf s0 bse [] ++ ext).map Prod.fst)
    (hpidf : s0.w "pl.pid" < s0.w "blk.fresh") (hpidb : s0.w "pl.pid" < bcap)
    (hwc : base + 6 * accF.length + 60 ≤ s0.wlen "sel.w") (hsc : bse + 1 ≤ s0.wlen "dsl.stk")
    (hrow : RowRep s0 "S" "S.len" G.n row []) (hrb : s0.w "pl.rb" = row * G.n)
    (hrr : s0.w "pl.row" = row) (hBd : BdHolds s0 lv H V Bd) (hBL : BdLens s0 lv)
    (hSL : SlotLens s0 (4 * lv + 3)) (hcapS : (row + 1) * G.n + base + accF.length + 2 < s0.cap)
    (hcap4 : 4 * lv + 4 < s0.cap) :
    Runs realOps pullAll s0 (fun r =>
      PullRes s0 r H V bcap lv bse (clearKeys L (accF.map (·.key))) ⟨M, Bd, [⟨⊥, []⟩]⟩ ext row
        (accF.map (·.key)) Bd ∧ r.cost = s0.cost + 26 + 6 * accF.length ∧
      r.w "blk.fresh" = s0.w "blk.fresh") := by
  set ks := accF.map (·.key) with hksd
  have hidnd : (accF.map (·.id)).Nodup := (List.nodup_append.mp hnd).1
  have hksnd : ks.Nodup := keys_nodup hidnd (fun e he => (hents e he).2.1)
  have hkslen : ks.length ≤ G.n := by
    have := hksnd.length_le_card; simpa using this
  have hlen : accF.length ≤ G.n := by simpa [hksd] using hkslen
  have hk0 : ∀ e ∈ accF, s0.wa "ent.key" e.id = e.key := fun e he => (hents e he).1.1
  obtain ⟨_, hSw, hSlw, _, _⟩ := hrow
  have hswc := hP.swc
  unfold pullAll
  apply runs_seq
  refine runs_wset (a := base) (by simp [hbase]) ?_
  apply runs_seq
  refine runs_wset (a := accF.length) (by simp [hcnt]) ?_
  set s2 := ((((s0.setW "pl.lo" base).charge 1).setW "pl.n" accF.length).charge 1) with hs2
  have hsp2 : DList.Spells s2 "sel.w" base (accF.map (·.id)) := spells_congr (fun i _ => by simp [hs2]) hsp
  have hkeys : keysOf s2 base accF.length = ks.map Fin.val :=
    keysOf_eq hsp2 (fun e he => by simp [hs2]; exact hk0 e he)
  apply runs_seq
  refine (emitKeys_spec (ops := realOps) s2 (lo := base) (n0 := accF.length) (rb := row * G.n) (row := row)
    (by simp [hs2]) (by simp [hs2]) (by simp [hs2, hrb]) (by simp [hs2, hrr]) (by simp [hs2]; omega)
    (fun i hi => ?_) (by simp [hs2]; nlinarith) (by simpa [hs2] using hSlw) (by simp [hs2]; nlinarith)).mono
    (fun s3 ⟨hl3, hS3, hSo3, hSl3, hSlo3, hu3, hwl3, hc3⟩ => ?_)
  · have hid := hsp2 i (by simpa using hi)
    simp only [List.getElem_map] at hid
    have hmem : accF[i]'(by simpa using hi) ∈ accF := List.getElem_mem _
    obtain ⟨h1, _, h3⟩ := hents _ hmem
    rw [hid]
    have hk := (hP.key _ (by simpa using h3))
    simp only [hs2, State.charge_wa, State.setW_wa, State.charge_wlen, State.setW_wlen]
    exact hk
  rw [hkeys] at hl3
  have hwa3 : ∀ c, c ∉ ["live", "S", "S.len"] → s3.wa c = s0.wa c := fun c hc => by
    rw [(hu3.warr c hc).1]; simp [hs2]
  have hwl3' : s3.wlen = s0.wlen := by rw [hwl3]; simp [hs2]
  have hva3 : s3.va = s0.va := funext fun c => by rw [(hu3.varr c (by simp)).1]; simp [hs2]
  have hvl3 : s3.vlen = s0.vlen := funext fun c => by rw [(hu3.varr c (by simp)).2]; simp [hs2]
  have hlv3 : s3.w "ds.lv" = lv := by rw [hu3.wreg _ (by simp)]; simp [hs2, hP.lv]
  apply runs_seq
  refine (copyBd_spec s3 hlv3 ⟨by rw [hvl3]; exact hBL.bl, by rw [hwl3']; exact hBL.bh,
      by rw [hwl3']; exact hBL.bv, by rw [hwl3']; exact hBL.be, by rw [hwl3']; exact hBL.br,
      by rw [hwl3']; exact hBL.bf⟩
    (hBd.of_eq (fun a ha => by
      rw [hwa3 a (by simp at ha ⊢; rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp)])
      (by rw [hva3]))
    ⟨by rw [hvl3]; exact hSL.l, by rw [hwl3']; exact hSL.h, by rw [hwl3']; exact hSL.v,
      by rw [hwl3']; exact hSL.e, by rw [hwl3']; exact hSL.r, by rw [hwl3']; exact hSL.f⟩
    (by rw [hu3.cap]; simp [hs2]; exact hcap4)).mono (fun s4 ⟨hsl4, hslo4, hu4, hc4, hwl4, hvl4⟩ => ?_)
  have hw4 : ∀ y, y ∉ sepRegs → y ∉ ["pl.i", "pl.id", "pl.k"] → s4.w y = s2.w y := fun y h1 h2 => by
    rw [hu4.wreg y h1, hu3.wreg y h2]
  have hpid4 : s4.w "pl.pid" = s0.w "pl.pid" := by
    rw [hw4 _ (by simp [sepRegs, fsX, LReg.ws]) (by simp)]; simp [hs2]
  have hb4 : s4.w "ds.b" = bse := by
    rw [hw4 _ (by simp [sepRegs, fsX, LReg.ws]) (by simp)]; simp [hs2, hP.b]
  have hlv4 : s4.w "ds.lv" = lv := by
    rw [hw4 _ (by simp [sepRegs, fsX, LReg.ws]) (by simp)]; simp [hs2, hP.lv]
  have hwl4' : s4.wlen = s0.wlen := by rw [hwl4, hwl3']
  have hcap4' : s4.cap = s0.cap := by rw [hu4.cap, hu3.cap]; simp [hs2]
  have hbarr := hP.barr
  obtain ⟨ba1, ba2, ba3, ba4, _, _, _, _, _⟩ := hbarr
  set pid := s0.w "pl.pid" with hpidd
  have h0c : 0 < s4.cap := by rw [hcap4']; omega
  have h1c : 1 < s4.cap := by rw [hcap4']; omega
  apply runs_seq
  refine runs_wstore (j := pid) (a := 0) (by simp [hpid4]) (by simp [fit_of_lt h0c]) (by rw [hwl4']; omega) ?_
  apply runs_seq
  refine runs_wstore (j := pid) (a := 0) (by simp [hpid4]) (by simp [fit_of_lt h0c]) (by simp [hwl4']; omega) ?_
  apply runs_seq
  refine runs_wstore (j := pid) (a := 0) (by simp [hpid4]) (by simp [fit_of_lt h0c]) (by simp [hwl4']; omega) ?_
  apply runs_seq
  refine runs_wstore (j := pid) (a := 1) (by simp [hpid4]) (by simp [fit_of_lt h1c]) (by simp [hwl4']; omega) ?_
  apply runs_seq
  refine runs_wstore (j := bse) (a := pid) (by simp [hb4]) (by simp [hpid4]) (by simp [hwl4']; omega) ?_
  refine runs_wstore (j := lv) (a := 1) (by simp [hlv4]) (by simp [fit_of_lt h1c])
    (by simp [hwl4']; exact hP.drep.szb) ?_
  show PullRes s0 (allSt s4 pid bse lv) H V bcap lv bse (clearKeys L ks) ⟨M, Bd, [⟨⊥, []⟩]⟩ ext row ks Bd ∧
    (allSt s4 pid bse lv).cost = s0.cost + 26 + 6 * accF.length ∧
    (allSt s4 pid bse lv).w "blk.fresh" = s0.w "blk.fresh"
  obtain ⟨ewl, evl, eva, ew, ev, ecap, epr, ecost⟩ := allSt_len s4 pid bse lv
  have ewa := allSt_wa s4 pid bse lv
  have eblk := allSt_blk s4 pid bse lv
  set r := allSt s4 pid bse lv with hrd
  have hwl : r.wlen = s0.wlen := by rw [ewl, hwl4']
  have hvl : r.vlen = s0.vlen := by rw [evl, hvl4, hvl3]
  -- arrays other than the written ones
  have hwa4 : ∀ c, c ∉ ["live", "S", "S.len"] → c ∉ slotW → s4.wa c = s0.wa c := fun c h1 h2 => by
    rw [(hu4.warr c h2).1, hwa3 c h1]
  have hwaR : ∀ c, c ∉ ["blk.hd", "blk.tl", "blk.cnt", "blk.bot", "dsl.stk", "dsl.sz"] →
      c ∉ ["live", "S", "S.len"] → c ∉ slotW → r.wa c = s0.wa c := fun c h0 h1 h2 => by
    rw [ewa c h0, hwa4 c h1 h2]
  have hvaR : ∀ c, c ≠ "sl.l" → r.va c = s0.va c := fun c hc => by
    rw [eva, (hu4.varr c (by simpa using hc)).1, hva3]
  have hEA : EntArrSame s0 r := ⟨hwaR _ (by simp) (by simp) (by simp [slotW]), hvaR _ (by simp),
    hwaR _ (by simp) (by simp) (by simp [slotW]), hwaR _ (by simp) (by simp) (by simp [slotW]),
    hwaR _ (by simp) (by simp) (by simp [slotW]), hwaR _ (by simp) (by simp) (by simp [slotW])⟩
  have hrecs0 : recsOf s0 bse ([] : List (Block (Fin G.n) (WLab G s))) = [] := by simp [recsOf]
  have hfreshR : r.w "blk.fresh" = s0.w "blk.fresh" := by
    rw [ew, hw4 _ (by simp [sepRegs, fsX, LReg.ws]) (by simp)]; simp [hs2]
  -- the new record
  have hB : BlkRep r H V pid (⟨⊥, []⟩ : Block (Fin G.n) (WLab G s)) := by
    refine ⟨⟨by rw [(eblk pid).2.2.2.1, if_pos rfl]; simp, Or.inl rfl⟩, ?_, fun x hx => absurd hx (by simp),
      by rw [(eblk pid).2.2.1, if_pos rfl]; rfl, by rw [(eblk pid).2.1, if_pos rfl]; rfl⟩
    rw [(eblk pid).1, if_pos rfl]; exact .nil
  have hR0 := hP.recs
  obtain ⟨hRn, hDn⟩ := push_reps (q := s0) (r := r) (M := M) (Bd := Bd) (restF := []) (blk := ⟨⊥, []⟩)
    hR0 hpid hpidb (by rw [hrecs0]; simp) hB (by simpa using hR0.2.2) hEA
    (fun y _ => by rw [hwaR "ent.nxt" (by simp) (by simp) (by simp [slotW])])
    (by rw [hwl]) (fun x hx => by rw [(eblk x).1, if_neg hx, hwa4 _ (by simp) (by simp [slotW])])
    (fun x hx => by rw [(eblk x).2.1, if_neg hx, hwa4 _ (by simp) (by simp [slotW])])
    (fun x hx => by rw [(eblk x).2.2.1, if_neg hx, hwa4 _ (by simp) (by simp [slotW])])
    (fun x hx => by rw [(eblk x).2.2.2.1, if_neg hx, hwa4 _ (by simp) (by simp [slotW])])
    (fun x _ y hy => by
      obtain ⟨y1, y2, y3, y4, y5⟩ := hy
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [blkA]; rw [hvaR _ (by simp)]; exact y1
      · simp only [blkA]; rw [hwaR _ (by simp) (by simp) (by simp [slotW])]; exact y2
      · simp only [blkA]; rw [hwaR _ (by simp) (by simp) (by simp [slotW])]; exact y3
      · simp only [blkA]; rw [hwaR _ (by simp) (by simp) (by simp [slotW])]; exact y4
      · simp only [blkA]; rw [hwaR _ (by simp) (by simp) (by simp [slotW])]; exact y5)
    (fun x hx => by
      rw [(eblk x).2.2.2.2.1, if_neg (by simp at hx; omega), hwa4 _ (by simp) (by simp [slotW])])
    (by simp only [List.length_nil, Nat.add_zero]; rw [(eblk bse).2.2.2.2.1, if_pos rfl])
    (by rw [(eblk lv).2.2.2.2.2, if_pos rfl]; rfl)
    (by rw [hwl]; exact hP.drep.szb) (by rw [hwl]; simpa using hsc)
  refine ⟨⟨hDn, hRn, ?_, blkArrs_same hP.barr hwl hvl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hwl, hvl, ?_, ?_,
    by rw [hfreshR], hEA⟩, ?_, hfreshR⟩
  · -- live
    refine liveRep_clearKeys hP.live (fun v => ?_) hEA (by rw [hwl])
    rw [ewa _ (by simp), (hu4.warr _ (by simp [slotW])).1, hl3 v]
    simp [hs2]
  · -- fresh
    intro p hp
    rw [hfreshR]
    rcases List.mem_append.mp hp with hp | hp
    · simp only [recsOf, List.length_singleton, List.range_one, List.map_cons, List.map_nil,
        List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
      subst hp
      simp only [stkId, Nat.sub_self, Nat.add_zero]
      rw [(eblk bse).2.2.2.2.1, if_pos rfl]
      exact hpidf
    · exact hP.fresh p (List.mem_append_right _ hp)
  · -- the S row
    have hSr : ∀ i, r.wa "S" i = s3.wa "S" i := fun i => by
      rw [ewa _ (by simp), (hu4.warr _ (by simp [slotW])).1]
    have hSlr : ∀ j, r.wa "S.len" j = s3.wa "S.len" j := fun j => by
      rw [ewa _ (by simp), (hu4.warr _ (by simp [slotW])).1]
    refine ⟨by simpa using hkslen, by rw [hwl]; exact hSw, by rw [hwl]; exact hSlw,
      by rw [hSlr, hSl3]; simp [hksd], fun i hi => ?_⟩
    have hi' : i < accF.length := by simpa [hksd] using hi
    rw [hSr, hS3 i hi']
    have := keysOf_get s2 base accF.length i hi'
    rw [← this]
    simp only [hkeys]
  · -- the slot
    refine hsl4.of_slot_eq (by rw [eva]) (fun a ha => ?_)
    rw [ewa a (by simp [slotW] at ha ⊢; rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp)]
  · -- S outside the row
    intro i hi
    have e1 : (row + 1) * G.n = row * G.n + G.n := by ring
    rw [ewa _ (by simp), (hu4.warr _ (by simp [slotW])).1, hSo3 i (by omega)]
    simp [hs2]
  · -- S.len elsewhere
    intro j hj
    rw [ewa _ (by simp), (hu4.warr _ (by simp [slotW])).1, hSlo3 j hj]
    simp [hs2]
  · -- other slots
    intro i hi
    refine ⟨by rw [eva, (hslo4 i hi).1, hva3], fun a ha => ?_⟩
    rw [ewa a (by simp [slotW] at ha ⊢; rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp),
      (hslo4 i hi).2 a ha, hwa3 a (by simp [slotW] at ha ⊢; rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp)]
  · -- the frame
    have u02 : Unchanged s0 s2 pullWA pullVA pullWR pullVR := by
      rw [hs2, unch_charge', unch_setW' (by simp [pullWR]), unch_charge', unch_setW' (by simp [pullWR])]
      exact Unchanged.refl _ _ _ _ _
    have u23 : Unchanged s2 s3 pullWA pullVA pullWR pullVR :=
      hu3.mono (by intro a ha; simp at ha; rcases ha with rfl | rfl | rfl <;> simp [pullWA])
        (by simp) (by intro a ha; simp at ha; rcases ha with rfl | rfl | rfl <;> simp [pullWR]) (by simp)
    have u34 : Unchanged s3 s4 pullWA pullVA pullWR pullVR :=
      hu4.mono (by intro a ha; simp [pullWA]; right; right; right; right; exact ha) (by simp [pullVA])
        (by intro a ha; simp only [pullWR, List.mem_append]; right; exact ha) (by simp [pullVR, entLessV])
    have u4r : Unchanged s4 r pullWA pullVA pullWR pullVR := by
      refine ⟨fun c hc => ⟨ewa c (fun h => hc ?_), by rw [ewl]⟩, fun c _ => ⟨by rw [eva], by rw [evl]⟩,
        fun y _ => by rw [ew], fun y _ => by rw [ev], ecap, epr⟩
      simp at h; simp [pullWA, splitWA]
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    exact u02.trans (u23.trans (u34.trans u4r))
  · intro x hx
    rw [(eblk x).2.2.2.2.1, if_neg (by omega), hwa4 _ (by simp) (by simp [slotW])]
  · intro l hl
    rw [(eblk l).2.2.2.2.2, if_neg hl, hwa4 _ (by simp) (by simp [slotW])]
  · rw [ecost, hc4, hc3]; simp [hs2]; ring

end PullResS

/-! ## The cut finish -/

/-- the record of the remainder block `⟨⊥, R⟩` and its push -/
def cutRec : Stmt :=
  seq (wstore "blk.hd" (var "pl.pid") (var "dl.h"))
  (seq (wstore "blk.tl" (var "pl.pid")
        (tlE (add (add (add (var "sp.w0") (var "sp.c")) (var "sel.a")) (var "sel.b"))))
  (seq (wstore "blk.cnt" (var "pl.pid") (var "sel.b"))
  (seq (wstore "blk.bot" (var "pl.pid") (lit 1))
  (seq (wstore "dsl.stk" (add (var "ds.b") (load "dsl.sz" (var "ds.lv"))) (var "pl.pid"))
       (wstore "dsl.sz" (var "ds.lv") (add (load "dsl.sz" (var "ds.lv")) (lit 1)))))))

/-- more than `M` collected: select rank `M`, emit the keys below it, `B_i :=` its label, keep the
rest as the new front block `⟨⊥, R⟩` (record `pl.pid`) -/
def pullCut (pSel : ℕ) : Stmt :=
  seq (wset "sp.w0" (var "pl.base"))
  (seq (wset "sp.c" (var "pl.cnt"))
  (seq (spMedK (var "ds.M") pSel)
  (seq spHalves
  (seq (wset "pl.lo" (add (var "sp.w0") (var "sp.c")))
  (seq (wset "pl.n" (var "sel.a"))
  (seq emitKeys
  (seq copyMed
  (seq (wset "dl.a" (add (add (var "sp.w0") (var "sp.c")) (var "sel.a")))
  (seq (wset "dl.n" (var "sel.b"))
  (seq DList.buildList
       cutRec))))))))))

section CutSt

/-- the state after `cutRec` -/
def cutSt (r : State ℝ≥0) (pid hd tl b pos lv k : ℕ) : State ℝ≥0 :=
  (((((((((((r.storeW "blk.hd" pid hd).charge 1).storeW "blk.tl" pid tl).charge 1).storeW "blk.cnt" pid b).charge
    1).storeW "blk.bot" pid 1).charge 1).storeW "dsl.stk" pos pid).charge 1).storeW "dsl.sz" lv k).charge 1

variable (r : State ℝ≥0) (pid hd tl b pos lv k : ℕ)

theorem cutSt_blk (x : ℕ) : (cutSt r pid hd tl b pos lv k).wa "blk.hd" x = (if x = pid then hd else r.wa "blk.hd" x) ∧
    (cutSt r pid hd tl b pos lv k).wa "blk.tl" x = (if x = pid then tl else r.wa "blk.tl" x) ∧
    (cutSt r pid hd tl b pos lv k).wa "blk.cnt" x = (if x = pid then b else r.wa "blk.cnt" x) ∧
    (cutSt r pid hd tl b pos lv k).wa "blk.bot" x = (if x = pid then 1 else r.wa "blk.bot" x) ∧
    (cutSt r pid hd tl b pos lv k).wa "dsl.stk" x = (if x = pos then pid else r.wa "dsl.stk" x) ∧
    (cutSt r pid hd tl b pos lv k).wa "dsl.sz" x = (if x = lv then k else r.wa "dsl.sz" x) := by
  simp [cutSt]

theorem cutSt_wa (c : String) (hc : c ∉ ["blk.hd", "blk.tl", "blk.cnt", "blk.bot", "dsl.stk", "dsl.sz"]) :
    (cutSt r pid hd tl b pos lv k).wa c = r.wa c := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
  funext x; simp [cutSt, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2]

theorem cutSt_len : (cutSt r pid hd tl b pos lv k).wlen = r.wlen ∧ (cutSt r pid hd tl b pos lv k).vlen = r.vlen ∧
    (cutSt r pid hd tl b pos lv k).va = r.va ∧ (cutSt r pid hd tl b pos lv k).w = r.w ∧
    (cutSt r pid hd tl b pos lv k).v = r.v ∧ (cutSt r pid hd tl b pos lv k).cap = r.cap ∧
    (cutSt r pid hd tl b pos lv k).procs = r.procs ∧ (cutSt r pid hd tl b pos lv k).cost = r.cost + 6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [cutSt] <;> ring

end CutSt

set_option maxHeartbeats 1000000 in
theorem cutRec_run (q : State ℝ≥0) {pid hd w0 c a b bse lv k : ℕ} (hpid : q.w "pl.pid" = pid)
    (hhd : q.w "dl.h" = hd) (hw0 : q.w "sp.w0" = w0) (hc : q.w "sp.c" = c) (ha : q.w "sel.a" = a)
    (hb : q.w "sel.b" = b) (hbse : q.w "ds.b" = bse) (hlv : q.w "ds.lv" = lv) (hk : q.wa "dsl.sz" lv = k)
    (hb1 : 1 ≤ b) (hpb : pid < q.wlen "blk.hd" ∧ pid < q.wlen "blk.tl" ∧ pid < q.wlen "blk.cnt" ∧
      pid < q.wlen "blk.bot")
    (hsl : w0 + c + a + b ≤ q.wlen "sel.w") (hcap : w0 + c + a + b + 1 < q.cap)
    (htl : q.wa "sel.w" (w0 + c + a + b - 1) + 1 < q.cap) (hls : lv < q.wlen "dsl.sz")
    (hst : bse + k < q.wlen "dsl.stk") (hkc : bse + k + 1 < q.cap) :
    Runs realOps cutRec q (fun r =>
      r = cutSt q pid hd (q.wa "sel.w" (w0 + c + a + b - 1) + 1) b (bse + k) lv (k + 1)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hpb
  have c1 : 1 < q.cap := by omega
  unfold cutRec
  apply runs_seq
  refine runs_wstore (j := pid) (a := hd) (by simp [hpid]) (by simp [hhd]) h1 ?_
  apply runs_seq
  refine runs_wstore (j := pid) (a := q.wa "sel.w" (w0 + c + a + b - 1) + 1) (by simp [hpid])
    (evalW_tlE (x := w0 + c + a + b) (evalW_add_of (evalW_add_of (evalW_add_of (by simp [hw0])
      (by simp [hc]) (by simp; omega)) (by simp [ha]) (by simp; omega)) (by simp [hb]) (by simp; omega))
      (by omega) (by simp; omega) (by simp; omega) (by simpa using htl)) (by simpa using h2) ?_
  apply runs_seq
  refine runs_wstore (j := pid) (a := b) (by simp [hpid]) (by simp [hb]) (by simpa using h3) ?_
  apply runs_seq
  refine runs_wstore (j := pid) (a := 1) (by simp [hpid]) (by simp [fit_of_lt c1]) (by simpa using h4) ?_
  apply runs_seq
  refine runs_wstore (j := bse + k) (a := pid) ?_ (by simp [hpid]) (by simpa using hst) ?_
  · have : evalW ((((((((q.storeW "blk.hd" pid hd).charge 1).storeW "blk.tl" pid
        (q.wa "sel.w" (w0 + c + a + b - 1) + 1)).charge 1).storeW "blk.cnt" pid b).charge 1).storeW
        "blk.bot" pid 1).charge 1) (load "dsl.sz" (var "ds.lv")) = some k := by
      rw [evalW_load_of (j := lv) (by simp [hlv]) (by simpa using hls)]; simp [hk]
    exact evalW_add_of (by simp [hbse]) this (by simp; omega)
  refine runs_wstore (j := lv) (a := k + 1) (by simp [hlv]) ?_ (by simpa using hls) ?_
  · have : evalW ((((((((((q.storeW "blk.hd" pid hd).charge 1).storeW "blk.tl" pid
        (q.wa "sel.w" (w0 + c + a + b - 1) + 1)).charge 1).storeW "blk.cnt" pid b).charge 1).storeW
        "blk.bot" pid 1).charge 1).storeW "dsl.stk" (bse + k) pid).charge 1) (load "dsl.sz" (var "ds.lv")) =
        some k := by
      rw [evalW_load_of (j := lv) (by simp [hlv]) (by simpa using hls)]; simp [hk]
    exact evalW_add_of this (evalW_lit_of (by simp; omega)) (by simp; omega)
  rfl

section CutSpec

open Frontier.CHD.DIns Frontier.CHD.DB Frontier.CHD.DL Frontier.CHD.MLab Frontier.CHD.LabTab
  Frontier.CHD.DList Frontier.CHD.RamLevel

variable {G : Graph} {s : Fin G.n}

set_option maxHeartbeats 16000000 in
/-- **the cut finish** -/
theorem pullCut_spec (hH : GoodHist (s := s) H V) (pSel : ℕ) (s0 : State ℝ≥0)
    {bcap lv bse base M row : ℕ} {Bd : WLab G s} {L : Live (Fin G.n) (WLab G s)}
    {ext : List (ℕ × Block (Fin G.n) (WLab G s))} {accF : List (Entry (Fin G.n) (WLab G s))}
    {restF : List (Block (Fin G.n) (WLab G s))}
    (hP : SplitPre s0 H V bcap lv bse (base + accF.length) L ⟨M, Bd, restF⟩ ext pSel)
    (hsp : DList.Spells s0 "sel.w" base (accF.map (·.id))) (hcnt : s0.w "pl.cnt" = accF.length)
    (hbase : s0.w "pl.base" = base)
    (hnd : (accF.map (·.id) ++ entIds ((recsOf s0 bse restF ++ ext).map Prod.snd)).Nodup)
    (hents : ∀ e ∈ accF, EntRep s0 H V e.id e.key e.val ∧ e.IsLive L ∧ e.id < s0.wlen "ent.nxt")
    (hpid : s0.w "pl.pid" ∉ (recsOf s0 bse restF ++ ext).map Prod.fst)
    (hpidf : s0.w "pl.pid" < s0.w "blk.fresh") (hpidb : s0.w "pl.pid" < bcap)
    (hwc : base + 6 * accF.length + 60 ≤ s0.wlen "sel.w")
    (hsc : bse + restF.length + 1 ≤ s0.wlen "dsl.stk") (hMc : M < accF.length)
    (hrow : RowRep s0 "S" "S.len" G.n row []) (hrb : s0.w "pl.rb" = row * G.n)
    (hrr : s0.w "pl.row" = row) (hSL : SlotLens s0 (4 * lv + 3))
    (hcapS : (row + 1) * G.n + base + 2 * accF.length + 2 < s0.cap) (hcap4 : 4 * lv + 4 < s0.cap) :
    Runs realOps (pullCut pSel) s0 (fun r =>
      PullRes s0 r H V bcap lv bse
        (clearKeys L ((accF.filter (fun e => decide (e.val < (selectC (accF.map (·.val)) M).1))).map (·.key)))
        ⟨M, Bd, ⟨⊥, accF.filter (fun e => decide ((selectC (accF.map (·.val)) M).1 ≤ e.val))⟩ :: restF⟩ ext row
        ((accF.filter (fun e => decide (e.val < (selectC (accF.map (·.val)) M).1))).map (·.key))
        (selectC (accF.map (·.val)) M).1 ∧
      r.cost ≤ s0.cost + 200 + (Ksel 23 + 100) * accF.length ∧ r.w "blk.fresh" = s0.w "blk.fresh") := by
  set x := (selectC (accF.map (·.val)) M).1 with hxd
  set Sents := accF.filter (fun e => decide (e.val < x)) with hSd
  set Rents := accF.filter (fun e => decide (x ≤ e.val)) with hRd
  set c := accF.length with hcd
  have hidnd : (accF.map (·.id)).Nodup := (List.nodup_append.mp hnd).1
  have hL := lessB hH accF hidnd
  have hk0 : ∀ e ∈ accF, s0.wa "ent.key" e.id = e.key := fun e he => (hents e he).1.1
  obtain ⟨_, hSw, hSlw, _, _⟩ := hrow
  have hswc := hP.swc
  have hlenS : Sents.length ≤ c := List.length_filter_le _ _
  have hlenR : Rents.length ≤ c := List.length_filter_le _ _
  have hksnd : (accF.map (·.key)).Nodup := keys_nodup hidnd (fun e he => (hents e he).2.1)
  have hcn : c ≤ G.n := by
    have := hksnd.length_le_card; simpa using this
  unfold pullCut
  apply runs_seq
  refine runs_wset (a := base) (by simp [hbase]) ?_
  apply runs_seq
  refine runs_wset (a := c) (by simp [hcnt]) ?_
  set s2 := ((((s0.setW "sp.w0" base).charge 1).setW "sp.c" c).charge 1) with hs2
  have hseg2 : seg s2 base c = accF.map (·.id) := by
    have := seg_of_spells (st := s2) (spells_congr (fun i _ => by simp [hs2]) hsp)
    simpa using this
  have hK2 : KRB H V accF s2 := ⟨fun e he => ⟨entRep_same' (hents e he).1 ⟨by simp [hs2], by simp [hs2],
      by simp [hs2], by simp [hs2], by simp [hs2], by simp [hs2]⟩,
      by have := hP.inb _ (hents e he).2.2; exact this⟩, by simp [hs2]; omega⟩
  apply runs_seq
  refine (spMedK_run hL krb_frame (var "ds.M") pSel s2 hK2 (w0 := base) (c := c) (kk := M) (by simp [hs2])
    (by simp [hs2]) (by simp [hs2, hP.M]) hMc (fun y hy => by rw [hseg2] at hy; exact hy)
    (by simpa [hs2] using hP.procs) (by simp [hs2]; omega) (by simp [hs2]; omega)
    (by simpa [hs2] using hP.c300)).mono (fun s3 ⟨hK3, hmem3, hkth3, hlow3, hwl3, hu3, hc3⟩ => ?_)
  set med := s3.w "sp.med" with hmedd
  rw [hseg2, map_valOf_ids hidnd] at hkth3
  rw [hseg2] at hmem3
  have hmv : valOf accF med = x := hkth3.unique (Frontier.CHD.selectC_isKth _ (by simp; omega))
  have hnot3 : ∀ y ∈ ["sp.w0", "sp.c", "ds.lv", "ds.b", "pl.pid", "pl.rb", "pl.row", "blk.fresh"],
      y ∉ myRegs ++ entLessW ++ ["sp.med"] := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [myRegs, lessRegs, csRegs, selRegs, entLessW, fsX, fsY, LReg.ws]
  have hseg3 : seg s3 base c = accF.map (·.id) := by
    rw [← hseg2]; apply seg_congr; intro y _ h2; exact hlow3 y h2
  apply runs_seq
  refine (spHalves_run hL s3 (w0 := base) (c := c) (med := med) hK3
    (by rw [hu3.wreg _ (hnot3 _ (by simp))]; simp [hs2]) (by rw [hu3.wreg _ (hnot3 _ (by simp))]; simp [hs2])
    rfl (fun y hy => by rw [hseg3] at hy; exact hy) hmem3 (by rw [hwl3]; simp [hs2]; omega)
    (by rw [hu3.cap]; simp [hs2]; omega)).mono (fun s4 ⟨hK4, hlo4, hhi4, hsum4, hlow4, hwl4, hu4, hc4⟩ => ?_)
  rw [hseg3, filt_ids_lt hidnd hmv] at hlo4
  rw [hseg3, filt_ids_ge hidnd hmv] at hhi4
  set a := s4.w "sel.a" with had
  set b := s4.w "sel.b" with hbd
  have hla : Sents.length = a := by
    have h1 := congrArg List.length hlo4
    rw [length_seg, List.length_map] at h1
    exact h1.symm
  have hlb : Rents.length = b := by
    have h1 := congrArg List.length hhi4
    rw [length_seg, List.length_map] at h1
    exact h1.symm
  -- the pivot entry
  obtain ⟨em, hem, hemid⟩ := List.mem_map.mp hmem3
  obtain ⟨⟨_, m, pm, hAm, hRm, hvm⟩, _, hem3⟩ := hents em hem
  have hemv : em.val = x := by rw [← hmv, ← hemid, valOf_of_mem hidnd hem]
  have hb1 : 1 ≤ b := by
    rw [← hlb]
    exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hem, by simp [hemv]⟩)
  have hsum : a + b = c := hsum4
  -- frame s2 → s4
  have u24 : Unchanged s2 s4 ["sel.w"] [] (myRegs ++ entLessW ++ ["sp.med"]) entLessV :=
    hu3.trans (hu4.mono (List.Subset.refl _) (List.Subset.refl _) (fun y hy => List.mem_append_left _ hy)
      (List.Subset.refl _))
  have hreg4 : ∀ y ∈ ["sp.w0", "sp.c", "ds.lv", "ds.b", "pl.pid", "pl.rb", "pl.row", "blk.fresh"],
      s4.w y = s2.w y := fun y hy => u24.wreg y (hnot3 y hy)
  have hwa4 : ∀ c', c' ≠ "sel.w" → s4.wa c' = s0.wa c' := fun c' hc' => by
    rw [(u24.warr c' (by simpa using hc')).1]; simp [hs2]
  have hwl4' : s4.wlen = s0.wlen := by
    funext c'
    by_cases h : c' = "sel.w"
    · subst h; rw [hwl4, hwl3]; simp [hs2]
    · rw [(u24.warr c' (by simpa using h)).2]; simp [hs2]
  have hva4 : s4.va = s0.va := funext fun c' => by rw [(u24.varr c' (by simp)).1]; simp [hs2]
  have hvl4 : s4.vlen = s0.vlen := funext fun c' => by rw [(u24.varr c' (by simp)).2]; simp [hs2]
  have hcap4' : s4.cap = s0.cap := by rw [u24.cap]; simp [hs2]
  have hsw4low : ∀ y, y < base + c → s4.wa "sel.w" y = s0.wa "sel.w" y := fun y hy => by
    rw [hlow4 y hy, hlow3 y hy]; simp [hs2]
  -- emit the keys of `Sents`
  apply runs_seq
  refine runs_wset (a := base + c) (evalW_add_of (x := base) (y := c)
    (by simp [hreg4 "sp.w0" (by simp), hs2]) (by simp [hreg4 "sp.c" (by simp), hs2])
    (by rw [hcap4']; omega)) ?_
  apply runs_seq
  refine runs_wset (a := a) (by simp [had]) ?_
  set s5 := (((s4.setW "pl.lo" (base + c)).charge 1).setW "pl.n" a).charge 1 with hs5
  have hsp5 : DList.Spells s5 "sel.w" (base + c) (Sents.map (·.id)) := by
    have h1 := spells_seg s4 (base + c) a
    rw [hlo4] at h1
    exact spells_congr (fun i _ => by simp [hs5]) h1
  have hkeys5 : keysOf s5 (base + c) a = (Sents.map (·.key)).map Fin.val := by
    rw [← hla]
    exact keysOf_eq hsp5 (fun e he => by
      simp only [hs5, State.charge_wa, State.setW_wa]
      rw [hwa4 _ (by simp)]
      exact hk0 e (List.mem_of_mem_filter he))
  have hSsub : ∀ e ∈ Sents, e ∈ accF := fun e he => List.mem_of_mem_filter he
  have hRsub : ∀ e ∈ Rents, e ∈ accF := fun e he => List.mem_of_mem_filter he
  apply runs_seq
  refine (emitKeys_spec (ops := realOps) s5 (lo := base + c) (n0 := a) (rb := row * G.n) (row := row)
    (by simp [hs5]) (by simp [hs5]) (by simp [hs5, hreg4 "pl.rb" (by simp), hs2, hrb])
    (by simp [hs5, hreg4 "pl.row" (by simp), hs2, hrr]) (by simp [hs5, hwl4']; omega)
    (fun i hi => ?_) (by simp [hs5, hwl4']; nlinarith) (by simpa [hs5, hwl4'] using hSlw)
    (by simp [hs5, hcap4']; nlinarith)).mono (fun s6 ⟨hl6, hS6, hSo6, hSl6, hSlo6, hu6, hwl6, hc6⟩ => ?_)
  · have hid := hsp5 i (by simpa [hla] using hi)
    simp only [List.getElem_map] at hid
    have hmem : Sents[i]'(by simpa [hla] using hi) ∈ accF := hSsub _ (List.getElem_mem _)
    obtain ⟨h1, _, h3⟩ := hents _ hmem
    rw [hid]
    have hk := hP.key _ h3
    simp only [hs5, State.charge_wa, State.setW_wa, State.charge_wlen, State.setW_wlen]
    rw [hwa4 _ (by simp), hwl4']
    exact hk
  rw [hkeys5] at hl6
  have hw6 : ∀ y, y ∉ ["pl.i", "pl.id", "pl.k"] → s6.w y = s5.w y := fun y hy => hu6.wreg y hy
  have hwa6 : ∀ c', c' ∉ ["live", "S", "S.len"] → s6.wa c' = s5.wa c' := fun c' hc' => (hu6.warr c' hc').1
  have hwl6' : s6.wlen = s0.wlen := by rw [hwl6]; simp [hs5, hwl4']
  have hva6 : s6.va = s0.va := funext fun c' => by rw [(hu6.varr c' (by simp)).1]; simp [hs5, hva4]
  have hvl6 : s6.vlen = s0.vlen := funext fun c' => by rw [(hu6.varr c' (by simp)).2]; simp [hs5, hvl4]
  have hcap6 : s6.cap = s0.cap := by rw [hu6.cap]; simp [hs5, hcap4']
  have hmed6 : s6.w "sp.med" = em.id := by
    rw [hw6 _ (by simp)]; simp only [hs5, State.charge_w, State.setW_w]; simp only [if_neg (by decide : ¬ ("sp.med" = "pl.n")), if_neg (by decide : ¬ ("sp.med" = "pl.lo"))]
    rw [hu4.wreg _ (by simp [myRegs, lessRegs, csRegs, selRegs, entLessW, fsX, fsY, LReg.ws]), hemid]
  have hlv6 : s6.w "ds.lv" = lv := by
    rw [hw6 _ (by simp)]; simp [hs5, hreg4 "ds.lv" (by simp), hs2, hP.lv]
  have hAm6 : AHolds s6 entA em.id m := by
    obtain ⟨a1, a2, a3, a4, a5⟩ := hAm
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [entA]; rw [hva6]; exact a1
    · simp only [entA]; rw [hwa6 _ (by simp)]; simp [hs5]; rw [hwa4 _ (by simp)]; exact a2
    · simp only [entA]; rw [hwa6 _ (by simp)]; simp [hs5]; rw [hwa4 _ (by simp)]; exact a3
    · simp only [entA]; rw [hwa6 _ (by simp)]; simp [hs5]; rw [hwa4 _ (by simp)]; exact a4
    · simp only [entA]; rw [hwa6 _ (by simp)]; simp [hs5]; rw [hwa4 _ (by simp)]; exact a5
  have hbe6 : entA.InB s6 em.id := by
    obtain ⟨b1, b2, b3, b4, b5⟩ := hP.inb _ hem3
    exact ⟨by rw [hvl6]; exact b1, by rw [hwl6']; exact b2, by rw [hwl6']; exact b3,
      by rw [hwl6']; exact b4, by rw [hwl6']; exact b5⟩
  have hSL6 : SlotLens s6 (4 * lv + 3) :=
    ⟨by rw [hvl6]; exact hSL.l, by rw [hwl6']; exact hSL.h, by rw [hwl6']; exact hSL.v,
      by rw [hwl6']; exact hSL.e, by rw [hwl6']; exact hSL.r, by rw [hwl6']; exact hSL.f⟩
  apply runs_seq
  refine (copyMed_spec s6 hlv6 hmed6 hbe6 hAm6 hRm hSL6 (by rw [hcap6]; exact hcap4)).mono
    (fun s7 ⟨hsl7, hslo7, hu7, hc7, hwl7, hvl7⟩ => ?_)
  rw [← hvm, hemv] at hsl7
  -- relink `Rents`
  have hw7 : ∀ y, y ∉ sepRegs → s7.w y = s6.w y := fun y hy => hu7.wreg y hy
  have hwa7 : ∀ c', c' ∉ slotW → s7.wa c' = s6.wa c' := fun c' hc' => (hu7.warr c' hc').1
  have hcap7 : s7.cap = s0.cap := by rw [hu7.cap, hcap6]
  have hwl7' : s7.wlen = s0.wlen := by rw [hwl7, hwl6']
  have hreg7 : ∀ y ∈ ["sp.w0", "sp.c", "ds.lv", "ds.b", "pl.pid", "blk.fresh", "sel.a", "sel.b"],
      s7.w y = s4.w y := by
    intro y hy
    rw [hw7 y (by simp at hy ⊢; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [sepRegs, fsX, LReg.ws]), hw6 y (by simp at hy ⊢; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)]
    simp only [hs5, State.charge_w, State.setW_w]
    simp at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  apply runs_seq
  refine runs_wset (a := base + c + a) (evalW_add_of (x := base + c) (y := a)
    (evalW_add_of (x := base) (y := c) (by simp [hreg7 "sp.w0" (by simp), hreg4 "sp.w0" (by simp), hs2])
      (by simp [hreg7 "sp.c" (by simp), hreg4 "sp.c" (by simp), hs2]) (by rw [hcap7]; omega))
    (by simp [hreg7 "sel.a" (by simp), had]) (by rw [hcap7]; omega)) ?_
  apply runs_seq
  refine runs_wset (a := b) (by simp [hreg7 "sel.b" (by simp), hbd]) ?_
  set s8 := (((s7.setW "dl.a" (base + c + a)).charge 1).setW "dl.n" b).charge 1 with hs8
  have hsel8 : ∀ y, s8.wa "sel.w" y = s4.wa "sel.w" y := fun y => by
    simp only [hs8, State.charge_wa, State.setW_wa]
    rw [hwa7 _ (by simp [slotW]), hwa6 _ (by simp)]; simp [hs5]
  have hRids : (Rents.map (·.id)).Nodup :=
    (List.Sublist.map _ (List.filter_sublist)).nodup hidnd
  have hRlt : ∀ y ∈ Rents.map (·.id), y < s8.wlen "ent.nxt" := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
    simp only [hs8, State.charge_wlen, State.setW_wlen]; rw [hwl7']
    exact (hents e (hRsub e he)).2.2
  have hsp8 : DList.Spells s8 "sel.w" (s8.w "dl.a") (Rents.map (·.id)) := by
    have h1 := spells_seg s4 (base + c + a) b
    rw [hhi4] at h1
    rw [show s8.w "dl.a" = base + c + a by simp [hs8]]
    exact spells_congr (fun i _ => hsel8 _) h1
  have hnxc := hP.nxc
  apply runs_seq
  refine (DList.buildList_spec (ops := realOps) s8 (Rents.map (·.id)) hsp8 (by simp [hs8, hlb]) hRids hRlt
    (by simp [hs8, hlb, hwl7']; omega) (by simp [hs8, hlb, hcap7]; omega)
    (fun y hy => by have := hRlt y hy; simp [hs8, hwl7', hcap7] at this ⊢; omega)).mono
    (fun s9 ⟨hL9, hout9, hu9, hnl9, hc9⟩ => ?_)
  have hw9 : ∀ y, y ∉ DList.buildRegs → s9.w y = s8.w y := fun y hy => hu9.wreg y hy
  have hwa9 : ∀ c', c' ≠ "ent.nxt" → s9.wa c' = s8.wa c' := fun c' hc' => (hu9.warr c' (by simpa using hc')).1
  have hwl9 : s9.wlen = s0.wlen := by
    funext c'
    by_cases h : c' = "ent.nxt"
    · subst h; rw [hnl9]; simp [hs8, hwl7']
    · rw [(hu9.warr c' (by simpa using h)).2]; simp [hs8, hwl7']
  have hreg9 : ∀ y ∈ ["sp.w0", "sp.c", "ds.lv", "ds.b", "pl.pid", "blk.fresh", "sel.a", "sel.b"],
      s9.w y = s4.w y := by
    intro y hy
    rw [hw9 y (by simp at hy ⊢; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [DList.buildRegs])]
    simp only [hs8, State.charge_w, State.setW_w]
    simp at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> exact hreg7 _ (by simp)
  set pid := s0.w "pl.pid" with hpidd
  have hpid9 : s9.w "pl.pid" = pid := by rw [hreg9 _ (by simp), hreg4 _ (by simp)]; simp [hs2, hpidd]
  have hsz9 : s9.wa "dsl.sz" lv = restF.length := by
    rw [hwa9 _ (by simp)]; simp only [hs8, State.charge_wa, State.setW_wa]
    rw [hwa7 _ (by simp [slotW]), hwa6 _ (by simp)]; simp only [hs5, State.charge_wa, State.setW_wa]
    rw [hwa4 _ (by simp)]; simpa using hP.drep.sz
  have hsel9 : ∀ y, s9.wa "sel.w" y = s4.wa "sel.w" y := fun y => by rw [hwa9 _ (by simp), hsel8]
  obtain ⟨ba1, ba2, ba3, ba4, _, _, _, _, _⟩ := hP.barr
  have hstc := hP.stc
  have htlc : s9.wa "sel.w" (base + c + a + b - 1) + 1 < s9.cap := by
    have hx : s4.wa "sel.w" (base + c + a + b - 1) ∈ Rents.map (·.id) := by
      rw [← hhi4]; simp only [seg, List.mem_map, List.mem_range]; exact ⟨b - 1, by omega, by congr 1; omega⟩
    have := hRlt _ hx
    rw [hsel9]; simp [hs8, hwl7'] at this; rw [hu9.cap]; simp [hs8, hcap7]; omega
  refine (cutRec_run s9 (pid := pid) (hd := s9.w "dl.h") (w0 := base) (c := c) (a := a) (b := b) (bse := bse)
    (lv := lv) (k := restF.length) hpid9 rfl
    (by rw [hreg9 _ (by simp), hreg4 _ (by simp)]; simp [hs2])
    (by rw [hreg9 _ (by simp), hreg4 _ (by simp)]; simp [hs2])
    (by rw [hreg9 _ (by simp)]) (by rw [hreg9 _ (by simp)])
    (by rw [hreg9 _ (by simp), hreg4 _ (by simp)]; simp [hs2, hP.b])
    (by rw [hreg9 _ (by simp), hreg4 _ (by simp)]; simp [hs2, hP.lv]) hsz9 hb1
    ⟨by rw [hwl9]; omega, by rw [hwl9]; omega, by rw [hwl9]; omega, by rw [hwl9]; omega⟩
    (by rw [hwl9]; omega) (by rw [hu9.cap]; simp [hs8, hcap7]; omega) htlc
    (by rw [hwl9]; exact hP.drep.szb) (by rw [hwl9]; omega) (by rw [hu9.cap]; simp [hs8, hcap7]; omega)).mono
    (fun r hr => ?_)
  subst hr
  set tl := s9.wa "sel.w" (base + c + a + b - 1) + 1 with htld
  obtain ⟨ewl, evl, eva, ew, ev, ecap, epr, ecost⟩ :=
    cutSt_len s9 pid (s9.w "dl.h") tl b (bse + restF.length) lv (restF.length + 1)
  have ewa := cutSt_wa s9 pid (s9.w "dl.h") tl b (bse + restF.length) lv (restF.length + 1)
  have eblk := cutSt_blk s9 pid (s9.w "dl.h") tl b (bse + restF.length) lv (restF.length + 1)
  set r := cutSt s9 pid (s9.w "dl.h") tl b (bse + restF.length) lv (restF.length + 1) with hrd
  have hwl : r.wlen = s0.wlen := by rw [ewl, hwl9]
  have hvl : r.vlen = s0.vlen := by
    rw [evl]
    funext c'; rw [(hu9.varr c' (by simp)).2]; simp [hs8]; rw [hvl7, hvl6]
  -- arrays of `r` in terms of `s0`
  have hbig : ∀ c', c' ∉ ["blk.hd", "blk.tl", "blk.cnt", "blk.bot", "dsl.stk", "dsl.sz"] → c' ≠ "ent.nxt" →
      c' ∉ slotW → c' ∉ ["live", "S", "S.len"] → c' ≠ "sel.w" → r.wa c' = s0.wa c' := by
    intro c' h1 h2 h3 h4 h5
    rw [ewa c' h1, hwa9 c' h2]; simp only [hs8, State.charge_wa, State.setW_wa]
    rw [hwa7 c' h3, hwa6 c' h4]; simp only [hs5, State.charge_wa, State.setW_wa]; exact hwa4 c' h5
  have hvaR : ∀ c', c' ≠ "sl.l" → r.va c' = s0.va c' := fun c' hc' => by
    rw [eva, (hu9.varr c' (by simp)).1]; simp only [hs8, State.charge_va, State.setW_va]
    rw [(hu7.varr c' (by simpa using hc')).1, hva6]
  have hEA : EntArrSame s0 r := ⟨hbig _ (by simp) (by simp) (by simp [slotW]) (by simp) (by simp),
    hvaR _ (by simp), hbig _ (by simp) (by simp) (by simp [slotW]) (by simp) (by simp),
    hbig _ (by simp) (by simp) (by simp [slotW]) (by simp) (by simp),
    hbig _ (by simp) (by simp) (by simp [slotW]) (by simp) (by simp),
    hbig _ (by simp) (by simp) (by simp [slotW]) (by simp) (by simp)⟩
  have hfreshR : r.w "blk.fresh" = s0.w "blk.fresh" := by
    rw [ew, hreg9 _ (by simp), hreg4 _ (by simp)]; simp [hs2]
  -- ent.nxt: only `Rents` ids were relinked
  have hRdisj : ∀ y ∈ entIds ((recsOf s0 bse restF ++ ext).map Prod.snd), y ∉ Rents.map (·.id) := by
    intro y hy hyR
    have hyA : y ∈ accF.map (·.id) := (List.Sublist.map _ List.filter_sublist).subset hyR
    exact (List.nodup_append.mp hnd).2.2 y hyA y hy rfl
  have hnx8 : ∀ y, s8.wa "ent.nxt" y = s0.wa "ent.nxt" y := fun y => by
    simp only [hs8, State.charge_wa, State.setW_wa]
    rw [hwa7 _ (by simp [slotW]), hwa6 _ (by simp)]; simp only [hs5, State.charge_wa, State.setW_wa]
    rw [hwa4 _ (by simp)]
  have hB : BlkRep r H V pid (⟨⊥, Rents⟩ : Block (Fin G.n) (WLab G s)) := by
    refine ⟨⟨by rw [(eblk pid).2.2.2.1, if_pos rfl]; simp, Or.inl rfl⟩, ?_, fun e he => entRep_same'
      (hents e (hRsub e he)).1 hEA, by rw [(eblk pid).2.2.1, if_pos rfl, ← hlb], ?_⟩
    · rw [(eblk pid).1, if_pos rfl]
      exact hL9.frame (by rw [ewl]) (fun i _ => by rw [ewa _ (by simp)])
    · rw [(eblk pid).2.1, if_pos rfl, htld, hsel9, ← hhi4, tlWord_seg _ _ _ hb1]
  have hR0 := hP.recs
  obtain ⟨hRn, hDn⟩ := push_reps (q := s0) (r := r) (M := M) (Bd := Bd) (restF := restF)
    (blk := ⟨⊥, Rents⟩) hR0 hpid hpidb (recsOf_bound hP.drep) hB
    (by
      have hsub : (Rents.map (·.id) ++ entIds ((recsOf s0 bse restF ++ ext).map Prod.snd)).Sublist
          (accF.map (·.id) ++ entIds ((recsOf s0 bse restF ++ ext).map Prod.snd)) :=
        (List.Sublist.map _ List.filter_sublist).append (List.Sublist.refl _)
      exact hsub.nodup hnd) hEA
    (fun y hy => by rw [ewa _ (by simp), hout9 y (hRdisj y hy), hnx8])
    (by rw [hwl])
    (fun x hx => by
      rw [(eblk x).1, if_neg hx, hwa9 _ (by simp)]; simp only [hs8, State.charge_wa, State.setW_wa]
      rw [hwa7 _ (by simp [slotW]), hwa6 _ (by simp)]; simp only [hs5, State.charge_wa, State.setW_wa]
      rw [hwa4 _ (by simp)])
    (fun x hx => by
      rw [(eblk x).2.1, if_neg hx, hwa9 _ (by simp)]; simp only [hs8, State.charge_wa, State.setW_wa]
      rw [hwa7 _ (by simp [slotW]), hwa6 _ (by simp)]; simp only [hs5, State.charge_wa, State.setW_wa]
      rw [hwa4 _ (by simp)])
    (fun x hx => by
      rw [(eblk x).2.2.1, if_neg hx, hwa9 _ (by simp)]; simp only [hs8, State.charge_wa, State.setW_wa]
      rw [hwa7 _ (by simp [slotW]), hwa6 _ (by simp)]; simp only [hs5, State.charge_wa, State.setW_wa]
      rw [hwa4 _ (by simp)])
    (fun x hx => by
      rw [(eblk x).2.2.2.1, if_neg hx, hwa9 _ (by simp)]; simp only [hs8, State.charge_wa, State.setW_wa]
      rw [hwa7 _ (by simp [slotW]), hwa6 _ (by simp)]; simp only [hs5, State.charge_wa, State.setW_wa]
      rw [hwa4 _ (by simp)])
    (fun x _ y hy => by
      obtain ⟨y1, y2, y3, y4, y5⟩ := hy
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [blkA]; rw [hvaR _ (by simp)]; exact y1
      · simp only [blkA]; rw [hbig _ (by simp) (by simp) (by simp [slotW]) (by simp) (by simp)]; exact y2
      · simp only [blkA]; rw [hbig _ (by simp) (by simp) (by simp [slotW]) (by simp) (by simp)]; exact y3
      · simp only [blkA]; rw [hbig _ (by simp) (by simp) (by simp [slotW]) (by simp) (by simp)]; exact y4
      · simp only [blkA]; rw [hbig _ (by simp) (by simp) (by simp [slotW]) (by simp) (by simp)]; exact y5)
    (fun x hx => by
      rw [(eblk x).2.2.2.2.1, if_neg (by omega), hwa9 _ (by simp)]
      simp only [hs8, State.charge_wa, State.setW_wa]
      rw [hwa7 _ (by simp [slotW]), hwa6 _ (by simp)]; simp only [hs5, State.charge_wa, State.setW_wa]
      rw [hwa4 _ (by simp)])
    (by rw [(eblk _).2.2.2.2.1, if_pos rfl])
    (by rw [(eblk lv).2.2.2.2.2, if_pos rfl])
    (by rw [hwl]; exact hP.drep.szb) (by rw [hwl]; exact hsc)
  have hSr : ∀ i, r.wa "S" i = s6.wa "S" i := fun i => by
    rw [ewa _ (by simp), hwa9 _ (by simp)]; simp only [hs8, State.charge_wa, State.setW_wa]
    rw [hwa7 _ (by simp [slotW])]
  have hSlr : ∀ j, r.wa "S.len" j = s6.wa "S.len" j := fun j => by
    rw [ewa _ (by simp), hwa9 _ (by simp)]; simp only [hs8, State.charge_wa, State.setW_wa]
    rw [hwa7 _ (by simp [slotW])]
  have hS5 : ∀ i, s5.wa "S" i = s0.wa "S" i := fun i => by simp only [hs5, State.charge_wa, State.setW_wa]; rw [hwa4 _ (by simp)]
  have hSl5 : ∀ j, s5.wa "S.len" j = s0.wa "S.len" j := fun j => by
    simp only [hs5, State.charge_wa, State.setW_wa]; rw [hwa4 _ (by simp)]
  refine ⟨⟨hDn, hRn, ?_, blkArrs_same hP.barr hwl hvl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hwl, hvl, ?_, ?_,
    by rw [hfreshR], hEA⟩, ?_, hfreshR⟩
  · -- live
    refine liveRep_clearKeys hP.live (fun v => ?_) hEA (by rw [hwl])
    rw [ewa _ (by simp), hwa9 _ (by simp)]; simp only [hs8, State.charge_wa, State.setW_wa]
    rw [hwa7 _ (by simp [slotW]), hl6 v]
    simp only [hs5, State.charge_wa, State.setW_wa]
    rw [hwa4 _ (by simp)]
  · -- fresh
    intro p hp
    rw [hfreshR]
    have hstk' : ∀ x, x < bse + restF.length → r.wa "dsl.stk" x = s0.wa "dsl.stk" x := by
      intro x hx
      rw [(eblk x).2.2.2.2.1, if_neg (by omega), hwa9 _ (by simp)]
      simp only [hs8, State.charge_wa, State.setW_wa]
      rw [hwa7 _ (by simp [slotW]), hwa6 _ (by simp)]; simp only [hs5, State.charge_wa, State.setW_wa]
      rw [hwa4 _ (by simp)]
    have hrr : recsOf r bse restF = recsOf s0 bse restF := recsOf_congr bse restF hstk'
    rw [recsOf_cons, hrr, (eblk _).2.2.2.2.1, if_pos rfl] at hp
    simp only [List.cons_append, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hpidf
    · exact hP.fresh p hp
  · -- the S row
    refine ⟨by simpa using (List.length_filter_le _ _).trans hcn, by rw [hwl]; exact hSw,
      by rw [hwl]; exact hSlw, by rw [hSlr, hSl6]; simp [hla], fun i hi => ?_⟩
    have hi' : i < a := by simp at hi; omega
    rw [hSr, hS6 i hi']
    have := keysOf_get s5 (base + c) a i hi'
    rw [← this]
    simp only [hkeys5]
  · -- the slot
    refine hsl7.of_slot_eq ?_ (fun a' ha' => ?_)
    · rw [eva, (hu9.varr _ (by simp)).1]; simp [hs8]
    · rw [ewa a' (by simp [slotW] at ha' ⊢; rcases ha' with rfl | rfl | rfl | rfl | rfl <;> simp),
        hwa9 a' (by simp [slotW] at ha' ⊢; rcases ha' with rfl | rfl | rfl | rfl | rfl <;> simp)]
      simp [hs8]
  · -- S outside the row
    intro i hi
    have e1 : (row + 1) * G.n = row * G.n + G.n := by ring
    rw [hSr, hSo6 i (by omega), hS5]
  · intro j hj
    rw [hSlr, hSlo6 j hj, hSl5]
  · -- other slots
    intro i hi
    have hva7' : ∀ c', c' ≠ "sl.l" → s7.va c' = s0.va c' := fun c' hc' => by
      rw [(hu7.varr c' (by simpa using hc')).1, hva6]
    refine ⟨?_, fun a' ha' => ?_⟩
    · rw [eva, (hu9.varr _ (by simp)).1]; simp only [hs8, State.charge_va, State.setW_va]
      rw [(hslo7 i hi).1, hva6]
    · rw [ewa a' (by simp [slotW] at ha' ⊢; rcases ha' with rfl | rfl | rfl | rfl | rfl <;> simp),
        hwa9 a' (by simp [slotW] at ha' ⊢; rcases ha' with rfl | rfl | rfl | rfl | rfl <;> simp)]
      simp only [hs8, State.charge_wa, State.setW_wa]
      rw [(hslo7 i hi).2 a' ha', hwa6 a' (by simp [slotW] at ha' ⊢; rcases ha' with rfl | rfl | rfl | rfl | rfl <;> simp)]
      simp only [hs5, State.charge_wa, State.setW_wa]
      rw [hwa4 a' (by simp [slotW] at ha' ⊢; rcases ha' with rfl | rfl | rfl | rfl | rfl <;> simp)]
  · -- the frame
    have sub1 : ∀ y ∈ myRegs ++ entLessW ++ ["sp.med"], y ∈ pullWR := fun y hy => by
      simp only [pullWR, List.mem_append]; left; left; left; exact medRegs_sub hy
    have u02 : Unchanged s0 s2 pullWA pullVA pullWR pullVR := by
      rw [hs2, unch_charge', unch_setW' (by simp [pullWR, splitWR]), unch_charge',
        unch_setW' (by simp [pullWR, plRegs])]
      exact Unchanged.refl _ _ _ _ _
    have u24' : Unchanged s2 s4 pullWA pullVA pullWR pullVR :=
      u24.mono (by simp [pullWA, splitWA]) (by simp) sub1 (List.Subset.refl _)
    have u45 : Unchanged s4 s5 pullWA pullVA pullWR pullVR := by
      rw [hs5, unch_charge', unch_setW' (by simp [pullWR]), unch_charge', unch_setW' (by simp [pullWR])]
      exact Unchanged.refl _ _ _ _ _
    have u56 : Unchanged s5 s6 pullWA pullVA pullWR pullVR :=
      hu6.mono (by intro a' ha'; simp at ha'; rcases ha' with rfl | rfl | rfl <;> simp [pullWA])
        (by simp) (by intro a' ha'; simp at ha'; rcases ha' with rfl | rfl | rfl <;> simp [pullWR]) (by simp)
    have u67 : Unchanged s6 s7 pullWA pullVA pullWR pullVR :=
      hu7.mono (by intro a' ha'; simp [pullWA]; right; right; right; right; exact ha') (by simp [pullVA])
        (by intro a' ha'; simp only [pullWR, List.mem_append]; right; exact ha') (by simp [pullVR, entLessV])
    have u78 : Unchanged s7 s8 pullWA pullVA pullWR pullVR := by
      rw [hs8, unch_charge', unch_setW' (by simp [pullWR, splitWR, linkRegs]), unch_charge',
        unch_setW' (by simp [pullWR, splitWR, linkRegs])]
      exact Unchanged.refl _ _ _ _ _
    have u89 : Unchanged s8 s9 pullWA pullVA pullWR pullVR :=
      hu9.mono (by simp [pullWA, splitWA]) (by simp)
        (by intro y hy; simp only [pullWR, splitWR, List.mem_append]; left; left; left; right
            simp only [linkRegs, List.mem_append]; right; exact hy) (by simp)
    have u9r : Unchanged s9 r pullWA pullVA pullWR pullVR := by
      refine ⟨fun c' hc' => ⟨ewa c' (fun h => hc' ?_), by rw [ewl]⟩, fun c' _ => ⟨by rw [eva], by rw [evl]⟩,
        fun y _ => by rw [ew], fun y _ => by rw [ev], ecap, epr⟩
      simp at h; simp [pullWA, splitWA]
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    exact u02.trans (u24'.trans (u45.trans (u56.trans (u67.trans (u78.trans (u89.trans u9r))))))
  · intro x hx
    rw [(eblk x).2.2.2.2.1, if_neg (by omega), hwa9 _ (by simp)]
    simp only [hs8, State.charge_wa, State.setW_wa]
    rw [hwa7 _ (by simp [slotW]), hwa6 _ (by simp)]; simp only [hs5, State.charge_wa, State.setW_wa]
    rw [hwa4 _ (by simp)]
  · intro l hl
    rw [(eblk l).2.2.2.2.2, if_neg hl, hwa9 _ (by simp)]
    simp only [hs8, State.charge_wa, State.setW_wa]
    rw [hwa7 _ (by simp [slotW]), hwa6 _ (by simp)]; simp only [hs5, State.charge_wa, State.setW_wa]
    rw [hwa4 _ (by simp)]
  · -- cost
    rw [ecost]
    have hK : Ksel 23 = 11300 := by simp [Ksel]
    rw [hK] at hc3 ⊢
    simp only [hs8, State.charge_cost, State.setW_cost, List.length_map] at hc9
    simp only [hs5, State.charge_cost, State.setW_cost] at hc6
    simp only [hs2, State.charge_cost, State.setW_cost] at hc3
    rw [hlb] at hc9
    omega

end CutSpec

/-! ## The complete Pull -/

/-- **RAM Pull** on the level structure (`ds.lv`, `ds.b`, `ds.M` set by the caller): collect (with
lazy splitting of each block before it is taken), then cut at rank `M` or take everything -/
def pullS (pSel : ℕ) : Stmt :=
  seq (wset "pl.row" (sub (var "ds.lv") (lit 1)))
  (seq (wset "pl.rb" (mul (var "pl.row") (var "n")))
  (seq (wset "pl.base" (lit 0))
  (seq (wset "pl.cnt" (lit 0))
  (seq (wset "sp.w0" (lit 0))
  (seq (wset "pl.go" (lit 1))
  (seq (colLoop pSel)
       (ite (lt (var "ds.M") (var "pl.cnt")) (pullCut pSel) pullAll)))))))

/-- cost constant of Pull -/
def Kpull : ℕ := Kcol + 11500

section PullTop

open Frontier.CHD.DIns Frontier.CHD.DB Frontier.CHD.DL Frontier.CHD.MLab Frontier.CHD.LabTab
  Frontier.CHD.DList Frontier.CHD.RamLevel

variable {G : Graph} {s : Fin G.n}

/-- a prefix frame composes with the finish's result -/
theorem PullRes.prefix {q s0 r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap lv bse row : ℕ} {L' : Live (Fin G.n) (WLab G s)} {D' : DStr (Fin G.n) (WLab G s)}
    {ext : List (ℕ × Block (Fin G.n) (WLab G s))} {ks : List (Fin G.n)} {sep : WLab G s}
    (h : PullRes s0 r H V bcap lv bse L' D' ext row ks sep)
    (hu : Unchanged q s0 pullWA pullVA pullWR pullVR)
    (hS : ∀ i, s0.wa "S" i = q.wa "S" i) (hSl : ∀ j, s0.wa "S.len" j = q.wa "S.len" j)
    (hsl : ∀ i, s0.va "sl.l" i = q.va "sl.l" i ∧ ∀ a ∈ slotW, s0.wa a i = q.wa a i)
    (hwl : s0.wlen = q.wlen) (hvl : s0.vlen = q.vlen)
    (hstk : ∀ x, x < bse → s0.wa "dsl.stk" x = q.wa "dsl.stk" x)
    (hsz : ∀ l, l ≠ lv → s0.wa "dsl.sz" l = q.wa "dsl.sz" l)
    (hfr : q.w "blk.fresh" ≤ s0.w "blk.fresh") (hea : EntArrSame q s0) :
    PullRes q r H V bcap lv bse L' D' ext row ks sep :=
  ⟨h.drep, h.recs, h.live, h.barr, h.fresh, h.rowr, h.slot, fun i hi => by rw [h.Sout i hi, hS],
    fun j hj => by rw [h.Slen j hj, hSl], fun i hi => ⟨by rw [(h.slots i hi).1, (hsl i).1],
      fun a ha => by rw [(h.slots i hi).2 a ha, (hsl i).2 a ha]⟩, hu.trans h.unch, by rw [h.wlen, hwl],
    by rw [h.vlen, hvl], fun x hx => by rw [h.stk x hx, hstk x hx], fun l hl => by rw [h.sz l hl, hsz l hl],
    le_trans hfr h.fr, hea.trans h.earr⟩

set_option maxHeartbeats 16000000 in
/-- **F-PULL: the RAM Pull refines `DLazy.pullL 1`** on agent-02's representation: the pulled keys
go to row `lv - 1` of `S`, the separator to slot `B_i[lv]`, the new structure / live map are
represented, and the cost is `≤ Kpull · (Layer-A cost + 1)`. -/
theorem pullS_spec (hH : GoodHist (s := s) H V) (pSel : ℕ) (q : State ℝ≥0)
    {bcap lv bse w0 M : ℕ} {Bd : WLab G s} {bs : List (Block (Fin G.n) (WLab G s))}
    {L : Live (Fin G.n) (WLab G s)} {ext : List (ℕ × Block (Fin G.n) (WLab G s))}
    (hP : SplitPre q H V bcap lv bse w0 L ⟨M, Bd, bs⟩ ext pSel) (hne : bs ≠ [])
    (hlv1 : 1 ≤ lv) (hn : q.w "n" = G.n) (hrow : RowRep q "S" "S.len" G.n (lv - 1) [])
    (hBd : BdHolds q lv H V Bd) (hBL : BdLens q lv) (hSL : SlotLens q (4 * lv + 3))
    (hfc : q.w "blk.fresh" + (prepList L M 0 bs).2 ≤ bcap)
    (hsc : bse + bs.length + (prepList L M 0 bs).2 ≤ q.wlen "dsl.stk")
    (hwc : 6 * (allEnts bs).length + 60 ≤ q.wlen "sel.w")
    (hcapS : lv * G.n + 2 * (allEnts bs).length + 2 < q.cap) (hcap4 : 4 * lv + 4 < q.cap) :
    Runs realOps (pullS pSel) q (fun r =>
      PullRes q r H V bcap lv bse (pullL 1 L ⟨M, Bd, bs⟩).2.2.1 (pullL 1 L ⟨M, Bd, bs⟩).2.2.2.1 ext
        (lv - 1) (pullL 1 L ⟨M, Bd, bs⟩).1 (pullL 1 L ⟨M, Bd, bs⟩).2.1 ∧
      r.cost ≤ q.cost + Kpull * ((pullL 1 L ⟨M, Bd, bs⟩).2.2.2.2 + 1) ∧
      r.w "blk.fresh" ≤ q.w "blk.fresh" + (pullL 1 L ⟨M, Bd, bs⟩).2.2.2.2) := by
  have hc1 : 1 < q.cap := by have := hP.c300; omega
  have hmulc : (lv - 1) * G.n < q.cap := by
    have : (lv - 1) * G.n ≤ lv * G.n := Nat.mul_le_mul_right _ (by omega)
    omega
  unfold pullS
  apply runs_seq
  refine runs_wset (a := lv - 1) (by simp [hP.lv, fit_of_lt hc1]) ?_
  apply runs_seq
  refine runs_wset (a := (lv - 1) * G.n) (by simp [hn, fit_of_lt hmulc]) ?_
  apply runs_seq
  refine runs_wset (a := 0) (by simp [fit_of_lt (show 0 < q.cap by omega)]) ?_
  apply runs_seq
  refine runs_wset (a := 0) (by simp [fit_of_lt (show 0 < q.cap by omega)]) ?_
  apply runs_seq
  refine runs_wset (a := 0) (by simp [fit_of_lt (show 0 < q.cap by omega)]) ?_
  apply runs_seq
  refine runs_wset (a := 1) (by simp [fit_of_lt hc1]) ?_
  set q1 := (((((((((((q.setW "pl.row" (lv - 1)).charge 1).setW "pl.rb" ((lv - 1) * G.n)).charge 1).setW
    "pl.base" 0).charge 1).setW "pl.cnt" 0).charge 1).setW "sp.w0" 0).charge 1).setW "pl.go" 1).charge 1
    with hq1
  have hu1 : Unchanged q q1 ["sel.w"] [] (["pl.row", "pl.rb", "pl.base", "pl.cnt", "sp.w0", "pl.go"]) [] := by
    rw [hq1]
    simp only [unch_charge']
    rw [unch_setW' (by simp), unch_charge', unch_setW' (by simp), unch_charge', unch_setW' (by simp),
      unch_charge', unch_setW' (by simp), unch_charge', unch_setW' (by simp), unch_charge',
      unch_setW' (by simp)]
    exact Unchanged.refl _ _ _ _ _
  have hP1 : SplitPre q1 H V bcap lv bse 0 L ⟨M, Bd, bs⟩ ext pSel :=
    hP.transfer hu1 (by simp) (by simp [hq1]) (by simp [hq1]) (by simp [hq1])
  have hI : ColInv q1 H V bcap lv bse 0 M Bd L ext pSel [] bs := by
    refine ⟨by simpa using hP1, fun i hi => absurd hi (by simp), by simp [hq1], by simp [hq1], ?_,
      fun e he => absurd he (by simp), by simpa [hq1] using hfc, by simpa [hq1] using hsc,
      by simpa [hq1] using hwc⟩
    simpa using hP1.recs.2.2
  apply runs_seq
  refine (col_loop hH pSel 0 bs q1 [] rfl (by omega) hne hI (by simp [hq1])).mono
    (fun r ⟨hO, hcr⟩ => ?_)
  set X := (prepList L M 0 bs).1 with hXd
  set C := collect L M [] X with hCd
  set accF := C.1 with haccd
  set restF := C.2.1 with hrestd
  have hAX : (allEnts X).length ≤ (allEnts bs).length := (prepList_subperm L M 0 bs).length_le
  have hacc : accF.length ≤ (allEnts bs).length := le_trans (collect_len_le L M X) hAX
  -- frame of the prefix q → r
  have hwaq1 : ∀ c, c ≠ "sel.w" → q1.wa c = q.wa c := fun c hc => (hu1.warr c (by simpa using hc)).1
  have hwar : ∀ c, c ∉ splitWA → r.wa c = q.wa c := fun c hc => by
    rw [(hO.unch.warr c hc).1, hwaq1 c (by intro h; apply hc; rw [h]; simp [splitWA])]
  have hwlq1 : q1.wlen = q.wlen := by simp [hq1]
  have hvlq1 : q1.vlen = q.vlen := by simp [hq1]
  have hvar : ∀ c, c ≠ "blk.len" → r.va c = q.va c := fun c hc => by
    rw [(hO.unch.varr c (by simpa using hc)).1]; simp [hq1]
  have hregr : ∀ y, y ∉ splitWR ++ plRegs → y ∉ ["pl.row", "pl.rb", "pl.base", "pl.cnt", "sp.w0", "pl.go"] →
      r.w y = q.w y := fun y h1 h2 => by rw [hO.unch.wreg y h1, hu1.wreg y h2]
  have huq : Unchanged q (r.charge 1) pullWA pullVA pullWR pullVR := by
    rw [unch_charge']
    refine (hu1.mono (by simp [pullWA, splitWA]) (by simp) ?_ (by simp)).trans
      (hO.unch.mono (fun a ha => by simp only [pullWA, List.mem_append]; left; left; exact ha) (by simp [pullVA])
        (fun a ha => by simp only [pullWR, List.mem_append] at ha ⊢; tauto)
        (List.Subset.refl _))
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [pullWR, plRegs]
  have hS0 : ∀ i, (r.charge 1).wa "S" i = q.wa "S" i := fun i => by
    simp only [State.charge_wa]; rw [hwar _ (by simp [splitWA])]
  have hSl0 : ∀ j, (r.charge 1).wa "S.len" j = q.wa "S.len" j := fun j => by
    simp only [State.charge_wa]; rw [hwar _ (by simp [splitWA])]
  have hsl0 : ∀ i, (r.charge 1).va "sl.l" i = q.va "sl.l" i ∧ ∀ a ∈ slotW, (r.charge 1).wa a i = q.wa a i :=
    fun i => ⟨by simp only [State.charge_va]; rw [hvar _ (by simp)], fun a ha => by
      simp only [State.charge_wa]
      rw [hwar a (by simp [slotW] at ha; simp [splitWA]; rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp)]⟩
  have hwl0 : (r.charge 1).wlen = q.wlen := by simp only [State.charge_wlen]; rw [hO.wlen, hwlq1]
  have hvl0 : (r.charge 1).vlen = q.vlen := by simp only [State.charge_vlen]; rw [hO.vlen, hvlq1]
  have hstk0 : ∀ x, x < bse → (r.charge 1).wa "dsl.stk" x = q.wa "dsl.stk" x := fun x hx => by
    simp only [State.charge_wa]; rw [hO.stk x hx, hwaq1 _ (by simp)]
  have hsz0 : ∀ l, l ≠ lv → (r.charge 1).wa "dsl.sz" l = q.wa "dsl.sz" l := fun l hl => by
    simp only [State.charge_wa]; rw [hO.sz l hl, hwaq1 _ (by simp)]
  have hfr0 : q.w "blk.fresh" ≤ (r.charge 1).w "blk.fresh" := by
    simp only [State.charge_w]; have := hO.fr1; simp [hq1] at this; exact this
  have hea0 : EntArrSame q (r.charge 1) := ⟨by simp only [State.charge_wa]; rw [hwar _ (by simp [splitWA])],
    by simp only [State.charge_va]; rw [hvar _ (by simp)], by simp only [State.charge_wa]; rw [hwar _ (by simp [splitWA])],
    by simp only [State.charge_wa]; rw [hwar _ (by simp [splitWA])],
    by simp only [State.charge_wa]; rw [hwar _ (by simp [splitWA])],
    by simp only [State.charge_wa]; rw [hwar _ (by simp [splitWA])]⟩
  -- common facts at the finish
  have hrow0 : RowRep (r.charge 1) "S" "S.len" G.n (lv - 1 : ℕ) [] :=
    hrow.of_eq (by rw [hwl0]) (by rw [hwl0]) (hSl0 _) (fun i _ => hS0 _)
  have hrb0 : (r.charge 1).w "pl.rb" = (lv - 1) * G.n := by
    simp only [State.charge_w]; rw [hO.unch.wreg _ (by simp [splitWR, plRegs, DList.walkRegs, myRegs, lessRegs,
      csRegs, selRegs, entLessW, fsX, fsY, LReg.ws, linkRegs, DList.buildRegs])]; simp [hq1]
  have hrr0 : (r.charge 1).w "pl.row" = lv - 1 := by
    simp only [State.charge_w]; rw [hO.unch.wreg _ (by simp [splitWR, plRegs, DList.walkRegs, myRegs, lessRegs,
      csRegs, selRegs, entLessW, fsX, fsY, LReg.ws, linkRegs, DList.buildRegs])]; simp [hq1]
  have hSL0 : SlotLens (r.charge 1) (4 * lv + 3) :=
    ⟨by rw [hvl0]; exact hSL.l, by rw [hwl0]; exact hSL.h, by rw [hwl0]; exact hSL.v,
      by rw [hwl0]; exact hSL.e, by rw [hwl0]; exact hSL.r, by rw [hwl0]; exact hSL.f⟩
  have hcap0 : (r.charge 1).cap = q.cap := by simp only [State.charge_cap]; rw [hO.unch.cap]; simp [hq1]
  have hlvn : (lv - 1 + 1) * G.n = lv * G.n := by congr 1; omega
  have hg : evalW r (lt (var "ds.M") (var "pl.cnt")) = some (if M < accF.length then 1 else 0) :=
    evalW_lt_of (by simp [hO.pre.M]) (by simp [hO.cntreg]) (by rw [hO.unch.cap]; simp [hq1]; exact hc1)
  have hq1c : q1.cost = q.cost + 6 := by simp [hq1]
  by_cases hMc : M < accF.length
  · refine runs_ite_true (x := 1) (by rw [hg, if_pos hMc]) one_ne_zero ?_
    refine (pullCut_spec hH pSel (r.charge 1) (hO.pre.charge 1) hO.spell (by simpa using hO.cntreg)
      (by simpa using hO.basereg) hO.nd hO.ents hO.pid (by simpa using hO.pidf) (by simpa using hO.pidb)
      (by simpa using hO.wcap) (by simpa using hO.scap) hMc hrow0 hrb0 hrr0 hSL0
      (by rw [hcap0, hlvn]; omega) (by rw [hcap0]; exact hcap4)).mono (fun r' ⟨hR', hc', hfr'⟩ => ?_)
    rw [pullL_cut L M Bd bs hMc]
    refine ⟨hR'.prefix huq hS0 hSl0 hsl0 hwl0 hvl0 hstk0 hsz0 hfr0 hea0, ?_, ?_⟩
    swap
    · dsimp only
      rw [hfr']
      simp only [State.charge_w]
      have := hO.fr2
      simp only [hq1, State.charge_w, State.setW_w] at this
      simp at this
      omega
    dsimp only
    simp only [State.charge_cost] at hc'
    have hK : Ksel 23 = 11300 := rfl
    have hKc : Kcol = 11511 := rfl
    have hKp : Kpull = 23011 := rfl
    rw [hK] at hc'
    rw [hKc, hq1c] at hcr
    rw [hKp]
    generalize (prepList L M 0 bs).2 = P at hcr ⊢
    generalize (selectC ((collect L M [] (prepList L M 0 bs).1).1.map (·.val)) M).2 = Sel
    generalize hSc : (collect L M [] (prepList L M 0 bs).1).2.2.2 = Sc at hcr ⊢
    generalize hRm : (collect L M [] (prepList L M 0 bs).1).2.2.1 = Rm at hcr ⊢
    generalize hA : (collect L M [] (prepList L M 0 bs).1).1.length = A at hc' ⊢
    omega
  · have hrest : restF = [] := collect_rest_nil L M X hMc
    refine runs_ite_false (by rw [hg, if_neg hMc]) ?_
    have hP0 : SplitPre (r.charge 1) H V bcap lv bse (0 + accF.length) L ⟨M, Bd, []⟩ ext pSel := by
      rw [← hrest]; exact hO.pre.charge 1
    have hnd0 : (accF.map (·.id) ++ entIds ((recsOf (r.charge 1) bse [] ++ ext).map Prod.snd)).Nodup := by
      rw [← hrest]; exact hO.nd
    have hpid0 : (r.charge 1).w "pl.pid" ∉ (recsOf (r.charge 1) bse [] ++ ext).map Prod.fst := by
      rw [← hrest]; exact hO.pid
    have hsc0 : bse + 1 ≤ (r.charge 1).wlen "dsl.stk" := by
      have := hO.scap; rw [hrest] at this; simpa using this
    have hBd0 : BdHolds (r.charge 1) lv H V Bd :=
      hBd.of_eq (fun a ha => by
        simp only [State.charge_wa]
        rw [hwar a (by simp at ha; simp [splitWA]; rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp)])
        (by simp only [State.charge_va]; rw [hvar _ (by simp)])
    have hBL0 : BdLens (r.charge 1) lv :=
      ⟨by rw [hvl0]; exact hBL.bl, by rw [hwl0]; exact hBL.bh, by rw [hwl0]; exact hBL.bv,
        by rw [hwl0]; exact hBL.be, by rw [hwl0]; exact hBL.br, by rw [hwl0]; exact hBL.bf⟩
    refine (pullAll_spec (r.charge 1) hP0 hO.spell (by simpa using hO.cntreg) (by simpa using hO.basereg)
      hnd0 hO.ents hpid0 (by simpa using hO.pidf) (by simpa using hO.pidb) (by simpa using hO.wcap) hsc0
      hrow0 hrb0 hrr0 hBd0 hBL0 hSL0 (by rw [hcap0, hlvn]; omega) (by rw [hcap0]; exact hcap4)).mono
      (fun r' ⟨hR', hc', hfr'⟩ => ?_)
    rw [pullL_all L M Bd bs hMc]
    refine ⟨hR'.prefix huq hS0 hSl0 hsl0 hwl0 hvl0 hstk0 hsz0 hfr0 hea0, ?_, ?_⟩
    swap
    · dsimp only
      rw [hfr']
      simp only [State.charge_w]
      have := hO.fr2
      simp only [hq1, State.charge_w, State.setW_w] at this
      simp at this
      omega
    dsimp only
    simp only [State.charge_cost] at hc'
    have hKc : Kcol = 11511 := rfl
    have hKp : Kpull = 23011 := rfl
    rw [hKc, hq1c] at hcr
    rw [hKp]
    generalize (prepList L M 0 bs).2 = P at hcr ⊢
    generalize hSc : (collect L M [] (prepList L M 0 bs).1).2.2.2 = Sc at hcr ⊢
    generalize hRm : (collect L M [] (prepList L M 0 bs).1).2.2.1 = Rm at hcr ⊢
    generalize hA : (collect L M [] (prepList L M 0 bs).1).1.length = A at hc' ⊢
    omega

end PullTop

end Frontier.CHD.DPull
