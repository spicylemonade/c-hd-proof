import Frontier.CHD.DRep
import Frontier.CHD.BSearch

/-!
# DInsert — RAM Insert of the DS' structure (B-L3, agent-02, NON-GATE)

Layer-A target: agent-04's lazy-split `insertL` (DLazy): skip if the live entry of `v` has value
`≤ λ`; otherwise a fresh entry `⟨fresh, v, λ⟩` is PREPENDED to the owning block (the last block,
in list order, whose separator is `≤ λ`), with no split.  This file states it as the pure function
`insertNS` (`prependOwner` = DBlocks' `addTo` without `fixBlock`).

Part 1 (this section): the pure list facts the RAM search needs — the owner block index, its
characterization as the first stack position whose separator is `≤ λ`, and separator
monotonicity from `IntervalOK`.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.DIns

open Frontier Frontier.CHD Frontier.CHD.DB

variable {κ : Type*} [DecidableEq κ] {α : Type*} [LinearOrder α] [Inhabited α]

/-- DBlocks' `addTo` without splitting: prepend `e` to the owning block. -/
def prependOwner (lam : α) (e : Entry κ α) : List (Block κ α) → List (Block κ α)
  | [] => []
  | [b] => [⟨b.sep, e :: b.ents⟩]
  | b :: b' :: bs =>
    if sepLe b'.sep lam then b :: prependOwner lam e (b' :: bs)
    else ⟨b.sep, e :: b.ents⟩ :: b' :: bs

/-- Insert without split (the state part of DLazy's `insertL`). -/
def insertNS (L : Live κ α) (fresh : ℕ) (D : DStr κ α) (v : κ) (lam : α) :
    Live κ α × ℕ × DStr κ α :=
  if skipIns L v lam then (L, fresh, D)
  else (Function.update L v (some (fresh, lam)), fresh + 1,
    { D with blocks := prependOwner lam ⟨fresh, v, lam⟩ D.blocks })

/-- The owning block's list index: how many blocks after the first have separator `≤ λ`
(contiguously). -/
def ownerIdx (lam : α) : List (Block κ α) → ℕ
  | [] => 0
  | [_] => 0
  | _ :: b' :: bs => if sepLe b'.sep lam then ownerIdx lam (b' :: bs) + 1 else 0

/-- Prepending at a list index. -/
def prependAt (e : Entry κ α) : ℕ → List (Block κ α) → List (Block κ α)
  | _, [] => []
  | 0, b :: bs => ⟨b.sep, e :: b.ents⟩ :: bs
  | i + 1, b :: bs => b :: prependAt e i bs

theorem prependOwner_eq (lam : α) (e : Entry κ α) :
    ∀ bs : List (Block κ α), prependOwner lam e bs = prependAt e (ownerIdx lam bs) bs
  | [] => rfl
  | [b] => rfl
  | b :: b' :: bs => by
    simp only [prependOwner, ownerIdx]
    split_ifs with h
    · rw [prependOwner_eq lam e (b' :: bs)]; rfl
    · rfl

theorem ownerIdx_lt (lam : α) : ∀ bs : List (Block κ α), bs ≠ [] → ownerIdx lam bs < bs.length
  | [], h => absurd rfl h
  | [_], _ => by simp [ownerIdx]
  | _ :: b' :: bs, _ => by
    simp only [ownerIdx]
    split_ifs
    · have := ownerIdx_lt lam (b' :: bs) (List.cons_ne_nil _ _)
      simp only [List.length_cons] at this ⊢; omega
    · simp

/-- Separators of a list of blocks satisfying `IntervalOK` strictly increase, all `≥ lo`. -/
theorem sep_pairwise {L : Live κ α} :
    ∀ {bs : List (Block κ α)} {lo hi : WithBot α}, IntervalOK L bs lo hi →
      List.Pairwise (fun a b : Block κ α => a.sep < b.sep) bs ∧ ∀ c ∈ bs, lo ≤ c.sep
  | [], _, _, _ => ⟨List.Pairwise.nil, fun _ h => absurd h List.not_mem_nil⟩
  | [b], _, _, h => ⟨List.pairwise_singleton _ _, fun c hc => by
      simp only [List.mem_singleton] at hc; subst hc; exact le_of_eq h.1.symm⟩
  | b :: b' :: bs, lo, hi, h => by
    obtain ⟨h1, h2, _, h4⟩ := h
    obtain ⟨hp, hlo⟩ := sep_pairwise h4
    refine ⟨List.Pairwise.cons (fun c hc => ?_) hp, fun c hc => ?_⟩
    · rw [h1]; exact lt_of_lt_of_le h2 (hlo c hc)
    · simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact le_of_eq h1.symm
      · exact le_trans (le_of_lt h2) (hlo c (List.mem_cons.mpr hc))

omit [DecidableEq κ] [Inhabited α] in
theorem sep_first {L : Live κ α} {bs : List (Block κ α)} {lo hi : WithBot α}
    (h : IntervalOK L bs lo hi) (hne : bs ≠ []) :
    (bs[0]'(List.length_pos_of_ne_nil hne)).sep = lo := by
  match bs, h with
  | [b], h => exact h.1
  | b :: b' :: bs, h => exact h.1

/-- Characterization of the owner: blocks up to `ownerIdx` have separator `≤ λ`, later ones
`> λ` (given increasing separators with the first `≤ λ`). -/
theorem ownerIdx_spec (lam : α) :
    ∀ bs : List (Block κ α), List.Pairwise (fun a b : Block κ α => a.sep < b.sep) bs →
      ∀ (h0 : bs ≠ []), sepLe (bs[0]'(List.length_pos_of_ne_nil h0)).sep lam = true →
      ∀ i (hi : i < bs.length), (sepLe (bs[i]'hi).sep lam = true ↔ i ≤ ownerIdx lam bs)
  | [], _, h0, _, _, _ => absurd rfl h0
  | [b], _, _, hf, i, hi => by
    simp only [List.length_singleton] at hi
    have : i = 0 := by omega
    subst this; simpa [ownerIdx] using hf
  | b :: b' :: bs, hc, _, hf, i, hi => by
    have hc' : List.Pairwise (fun a b : Block κ α => a.sep < b.sep) (b' :: bs) :=
      (List.pairwise_cons.mp hc).2
    cases i with
    | zero => simp only [List.getElem_cons_zero] at hf ⊢; simp [hf]
    | succ i =>
      simp only [List.getElem_cons_succ, ownerIdx]
      split_ifs with hs
      · have := ownerIdx_spec lam (b' :: bs) hc' (List.cons_ne_nil _ _) (by simpa using hs) i
          (by simpa using hi)
        rw [this]; omega
      · simp only [Nat.le_zero, Nat.add_one_ne_zero, iff_false]
        intro hi'
        cases i with
        | zero => simp at hi'; exact hs hi'
        | succ i =>
          have hmono : b'.sep < ((b' :: bs)[i + 1]'(by simpa using hi)).sep :=
            List.pairwise_iff_getElem.mp hc' 0 (i + 1) (by simp) (by simpa using hi)
              (Nat.succ_pos _)
          have hi'' := (sepLe_iff _ _).mp hi'
          exact hs ((sepLe_iff _ _).mpr (le_of_lt (lt_of_lt_of_le hmono hi'')))

/-! ## Part 3: the probe of the separator search -/

section Probe

open Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD.MLab Frontier.CHD.LabTab Frontier.RAM.BSearch

variable {G : Graph} {s : Fin G.n}

theorem wp_ite_of {V : Type} {ops : VOps V} {c : WExpr} {a b : Stmt} {Q : State V → Prop}
    {st : State V} {x : ℕ} (he : evalW st c = some x) :
    wp ops (.ite c a b) Q st = ((x ≠ 0 → wp ops a Q (st.charge 1)) ∧
      (x = 0 → wp ops b Q (st.charge 1))) := by
  simp [wp, he]

/-- The key block: the value `λ` being inserted (set by the caller). -/
def KB : LReg := ⟨"ins.kl", "ins.kh", "ins.kv", "ins.ke", "ins.kr"⟩
/-- Scratch block for loaded labels. -/
def YB : LReg := ⟨"ins.yl", "ins.yh", "ins.yv", "ins.ye", "ins.yr"⟩

open WExpr Stmt in
/-- Probe: `bs.p := [sep(stk[ds.b + bs.mid]) ≤ λ]`. -/
def probe : Stmt :=
  seq (wset "ins.pb" (load "dsl.stk" (add (var "ds.b") (var "bs.mid"))))
  (seq (wset "ins.bot" (load "blk.bot" (var "ins.pb")))
  (ite (eq (var "ins.bot") (lit 1)) (wset "bs.p" (lit 1))
    (seq (loadA blkA "ins.pb" YB)
    (seq (cmp KB YB "ins.c1" "ins.c2" "ins.lt")
         (wset "bs.p" (eq (var "ins.lt") (lit 0)))))))

/-- Registers the probe writes. -/
def probeW : List String :=
  ["ins.pb", "ins.bot", "ins.yh", "ins.yv", "ins.ye", "ins.yr", "ins.c1", "ins.c2", "ins.lt", "bs.p"]

theorem stkId_rev {st : State ℝ≥0} {bse k j : ℕ} (hj : j < k) :
    stkId st bse k (k - 1 - j) = st.wa "dsl.stk" (bse + j) := by
  unfold stkId; congr 2; omega

/-- The search predicate on stack positions. -/
def Pj (D : DStr (Fin G.n) (WLab G s)) (lam : WLab G s) (j : ℕ) : Prop :=
  ∃ h : D.blocks.length - 1 - j < D.blocks.length, sepLe (D.blocks[D.blocks.length - 1 - j]).sep lam = true

noncomputable instance (D : DStr (Fin G.n) (WLab G s)) (lam : WLab G s) : DecidablePred (Pj D lam) := by
  intro j; unfold Pj; infer_instance

/-- The context the probe needs (and keeps). -/
def ProbeCtx (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ) (bcap lv bse : ℕ)
    (D : DStr (Fin G.n) (WLab G s)) (k : MLabel G) (p : List (Fin G.m)) (st : State ℝ≥0) : Prop :=
  DRep (s := s) st H V bcap lv bse D ∧ BlkArrs st bcap ∧ st.w "ds.lv" = lv ∧ st.w "ds.b" = bse ∧
    Holds st KB k ∧ Rep (s := s) H V k p ∧ 1 < st.cap ∧ bse + D.blocks.length + 2 < st.cap

theorem probe_spec (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (hH : GoodHist (s := s) H V) (bcap lv bse : ℕ) (D : DStr (Fin G.n) (WLab G s))
    (k : MLabel G) (p : List (Fin G.m)) (X : State ℝ≥0 → Prop)
    (hX : ∀ st r, X st → Unchanged st r [] [] probeW [YB.l] → X r) :
    ProbeSpec (ops := realOps) probe (fun r => ProbeCtx H V bcap lv bse D k p r ∧ X r)
      (Pj D ((toW p : WalkOrd G s) : WLab G s)) D.blocks.length 30 := by
  intro st ⟨hC, hXst⟩ hmid
  obtain ⟨hD, hBA, hlv, hb, hK, hKp, hcap1, hcap2⟩ := hC
  set j := st.w "bs.mid" with hj
  set nb := D.blocks.length with hnb
  have hi : nb - 1 - j < nb := by omega
  have hid : stkId st bse nb (nb - 1 - j) = st.wa "dsl.stk" (bse + j) := stkId_rev hmid
  have hbr := hD.blk (nb - 1 - j) hi
  have hbidlt := hD.bidb (nb - 1 - j) hi
  rw [hid] at hbr hbidlt
  set bid := st.wa "dsl.stk" (bse + j) with hbid
  obtain ⟨hsep, -, -, -, -⟩ := hbr
  obtain ⟨hbot, hsep2⟩ := hsep
  have hbj : bse + j < st.wlen "dsl.stk" := by have := hD.stkb; omega
  have hbb : bid < st.wlen "blk.bot" := lt_of_lt_of_le hbidlt hBA.2.2.2.1
  apply wp_sound
  rw [probe, wp_seq, wp_wset_of (a := bid) (by
    have : bse + j < st.cap := by omega
    simp [hb, ← hj, fit_of_lt this, hbj, hbid]), wp_seq, wp_wset_of (a := st.wa "blk.bot" bid) (by
    simp [hbb])]
  set q1 := ((st.setW "ins.pb" bid).charge 1) with hq1
  set q2 := (q1.setW "ins.bot" (st.wa "blk.bot" bid)).charge 1 with hq2
  have hU2 : Unchanged st q2 [] [] ["ins.pb", "ins.bot"] [] := by
    simp [hq2, q1, unch_setW]
  have hcapq : q2.cap = st.cap := hU2.cap
  have hbotq : q2.w "ins.bot" = st.wa "blk.bot" bid := by simp [hq2]
  have hpbq : q2.w "ins.pb" = bid := by simp [hq2, q1]
  have hbit : evalW q2 (WExpr.eq (WExpr.var "ins.bot") (WExpr.lit 1)) =
      some (if st.wa "blk.bot" bid = 1 then 1 else 0) := by
    rw [evalW_eq', evalW_var, evalW_lit', hbotq, fit_of_lt (by rw [hcapq]; exact hcap1)]
    simp only [Option.bind_some]
    exact fit_bit (by rw [hcapq]; exact hcap1) _
  rw [wp_ite_of hbit]
  have hctx : ∀ r : State ℝ≥0, Unchanged st r [] [] probeW [YB.l] →
      ProbeCtx H V bcap lv bse D k p r := by
    intro r hU
    have hw0 : ∀ a ∈ ([] : List String), a ∉ dW := by simp
    have hv0 : ∀ a ∈ ([] : List String), a ∉ dV := by simp
    refine ⟨hD.of_unchanged hU hw0 hv0, hBA.of_unchanged hU hw0 hv0, ?_, ?_,
      hK.of_unchanged hU (by decide) (by decide), hKp, by rw [hU.cap]; exact hcap1,
      by rw [hU.cap]; exact hcap2⟩
    · rw [hU.wreg _ (by decide)]; exact hlv
    · rw [hU.wreg _ (by decide)]; exact hb
  refine ⟨fun hb1 => ?_, fun hb0 => ?_⟩
  · -- separator `⊥`: `sepLe ⊥ λ`
    have hb1' : st.wa "blk.bot" bid = 1 := by by_contra h; simp [h] at hb1
    have hbot' : (D.blocks[nb - 1 - j]'hi).sep = ⊥ := hbot.mp hb1'
    refine wp_mono _ ?_ _ (wset_lit_wp (ops := realOps) "bs.p" 1 (q2.charge 1)
      (by simp [hcapq]; exact hcap1))
    rintro r ⟨h1, h2, h3⟩
    have hU : Unchanged st r [] [] probeW [YB.l] :=
      ((hU2.comp (Unchanged.charge q2 1 [] [] [] [])).comp h2).mono (by simp) (by simp)
        (by intro a; simp [probeW]; tauto) (by simp)
    refine ⟨⟨hctx r hU, hX st r hXst hU⟩, ?_, hU.wreg _ (by decide), hU.wreg _ (by decide), hU.wreg _ (by decide),
      hU.wreg _ (by decide), hU.cap, ?_, ?_⟩
    · rw [h1, if_pos]; exact ⟨hi, by rw [hbot']; rfl⟩
    · simp only [State.charge_cost] at h3; simp [hq2, q1] at h3; omega
    · simp only [State.charge_cost] at h3; simp [hq2, q1] at h3; omega
  · -- finite separator: load it and compare
    have hb0' : st.wa "blk.bot" bid ≠ 1 := by intro h; simp [h] at hb0
    have hnb : (D.blocks[nb - 1 - j]'hi).sep ≠ ⊥ := fun h => hb0' (hbot.mpr h)
    obtain ⟨m, q, hAm, hRm, hsq⟩ := hsep2.resolve_left hnb
    have hInB : blkA.InB (q2.charge 1) bid := by
      obtain ⟨-, -, -, -, h5, h6, h7, h8, h9⟩ := hBA
      unfold LArr.InB
      simp only [hq2, hq1, State.charge_vlen, State.charge_wlen, State.setW_wlen, State.setW_vlen]
      exact ⟨lt_of_lt_of_le hbidlt h5, lt_of_lt_of_le hbidlt h6, lt_of_lt_of_le hbidlt h7,
        lt_of_lt_of_le hbidlt h8, lt_of_lt_of_le hbidlt h9⟩
    have hAm' : AHolds (q2.charge 1) blkA bid m := by
      obtain ⟨a1, a2, a3, a4, a5⟩ := hAm
      exact ⟨by simpa [hq2, q1] using a1, by simpa [hq2, q1] using a2, by simpa [hq2, q1] using a3,
        by simpa [hq2, q1] using a4, by simpa [hq2, q1] using a5⟩
    rw [wp_seq]
    refine wp_mono _ ?_ _ (loadA_wp blkA "ins.pb" YB ⟨by decide, by decide⟩ (q2.charge 1) bid
      (by simpa using hpbq) hInB m hAm')
    rintro r1 ⟨hY1, hU1, hc1⟩
    have hK1 : Holds r1 KB k :=
      ((hK.of_unchanged hU2 (by decide) (by decide)).charge 1).of_unchanged hU1 (by decide)
        (by decide)
    have hcap1' : 1 < r1.cap := by rw [hU1.cap]; simp [hcapq]; exact hcap1
    rw [wp_seq]
    refine wp_mono _ ?_ _ (cmp_wp (ops := realOps) (fun a b => rfl) "ins.lt"
      ⟨by decide, by decide, by decide, by decide, by decide⟩ r1 hcap1')
    rintro r2 ⟨hlt2, hU2', hc2lo, hc2hi⟩
    rw [cbit_eq hK1 hY1] at hlt2
    refine wp_mono _ ?_ _ (wset_eqz_wp (ops := realOps) "bs.p" "ins.lt" r2
      (by rw [hU2'.cap]; exact hcap1'))
    rintro r ⟨h1, h2, h3⟩
    have hU : Unchanged st r [] [] probeW [YB.l] :=
      ((((hU2.comp (Unchanged.charge q2 1 [] [] [] [])).comp hU1).comp hU2').comp h2).mono
        (by simp) (by simp) (by intro a; first | (simp [probeW, YB, LReg.ws]; done) | (simp [probeW, YB, LReg.ws]; tauto)) (by simp [YB])
    have hiff := lt_iff hH hKp hRm
    refine ⟨⟨hctx r hU, hX st r hXst hU⟩, ?_, hU.wreg _ (by decide), hU.wreg _ (by decide), hU.wreg _ (by decide),
      hU.wreg _ (by decide), hU.cap, ?_, ?_⟩
    · rw [h1, hlt2]
      by_cases hkm : k.lt m
      · rw [if_pos hkm, if_neg one_ne_zero, if_neg]
        rintro ⟨_, hP⟩
        have hP' := (sepLe_iff _ _).mp hP
        rw [hsq] at hP'
        exact absurd (WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hP')) (not_le.mpr (hiff.mp hkm))
      · rw [if_neg hkm, if_pos rfl, if_pos]
        refine ⟨hi, (sepLe_iff _ _).mpr ?_⟩
        rw [hsq]
        exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (not_lt.mp (fun h => hkm (hiff.mpr h))))
    · simp only [State.charge_cost] at hc1 hc2lo h3 ⊢; simp [hq2, q1] at hc1; omega
    · simp only [State.charge_cost] at hc1 hc2hi h3 ⊢; simp [hq2, q1] at hc1; omega

end Probe

/-! ## Part 4: the insertion update on representations (state-level, program-free) -/

section Update

open Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD.MLab Frontier.CHD.LabTab

variable {G : Graph} {s : Fin G.n}

theorem prependAt_length (e : Entry κ α) :
    ∀ (i : ℕ) (bs : List (Block κ α)), (prependAt e i bs).length = bs.length
  | i, [] => by cases i <;> rfl
  | 0, b :: bs => rfl
  | i + 1, b :: bs => by simp [prependAt, prependAt_length e i bs]

theorem prependAt_get_ne (e : Entry κ α) :
    ∀ (i : ℕ) (bs : List (Block κ α)) (j : ℕ) (hj : j < bs.length), j ≠ i →
      (prependAt e i bs)[j]'(by rw [prependAt_length]; exact hj) = bs[j]
  | _, [], j, hj, _ => absurd hj (Nat.not_lt_zero _)
  | 0, b :: bs, j, hj, hne => by
    cases j with
    | zero => exact absurd rfl hne
    | succ j => rfl
  | i + 1, b :: bs, j, hj, hne => by
    cases j with
    | zero => rfl
    | succ j =>
      simp only [prependAt, List.getElem_cons_succ]
      exact prependAt_get_ne e i bs j (by simpa using hj) (by omega)

theorem prependAt_get_self (e : Entry κ α) :
    ∀ (i : ℕ) (bs : List (Block κ α)) (hi : i < bs.length),
      (prependAt e i bs)[i]'(by rw [prependAt_length]; exact hi) = ⟨bs[i].sep, e :: bs[i].ents⟩
  | _, [], hi => absurd hi (Nat.not_lt_zero _)
  | 0, b :: bs, _ => rfl
  | i + 1, b :: bs, hi => by
    simp only [prependAt, List.getElem_cons_succ]
    exact prependAt_get_self e i bs (by simpa using hi)

/-- The pointwise effect of the insertion writes (entry `fid` created, block record `bid` updated,
`live[v]` set), everything else in the D arrays unchanged. -/
structure InsFacts (st r : State ℝ≥0) (fid bid : ℕ) (v : Fin G.n) (k : MLabel G) : Prop where
  ekey : ∀ j, j ≠ fid → r.wa "ent.key" j = st.wa "ent.key" j
  enxt : ∀ j, j ≠ fid → r.wa "ent.nxt" j = st.wa "ent.nxt" j
  eflds : ∀ j, j ≠ fid → r.va entA.l j = st.va entA.l j ∧ r.wa entA.h j = st.wa entA.h j ∧
    r.wa entA.v j = st.wa entA.v j ∧ r.wa entA.e j = st.wa entA.e j ∧ r.wa entA.r j = st.wa entA.r j
  nkey : r.wa "ent.key" fid = v
  nnxt : r.wa "ent.nxt" fid = st.wa "blk.hd" bid
  nlab : AHolds r entA fid k
  hd : r.wa "blk.hd" bid = fid + 1
  cnt : r.wa "blk.cnt" bid = st.wa "blk.cnt" bid + 1
  tl : r.wa "blk.tl" bid = if st.wa "blk.tl" bid = 0 then fid + 1 else st.wa "blk.tl" bid
  oblk : ∀ b', b' ≠ bid → r.wa "blk.hd" b' = st.wa "blk.hd" b' ∧
    r.wa "blk.tl" b' = st.wa "blk.tl" b' ∧ r.wa "blk.cnt" b' = st.wa "blk.cnt" b'
  bot : r.wa "blk.bot" = st.wa "blk.bot"
  sep : r.va blkA.l = st.va blkA.l ∧ r.wa blkA.h = st.wa blkA.h ∧ r.wa blkA.v = st.wa blkA.v ∧
    r.wa blkA.e = st.wa blkA.e ∧ r.wa blkA.r = st.wa blkA.r
  stk : r.wa "dsl.stk" = st.wa "dsl.stk" ∧ r.wa "dsl.sz" = st.wa "dsl.sz"
  live : r.wa "live" v = fid + 1 ∧ ∀ u, u ≠ (v : ℕ) → r.wa "live" u = st.wa "live" u
  lens : ∀ a, r.wlen a = st.wlen a
  vlens : ∀ a, r.vlen a = st.vlen a

theorem EntRep.of_insFacts {st r : State ℝ≥0} {fid bid : ℕ} {v : Fin G.n} {k : MLabel G}
    {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {i : ℕ} {u : Fin G.n} {a : WLab G s}
    (hF : InsFacts st r fid bid v k) (h : EntRep st H V i u a) (hi : i ≠ fid) :
    EntRep r H V i u a := by
  obtain ⟨l1, l2, l3, l4, l5⟩ := hF.eflds i hi
  exact h.of_eq (hF.ekey i hi) l1 l2 l3 l4 l5

theorem LList.of_insFacts {st r : State ℝ≥0} {fid bid : ℕ} {v : Fin G.n} {k : MLabel G}
    {h : ℕ} {l : List ℕ} (hF : InsFacts (G := G) st r fid bid v k) (hl : LList st h l)
    (hfl : ∀ j ∈ l, j ≠ fid) : LList r h l :=
  hl.of_eq (fun j hj => hF.enxt j (hfl j hj)) (le_of_eq (hF.lens _).symm)

theorem SepRep.of_insFacts {st r : State ℝ≥0} {fid bid : ℕ} {v : Fin G.n} {k : MLabel G}
    {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {b : ℕ} {sp : WithBot (WLab G s)}
    (hF : InsFacts st r fid bid v k) (h : SepRep st H V b sp) : SepRep r H V b sp := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := hF.sep
  exact h.of_eq (by rw [hF.bot]) (by rw [s1]) (by rw [s2]) (by rw [s3]) (by rw [s4]) (by rw [s5])

theorem tlWord_cons (i : ℕ) (l : List ℕ) : tlWord (i :: l) = if l = [] then i + 1 else tlWord l := by
  cases l with
  | nil => rfl
  | cons j l =>
    simp only [tlWord, List.getLast?_cons_cons, reduceCtorEq, if_false]

theorem tlWord_eq_zero {l : List ℕ} : tlWord l = 0 ↔ l = [] := by
  cases hl : l.getLast? with
  | none => simp [tlWord, hl, List.getLast?_eq_none_iff.mp hl]
  | some i =>
    have hne : l ≠ [] := by intro h; rw [h] at hl; simp at hl
    simp [tlWord, hl, hne]

/-- The owner block after the writes. -/
theorem BlkRep.insert_owner {st r : State ℝ≥0} {fid bid : ℕ} {v : Fin G.n} {k : MLabel G}
    {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {b : Block (Fin G.n) (WLab G s)}
    {p : List (Fin G.m)} (hF : InsFacts st r fid bid v k) (h : BlkRep st H V bid b)
    (hfid : ∀ x ∈ b.ents, x.id ≠ fid) (hcap : fid < st.wlen "ent.nxt")
    (hkp : Rep (s := s) H V k p) :
    BlkRep r H V bid ⟨b.sep, ⟨fid, v, ((toW p : WalkOrd G s) : WLab G s)⟩ :: b.ents⟩ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hfl : ∀ j ∈ b.ents.map (·.id), j ≠ fid := by
    intro j hj; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hj; exact hfid x hx
  refine ⟨h1.of_insFacts hF, ?_, ?_, ?_, ?_⟩
  · simp only [List.map_cons]
    rw [hF.hd]
    refine LList.cons fid _ (by rw [hF.lens]; exact hcap) ?_
    rw [hF.nnxt]
    exact h2.of_insFacts hF hfl
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨hF.nkey, k, p, hF.nlab, hkp, rfl⟩
    · exact (h3 x hx).of_insFacts hF (hfid x hx)
  · rw [hF.cnt, h4]; rfl
  · rw [hF.tl, h5]
    simp only [List.map_cons, tlWord_cons]
    by_cases he : b.ents.map (·.id) = []
    · rw [if_pos (tlWord_eq_zero.mpr he), if_pos he]
    · rw [if_neg (fun h => he (tlWord_eq_zero.mp h)), if_neg he]

/-- Any other block after the writes. -/
theorem BlkRep.insert_other {st r : State ℝ≥0} {fid bid : ℕ} {v : Fin G.n} {k : MLabel G}
    {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {b' : ℕ} {b : Block (Fin G.n) (WLab G s)}
    (hF : InsFacts st r fid bid v k) (h : BlkRep st H V b' b) (hne : b' ≠ bid)
    (hfid : ∀ x ∈ b.ents, x.id ≠ fid) : BlkRep r H V b' b := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨o1, o2, o3⟩ := hF.oblk b' hne
  have hfl : ∀ j ∈ b.ents.map (·.id), j ≠ fid := by
    intro j hj; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hj; exact hfid x hx
  refine ⟨h1.of_insFacts hF, by rw [o1]; exact h2.of_insFacts hF hfl,
    fun x hx => (h3 x hx).of_insFacts hF (hfid x hx), by rw [o3]; exact h4, by rw [o2]; exact h5⟩

end Update

end Frontier.CHD.DIns
