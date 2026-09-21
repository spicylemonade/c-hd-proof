import Frontier.CHD.DGlobal

/-!
# DRekey — re-keying the parent's front block before a merge (B-L3, agent-04, NON-GATE)

In `DB.merge` the parent's front block `f` gets the separator `D'.Bd` (the child's bound) when
`ltSep D'.Bd (nextSep rest D.Bd)` ("keep").  `rekeyS X` stores the label held by the register block
`X` into the separator fields of the parent's front record and clears its `⊥` flag.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.DGlob

open Frontier Frontier.RAM Frontier.CHD Frontier.CHD.DB Frontier.CHD.DIns Frontier.CHD.DList
open Frontier.RAM.LabRAM Frontier.CHD.MLab Frontier.CHD.LabTab
open Frontier.RAM.WExpr Frontier.RAM.Stmt

variable {G : Graph} {s : Fin G.n}

/-- `rk.id := stk[rk.pb + rk.pk - 1]` (the parent's front record); `blkA[rk.id] := X`; `bot := 0` -/
def rekeyS (X : LReg) : Stmt :=
  seq (wset "rk.id" (load "dsl.stk" (sub (add (var "rk.pb") (var "rk.pk")) (lit 1))))
  (seq (storeA blkA "rk.id" X) (wstore "blk.bot" (var "rk.id") (lit 0)))

theorem blkA_nodup : blkA.Nodup := by
  simp [LArr.Nodup, LArr.ws, blkA]

/-- separator records survive when their bot flag and label fields survive -/
theorem sepRep_of_fields {q r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bid : ℕ} {sp : WithBot (WLab G s)} (h : SepRep q H V bid sp)
    (hbot : r.wa "blk.bot" bid = q.wa "blk.bot" bid)
    (hA : ∀ y : MLabel G, AHolds q blkA bid y → AHolds r blkA bid y) : SepRep r H V bid sp := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [hbot]; exact h1, ?_⟩
  rcases h2 with h2 | ⟨m, q', hm, hq, hsp⟩
  · exact Or.inl h2
  · exact Or.inr ⟨m, q', hA m hm, hq, hsp⟩

/-- the arrays `rekeyS` writes -/
def rkW : List String := ["blk.h", "blk.v", "blk.e", "blk.r", "blk.bot"]

/-- what `rekeyS` does to the arrays -/
structure RekeyFacts (st0 r : State ℝ≥0) (fid : ℕ) (x : MLabel G) : Prop where
  unch : Unchanged st0 r rkW ["blk.len"] ["rk.id"] []
  bot : ∀ j, j ≠ fid → r.wa "blk.bot" j = st0.wa "blk.bot" j
  bot0 : r.wa "blk.bot" fid = 0
  ahold : ∀ j, j ≠ fid → ∀ y : MLabel G, AHolds st0 blkA j y → AHolds r blkA j y
  anew : AHolds r blkA fid x

theorem rekeyS_noalloc (X : LReg) : NoAlloc (rekeyS X) := by
  simp [NoAlloc, rekeyS, storeA]

theorem rekey_facts (st0 : State ℝ≥0) (X : LReg) (x : MLabel G) (pb kP fid bcap : ℕ)
    (hX : Holds st0 X x) (hXr : "rk.id" ∉ X.ws) (hpb : st0.w "rk.pb" = pb) (hpk : st0.w "rk.pk" = kP)
    (hkP1 : 1 ≤ kP) (hfidv : st0.wa "dsl.stk" (pb + kP - 1) = fid) (hfidb : fid < bcap)
    (hBA : BlkArrs st0 bcap) (hstkl : pb + kP - 1 < st0.wlen "dsl.stk") (hcap : pb + kP + 1 < st0.cap) :
    Runs realOps (rekeyS X) st0 (fun r => RekeyFacts st0 r fid x ∧ r.cost = st0.cost + 7) := by
  obtain ⟨ba1, ba2, ba3, ba4, ba5, ba6, ba7, ba8, ba9⟩ := hBA
  have hc1 : 1 < st0.cap := by omega
  apply wp_sound
  rw [rekeyS, LabRAM.wp_seq, LabRAM.wp_wset_of (a := fid) (by
    simp [hpb, hpk, fit, show pb + kP < st0.cap by omega, hc1, hstkl, hfidv])]
  set q1 := (st0.setW "rk.id" fid).charge 1 with hq1
  have hUq1 : Unchanged st0 q1 [] [] ["rk.id"] [] := by
    rw [hq1, unch_charge, unch_setW (List.mem_singleton_self _)]; exact Unchanged.refl _ _ _ _ _
  have hX1 : Holds q1 X x := hX.of_unchanged hUq1
    (by intro a ha; simp only [List.mem_singleton]; intro h; subst h; exact hXr ha) (by simp)
  have hInB : blkA.InB q1 fid := by
    simp only [blkA] at ba5 ba6 ba7 ba8 ba9
    simp only [LArr.InB, hq1, State.charge_vlen, State.charge_wlen, State.setW_wlen, State.setW_vlen, blkA]
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  rw [LabRAM.wp_seq]
  refine wp_mono _ ?_ _ (storeA_wp blkA blkA_nodup "rk.id" X q1 fid (by simp [hq1]) hInB x hX1)
  rintro r1 ⟨hA1, hAo, hInB1, hU1, hc1'⟩
  have hU1w : ∀ a, a ∉ blkA.ws → r1.wa a = q1.wa a ∧ r1.wlen a = q1.wlen a := fun a ha => hU1.warr a ha
  have hr1id : r1.w "rk.id" = fid := by rw [hU1.wreg _ (by simp)]; simp [hq1]
  have hbotl : fid < r1.wlen "blk.bot" := by
    rw [(hU1w "blk.bot" (by simp [LArr.ws, blkA])).2]; simp [hq1]; omega
  have hr1cap : r1.cap = st0.cap := by rw [hU1.cap]; simp [hq1]
  rw [DList.wp_wstore_of (j := fid) (a := 0) (by simp [hr1id]) (by simp [fit, hr1cap]; omega) hbotl]
  have hq1wa : q1.wa = st0.wa := by simp [hq1]
  have hq1va : q1.va = st0.va := by simp [hq1]
  have hbot1 : r1.wa "blk.bot" = st0.wa "blk.bot" := by
    rw [(hU1w "blk.bot" (by simp [LArr.ws, blkA])).1, hq1wa]
  refine ⟨⟨?_, fun j hj => ?_, by simp, fun j hj y hy => ?_, ?_⟩, by simp [hc1', hq1]⟩
  · rw [unch_charge, unch_storeW (by simp [rkW])]
    exact (hUq1.comp hU1).mono (by simp [LArr.ws, blkA, rkW]) (by simp [blkA]) (by simp) (by simp)
  · simp [hj, hbot1]
  · have hy1 : AHolds q1 blkA j y := by
      obtain ⟨y1, y2, y3, y4, y5⟩ := hy
      exact ⟨by rw [hq1va]; exact y1, by rw [hq1wa]; exact y2, by rw [hq1wa]; exact y3,
        by rw [hq1wa]; exact y4, by rw [hq1wa]; exact y5⟩
    obtain ⟨z1, z2, z3, z4, z5⟩ := hAo j hj y hy1
    exact ⟨by simpa using z1, by simpa [blkA] using z2, by simpa [blkA] using z3,
      by simpa [blkA] using z4, by simpa [blkA] using z5⟩
  · obtain ⟨z1, z2, z3, z4, z5⟩ := hA1
    exact ⟨by simpa using z1, by simpa [blkA] using z2, by simpa [blkA] using z3,
      by simpa [blkA] using z4, by simpa [blkA] using z5⟩

/-! ## Lifting to the D layer -/

theorem ne_of_nodup_mid {l₁ l₂ : List ℕ} {a b : ℕ} (h : (l₁ ++ a :: l₂).Nodup) (hb : b ∈ l₁ ++ l₂) :
    b ≠ a := by
  rw [List.nodup_middle, List.nodup_cons] at h
  intro e; subst e; exact h.1 hb

/-- a block record keeps its entry list through `rekeyS` (given its new separator) -/
theorem blkRep_rekey {st0 r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {fid : ℕ} {x : MLabel G} (hR : RekeyFacts st0 r fid x) (hl : r.wlen "ent.nxt" = st0.wlen "ent.nxt")
    {bid : ℕ} {b : Block (Fin G.n) (WLab G s)} (h : BlkRep st0 H V bid b) {sp : WithBot (WLab G s)}
    (hsp : SepRep r H V bid sp) : BlkRep r H V bid ⟨sp, b.ents⟩ := by
  obtain ⟨_, h2, h3, h4, h5⟩ := h
  have e1 : r.wa "blk.hd" = st0.wa "blk.hd" := (hR.unch.warr _ (by simp [rkW])).1
  have e2 : r.wa "blk.tl" = st0.wa "blk.tl" := (hR.unch.warr _ (by simp [rkW])).1
  have e3 : r.wa "blk.cnt" = st0.wa "blk.cnt" := (hR.unch.warr _ (by simp [rkW])).1
  have e4 : r.wa "ent.nxt" = st0.wa "ent.nxt" := (hR.unch.warr _ (by simp [rkW])).1
  have e5 : r.wa "ent.key" = st0.wa "ent.key" := (hR.unch.warr _ (by simp [rkW])).1
  have e6 : r.wa "ent.h" = st0.wa "ent.h" := (hR.unch.warr _ (by simp [rkW])).1
  have e7 : r.wa "ent.v" = st0.wa "ent.v" := (hR.unch.warr _ (by simp [rkW])).1
  have e8 : r.wa "ent.e" = st0.wa "ent.e" := (hR.unch.warr _ (by simp [rkW])).1
  have e9 : r.wa "ent.r" = st0.wa "ent.r" := (hR.unch.warr _ (by simp [rkW])).1
  have e10 : r.va "ent.len" = st0.va "ent.len" := (hR.unch.varr _ (by simp)).1
  refine ⟨hsp, ?_, fun y hy => (h3 y hy).of_eq (by rw [e5]) (by rw [show entA.l = "ent.len" from rfl, e10])
    (by rw [show entA.h = "ent.h" from rfl, e6]) (by rw [show entA.v = "ent.v" from rfl, e7])
    (by rw [show entA.e = "ent.e" from rfl, e8]) (by rw [show entA.r = "ent.r" from rfl, e9]),
    by rw [e3]; exact h4, by rw [e2]; exact h5⟩
  show LList r (r.wa "blk.hd" bid) (b.ents.map (·.id))
  rw [e1]
  exact h2.of_eq (fun j _ => by rw [e4]) (le_of_eq hl.symm)

/-- a structure survives a change of its blocks (same number) when its stack slice, its size cell
and its (new) records survive -/
theorem drep_of_frame' {q r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap lv bse : ℕ} {D D' : DStr (Fin G.n) (WLab G s)} (h : DRep q H V bcap lv bse D)
    (hlenD : D'.blocks.length = D.blocks.length)
    (hstk : ∀ x, bse ≤ x → x < bse + D.blocks.length → r.wa "dsl.stk" x = q.wa "dsl.stk" x)
    (hsz : r.wa "dsl.sz" lv = q.wa "dsl.sz" lv) (hl : ∀ a, r.wlen a = q.wlen a)
    (hrec : ∀ i (hi : i < D'.blocks.length), BlkRep r H V (stkId q bse D'.blocks.length i) D'.blocks[i]) :
    DRep r H V bcap lv bse D' := by
  have hs : ∀ i, i < D'.blocks.length → stkId r bse D'.blocks.length i = stkId q bse D'.blocks.length i := by
    intro i hi; unfold stkId; exact hstk _ (by omega) (by omega)
  refine ⟨by rw [hsz, hlenD]; exact h.sz, by rw [hl]; exact h.szb, by rw [hl, hlenD]; exact h.stkb,
    fun i hi => by rw [hs i hi]; exact hrec i hi, fun i j hi hj hij => ?_, fun i hi => ?_⟩
  · rw [hs i hi, hs j hj, hlenD] at hij; exact h.inj i j (by omega) (by omega) hij
  · rw [hs i hi, hlenD]; exact h.bidb i (by omega)

theorem recsOf_cons (st : State ℝ≥0) (bse : ℕ) (b : Block (Fin G.n) (WLab G s))
    (rest : List (Block (Fin G.n) (WLab G s))) :
    recsOf st bse (b :: rest) = (stkId st bse (rest.length + 1) 0, b) ::
      ((List.range rest.length).map (fun i => stkId st bse (rest.length + 1) (i + 1))).zip rest := by
  unfold recsOf
  simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.zip_cons_cons, List.map_map]
  rfl

theorem recsFrom_of_wa {st r : State ℝ≥0} (Ds : ℕ → DStr (Fin G.n) (WLab G s))
    (hb : r.wa "dsl.base" = st.wa "dsl.base") (hs : r.wa "dsl.stk" = st.wa "dsl.stk") (n l : ℕ) :
    recsFrom r Ds l n = recsFrom st Ds l n := by
  have hid : stkId r = stkId st := by funext b k i; unfold stkId; rw [hs]
  have hbs : base r = base st := by funext l; unfold base; rw [hb]
  have hro : recsOf (G := G) (s := s) r = recsOf st := by funext bse P; unfold recsOf; rw [hid]
  induction n generalizing l with
  | zero => rfl
  | succ n ih => simp only [recsFrom]; rw [ih, hbs, hro]

theorem recsFrom_split (st : State ℝ≥0) (Ds : ℕ → DStr (Fin G.n) (WLab G s)) (lo k : ℕ) (hk : 1 ≤ k) :
    recsFrom st Ds lo (k + 1) = recsOf st (base st lo) (Ds lo).blocks ++
      (recsOf st (base st (lo + 1)) (Ds (lo + 1)).blocks ++ recsFrom st Ds (lo + 2) (k - 1)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show lo + 2 = lo + 1 + 1 by omega, Nat.add_sub_cancel]
  simp only [recsFrom]

/-- **Re-key of the parent's front block** (level `lo+1`) with the label held by `X` (the new
separator `toW q`); everything else of the D layer is unchanged. -/
theorem rekeyDL (st0 : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (ecap bcap : ℕ) (L : Live (Fin G.n) (WLab G s)) (fresh : ℕ)
    (Ds : ℕ → DStr (Fin G.n) (WLab G s)) (lo k : ℕ) (hk : 1 ≤ k)
    (hDL : DLRep st0 H V ecap bcap L fresh Ds lo k)
    (f : Block (Fin G.n) (WLab G s)) (rest : List (Block (Fin G.n) (WLab G s)))
    (hP : (Ds (lo + 1)).blocks = f :: rest)
    (X : LReg) (x : MLabel G) (q : List (Fin G.m)) (hX : Holds st0 X x) (hxq : Rep (s := s) H V x q)
    (hXr : "rk.id" ∉ X.ws) (hpb : st0.w "rk.pb" = base st0 (lo + 1))
    (hpk : st0.w "rk.pk" = (Ds (lo + 1)).blocks.length)
    (hcap : base st0 (lo + 1) + (Ds (lo + 1)).blocks.length + 1 < st0.cap) :
    Runs realOps (rekeyS X) st0 (fun r => DLRep r H V ecap bcap L fresh (Function.update Ds (lo + 1)
      { Ds (lo + 1) with blocks := ⟨(((toW q : WalkOrd G s) : WLab G s) : WithBot (WLab G s)), f.ents⟩ :: rest })
      lo k ∧ Unchanged st0 r rkW ["blk.len"] ["rk.id"] [] ∧ r.cost = st0.cost + 7) := by
  have hPd : DRep st0 H V bcap (lo + 1) (base st0 (lo + 1)) (Ds (lo + 1)) := hDL.drep 1 (by omega)
  have hkP : (Ds (lo + 1)).blocks.length = rest.length + 1 := by rw [hP]; rfl
  obtain ⟨fid, hfid⟩ : ∃ fid, fid = stkId st0 (base st0 (lo + 1)) (rest.length + 1) 0 := ⟨_, rfl⟩
  have hfidv : st0.wa "dsl.stk" (base st0 (lo + 1) + (Ds (lo + 1)).blocks.length - 1) = fid := by
    rw [hfid, hkP]; unfold stkId; congr 1
  have hfidb : fid < bcap := by
    have := hPd.bidb 0 (by omega); rw [hkP] at this; rw [hfid]; exact this
  have hstkl : base st0 (lo + 1) + (Ds (lo + 1)).blocks.length - 1 < st0.wlen "dsl.stk" := by
    have := hPd.stkb; omega
  refine (Runs.keep_len (rekey_facts st0 X x (base st0 (lo + 1)) (Ds (lo + 1)).blocks.length fid bcap
    hX hXr hpb hpk (by omega) hfidv hfidb hDL.barr hstkl hcap) (rekeyS_noalloc X)).mono ?_
  rintro r ⟨⟨hR, hc⟩, hwl, hvl⟩
  set b1 : Block (Fin G.n) (WLab G s) :=
    ⟨(((toW q : WalkOrd G s) : WLab G s) : WithBot (WLab G s)), f.ents⟩ with hb1
  set D1 : DStr (Fin G.n) (WLab G s) := { Ds (lo + 1) with blocks := b1 :: rest } with hD1
  set Ds1 := Function.update Ds (lo + 1) D1 with hDs1
  have hwa : ∀ a, a ∉ rkW → r.wa a = st0.wa a := fun a ha => (hR.unch.warr a ha).1
  have hstk : r.wa "dsl.stk" = st0.wa "dsl.stk" := hwa _ (by simp [rkW])
  have hbs : r.wa "dsl.base" = st0.wa "dsl.base" := hwa _ (by simp [rkW])
  have hszw : r.wa "dsl.sz" = st0.wa "dsl.sz" := hwa _ (by simp [rkW])
  have hbase : ∀ l, base r l = base st0 l := fun l => by unfold base; rw [hbs]
  have hsid : ∀ b k i, stkId r b k i = stkId st0 b k i := fun b k i => by unfold stkId; rw [hstk]
  have hbf : r.w "blk.fresh" = st0.w "blk.fresh" := hR.unch.wreg _ (by simp)
  have hlenD : ∀ l, (Ds1 l).blocks.length = (Ds l).blocks.length := by
    intro l
    by_cases hl : l = lo + 1
    · subst hl; rw [hDs1, Function.update_self, hkP]; rfl
    · rw [hDs1, Function.update_of_ne hl]
  obtain ⟨A, T, C, e0, e1⟩ : ∃ A T C : List (ℕ × Block (Fin G.n) (WLab G s)),
      recsFrom st0 Ds lo (k + 1) = A ++ (((fid, f) :: T) ++ C) ∧
      recsFrom r Ds1 lo (k + 1) = A ++ (((fid, b1) :: T) ++ C) := by
    refine ⟨recsOf st0 (base st0 lo) (Ds lo).blocks,
      ((List.range rest.length).map (fun i => stkId st0 (base st0 (lo + 1)) (rest.length + 1) (i + 1))).zip rest,
      recsFrom st0 Ds (lo + 2) (k - 1), ?_, ?_⟩
    · rw [recsFrom_split st0 Ds lo k hk, hP, recsOf_cons, ← hfid]
    · have h1 : Ds1 lo = Ds lo := by rw [hDs1, Function.update_of_ne (show lo ≠ lo + 1 by omega)]
      have h2 : Ds1 (lo + 1) = D1 := by rw [hDs1, Function.update_self]
      have h3 : recsFrom st0 Ds1 (lo + 2) (k - 1) = recsFrom st0 Ds (lo + 2) (k - 1) :=
        recsFrom_congr st0 st0 Ds Ds1 (k - 1) (lo + 2) (fun l hl1 hl2 =>
          ⟨by rw [hDs1, Function.update_of_ne (show l ≠ lo + 1 by omega)], rfl, fun _ _ _ => rfl⟩)
      rw [recsFrom_of_wa Ds1 hbs hstk, recsFrom_split st0 Ds1 lo k hk, h1, h2, h3,
        show D1.blocks = b1 :: rest from rfl, recsOf_cons, ← hfid]
  have hR1 : RecsOK r H V (recsFrom r Ds1 lo (k + 1)) := by
    have h0 := hDL.recs
    rw [e0] at h0
    obtain ⟨n1, n2, n3⟩ := h0
    have n1' : (A.map Prod.fst ++ fid :: (T.map Prod.fst ++ C.map Prod.fst)).Nodup := by
      simpa only [List.map_append, List.map_cons, List.cons_append] using n1
    have hold : ∀ p, p ∈ A ∨ p ∈ T ∨ p ∈ C → BlkRep r H V p.1 p.2 := by
      intro p hp
      have hne : p.1 ≠ fid := ne_of_nodup_mid n1' (by
        simp only [List.mem_append, List.mem_map]
        rcases hp with hp | hp | hp
        · exact Or.inl ⟨p, hp, rfl⟩
        · exact Or.inr (Or.inl ⟨p, hp, rfl⟩)
        · exact Or.inr (Or.inr ⟨p, hp, rfl⟩))
      have hb0 : BlkRep st0 H V p.1 p.2 := n2 p (by
        simp only [List.mem_append, List.mem_cons]
        rcases hp with hp | hp | hp
        · exact Or.inl hp
        · exact Or.inr (Or.inl (Or.inr hp))
        · exact Or.inr (Or.inr hp))
      exact blkRep_rekey hR (hwl _) hb0 (sepRep_of_fields hb0.1 (hR.bot _ hne) (hR.ahold _ hne))
    rw [e1]
    refine ⟨by simpa only [List.map_append, List.map_cons, List.cons_append] using n1', fun p hp => ?_, ?_⟩
    · simp only [List.mem_append, List.mem_cons] at hp
      rcases hp with hp | (hp | hp) | hp
      · exact hold p (Or.inl hp)
      · subst hp
        have hb0 : BlkRep st0 H V fid f := n2 (fid, f) (by simp)
        show BlkRep r H V fid ⟨(((toW q : WalkOrd G s) : WLab G s) : WithBot (WLab G s)), f.ents⟩
        refine blkRep_rekey hR (hwl _) hb0 ⟨?_, Or.inr ⟨x, q, hR.anew, hxq, rfl⟩⟩
        rw [hR.bot0]; simp
      · exact hold p (Or.inr (Or.inl hp))
      · exact hold p (Or.inr (Or.inr hp))
    · simpa only [List.map_append, List.map_cons, entIds_append, entIds_cons, hb1] using n3
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hR1, ?_, ?_⟩, hR.unch, hc⟩
  · exact liveRep_of_arrays hDL.live (fun a ha => hwa a (by
      simp only [poolArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with h | h | h | h | h | h <;> subst h <;> simp [rkW]))
      (hR.unch.varr _ (by simp)).1 (hwl _)
  · exact poolRep_of hDL.pool (hR.unch.wreg _ (by simp)) hwl hvl
  · exact blkArrs_of hDL.barr hwl hvl
  · rw [hwl]; exact hDL.basel
  · rw [hbase]; exact hDL.base0
  · intro j hj; rw [hbase, hbase, hlenD]; exact hDL.chain j hj
  · intro j hj
    rw [hbase]
    refine drep_of_frame' (hDL.drep j hj) (hlenD _) (fun y _ _ => by rw [hstk]) (by rw [hszw]) hwl
      (fun i hi => ?_)
    have hm := mem_recsFrom r Ds1 (k + 1) lo (lo + j) i (by omega) (by omega) hi
    have := hR1.2.1 _ hm
    rw [hsid, hbase] at this
    exact this
  · intro p hp
    rw [hbf]
    have hb0 := hDL.bfresh
    rw [e0] at hb0
    rw [e1] at hp
    simp only [List.mem_append, List.mem_cons] at hp
    rcases hp with hp | (hp | hp) | hp
    · exact hb0 p (by simp [hp])
    · subst hp; exact hb0 (fid, f) (by simp)
    · exact hb0 p (by simp [hp])
    · exact hb0 p (by simp [hp])
  · rw [hbf]; exact hDL.bfcap

end Frontier.CHD.DGlob
