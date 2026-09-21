import Frontier.CHD.DRep
import Frontier.RAMWP

/-!
# Frontier.CHD.FGroup — B-L3 F-MERGE core: in-place grouping of the child's blocks (agent-06; Layer B, NON-GATE)

Layer-A target: `DB.merge 1 D D'` (agent-04) with `D.blocks = f :: rest`.  The caller has decided whether the
front block `f` is kept (re-keyed to `D'.Bd`) or dropped (`md.df = 0 / 1`) and presents the parent's tail
`T = (if keep then ⟨D'.Bd, f.ents⟩ :: rest else rest)` as a stack segment.  `fGroup` then
1. walks the child's stack slice top-down (= list order) forming `groupAux (M/3) none D'.blocks` in place
   (each group reuses its first block's record; lists are concatenated in `O(1)` through `blk.tl`/`ent.nxt`),
   writing the group ids compactly downward from the top of the child slice;
2. shifts the group ids down onto the parent's stack slice;
3. sets `dsl.sz[lv]`.

Main theorem `runs_fGroup`: inputs `md.lv = lv`, `md.b = bse` (parent base), `md.g = g`, `md.df = df`,
`dsl.sz[lv] = k = |T| + df`, the child `D'` as `DRep … (lv+1) (bse+k) D'` (A1: child base = parent base + parent
size), the tail `T` as `SlRep … bse T`, block ids of `T` disjoint from the child's, entries of `T` outside
`eids D'.blocks`, `(eids D'.blocks).Nodup`.  Output: `DRep r … lv bse ⟨M, Bd, groupAux g none D'.blocks ++ T⟩`
for every `M, Bd`, a precise frame (arrays outside `fgArrs`, `dsl.sz` off `lv`, the stack below `bse + |T|`, block
records outside the child's ids, `ent.nxt` outside the child's entries, registers outside `fgRegs`) and
cost `≤ 24 |D'.blocks| + 18`.  `Layer-A` bridge: with `g = D.M / 3` and `T` the `if ltSep …` tail this is exactly
the block list of `(DB.merge D D').1`.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.DB

variable {κ α : Type*}

/-- the entries of an optional open group -/
def curEnts : Option (Block κ α) → List (Entry κ α)
  | none => []
  | some c => c.ents

/-- **Entries are preserved in order by grouping.** -/
theorem allEnts_groupAux (g : ℕ) :
    ∀ (cur : Option (Block κ α)) (bs : List (Block κ α)),
      allEnts (groupAux g cur bs) = curEnts cur ++ allEnts bs
  | none, [] => by simp [groupAux, allEnts, curEnts]
  | some c, [] => by simp [groupAux, allEnts, curEnts]
  | none, b :: bs => by
      simp only [groupAux]
      split_ifs
      · have := allEnts_groupAux g none bs
        simp only [allEnts, List.map_cons, List.flatten_cons, curEnts, List.nil_append] at this ⊢
        rw [this]
      · rw [allEnts_groupAux g (some b) bs]
        simp [allEnts, curEnts]
  | some c, b :: bs => by
      simp only [groupAux]
      split_ifs
      · have := allEnts_groupAux g none bs
        simp only [allEnts, List.map_cons, List.flatten_cons, curEnts, List.nil_append] at this ⊢
        rw [this]
        simp
      · rw [allEnts_groupAux g (some ⟨c.sep, c.ents ++ b.ents⟩) bs]
        simp [allEnts, curEnts]

theorem groupAux_none_cons (g : ℕ) (b : Block κ α) (bs : List (Block κ α)) :
    groupAux g none (b :: bs) = if g ≤ b.ents.length then b :: groupAux g none bs else groupAux g (some b) bs := by
  simp [groupAux]

theorem groupAux_some_cons (g : ℕ) (c b : Block κ α) (bs : List (Block κ α)) :
    groupAux g (some c) (b :: bs) =
      if g ≤ (c.ents ++ b.ents).length then ⟨c.sep, c.ents ++ b.ents⟩ :: groupAux g none bs
      else groupAux g (some ⟨c.sep, c.ents ++ b.ents⟩) bs := by
  simp [groupAux]

end Frontier.CHD.DB

namespace Frontier.CHD.FGroup

open Frontier Frontier.RAM Frontier.CHD Frontier.CHD.DB Frontier.CHD.DIns WExpr Stmt

/-! ## The program -/

/-- `c.ents ++= x.ents` for the block records `md.c`, `md.x` -/
def concatS : Stmt :=
  seq (ite (lt (lit 0) (load "blk.hd" (var "md.x")))
        (seq (ite (eq (load "blk.hd" (var "md.c")) (lit 0))
                (wstore "blk.hd" (var "md.c") (load "blk.hd" (var "md.x")))
                (wstore "ent.nxt" (sub (load "blk.tl" (var "md.c")) (lit 1)) (load "blk.hd" (var "md.x"))))
             (wstore "blk.tl" (var "md.c") (load "blk.tl" (var "md.x"))))
        skip)
    (wstore "blk.cnt" (var "md.c") (add (load "blk.cnt" (var "md.c")) (load "blk.cnt" (var "md.x"))))

/-- `stk[top - w] := reg; w := w + 1` -/
def emitS (reg : String) : Stmt :=
  seq (wstore "dsl.stk" (sub (var "md.top") (var "md.w")) (var reg)) (wset "md.w" (add (var "md.w") (lit 1)))

/-- one child block: open a group, emit it alone, or absorb it into the open group -/
def groupBody : Stmt :=
  seq (wset "md.x" (load "dsl.stk" (sub (var "md.top") (var "md.r"))))
    (seq (ite (eq (var "md.hc") (lit 0))
            (ite (lt (load "blk.cnt" (var "md.x")) (var "md.g"))
              (seq (wset "md.c" (var "md.x")) (wset "md.hc" (lit 1)))
              (emitS "md.x"))
            (seq concatS
              (ite (lt (load "blk.cnt" (var "md.c")) (var "md.g")) skip
                (seq (emitS "md.c") (wset "md.hc" (lit 0))))))
      (wset "md.r" (add (var "md.r") (lit 1))))

def groupLoop : Stmt := .while (lt (var "md.r") (var "md.kc")) groupBody

/-- `stk[b + k - df + j] := stk[top + 1 - w + j]; j := j + 1` -/
def shiftBody : Stmt :=
  seq (wstore "dsl.stk" (add (sub (add (var "md.b") (var "md.k")) (var "md.df")) (var "md.j"))
        (load "dsl.stk" (add (sub (add (var "md.top") (lit 1)) (var "md.w")) (var "md.j"))))
    (wset "md.j" (add (var "md.j") (lit 1)))

def shiftLoop : Stmt := .while (lt (var "md.j") (var "md.w")) shiftBody

/-- **F-GROUP** (inputs `md.lv`, `md.b`, `md.g = M/3`, `md.df`) -/
def fgMain : Stmt :=
  seq groupLoop
  (seq (ite (eq (var "md.hc") (lit 0)) skip (seq (emitS "md.c") (wset "md.hc" (lit 0))))
  (seq (wset "md.j" (lit 0))
  (seq shiftLoop
    (wstore "dsl.sz" (var "md.lv") (add (sub (var "md.k") (var "md.df")) (var "md.w"))))))

def fGroup : Stmt :=
  seq (wset "md.k" (load "dsl.sz" (var "md.lv")))
  (seq (wset "md.kc" (load "dsl.sz" (add (var "md.lv") (lit 1))))
  (seq (wset "md.top" (sub (add (add (var "md.b") (var "md.k")) (var "md.kc")) (lit 1)))
  (seq (wset "md.r" (lit 0))
  (seq (wset "md.w" (lit 0))
  (seq (wset "md.hc" (lit 0)) fgMain)))))

/-- registers written by `fGroup` -/
def fgRegs : List String :=
  ["md.k", "md.kc", "md.top", "md.r", "md.w", "md.hc", "md.x", "md.c", "md.j"]

/-- registers written by the grouping loop -/
def loopRegs : List String := ["md.r", "md.w", "md.hc", "md.x", "md.c"]

/-- arrays written by `fGroup` -/
def fgArrs : List String := ["dsl.stk", "dsl.sz", "blk.hd", "blk.tl", "blk.cnt", "ent.nxt"]

/-! ## Linked lists: linking a nonempty list to another one -/

theorem LList.link {st r : State ℝ≥0} {h₁ h₂ : ℕ} {l₁ l₂ : List ℕ} (hl₁ : LList st h₁ l₁) (hne : l₁ ≠ [])
    (hl₂ : LList st h₂ l₂) (hnd : (l₁ ++ l₂).Nodup)
    (hnx : ∀ j, j ≠ l₁.getLast hne → r.wa "ent.nxt" j = st.wa "ent.nxt" j)
    (hlast : r.wa "ent.nxt" (l₁.getLast hne) = h₂) (hlen : st.wlen "ent.nxt" ≤ r.wlen "ent.nxt") :
    LList r h₁ (l₁ ++ l₂) := by
  induction hl₁ with
  | nil => exact absurd rfl hne
  | cons i l hi hl ih =>
    by_cases hl0 : l = []
    · subst hl0
      have hli : ([i] : List ℕ).getLast hne = i := rfl
      rw [hli] at hlast hnx
      simp only [List.singleton_append]
      refine LList.cons i l₂ (lt_of_lt_of_le hi hlen) ?_
      rw [hlast]
      refine hl₂.of_eq (fun j hj => hnx j ?_) hlen
      intro e; subst e
      simp only [List.singleton_append, List.nodup_cons] at hnd
      exact hnd.1 hj
    · have hlast' : (i :: l).getLast hne = l.getLast hl0 := List.getLast_cons hl0
      rw [hlast'] at hlast hnx
      have hi' : i ≠ l.getLast hl0 := by
        intro e
        have hmem : l.getLast hl0 ∈ l := List.getLast_mem hl0
        rw [← e] at hmem
        simp only [List.cons_append, List.nodup_cons, List.mem_append] at hnd
        exact hnd.1 (Or.inl hmem)
      simp only [List.cons_append]
      refine LList.cons i (l ++ l₂) (lt_of_lt_of_le hi hlen) ?_
      rw [hnx i hi']
      exact ih hl0 (by simp only [List.cons_append, List.nodup_cons] at hnd; exact hnd.2) hnx hlast


/-! ## The concatenation step -/

section Concat

variable {G : Graph} {s : Fin G.n}

theorem LList.nil_iff_zero {st : State ℝ≥0} {h : ℕ} {l : List ℕ} (hl : LList st h l) : l = [] ↔ h = 0 := by
  cases hl with
  | nil => simp
  | cons i l _ _ => simp

theorem LList.head_of_ne {st : State ℝ≥0} {h : ℕ} {l : List ℕ} (hl : LList st h l) (hne : l ≠ []) :
    h = l.head hne + 1 := by
  cases hl with
  | nil => exact absurd rfl hne
  | cons i l _ _ => rfl

theorem tlWord_eq_getLast {l : List ℕ} (hne : l ≠ []) : tlWord l = l.getLast hne + 1 := by
  unfold tlWord
  rw [List.getLast?_eq_getLast hne]

theorem tlWord_append_right {l₁ l₂ : List ℕ} (hne : l₂ ≠ []) : tlWord (l₁ ++ l₂) = tlWord l₂ := by
  rw [tlWord_eq_getLast (by simp [hne]), tlWord_eq_getLast hne, List.getLast_append_of_ne_nil _ hne]

/-- What `concatS` leaves: the record `c` holds the concatenation, nothing else of the D layer moved
except `ent.nxt` at `c`'s last entry and the fields of `c`. -/
structure ConcatPost (st r : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ) (c : ℕ)
    (bc bx : Block (Fin G.n) (WLab G s)) : Prop where
  rep : BlkRep r H V c ⟨bc.sep, bc.ents ++ bx.ents⟩
  arr : ∀ a, a ∉ ["blk.hd", "blk.tl", "blk.cnt", "ent.nxt"] → r.wa a = st.wa a
  wlen : r.wlen = st.wlen
  va : r.va = st.va
  vlen : r.vlen = st.vlen
  w : r.w = st.w
  v : r.v = st.v
  cap : r.cap = st.cap
  procs : r.procs = st.procs
  recs : ∀ b, b ≠ c → r.wa "blk.hd" b = st.wa "blk.hd" b ∧ r.wa "blk.tl" b = st.wa "blk.tl" b ∧
    r.wa "blk.cnt" b = st.wa "blk.cnt" b
  nxt : ∀ j, j ∉ bc.ents.map (·.id) → r.wa "ent.nxt" j = st.wa "ent.nxt" j
  cost : r.cost ≤ st.cost + 8

end Concat

section ConcatProof

variable {G : Graph} {s : Fin G.n}

theorem LList.lt_len' {st : State ℝ≥0} : ∀ {h : ℕ} {l : List ℕ}, LList st h l → ∀ i ∈ l, i < st.wlen "ent.nxt"
  | _, _, .nil, i, hi => absurd hi List.not_mem_nil
  | _, _, .cons j l hj hl, i, hi => by
      rcases List.mem_cons.mp hi with rfl | hi
      · exact hj
      · exact LList.lt_len' hl i hi

/-- The concatenation post-state from pointwise equations. -/
theorem concatPost_of {st R : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {c : ℕ}
    {bc bx : Block (Fin G.n) (WLab G s)} (HD TL : ℕ) (hsc : SepRep st H V c bc.sep)
    (hen : ∀ y ∈ bc.ents ++ bx.ents, EntRep st H V y.id y.key y.val)
    (hhd : ∀ i, R.wa "blk.hd" i = if i = c then HD else st.wa "blk.hd" i)
    (htl : ∀ i, R.wa "blk.tl" i = if i = c then TL else st.wa "blk.tl" i)
    (hcn : ∀ i, R.wa "blk.cnt" i = if i = c then (bc.ents ++ bx.ents).length else st.wa "blk.cnt" i)
    (hnx : ∀ j, j ∉ bc.ents.map (·.id) → R.wa "ent.nxt" j = st.wa "ent.nxt" j)
    (harr : ∀ a, a ∉ ["blk.hd", "blk.tl", "blk.cnt", "ent.nxt"] → R.wa a = st.wa a)
    (hwl : R.wlen = st.wlen) (hva : R.va = st.va) (hvl : R.vlen = st.vlen) (hw : R.w = st.w)
    (hv : R.v = st.v) (hcp : R.cap = st.cap) (hpr : R.procs = st.procs) (hcost : R.cost ≤ st.cost + 8)
    (hLL : LList R HD ((bc.ents ++ bx.ents).map (·.id))) (hTL : TL = tlWord ((bc.ents ++ bx.ents).map (·.id))) :
    ConcatPost st R H V c bc bx := by
  have hsep : ∀ a ∈ ["blk.bot", "blk.h", "blk.v", "blk.e", "blk.r", "ent.key", "ent.h", "ent.v", "ent.e", "ent.r"],
      R.wa a = st.wa a := by
    intro a ha; apply harr; simp at ha ⊢; rcases ha with h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide
  refine ⟨⟨hsc.of_eq (by rw [hsep _ (by simp)]) (by rw [hva]) (by rw [hsep _ (by simp [blkA])])
      (by rw [hsep _ (by simp [blkA])]) (by rw [hsep _ (by simp [blkA])]) (by rw [hsep _ (by simp [blkA])]),
      by rw [hhd, if_pos rfl]; exact hLL, fun y hy => ?_, by rw [hcn, if_pos rfl], by rw [htl, if_pos rfl]; exact hTL⟩,
    harr, hwl, hva, hvl, hw, hv, hcp, hpr, fun b hb => ⟨by rw [hhd, if_neg hb], by rw [htl, if_neg hb],
      by rw [hcn, if_neg hb]⟩, hnx, hcost⟩
  exact (hen y hy).of_eq (by rw [hsep _ (by simp)]) (by rw [hva]) (by rw [hsep _ (by simp [entA])])
    (by rw [hsep _ (by simp [entA])]) (by rw [hsep _ (by simp [entA])]) (by rw [hsep _ (by simp [entA])])

theorem runs_concatS {st : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {c x : ℕ}
    {bc bx : Block (Fin G.n) (WLab G s)} (hc : st.w "md.c" = c) (hx : st.w "md.x" = x)
    (hbc : BlkRep st H V c bc) (hbx : BlkRep st H V x bx)
    (hnd : ((bc.ents ++ bx.ents).map (·.id)).Nodup)
    (hcl : c < st.wlen "blk.hd" ∧ c < st.wlen "blk.tl" ∧ c < st.wlen "blk.cnt")
    (hxl : x < st.wlen "blk.hd" ∧ x < st.wlen "blk.tl" ∧ x < st.wlen "blk.cnt")
    (hcap : bc.ents.length + bx.ents.length + 1 < st.cap) :
    Runs realOps concatS st (fun r => ConcatPost st r H V c bc bx) := by
  obtain ⟨hsc, hlc, hec, hnc, htc⟩ := hbc
  obtain ⟨hsx, hlx, hex, hnx, htx⟩ := hbx
  have h1 : 1 < st.cap := by omega
  have h0 : 0 < st.cap := by omega
  have hcnt : st.wa "blk.cnt" c + st.wa "blk.cnt" x < st.cap := by rw [hnc, hnx]; omega
  have hen : ∀ y ∈ bc.ents ++ bx.ents, EntRep st H V y.id y.key y.val := by
    intro y hy; rcases List.mem_append.mp hy with h | h
    · exact hec y h
    · exact hex y h
  have hsum : st.wa "blk.cnt" c + st.wa "blk.cnt" x = (bc.ents ++ bx.ents).length := by simp [hnc, hnx]
  have hs1 : ¬ ("blk.cnt" = "blk.tl") := by decide
  have hs2 : ¬ ("blk.cnt" = "blk.hd") := by decide
  have hs3 : ¬ ("blk.tl" = "blk.hd") := by decide
  have hs4 : ¬ ("blk.cnt" = "ent.nxt") := by decide
  have hs5 : ¬ ("blk.tl" = "ent.nxt") := by decide
  apply wp_sound
  by_cases hxe : bx.ents = []
  · -- nothing to link: only the count changes
    have hhx : st.wa "blk.hd" x = 0 := (LList.nil_iff_zero hlx).mp (by simp [hxe])
    simp only [concatS, wp, evalW_lt', evalW_lit', evalW_load', evalW_add', evalW_var, hc, hx, hxl.1, hxl.2.2,
      hcl.2.2, fit_of_lt h0, fit_of_lt hcnt, Option.bind_some, hhx, lt_irrefl, if_false,
      State.charge_w, State.charge_wa, State.charge_wlen, State.charge_cap, ite_true, ne_eq, not_true_eq_false,
      false_implies, true_and, forall_const]
    refine concatPost_of (st.wa "blk.hd" c) (st.wa "blk.tl" c) hsc hen (fun i => ?_) (fun i => ?_) (fun i => ?_)
      (fun j _ => by simp) (fun a ha => ?_) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) ?_ (by simp [htc, hxe])
    · by_cases hi : i = c <;> simp [hi]
    · by_cases hi : i = c <;> simp [hi]
    · by_cases hi : i = c
      · subst hi; simp [hsum]
      · simp [hi]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
      funext i; simp [ha.2.2.1]
    · simp only [hxe, List.append_nil]
      exact hlc.of_eq (fun j _ => by simp) (by simp)
  · have hxne : bx.ents.map (·.id) ≠ [] := by simpa using hxe
    have hhx : st.wa "blk.hd" x = (bx.ents.map (·.id)).head hxne + 1 := LList.head_of_ne hlx hxne
    have hhx0 : 0 < st.wa "blk.hd" x := by omega
    by_cases hce : bc.ents = []
    · -- the left list is empty: the right one becomes the concatenation
      have hhc : st.wa "blk.hd" c = 0 := (LList.nil_iff_zero hlc).mp (by simp [hce])
      simp only [concatS, wp, evalW_lt', evalW_lit', evalW_load', evalW_add', evalW_eq', evalW_var, hc, hx, hxl.1,
        hxl.2.1, hxl.2.2, hcl.1, hcl.2.1, hcl.2.2, fit_of_lt h0, fit_of_lt h1, Option.bind_some, hhx0, if_true, hhc,
        State.charge_w, State.charge_wa, State.charge_wlen, State.charge_cap, State.storeW_wa, State.storeW_wlen,
        State.storeW_w, State.storeW_cap, ne_eq, one_ne_zero, not_false_eq_true, forall_const, true_and,
        and_true, false_implies, hs1, hs2, hs3, false_and, ite_false, fit_of_lt hcnt]
      refine concatPost_of (st.wa "blk.hd" x) (st.wa "blk.tl" x) hsc hen (fun i => ?_) (fun i => ?_) (fun i => ?_)
        (fun j _ => by simp) (fun a ha => ?_) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        (by simp) ?_ (by simp [htx, hce])
      · by_cases hi : i = c <;> simp [hi]
      · by_cases hi : i = c <;> simp [hi]
      · by_cases hi : i = c
        · subst hi; simp [hsum]
        · simp [hi]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
        funext i; simp [ha.1, ha.2.1, ha.2.2.1]
      · simp only [hce, List.nil_append]
        exact hlx.of_eq (fun j _ => by simp) (by simp)
    · -- both nonempty: link the last entry of `c` to the head of `x`
      have hcne : bc.ents.map (·.id) ≠ [] := by simpa using hce
      set last := (bc.ents.map (·.id)).getLast hcne with hlast
      have htcl : st.wa "blk.tl" c - 1 = last := by rw [htc, tlWord_eq_getLast hcne]; omega
      have hlastlt : last < st.wlen "ent.nxt" := LList.lt_len' hlc last (List.getLast_mem hcne)
      have hhc : st.wa "blk.hd" c ≠ 0 := by
        rw [LList.head_of_ne hlc hcne]; omega
      simp only [concatS, wp, evalW_lt', evalW_lit', evalW_load', evalW_add', evalW_eq', evalW_sub', evalW_var, hc,
        hx, hxl.1, hxl.2.1, hxl.2.2, hcl.1, hcl.2.1, hcl.2.2, fit_of_lt h0, fit_of_lt h1, Option.bind_some, hhx0,
        if_true, hhc, htcl, hlastlt, State.charge_w, State.charge_wa, State.charge_wlen, State.charge_cap,
        State.storeW_wa, State.storeW_wlen, State.storeW_w, State.storeW_cap, ne_eq, one_ne_zero, not_false_eq_true,
        forall_const, true_and, and_true, false_implies, not_true_eq_false, hs1, hs4, hs5, false_and, ite_false,
        fit_of_lt hcnt]
      refine concatPost_of (st.wa "blk.hd" c) (st.wa "blk.tl" x) hsc hen (fun i => ?_) (fun i => ?_) (fun i => ?_)
        (fun j hj => ?_) (fun a ha => ?_) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        (by simp) ?_ (by rw [htx, List.map_append, tlWord_append_right hxne])
      · by_cases hi : i = c <;> simp [hi]
      · by_cases hi : i = c <;> simp [hi]
      · by_cases hi : i = c
        · subst hi; simp [hsum]
        · simp [hi]
      · have hjl : j ≠ last := fun e => hj (e ▸ List.getLast_mem hcne)
        simp [hjl]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
        funext i; simp [ha.2.1, ha.2.2.1, ha.2.2.2]
      · rw [List.map_append]
        refine LList.link hlc hcne hlx (by rw [← List.map_append]; exact hnd)
          (fun j hj => by rw [← hlast] at hj; simp [hj]) (by rw [← hlast]; simp) (by simp)

end ConcatProof


/-! ## Transport of block records -/

section Transport

variable {G : Graph} {s : Fin G.n}

/-- A block record survives any change that keeps every D-layer array it reads at its own fields. -/
theorem BlkRep.of_fields {st r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bid : ℕ} {b : Block (Fin G.n) (WLab G s)} (h : BlkRep st H V bid b)
    (hsep : ∀ a ∈ ["blk.bot", "blk.h", "blk.v", "blk.e", "blk.r"], r.wa a bid = st.wa a bid)
    (hsepv : r.va "blk.len" bid = st.va "blk.len" bid)
    (hrec : ∀ a ∈ ["blk.hd", "blk.tl", "blk.cnt"], r.wa a bid = st.wa a bid)
    (hent : ∀ x ∈ b.ents, (∀ a ∈ ["ent.key", "ent.h", "ent.v", "ent.e", "ent.r", "ent.nxt"],
      r.wa a x.id = st.wa a x.id) ∧ r.va "ent.len" x.id = st.va "ent.len" x.id)
    (hlen : st.wlen "ent.nxt" ≤ r.wlen "ent.nxt") : BlkRep r H V bid b := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1.of_eq (hsep _ (by simp)) hsepv (hsep _ (by simp [blkA])) (hsep _ (by simp [blkA]))
      (hsep _ (by simp [blkA])) (hsep _ (by simp [blkA])), ?_, fun x hx => ?_, ?_, ?_⟩
  · rw [hrec _ (by simp)]
    refine h2.of_eq (fun j hj => ?_) hlen
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hj
    exact (hent x hx).1 _ (by simp)
  · have := hent x hx
    exact (h3 x hx).of_eq (this.1 _ (by simp)) this.2 (this.1 _ (by simp [entA])) (this.1 _ (by simp [entA]))
      (this.1 _ (by simp [entA])) (this.1 _ (by simp [entA]))
  · rw [hrec _ (by simp)]; exact h4
  · rw [hrec _ (by simp)]; exact h5

end Transport


/-! ## The grouping loop -/

section GroupLoop

variable {G : Graph} {s : Fin G.n}

/-- entry ids of a block list -/
def eids (bs : List (Block (Fin G.n) (WLab G s))) : List ℕ := (allEnts bs).map (·.id)

/-- the id of the open group, as a list -/
def curIds (cur : Option (Block (Fin G.n) (WLab G s) × ℕ)) : List ℕ := cur.toList.map Prod.snd

/-- `1` if a group is open -/
def curOne (cur : Option (Block (Fin G.n) (WLab G s) × ℕ)) : ℕ := cur.toList.length

/-- Invariant of the grouping loop after `r` child blocks (child list block `i` sits at `top - i`). -/
structure GInv (st0 : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ) (bse k kc g : ℕ)
    (cb : List (Block (Fin G.n) (WLab G s))) (cid : ℕ → ℕ) (c0 r : ℕ) (st : State ℝ≥0) : Prop where
  rr : st.w "md.r" = r
  rtop : st.w "md.top" = bse + k + kc - 1
  rkc : st.w "md.kc" = kc
  rg : st.w "md.g" = g
  ex : ∃ (E : List (Block (Fin G.n) (WLab G s))) (gids : List ℕ) (cur : Option (Block (Fin G.n) (WLab G s) × ℕ)),
    groupAux g none cb = E ++ groupAux g (cur.map Prod.fst) (cb.drop r) ∧
    gids.length = E.length ∧ st.w "md.w" = E.length ∧
    (∀ j, j < E.length → ∃ b gid, E[j]? = some b ∧ gids[j]? = some gid ∧
      st.wa "dsl.stk" (bse + k + kc - 1 - j) = gid ∧ BlkRep st H V gid b) ∧
    (cur = none → st.w "md.hc" = 0) ∧
    (∀ c i, cur = some (c, i) → st.w "md.hc" = 1 ∧ st.w "md.c" = i ∧ BlkRep st H V i c) ∧
    E.length + curOne cur ≤ r ∧
    (gids ++ curIds cur ++ ((List.range kc).drop r).map cid).Nodup ∧
    (∀ i ∈ gids ++ curIds cur, ∃ j < kc, cid j = i)
  unread : ∀ i, r ≤ i → i < kc → ∃ b, cb[i]? = some b ∧ st.wa "dsl.stk" (bse + k + kc - 1 - i) = cid i ∧
    BlkRep st H V (cid i) b
  rle : r ≤ kc
  -- frame
  arr : ∀ a, a ∉ ["dsl.stk", "blk.hd", "blk.tl", "blk.cnt", "ent.nxt"] → st.wa a = st0.wa a
  stklow : ∀ p, p < bse + k → st.wa "dsl.stk" p = st0.wa "dsl.stk" p
  recs : ∀ b, (∀ j < kc, cid j ≠ b) → st.wa "blk.hd" b = st0.wa "blk.hd" b ∧
    st.wa "blk.tl" b = st0.wa "blk.tl" b ∧ st.wa "blk.cnt" b = st0.wa "blk.cnt" b
  nxt : ∀ j, j ∉ eids cb → st.wa "ent.nxt" j = st0.wa "ent.nxt" j
  wlen : st.wlen = st0.wlen
  va : st.va = st0.va
  vlen : st.vlen = st0.vlen
  cap : st.cap = st0.cap
  procs : st.procs = st0.procs
  v : st.v = st0.v
  wreg : ∀ y, y ∉ loopRegs → st.w y = st0.w y
  cost : st.cost ≤ c0 + 20 * r

end GroupLoop


/-! ## Helper facts for the loop step -/

section StepHelpers

variable {G : Graph} {s : Fin G.n}

theorem allEnts_append' (bs bs' : List (Block (Fin G.n) (WLab G s))) :
    allEnts (bs ++ bs') = allEnts bs ++ allEnts bs' := by
  simp [allEnts]

theorem ents_decomp {g r : ℕ} {cb E : List (Block (Fin G.n) (WLab G s))} {cur : Option (Block (Fin G.n) (WLab G s))}
    (h : groupAux g none cb = E ++ groupAux g cur (cb.drop r)) :
    allEnts cb = allEnts E ++ curEnts cur ++ allEnts (cb.drop r) := by
  have h1 := congrArg allEnts h
  rw [allEnts_groupAux, allEnts_append', allEnts_groupAux] at h1
  simpa [curEnts, List.append_assoc] using h1

theorem drop_cons_getElem {α : Type*} {l : List α} {r : ℕ} {b : α} (hb : l[r]? = some b) :
    l.drop r = b :: l.drop (r + 1) := by
  have hr : r < l.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hb; exact absurd hb (by simp)
  rw [List.drop_eq_getElem_cons hr]
  congr
  rw [List.getElem?_eq_getElem hr] at hb
  exact Option.some.inj hb

theorem range_drop_cons {kc r : ℕ} (hr : r < kc) (f : ℕ → ℕ) :
    ((List.range kc).drop r).map f = f r :: ((List.range kc).drop (r + 1)).map f := by
  rw [List.drop_eq_getElem_cons (by simpa using hr)]
  simp

end StepHelpers

/-! ## Single-cell store facts and the shift loop -/

section Shift

theorem storeW_wa_ne {s : State ℝ≥0} {arr : String} {p q a : ℕ} (h : p ≠ q) :
    (s.storeW arr q a).wa arr p = s.wa arr p := by simp [h]

theorem storeW_wa_self {s : State ℝ≥0} {arr : String} {q a : ℕ} : (s.storeW arr q a).wa arr q = a := by simp

theorem storeW_wa_other {s : State ℝ≥0} {arr b : String} {q a : ℕ} (h : b ≠ arr) :
    (s.storeW arr q a).wa b = s.wa b := by funext j; simp [h]

/-- **The shift**: `stk[d + j] := stk[src0 + j]` for `j < w`, bottom-up, with `d = b + k - df ≤ src0 = top + 1 - w`
(no source is overwritten before it is read). -/
theorem runs_shiftLoop {st : State ℝ≥0} {bse k df top w : ℕ} (hj0 : st.w "md.j" = 0)
    (hw : st.w "md.w" = w) (hb : st.w "md.b" = bse) (hk : st.w "md.k" = k) (hdf : st.w "md.df" = df)
    (htop : st.w "md.top" = top) (hle : bse + k - df ≤ top + 1 - w) (hwt : w ≤ top + 1)
    (hbk : bse + k ≤ top + 1) (hlen : top < st.wlen "dsl.stk") (hcap : top + 2 < st.cap) :
    Runs realOps shiftLoop st (fun r =>
      (∀ j, j < w → r.wa "dsl.stk" (bse + k - df + j) = st.wa "dsl.stk" (top + 1 - w + j)) ∧
      (∀ p, (p < bse + k - df ∨ top < p) → r.wa "dsl.stk" p = st.wa "dsl.stk" p) ∧
      (∀ a, a ≠ "dsl.stk" → r.wa a = st.wa a) ∧ r.wlen = st.wlen ∧ r.va = st.va ∧ r.vlen = st.vlen ∧
      r.v = st.v ∧ r.cap = st.cap ∧ r.procs = st.procs ∧
      (∀ y, y ≠ "md.j" → r.w y = st.w y) ∧ r.w "md.j" = w ∧ r.cost ≤ st.cost + 4 * w + 1) := by
  have h1 : 1 < st.cap := by omega
  refine runs_while (fun j t =>
      t.w "md.j" = j ∧ (∀ y, y ≠ "md.j" → t.w y = st.w y) ∧
      (∀ j', j' < j → t.wa "dsl.stk" (bse + k - df + j') = st.wa "dsl.stk" (top + 1 - w + j')) ∧
      (∀ p, (p < bse + k - df ∨ top + 1 - w + j ≤ p) → t.wa "dsl.stk" p = st.wa "dsl.stk" p) ∧
      (∀ a, a ≠ "dsl.stk" → t.wa a = st.wa a) ∧ t.wlen = st.wlen ∧ t.va = st.va ∧ t.vlen = st.vlen ∧
      t.v = st.v ∧ t.cap = st.cap ∧ t.procs = st.procs ∧ t.cost ≤ st.cost + 4 * j) w _ ?_ ?_ st
    ⟨hj0, fun _ _ => rfl, fun j' h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, fun _ _ => rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, by simp⟩
  · rintro j hj t ⟨htj, htw, hdone, hkeep, harr, hwl, hva, hvl, hv, hcp, hpr, hc⟩
    have htc : 1 < t.cap := by rw [hcp]; exact h1
    have tw : t.w "md.w" = w := by rw [htw _ (by decide)]; exact hw
    have tb : t.w "md.b" = bse := by rw [htw _ (by decide)]; exact hb
    have tk : t.w "md.k" = k := by rw [htw _ (by decide)]; exact hk
    have tdf : t.w "md.df" = df := by rw [htw _ (by decide)]; exact hdf
    have ttop : t.w "md.top" = top := by rw [htw _ (by decide)]; exact htop
    have tlen : top < t.wlen "dsl.stk" := by rw [hwl]; exact hlen
    refine ⟨1, by rw [evalW_lt_of rfl rfl htc, htj, tw, if_pos hj], one_ne_zero, ?_⟩
    have hsrc : t.wa "dsl.stk" (top + 1 - w + j) = st.wa "dsl.stk" (top + 1 - w + j) :=
      hkeep _ (Or.inr le_rfl)
    have hc1 : bse + k < t.cap := by rw [hcp]; omega
    have hc2 : bse + k - df + j < t.cap := by rw [hcp]; omega
    have hc3 : top + 1 < t.cap := by rw [hcp]; omega
    have hc4 : top + 1 - w + j < t.cap := by rw [hcp]; omega
    have hsl : top + 1 - w + j < t.wlen "dsl.stk" := by omega
    unfold shiftBody
    apply runs_seq
    refine runs_wstore (j := bse + k - df + j) (a := t.wa "dsl.stk" (top + 1 - w + j))
      (by simp [tb, tk, tdf, htj, fit_of_lt hc1, fit_of_lt hc2])
      (by simp [ttop, tw, htj, fit_of_lt hc3, fit_of_lt hc4, fit_of_lt htc, hsl])
      (by simp; omega) ?_
    refine runs_wset (evalW_add_of (x := j) (y := 1) (by simp [htj]) (evalW_lit_of (by simpa using htc)) (by simp; omega)) ?_
    refine ⟨by simp [htj], fun y hy => ?_, fun j' hj' => ?_, fun p hp => ?_, fun a ha => ?_, by simp [hwl],
      by simp [hva], by simp [hvl], by simp [hv], by simp [hcp], by simp [hpr], by simp; omega⟩
    · simp [hy, htw y hy]
    · simp only [State.charge_wa, State.setW_wa]
      by_cases hjj : j' = j
      · subst hjj; rw [storeW_wa_self]; exact hsrc
      · rw [storeW_wa_ne (show bse + k - df + j' ≠ bse + k - df + j by omega)]; exact hdone j' (by omega)
    · simp only [State.charge_wa, State.setW_wa]
      rw [storeW_wa_ne (show p ≠ bse + k - df + j by omega)]
      exact hkeep p (by omega)
    · simp only [State.charge_wa, State.setW_wa]
      rw [storeW_wa_other ha]; exact harr a ha
  · rintro t ⟨htj, htw, hdone, hkeep, harr, hwl, hva, hvl, hv, hcp, hpr, hc⟩
    have htc : 1 < t.cap := by rw [hcp]; exact h1
    refine ⟨by rw [evalW_lt_of rfl rfl htc, htj, htw _ (by decide), hw]; simp, hdone, fun p hp => hkeep p (by omega),
      fun a ha => by simp [harr a ha], by simp [hwl], by simp [hva], by simp [hvl], by simp [hv], by simp [hcp],
      by simp [hpr], fun y hy => by simp [htw y hy], by simp [htj], by simp; omega⟩

end Shift

/-! ## The loop step -/

section Step

variable {G : Graph} {s : Fin G.n}

/-- A block record only reads word/value arrays (and their lengths). -/
theorem BlkRep.of_same {st r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {bid : ℕ}
    {b : Block (Fin G.n) (WLab G s)} (h : BlkRep st H V bid b) (hwa : ∀ a, a ≠ "dsl.stk" → r.wa a = st.wa a)
    (hva : r.va = st.va) (hl : r.wlen = st.wlen) : BlkRep r H V bid b :=
  BlkRep.of_fields h (fun a ha => by rw [hwa a (by simp at ha; rcases ha with h | h | h | h | h <;> subst h <;> decide)])
    (by rw [hva]) (fun a ha => by rw [hwa a (by simp at ha; rcases ha with h | h | h <;> subst h <;> decide)])
    (fun x _ => ⟨fun a ha => by rw [hwa a (by simp at ha; rcases ha with h | h | h | h | h | h <;> subst h <;> decide)],
      by rw [hva]⟩) (by rw [hl])

end Step

section Step2

variable {G : Graph} {s : Fin G.n}

/-- Static facts for the grouping loop. -/
structure GStat (st0 : State ℝ≥0) (bcap bse k kc : ℕ) (cb : List (Block (Fin G.n) (WLab G s)))
    (cid : ℕ → ℕ) : Prop where
  kc_eq : cb.length = kc
  arrs : BlkArrs st0 bcap
  cid_lt : ∀ i < kc, cid i < bcap
  ents_nd : (eids cb).Nodup
  stk_len : bse + k + kc ≤ st0.wlen "dsl.stk"
  kc_pos : 0 < kc
  cap : bse + k + kc + (eids cb).length + 8 < st0.cap

theorem gstep_test {st0 st : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bse k kc g c0 r : ℕ} {cb : List (Block (Fin G.n) (WLab G s))} {cid : ℕ → ℕ}
    (hG : GInv st0 H V bse k kc g cb cid c0 r st) (h1 : 1 < st.cap) (hr : r < kc) :
    evalW st (lt (var "md.r") (var "md.kc")) = some 1 := by
  rw [evalW_lt_of rfl rfl h1, hG.rr, hG.rkc, if_pos hr]

end Step2

/-! ## Re-establishing the invariant -/

section Next

variable {G : Graph} {s : Fin G.n}

/-- `GInv (r+1)` for a state `u` that differs from a `GInv r` state `st` only by allowed writes. -/
theorem ginv_next {st0 st u : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bse k kc g c0 r : ℕ} {cb : List (Block (Fin G.n) (WLab G s))} {cid : ℕ → ℕ}
    (hG : GInv st0 H V bse k kc g cb cid c0 r st) (hr : r < kc)
    (farr : ∀ a, a ∉ ["dsl.stk", "blk.hd", "blk.tl", "blk.cnt", "ent.nxt"] → u.wa a = st.wa a)
    (fstk : ∀ p, p < bse + k → u.wa "dsl.stk" p = st.wa "dsl.stk" p)
    (frecs : ∀ b, (∀ j < kc, cid j ≠ b) → u.wa "blk.hd" b = st.wa "blk.hd" b ∧
      u.wa "blk.tl" b = st.wa "blk.tl" b ∧ u.wa "blk.cnt" b = st.wa "blk.cnt" b)
    (fnxt : ∀ j, j ∉ eids cb → u.wa "ent.nxt" j = st.wa "ent.nxt" j)
    (fwlen : u.wlen = st.wlen) (fva : u.va = st.va) (fvlen : u.vlen = st.vlen) (fcap : u.cap = st.cap)
    (fprocs : u.procs = st.procs) (fv : u.v = st.v) (fwreg : ∀ y, y ∉ loopRegs → u.w y = st.w y)
    (frr : u.w "md.r" = r + 1) (ftop : u.w "md.top" = bse + k + kc - 1) (fkc : u.w "md.kc" = kc)
    (fg : u.w "md.g" = g)
    (fex : ∃ (E : List (Block (Fin G.n) (WLab G s))) (gids : List ℕ)
      (cur : Option (Block (Fin G.n) (WLab G s) × ℕ)),
      groupAux g none cb = E ++ groupAux g (cur.map Prod.fst) (cb.drop (r + 1)) ∧
      gids.length = E.length ∧ u.w "md.w" = E.length ∧
      (∀ j, j < E.length → ∃ b gid, E[j]? = some b ∧ gids[j]? = some gid ∧
        u.wa "dsl.stk" (bse + k + kc - 1 - j) = gid ∧ BlkRep u H V gid b) ∧
      (cur = none → u.w "md.hc" = 0) ∧
      (∀ c i, cur = some (c, i) → u.w "md.hc" = 1 ∧ u.w "md.c" = i ∧ BlkRep u H V i c) ∧
      E.length + curOne cur ≤ r + 1 ∧
      (gids ++ curIds cur ++ ((List.range kc).drop (r + 1)).map cid).Nodup ∧
      (∀ i ∈ gids ++ curIds cur, ∃ j < kc, cid j = i))
    (funread : ∀ i, r + 1 ≤ i → i < kc → ∃ b, cb[i]? = some b ∧
      u.wa "dsl.stk" (bse + k + kc - 1 - i) = cid i ∧ BlkRep u H V (cid i) b)
    (fcost : u.cost ≤ c0 + 20 * (r + 1)) :
    GInv st0 H V bse k kc g cb cid c0 (r + 1) u where
  rr := frr
  rtop := ftop
  rkc := fkc
  rg := fg
  ex := fex
  unread := funread
  rle := hr
  arr a ha := (farr a ha).trans (hG.arr a ha)
  stklow p hp := (fstk p hp).trans (hG.stklow p hp)
  recs b hb := ⟨(frecs b hb).1.trans (hG.recs b hb).1, (frecs b hb).2.1.trans (hG.recs b hb).2.1,
    (frecs b hb).2.2.trans (hG.recs b hb).2.2⟩
  nxt j hj := (fnxt j hj).trans (hG.nxt j hj)
  wlen := fwlen.trans hG.wlen
  va := fva.trans hG.va
  vlen := fvlen.trans hG.vlen
  cap := fcap.trans hG.cap
  procs := fprocs.trans hG.procs
  v := fv.trans hG.v
  wreg y hy := (fwreg y hy).trans (hG.wreg y hy)
  cost := fcost

end Next

/-! ## Bookkeeping for the loop step -/

section StepAux

variable {G : Graph} {s : Fin G.n}

theorem absorb_ids {A B C D : List ℕ} (h : (A ++ B ++ C ++ D).Nodup) :
    (B ++ C).Nodup ∧ (∀ x ∈ A, x ∉ B) ∧ (∀ x ∈ D, x ∉ B) := by
  rw [List.nodup_append, List.nodup_append, List.nodup_append] at h
  obtain ⟨⟨⟨_, hB, hAB⟩, hC, hABC⟩, _, hABCD⟩ := h
  exact ⟨List.nodup_append.mpr ⟨hB, hC, fun a ha b hb => hABC a (List.mem_append_right _ ha) b hb⟩,
    fun x hx hxB => hAB x hx x hxB rfl,
    fun x hx hxB => hABCD x (List.mem_append_left _ (List.mem_append_right _ hxB)) x hx rfl⟩

theorem nd_ne {A B C : List ℕ} (h : (A ++ B ++ C).Nodup) {x y : ℕ} (hx : x ∈ A) (hy : y ∈ B) : x ≠ y := by
  rw [List.nodup_append, List.nodup_append] at h
  exact h.1.2.2 x hx y hy

theorem nd_ne' {A B C : List ℕ} (h : (A ++ B ++ C).Nodup) {x y : ℕ} (hx : x ∈ B) (hy : y ∈ C) : x ≠ y := by
  rw [List.nodup_append] at h
  exact h.2.2 x (List.mem_append_right _ hx) y hy

theorem mem_range_drop {kc r i : ℕ} (h1 : r ≤ i) (h2 : i < kc) : i ∈ (List.range kc).drop r :=
  List.mem_of_getElem? (i := i - r) (by rw [List.getElem?_drop, Nat.add_sub_cancel' h1, List.getElem?_range h2])

theorem mem_drop_of_getElem? {α : Type*} {l : List α} {r i : ℕ} {b : α} (h1 : r ≤ i) (h : l[i]? = some b) :
    b ∈ l.drop r :=
  List.mem_of_getElem? (i := i - r) (by rw [List.getElem?_drop, Nat.add_sub_cancel' h1]; exact h)

/-- A block record disjoint from the concatenated record survives `concatS`. -/
theorem BlkRep.of_concat {st R : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {c gid : ℕ} {bc bx b' : Block (Fin G.n) (WLab G s)} (hP : ConcatPost st R H V c bc bx)
    (h : BlkRep st H V gid b') (hne : gid ≠ c) (hdis : ∀ y ∈ b'.ents, y.id ∉ bc.ents.map (·.id)) :
    BlkRep R H V gid b' := by
  have ha : ∀ a, a ∉ ["blk.hd", "blk.tl", "blk.cnt", "ent.nxt"] → ∀ j, R.wa a j = st.wa a j :=
    fun a ha j => congrFun (hP.arr a ha) j
  refine BlkRep.of_fields h (fun a hm => ha a ?_ gid) (by rw [hP.va]) (fun a hm => ?_)
    (fun x hx => ⟨fun a hm => ?_, by rw [hP.va]⟩) (by rw [hP.wlen])
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h <;> subst h <;> decide
  · obtain ⟨h1, h2, h3⟩ := hP.recs gid hne
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h <;> subst h <;> assumption
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h <;> subst h
    · exact ha _ (by decide) _
    · exact ha _ (by decide) _
    · exact ha _ (by decide) _
    · exact ha _ (by decide) _
    · exact ha _ (by decide) _
    · exact hP.nxt _ (hdis x hx)

/-- `stk[top - w] := reg; w := w + 1` -/
theorem runs_emitS {reg : String} {st : State ℝ≥0} {Q : State ℝ≥0 → Prop} {top w : ℕ}
    (htop : st.w "md.top" = top) (hw : st.w "md.w" = w) (hlen : top - w < st.wlen "dsl.stk")
    (hcap : w + 1 < st.cap)
    (hQ : Q ((((st.storeW "dsl.stk" (top - w) (st.w reg)).charge 1).setW "md.w" (w + 1)).charge 1)) :
    Runs realOps (emitS reg) st Q := by
  unfold emitS
  apply runs_seq
  refine runs_wstore (j := top - w) (a := st.w reg) (by simp [htop, hw]) rfl hlen ?_
  refine runs_wset (evalW_add_of (x := w) (y := 1) (by simp [hw]) (evalW_lit_of (by simp; omega)) (by simp; omega)) ?_
  exact hQ

theorem evalW_cntlt {st : State ℝ≥0} {reg : String} {x g n : ℕ} (hx : st.w reg = x)
    (hxl : x < st.wlen "blk.cnt") (hn : st.wa "blk.cnt" x = n) (hg : st.w "md.g" = g) (h1 : 1 < st.cap) :
    evalW st (lt (load "blk.cnt" (var reg)) (var "md.g")) = some (if n < g then 1 else 0) := by
  rw [evalW_lt_of (y := g) (evalW_load_of (i := var reg) (j := x) (by simp [hx]) hxl) (by simp [hg]) h1, hn]

theorem evalW_hc {st : State ℝ≥0} {h : ℕ} (hh : st.w "md.hc" = h) (h1 : 1 < st.cap) :
    evalW st (eq (var "md.hc") (lit 0)) = some (if h = 0 then 1 else 0) := by
  rw [evalW_eq_of (x := h) (y := 0) (by simp [hh]) (evalW_lit_of (by omega)) h1]

end StepAux

/-! ## The loop step -/

section GStep

variable {G : Graph} {s : Fin G.n}

theorem gstep {st0 st : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap bse k kc g c0 r : ℕ} {cb : List (Block (Fin G.n) (WLab G s))} {cid : ℕ → ℕ}
    (hS : GStat st0 bcap bse k kc cb cid) (hG : GInv st0 H V bse k kc g cb cid c0 r st) (hr : r < kc) :
    Runs realOps groupBody (st.charge 1) (GInv st0 H V bse k kc g cb cid c0 (r + 1)) := by
  obtain ⟨E, gids, cur, heq, hgl, hw, hemit, hcur0, hcur1, hcnt, hnd, hsub⟩ := hG.ex
  obtain ⟨b, hb, hstk, hrep⟩ := hG.unread r le_rfl hr
  have hcapE : st.cap = st0.cap := hG.cap
  have hwl : st.wlen = st0.wlen := hG.wlen
  have hcap0 := hS.cap
  have h1 : 1 < st.cap := by rw [hcapE]; omega
  have hstkl := hS.stk_len
  have htr : bse + k + kc - 1 - r < st.wlen "dsl.stk" := by rw [hwl]; omega
  have hdrop := drop_cons_getElem hb
  have hrk := range_drop_cons hr cid
  have hdec := ents_decomp heq
  have harrs : BlkArrs st bcap := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hS.arrs
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hwl, hG.vlen, blkA] <;> assumption
  have hcidlt : cid r < bcap := hS.cid_lt r hr
  have hcntb : st.wa "blk.cnt" (cid r) = b.ents.length := hrep.2.2.2.1
  -- the value of `md.x`
  unfold groupBody
  apply runs_seq
  refine runs_wset (a := cid r) (by
      rw [evalW_load_of (j := bse + k + kc - 1 - r) (by simp [evalW_sub', hG.rtop, hG.rr]) (by simpa using htr)]
      simp [hstk]) ?_
  apply runs_seq
  rcases cur with _ | ⟨c, i⟩
  · -- no open group
    have hhc : st.w "md.hc" = 0 := hcur0 rfl
    refine runs_ite_true (evalW_eq_of rfl (evalW_lit_of (by simp; omega)) (by simpa using h1)) (by simp [hhc]) ?_
    by_cases hlt : b.ents.length < g
    · -- open a group with this block
      refine runs_ite_true (evalW_lt_of (evalW_load_of rfl (by simp; exact lt_of_lt_of_le hcidlt harrs.2.2.1))
        rfl (by simpa using h1)) (by simp [hcntb, hG.rg, hlt]) ?_
      apply runs_seq
      refine runs_wset rfl ?_
      refine runs_wset (evalW_lit_of (by simpa using h1)) ?_
      refine runs_wset (evalW_add_of rfl (evalW_lit_of (by simpa using h1)) (by simp [hG.rr]; omega)) ?_
      refine ginv_next hG hr (fun a _ => by simp) (fun p _ => by simp) (fun b _ => by simp) (fun j _ => by simp)
        (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        (fun y hy => by simp [loopRegs] at hy; simp [hy]) (by simp [hG.rr]) (by simp [hG.rtop]) (by simp [hG.rkc])
        (by simp [hG.rg]) ⟨E, gids, some (b, cid r), ?_, hgl, by simp [hw], ?_, by simp, ?_, ?_, ?_, ?_⟩ ?_ ?_
      · rw [heq, hdrop]; dsimp only [Option.map]
        rw [groupAux_none_cons, if_neg (show ¬ (g ≤ b.ents.length) by omega)]
      · intro j hj
        obtain ⟨b', gid, h1', h2', h3', h4'⟩ := hemit j hj
        exact ⟨b', gid, h1', h2', by simp [h3'], BlkRep.of_same h4' (fun a _ => by simp) (by simp) (by simp)⟩
      · rintro c' i' he
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨by simp, by simp, BlkRep.of_same hrep (fun a _ => by simp) (by simp) (by simp)⟩
      · simp only [curOne, Option.toList_some, List.length_singleton]
        simp only [curOne, Option.toList_none, List.length_nil] at hcnt; omega
      · simp only [curIds, Option.toList_some, List.map_singleton] at hnd ⊢
        simp only [curIds, Option.toList_none, List.map_nil, List.append_nil] at hnd
        rw [hrk] at hnd
        simpa [List.append_assoc] using hnd
      · intro i' hi'
        simp only [curIds, Option.toList_some, List.map_singleton, List.mem_append, List.mem_singleton] at hi'
        rcases hi' with hi' | rfl
        · exact hsub i' (by simpa [curIds] using hi')
        · exact ⟨r, hr, rfl⟩
      · intro i' hi1 hi2
        obtain ⟨b', h1', h2', h3'⟩ := hG.unread i' (by omega) hi2
        exact ⟨b', h1', by simp [h2'], BlkRep.of_same h3' (fun a _ => by simp) (by simp) (by simp)⟩
      · simp; have := hG.cost; omega
    · -- emit this block alone
      have hge : g ≤ b.ents.length := by omega
      have hEr : E.length ≤ r := by simpa [curOne] using hcnt
      refine runs_ite_false (by
          rw [evalW_cntlt (reg := "md.x") (x := cid r) (n := b.ents.length) (g := g) (by simp)
            (by simpa using lt_of_lt_of_le hcidlt harrs.2.2.1) (by simpa using hcntb) (by simp [hG.rg])
            (by simpa using h1)]
          simp [hlt]) ?_
      refine runs_emitS (top := bse + k + kc - 1) (w := E.length) (by simp [hG.rtop]) (by simp [hw])
        (by simp [hwl]; omega) (by simp; omega) ?_
      refine runs_wset (evalW_add_of (x := r) (y := 1) (by simp [hG.rr]) (evalW_lit_of (by simpa using h1))
        (by simp; omega)) ?_
      refine ginv_next hG hr (fun a ha => ?_) (fun p hp => ?_) (fun b _ => by simp) (fun j _ => by simp)
        (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        (fun y hy => by simp [loopRegs] at hy; simp [hy]) (by simp) (by simp [hG.rtop]) (by simp [hG.rkc])
        (by simp [hG.rg]) ⟨E ++ [b], gids ++ [cid r], none, ?_, by simp [hgl], by simp, ?_, fun _ => by simp [hhc],
          by simp, by simp [curOne]; omega, ?_, ?_⟩ ?_ ?_
      · funext j
        have hne : a ≠ "dsl.stk" := fun e => ha (by simp [e])
        simp [hne]
      · have hne : p ≠ bse + k + kc - 1 - E.length := by omega
        simp only [State.charge_wa, State.setW_wa]
        rw [storeW_wa_ne hne]
        simp
      · rw [heq, hdrop]; dsimp only [Option.map]
        rw [groupAux_none_cons, if_pos hge]; simp
      · intro j hj
        simp only [List.length_append, List.length_singleton] at hj
        rcases Nat.lt_or_ge j E.length with hjE | hjE
        · obtain ⟨b', gid, h1', h2', h3', h4'⟩ := hemit j hjE
          have hne : bse + k + kc - 1 - j ≠ bse + k + kc - 1 - E.length := by omega
          refine ⟨b', gid, by rw [List.getElem?_append_left hjE]; exact h1',
            by rw [List.getElem?_append_left (by omega)]; exact h2', ?_,
            BlkRep.of_same h4' (fun a ha => by funext j; simp [ha]) (by simp) (by simp)⟩
          simp only [State.charge_wa, State.setW_wa]
          rw [storeW_wa_ne hne]
          simpa using h3'
        · obtain rfl : j = E.length := by omega
          refine ⟨b, cid r, List.getElem?_concat_length, by rw [← hgl]; exact List.getElem?_concat_length,
            by simp, BlkRep.of_same hrep (fun a ha => by funext j; simp [ha]) (by simp) (by simp)⟩
      · simp only [curIds, Option.toList_none, List.map_nil, List.append_nil] at hnd ⊢
        rw [hrk] at hnd
        simpa using hnd
      · intro i' hi'
        simp only [curIds, Option.toList_none, List.map_nil, List.append_nil, List.mem_append,
          List.mem_singleton] at hi'
        rcases hi' with hi' | rfl
        · exact hsub i' (by simpa [curIds] using hi')
        · exact ⟨r, hr, rfl⟩
      · intro i' hi1 hi2
        obtain ⟨b', h1', h2', h3'⟩ := hG.unread i' (by omega) hi2
        have hne : bse + k + kc - 1 - i' ≠ bse + k + kc - 1 - E.length := by omega
        refine ⟨b', h1', ?_, BlkRep.of_same h3' (fun a ha => by funext j; simp [ha]) (by simp) (by simp)⟩
        simp only [State.charge_wa, State.setW_wa]
        rw [storeW_wa_ne hne]
        simpa using h2'
      · simp; have := hG.cost; omega
  · -- absorb into the open group
    obtain ⟨hhc1, hmc, hrepc⟩ := hcur1 c i rfl
    have hEr : E.length + 1 ≤ r := by simpa [curOne] using hcnt
    obtain ⟨ji, hji, hcidi⟩ := hsub i (by simp [curIds])
    have hilt : i < bcap := by rw [← hcidi]; exact hS.cid_lt ji hji
    have hids : eids cb = (allEnts E).map (·.id) ++ c.ents.map (·.id) ++ b.ents.map (·.id) ++
        (allEnts (cb.drop (r + 1))).map (·.id) := by
      unfold eids; rw [hdec, hdrop]; simp [curEnts, allEnts]
    have hnd4 := hS.ents_nd
    rw [hids] at hnd4
    obtain ⟨hndcb, hdisE, hdisR⟩ := absorb_ids hnd4
    have hcsub : ∀ j, j ∉ eids cb → j ∉ c.ents.map (·.id) := fun j hj hm =>
      hj (by rw [hids]; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hm)))
    have hdisE' : ∀ b' ∈ E, ∀ y ∈ b'.ents, y.id ∉ c.ents.map (·.id) := fun b' hb' y hy =>
      hdisE _ (List.mem_map_of_mem (mem_allEnts.mpr ⟨b', hb', hy⟩))
    have hdisR' : ∀ b' ∈ cb.drop (r + 1), ∀ y ∈ b'.ents, y.id ∉ c.ents.map (·.id) := fun b' hb' y hy =>
      hdisR _ (List.mem_map_of_mem (mem_allEnts.mpr ⟨b', hb', hy⟩))
    have hlenE : c.ents.length + b.ents.length ≤ (eids cb).length := by
      rw [hids]; simp only [List.length_append, List.length_map]; omega
    refine runs_ite_false (by rw [evalW_hc (h := 1) (by simp [hhc1]) (by simpa using h1)]; simp) ?_
    apply runs_seq
    refine (runs_concatS (c := i) (x := cid r) (bc := c) (bx := b) (by simp [hmc]) (by simp)
      (BlkRep.of_same hrepc (fun a _ => by simp) (by simp) (by simp))
      (BlkRep.of_same hrep (fun a _ => by simp) (by simp) (by simp))
      (by rw [List.map_append]; exact hndcb)
      (by simp only [State.charge_wlen, State.setW_wlen]
          exact ⟨lt_of_lt_of_le hilt harrs.1, lt_of_lt_of_le hilt harrs.2.1, lt_of_lt_of_le hilt harrs.2.2.1⟩)
      (by simp only [State.charge_wlen, State.setW_wlen]
          exact ⟨lt_of_lt_of_le hcidlt harrs.1, lt_of_lt_of_le hcidlt harrs.2.1,
            lt_of_lt_of_le hcidlt harrs.2.2.1⟩)
      (by simp; omega)).mono (fun R hR => ?_)
    have hRw : ∀ y, R.w y = if y = "md.x" then cid r else st.w y := fun y => by rw [hR.w]; simp
    have hRcap : R.cap = st.cap := by rw [hR.cap]; simp
    have hRwl : R.wlen = st.wlen := by rw [hR.wlen]; simp
    have hRva : R.va = st.va := by rw [hR.va]; simp
    have hRvl : R.vlen = st.vlen := by rw [hR.vlen]; simp
    have hRpr : R.procs = st.procs := by rw [hR.procs]; simp
    have hRv : R.v = st.v := by rw [hR.v]; simp
    have hRcost : R.cost ≤ st.cost + 11 := by have := hR.cost; simp at this; omega
    have hRcnt : R.wa "blk.cnt" i = (c.ents ++ b.ents).length := hR.rep.2.2.2.1
    have hR1 : 1 < R.cap := by rw [hRcap]; exact h1
    have hRilt : i < R.wlen "blk.cnt" := by rw [hRwl]; exact lt_of_lt_of_le hilt harrs.2.2.1
    have hRst : ∀ a, a ∉ ["blk.hd", "blk.tl", "blk.cnt", "ent.nxt"] → R.wa a = st.wa a :=
      fun a ha => (hR.arr a ha).trans rfl
    have hRtrans : ∀ gid (b' : Block (Fin G.n) (WLab G s)), BlkRep st H V gid b' → gid ≠ i →
        (∀ y ∈ b'.ents, y.id ∉ c.ents.map (·.id)) → BlkRep R H V gid b' :=
      fun gid b' h hne hdis =>
        BlkRep.of_concat hR (BlkRep.of_same h (fun a _ => by simp) (by simp) (by simp)) hne hdis
    have hRrecs : ∀ b', (∀ j < kc, cid j ≠ b') → R.wa "blk.hd" b' = st.wa "blk.hd" b' ∧
        R.wa "blk.tl" b' = st.wa "blk.tl" b' ∧ R.wa "blk.cnt" b' = st.wa "blk.cnt" b' := fun b' hb' =>
      hR.recs b' (fun e => hb' ji hji (hcidi.trans e.symm))
    have hRnxt : ∀ j, j ∉ eids cb → R.wa "ent.nxt" j = st.wa "ent.nxt" j := fun j hj => hR.nxt j (hcsub j hj)
    have hRc : R.w "md.c" = i := by rw [hRw]; simp [hmc]
    have hRg : R.w "md.g" = g := by rw [hRw]; simp [hG.rg]
    by_cases hlt : (c.ents ++ b.ents).length < g
    · -- keep the group open
      refine runs_ite_true (evalW_cntlt hRc hRilt hRcnt hRg hR1) (by rw [if_pos hlt]; exact one_ne_zero) ?_
      refine runs_skip ?_
      refine runs_wset (evalW_add_of (x := r) (y := 1) (by simp [hRw, hG.rr])
        (evalW_lit_of (by simpa [hRcap] using h1)) (by simp [hRcap]; omega)) ?_
      refine ginv_next hG hr (fun a ha => ?_) (fun p _ => ?_) (fun b' hb' => ?_) (fun j hj => ?_)
        (by simp [hRwl]) (by simp [hRva]) (by simp [hRvl]) (by simp [hRcap]) (by simp [hRpr]) (by simp [hRv])
        (fun y hy => by simp [loopRegs] at hy; simp [hRw, hy]) (by simp) (by simp [hRw, hG.rtop])
        (by simp [hRw, hG.rkc]) (by simp [hRw, hG.rg])
        ⟨E, gids, some (⟨c.sep, c.ents ++ b.ents⟩, i), ?_, hgl, by simp [hRw, hw], ?_, by simp, ?_,
          by simp [curOne]; omega, ?_, ?_⟩ ?_ ?_
      · simp only [State.charge_wa, State.setW_wa]; exact hRst a (fun h => ha (List.mem_cons_of_mem _ h))
      · simp only [State.charge_wa, State.setW_wa]; rw [hRst "dsl.stk" (by decide)]
      · simp only [State.charge_wa, State.setW_wa]; exact hRrecs b' hb'
      · simp only [State.charge_wa, State.setW_wa]; exact hRnxt j hj
      · rw [heq, hdrop]; dsimp only [Option.map]
        rw [groupAux_some_cons, if_neg (show ¬ (g ≤ (c.ents ++ b.ents).length) by omega)]
      · intro j hj
        obtain ⟨b', gid, h1', h2', h3', h4'⟩ := hemit j hj
        have hne : gid ≠ i := nd_ne hnd (List.mem_of_getElem? h2') (by simp [curIds])
        refine ⟨b', gid, h1', h2', ?_,
          BlkRep.of_same (hRtrans gid b' h4' hne (hdisE' b' (List.mem_of_getElem? h1')))
            (fun a _ => by simp) (by simp) (by simp)⟩
        simp only [State.charge_wa, State.setW_wa]; rw [hRst "dsl.stk" (by decide)]; exact h3'
      · rintro c' i' he
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨by simp [hRw, hhc1], by simp [hRc], BlkRep.of_same hR.rep (fun a _ => by simp) (by simp) (by simp)⟩
      · have hnd' : (gids ++ [i] ++ ((List.range kc).drop r).map cid).Nodup := hnd
        rw [hrk] at hnd'
        exact ((List.sublist_cons_self _ _).append_left _).nodup hnd'
      · intro i' hi'
        exact hsub i' (by simpa [curIds] using hi')
      · intro i' hi1 hi2
        obtain ⟨b', h1', h2', h3'⟩ := hG.unread i' (by omega) hi2
        have hne : cid i' ≠ i := fun e => nd_ne' hnd (x := i) (y := cid i') (by simp [curIds])
          (List.mem_map_of_mem (mem_range_drop (by omega) hi2)) e.symm
        refine ⟨b', h1', ?_,
          BlkRep.of_same (hRtrans (cid i') b' h3' hne (hdisR' b' (mem_drop_of_getElem? (by omega) h1')))
            (fun a _ => by simp) (by simp) (by simp)⟩
        simp only [State.charge_wa, State.setW_wa]; rw [hRst "dsl.stk" (by decide)]; exact h2'
      · have := hG.cost; simp; omega
    · -- close the group
      have hge : g ≤ (c.ents ++ b.ents).length := by omega
      refine runs_ite_false (by rw [evalW_cntlt hRc hRilt hRcnt hRg hR1, if_neg hlt]) ?_
      apply runs_seq
      refine runs_emitS (top := bse + k + kc - 1) (w := E.length) (by simp [hRw, hG.rtop]) (by simp [hRw, hw])
        (by simp [hRwl, hwl]; omega) (by simp [hRcap]; omega) ?_
      refine runs_wset (evalW_lit_of (by simp [hRcap]; omega)) ?_
      refine runs_wset (evalW_add_of (x := r) (y := 1) (by simp [hRw, hG.rr])
        (evalW_lit_of (by simpa [hRcap] using h1)) (by simp [hRcap]; omega)) ?_
      refine ginv_next hG hr (fun a ha => ?_) (fun p hp => ?_) (fun b' hb' => ?_) (fun j hj => ?_)
        (by simp [hRwl]) (by simp [hRva]) (by simp [hRvl]) (by simp [hRcap]) (by simp [hRpr]) (by simp [hRv])
        (fun y hy => by simp [loopRegs] at hy; simp [hRw, hy]) (by simp) (by simp [hRw, hG.rtop])
        (by simp [hRw, hG.rkc]) (by simp [hRw, hG.rg])
        ⟨E ++ [⟨c.sep, c.ents ++ b.ents⟩], gids ++ [i], none, ?_, by simp [hgl], by simp, ?_, fun _ => by simp,
          by simp, by simp [curOne]; omega, ?_, ?_⟩ ?_ ?_
      · funext j
        have hne : a ≠ "dsl.stk" := fun e => ha (by simp [e])
        have := congrFun (hRst a (fun h => ha (List.mem_cons_of_mem _ h))) j
        simp [hne, this]
      · have hne : p ≠ bse + k + kc - 1 - E.length := by omega
        simp only [State.charge_wa, State.setW_wa]
        rw [storeW_wa_ne hne]
        simp only [State.charge_wa]
        rw [hRst "dsl.stk" (by decide)]
      · have e := hRrecs b' hb'
        simp [e]
      · have e := hRnxt j hj
        simp [e]
      · rw [heq, hdrop]; dsimp only [Option.map]
        rw [groupAux_some_cons, if_pos hge]; simp
      · intro j hj
        simp only [List.length_append, List.length_singleton] at hj
        rcases Nat.lt_or_ge j E.length with hjE | hjE
        · obtain ⟨b', gid, h1', h2', h3', h4'⟩ := hemit j hjE
          have hne : gid ≠ i := nd_ne hnd (List.mem_of_getElem? h2') (by simp [curIds])
          have hpq : bse + k + kc - 1 - j ≠ bse + k + kc - 1 - E.length := by omega
          refine ⟨b', gid, by rw [List.getElem?_append_left hjE]; exact h1',
            by rw [List.getElem?_append_left (by omega)]; exact h2', ?_,
            BlkRep.of_same (hRtrans gid b' h4' hne (hdisE' b' (List.mem_of_getElem? h1')))
              (fun a ha => by funext j; simp [ha]) (by simp) (by simp)⟩
          simp only [State.charge_wa, State.setW_wa]
          rw [storeW_wa_ne hpq]
          simp only [State.charge_wa]
          rw [hRst "dsl.stk" (by decide)]; exact h3'
        · obtain rfl : j = E.length := by omega
          refine ⟨⟨c.sep, c.ents ++ b.ents⟩, i, List.getElem?_concat_length,
            by rw [← hgl]; exact List.getElem?_concat_length, by simp [hRc],
            BlkRep.of_same hR.rep (fun a ha => by funext j; simp [ha]) (by simp) (by simp)⟩
      · have hnd' : (gids ++ [i] ++ ((List.range kc).drop r).map cid).Nodup := hnd
        rw [hrk] at hnd'
        show (gids ++ [i] ++ [] ++ ((List.range kc).drop (r + 1)).map cid).Nodup
        rw [List.append_nil]
        exact ((List.sublist_cons_self _ _).append_left _).nodup hnd'
      · intro i' hi'
        simp only [curIds, Option.toList_none, List.map_nil, List.append_nil] at hi'
        exact hsub i' (by simpa [curIds] using hi')
      · intro i' hi1 hi2
        obtain ⟨b', h1', h2', h3'⟩ := hG.unread i' (by omega) hi2
        have hne : cid i' ≠ i := fun e => nd_ne' hnd (x := i) (y := cid i') (by simp [curIds])
          (List.mem_map_of_mem (mem_range_drop (by omega) hi2)) e.symm
        have hpq : bse + k + kc - 1 - i' ≠ bse + k + kc - 1 - E.length := by omega
        refine ⟨b', h1', ?_,
          BlkRep.of_same (hRtrans (cid i') b' h3' hne (hdisR' b' (mem_drop_of_getElem? (by omega) h1')))
            (fun a ha => by funext j; simp [ha]) (by simp) (by simp)⟩
        simp only [State.charge_wa, State.setW_wa]
        rw [storeW_wa_ne hpq]
        simp only [State.charge_wa]
        rw [hRst "dsl.stk" (by decide)]; exact h2'
      · have := hG.cost; simp; omega

end GStep


/-! ## The grouping loop and the final emit -/

section Loop

variable {G : Graph} {s : Fin G.n}

theorem getElem_of_getElem? {α : Type*} {l : List α} {j : ℕ} {b : α} (hj : j < l.length) (h : l[j]? = some b) :
    l[j] = b := by
  rw [List.getElem?_eq_getElem hj] at h; exact Option.some.inj h

theorem runs_groupLoop {st0 st : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap bse k kc g c0 : ℕ} {cb : List (Block (Fin G.n) (WLab G s))} {cid : ℕ → ℕ}
    (hS : GStat st0 bcap bse k kc cb cid) (hG : GInv st0 H V bse k kc g cb cid c0 0 st) :
    Runs realOps groupLoop st (fun t => ∃ u, GInv st0 H V bse k kc g cb cid c0 kc u ∧ t = u.charge 1) := by
  unfold groupLoop
  refine runs_while (fun r t => GInv st0 H V bse k kc g cb cid c0 r t) kc _ ?_ ?_ st hG
  · intro r hr t ht
    have h1 : 1 < t.cap := by rw [ht.cap]; have := hS.cap; omega
    exact ⟨1, gstep_test ht h1 hr, one_ne_zero, gstep hS ht hr⟩
  · intro t ht
    have h1 : 1 < t.cap := by rw [ht.cap]; have := hS.cap; omega
    refine ⟨?_, t, ht, rfl⟩
    rw [evalW_lt_of rfl rfl h1, ht.rr, ht.rkc]; simp

/-- After the loop and the final emit: the group ids sit compactly at `top, top - 1, …`. -/
structure GFin (st0 : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ) (bse k kc g : ℕ)
    (cb : List (Block (Fin G.n) (WLab G s))) (cid : ℕ → ℕ) (c0 : ℕ) (st : State ℝ≥0) : Prop where
  ex : ∃ gids : List ℕ, gids.length = (groupAux g none cb).length ∧
    st.w "md.w" = (groupAux g none cb).length ∧
    (∀ j (hj : j < (groupAux g none cb).length), ∃ gid, gids[j]? = some gid ∧
      st.wa "dsl.stk" (bse + k + kc - 1 - j) = gid ∧ BlkRep st H V gid (groupAux g none cb)[j]) ∧
    gids.Nodup ∧ (∀ i ∈ gids, ∃ j < kc, cid j = i)
  glen : (groupAux g none cb).length ≤ kc
  arr : ∀ a, a ∉ ["dsl.stk", "blk.hd", "blk.tl", "blk.cnt", "ent.nxt"] → st.wa a = st0.wa a
  stklow : ∀ p, p < bse + k → st.wa "dsl.stk" p = st0.wa "dsl.stk" p
  recs : ∀ b, (∀ j < kc, cid j ≠ b) → st.wa "blk.hd" b = st0.wa "blk.hd" b ∧
    st.wa "blk.tl" b = st0.wa "blk.tl" b ∧ st.wa "blk.cnt" b = st0.wa "blk.cnt" b
  nxt : ∀ j, j ∉ eids cb → st.wa "ent.nxt" j = st0.wa "ent.nxt" j
  wlen : st.wlen = st0.wlen
  va : st.va = st0.va
  vlen : st.vlen = st0.vlen
  cap : st.cap = st0.cap
  procs : st.procs = st0.procs
  v : st.v = st0.v
  wreg : ∀ y, y ∉ loopRegs → st.w y = st0.w y
  cost : st.cost ≤ c0 + 20 * kc + 6

theorem runs_finalEmit {st0 u : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap bse k kc g c0 : ℕ} {cb : List (Block (Fin G.n) (WLab G s))} {cid : ℕ → ℕ}
    (hS : GStat st0 bcap bse k kc cb cid) (hG : GInv st0 H V bse k kc g cb cid c0 kc u) :
    Runs realOps (ite (eq (var "md.hc") (lit 0)) skip (seq (emitS "md.c") (wset "md.hc" (lit 0)))) (u.charge 1)
      (GFin st0 H V bse k kc g cb cid c0) := by
  obtain ⟨E, gids, cur, heq, hgl, hw, hemit, hcur0, hcur1, hcnt, hnd, hsub⟩ := hG.ex
  have hcapE : u.cap = st0.cap := hG.cap
  have hcap0 := hS.cap
  have h1 : 1 < u.cap := by rw [hcapE]; omega
  have hdrop : cb.drop kc = [] := List.drop_eq_nil_of_le (by rw [hS.kc_eq])
  rw [hdrop] at heq
  have hrk : ((List.range kc).drop kc).map cid = [] := by simp
  rw [hrk, List.append_nil] at hnd
  rcases cur with _ | ⟨c, i⟩
  · -- nothing open
    have hhc : u.w "md.hc" = 0 := hcur0 rfl
    have hE : groupAux g none cb = E := by rw [heq]; simp [groupAux]
    have hEl : E.length ≤ kc := by simp only [curOne, Option.toList_none, List.length_nil] at hcnt; omega
    refine runs_ite_true (evalW_hc (h := 0) (by simp [hhc]) (by simpa using h1)) (by simp) (runs_skip ?_)
    refine ⟨⟨gids, by rw [hE, hgl], by simp [hw, hE], fun j hj => ?_, by simpa [curIds] using hnd,
      fun i hi => hsub i (by simpa [curIds] using hi)⟩, by rw [hE]; exact hEl,
      fun a ha => by simpa using hG.arr a ha, fun p hp => by simpa using hG.stklow p hp,
      fun b hb => by simpa using hG.recs b hb, fun j hj => by simpa using hG.nxt j hj,
      by simpa using hG.wlen, by simpa using hG.va, by simpa using hG.vlen, by simpa using hG.cap,
      by simpa using hG.procs, by simpa using hG.v, fun y hy => by simpa using hG.wreg y hy,
      by simp; have := hG.cost; omega⟩
    have hjE : j < E.length := by rw [← hE]; exact hj
    obtain ⟨b', gid, h1', h2', h3', h4'⟩ := hemit j hjE
    have e : (groupAux g none cb)[j] = b' := getElem_of_getElem? hj (by rw [hE]; exact h1')
    refine ⟨gid, h2', by simpa using h3', ?_⟩
    rw [e]; exact BlkRep.of_same h4' (fun a _ => by simp) (by simp) (by simp)
  · -- close the open group
    obtain ⟨hhc1, hmc, hrepc⟩ := hcur1 c i rfl
    have hE : groupAux g none cb = E ++ [c] := by rw [heq]; simp [groupAux]
    have hEr : E.length + 1 ≤ kc := by
      simp only [curOne, Option.toList_some, List.length_singleton] at hcnt; omega
    have hstkl := hS.stk_len
    refine runs_ite_false (by rw [evalW_hc (h := 1) (by simp [hhc1]) (by simpa using h1)]; simp) ?_
    apply runs_seq
    refine runs_emitS (top := bse + k + kc - 1) (w := E.length) (by simp [hG.rtop]) (by simp [hw])
      (by simp [hG.wlen]; omega) (by simp; omega) ?_
    refine runs_wset (evalW_lit_of (by simp; omega)) ?_
    refine ⟨⟨gids ++ [i], by rw [hE]; simp [hgl], by simp [hE], fun j hj => ?_, by simpa [curIds] using hnd,
      fun i' hi' => hsub i' (by simpa [curIds] using hi')⟩, by rw [hE]; simp; omega,
      fun a ha => ?_, fun p hp => ?_, fun b hb => ?_, fun j hj => ?_, by simpa using hG.wlen, by simpa using hG.va,
      by simpa using hG.vlen, by simpa using hG.cap, by simpa using hG.procs, by simpa using hG.v,
      fun y hy => ?_, by simp; have := hG.cost; omega⟩
    · have hj' : j < E.length + 1 := by rw [hE] at hj; simpa using hj
      rcases Nat.lt_or_ge j E.length with hjE | hjE
      · obtain ⟨b', gid, h1', h2', h3', h4'⟩ := hemit j hjE
        have hpq : bse + k + kc - 1 - j ≠ bse + k + kc - 1 - E.length := by omega
        have e : (groupAux g none cb)[j] = b' :=
          getElem_of_getElem? hj (by rw [hE, List.getElem?_append_left hjE]; exact h1')
        refine ⟨gid, by rw [List.getElem?_append_left (by omega)]; exact h2', ?_, ?_⟩
        · simp only [State.charge_wa, State.setW_wa]; rw [storeW_wa_ne hpq]; simpa using h3'
        · rw [e]; exact BlkRep.of_same h4' (fun a ha => by funext j; simp [ha]) (by simp) (by simp)
      · obtain rfl : j = E.length := by omega
        have e : (groupAux g none cb)[E.length] = c :=
          getElem_of_getElem? hj (by rw [hE]; exact List.getElem?_concat_length)
        refine ⟨i, by rw [← hgl]; exact List.getElem?_concat_length, by simp [hmc], ?_⟩
        rw [e]; exact BlkRep.of_same hrepc (fun a ha => by funext j; simp [ha]) (by simp) (by simp)
    · funext j
      have hne : a ≠ "dsl.stk" := fun e => ha (by simp [e])
      have := congrFun (hG.arr a ha) j
      simp [hne, this]
    · have hpq : p ≠ bse + k + kc - 1 - E.length := by omega
      simp only [State.charge_wa, State.setW_wa]; rw [storeW_wa_ne hpq]; simpa using hG.stklow p hp
    · have := hG.recs b hb
      simp [this]
    · have := hG.nxt j hj
      simp [this]
    · have := hG.wreg y hy
      simp [loopRegs] at hy
      simp [hy, this]

end Loop


/-! ## Slices of the shared stack -/

section Slice

variable {G : Graph} {s : Fin G.n}

/-- A block list on the stack slice `[bse, bse + |bs|)` (front = top): `DRep` without the size cell. -/
structure SlRep (st : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ) (bcap bse : ℕ)
    (bs : List (Block (Fin G.n) (WLab G s))) : Prop where
  stkb : bse + bs.length ≤ st.wlen "dsl.stk"
  blk : ∀ i (hi : i < bs.length), BlkRep st H V (stkId st bse bs.length i) bs[i]
  inj : ∀ i j, i < bs.length → j < bs.length → stkId st bse bs.length i = stkId st bse bs.length j → i = j
  bidb : ∀ i < bs.length, stkId st bse bs.length i < bcap

theorem DRep.of_sl {st : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {bcap lv bse : ℕ}
    {D : DStr (Fin G.n) (WLab G s)} (hsz : st.wa "dsl.sz" lv = D.blocks.length) (hszb : lv < st.wlen "dsl.sz")
    (h : SlRep st H V bcap bse D.blocks) : DRep st H V bcap lv bse D :=
  ⟨hsz, hszb, h.stkb, h.blk, h.inj, h.bidb⟩

theorem DRep.sl {st : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {bcap lv bse : ℕ}
    {D : DStr (Fin G.n) (WLab G s)} (h : DRep st H V bcap lv bse D) : SlRep st H V bcap bse D.blocks :=
  ⟨h.stkb, h.blk, h.inj, h.bidb⟩

theorem SlRep.of_regs {st r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {bcap bse : ℕ}
    {bs : List (Block (Fin G.n) (WLab G s))} (h : SlRep st H V bcap bse bs)
    (hwa : r.wa = st.wa) (hva : r.va = st.va) (hwl : r.wlen = st.wlen) : SlRep r H V bcap bse bs := by
  have hid : ∀ i, stkId r bse bs.length i = stkId st bse bs.length i := fun i => by simp [stkId, hwa]
  refine ⟨by rw [hwl]; exact h.stkb, fun i hi => ?_,
    fun i j hi hj he => h.inj i j hi hj (by rw [← hid i, ← hid j]; exact he),
    fun i hi => by rw [hid]; exact h.bidb i hi⟩
  rw [hid]; exact BlkRep.of_same (h.blk i hi) (fun a _ => by rw [hwa]) hva hwl

theorem DRep.of_regs {st r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {bcap lv bse : ℕ}
    {D : DStr (Fin G.n) (WLab G s)} (h : DRep st H V bcap lv bse D)
    (hwa : r.wa = st.wa) (hva : r.va = st.va) (hwl : r.wlen = st.wlen) : DRep r H V bcap lv bse D :=
  DRep.of_sl (by rw [hwa]; exact h.sz) (by rw [hwl]; exact h.szb) (SlRep.of_regs (DRep.sl h) hwa hva hwl)

/-- A block record reads no `dsl.*` array. -/
theorem BlkRep.of_dsl {st r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {bid : ℕ}
    {b : Block (Fin G.n) (WLab G s)} (h : BlkRep st H V bid b)
    (hwa : ∀ a, a ≠ "dsl.stk" → a ≠ "dsl.sz" → r.wa a = st.wa a)
    (hva : r.va = st.va) (hl : r.wlen = st.wlen) : BlkRep r H V bid b :=
  BlkRep.of_fields h
    (fun a ha => by
      rw [hwa a (by simp at ha; rcases ha with h | h | h | h | h <;> subst h <;> decide)
        (by simp at ha; rcases ha with h | h | h | h | h <;> subst h <;> decide)])
    (by rw [hva])
    (fun a ha => by
      rw [hwa a (by simp at ha; rcases ha with h | h | h <;> subst h <;> decide)
        (by simp at ha; rcases ha with h | h | h <;> subst h <;> decide)])
    (fun x _ => ⟨fun a ha => by
      rw [hwa a (by simp at ha; rcases ha with h | h | h | h | h | h <;> subst h <;> decide)
        (by simp at ha; rcases ha with h | h | h | h | h | h <;> subst h <;> decide)], by rw [hva]⟩)
    (by rw [hl])

/-- **Assembling the merged slice** `Gs ++ T` from the group ids (on top) and the untouched tail. -/
theorem slRep_result {st fin : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap bse kc : ℕ} {Gs T : List (Block (Fin G.n) (WLab G s))} {cid : ℕ → ℕ} {gids : List ℕ}
    (hT : SlRep st H V bcap bse T) (hgl : gids.length = Gs.length) (hnd : gids.Nodup)
    (hsub : ∀ i ∈ gids, ∃ j < kc, cid j = i) (hcidb : ∀ j < kc, cid j < bcap)
    (hgrp : ∀ j (hj : j < Gs.length), ∃ gid, gids[j]? = some gid ∧
      fin.wa "dsl.stk" (bse + T.length + (Gs.length - 1 - j)) = gid ∧ BlkRep fin H V gid Gs[j])
    (htail : ∀ i' < T.length, fin.wa "dsl.stk" (bse + (T.length - 1 - i')) = stkId st bse T.length i')
    (htrep : ∀ i' (hi : i' < T.length), BlkRep fin H V (stkId st bse T.length i') T[i'])
    (hTid : ∀ i' < T.length, ∀ j < kc, stkId st bse T.length i' ≠ cid j)
    (hlen : bse + Gs.length + T.length ≤ fin.wlen "dsl.stk") :
    SlRep fin H V bcap bse (Gs ++ T) := by
  have hL : (Gs ++ T).length = Gs.length + T.length := by simp
  have hgid : ∀ i (h : i < Gs.length), ∃ gid, gids[i]? = some gid ∧ stkId fin bse (Gs ++ T).length i = gid ∧
      BlkRep fin H V gid Gs[i] := by
    intro i h
    obtain ⟨gid, h1, h2, h3⟩ := hgrp i h
    refine ⟨gid, h1, ?_, h3⟩
    unfold stkId
    rw [hL, show bse + (Gs.length + T.length - 1 - i) = bse + T.length + (Gs.length - 1 - i) by omega]
    exact h2
  have htl : ∀ i, Gs.length ≤ i → i < (Gs ++ T).length →
      stkId fin bse (Gs ++ T).length i = stkId st bse T.length (i - Gs.length) := by
    intro i h hi
    rw [hL] at hi
    unfold stkId
    rw [hL, show bse + (Gs.length + T.length - 1 - i) = bse + (T.length - 1 - (i - Gs.length)) by omega]
    exact htail _ (by omega)
  refine ⟨by rw [hL]; omega, fun i hi => ?_, fun i j hi hj he => ?_, fun i hi => ?_⟩
  · by_cases h : i < Gs.length
    · obtain ⟨gid, -, h2, h3⟩ := hgid i h
      rw [h2, List.getElem_append_left h]; exact h3
    · rw [htl i (by omega) hi, List.getElem_append_right (by omega)]
      exact htrep _ (by rw [hL] at hi; omega)
  · by_cases h1 : i < Gs.length <;> by_cases h2 : j < Gs.length
    · obtain ⟨g1, e1, f1, -⟩ := hgid i h1
      obtain ⟨g2, e2, f2, -⟩ := hgid j h2
      rw [f1, f2] at he
      subst he
      have hi' : i < gids.length := by omega
      have hj' : j < gids.length := by omega
      rw [List.getElem?_eq_getElem hi'] at e1
      rw [List.getElem?_eq_getElem hj'] at e2
      exact (List.Nodup.getElem_inj_iff hnd).mp ((Option.some.inj e1).trans (Option.some.inj e2).symm)
    · obtain ⟨g1, e1, f1, -⟩ := hgid i h1
      rw [f1, htl j (by omega) hj] at he
      obtain ⟨j0, hj0, hc⟩ := hsub g1 (List.mem_of_getElem? e1)
      exact absurd (he.symm.trans hc.symm) (hTid _ (by rw [hL] at hj; omega) j0 hj0)
    · obtain ⟨g2, e2, f2, -⟩ := hgid j h2
      rw [f2, htl i (by omega) hi] at he
      obtain ⟨j0, hj0, hc⟩ := hsub g2 (List.mem_of_getElem? e2)
      exact absurd (he.trans hc.symm) (hTid _ (by rw [hL] at hi; omega) j0 hj0)
    · rw [htl i (by omega) hi, htl j (by omega) hj] at he
      have := hT.inj _ _ (by rw [hL] at hi; omega) (by rw [hL] at hj; omega) he
      omega
  · by_cases h : i < Gs.length
    · obtain ⟨g1, e1, f1, -⟩ := hgid i h
      rw [f1]
      obtain ⟨j0, hj0, hc⟩ := hsub g1 (List.mem_of_getElem? e1)
      rw [← hc]; exact hcidb j0 hj0
    · rw [htl i (by omega) hi]; exact hT.bidb _ (by rw [hL] at hi; omega)

end Slice

/-! ## The main part and the top-level specification -/

section Top

variable {G : Graph} {s : Fin G.n}

/-- `fgMain` after the register setup: group, final emit, shift, size update. -/
theorem runs_fgMain {st : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap lv bse g df k : ℕ} {D' : DStr (Fin G.n) (WLab G s)} {T : List (Block (Fin G.n) (WLab G s))}
    (hlv : st.w "md.lv" = lv) (hb : st.w "md.b" = bse) (hg : st.w "md.g" = g) (hdfr : st.w "md.df" = df)
    (hkr : st.w "md.k" = k) (hkcr : st.w "md.kc" = D'.blocks.length)
    (htopr : st.w "md.top" = bse + k + D'.blocks.length - 1)
    (hr0 : st.w "md.r" = 0) (hw0 : st.w "md.w" = 0) (hhc0 : st.w "md.hc" = 0)
    (hszl : lv < st.wlen "dsl.sz") (hTl : T.length + df = k)
    (hC : DRep st H V bcap (lv + 1) (bse + k) D') (hne : D'.blocks ≠ [])
    (hT : SlRep st H V bcap bse T)
    (hTid : ∀ i < T.length, ∀ j < D'.blocks.length,
      stkId st bse T.length i ≠ stkId st (bse + k) D'.blocks.length j)
    (hTent : ∀ b ∈ T, ∀ y ∈ b.ents, y.id ∉ eids D'.blocks)
    (hent : (eids D'.blocks).Nodup) (hBA : BlkArrs st bcap)
    (hcap : bse + k + D'.blocks.length + (eids D'.blocks).length + 8 < st.cap) :
    Runs realOps fgMain st (fun r =>
      (∀ (M : ℕ) (Bd : WLab G s), DRep r H V bcap lv bse ⟨M, Bd, groupAux g none D'.blocks ++ T⟩) ∧
      (∀ a, a ∉ fgArrs → r.wa a = st.wa a) ∧
      (∀ p, p ≠ lv → r.wa "dsl.sz" p = st.wa "dsl.sz" p) ∧
      (∀ p, p < bse + T.length → r.wa "dsl.stk" p = st.wa "dsl.stk" p) ∧
      (∀ b, (∀ j < D'.blocks.length, stkId st (bse + k) D'.blocks.length j ≠ b) →
        r.wa "blk.hd" b = st.wa "blk.hd" b ∧ r.wa "blk.tl" b = st.wa "blk.tl" b ∧
        r.wa "blk.cnt" b = st.wa "blk.cnt" b) ∧
      (∀ j, j ∉ eids D'.blocks → r.wa "ent.nxt" j = st.wa "ent.nxt" j) ∧
      r.wlen = st.wlen ∧ r.va = st.va ∧ r.vlen = st.vlen ∧ r.cap = st.cap ∧ r.procs = st.procs ∧
      r.v = st.v ∧ (∀ y, y ≠ "md.j" → y ∉ loopRegs → r.w y = st.w y) ∧
      r.cost ≤ st.cost + 24 * D'.blocks.length + 12) := by
  obtain ⟨hszC, _, hstkC, hblkC, hinjC, hbidC⟩ := hC
  set cb := D'.blocks with hcb
  set kc := cb.length with hkcd
  set cid : ℕ → ℕ := fun j => stkId st (bse + k) kc j with hcid
  have hkc0 : 0 < kc := List.length_pos_of_ne_nil hne
  have h1 : 1 < st.cap := by omega
  have hS : GStat st bcap bse k kc cb cid := ⟨rfl, hBA, fun i hi => hbidC i hi, hent, hstkC, hkc0, by omega⟩
  have hnd0 : ((List.range kc).map cid).Nodup :=
    List.Nodup.map_on (fun x hx y hy e => hinjC x y (List.mem_range.mp hx) (List.mem_range.mp hy) e)
      List.nodup_range
  have hG0 : GInv st H V bse k kc g cb cid st.cost 0 st := by
    refine ⟨hr0, htopr, hkcr, hg, ⟨[], [], none, by simp, rfl, by simp [hw0], fun j hj => absurd hj (by simp),
      fun _ => hhc0, by simp, by simp [curOne], by simpa [curIds] using hnd0, by simp [curIds]⟩,
      fun i _ hi => ⟨cb[i], List.getElem?_eq_getElem hi, ?_, hblkC i hi⟩, Nat.zero_le _,
      fun _ _ => rfl, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      fun _ _ => rfl, by simp⟩
    simp only [hcid, stkId]
    congr 1; omega
  unfold fgMain
  apply runs_seq
  refine (runs_groupLoop hS hG0).mono (fun t ⟨u, hu, htu⟩ => ?_)
  subst htu
  apply runs_seq
  refine (runs_finalEmit hS hu).mono (fun v hv => ?_)
  obtain ⟨gids, hgl, hwv, hgrp, hndg, hsubg⟩ := hv.ex
  have hGl := hv.glen
  have hvw : ∀ y, y ∉ loopRegs → v.w y = st.w y := hv.wreg
  have vb : v.w "md.b" = bse := by rw [hvw _ (by simp [loopRegs])]; exact hb
  have vk : v.w "md.k" = k := by rw [hvw _ (by simp [loopRegs])]; exact hkr
  have vdf : v.w "md.df" = df := by rw [hvw _ (by simp [loopRegs])]; exact hdfr
  have vtop : v.w "md.top" = bse + k + kc - 1 := by rw [hvw _ (by simp [loopRegs])]; exact htopr
  have vlv : v.w "md.lv" = lv := by rw [hvw _ (by simp [loopRegs])]; exact hlv
  have hvcap : v.cap = st.cap := hv.cap
  have hvwl : v.wlen = st.wlen := hv.wlen
  apply runs_seq
  refine runs_wset (evalW_lit_of (by rw [hvcap]; omega)) ?_
  apply runs_seq
  refine (runs_shiftLoop (st := (v.setW "md.j" 0).charge 1) (bse := bse) (k := k) (df := df)
    (top := bse + k + kc - 1) (w := (groupAux g none cb).length) (by simp) (by simp [hwv]) (by simp [vb])
    (by simp [vk]) (by simp [vdf]) (by simp [vtop]) (by omega) (by omega) (by omega)
    (by simp [hvwl]; omega) (by simp [hvcap]; omega)).mono (fun r hr => ?_)
  obtain ⟨hsh, hkeep, harr, hwl, hva, hvl, hvv, hcp, hpr, hwr, _, hcost⟩ := hr
  have rw_ : ∀ y, y ≠ "md.j" → r.w y = v.w y := fun y hy => by rw [hwr y hy]; simp [hy]
  have rcap : r.cap = st.cap := by rw [hcp]; simp [hvcap]
  have rwl : r.wlen = st.wlen := by rw [hwl]; simp [hvwl]
  refine runs_wstore (j := lv) (a := k - df + (groupAux g none cb).length)
    (by rw [evalW_var, rw_ "md.lv" (by decide), vlv])
    (evalW_add_of (x := k - df) (y := (groupAux g none cb).length)
      (by simp [rw_ "md.k" (by decide), rw_ "md.df" (by decide), vk, vdf])
      (by simp [rw_ "md.w" (by decide), hwv]) (by rw [rcap]; omega))
    (by rw [rwl]; exact hszl) ?_
  -- frame facts of the final state
  have hss : ∀ (x : State ℝ≥0) (q a : ℕ), (x.storeW "dsl.sz" q a).wa "dsl.stk" = x.wa "dsl.stk" :=
    fun x q a => storeW_wa_other (by decide)
  have hfv : ∀ a, a ≠ "dsl.stk" → a ≠ "dsl.sz" →
      ((r.storeW "dsl.sz" lv (k - df + (groupAux g none cb).length)).charge 1).wa a = v.wa a := by
    intro a h1 h2
    simp only [State.charge_wa]; rw [storeW_wa_other h2, harr a h1, State.charge_wa, State.setW_wa]
  have hfA : ∀ a, a ∉ fgArrs →
      ((r.storeW "dsl.sz" lv (k - df + (groupAux g none cb).length)).charge 1).wa a = st.wa a := by
    intro a ha
    have h1 : a ≠ "dsl.stk" := fun e => ha (by simp [e, fgArrs])
    have h2 : a ≠ "dsl.sz" := fun e => ha (by simp [e, fgArrs])
    rw [hfv a h1 h2]
    exact hv.arr a (fun h => ha (by simp [fgArrs] at h ⊢; tauto))
  refine ⟨fun M Bd => DRep.of_sl (by simp; omega) (by simp [rwl]; exact hszl) ?_, hfA, fun p hp => ?_,
    fun p hp => ?_, fun b hb => ?_, fun j hj => ?_, by simp [rwl], by simp [hva, hv.va], by simp [hvl, hv.vlen],
    by simp [rcap], by simp [hpr, hv.procs], by simp [hvv, hv.v], fun y hy1 hy2 => ?_, ?_⟩
  · refine slRep_result (kc := kc) (cid := cid) (gids := gids) hT hgl hndg hsubg (fun j hj => hbidC j hj)
      (fun j hj => ?_) (fun i' hi' => ?_) (fun i' hi' => ?_) hTid (by simp [rwl]; omega)
    · obtain ⟨gid, e1, e2, e3⟩ := hgrp j hj
      refine ⟨gid, e1, ?_, BlkRep.of_dsl e3 hfv (by simp [hva]) (by simp [hwl])⟩
      have hpos : bse + T.length + ((groupAux g none cb).length - 1 - j) =
          bse + k - df + ((groupAux g none cb).length - 1 - j) := by omega
      simp only [State.charge_wa]
      rw [hss, hpos, hsh ((groupAux g none cb).length - 1 - j) (by omega)]
      simp only [State.charge_wa, State.setW_wa]
      rw [show bse + k + kc - 1 + 1 - (groupAux g none cb).length + ((groupAux g none cb).length - 1 - j) =
        bse + k + kc - 1 - j by omega]
      exact e2
    · have hp : bse + (T.length - 1 - i') < bse + k - df := by omega
      simp only [State.charge_wa]; rw [hss, hkeep _ (Or.inl hp), State.charge_wa, State.setW_wa]
      exact hv.stklow _ (by omega)
    · have hne' : ∀ j < kc, cid j ≠ stkId st bse T.length i' := fun j hj e => hTid i' hi' j hj e.symm
      have hrec := hv.recs _ hne'
      have hmem : T[i'] ∈ T := List.getElem_mem hi'
      refine BlkRep.of_fields (hT.blk i' hi') (fun a ha => ?_) (by simp [hva, hv.va]) (fun a ha => ?_)
        (fun x hx => ⟨fun a ha => ?_, by simp [hva, hv.va]⟩) (by simp [rwl])
      · simp at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl
        · rw [hfA "blk.bot" (by simp [fgArrs])]
        · rw [hfA "blk.h" (by simp [fgArrs])]
        · rw [hfA "blk.v" (by simp [fgArrs])]
        · rw [hfA "blk.e" (by simp [fgArrs])]
        · rw [hfA "blk.r" (by simp [fgArrs])]
      · simp at ha
        rcases ha with rfl | rfl | rfl
        · rw [hfv "blk.hd" (by decide) (by decide)]; exact hrec.1
        · rw [hfv "blk.tl" (by decide) (by decide)]; exact hrec.2.1
        · rw [hfv "blk.cnt" (by decide) (by decide)]; exact hrec.2.2
      · simp at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [hfA "ent.key" (by simp [fgArrs])]
        · rw [hfA "ent.h" (by simp [fgArrs])]
        · rw [hfA "ent.v" (by simp [fgArrs])]
        · rw [hfA "ent.e" (by simp [fgArrs])]
        · rw [hfA "ent.r" (by simp [fgArrs])]
        · rw [hfv "ent.nxt" (by decide) (by decide)]; exact hv.nxt _ (hTent _ hmem x hx)
  · simp only [State.charge_wa]
    rw [storeW_wa_ne hp, harr "dsl.sz" (by decide), State.charge_wa, State.setW_wa, hv.arr "dsl.sz" (by decide)]
  · have hp' : p < bse + k - df := by omega
    simp only [State.charge_wa]; rw [hss, hkeep p (Or.inl hp'), State.charge_wa, State.setW_wa]
    exact hv.stklow _ (by omega)
  · have hrec := hv.recs b hb
    refine ⟨?_, ?_, ?_⟩
    · rw [hfv "blk.hd" (by decide) (by decide)]; exact hrec.1
    · rw [hfv "blk.tl" (by decide) (by decide)]; exact hrec.2.1
    · rw [hfv "blk.cnt" (by decide) (by decide)]; exact hrec.2.2
  · rw [hfv "ent.nxt" (by decide) (by decide)]; exact hv.nxt j hj
  · simp only [State.charge_w, State.storeW_w]; rw [rw_ y hy1]; exact hvw y hy2
  · simp only [State.charge_cost, State.storeW_cost]
    have := hv.cost
    simp only [State.charge_cost, State.setW_cost] at hcost
    omega

/-- **F-GROUP** (B-L3 F-MERGE core, agent-06).  With the child `D'` on top of the parent's slice
(`base(child) = bse + k`, agent-04's A1) and the parent's surviving tail `T` (length `k - df`) at `[bse, …)`,
`fGroup` leaves the parent's slice holding `groupAux g none D'.blocks ++ T` (`g = M/3` in `DB.merge`), in time
`O(|D'.blocks|)`. -/
theorem runs_fGroup {st : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap lv bse g df k : ℕ} {D' : DStr (Fin G.n) (WLab G s)} {T : List (Block (Fin G.n) (WLab G s))}
    (hlv : st.w "md.lv" = lv) (hb : st.w "md.b" = bse) (hg : st.w "md.g" = g) (hdfr : st.w "md.df" = df)
    (hszl : lv + 1 < st.wlen "dsl.sz") (hk : st.wa "dsl.sz" lv = k) (hTl : T.length + df = k)
    (hC : DRep st H V bcap (lv + 1) (bse + k) D') (hne : D'.blocks ≠ [])
    (hT : SlRep st H V bcap bse T)
    (hTid : ∀ i < T.length, ∀ j < D'.blocks.length,
      stkId st bse T.length i ≠ stkId st (bse + k) D'.blocks.length j)
    (hTent : ∀ b ∈ T, ∀ y ∈ b.ents, y.id ∉ eids D'.blocks)
    (hent : (eids D'.blocks).Nodup) (hBA : BlkArrs st bcap)
    (hcap : bse + k + D'.blocks.length + (eids D'.blocks).length + lv + 8 < st.cap) :
    Runs realOps fGroup st (fun r =>
      (∀ (M : ℕ) (Bd : WLab G s), DRep r H V bcap lv bse ⟨M, Bd, groupAux g none D'.blocks ++ T⟩) ∧
      (∀ a, a ∉ fgArrs → r.wa a = st.wa a) ∧
      (∀ p, p ≠ lv → r.wa "dsl.sz" p = st.wa "dsl.sz" p) ∧
      (∀ p, p < bse + T.length → r.wa "dsl.stk" p = st.wa "dsl.stk" p) ∧
      (∀ b, (∀ j < D'.blocks.length, stkId st (bse + k) D'.blocks.length j ≠ b) →
        r.wa "blk.hd" b = st.wa "blk.hd" b ∧ r.wa "blk.tl" b = st.wa "blk.tl" b ∧
        r.wa "blk.cnt" b = st.wa "blk.cnt" b) ∧
      (∀ j, j ∉ eids D'.blocks → r.wa "ent.nxt" j = st.wa "ent.nxt" j) ∧
      r.wlen = st.wlen ∧ r.va = st.va ∧ r.vlen = st.vlen ∧ r.cap = st.cap ∧ r.procs = st.procs ∧
      r.v = st.v ∧ (∀ y, y ∉ fgRegs → r.w y = st.w y) ∧
      r.cost ≤ st.cost + 24 * D'.blocks.length + 18) := by
  have hszC := hC.sz
  have hstkC := hC.stkb
  have h1 : 1 < st.cap := by omega
  unfold fGroup
  apply runs_seq
  refine runs_wset (a := k) (by rw [evalW_load_of (j := lv) (by simp [hlv]) (by omega)]; simp [hk]) ?_
  apply runs_seq
  refine runs_wset (a := D'.blocks.length) (by
      rw [evalW_load_of (evalW_add_of (x := lv) (y := 1) (by simp [hlv]) (evalW_lit_of (by simp; omega))
        (by simp; omega)) (by simp; omega)]
      simp [hszC]) ?_
  apply runs_seq
  refine runs_wset (a := bse + k + D'.blocks.length - 1) (by
      simp [hb, fit_of_lt (show bse + k < st.cap by omega),
        fit_of_lt (show bse + k + D'.blocks.length < st.cap by omega), fit_of_lt h1]) ?_
  apply runs_seq
  refine runs_wset (evalW_lit_of (by simp; omega)) ?_
  apply runs_seq
  refine runs_wset (evalW_lit_of (by simp; omega)) ?_
  apply runs_seq
  refine runs_wset (evalW_lit_of (by simp; omega)) ?_
  refine (runs_fgMain (lv := lv) (bse := bse) (g := g) (df := df) (k := k) (D' := D') (T := T)
    (st := (((((((((((st.setW "md.k" k).charge 1).setW "md.kc" D'.blocks.length).charge 1).setW "md.top"
      (bse + k + D'.blocks.length - 1)).charge 1).setW "md.r" 0).charge 1).setW "md.w" 0).charge 1).setW "md.hc" 0).charge 1)
    (by simp [hlv]) (by simp [hb]) (by simp [hg]) (by simp [hdfr]) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp; omega) hTl
    (DRep.of_regs hC (by simp) (by simp) (by simp)) hne (SlRep.of_regs hT (by simp) (by simp) (by simp)) hTid hTent
    hent (by unfold BlkArrs at hBA ⊢; simpa using hBA) (by simp; omega)).mono (fun r hr => ?_)
  obtain ⟨h1', h2', h3', h4', h5', h6', h7', h8', h9', h10', h11', h12', h13', h14'⟩ := hr
  refine ⟨h1', h2', h3', h4', h5', h6', h7', h8', h9', h10', h11', h12', fun y hy => ?_, ?_⟩
  · have hy' : y ≠ "md.j" := fun e => hy (by simp [e, fgRegs])
    have hy'' : y ∉ loopRegs := fun h => hy (by simp [loopRegs] at h; simp [fgRegs]; tauto)
    rw [h13' y hy' hy'']
    simp [fgRegs] at hy
    simp [hy]
  · simp only [State.charge_cost, State.setW_cost] at h14'; omega

end Top

end Frontier.CHD.FGroup
