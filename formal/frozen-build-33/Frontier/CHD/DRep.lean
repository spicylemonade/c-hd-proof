import Frontier.CHD.DBlocks
import Frontier.CHD.LabRAM

/-!
# DRep — RAM representation of DS' structures (B-L3, agent-02, NON-GATE)

Layout (agent-02 13:38, ACKed by agent-04 13:54; shared-stack variant (A1) = one `dsl.stk` array,
each level owning the slice `[base, base + sz)`):

* entry pool: `ent.key[i]`, `ent.nxt[i]` (`0` = end, `j+1`), label fields `entA`;
* `live[v]` (`0` = none, `i+1`), fresh counter register `ds.fresh`;
* block records by id: `blk.hd/tl` (`0` = empty, `i+1`), `blk.cnt`, `blk.bot` (`1` iff sep `= ⊥`),
  separator label fields `blkA`;
* per level: `dsl.sz[lv]`, stack slice `dsl.stk[base + j]` (top `j = sz-1` = FRONT).

Predicates: `EntRep` (pool entry = key + represented FINITE value), `LList` (linked id list),
`SepRep`, `BlkRep`, `DRep` (one structure), `LiveRep`, `PoolRep`, `BlkArrs`/`EntArrs`
(capacities), with transport lemmas (`*.of_unchanged` for frames disjoint from the D arrays `dW`/`dV`,
`EntRep.ext` for history growth).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.DIns

open Frontier Frontier.CHD Frontier.CHD.DB

/-! ## Part 2: the RAM representation of DS' structures -/

section RAMRep

open Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD.MLab Frontier.CHD.LabTab

variable {G : Graph} {s : Fin G.n}

/-- The entry pool's label fields. -/
def entA : LArr := ⟨"ent.len", "ent.h", "ent.v", "ent.e", "ent.r"⟩
/-- The block records' separator label fields. -/
def blkA : LArr := ⟨"blk.len", "blk.h", "blk.v", "blk.e", "blk.r"⟩

/-- Pool entry `i` holds key `v` and the FINITE walk value `a` (history `H`, counters `V`). -/
def EntRep (st : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ) (i : ℕ)
    (v : Fin G.n) (a : WLab G s) : Prop :=
  st.wa "ent.key" i = v ∧ ∃ (m : MLabel G) (p : List (Fin G.m)),
    AHolds st entA i m ∧ Rep (s := s) H V m p ∧ a = ((toW p : WalkOrd G s) : WLab G s)

/-- The linked list through `ent.nxt` from head word `h` (`0` = nil, `i+1` = entry `i`) visits
exactly `l`. -/
inductive LList (st : State ℝ≥0) : ℕ → List ℕ → Prop
  | nil : LList st 0 []
  | cons (i : ℕ) (l : List ℕ) : i < st.wlen "ent.nxt" → LList st (st.wa "ent.nxt" i) l →
      LList st (i + 1) (i :: l)

/-- Separator of block record `bid`: `⊥` (bot flag `1`) or a represented finite label. -/
def SepRep (st : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ) (bid : ℕ)
    (sp : WithBot (WLab G s)) : Prop :=
  (st.wa "blk.bot" bid = 1 ↔ sp = ⊥) ∧
  (sp = ⊥ ∨ ∃ (m : MLabel G) (q : List (Fin G.m)), AHolds st blkA bid m ∧
    Rep (s := s) H V m q ∧ sp = ((((toW q : WalkOrd G s) : WLab G s)) : WithBot (WLab G s)))

/-- The tail word of an id list. -/
def tlWord (l : List ℕ) : ℕ :=
  match l.getLast? with
  | none => 0
  | some i => i + 1

/-- Block record `bid` represents block `b`. -/
def BlkRep (st : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ) (bid : ℕ)
    (b : Block (Fin G.n) (WLab G s)) : Prop :=
  SepRep st H V bid b.sep ∧ LList st (st.wa "blk.hd" bid) (b.ents.map (·.id)) ∧
    (∀ x ∈ b.ents, EntRep st H V x.id x.key x.val) ∧
    st.wa "blk.cnt" bid = b.ents.length ∧ st.wa "blk.tl" bid = tlWord (b.ents.map (·.id))

/-- The id of list block `i` of a stack with base `bse` holding `k` blocks (top = front). -/
def stkId (st : State ℝ≥0) (bse k i : ℕ) : ℕ := st.wa "dsl.stk" (bse + (k - 1 - i))

/-- Arrays of block records are allocated for ids `< bcap`. -/
def BlkArrs (st : State ℝ≥0) (bcap : ℕ) : Prop :=
  bcap ≤ st.wlen "blk.hd" ∧ bcap ≤ st.wlen "blk.tl" ∧ bcap ≤ st.wlen "blk.cnt" ∧
    bcap ≤ st.wlen "blk.bot" ∧ bcap ≤ st.vlen blkA.l ∧ bcap ≤ st.wlen blkA.h ∧
    bcap ≤ st.wlen blkA.v ∧ bcap ≤ st.wlen blkA.e ∧ bcap ≤ st.wlen blkA.r

/-- Arrays of the entry pool are allocated for ids `< ecap`. -/
def EntArrs (st : State ℝ≥0) (ecap : ℕ) : Prop :=
  ecap ≤ st.wlen "ent.key" ∧ ecap ≤ st.wlen "ent.nxt" ∧ ecap ≤ st.vlen entA.l ∧
    ecap ≤ st.wlen entA.h ∧ ecap ≤ st.wlen entA.v ∧ ecap ≤ st.wlen entA.e ∧ ecap ≤ st.wlen entA.r

/-- **One DS' structure** at level `lv` with stack base `bse`. -/
structure DRep (st : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (bcap lv bse : ℕ) (D : DStr (Fin G.n) (WLab G s)) : Prop where
  sz : st.wa "dsl.sz" lv = D.blocks.length
  szb : lv < st.wlen "dsl.sz"
  stkb : bse + D.blocks.length ≤ st.wlen "dsl.stk"
  blk : ∀ i (hi : i < D.blocks.length), BlkRep st H V (stkId st bse D.blocks.length i) D.blocks[i]
  inj : ∀ i j, i < D.blocks.length → j < D.blocks.length →
    stkId st bse D.blocks.length i = stkId st bse D.blocks.length j → i = j
  bidb : ∀ i < D.blocks.length, stkId st bse D.blocks.length i < bcap

/-- The live map word. -/
def liveWord (o : Option (ℕ × WLab G s)) : ℕ :=
  match o with
  | none => 0
  | some (i, _) => i + 1

/-- The global live map. -/
def LiveRep (st : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (L : Live (Fin G.n) (WLab G s)) : Prop :=
  G.n ≤ st.wlen "live" ∧ ∀ v : Fin G.n, st.wa "live" v = liveWord (L v) ∧
    ∀ i a, L v = some (i, a) → EntRep st H V i v a

/-- The fresh-id counter and pool capacity. -/
def PoolRep (st : State ℝ≥0) (fresh ecap : ℕ) : Prop :=
  st.w "ds.fresh" = fresh ∧ fresh < ecap ∧ EntArrs st ecap

/-! ### Transport lemmas -/

theorem EntRep.ext {st : State ℝ≥0} {H H' : Fin G.n → ℕ → List (Fin G.m)} {V V' : Fin G.n → ℕ}
    {i : ℕ} {v : Fin G.n} {a : WLab G s} (h : EntRep st H V i v a) (hE : HExt H V H' V') :
    EntRep st H' V' i v a := by
  obtain ⟨h1, m, p, h2, h3, h4⟩ := h
  exact ⟨h1, m, p, h2, Rep.ext h3 hE, h4⟩

/-- Entries are preserved by machine steps that leave the pool fields at `i` alone. -/
theorem EntRep.of_eq {st r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {i : ℕ} {v : Fin G.n} {a : WLab G s} (h : EntRep st H V i v a)
    (hk : r.wa "ent.key" i = st.wa "ent.key" i) (hl : r.va entA.l i = st.va entA.l i)
    (hh : r.wa entA.h i = st.wa entA.h i) (hv : r.wa entA.v i = st.wa entA.v i)
    (he : r.wa entA.e i = st.wa entA.e i) (hr : r.wa entA.r i = st.wa entA.r i) :
    EntRep r H V i v a := by
  obtain ⟨h1, m, p, ⟨a1, a2, a3, a4, a5⟩, h3, h4⟩ := h
  exact ⟨hk.trans h1, m, p, ⟨hl.trans a1, hh.trans a2, hv.trans a3, he.trans a4, hr.trans a5⟩,
    h3, h4⟩

/-- A linked list survives any change that keeps `ent.nxt` on its nodes (and its length). -/
theorem LList.of_eq {st r : State ℝ≥0} {h : ℕ} {l : List ℕ} (hl : LList st h l)
    (hn : ∀ j ∈ l, r.wa "ent.nxt" j = st.wa "ent.nxt" j)
    (hlen : st.wlen "ent.nxt" ≤ r.wlen "ent.nxt") : LList r h l := by
  induction hl with
  | nil => exact LList.nil
  | cons i l hi _ ih =>
    refine LList.cons i l (lt_of_lt_of_le hi hlen) ?_
    rw [hn i List.mem_cons_self]
    exact ih (fun j hj => hn j (List.mem_cons_of_mem _ hj))

theorem SepRep.of_eq {st r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bid : ℕ} {sp : WithBot (WLab G s)} (h : SepRep st H V bid sp)
    (hb : r.wa "blk.bot" bid = st.wa "blk.bot" bid) (hl : r.va blkA.l bid = st.va blkA.l bid)
    (hh : r.wa blkA.h bid = st.wa blkA.h bid) (hv : r.wa blkA.v bid = st.wa blkA.v bid)
    (he : r.wa blkA.e bid = st.wa blkA.e bid) (hr : r.wa blkA.r bid = st.wa blkA.r bid) :
    SepRep r H V bid sp := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [hb]; exact h1, ?_⟩
  rcases h2 with h2 | ⟨m, q, ⟨a1, a2, a3, a4, a5⟩, h3, h4⟩
  · exact Or.inl h2
  · exact Or.inr ⟨m, q, ⟨hl.trans a1, hh.trans a2, hv.trans a3, he.trans a4, hr.trans a5⟩, h3, h4⟩

/-- Word arrays of the D layer. -/
def dW : List String :=
  ["ent.key", "ent.nxt", "ent.h", "ent.v", "ent.e", "ent.r", "blk.hd", "blk.tl", "blk.cnt",
   "blk.bot", "blk.h", "blk.v", "blk.e", "blk.r", "dsl.sz", "dsl.stk", "live"]
/-- Value arrays of the D layer. -/
def dV : List String := ["ent.len", "blk.len"]

section Frames

variable {st r : State ℝ≥0} {wa va wr vr : List String}

theorem wa_eq (hu : Unchanged st r wa va wr vr) (hw : ∀ a ∈ wa, a ∉ dW) {a : String}
    (ha : a ∈ dW) : r.wa a = st.wa a ∧ r.wlen a = st.wlen a :=
  hu.warr a (fun h => hw a h ha)

theorem va_eq (hu : Unchanged st r wa va wr vr) (hv : ∀ a ∈ va, a ∉ dV) {a : String}
    (ha : a ∈ dV) : r.va a = st.va a ∧ r.vlen a = st.vlen a :=
  hu.varr a (fun h => hv a h ha)

theorem EntRep.of_unchanged {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {i : ℕ}
    {v : Fin G.n} {a : WLab G s} (h : EntRep st H V i v a) (hu : Unchanged st r wa va wr vr)
    (hw : ∀ a ∈ wa, a ∉ dW) (hv : ∀ a ∈ va, a ∉ dV) : EntRep r H V i v a :=
  h.of_eq (by rw [(wa_eq hu hw (by simp [dW])).1]) (by rw [(va_eq hu hv (by simp [dV, entA])).1])
    (by rw [(wa_eq hu hw (by simp [dW, entA])).1]) (by rw [(wa_eq hu hw (by simp [dW, entA])).1])
    (by rw [(wa_eq hu hw (by simp [dW, entA])).1]) (by rw [(wa_eq hu hw (by simp [dW, entA])).1])

theorem SepRep.of_unchanged {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {bid : ℕ}
    {sp : WithBot (WLab G s)} (h : SepRep st H V bid sp) (hu : Unchanged st r wa va wr vr)
    (hw : ∀ a ∈ wa, a ∉ dW) (hv : ∀ a ∈ va, a ∉ dV) : SepRep r H V bid sp :=
  h.of_eq (by rw [(wa_eq hu hw (by simp [dW])).1]) (by rw [(va_eq hu hv (by simp [dV, blkA])).1])
    (by rw [(wa_eq hu hw (by simp [dW, blkA])).1]) (by rw [(wa_eq hu hw (by simp [dW, blkA])).1])
    (by rw [(wa_eq hu hw (by simp [dW, blkA])).1]) (by rw [(wa_eq hu hw (by simp [dW, blkA])).1])

theorem LList.of_unchanged {h : ℕ} {l : List ℕ} (hl : LList st h l)
    (hu : Unchanged st r wa va wr vr) (hw : ∀ a ∈ wa, a ∉ dW) : LList r h l :=
  hl.of_eq (fun j _ => by rw [(wa_eq hu hw (by simp [dW])).1])
    (le_of_eq (wa_eq hu hw (by simp [dW])).2.symm)

theorem BlkRep.of_unchanged {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {bid : ℕ}
    {b : Block (Fin G.n) (WLab G s)} (h : BlkRep st H V bid b) (hu : Unchanged st r wa va wr vr)
    (hw : ∀ a ∈ wa, a ∉ dW) (hv : ∀ a ∈ va, a ∉ dV) : BlkRep r H V bid b := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1.of_unchanged hu hw hv, ?_, fun x hx => (h3 x hx).of_unchanged hu hw hv, ?_, ?_⟩
  · rw [(wa_eq hu hw (by simp [dW])).1]; exact h2.of_unchanged hu hw
  · rw [(wa_eq hu hw (by simp [dW])).1]; exact h4
  · rw [(wa_eq hu hw (by simp [dW])).1]; exact h5

theorem stkId_of_unchanged (hu : Unchanged st r wa va wr vr) (hw : ∀ a ∈ wa, a ∉ dW)
    (bse k i : ℕ) : stkId r bse k i = stkId st bse k i := by
  unfold stkId; rw [(wa_eq hu hw (by simp [dW])).1]

theorem DRep.of_unchanged {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bcap lv bse : ℕ} {D : DStr (Fin G.n) (WLab G s)} (h : DRep st H V bcap lv bse D)
    (hu : Unchanged st r wa va wr vr) (hw : ∀ a ∈ wa, a ∉ dW) (hv : ∀ a ∈ va, a ∉ dV) :
    DRep r H V bcap lv bse D := by
  have hs := stkId_of_unchanged hu hw
  refine ⟨?_, ?_, ?_, fun i hi => ?_, fun i j hi hj => ?_, fun i hi => ?_⟩
  · rw [(wa_eq hu hw (by simp [dW])).1]; exact h.sz
  · rw [(wa_eq hu hw (by simp [dW])).2]; exact h.szb
  · rw [(wa_eq hu hw (by simp [dW])).2]; exact h.stkb
  · rw [hs]; exact (h.blk i hi).of_unchanged hu hw hv
  · rw [hs, hs]; exact h.inj i j hi hj
  · rw [hs]; exact h.bidb i hi

theorem BlkArrs.of_unchanged {bcap : ℕ} (h : BlkArrs st bcap) (hu : Unchanged st r wa va wr vr)
    (hw : ∀ a ∈ wa, a ∉ dW) (hv : ∀ a ∈ va, a ∉ dV) : BlkArrs r bcap := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [(wa_eq hu hw (by simp [dW, blkA])).2]; assumption)
    | (rw [(va_eq hu hv (by simp [dV, blkA])).2]; assumption)

end Frames

end RAMRep

end Frontier.CHD.DIns
