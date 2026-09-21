import Frontier.CHD.BM
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Frontier.CHD.BMCost — the cost-indexed, traced BMSSP recursion (L4-COST, Layer A)

Owner: agent-01 (with agent-03, COORD G2-4 "L4-COST bridge"; spine side agent-08).  NON-GATE.

A cost-indexed refinement of the relational BMSSP of `Frontier.CHD.BM`, in the form the RAM
spine (B-L4) refines and the cost aggregation (L5, `Frontier.CostAggregate`) consumes:

* **phases** — every premise of a constructor is one phase of the B1 pseudocode BM.1–BM.31 /
  BC.1–BC.9, and carries the operation-table cost of that phase (see `iterCost`, `initCost`,
  `finCost`, `BaseLoopC`); `D`-store operations are charged the amortized costs `DCost` of
  package L3, FindPivots the cost reported by its cost-indexed relation (package L2);
* **window scans** (BM.19–21) relax only the window edges `B_i ≤ d[u] ⊕ e < B` (monotone
  pointers into sorted out-lists), in any order (tracker O8);
* **persistent FindPivots state** `Φ` (e.g. the set of deleted edges of the L_X rule, COORD
  G2-4 D1) is threaded through all calls in execution order;
* **lower bounds**: the sub-call of an iteration receives `B_low = B'` of the current state;
* **logs**: every derivation produces the list of its call records (`CallRec`) indexed by call
  paths (`[]` = the call itself; sub-call `i` of the path-`π` call has path `i :: π`
  shifted…, i.e. child paths are obtained by prepending the loop index), so the call forest
  and all L4-owned counters of `CostAggregate.CallCounters` are read off the log.

Main results (stage 1):
* `bmsspC_post`: Lemma S2.1 (`CallPost`) for every derivation of the cost-indexed relation,
  for any FindPivots cost relation meeting the contract (`FPCSound`), plus preservation of the
  persistent-state invariant;
* `bmsspC_top_exact`, `bmsspC_top_isSSSP`: top-level exactness.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-! ## Cost parameters, call records, logs -/

/-- Amortized costs and the pull-size bound of the `D` store at level `l` (package L3's cost
contract, DMSY26 Lemma 3.4 / CHD_SEC_DS).  The RAM implementation of `D` must refine each
operation within these costs up to a potential (amortization). -/
structure DCost where
  /-- pull-size bound `M_l` -/
  M : ℕ → ℕ
  /-- create an empty level-`l` structure -/
  new : ℕ → ℕ
  /-- one `Insert` (or decrease) at level `l` -/
  ins : ℕ → ℕ
  /-- `Delete` of a batch of `k` keys at level `l` -/
  del : ℕ → ℕ → ℕ
  /-- `Pull` at level `l` returning `k` keys -/
  pull : ℕ → ℕ → ℕ
  /-- `Merge` of a returned child structure with `k` keys into the level-`l` structure -/
  merge : ℕ → ℕ → ℕ
  /-- base case: one heap insertion / decrease-key -/
  bins : ℕ
  /-- base case: one extract-min -/
  bext : ℕ

section defs

variable (G s)

/-- The number of keys of a `D` store. -/
noncomputable def keyCount (D : DS G s) : ℕ := by
  classical
  exact (Finset.univ.filter fun y => D y ≠ none).card

/-- The record of one call: the counters exposed to the cost analysis (L5). -/
structure CallRec (Ω : Type) where
  /-- level of the call (`0` = base case) -/
  lvl : ℕ
  /-- lower bound `B_low` given by the caller -/
  Blow : WLab G s
  /-- bound `B` -/
  B : WLab G s
  /-- frontier `S` -/
  S : Finset (Fin G.n)
  /-- returned bound `B'` -/
  B' : WLab G s
  /-- returned set `U` -/
  U : Finset (Fin G.n)
  /-- base-case call -/
  base : Bool
  /-- number of pivot groups -/
  p : ℕ
  /-- failed roots (FindPivots) -/
  Q : Finset (Fin G.n)
  /-- completed region (FindPivots) -/
  W : Finset (Fin G.n)
  /-- `W'` (BM.26) -/
  W' : Finset (Fin G.n)
  /-- jumps: window edges scanned at BM.19–21 over all iterations -/
  J : Finset (Fin G.m)
  /-- edges relaxed out of `W'` at BM.27–28 -/
  Wr : Finset (Fin G.m)
  /-- FindPivots data (trees, foreign leaves, deleted edges, …; `none` for base calls) -/
  fp : Option Ω
  /-- FindPivots cost -/
  cFP : ℕ
  /-- total `Merge` cost of the loop -/
  cMerge : ℕ
  /-- own cost of the call (excluding its sub-calls), including `cFP` and `cMerge` -/
  cost : ℕ

/-- An execution log: call records indexed by call paths. -/
abbrev Log (Ω : Type) := List (List ℕ × CallRec G s Ω)

/-- A cost-indexed FindPivots relation (package L2: `Invoke` + MakePivots):
`FPC l Blow B S d0 φ d1 p P Q W φ' ω c` — at level `l`, with lower bound `Blow`, bound `B`,
frontier `S`, labels `d0` and persistent state `φ`, FindPivots returns labels `d1`, groups `P`,
failed roots `Q`, region `W`, new persistent state `φ'`, data `ω`, at cost `c`. -/
abbrev FPRelC (Φ Ω : Type) := ℕ → WLab G s → WLab G s → Finset (Fin G.n) → Labels G s → Φ →
  Labels G s → (p : ℕ) → (Fin p → Finset (Fin G.n)) → Finset (Fin G.n) → Finset (Fin G.n) →
  Φ → Ω → ℕ → Prop

/-- The shape of a traced call relation: `Blow B S d0 φ ↦ res φ' log`. -/
abbrev SubRelC (Φ Ω : Type) := WLab G s → WLab G s → Finset (Fin G.n) → Labels G s → Φ →
  Result G s → Φ → Log G s Ω → Prop

variable {G s}

/-- Prefix every path of a log by the loop index `i` (embedding a sub-call's log). -/
def Log.shift {Ω : Type} (i : ℕ) (lg : Log G s Ω) : Log G s Ω :=
  lg.map fun x => (i :: x.1, x.2)

/-- Total cost of a log. -/
def Log.cost {Ω : Type} (lg : Log G s Ω) : ℕ := (lg.map fun x => x.2.cost).sum

/-- Groups whose current pivot was pulled (BM.11–12 scans them). -/
noncomputable def pulledGroups {p : ℕ} (σ : LState G s p) (S0 : Finset (Fin G.n)) :
    Finset (Fin p) := by
  classical
  exact Finset.univ.filter fun j => σ.piv j ∈ S0 ∧ σ.piv j ∈ σ.P j

/-- Groups needing a re-selected pivot (BM.16–18 / BM.23). -/
noncomputable def markedGroups {p : ℕ} (σ : LState G s p) (Ui : Finset (Fin G.n)) :
    Finset (Fin p) := by
  classical
  exact Finset.univ.filter fun j => σ.piv j ∈ Ui ∧ (σ.P j \ Ui).Nonempty

/-- Cost of one loop iteration at level `lv`, excluding the sub-call and the merge:
BM.9 test (1), BM.10 Pull, BM.11–12 expansion (the pulled keys and the scanned groups),
BM.15–18 FIX-STALE deletion plus group removal / marking (1 per returned vertex), BM.19–21
window scan (1 per returned vertex for the pointer test, `1 + ins` per window edge),
BM.23 re-selection (a scan of the remaining group plus one insertion per marked group). -/
noncomputable def iterCost (DC : DCost) (lv : ℕ) {p : ℕ} (σ : LState G s p)
    (S0 Ui : Finset (Fin G.n)) (nL : ℕ) : ℕ :=
  1 + DC.pull lv S0.card
    + (S0.card + ∑ j ∈ pulledGroups σ S0, (σ.P j).card)
    + (DC.del lv Ui.card + Ui.card)
    + (Ui.card + nL * (1 + DC.ins lv))
    + ∑ j ∈ markedGroups σ Ui, ((σ.P j \ Ui).card + 1 + DC.ins lv)

/-- Cost of BM.3–8 after FindPivots: a new structure, per group an argmin scan and a
membership push (`|P_j|`), per pivot an insertion and a `min` (BM.8). -/
noncomputable def initCost (DC : DCost) (lv p : ℕ) (P : Fin p → Finset (Fin G.n)) : ℕ :=
  DC.new lv + ∑ j, (P j).card + p * (2 + DC.ins lv)

/-- Cost of BM.24a–31: `B'` (1), BM.25 scan of `S` with re-insertions, BM.26 scan of `W`,
BM.27–28 relaxations out of `W'` (`1 + ins` per edge, 1 per vertex), BM.29 deletion of `W'`,
BM.30 popping the group memberships (`|P_j|`). -/
noncomputable def finCost (DC : DCost) (lv p : ℕ) (P : Fin p → Finset (Fin G.n))
    (S W T6 W' : Finset (Fin G.n)) (nL : ℕ) : ℕ :=
  1 + (S.card + T6.card * DC.ins lv) + W.card + (W'.card + nL * (1 + DC.ins lv))
    + DC.del lv W'.card + ∑ j, (P j).card

/-- The loop state after one iteration (BM.14–BM.23), relaxing along the list `L`. -/
noncomputable def nextState (B : WLab G s) {p : ℕ} (σ : LState G s p) (Bi B'i : WLab G s)
    (Ui : Finset (Fin G.n)) (D1 Di : DS G s) (d1 : Labels G s) (L : List (Fin G.m))
    (piv' : Fin p → Fin G.n) : LState G s p :=
  { d := (L.foldl (relaxIns G s B (some Bi)) (d1, (D1.merge Di).deleteSet Ui)).1
    D := insertMany G s
          (L.foldl (relaxIns G s B (some Bi)) (d1, (D1.merge Di).deleteSet Ui)).2
          (reselected σ Ui piv')
          (L.foldl (relaxIns G s B (some Bi)) (d1, (D1.merge Di).deleteSet Ui)).1
    P := fun j => σ.P j \ Ui
    piv := piv'
    U := σ.U ∪ Ui
    B' := B'i }

variable (G s)

/-- The main loop (BM.9–BM.24), cost-indexed and traced.
`LoopC DC sub lv B τ i σ φ σ' φ' lg J cm c`: from iteration `i`, loop state `σ` and persistent
state `φ`, the loop ends in `σ'`, `φ'`; `lg` is the log of the sub-calls (sub-call of iteration
`i` gets path prefix `i`), `J` the window edges scanned, `cm` the merge costs, `c` the other
own costs of the loop. -/
inductive LoopC {Φ Ω : Type} {p : ℕ} (DC : DCost) (sub : SubRelC G s Φ Ω) (lv : ℕ)
    (B : WLab G s) (τ : ℕ) :
    ℕ → LState G s p → Φ → LState G s p → Φ → Log G s Ω → Finset (Fin G.m) → ℕ → ℕ → Prop
  | stop (i : ℕ) (σ : LState G s p) (φ : Φ) :
      (τ < σ.U.card ∨ σ.D.IsEmpty) → LoopC DC sub lv B τ i σ φ σ φ [] ∅ 0 1
  | step (i : ℕ) (σ σ' : LState G s p) (φ φ1 φ' : Φ) (S0 : Finset (Fin G.n)) (Bi : WLab G s)
      (D1 : DS G s) (B'i : WLab G s) (Ui : Finset (Fin G.n)) (Di : DS G s) (d1 : Labels G s)
      (L' : List (Fin G.m)) (piv' : Fin p → Fin G.n) (lg lg' : Log G s Ω)
      (J' : Finset (Fin G.m)) (cm c : ℕ) :
      σ.U.card ≤ τ → ¬ σ.D.IsEmpty →
      -- BM.10
      PullSpec σ.D B S0 Bi D1 → S0.card ≤ DC.M lv →
      -- strong pull (DS' pull_post): a short pull empties `D` at separator `B`
      (S0.card < DC.M lv → D1.IsEmpty ∧ Bi = B) →
      -- BM.11–13
      sub σ.B' Bi (expand σ S0 Bi) σ.d φ (B'i, Ui, Di, d1) φ1 lg →
      -- BM.19–21: the window edges, any order, no repetition
      L'.Nodup →
      (∀ e, e ∈ L' ↔ G.src e ∈ Ui ∧ Bi ≤ ext (d1 (G.src e)) e ∧ ext (d1 (G.src e)) e < B) →
      -- BM.16–18, BM.23
      Reselect σ Ui (L'.foldl (relaxIns G s B (some Bi)) (d1, (D1.merge Di).deleteSet Ui)).1
        piv' →
      LoopC DC sub lv B τ (i + 1) (nextState B σ Bi B'i Ui D1 Di d1 L' piv') φ1 σ' φ' lg' J' cm c →
      LoopC DC sub lv B τ i σ φ σ' φ' (lg.shift i ++ lg') (L'.toFinset ∪ J')
        (DC.merge lv (keyCount G s Di) + cm) (iterCost DC lv σ S0 Ui L'.length + c)

/-- One recursive call at level `lv` (BM.1–BM.31), cost-indexed and traced. -/
def CallC {Φ Ω : Type} (FPC : FPRelC G s Φ Ω) (DC : DCost) (sub : SubRelC G s Φ Ω) (lv : ℕ)
    (Blow B : WLab G s) (S : Finset (Fin G.n)) (d0 : Labels G s) (φ0 : Φ) (τ : ℕ)
    (res : Result G s) (φ2 : Φ) (lg : Log G s Ω) : Prop :=
  ∃ (d1 : Labels G s) (p : ℕ) (P : Fin p → Finset (Fin G.n)) (Q W : Finset (Fin G.n)) (φ1 : Φ)
    (ω : Ω) (cfp : ℕ) (piv : Fin p → Fin G.n) (σ : LState G s p) (lgc : Log G s Ω)
    (J : Finset (Fin G.m)) (cm cl : ℕ) (L : List (Fin G.m)) (B'f : WLab G s)
    (T6 W' : Finset (Fin G.n)),
    -- BM.3–4
    FPC lv Blow B S d0 φ0 d1 p P Q W φ1 ω cfp ∧
    -- BM.5–8
    (∀ j, piv j ∈ P j ∧ ∀ x ∈ P j, d1 (piv j) ≤ d1 x) ∧
    -- BM.9–24
    LoopC G s DC sub lv B τ 0 (initState B d1 P piv) φ1 σ φ2 lgc J cm cl ∧
    -- BM.24a (FIX-EMPTY)
    (σ.D.IsEmpty → B'f = B) ∧ (¬ σ.D.IsEmpty → B'f = σ.B') ∧
    -- BM.25
    (∀ x, x ∈ T6 ↔ x ∈ S ∧ B'f ≤ σ.d x ∧ σ.d x < B) ∧
    -- BM.26
    (∀ x, x ∈ W' ↔ (x ∈ W ∧ x ∉ σ.U) ∧ σ.d x < B'f) ∧
    -- BM.27–31
    Enumerates G L W' ∧
    res = (B'f, σ.U ∪ W',
      ((L.foldl (relaxIns G s B (some B'f)) (σ.d, insertMany G s σ.D T6 σ.d)).2).deleteSet W',
      (L.foldl (relaxIns G s B (some B'f)) (σ.d, insertMany G s σ.D T6 σ.d)).1) ∧
    lg = ([], { lvl := lv, Blow := Blow, B := B, S := S, B' := B'f, U := σ.U ∪ W',
                base := false, p := p, Q := Q, W := W, W' := W', J := J, Wr := L.toFinset,
                fp := some ω, cFP := cfp, cMerge := cm,
                cost := cfp + initCost DC lv p P + cl + cm
                  + finCost DC lv p P S W T6 W' L.length }) :: lgc

/-- The base-case loop (BC.3–BC.7), cost-indexed: each extraction costs `1 + bext`, each
out-edge of the extracted vertex `1 + bins`; the final test costs 1. -/
inductive BaseLoopC (DC : DCost) (B : WLab G s) (τ : ℕ) :
    Labels G s × DS G s × Finset (Fin G.n) → Labels G s × DS G s × Finset (Fin G.n) → ℕ → Prop
  | stop (st : Labels G s × DS G s × Finset (Fin G.n)) :
      (st.2.1.IsEmpty ∨ τ ≤ st.2.2.card) → BaseLoopC DC B τ st st 1
  | step (d : Labels G s) (D : DS G s) (U : Finset (Fin G.n)) (u : Fin G.n) (val : WLab G s)
      (L : List (Fin G.m)) (st' : Labels G s × DS G s × Finset (Fin G.n)) (c : ℕ) :
      D u = some val → (∀ y v, D y = some v → val ≤ v) → U.card < τ →
      Enumerates G L {u} →
      BaseLoopC DC B τ
        ((L.foldl (relaxIns G s B none) (d, D.deleteSet {u})).1,
         (L.foldl (relaxIns G s B none) (d, D.deleteSet {u})).2, insert u U) st' c →
      BaseLoopC DC B τ (d, D, U) st' (c + 1 + DC.bext + L.length * (1 + DC.bins))

/-- The base case (BC.1–BC.9, FIX-BASE), cost-indexed and traced: `|S|` insertions, the loop,
and the final `B'` (1). -/
def BaseC {Φ Ω : Type} (DC : DCost) (Blow B : WLab G s) (S : Finset (Fin G.n)) (d0 : Labels G s)
    (φ0 : Φ) (τ : ℕ) (res : Result G s) (φ1 : Φ) (lg : Log G s Ω) : Prop :=
  ∃ (st : Labels G s × DS G s × Finset (Fin G.n)) (c : ℕ),
    BaseLoopC G s DC B τ (d0, insertMany G s DS.empty S d0, ∅) st c ∧
    res.2.1 = st.2.2 ∧ res.2.2.1 = st.2.1 ∧ res.2.2.2 = st.1 ∧
    (st.2.1.IsEmpty → res.1 = B) ∧
    (¬ st.2.1.IsEmpty → ∃ y, st.2.1 y = some res.1 ∧ ∀ z v, st.2.1 z = some v → res.1 ≤ v) ∧
    φ1 = φ0 ∧
    lg = [([], { lvl := 0, Blow := Blow, B := B, S := S, B' := res.1, U := res.2.1,
                 base := true, p := 0, Q := ∅, W := ∅, W' := ∅, J := ∅, Wr := ∅,
                 fp := none, cFP := 0, cMerge := 0,
                 cost := S.card * (1 + DC.bins) + c + 1 })]

/-- The cost-indexed, traced BMSSP relation at every level. -/
def BMSSPC {Φ Ω : Type} (FPC : FPRelC G s Φ Ω) (DC : DCost) (τ : ℕ → ℕ) :
    ℕ → SubRelC G s Φ Ω
  | 0 => fun Blow B S d φ res φ' lg => BaseC G s DC Blow B S d φ (τ 0) res φ' lg
  | l + 1 => fun Blow B S d φ res φ' lg =>
      CallC G s FPC DC (BMSSPC FPC DC τ l) (l + 1) Blow B S d φ (τ (l + 1)) res φ' lg

/-- The cost-indexed relation in the `Refines` shape: a call of cost `k` is a derivation whose
log has total cost `k`. -/
def CallRelCost {Φ Ω : Type} (FPC : FPRelC G s Φ Ω) (DC : DCost) (τ : ℕ → ℕ) (l : ℕ)
    (Blow B : WLab G s) (S : Finset (Fin G.n)) (d0 : Labels G s) (φ0 : Φ) (res : Result G s)
    (φ1 : Φ) (k : ℕ) : Prop :=
  ∃ lg : Log G s Ω, BMSSPC G s FPC DC τ l Blow B S d0 φ0 res φ1 lg ∧ k = lg.cost

/-- A cost-indexed FindPivots relation meets the contract, and preserves the persistent-state
invariant `Inv`, on every call satisfying `CallPre` whose frontier lies above `Blow`. -/
def FPCSound {Φ Ω : Type} (FPC : FPRelC G s Φ Ω) (Inv : Φ → Prop) : Prop :=
  ∀ l Blow B S d0 φ d1 p (P : Fin p → Finset (Fin G.n)) Q W φ' ω c,
    CallPre B S d0 → Inv φ → (∀ x ∈ S, Blow ≤ d0 x) →
    FPC l Blow B S d0 φ d1 p P Q W φ' ω c → FPContract B S d0 d1 p P Q W ∧ Inv φ'

end defs

/-! ## Stage 1: correctness of every cost-indexed derivation -/

section post

variable {Φ Ω : Type} {DC : DCost}

theorem baseLoopC_erase {B : WLab G s} {τ : ℕ} :
    ∀ {st st' : Labels G s × DS G s × Finset (Fin G.n)} {c : ℕ},
      BaseLoopC G s DC B τ st st' c → BaseLoop G s B τ st st' := by
  intro st st' c h
  induction h with
  | stop st hst => exact BaseLoop.stop st hst
  | step d D U u val L st' c hu hmin hcard hL _ ih => exact BaseLoop.step d D U u val L st' hu hmin hcard hL ih

theorem baseC_erase {Blow B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} {φ0 φ1 : Φ}
    {τ : ℕ} {res : Result G s} {lg : Log G s Ω} (h : BaseC G s DC Blow B S d0 φ0 τ res φ1 lg) :
    BaseRel G s B S d0 τ res ∧ φ1 = φ0 := by
  obtain ⟨st, c, hloop, h1, h2, h3, h4, h5, h6, -⟩ := h
  exact ⟨⟨st, baseLoopC_erase hloop, h1, h2, h3, h4, h5⟩, h6⟩

variable {B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {p : ℕ}
  {P0 : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {B'0 : WLab G s}

/-- The cost-indexed loop preserves the loop invariant (and the persistent invariant), given
correct sub-calls. -/
theorem loopC_inv (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W) {cap : ℕ}
    {sub : SubRelC G s Φ Ω} {Inv : Φ → Prop}
    (hsub : ∀ Blow B S d φ res φ' lg, CallPre B S d → Inv φ → (∀ x ∈ S, Blow ≤ d x) →
      sub Blow B S d φ res φ' lg → CallPost G s B S d cap res ∧ Inv φ')
    {lv τ : ℕ} :
    ∀ i (σ : LState G s p) φ σ' φ' lg J cm c, LoopC G s DC sub lv B τ i σ φ σ' φ' lg J cm c →
      LInv G s B S d0 d1 P0 B'0 σ → Inv φ →
      LInv G s B S d0 d1 P0 B'0 σ' ∧ (τ < σ'.U.card ∨ σ'.D.IsEmpty) ∧ Inv φ' := by
  intro i σ φ σ' φ' lg J cm c hloop
  induction hloop with
  | stop i σ φ hstop => exact fun h hI => ⟨h, hstop, hI⟩
  | step i σ σ' φ φ1 φ' S0 Bi D1 B'i Ui Di dsub L' piv' lg lg' J' cm c _ hne hpull _ _ hsubrel
      hnd hmem hres _ ih =>
    intro h hI
    have hsp := step_pre hpre hfp h hpull
    have hlow : ∀ x ∈ expand σ S0 Bi, σ.B' ≤ σ.d x := fun x hx =>
      ((Si_facts h hpull hx).1.2.2).trans (h.walk.sound x)
    obtain ⟨hpost, hI1⟩ := hsub _ _ _ _ _ _ _ _ hsp hI hlow hsubrel
    have hmem' : ∀ e, e ∈ L' ↔ G.src e ∈ Ui ∧ Bi ≤ ext (dis (s := s) (G.src e)) e ∧
        ext (dis (s := s) (G.src e)) e < B := by
      intro e
      rw [hmem e]
      constructor
      · rintro ⟨hu, h1, h2⟩
        have hc : dsub (G.src e) = dis (s := s) (G.src e) := hpost.U_complete _ hu
        rw [hc] at h1 h2
        exact ⟨hu, h1, h2⟩
      · rintro ⟨hu, h1, h2⟩
        have hc : dsub (G.src e) = dis (s := s) (G.src e) := hpost.U_complete _ hu
        rw [← hc] at h1 h2
        exact ⟨hu, h1, h2⟩
    obtain ⟨L, hL, hfold⟩ :=
      window_scan_step hpull.bound hpost ((D1.merge Di).deleteSet Ui) hnd hmem'
    have hres' : Reselect σ Ui
        (L.foldl (relaxIns G s B (some Bi)) (dsub, (D1.merge Di).deleteSet Ui)).1 piv' := by
      rw [hfold]; exact hres
    have hnext := step_post hpre hfp h hne hpull hpost hL hres'
    rw [hfold] at hnext
    exact ih hnext hI1

/-- **Recursive case of Lemma S2.1** for the cost-indexed relation. -/
theorem callC_post {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} (hFPC : FPCSound G s FPC Inv)
    {sub : SubRelC G s Φ Ω} {cap : ℕ}
    (hsub : ∀ Blow B S d φ res φ' lg, CallPre B S d → Inv φ → (∀ x ∈ S, Blow ≤ d x) →
      sub Blow B S d φ res φ' lg → CallPost G s B S d cap res ∧ Inv φ')
    {lv : ℕ} {Blow : WLab G s} {φ0 φ2 : Φ} {τ : ℕ} {res : Result G s} {lg : Log G s Ω}
    (hpre : CallPre B S d0) (hI : Inv φ0) (hlow : ∀ x ∈ S, Blow ≤ d0 x)
    (hrel : CallC G s FPC DC sub lv Blow B S d0 φ0 τ res φ2 lg) :
    CallPost G s B S d0 (τ + 1) res ∧ Inv φ2 := by
  obtain ⟨d1, p, P, Q, W, φ1, ω, cfp, piv, σ, lgc, J, cm, cl, L, B'f, T6, W', hfprel, hpiv,
    hloop, hB'e, hB'n, hT6, hW', hL, rfl, -⟩ := hrel
  obtain ⟨hfp, hI1⟩ := hFPC _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpre hI hlow hfprel
  have h0 := linv_init hpre hfp hpiv
  obtain ⟨h, hstop, hI2⟩ := loopC_inv hpre hfp hsub _ _ _ _ _ _ _ _ _ hloop h0 hI1
  exact ⟨final_post hpre hfp hpiv h hstop hB'e hB'n hT6 hW' hL, hI2⟩

/-- **Lemma S2.1 (all levels)** for every derivation of the cost-indexed, traced relation. -/
theorem bmsspC_post {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} (hFPC : FPCSound G s FPC Inv)
    (τ : ℕ → ℕ) :
    ∀ (l : ℕ) (Blow B : WLab G s) (S : Finset (Fin G.n)) (d : Labels G s) (φ : Φ)
      (res : Result G s) (φ' : Φ) (lg : Log G s Ω),
      CallPre B S d → Inv φ → (∀ x ∈ S, Blow ≤ d x) →
      BMSSPC G s FPC DC τ l Blow B S d φ res φ' lg → CallPost G s B S d (τ l) res ∧ Inv φ'
  | 0, Blow, B, S, d, φ, res, φ', lg, hpre, hI, _, hrel => by
    obtain ⟨hb, rfl⟩ := baseC_erase hrel
    exact ⟨baseRel_post hpre hb, hI⟩
  | l + 1, Blow, B, S, d, φ, res, φ', lg, hpre, hI, hlow, hrel => by
    obtain ⟨hpost, hI'⟩ := callC_post hFPC (bmsspC_post hFPC τ l) hpre hI hlow hrel
    exact ⟨hpost.of_cap_le (Nat.le_succ _), hI'⟩

/-- **Top-level exactness** for the cost-indexed relation: `BMSSP(⊤, {s}, l)` with `τ l > n`
from the initial labels returns the canonical labels. -/
theorem bmsspC_top_exact {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} (hFPC : FPCSound G s FPC Inv)
    (τ : ℕ → ℕ) (l : ℕ) (hτ : G.n < τ l) {Blow : WLab G s} (hlow : Blow ≤ initLabels s s)
    {φ φ' : Φ} (hI : Inv φ) {res : Result G s} {lg : Log G s Ω}
    (hrel : BMSSPC G s FPC DC τ l Blow ⊤ {s} (initLabels s) φ res φ' lg) :
    (∀ v, Complete res.2.2.2 v) ∧ Inv φ' := by
  obtain ⟨hpost, hI'⟩ := bmsspC_post hFPC τ l Blow ⊤ {s} (initLabels s) φ res φ' lg callPre_top hI
    (fun x hx => by rw [Finset.mem_singleton.mp hx]; exact hlow) hrel
  refine ⟨?_, hI'⟩
  have hB' : res.1 = ⊤ := by
    by_contra hne
    have hcard := hpost.partial_card (lt_of_le_of_ne le_top hne)
    have hle : res.2.1.card ≤ G.n := by
      calc res.2.1.card ≤ (Finset.univ : Finset (Fin G.n)).card :=
            Finset.card_le_card (Finset.subset_univ _)
        _ = G.n := Finset.card_fin G.n
    omega
  intro v
  by_cases hr : G.Reachable s v
  · have hvU : v ∈ res.2.1 := by
      rw [hpost.U_eq v, hB']
      have hs : OnPath (s := s) s v :=
        ⟨hr, [], path (s := s) v, by simp, IsWalk.nil s, (path_isMinWalk hr).1⟩
      refine ⟨?_, s, Finset.mem_coe.mpr (Finset.mem_singleton_self s), hs⟩
      rw [dis_of_reachable hr]; exact WithTop.coe_lt_top _
    exact hpost.U_complete v hvU
  · have h1 := hpost.walk.sound v
    show res.2.2.2 v = dis (s := s) v
    rw [dis_of_not_reachable hr] at h1 ⊢
    exact top_le_iff.mp h1

/-- **Top-level output** of the cost-indexed relation: an exact SSSP solution. -/
theorem bmsspC_top_isSSSP {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} (hFPC : FPCSound G s FPC Inv)
    (τ : ℕ → ℕ) (l : ℕ) (hτ : G.n < τ l) {Blow : WLab G s} (hlow : Blow ≤ initLabels s s)
    {φ φ' : Φ} (hI : Inv φ) {res : Result G s} {lg : Log G s Ω}
    (hrel : BMSSPC G s FPC DC τ l Blow ⊤ {s} (initLabels s) φ res φ' lg) :
    G.IsSSSP s (fun v => labelLen (res.2.2.2 v)) :=
  isSSSP_of_complete (bmsspC_top_exact hFPC τ l hτ hlow hI hrel).1

end post

end BM
end CHD
end Frontier
