import Frontier.CHD.BMTrace
import Frontier.CHD.DBlocks
import Frontier.CHD.DLazy

/-!
# Frontier.CHD.BMLazy — BMSSP over the lazy block structure `D` (option (B), L4-COST + O6)

Owner: agent-01 (with agent-04's `Frontier.CHD.DBlocks`).  NON-GATE.

The cost-indexed traced BMSSP relation `BMSSPD` whose `D`-store is the CONCRETE lazy structure of
package L3 (`DB.DStr` blocks with one GLOBAL live map and a fresh-id counter), with the ACTUAL
costs of agent-04's operations `DB.pull`, `DB.insert`, `DB.merge`, `DB.deleteKeys`.  Its premises
are only these functions (plus FindPivots, sub-calls and choices of lists), so a RAM refinement
of `D` is a plain data refinement.

The literal stores of `Frontier.CHD.BMCost` are the VIEWS of the concrete structures; the
simulation theorem (stage O6) maps every `BMSSPD` derivation to a `BMSSPC` derivation with the
same states and call records, so correctness (Lemma S2.1, exactness) and all log facts
(call forest, ranges, counters) transfer.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

section defs

variable (G s)

/-- The global live map of the lazy `D` structures. -/
abbrev LiveM := DB.Live (Fin G.n) (WLab G s)

/-- One lazy `D` structure. -/
abbrev DStrM := DB.DStr (Fin G.n) (WLab G s)

/-- The key (end vertex) of a label; `s` for `⊤` (never stored). -/
def kof (lab : WLab G s) : Fin G.n :=
  match lab with
  | ⊤ => s
  | (p : WalkOrd G s) => endV G s p

/-- The global state of the lazy structures: live map and fresh entry id. -/
structure DGl where
  L : LiveM G s
  fresh : ℕ

variable {G s}

/-- The literal view of a structure. -/
noncomputable def DGl.view (g : DGl G s) (Dc : DStrM G s) : DS G s := DB.view g.L Dc

/-- A new, empty level structure with parameter `M` and bound `Bd`. -/
def newC (M : ℕ) (Bd : WLab G s) : DStrM G s := ⟨M, Bd, [⟨⊥, []⟩]⟩

variable (G s) in
/-- A `D` implementation over lazy block structures (package L3): its operations (tree charge
`T` first) and the view-level specifications the simulation uses.  Instances: `dbOps`
(agent-04's `DBlocks`, eager splits); agent-04's `DLazy` (lazy front splits) has the same types. -/
structure DOps where
  /-- a size invariant of structures preserved by the operations -/
  SzOK : DStrM G s → Prop
  /-- admissible block parameters for merging a child (parameter `M'`) into a parent (`M`) -/
  mergeM : ℕ → ℕ → Prop
  pull : ℕ → LiveM G s → DStrM G s → List (Fin G.n) × WLab G s × LiveM G s × DStrM G s × ℕ
  insert : ℕ → LiveM G s → ℕ → DStrM G s → Fin G.n → WLab G s →
    LiveM G s × ℕ × DStrM G s × ℕ
  merge : ℕ → DStrM G s → DStrM G s → DStrM G s × ℕ
  sz_new : ∀ (M : ℕ) (Bd : WLab G s), SzOK ⟨M, Bd, [⟨⊥, []⟩]⟩
  pull_spec : ∀ (T : ℕ) {L : LiveM G s} {D : DStrM G s}, DB.WF L D →
    (∀ y, y ∈ (pull T L D).1 ↔ ∃ a, DB.view L D y = some a ∧ a < (pull T L D).2.1) ∧
    (∀ y, DB.view (pull T L D).2.2.1 (pull T L D).2.2.2.1 y =
        if y ∈ (pull T L D).1 then none else DB.view L D y) ∧
    (pull T L D).2.1 ≤ D.Bd ∧
    DB.WF (pull T L D).2.2.1 (pull T L D).2.2.2.1 ∧
    (pull T L D).2.2.1 = DB.clearKeys L (pull T L D).1 ∧
    (pull T L D).2.2.2.1.M = D.M ∧ (pull T L D).2.2.2.1.Bd = D.Bd
  pull_post : ∀ (T : ℕ) {L : LiveM G s} {D : DStrM G s} {kf : WLab G s → Fin G.n}, DB.WF L D →
    DB.KeyInj L kf → DB.IdsNodup D → 1 ≤ D.M →
    (pull T L D).1.length ≤ D.M ∧
    ((pull T L D).2.1 = D.Bd ∨ (pull T L D).1.length = D.M) ∧
    ((∃ y, DB.HasKey L D y) → (pull T L D).1 ≠ []) ∧
    (∀ e ∈ DB.liveVals (pull T L D).2.2.1 (pull T L D).2.2.2.1.blocks, (pull T L D).2.1 ≤ e.val) ∧
    (∀ b ∈ (pull T L D).2.2.2.1.blocks.tail, ((pull T L D).2.1 : WithBot (WLab G s)) < b.sep)
  pull_aux : ∀ (T : ℕ) {L : LiveM G s} {D : DStrM G s} {kf : WLab G s → Fin G.n} {fresh : ℕ},
    DB.WF L D → DB.KeyInj L kf → DB.IdsNodup D → 1 ≤ D.M → SzOK D → DB.FreshOK fresh D →
    DB.IdsNodup (pull T L D).2.2.2.1 ∧ SzOK (pull T L D).2.2.2.1 ∧
      DB.FreshOK fresh (pull T L D).2.2.2.1 ∧ DB.KeyInj (pull T L D).2.2.1 kf
  pull_ents : ∀ (T : ℕ) (L : LiveM G s) (D : DStrM G s),
    ∀ x ∈ DB.allEnts (pull T L D).2.2.2.1.blocks, x ∈ DB.allEnts D.blocks
  /-- the pulled keys are distinct -/
  pull_nodup : ∀ (T : ℕ) {L : LiveM G s} {D : DStrM G s}, DB.IdsNodup D → (pull T L D).1.Nodup
  insert_spec : ∀ (T : ℕ) {L : LiveM G s} {fresh : ℕ} {D : DStrM G s} {v : Fin G.n}
    {lam : WLab G s}, DB.WF L D → DB.FreshOK fresh D → lam < D.Bd →
    (DB.skipIns L v lam = true → DB.HasKey L D v) →
    (∀ y, DB.view (insert T L fresh D v lam).1 (insert T L fresh D v lam).2.2.1 y =
        if y = v then some (DB.insVal (DB.view L D v) lam) else DB.view L D y) ∧
    DB.WF (insert T L fresh D v lam).1 (insert T L fresh D v lam).2.2.1 ∧
    DB.FreshOK (insert T L fresh D v lam).2.1 (insert T L fresh D v lam).2.2.1 ∧
    fresh ≤ (insert T L fresh D v lam).2.1
  insert_aux : ∀ (T : ℕ) {L : LiveM G s} {fresh : ℕ} {D : DStrM G s} {v : Fin G.n}
    {lam : WLab G s} {kf : WLab G s → Fin G.n}, DB.FreshOK fresh D → DB.IdsNodup D →
    DB.KeyInj L kf → kf lam = v → SzOK D → 1 ≤ D.M →
    DB.IdsNodup (insert T L fresh D v lam).2.2.1 ∧ SzOK (insert T L fresh D v lam).2.2.1 ∧
      DB.KeyInj (insert T L fresh D v lam).1 kf
  insert_L : ∀ (T : ℕ) (L : LiveM G s) (fresh : ℕ) (D : DStrM G s) (v : Fin G.n) (lam : WLab G s),
    (insert T L fresh D v lam).1 =
      if DB.skipIns L v lam then L else Function.update L v (some (fresh, lam))
  insert_ents : ∀ (T : ℕ) (L : LiveM G s) (fresh : ℕ) (D : DStrM G s) (v : Fin G.n)
    (lam : WLab G s), ∀ x ∈ DB.allEnts (insert T L fresh D v lam).2.2.1.blocks,
      x ∈ DB.allEnts D.blocks ∨ x = ⟨fresh, v, lam⟩
  insert_M : ∀ (T : ℕ) (L : LiveM G s) (fresh : ℕ) (D : DStrM G s) (v : Fin G.n) (lam : WLab G s),
    (insert T L fresh D v lam).2.2.1.M = D.M ∧ (insert T L fresh D v lam).2.2.1.Bd = D.Bd
  merge_spec : ∀ (T : ℕ) {L : LiveM G s} {D D' : DStrM G s}, DB.WF L D → DB.WF L D' →
    (∀ e ∈ DB.liveVals L D.blocks, D'.Bd ≤ e.val) →
    (∀ b ∈ D.blocks.tail, ((D'.Bd : WLab G s) : WithBot (WLab G s)) < b.sep) → D'.Bd ≤ D.Bd →
    (∀ y, DB.HasKey L (merge T D D').1 y ↔ DB.HasKey L D' y ∨ DB.HasKey L D y) ∧
    (∀ y, DB.view L (merge T D D').1 y =
      if DB.HasKey L D' y then DB.view L D' y else DB.view L D y) ∧
    DB.WF L (merge T D D').1
  merge_aux : ∀ (T : ℕ) {D D' : DStrM G s} {fresh : ℕ}, D.blocks ≠ [] → DB.IdsNodup D →
    DB.IdsNodup D' → (∀ x ∈ DB.allEnts D.blocks, ∀ y ∈ DB.allEnts D'.blocks, x.id ≠ y.id) →
    SzOK D → SzOK D' → mergeM D.M D'.M → DB.FreshOK fresh D → DB.FreshOK fresh D' →
    DB.IdsNodup (merge T D D').1 ∧ SzOK (merge T D D').1 ∧ DB.FreshOK fresh (merge T D D').1
  merge_ents : ∀ (T : ℕ) (D D' : DStrM G s),
    ∀ x ∈ DB.allEnts (merge T D D').1.blocks, x ∈ DB.allEnts D.blocks ∨ x ∈ DB.allEnts D'.blocks
  merge_M : ∀ (T : ℕ) (D D' : DStrM G s), (merge T D D').1.M = D.M ∧ (merge T D D').1.Bd = D.Bd

variable (ops : DOps G s)

/-- `Insert` on a structure: new global state, new structure, cost. -/
noncomputable def insC (T : ℕ) (g : DGl G s) (Dc : DStrM G s) (v : Fin G.n) (lam : WLab G s) :
    DGl G s × DStrM G s × ℕ :=
  (⟨(ops.insert T g.L g.fresh Dc v lam).1, (ops.insert T g.L g.fresh Dc v lam).2.1⟩,
    (ops.insert T g.L g.fresh Dc v lam).2.2.1, (ops.insert T g.L g.fresh Dc v lam).2.2.2)

/-- Insert the vertices of a list with values `f`, in list order; costs add. -/
noncomputable def insManyC (T : ℕ) (f : Fin G.n → WLab G s) :
    List (Fin G.n) → DGl G s → DStrM G s → DGl G s × DStrM G s × ℕ
  | [], g, Dc => (g, Dc, 0)
  | y :: l, g, Dc =>
    ((insManyC T f l (insC ops T g Dc y (f y)).1 (insC ops T g Dc y (f y)).2.1).1,
     (insManyC T f l (insC ops T g Dc y (f y)).1 (insC ops T g Dc y (f y)).2.1).2.1,
     (insC ops T g Dc y (f y)).2.2 +
       (insManyC T f l (insC ops T g Dc y (f y)).1 (insC ops T g Dc y (f y)).2.1).2.2)

/-- `Pull` on a structure: pulled keys, separator, new global state, new structure, cost. -/
noncomputable def pullC (T : ℕ) (g : DGl G s) (Dc : DStrM G s) :
    List (Fin G.n) × WLab G s × DGl G s × DStrM G s × ℕ :=
  ((ops.pull T g.L Dc).1, (ops.pull T g.L Dc).2.1, ⟨(ops.pull T g.L Dc).2.2.1, g.fresh⟩,
    (ops.pull T g.L Dc).2.2.2.1, (ops.pull T g.L Dc).2.2.2.2)

/-- `Delete` of a list of keys: new global state, cost. -/
noncomputable def delC (g : DGl G s) (ks : List (Fin G.n)) : DGl G s × ℕ :=
  (⟨(DB.deleteKeys g.L ks).1, g.fresh⟩, (DB.deleteKeys g.L ks).2)

/-- State of a concrete relaxation scan: labels, global state, structure, cost so far. -/
structure RSt (G : Graph) (s : Fin G.n) where
  d : Labels G s
  g : DGl G s
  Dc : DStrM G s
  c : ℕ

/-- One relaxation with insertion into the concrete structure (mirrors `relaxIns`); the test costs
1, an insertion its actual cost. -/
noncomputable def relaxInsCc (T : ℕ) (B : WLab G s) (lo : Option (WLab G s)) (st : RSt G s)
    (e : Fin G.m) : RSt G s := by
  classical
  exact
    if ValidRelax G s st.d B e then
      match lo with
      | none =>
        ⟨Function.update st.d (G.dst e) (ext (st.d (G.src e)) e),
          (insC ops T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).1,
          (insC ops T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).2.1,
          st.c + 1 + (insC ops T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).2.2⟩
      | some b =>
        if b ≤ ext (st.d (G.src e)) e then
          ⟨Function.update st.d (G.dst e) (ext (st.d (G.src e)) e),
            (insC ops T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).1,
            (insC ops T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).2.1,
            st.c + 1 + (insC ops T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).2.2⟩
        else ⟨Function.update st.d (G.dst e) (ext (st.d (G.src e)) e), st.g, st.Dc, st.c + 1⟩
    else ⟨st.d, st.g, st.Dc, st.c + 1⟩

/-- The concrete loop state of a recursive call. -/
structure CSt (G : Graph) (s : Fin G.n) (p : ℕ) where
  d : Labels G s
  P : Fin p → Finset (Fin G.n)
  piv : Fin p → Fin G.n
  U : Finset (Fin G.n)
  B' : WLab G s
  g : DGl G s
  Dc : DStrM G s

/-- The literal loop state of a concrete one: its store is the view. -/
noncomputable def CSt.lit {p : ℕ} (cs : CSt G s p) : LState G s p :=
  { d := cs.d, D := cs.g.view cs.Dc, P := cs.P, piv := cs.piv, U := cs.U, B' := cs.B' }

/-- The concrete result of a call: bound, returned set, returned STRUCTURE, labels. -/
abbrev ResultD (G : Graph) (s : Fin G.n) := WLab G s × Finset (Fin G.n) × DStrM G s × Labels G s

variable (G s)

/-- The shape of a concrete traced call relation: `Blow B S d0 φ g ↦ res φ' g' log`. -/
abbrev SubRelD (Φ Ω : Type) := WLab G s → WLab G s → Finset (Fin G.n) → Labels G s → Φ →
  DGl G s → ResultD G s → Φ → DGl G s → Log G s Ω → Prop

variable {G s}

/-- The concrete state after one iteration (BM.14–BM.23): merge, FIX-STALE deletion (of the list
`lUi`), the window scan along `L'`, and the re-selection insertions (list `lres`). -/
noncomputable def nextD (T : ℕ) (B : WLab G s) {p : ℕ} (cs : CSt G s p) (Bi B'i : WLab G s)
    (Ui : Finset (Fin G.n)) (Dc1 Dci : DStrM G s) (d1 : Labels G s) (g2 : DGl G s)
    (lUi : List (Fin G.n)) (L' : List (Fin G.m)) (piv' : Fin p → Fin G.n)
    (lres : List (Fin G.n)) : CSt G s p :=
  { d := (L'.foldl (relaxInsCc ops T B (some Bi))
            ⟨d1, (delC g2 lUi).1, (ops.merge T Dc1 Dci).1, 0⟩).d
    P := fun j => cs.P j \ Ui
    piv := piv'
    U := cs.U ∪ Ui
    B' := B'i
    g := (insManyC ops T (L'.foldl (relaxInsCc ops T B (some Bi))
            ⟨d1, (delC g2 lUi).1, (ops.merge T Dc1 Dci).1, 0⟩).d lres
          (L'.foldl (relaxInsCc ops T B (some Bi)) ⟨d1, (delC g2 lUi).1, (ops.merge T Dc1 Dci).1, 0⟩).g
          (L'.foldl (relaxInsCc ops T B (some Bi))
            ⟨d1, (delC g2 lUi).1, (ops.merge T Dc1 Dci).1, 0⟩).Dc).1
    Dc := (insManyC ops T (L'.foldl (relaxInsCc ops T B (some Bi))
            ⟨d1, (delC g2 lUi).1, (ops.merge T Dc1 Dci).1, 0⟩).d lres
          (L'.foldl (relaxInsCc ops T B (some Bi)) ⟨d1, (delC g2 lUi).1, (ops.merge T Dc1 Dci).1, 0⟩).g
          (L'.foldl (relaxInsCc ops T B (some Bi))
            ⟨d1, (delC g2 lUi).1, (ops.merge T Dc1 Dci).1, 0⟩).Dc).2.1 }

/-- The actual cost of one iteration's own work (excluding the sub-call): loop test, pull, the
expansion scan, the merge, the deletion, the window scan (pointer tests + relaxations/insertions)
and the re-selection scan + insertions. -/
noncomputable def iterCostD (T : ℕ) (B : WLab G s) {p : ℕ} (cs : CSt G s p) (S0 : Finset (Fin G.n))
    (cp : ℕ) (Bi : WLab G s) (Ui : Finset (Fin G.n)) (Dc1 Dci : DStrM G s) (d1 : Labels G s)
    (g2 : DGl G s) (lUi : List (Fin G.n)) (L' : List (Fin G.m)) (lres : List (Fin G.n)) : ℕ :=
  1 + cp + (S0.card + ∑ j ∈ pulledGroups cs.lit S0, (cs.P j).card)
    + ((delC g2 lUi).2 + Ui.card) + Ui.card
    + (L'.foldl (relaxInsCc ops T B (some Bi)) ⟨d1, (delC g2 lUi).1, (ops.merge T Dc1 Dci).1, 0⟩).c
    + (∑ j ∈ markedGroups cs.lit Ui, ((cs.P j \ Ui).card + 1))
    + (insManyC ops T (L'.foldl (relaxInsCc ops T B (some Bi))
            ⟨d1, (delC g2 lUi).1, (ops.merge T Dc1 Dci).1, 0⟩).d lres
          (L'.foldl (relaxInsCc ops T B (some Bi)) ⟨d1, (delC g2 lUi).1, (ops.merge T Dc1 Dci).1, 0⟩).g
          (L'.foldl (relaxInsCc ops T B (some Bi))
            ⟨d1, (delC g2 lUi).1, (ops.merge T Dc1 Dci).1, 0⟩).Dc).2.2

variable (G s)

/-- The main loop over the lazy structure (BM.9–BM.24), cost-indexed (actual costs) and traced. -/
inductive LoopD {Φ Ω : Type} {p : ℕ} (T : ℕ) (sub : SubRelD G s Φ Ω) (B : WLab G s) (τ : ℕ) :
    ℕ → CSt G s p → Φ → CSt G s p → Φ → Log G s Ω → Finset (Fin G.m) → ℕ → ℕ → Prop
  | stop (i : ℕ) (cs : CSt G s p) (φ : Φ) :
      (τ < cs.U.card ∨ (cs.g.view cs.Dc).IsEmpty) → LoopD T sub B τ i cs φ cs φ [] ∅ 0 1
  | step (i : ℕ) (cs cs' : CSt G s p) (φ φ1 φ' : Φ) (ks : List (Fin G.n)) (Bi : WLab G s)
      (g1 : DGl G s) (Dc1 : DStrM G s) (cp : ℕ) (B'i : WLab G s) (Ui : Finset (Fin G.n))
      (Dci : DStrM G s) (d1 : Labels G s) (g2 : DGl G s) (lUi : List (Fin G.n))
      (L' : List (Fin G.m)) (piv' : Fin p → Fin G.n) (lres : List (Fin G.n))
      (lg lg' : Log G s Ω) (J' : Finset (Fin G.m)) (cm c : ℕ) :
      cs.U.card ≤ τ → ¬ (cs.g.view cs.Dc).IsEmpty →
      -- BM.10: pull
      pullC ops T cs.g cs.Dc = (ks, Bi, g1, Dc1, cp) →
      -- BM.11–13: the sub-call on the expanded pulled set, from the new global state
      sub cs.B' Bi (expand cs.lit ks.toFinset Bi) cs.d φ g1 (B'i, Ui, Dci, d1) φ1 g2 lg →
      -- BM.15: the list of `U_i` for FIX-STALE
      lUi.Nodup → lUi.toFinset = Ui →
      -- BM.19–21: the window edges
      L'.Nodup →
      (∀ e, e ∈ L' ↔ G.src e ∈ Ui ∧ Bi ≤ ext (d1 (G.src e)) e ∧ ext (d1 (G.src e)) e < B) →
      -- BM.16–18, BM.23
      Reselect cs.lit Ui (L'.foldl (relaxInsCc ops T B (some Bi))
        ⟨d1, (delC g2 lUi).1, (ops.merge T Dc1 Dci).1, 0⟩).d piv' →
      lres.Nodup → lres.toFinset = reselected cs.lit Ui piv' →
      LoopD T sub B τ (i + 1) (nextD ops T B cs Bi B'i Ui Dc1 Dci d1 g2 lUi L' piv' lres) φ1 cs' φ' lg'
        J' cm c →
      LoopD T sub B τ i cs φ cs' φ' (lg.shift i ++ lg') (L'.toFinset ∪ J')
        ((ops.merge T Dc1 Dci).2 + cm)
        (iterCostD ops T B cs ks.toFinset cp Bi Ui Dc1 Dci d1 g2 lUi L' lres + c)


variable {G s}

/-- The initialization BM.5–6: a new level structure, then the pivots (list `lpiv`) inserted with
their labels. -/
noncomputable def initD (T M : ℕ) (B : WLab G s) (d1 : Labels G s) (lpiv : List (Fin G.n))
    (g0 : DGl G s) : DGl G s × DStrM G s × ℕ :=
  insManyC ops T d1 lpiv g0 (newC M B)

/-- The finalization BM.25–29: re-insertion of `T6` (list `lT6`), the relaxations out of `W'`
along `L`, and the deletion of `W'` (list `lW'`): labels, global state, structure, cost. -/
noncomputable def finD (T : ℕ) (B B'f : WLab G s) (d : Labels G s) (g : DGl G s)
    (Dc : DStrM G s) (lT6 : List (Fin G.n)) (L : List (Fin G.m)) (lW' : List (Fin G.n)) :
    Labels G s × DGl G s × DStrM G s × ℕ :=
  ((L.foldl (relaxInsCc ops T B (some B'f))
      ⟨d, (insManyC ops T d lT6 g Dc).1, (insManyC ops T d lT6 g Dc).2.1, 0⟩).d,
    (delC (L.foldl (relaxInsCc ops T B (some B'f))
      ⟨d, (insManyC ops T d lT6 g Dc).1, (insManyC ops T d lT6 g Dc).2.1, 0⟩).g lW').1,
    (L.foldl (relaxInsCc ops T B (some B'f))
      ⟨d, (insManyC ops T d lT6 g Dc).1, (insManyC ops T d lT6 g Dc).2.1, 0⟩).Dc,
    (insManyC ops T d lT6 g Dc).2.2 + (L.foldl (relaxInsCc ops T B (some B'f))
      ⟨d, (insManyC ops T d lT6 g Dc).1, (insManyC ops T d lT6 g Dc).2.1, 0⟩).c
      + (delC (L.foldl (relaxInsCc ops T B (some B'f))
      ⟨d, (insManyC ops T d lT6 g Dc).1, (insManyC ops T d lT6 g Dc).2.1, 0⟩).g lW').2)

variable (G s)

/-- One recursive call at level `lv` over the lazy structure (BM.1–BM.31), cost-indexed (actual
costs) and traced.  `Mf lv` is the block parameter `M` of level `lv`. -/
def CallD {Φ Ω : Type} (FPC : FPRelC G s Φ Ω) (T : ℕ) (Mf : ℕ → ℕ) (sub : SubRelD G s Φ Ω)
    (lv : ℕ) (Blow B : WLab G s) (S : Finset (Fin G.n)) (d0 : Labels G s) (φ0 : Φ)
    (g0 : DGl G s) (τ : ℕ) (res : ResultD G s) (φ2 : Φ) (gE : DGl G s) (lg : Log G s Ω) :
    Prop :=
  ∃ (d1 : Labels G s) (p : ℕ) (P : Fin p → Finset (Fin G.n)) (Q W : Finset (Fin G.n)) (φ1 : Φ)
    (ω : Ω) (cfp : ℕ) (piv : Fin p → Fin G.n) (lpiv : List (Fin G.n)) (cs : CSt G s p)
    (lgc : Log G s Ω) (J : Finset (Fin G.m)) (cm cl : ℕ) (L : List (Fin G.m)) (B'f : WLab G s)
    (lT6 : List (Fin G.n)) (W' : Finset (Fin G.n)) (lW' : List (Fin G.n)),
    -- BM.3–4
    FPC lv Blow B S d0 φ0 d1 p P Q W φ1 ω cfp ∧
    -- BM.5–8
    (∀ j, piv j ∈ P j ∧ ∀ x ∈ P j, d1 (piv j) ≤ d1 x) ∧
    lpiv.Nodup ∧ lpiv.toFinset = Finset.univ.image piv ∧
    -- BM.9–24
    LoopD G s ops T sub B τ 0
      { d := d1, P := P, piv := piv, U := ∅, B' := initB' B d1 piv,
        g := (initD ops T (Mf lv) B d1 lpiv g0).1, Dc := (initD ops T (Mf lv) B d1 lpiv g0).2.1 }
      φ1 cs φ2 lgc J cm cl ∧
    -- BM.24a (FIX-EMPTY)
    ((cs.g.view cs.Dc).IsEmpty → B'f = B) ∧ (¬ (cs.g.view cs.Dc).IsEmpty → B'f = cs.B') ∧
    -- BM.25
    lT6.Nodup ∧ (∀ x, x ∈ lT6 ↔ x ∈ S ∧ B'f ≤ cs.d x ∧ cs.d x < B) ∧
    -- BM.26
    (∀ x, x ∈ W' ↔ (x ∈ W ∧ x ∉ cs.U) ∧ cs.d x < B'f) ∧
    -- BM.27–29
    Enumerates G L W' ∧ lW'.Nodup ∧ lW'.toFinset = W' ∧
    res = (B'f, cs.U ∪ W', (finD ops T B B'f cs.d cs.g cs.Dc lT6 L lW').2.2.1,
      (finD ops T B B'f cs.d cs.g cs.Dc lT6 L lW').1) ∧
    gE = (finD ops T B B'f cs.d cs.g cs.Dc lT6 L lW').2.1 ∧
    lg = ([], { lvl := lv, Blow := Blow, B := B, S := S, B' := B'f, U := cs.U ∪ W',
                base := false, p := p, Q := Q, W := W, W' := W', J := J, Wr := L.toFinset,
                fp := some ω, cFP := cfp, cMerge := cm,
                cost := cfp + ((initD ops T (Mf lv) B d1 lpiv g0).2.2 + ∑ j, (P j).card + 2 * p)
                  + cl + cm
                  + (1 + S.card + W.card + W'.card + ∑ j, (P j).card
                    + (finD ops T B B'f cs.d cs.g cs.Dc lT6 L lW').2.2.2) }) :: lgc

/-- The base-case loop (BC.3–BC.7) over a level-0 lazy structure (`M = 1`, so `Pull` is an
extract-min), cost-indexed (actual costs). -/
inductive BaseLoopD (T : ℕ) (B : WLab G s) (τ : ℕ) :
    Labels G s × DGl G s × DStrM G s × Finset (Fin G.n) →
      Labels G s × DGl G s × DStrM G s × Finset (Fin G.n) → ℕ → Prop
  | stop (st : Labels G s × DGl G s × DStrM G s × Finset (Fin G.n)) :
      ((st.2.1.view st.2.2.1).IsEmpty ∨ τ ≤ st.2.2.2.card) → BaseLoopD T B τ st st 1
  | step (d : Labels G s) (g : DGl G s) (Dc : DStrM G s) (U : Finset (Fin G.n)) (u : Fin G.n)
      (x : WLab G s) (g1 : DGl G s) (Dc1 : DStrM G s) (cp : ℕ) (L : List (Fin G.m))
      (st' : Labels G s × DGl G s × DStrM G s × Finset (Fin G.n)) (c : ℕ) :
      pullC ops T g Dc = ([u], x, g1, Dc1, cp) → U.card < τ → Enumerates G L {u} →
      BaseLoopD T B τ
        ((L.foldl (relaxInsCc ops T B none) ⟨d, g1, Dc1, 0⟩).d,
         (L.foldl (relaxInsCc ops T B none) ⟨d, g1, Dc1, 0⟩).g,
         (L.foldl (relaxInsCc ops T B none) ⟨d, g1, Dc1, 0⟩).Dc, insert u U) st' c →
      BaseLoopD T B τ (d, g, Dc, U) st'
        (c + 1 + cp + (L.foldl (relaxInsCc ops T B none) ⟨d, g1, Dc1, 0⟩).c)

/-- The base case (BC.1–BC.9, FIX-BASE) over a level-0 lazy structure with parameter `M0`: the
frontier (list `lS`) is inserted, the loop runs, and if the structure is not empty its minimum
`B'` is found by one more pull and re-inserted. -/
def BaseD {Φ Ω : Type} (T M0 : ℕ) (Blow B : WLab G s) (S : Finset (Fin G.n)) (d0 : Labels G s)
    (φ0 : Φ) (g0 : DGl G s) (τ : ℕ) (res : ResultD G s) (φ1 : Φ) (gE : DGl G s)
    (lg : Log G s Ω) : Prop :=
  ∃ (lS : List (Fin G.n)) (st : Labels G s × DGl G s × DStrM G s × Finset (Fin G.n)) (c cf : ℕ),
    lS.Nodup ∧ lS.toFinset = S ∧
    BaseLoopD G s ops T B τ
      (d0, (insManyC ops T d0 lS g0 (newC M0 B)).1, (insManyC ops T d0 lS g0 (newC M0 B)).2.1, ∅) st c ∧
    res.2.1 = st.2.2.2 ∧ res.2.2.2 = st.1 ∧
    ((st.2.1.view st.2.2.1).IsEmpty → res.1 = B ∧ res.2.2.1 = st.2.2.1 ∧ gE = st.2.1 ∧ cf = 0) ∧
    (¬ (st.2.1.view st.2.2.1).IsEmpty → ∃ (u : Fin G.n) (x : WLab G s) (g1 : DGl G s)
      (Dc1 : DStrM G s) (cp : ℕ),
      pullC ops T st.2.1 st.2.2.1 = ([u], x, g1, Dc1, cp) ∧ st.2.1.view st.2.2.1 u = some res.1 ∧
      res.2.2.1 = (insC ops T g1 Dc1 u res.1).2.1 ∧ gE = (insC ops T g1 Dc1 u res.1).1 ∧
      cf = cp + (insC ops T g1 Dc1 u res.1).2.2) ∧
    φ1 = φ0 ∧
    lg = [([], { lvl := 0, Blow := Blow, B := B, S := S, B' := res.1, U := res.2.1,
                 base := true, p := 0, Q := ∅, W := ∅, W' := ∅, J := ∅, Wr := ∅,
                 fp := none, cFP := 0, cMerge := 0,
                 cost := S.card + (insManyC ops T d0 lS g0 (newC M0 B)).2.2 + c + 1 + cf })]


/-- **The base case with a separate heap** (COORD O27, agent-08 14:07): the base loop is the
literal `BaseLoopC` (implemented by agent-06's IHeap; heap costs `DCb.bins/bext`), and at return
the leftover keys (list `lK`) are inserted with their labels into a new level-0 structure. -/
def BaseDH {Φ Ω : Type} (DCb : DCost) (T M0 : ℕ) (Blow B : WLab G s) (S : Finset (Fin G.n))
    (d0 : Labels G s) (φ0 : Φ) (g0 : DGl G s) (τ : ℕ) (res : ResultD G s) (φ1 : Φ) (gE : DGl G s)
    (lg : Log G s Ω) : Prop :=
  ∃ (st : Labels G s × DS G s × Finset (Fin G.n)) (c : ℕ) (lK : List (Fin G.n)),
    BaseLoopC G s DCb B τ (d0, insertMany G s DS.empty S d0, ∅) st c ∧
    lK.Nodup ∧ (∀ y, y ∈ lK ↔ st.2.1 y ≠ none) ∧
    res.2.1 = st.2.2 ∧ res.2.2.2 = st.1 ∧
    res.2.2.1 = (insManyC ops T st.1 lK g0 (newC M0 B)).2.1 ∧
    gE = (insManyC ops T st.1 lK g0 (newC M0 B)).1 ∧
    (st.2.1.IsEmpty → res.1 = B) ∧
    (¬ st.2.1.IsEmpty → ∃ y, st.2.1 y = some res.1 ∧ ∀ z v, st.2.1 z = some v → res.1 ≤ v) ∧
    φ1 = φ0 ∧
    lg = [([], { lvl := 0, Blow := Blow, B := B, S := S, B' := res.1, U := res.2.1,
                 base := true, p := 0, Q := ∅, W := ∅, W' := ∅, J := ∅, Wr := ∅,
                 fp := none, cFP := 0, cMerge := 0,
                 cost := S.card * (1 + DCb.bins) + c + 1
                   + (insManyC ops T st.1 lK g0 (newC M0 B)).2.2 })]

/-- The cost-indexed, traced BMSSP relation over the lazy structure, at every level. -/
def BMSSPD {Φ Ω : Type} (FPC : FPRelC G s Φ Ω) (DCb : DCost) (T : ℕ → ℕ) (Mf : ℕ → ℕ)
    (τ : ℕ → ℕ) : ℕ → SubRelD G s Φ Ω
  | 0 => fun Blow B S d φ g res φ' g' lg =>
      BaseDH G s ops DCb (T 0) (Mf 0) Blow B S d φ g (τ 0) res φ' g' lg
  | l + 1 => fun Blow B S d φ g res φ' g' lg =>
      CallD G s ops FPC (T (l + 1)) Mf (BMSSPD FPC DCb T Mf τ l) (l + 1) Blow B S d φ g (τ (l + 1))
        res φ' g' lg

end defs

variable {ops : DOps G s}


/-! ## Basic facts on keys, views and the operations -/

section basic

variable {T : ℕ}

theorem kof_coe (q : List (Fin G.m)) :
    kof G s ((toW q : WalkOrd G s) : WLab G s) = endV G s q := rfl

/-- The relaxation candidate of an edge has the edge's head as key. -/
theorem kof_ext {d : Labels G s} (hw : WalkInv d) {e : Fin G.m}
    (hne : ext (d (G.src e)) e ≠ ⊤) : kof G s (ext (d (G.src e)) e) = G.dst e := by
  have hs : d (G.src e) ≠ ⊤ := by
    intro h; rw [h, ext_top] at hne; exact hne rfl
  obtain ⟨q, hq⟩ := exists_list_of_ne_top hs
  rw [hq, ext_coe, kof_coe]
  exact endV_of_isWalk (walk_ext (hw _ q hq) e rfl)

/-- A finite label of `v` has key `v`. -/
theorem kof_of_walk {d : Labels G s} (hw : WalkInv d) {v : Fin G.n} (hv : d v ≠ ⊤) :
    kof G s (d v) = v := by
  obtain ⟨q, hq⟩ := exists_list_of_ne_top hv
  rw [hq, kof_coe]
  exact endV_of_isWalk (hw v q hq)

theorem view_ne_none_iff {L : LiveM G s} {D : DStrM G s} {v : Fin G.n} :
    DB.view L D v ≠ none ↔ DB.HasKey L D v := by
  rw [Ne, DB.view_eq_none, not_not]

theorem hasKey_of_view {L : LiveM G s} {D : DStrM G s} {v : Fin G.n} {a : WLab G s}
    (h : DB.view L D v = some a) : DB.HasKey L D v :=
  view_ne_none_iff.mp (by rw [h]; exact Option.some_ne_none a)

theorem view_lt_Bd {L : LiveM G s} {D : DStrM G s} (hwf : DB.WF L D) {y : Fin G.n} {a : WLab G s}
    (h : DB.view L D y = some a) : a < D.Bd := by
  obtain ⟨e, he, -, rfl⟩ := DB.view_eq_some.mp h
  obtain ⟨⟨b, hb, heb⟩, hl⟩ := DB.mem_liveVals.mp he
  have := (DB.IntervalOK.bounds hwf.2 b hb e heb hl).2
  exact WithBot.coe_lt_coe.mp this

theorem mergeVal_idem (a : Option (WLab G s)) (b : WLab G s) :
    DS.mergeVal (DS.mergeVal a (some b)) (some b) = DS.mergeVal a (some b) := by
  cases a with
  | none => simp [DS.mergeVal]
  | some a => simp [DS.mergeVal, min_assoc]

theorem mergeVal_eq_insVal (a : Option (WLab G s)) (b : WLab G s) :
    DS.mergeVal a (some b) = some (DB.insVal a b) := by
  cases a <;> rfl

theorem insertMany_insert (D : DS G s) (y : Fin G.n) (T0 : Finset (Fin G.n))
    (f : Fin G.n → WLab G s) :
    insertMany G s (D.insert y (f y)) T0 f = insertMany G s D (insert y T0) f := by
  classical
  funext z
  simp only [insertMany, DS.insert, Finset.mem_insert]
  by_cases hz : z = y
  · subst hz
    simp only [Function.update_self, true_or, ite_true]
    split_ifs
    · exact mergeVal_idem _ _
    · rfl
  · simp only [Function.update_of_ne hz, hz, false_or]

/-- Live-map changes of a call: unchanged, cleared, or pointing to a NEW entry (id `≥ f0`) with a
value below the call's bound `B`. -/
def CallChange (f0 : ℕ) (B : WLab G s) (L0 L1 : LiveM G s) : Prop :=
  ∀ y, L1 y = L0 y ∨ L1 y = none ∨ ∃ i a, f0 ≤ i ∧ a < B ∧ L1 y = some (i, a)

theorem CallChange.refl (f0 : ℕ) (B : WLab G s) (L : LiveM G s) : CallChange f0 B L L :=
  fun _ => Or.inl rfl

theorem CallChange.trans {f0 : ℕ} {B : WLab G s} {L0 L1 L2 : LiveM G s}
    (h1 : CallChange f0 B L0 L1) (h2 : CallChange f0 B L1 L2) : CallChange f0 B L0 L2 := by
  intro y
  rcases h2 y with h | h | h
  · rw [h]; exact h1 y
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem CallChange.mono {f0 f0' : ℕ} {B B' : WLab G s} {L0 L1 : LiveM G s}
    (h : CallChange f0 B L0 L1) (hf : f0' ≤ f0) (hB : B ≤ B') : CallChange f0' B' L0 L1 := by
  intro y
  rcases h y with h | h | ⟨i, a, hi, ha, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨i, a, hf.trans hi, lt_of_lt_of_le ha hB, h⟩)

theorem CallChange.freshChange {f0 : ℕ} {B : WLab G s} {L0 L1 : LiveM G s}
    (h : CallChange f0 B L0 L1) : DB.FreshChange f0 L0 L1 := by
  intro y
  rcases h y with h | h | ⟨i, a, hi, -, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨i, a, hi, h⟩)

variable (G s) in
/-- The invariant of the ACTIVE structure of a call with bound `B` started at fresh id `f0`. -/
structure SInv (ops : DOps G s) (B : WLab G s) (f0 : ℕ) (g : DGl G s) (Dc : DStrM G s) :
    Prop where
  wf : DB.WF g.L Dc
  fr : DB.FreshOK g.fresh Dc
  ids : DB.IdsNodup Dc
  sz : ops.SzOK Dc
  M1 : 1 ≤ Dc.M
  Bd : Dc.Bd = B
  own : ∀ x ∈ DB.allEnts Dc.blocks, f0 ≤ x.id
  f0_le : f0 ≤ g.fresh
  /-- every live entry below `B` lies in the active structure (gives `insert`'s discipline) -/
  low : ∀ v i a, g.L v = some (i, a) → a < B → DB.HasKey g.L Dc v

/-- **Insert simulation.** -/
theorem ins_sim {B : WLab G s} {f0 : ℕ} {g : DGl G s} {Dc : DStrM G s} (h : SInv G s ops B f0 g Dc)
    (hK : DB.KeyInj g.L (kof G s)) {v : Fin G.n} {lam : WLab G s} (hlt : lam < B)
    (hkv : kof G s lam = v) :
    (insC ops T g Dc v lam).1.view (insC ops T g Dc v lam).2.1 = (g.view Dc).insert v lam ∧
    SInv G s ops B f0 (insC ops T g Dc v lam).1 (insC ops T g Dc v lam).2.1 ∧
    DB.KeyInj (insC ops T g Dc v lam).1.L (kof G s) ∧
    g.fresh ≤ (insC ops T g Dc v lam).1.fresh ∧
    (∀ y, y ≠ v → (insC ops T g Dc v lam).1.L y = g.L y) ∧
    ((insC ops T g Dc v lam).1.L v = g.L v ∨ (insC ops T g Dc v lam).1.L v = some (g.fresh, lam)) := by
  have hB : lam < Dc.Bd := h.Bd ▸ hlt
  have hdisc : DB.skipIns g.L v lam = true → DB.HasKey g.L Dc v := by
    unfold DB.skipIns
    cases hL : g.L v with
    | none => simp
    | some pr =>
      obtain ⟨i, old⟩ := pr
      intro hs
      have hold : old ≤ lam := of_decide_eq_true hs
      exact h.low v i old hL (lt_of_le_of_lt hold hlt)
  obtain ⟨hview, hwf, hfr, hmono⟩ := ops.insert_spec T h.wf h.fr hB hdisc
  obtain ⟨hM, hBd⟩ := ops.insert_M T g.L g.fresh Dc v lam
  obtain ⟨hids, hsz, hK'⟩ := ops.insert_aux T h.fr h.ids hK hkv h.sz h.M1
  have hLy : ∀ y, y ≠ v → (ops.insert T g.L g.fresh Dc v lam).1 y = g.L y := by
    intro y hy
    rw [ops.insert_L]
    split_ifs
    · rfl
    · exact Function.update_of_ne hy _ _
  have hview' : ∀ y, DB.view (ops.insert T g.L g.fresh Dc v lam).1
      (ops.insert T g.L g.fresh Dc v lam).2.2.1 y = ((g.view Dc).insert v lam) y := by
    intro y
    rw [hview y]
    unfold DS.insert
    by_cases hy : y = v
    · subst hy
      rw [if_pos rfl, Function.update_self, mergeVal_eq_insVal]
      rfl
    · rw [if_neg hy, Function.update_of_ne hy]
      rfl
  refine ⟨funext hview', ⟨hwf, hfr, hids, hsz, hM ▸ h.M1, hBd.trans h.Bd, ?_, ?_, ?_⟩, hK', hmono,
    hLy, ?_⟩
  · intro x hx
    rcases ops.insert_ents T g.L g.fresh Dc v lam x hx with hx | rfl
    · exact h.own x hx
    · exact h.f0_le
  · exact h.f0_le.trans hmono
  · intro y i a hy ha
    apply view_ne_none_iff.mp
    show DB.view (ops.insert T g.L g.fresh Dc v lam).1 (ops.insert T g.L g.fresh Dc v lam).2.2.1 y ≠ none
    rw [hview' y]
    unfold DS.insert
    by_cases hyv : y = v
    · subst hyv
      rw [Function.update_self, mergeVal_eq_insVal]
      exact Option.some_ne_none _
    · rw [Function.update_of_ne hyv]
      have hLy' : g.L y = some (i, a) := by
        have := hLy y hyv
        show g.L y = some (i, a)
        rw [← this]; exact hy
      exact view_ne_none_iff.mpr (h.low y i a hLy' ha)
  · show (ops.insert T g.L g.fresh Dc v lam).1 v = g.L v ∨
      (ops.insert T g.L g.fresh Dc v lam).1 v = some (g.fresh, lam)
    rw [ops.insert_L]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr (Function.update_self _ _ _)

end basic


section ops

variable {T : ℕ}

theorem insertMany_nil (D : DS G s) (f : Fin G.n → WLab G s) : insertMany G s D ∅ f = D := by
  funext z; simp [insertMany]

/-- **Multi-insert simulation.** -/
theorem insMany_sim {B : WLab G s} {f0 : ℕ} (f : Fin G.n → WLab G s) :
    ∀ (l : List (Fin G.n)) (g : DGl G s) (Dc : DStrM G s), SInv G s ops B f0 g Dc →
      DB.KeyInj g.L (kof G s) → (∀ y ∈ l, f y < B ∧ kof G s (f y) = y) →
      (insManyC ops T f l g Dc).1.view (insManyC ops T f l g Dc).2.1 =
          insertMany G s (g.view Dc) l.toFinset f ∧
        SInv G s ops B f0 (insManyC ops T f l g Dc).1 (insManyC ops T f l g Dc).2.1 ∧
        DB.KeyInj (insManyC ops T f l g Dc).1.L (kof G s) ∧
        g.fresh ≤ (insManyC ops T f l g Dc).1.fresh ∧
        CallChange g.fresh B g.L (insManyC ops T f l g Dc).1.L ∧
        (∀ y, (insManyC ops T f l g Dc).1.L y ≠ g.L y → y ∈ l) := by
  intro l
  induction l with
  | nil =>
    intro g Dc h hK _
    refine ⟨?_, h, hK, le_rfl, CallChange.refl _ _ _, fun y hy => absurd rfl hy⟩
    show g.view Dc = insertMany G s (g.view Dc) ([] : List (Fin G.n)).toFinset f
    rw [List.toFinset_nil, insertMany_nil]
  | cons y l ih =>
    intro g Dc h hK hl
    obtain ⟨hfy, hky⟩ := hl y List.mem_cons_self
    obtain ⟨hv1, h1, hK1, hm1, hfr1, hLv1⟩ := ins_sim (T := T) h hK hfy hky
    obtain ⟨hv, h', hK', hm, hch, htch⟩ :=
      ih (insC ops T g Dc y (f y)).1 (insC ops T g Dc y (f y)).2.1 h1 hK1
        (fun z hz => hl z (List.mem_cons_of_mem _ hz))
    refine ⟨?_, h', hK', hm1.trans hm, ?_, ?_⟩
    · show (insManyC ops T f l (insC ops T g Dc y (f y)).1 (insC ops T g Dc y (f y)).2.1).1.view
        (insManyC ops T f l (insC ops T g Dc y (f y)).1 (insC ops T g Dc y (f y)).2.1).2.1 =
          insertMany G s (g.view Dc) (y :: l).toFinset f
      rw [hv, hv1, insertMany_insert, List.toFinset_cons]
    · have hc1 : CallChange g.fresh B g.L (insC ops T g Dc y (f y)).1.L := by
        intro z
        by_cases hz : z = y
        · subst hz
          rcases hLv1 with h2 | h2
          · exact Or.inl h2
          · exact Or.inr (Or.inr ⟨g.fresh, f z, le_rfl, hfy, h2⟩)
        · exact Or.inl (hfr1 z hz)
      exact hc1.trans (hch.mono hm1 le_rfl)
    · intro z hz
      show z ∈ y :: l
      by_cases h2 : (insManyC ops T f l (insC ops T g Dc y (f y)).1 (insC ops T g Dc y (f y)).2.1).1.L z =
          (insC ops T g Dc y (f y)).1.L z
      · have : (insC ops T g Dc y (f y)).1.L z ≠ g.L z := by
          intro h3; exact hz (h2.trans h3)
        by_cases hzy : z = y
        · rw [hzy]; exact List.mem_cons_self
        · exact absurd (hfr1 z hzy) this
      · exact List.mem_cons_of_mem _ (htch z h2)

theorem insert_view_mono (D : DS G s) (v : Fin G.n) (lam : WLab G s) {y : Fin G.n}
    {a : WLab G s} (h : D y = some a) : ∃ a', (D.insert v lam) y = some a' ∧ a' ≤ a := by
  unfold DS.insert
  by_cases hy : y = v
  · subst hy; rw [Function.update_self]; exact DSx.mergeVal_le_left h
  · rw [Function.update_of_ne hy]; exact ⟨a, h, le_rfl⟩

/-- **One relaxation, simulated.** -/
theorem relax_sim {B : WLab G s} {f0 : ℕ} (lo : Option (WLab G s)) (st : RSt G s) (e : Fin G.m)
    (h : SInv G s ops B f0 st.g st.Dc) (hK : DB.KeyInj st.g.L (kof G s)) (hw : WalkInv st.d) :
    (relaxInsCc ops T B lo st e).d = (relaxIns G s B lo (st.d, st.g.view st.Dc) e).1 ∧
    (relaxInsCc ops T B lo st e).g.view (relaxInsCc ops T B lo st e).Dc =
      (relaxIns G s B lo (st.d, st.g.view st.Dc) e).2 ∧
    SInv G s ops B f0 (relaxInsCc ops T B lo st e).g (relaxInsCc ops T B lo st e).Dc ∧
    DB.KeyInj (relaxInsCc ops T B lo st e).g.L (kof G s) ∧
    st.g.fresh ≤ (relaxInsCc ops T B lo st e).g.fresh ∧
    CallChange st.g.fresh B st.g.L (relaxInsCc ops T B lo st e).g.L ∧
    (∀ y, (relaxInsCc ops T B lo st e).g.L y ≠ st.g.L y →
      ∃ a, (relaxInsCc ops T B lo st e).g.view (relaxInsCc ops T B lo st e).Dc y = some a ∧
        a ≤ st.d y) := by
  classical
  by_cases hv : ValidRelax G s st.d B e
  · have hlt : ext (st.d (G.src e)) e < B := hv.2
    have hne : ext (st.d (G.src e)) e ≠ ⊤ := ne_top_of_lt hlt
    have hkv := kof_ext hw hne
    obtain ⟨hv1, h1, hK1, hm1, hfr1, hLv1⟩ :=
      ins_sim (T := T) h hK hlt hkv
    -- the inserting branch
    have hins : ∀ (r : RSt G s), r = ⟨Function.update st.d (G.dst e) (ext (st.d (G.src e)) e),
          (insC ops T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).1,
          (insC ops T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).2.1,
          st.c + 1 + (insC ops T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).2.2⟩ →
        r.g.view r.Dc = (st.g.view st.Dc).insert (G.dst e) (ext (st.d (G.src e)) e) ∧
        SInv G s ops B f0 r.g r.Dc ∧ DB.KeyInj r.g.L (kof G s) ∧ st.g.fresh ≤ r.g.fresh ∧
        CallChange st.g.fresh B st.g.L r.g.L ∧
        (∀ y, r.g.L y ≠ st.g.L y → ∃ a, r.g.view r.Dc y = some a ∧ a ≤ st.d y) := by
      rintro r rfl
      refine ⟨hv1, h1, hK1, hm1, ?_, ?_⟩
      · intro z
        by_cases hz : z = G.dst e
        · subst hz
          rcases hLv1 with h2 | h2
          · exact Or.inl h2
          · exact Or.inr (Or.inr ⟨st.g.fresh, _, le_rfl, hlt, h2⟩)
        · exact Or.inl (hfr1 z hz)
      · intro y hy
        have hyv : y = G.dst e := by
          by_contra hne'; exact hy (hfr1 y hne')
        subst hyv
        show ∃ a, (insC ops T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).1.view
          (insC ops T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).2.1 (G.dst e) = some a ∧
            a ≤ st.d (G.dst e)
        rw [hv1]
        unfold DS.insert
        rw [Function.update_self]
        rcases hD : st.g.view st.Dc (G.dst e) with _ | a0
        · exact ⟨_, rfl, hv.1⟩
        · exact ⟨min a0 (ext (st.d (G.src e)) e), rfl, (min_le_right _ _).trans hv.1⟩
    cases lo with
    | none =>
      have hr : relaxInsCc ops T B none st e =
          ⟨Function.update st.d (G.dst e) (ext (st.d (G.src e)) e),
            (insC ops T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).1,
            (insC ops T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).2.1,
            st.c + 1 + (insC ops T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).2.2⟩ := by
        unfold relaxInsCc; rw [if_pos hv]
      have hl : relaxIns G s B none (st.d, st.g.view st.Dc) e =
          (Function.update st.d (G.dst e) (ext (st.d (G.src e)) e),
            (st.g.view st.Dc).insert (G.dst e) (ext (st.d (G.src e)) e)) := by
        unfold relaxIns; rw [if_pos hv]
      rw [hr, hl]
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hins _ rfl
      exact ⟨rfl, a1, a2, a3, a4, a5, a6⟩
    | some b =>
      by_cases hb : b ≤ ext (st.d (G.src e)) e
      · have hr : relaxInsCc ops T B (some b) st e =
            ⟨Function.update st.d (G.dst e) (ext (st.d (G.src e)) e),
              (insC ops T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).1,
              (insC ops T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).2.1,
              st.c + 1 + (insC ops T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).2.2⟩ := by
          unfold relaxInsCc; rw [if_pos hv]; simp only; rw [if_pos hb]
        have hl : relaxIns G s B (some b) (st.d, st.g.view st.Dc) e =
            (Function.update st.d (G.dst e) (ext (st.d (G.src e)) e),
              (st.g.view st.Dc).insert (G.dst e) (ext (st.d (G.src e)) e)) := by
          unfold relaxIns; rw [if_pos hv]; simp only; rw [if_pos hb]
        rw [hr, hl]
        obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hins _ rfl
        exact ⟨rfl, a1, a2, a3, a4, a5, a6⟩
      · have hr : relaxInsCc ops T B (some b) st e =
            ⟨Function.update st.d (G.dst e) (ext (st.d (G.src e)) e), st.g, st.Dc, st.c + 1⟩ := by
          unfold relaxInsCc; rw [if_pos hv]; simp only; rw [if_neg hb]
        have hl : relaxIns G s B (some b) (st.d, st.g.view st.Dc) e =
            (Function.update st.d (G.dst e) (ext (st.d (G.src e)) e), st.g.view st.Dc) := by
          unfold relaxIns; rw [if_pos hv]; simp only; rw [if_neg hb]
        rw [hr, hl]
        exact ⟨rfl, rfl, h, hK, le_rfl, CallChange.refl _ _ _, fun y hy => absurd rfl hy⟩
  · have hr : relaxInsCc ops T B lo st e = ⟨st.d, st.g, st.Dc, st.c + 1⟩ := by
      unfold relaxInsCc; rw [if_neg hv]
    have hl : relaxIns G s B lo (st.d, st.g.view st.Dc) e = (st.d, st.g.view st.Dc) := by
      unfold relaxIns; rw [if_neg hv]
    rw [hr, hl]
    exact ⟨rfl, rfl, h, hK, le_rfl, CallChange.refl _ _ _, fun y hy => absurd rfl hy⟩

/-- **A relaxation scan, simulated.** -/
theorem fold_sim {B : WLab G s} {f0 : ℕ} (lo : Option (WLab G s)) :
    ∀ (L : List (Fin G.m)) (st : RSt G s), SInv G s ops B f0 st.g st.Dc →
      DB.KeyInj st.g.L (kof G s) → WalkInv st.d →
      (L.foldl (relaxInsCc ops T B lo) st).d = (L.foldl (relaxIns G s B lo) (st.d, st.g.view st.Dc)).1 ∧
      (L.foldl (relaxInsCc ops T B lo) st).g.view (L.foldl (relaxInsCc ops T B lo) st).Dc =
        (L.foldl (relaxIns G s B lo) (st.d, st.g.view st.Dc)).2 ∧
      SInv G s ops B f0 (L.foldl (relaxInsCc ops T B lo) st).g (L.foldl (relaxInsCc ops T B lo) st).Dc ∧
      DB.KeyInj (L.foldl (relaxInsCc ops T B lo) st).g.L (kof G s) ∧
      st.g.fresh ≤ (L.foldl (relaxInsCc ops T B lo) st).g.fresh ∧
      CallChange st.g.fresh B st.g.L (L.foldl (relaxInsCc ops T B lo) st).g.L ∧
      (∀ y, (L.foldl (relaxInsCc ops T B lo) st).g.L y ≠ st.g.L y →
        ∃ a, (L.foldl (relaxInsCc ops T B lo) st).g.view (L.foldl (relaxInsCc ops T B lo) st).Dc y =
          some a ∧ a ≤ st.d y) := by
  intro L
  induction L with
  | nil =>
    intro st h hK _
    exact ⟨rfl, rfl, h, hK, le_rfl, CallChange.refl _ _ _, fun y hy => absurd rfl hy⟩
  | cons e L ih =>
    intro st h hK hw
    rw [List.foldl_cons, List.foldl_cons]
    obtain ⟨e1, e2, h1, hK1, hm1, hc1, ht1⟩ := relax_sim (T := T) lo st e h hK hw
    have hw1 : WalkInv (relaxInsCc ops T B lo st e).d := by
      rw [e1]; exact relaxIns_walk B lo _ e hw
    obtain ⟨f1, f2, h2, hK2, hm2, hc2, ht2⟩ := ih (relaxInsCc ops T B lo st e) h1 hK1 hw1
    have hst : ((relaxInsCc ops T B lo st e).d, (relaxInsCc ops T B lo st e).g.view
        (relaxInsCc ops T B lo st e).Dc) = relaxIns G s B lo (st.d, st.g.view st.Dc) e := by
      rw [e1, e2]
    rw [hst] at f1 f2
    refine ⟨f1, f2, h2, hK2, hm1.trans hm2, hc1.trans (hc2.mono hm1 le_rfl), ?_⟩
    intro y hy
    by_cases h3 : (L.foldl (relaxInsCc ops T B lo) (relaxInsCc ops T B lo st e)).g.L y =
        (relaxInsCc ops T B lo st e).g.L y
    · have h4 : (relaxInsCc ops T B lo st e).g.L y ≠ st.g.L y := fun h5 => hy (h3.trans h5)
      obtain ⟨a, ha, hale⟩ := ht1 y h4
      rw [e2] at ha
      obtain ⟨a', ha', hle'⟩ := foldl_relaxIns_snd_le B lo L _ y a ha
      rw [← f2] at ha'
      exact ⟨a', ha', hle'.trans hale⟩
    · obtain ⟨a, ha, hale⟩ := ht2 y h3
      refine ⟨a, ha, hale.trans ?_⟩
      rw [e1]; exact relaxIns_fst_le B lo _ e y

end ops


section ops2

variable {T : ℕ}

/-- Entries of a structure with ids below `f0` that are live after a fresh change were live before. -/
theorem isLive_of_freshChange {f0 : ℕ} {L0 L1 : LiveM G s} (hch : DB.FreshChange f0 L0 L1)
    {x : DB.Entry (Fin G.n) (WLab G s)} (hx : x.id < f0) (hl : x.IsLive L1) : x.IsLive L0 := by
  unfold DB.Entry.IsLive at hl ⊢
  rcases hch x.key with h | h | ⟨i, a, hi, h⟩
  · rw [← h]; exact hl
  · rw [h] at hl; exact absurd hl (by simp)
  · rw [h] at hl
    simp only [Option.some.injEq, Prod.mk.injEq] at hl
    omega

theorem wf_of_freshChange {f0 : ℕ} {L0 L1 : LiveM G s} {D : DStrM G s} (hwf : DB.WF L0 D)
    (hfr : DB.FreshOK f0 D) (hch : DB.FreshChange f0 L0 L1) : DB.WF L1 D := by
  refine ⟨hwf.1, DB.IntervalOK.mono' ?_ hwf.2⟩
  intro b hb e he hl
  exact isLive_of_freshChange hch (hfr e (DB.mem_allEnts.mpr ⟨b, hb, he⟩)) hl

theorem freshOK_mono {f f' : ℕ} {D : DStrM G s} (h : DB.FreshOK f D) (hf : f ≤ f') :
    DB.FreshOK f' D := fun x hx => lt_of_lt_of_le (h x hx) hf

/-- **Pull simulation.** -/
theorem pull_sim {B : WLab G s} {f0 : ℕ} {g : DGl G s} {Dc : DStrM G s} (h : SInv G s ops B f0 g Dc)
    (hK : DB.KeyInj g.L (kof G s)) {ks : List (Fin G.n)} {x : WLab G s} {g1 : DGl G s}
    {Dc1 : DStrM G s} {cp : ℕ} (hp : pullC ops T g Dc = (ks, x, g1, Dc1, cp)) :
    PullSpec (g.view Dc) B ks.toFinset x (g1.view Dc1) ∧
    ks.toFinset.card ≤ Dc.M ∧
    SInv G s ops B f0 g1 Dc1 ∧
    DB.KeyInj g1.L (kof G s) ∧
    g1.fresh = g.fresh ∧
    g1.L = DB.clearKeys g.L ks ∧
    (∀ e ∈ DB.liveVals g1.L Dc1.blocks, x ≤ e.val) ∧
    (∀ b ∈ Dc1.blocks.tail, (x : WithBot (WLab G s)) < b.sep) ∧
    (∀ v i a, g1.L v = some (i, a) → x ≤ a) ∧
    Dc1.M = Dc.M := by
  simp only [pullC, Prod.mk.injEq] at hp
  obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hp
  obtain ⟨hmem, hrest, hbound, hwf1, hL1, hM1, hBd1⟩ := ops.pull_spec T h.wf
  obtain ⟨hlen, -, hne, hge, hsep⟩ := ops.pull_post T h.wf hK h.ids h.M1
  obtain ⟨hids1, hsz1, hfr1, hK1⟩ := ops.pull_aux T h.wf hK h.ids h.M1 h.sz h.fr
  have hview1 : ∀ y, DB.view (ops.pull T g.L Dc).2.2.1 (ops.pull T g.L Dc).2.2.2.1 y =
      if y ∈ (ops.pull T g.L Dc).1 then none else DB.view g.L Dc y := hrest
  refine ⟨⟨?_, ?_, ?_, ?_⟩, (List.toFinset_card_le _).trans hlen, ⟨hwf1, hfr1, hids1, hsz1, ?_, ?_,
    ?_, h.f0_le, ?_⟩, hK1, rfl, hL1, hge, hsep, ?_, hM1⟩
  · intro y; rw [List.mem_toFinset]; exact hmem y
  · intro y
    show DB.view (ops.pull T g.L Dc).2.2.1 (ops.pull T g.L Dc).2.2.2.1 y = _
    rw [hview1 y]
    simp only [List.mem_toFinset]
    rfl
  · exact h.Bd ▸ hbound
  · intro ⟨y, hy⟩
    have hk : DB.HasKey g.L Dc y := view_ne_none_iff.mp hy
    obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil _ (hne ⟨y, hk⟩)
    exact ⟨z, List.mem_toFinset.mpr hz⟩
  · rw [hM1]; exact h.M1
  · rw [hBd1]; exact h.Bd
  · intro e he
    exact h.own e (ops.pull_ents T g.L Dc e he)
  · intro v i a hv ha
    show DB.HasKey (ops.pull T g.L Dc).2.2.1 (ops.pull T g.L Dc).2.2.2.1 v
    have hvL : g.L v = some (i, a) ∧ v ∉ (ops.pull T g.L Dc).1 := by
      have hv' : (ops.pull T g.L Dc).2.2.1 v = some (i, a) := hv
      rw [hL1] at hv'
      unfold DB.clearKeys at hv'
      split_ifs at hv' with hvk
      exact ⟨hv', hvk⟩
    have hk := h.low v i a hvL.1 ha
    apply view_ne_none_iff.mp
    rw [hview1 v, if_neg hvL.2]
    exact view_ne_none_iff.mpr hk
  · intro v i a hv
    by_contra hlt
    push Not at hlt
    have hv' : (ops.pull T g.L Dc).2.2.1 v = some (i, a) := hv
    have hvL : g.L v = some (i, a) ∧ v ∉ (ops.pull T g.L Dc).1 := by
      rw [hL1] at hv'
      unfold DB.clearKeys at hv'
      split_ifs at hv' with hvk
      exact ⟨hv', hvk⟩
    have hk := h.low v i a hvL.1 (lt_of_lt_of_le hlt (h.Bd ▸ hbound))
    -- `v` has view value `a < x`, so it was pulled
    have hva : DB.view g.L Dc v = some a := by
      unfold DB.view; rw [if_pos hk, hvL.1]; rfl
    exact hvL.2 ((hmem v).mpr ⟨a, hva, hlt⟩)

/-- **Delete simulation.** -/
theorem del_sim {B : WLab G s} {f0 : ℕ} {g : DGl G s} {Dc : DStrM G s} (h : SInv G s ops B f0 g Dc)
    (hK : DB.KeyInj g.L (kof G s)) (ks : List (Fin G.n)) :
    (delC g ks).1.view Dc = (g.view Dc).deleteSet ks.toFinset ∧
    SInv G s ops B f0 (delC g ks).1 Dc ∧ DB.KeyInj (delC g ks).1.L (kof G s) ∧
    (delC g ks).1.fresh = g.fresh ∧ (delC g ks).1.L = DB.clearKeys g.L ks := by
  obtain ⟨hview, hwf⟩ := DB.deleteKeys_spec (L := g.L) (ks := ks) h.wf
  have hview' : ∀ y, (delC g ks).1.view Dc y = (g.view Dc).deleteSet ks.toFinset y := by
    intro y
    show DB.view (DB.deleteKeys g.L ks).1 Dc y = _
    rw [hview y]
    simp only [DS.deleteSet, List.mem_toFinset]
    rfl
  refine ⟨funext hview', ⟨hwf, h.fr, h.ids, h.sz, h.M1, h.Bd, h.own, h.f0_le, ?_⟩,
    DB.keyInj_clearKeys hK, rfl, rfl⟩
  intro v i a hv ha
  have hv' : DB.clearKeys g.L ks v = some (i, a) := hv
  unfold DB.clearKeys at hv'
  split_ifs at hv' with hvk
  have hk := h.low v i a hv' ha
  apply view_ne_none_iff.mp
  show DB.view (DB.deleteKeys g.L ks).1 Dc v ≠ none
  rw [hview v, if_neg hvk]
  exact view_ne_none_iff.mpr hk

/-- **New structure.** -/
theorem new_sim {B : WLab G s} {g : DGl G s} {M : ℕ} (hM : 1 ≤ M)
    (hab : ∀ v i a, g.L v = some (i, a) → B ≤ a) :
    SInv G s ops B g.fresh g (newC M B) ∧ g.view (newC M B) = DS.empty := by
  have hnokey : ∀ v, ¬ DB.HasKey g.L (newC M B) v := by
    rintro v ⟨e, he, -⟩
    simp [newC, DB.liveVals, DB.liveOf] at he
  refine ⟨⟨⟨by simp [newC], ?_⟩, ?_, ?_, ?_, hM, rfl, ?_, le_rfl, ?_⟩, ?_⟩
  · show DB.IntervalOK g.L [⟨⊥, []⟩] ⊥ ((B : WLab G s) : WithBot (WLab G s))
    exact ⟨rfl, WithBot.bot_lt_coe _, fun e he => absurd he (by simp)⟩
  · intro x hx; simp [newC, DB.allEnts] at hx
  · simp [DB.IdsNodup, newC, DB.allEnts]
  · exact ops.sz_new M B
  · intro x hx; simp [newC, DB.allEnts] at hx
  · intro v i a hv ha
    exact absurd (hab v i a hv) (not_le.mpr ha)
  · funext v
    show DB.view g.L (newC M B) v = none
    exact DB.view_eq_none.mpr (hnokey v)

end ops2



/-- `DB.lazy_merge_eq_literal` for an arbitrary merged structure `Dm` given by its view equation
(agent-04's proof, with `(merge T D D').1` abstracted). -/
theorem lazy_merge_gen {f₀ : ℕ} {L₀ L₁ : LiveM G s} {D D' Dm : DStrM G s} {Z : List (Fin G.n)}
    {V₀ W' : Fin G.n → Option (WLab G s)} (hfr : DB.FreshOK f₀ D) (hch : DB.FreshChange f₀ L₀ L₁)
    (hV₀ : ∀ y, DB.view L₀ D y = V₀ y) (hW' : ∀ y, DB.view L₁ D' y = W' y)
    (hmerge : ∀ y, DB.view L₁ Dm y =
      if DB.HasKey L₁ D' y then DB.view L₁ D' y else DB.view L₁ D y)
    (htouch : ∀ y, L₁ y ≠ L₀ y → y ∉ Z →
      ∃ a, W' y = some a ∧ ∀ b, V₀ y = some b → a ≤ b)
    (y : Fin G.n) (hy : y ∉ Z) :
    DB.view L₁ Dm y =
      match V₀ y, W' y with
      | none, w => w
      | v, none => v
      | some a, some b => some (min a b) := by
  rw [hmerge y]
  have hDy := DB.view_of_freshChange hfr hch y
  by_cases hk : DB.HasKey L₁ D' y
  · rw [ite_eq_left hk, hW']
    by_cases ht : L₁ y = L₀ y
    · rcases hW : W' y with _ | b
      · exfalso
        exact (DB.view_eq_none.mp (by rw [hW', hW])) hk
      · rcases hV : V₀ y with _ | a
        · rfl
        · have h1 : DB.view L₁ D y = some a := by rw [hDy, if_pos ht, hV₀, hV]
          have h2 : DB.view L₁ D' y = some b := by rw [hW', hW]
          have ha := DB.view_eq_some.mp h1
          have hb := DB.view_eq_some.mp h2
          obtain ⟨e, he, hek, hev⟩ := ha
          obtain ⟨e', he', hek', hev'⟩ := hb
          have := (DB.live_key_unique (DB.mem_liveVals.mp he).2 (DB.mem_liveVals.mp he').2
            (hek.trans hek'.symm)).2
          rw [← hev, ← hev', this]; simp
    · obtain ⟨a, ha, hle⟩ := htouch y ht hy
      rw [ha]
      rcases hV : V₀ y with _ | b
      · rfl
      · simp [min_eq_right (hle b hV)]
  · rw [ite_eq_right hk]
    have hW : W' y = none := by rw [← hW']; exact DB.view_eq_none.mpr hk
    rw [hW, hDy]
    by_cases ht : L₁ y = L₀ y
    · rw [if_pos ht, hV₀]
      rcases V₀ y <;> rfl
    · exfalso
      obtain ⟨a, ha, _⟩ := htouch y ht hy
      rw [hW] at ha; simp at ha

section mergesim

variable {T : ℕ}

/-- **Merge + FIX-STALE simulation (tracker O6).**  After a child call on `[·, B_i)` that started
from the parent's post-pull state `(g1, Dc1)` and ended in `(g2, Dci)`, merging `Dci` into `Dc1`
and deleting the list `lUi` gives exactly the literal `(D1.merge Di).deleteSet Ui`, provided the
child's touched keys are settled (`∈ lUi`) or kept in `Dci` with a value at most the parent's
(`htouch`, the L4 fact TOUCH). -/
theorem merge_sim {B Bi : WLab G s} {f0 : ℕ} {g1 g2 : DGl G s} {Dc1 Dci : DStrM G s}
    (h1 : SInv G s ops B f0 g1 Dc1)
    (hlive1 : ∀ e ∈ DB.liveVals g1.L Dc1.blocks, Bi ≤ e.val)
    (hsep1 : ∀ b ∈ Dc1.blocks.tail, ((Bi : WLab G s) : WithBot (WLab G s)) < b.sep)
    (hBi : Bi ≤ B)
    (hi : SInv G s ops Bi g1.fresh g2 Dci) (hK2 : DB.KeyInj g2.L (kof G s))
    (hch : CallChange g1.fresh Bi g1.L g2.L)
    (hMM : ops.mergeM Dc1.M Dci.M)
    (lUi : List (Fin G.n))
    (htouch : ∀ y, g2.L y ≠ g1.L y → y ∉ lUi →
      ∃ a, g2.view Dci y = some a ∧ ∀ b, g1.view Dc1 y = some b → a ≤ b) :
    (delC g2 lUi).1.view (ops.merge T Dc1 Dci).1 =
        ((g1.view Dc1).merge (g2.view Dci)).deleteSet lUi.toFinset ∧
      SInv G s ops B f0 (delC g2 lUi).1 (ops.merge T Dc1 Dci).1 ∧
      DB.KeyInj (delC g2 lUi).1.L (kof G s) ∧
      (delC g2 lUi).1.fresh = g2.fresh ∧ (delC g2 lUi).1.L = DB.clearKeys g2.L lUi := by
  have hfc : DB.FreshChange g1.fresh g1.L g2.L := hch.freshChange
  have hwf12 : DB.WF g2.L Dc1 := wf_of_freshChange h1.wf h1.fr hfc
  have hMP1 : ∀ e ∈ DB.liveVals g2.L Dc1.blocks, Dci.Bd ≤ e.val := by
    intro e he
    rw [hi.Bd]
    obtain ⟨⟨b, hb, heb⟩, hl⟩ := DB.mem_liveVals.mp he
    have hid : e.id < g1.fresh := h1.fr e (DB.mem_allEnts.mpr ⟨b, hb, heb⟩)
    exact hlive1 e (DB.mem_liveVals.mpr ⟨⟨b, hb, heb⟩, isLive_of_freshChange hfc hid hl⟩)
  have hMP2 : ∀ b ∈ Dc1.blocks.tail, ((Dci.Bd : WLab G s) : WithBot (WLab G s)) < b.sep := by
    rw [hi.Bd]; exact hsep1
  have hMP0 : Dci.Bd ≤ Dc1.Bd := by rw [hi.Bd, h1.Bd]; exact hBi
  obtain ⟨hhas, hview, hwfm⟩ := ops.merge_spec T hwf12 hi.wf hMP1 hMP2 hMP0
  obtain ⟨hMm, hBdm⟩ := ops.merge_M T Dc1 Dci
  obtain ⟨hdv, hwfd⟩ := DB.deleteKeys_spec (L := g2.L) (ks := lUi) hwfm
  have hdisj : ∀ x ∈ DB.allEnts Dc1.blocks, ∀ y ∈ DB.allEnts Dci.blocks, x.id ≠ y.id := by
    intro x hx y hy
    have h1' := h1.fr x hx
    have h2' := hi.own y hy
    omega
  obtain ⟨hidsm, hszm, hfrm⟩ := ops.merge_aux T hwf12.1 h1.ids hi.ids hdisj h1.sz hi.sz hMM
    (freshOK_mono h1.fr hi.f0_le) hi.fr
  have hviewd : ∀ y, (delC g2 lUi).1.view (ops.merge T Dc1 Dci).1 y =
      ((g1.view Dc1).merge (g2.view Dci)).deleteSet lUi.toFinset y := by
    intro y
    show DB.view (DB.deleteKeys g2.L lUi).1 (ops.merge T Dc1 Dci).1 y = _
    rw [hdv y]
    simp only [DS.deleteSet, List.mem_toFinset]
    split_ifs with hy
    · rfl
    · have hl := lazy_merge_gen (Dm := (ops.merge T Dc1 Dci).1) (V₀ := fun y => DB.view g1.L Dc1 y)
        (W' := fun y => DB.view g2.L Dci y) h1.fr hfc (fun y => rfl) (fun y => rfl) hview
        htouch y hy
      rw [hl]
      show _ = DS.mergeVal (DB.view g1.L Dc1 y) (DB.view g2.L Dci y)
      rcases DB.view g1.L Dc1 y with _ | a <;> rcases DB.view g2.L Dci y with _ | b <;> rfl
  have hlow' : ∀ v i a, (delC g2 lUi).1.L v = some (i, a) → a < B →
      DB.HasKey (delC g2 lUi).1.L (ops.merge T Dc1 Dci).1 v := by
    intro v i a hv ha
    have hv' : DB.clearKeys g2.L lUi v = some (i, a) := hv
    unfold DB.clearKeys at hv'
    split_ifs at hv' with hvk
    have hk2 : DB.HasKey g2.L (ops.merge T Dc1 Dci).1 v := by
      rw [hhas]
      by_cases hab : a < Bi
      · exact Or.inl (hi.low v i a hv' hab)
      · right
        have hL12 : g2.L v = g1.L v := by
          rcases hch v with h | h | ⟨i', a', -, ha', h⟩
          · exact h
          · rw [hv'] at h; exact absurd h (by simp)
          · rw [hv'] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            exact absurd ha' hab
        have hk1 := h1.low v i a (hL12 ▸ hv') ha
        obtain ⟨e, he, hek⟩ := hk1
        obtain ⟨hm, hl⟩ := DB.mem_liveVals.mp he
        refine ⟨e, DB.mem_liveVals.mpr ⟨hm, ?_⟩, hek⟩
        unfold DB.Entry.IsLive at hl ⊢
        rw [hek, hL12, ← hek]; exact hl
    apply view_ne_none_iff.mp
    show DB.view (DB.deleteKeys g2.L lUi).1 (ops.merge T Dc1 Dci).1 v ≠ none
    rw [hdv v, if_neg hvk]
    exact view_ne_none_iff.mpr hk2
  refine ⟨funext hviewd, ⟨hwfd, hfrm, hidsm, hszm, hMm ▸ h1.M1, hBdm.trans h1.Bd, ?_,
    h1.f0_le.trans hi.f0_le, hlow'⟩, DB.keyInj_clearKeys hK2, rfl, rfl⟩
  intro x hx
  rcases ops.merge_ents T Dc1 Dci x hx with hx | hx
  · exact h1.own x hx
  · exact h1.f0_le.trans (hi.own x hx)

end mergesim


section helpers

variable {T : ℕ}

theorem insC_M (g : DGl G s) (Dc : DStrM G s) (v : Fin G.n) (lam : WLab G s) :
    (insC ops T g Dc v lam).2.1.M = Dc.M := by
  exact (ops.insert_M T g.L g.fresh Dc v lam).1

theorem insC_Bd (g : DGl G s) (Dc : DStrM G s) (v : Fin G.n) (lam : WLab G s) :
    (insC ops T g Dc v lam).2.1.Bd = Dc.Bd := by
  exact (ops.insert_M T g.L g.fresh Dc v lam).2

theorem insManyC_M (f : Fin G.n → WLab G s) :
    ∀ (l : List (Fin G.n)) (g : DGl G s) (Dc : DStrM G s), (insManyC ops T f l g Dc).2.1.M = Dc.M
  | [], _, _ => rfl
  | y :: l, g, Dc => by
    show (insManyC ops T f l (insC ops T g Dc y (f y)).1 (insC ops T g Dc y (f y)).2.1).2.1.M = Dc.M
    rw [insManyC_M f l, insC_M]

theorem relaxInsCc_M (B : WLab G s) (lo : Option (WLab G s)) (st : RSt G s) (e : Fin G.m) :
    (relaxInsCc ops T B lo st e).Dc.M = st.Dc.M := by
  unfold relaxInsCc
  split_ifs with hv
  · cases lo with
    | none => exact insC_M _ _ _ _
    | some b =>
      simp only
      split_ifs
      · exact insC_M _ _ _ _
      · rfl
  · rfl

theorem fold_M (B : WLab G s) (lo : Option (WLab G s)) :
    ∀ (L : List (Fin G.m)) (st : RSt G s), (L.foldl (relaxInsCc ops T B lo) st).Dc.M = st.Dc.M
  | [], _ => rfl
  | e :: L, st => by rw [List.foldl_cons, fold_M B lo L, relaxInsCc_M]

theorem callChange_clearKeys (f0 : ℕ) (B : WLab G s) (L : LiveM G s) (ks : List (Fin G.n)) :
    CallChange f0 B L (DB.clearKeys L ks) := by
  intro y
  unfold DB.clearKeys
  split_ifs
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl

/-- Records without their cost fields. -/
def CallRec.strip {Ω : Type} (r : CallRec G s Ω) : CallRec G s Ω := { r with cMerge := 0, cost := 0 }

/-- A log without cost fields. -/
def Log.strip {Ω : Type} (lg : Log G s Ω) : Log G s Ω := lg.map fun x => (x.1, x.2.strip)

theorem Log.strip_append {Ω : Type} (l1 l2 : Log G s Ω) :
    Log.strip (l1 ++ l2) = Log.strip l1 ++ Log.strip l2 := by
  unfold Log.strip; rw [List.map_append]

theorem Log.strip_shift {Ω : Type} (i : ℕ) (lg : Log G s Ω) :
    Log.strip (Log.shift i lg) = Log.shift i (Log.strip lg) := by
  unfold Log.strip Log.shift; rw [List.map_map, List.map_map]; rfl

theorem Log.strip_cons {Ω : Type} (x : List ℕ × CallRec G s Ω) (lg : Log G s Ω) :
    Log.strip (x :: lg) = (x.1, x.2.strip) :: Log.strip lg := rfl

end helpers

section nextmono

variable {p : ℕ}

/-- Through one literal iteration, a key of the post-pull store not in `U_i` keeps a value at most
its value. -/
theorem nextState_D_le_left (B : WLab G s) (σ : LState G s p) (Bi B'i : WLab G s)
    (Ui : Finset (Fin G.n)) (D1 Di : DS G s) (d1 : Labels G s) (L : List (Fin G.m))
    (piv' : Fin p → Fin G.n) {y : Fin G.n} (hy : y ∉ Ui) {a : WLab G s} (ha : D1 y = some a) :
    ∃ a', (nextState B σ Bi B'i Ui D1 Di d1 L piv').D y = some a' ∧ a' ≤ a := by
  have h0 : ∃ a0, ((D1.merge Di).deleteSet Ui) y = some a0 ∧ a0 ≤ a := by
    rw [deleteSet_apply, if_neg hy, merge_apply]
    exact DSx.mergeVal_le_left ha
  obtain ⟨a0, h0, hle0⟩ := h0
  obtain ⟨a1, h1, hle1⟩ := foldl_relaxIns_snd_le B (some Bi) L (d1, (D1.merge Di).deleteSet Ui) y a0 h0
  obtain ⟨a2, h2, hle2⟩ := insertMany_le (D := (L.foldl (relaxIns G s B (some Bi))
    (d1, (D1.merge Di).deleteSet Ui)).2) (reselected σ Ui piv')
    (L.foldl (relaxIns G s B (some Bi)) (d1, (D1.merge Di).deleteSet Ui)).1 h1
  exact ⟨a2, h2, hle2.trans (hle1.trans hle0)⟩

theorem nextState_D_le_right (B : WLab G s) (σ : LState G s p) (Bi B'i : WLab G s)
    (Ui : Finset (Fin G.n)) (D1 Di : DS G s) (d1 : Labels G s) (L : List (Fin G.m))
    (piv' : Fin p → Fin G.n) {y : Fin G.n} (hy : y ∉ Ui) {a : WLab G s} (ha : Di y = some a) :
    ∃ a', (nextState B σ Bi B'i Ui D1 Di d1 L piv').D y = some a' ∧ a' ≤ a := by
  have h0 : ∃ a0, ((D1.merge Di).deleteSet Ui) y = some a0 ∧ a0 ≤ a := by
    rw [deleteSet_apply, if_neg hy, merge_apply]
    exact DSx.mergeVal_le_right ha
  obtain ⟨a0, h0, hle0⟩ := h0
  obtain ⟨a1, h1, hle1⟩ := foldl_relaxIns_snd_le B (some Bi) L (d1, (D1.merge Di).deleteSet Ui) y a0 h0
  obtain ⟨a2, h2, hle2⟩ := insertMany_le (D := (L.foldl (relaxIns G s B (some Bi))
    (d1, (D1.merge Di).deleteSet Ui)).2) (reselected σ Ui piv')
    (L.foldl (relaxIns G s B (some Bi)) (d1, (D1.merge Di).deleteSet Ui)).1 h1
  exact ⟨a2, h2, hle2.trans (hle1.trans hle0)⟩

end nextmono


/-- The number of entries of a structure. -/
def entCount (Dc : DStrM G s) : ℕ := (DB.allEnts Dc.blocks).length

section counting

theorem ents_nodup {Dc : DStrM G s} (h : DB.IdsNodup Dc) : (DB.allEnts Dc.blocks).Nodup :=
  List.Nodup.of_map _ h

theorem len_le_of_sub_one {l1 l2 : List (DB.Entry (Fin G.n) (WLab G s))}
    {e : DB.Entry (Fin G.n) (WLab G s)} (h1 : l1.Nodup) (h : ∀ x ∈ l1, x ∈ l2 ∨ x = e) :
    l1.length ≤ l2.length + 1 := by
  classical
  rw [← List.toFinset_card_of_nodup h1]
  calc l1.toFinset.card ≤ (insert e l2.toFinset).card := by
        apply Finset.card_le_card
        intro x hx
        rcases h x (List.mem_toFinset.mp hx) with h' | h'
        · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr h')
        · rw [h']; exact Finset.mem_insert_self _ _
    _ ≤ l2.toFinset.card + 1 := Finset.card_insert_le _ _
    _ ≤ l2.length + 1 := by have := List.toFinset_card_le l2; omega

theorem len_le_of_sub {l1 l2 : List (DB.Entry (Fin G.n) (WLab G s))} (h1 : l1.Nodup)
    (h : ∀ x ∈ l1, x ∈ l2) : l1.length ≤ l2.length := by
  classical
  rw [← List.toFinset_card_of_nodup h1]
  calc l1.toFinset.card ≤ l2.toFinset.card :=
        Finset.card_le_card (fun x hx => List.mem_toFinset.mpr (h x (List.mem_toFinset.mp hx)))
    _ ≤ l2.length := List.toFinset_card_le l2

theorem len_le_of_sub_union {l l1 l2 : List (DB.Entry (Fin G.n) (WLab G s))} (h1 : l.Nodup)
    (h : ∀ x ∈ l, x ∈ l1 ∨ x ∈ l2) : l.length ≤ l1.length + l2.length := by
  classical
  rw [← List.toFinset_card_of_nodup h1]
  calc l.toFinset.card ≤ (l1.toFinset ∪ l2.toFinset).card := by
        apply Finset.card_le_card
        intro x hx
        rcases h x (List.mem_toFinset.mp hx) with h' | h'
        · exact Finset.mem_union_left _ (List.mem_toFinset.mpr h')
        · exact Finset.mem_union_right _ (List.mem_toFinset.mpr h')
    _ ≤ l1.toFinset.card + l2.toFinset.card := Finset.card_union_le _ _
    _ ≤ l1.length + l2.length := by
        have := List.toFinset_card_le l1; have := List.toFinset_card_le l2; omega

end counting

section entops

variable {ops : DOps G s} {T : ℕ}

theorem ins_ent_le {B : WLab G s} {f0 : ℕ} {g : DGl G s} {Dc : DStrM G s}
    (h : SInv G s ops B f0 g Dc) (hK : DB.KeyInj g.L (kof G s)) {v : Fin G.n} {lam : WLab G s}
    (hlt : lam < B) (hkv : kof G s lam = v) :
    entCount (insC ops T g Dc v lam).2.1 ≤ entCount Dc + 1 := by
  obtain ⟨-, h', -⟩ := ins_sim (T := T) h hK hlt hkv
  exact len_le_of_sub_one (ents_nodup h'.ids) (ops.insert_ents T g.L g.fresh Dc v lam)

theorem insMany_ent_le {B : WLab G s} {f0 : ℕ} (f : Fin G.n → WLab G s) :
    ∀ (l : List (Fin G.n)) (g : DGl G s) (Dc : DStrM G s), SInv G s ops B f0 g Dc →
      DB.KeyInj g.L (kof G s) → (∀ y ∈ l, f y < B ∧ kof G s (f y) = y) →
      entCount (insManyC ops T f l g Dc).2.1 ≤ entCount Dc + l.length := by
  intro l
  induction l with
  | nil => intro g Dc _ _ _; exact le_refl _
  | cons y l ih =>
    intro g Dc h hK hl
    obtain ⟨hfy, hky⟩ := hl y List.mem_cons_self
    obtain ⟨-, h1, hK1, -⟩ := ins_sim (T := T) h hK hfy hky
    have e1 := ins_ent_le (T := T) h hK hfy hky
    have e2 := ih (insC ops T g Dc y (f y)).1 (insC ops T g Dc y (f y)).2.1 h1 hK1
      (fun z hz => hl z (List.mem_cons_of_mem _ hz))
    show entCount (insManyC ops T f l (insC ops T g Dc y (f y)).1 (insC ops T g Dc y (f y)).2.1).2.1
      ≤ entCount Dc + (y :: l).length
    rw [List.length_cons]
    omega

theorem relax_ent_le {B : WLab G s} {f0 : ℕ} (lo : Option (WLab G s)) (st : RSt G s) (e : Fin G.m)
    (h : SInv G s ops B f0 st.g st.Dc) (hK : DB.KeyInj st.g.L (kof G s)) (hw : WalkInv st.d) :
    entCount (relaxInsCc ops T B lo st e).Dc ≤ entCount st.Dc + 1 := by
  classical
  unfold relaxInsCc
  split_ifs with hv
  · have hlt : ext (st.d (G.src e)) e < B := hv.2
    have hkv := kof_ext hw (ne_top_of_lt hlt)
    cases lo with
    | none => exact ins_ent_le (T := T) h hK hlt hkv
    | some b =>
      simp only
      split_ifs
      · exact ins_ent_le (T := T) h hK hlt hkv
      · exact Nat.le_succ _
  · exact Nat.le_succ _

theorem fold_ent_le {B : WLab G s} {f0 : ℕ} (lo : Option (WLab G s)) :
    ∀ (L : List (Fin G.m)) (st : RSt G s), SInv G s ops B f0 st.g st.Dc →
      DB.KeyInj st.g.L (kof G s) → WalkInv st.d →
      entCount (L.foldl (relaxInsCc ops T B lo) st).Dc ≤ entCount st.Dc + L.length := by
  intro L
  induction L with
  | nil => intro st _ _ _; exact le_refl _
  | cons e L ih =>
    intro st h hK hw
    rw [List.foldl_cons]
    obtain ⟨e1, -, h1, hK1, -⟩ := relax_sim (T := T) lo st e h hK hw
    have hw1 : WalkInv (relaxInsCc ops T B lo st e).d := by
      rw [e1]; exact relaxIns_walk B lo _ e hw
    have a1 := relax_ent_le (T := T) lo st e h hK hw
    have a2 := ih (relaxInsCc ops T B lo st e) h1 hK1 hw1
    rw [List.length_cons]
    omega

theorem pull_ent_le {B : WLab G s} {f0 : ℕ} {g : DGl G s} {Dc : DStrM G s}
    (h : SInv G s ops B f0 g Dc) (hK : DB.KeyInj g.L (kof G s)) :
    entCount (pullC ops T g Dc).2.2.2.1 ≤ entCount Dc := by
  obtain ⟨hids1, -, -, -⟩ := ops.pull_aux T h.wf hK h.ids h.M1 h.sz h.fr
  exact len_le_of_sub (ents_nodup hids1) (ops.pull_ents T g.L Dc)

theorem merge_ent_le {D D' : DStrM G s} (hid : DB.IdsNodup (ops.merge T D D').1) :
    entCount (ops.merge T D D').1 ≤ entCount D + entCount D' :=
  len_le_of_sub_union (ents_nodup hid) (ops.merge_ents T D D')

end entops

section loopsim

variable {Φ Ω : Type} {T : ℕ} {DC : DCost}

theorem merge_M (D D' : DStrM G s) : (ops.merge T D D').1.M = D.M :=
  (ops.merge_M T D D').1

variable (G s) in
/-- The concrete post-condition of a call on the lazy structure (bound `B`, input labels `d0`,
level parameter `M`, global states `g ↦ g'`). -/
structure DPost (ops : DOps G s) (B : WLab G s) (d0 : Labels G s) (M : ℕ) (g g' : DGl G s)
    (res : ResultD G s) :
    Prop where
  sinv : SInv G s ops B g.fresh g' res.2.2.1
  M : res.2.2.1.M = M
  kinj : DB.KeyInj g'.L (kof G s)
  chg : CallChange g.fresh B g.L g'.L
  /-- TOUCH: every key whose live pointer changed is settled or kept with a value `≤ d0` -/
  touch : ∀ y, g'.L y ≠ g.L y → y ∈ res.2.1 ∨ ∃ a, g'.view res.2.2.1 y = some a ∧ a ≤ d0 y

/-- The literal result of a concrete one. -/
noncomputable def ResultD.lit (res : ResultD G s) (g' : DGl G s) : Result G s :=
  (res.1, res.2.1, g'.view res.2.2.1, res.2.2.2)

variable (G s) in
/-- Concrete sub-calls at level `l` simulate the literal ones. -/
def SimSub (ops : DOps G s) (τ : ℕ → ℕ) (Inv : Φ → Prop) (Mf : ℕ → ℕ) (l : ℕ) (subD : SubRelD G s Φ Ω)
    (subC : SubRelC G s Φ Ω) : Prop :=
  ∀ Blow B S d φ g res φ' g' lg, CallPre B S d → Inv φ → (∀ x ∈ S, Blow ≤ dis (s := s) x) →
    Blow ≤ B → DB.KeyInj g.L (kof G s) → (∀ v i a, g.L v = some (i, a) → B ≤ a) →
    subD Blow B S d φ g res φ' g' lg →
    ∃ lgC, subC Blow B S d φ (res.lit g') φ' lgC ∧ Log.strip lgC = Log.strip lg ∧
      DPost G s ops B d (Mf l) g g' res

variable {B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {p : ℕ}
  {P0 : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {B'0 : WLab G s}


/-- **One concrete iteration** (BM.10–BM.23): its literal counterpart and the simulation
invariants at the next state; the returned set `U_i` is disjoint from `U` and (for `τ l ≥ 1`)
nonempty. -/
theorem stepD_inv (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W)
    {τ : ℕ → ℕ} {Inv : Φ → Prop} {Mf : ℕ → ℕ}
    (hMf : ∀ l, ops.mergeM (Mf (l + 1)) (Mf l))
    {subD : SubRelD G s Φ Ω} {subC : SubRelC G s Φ Ω} {l : ℕ}
    (hsimsub : SimSub G s ops τ Inv Mf l subD subC) (hsubC : GoodSub G s τ Inv l subC)
    (hDC : DC.M (l + 1) = Mf (l + 1)) {g0 : DGl G s}
    {cs : CSt G s p} {φ φ1 : Φ} {ks : List (Fin G.n)} {Bi : WLab G s} {g1 : DGl G s}
    {Dc1 : DStrM G s} {cp : ℕ} {B'i : WLab G s} {Ui : Finset (Fin G.n)} {Dci : DStrM G s}
    {d1' : Labels G s} {g2 : DGl G s} {lUi : List (Fin G.n)} {L' : List (Fin G.m)}
    {piv' : Fin p → Fin G.n} {lres : List (Fin G.n)} {lg : Log G s Ω}
    (h : LInv G s B S d0 d1 P0 B'0 cs.lit) (hI : Inv φ) (hS : SInv G s ops B g0.fresh cs.g cs.Dc)
    (hMc : cs.Dc.M = Mf (l + 1)) (hK : DB.KeyInj cs.g.L (kof G s))
    (hCC : CallChange g0.fresh B g0.L cs.g.L)
    (hT : ∀ y, cs.g.L y ≠ g0.L y → y ∈ cs.U ∨ ∃ a, cs.g.view cs.Dc y = some a ∧ a ≤ d0 y)
    (hne : ¬ (cs.g.view cs.Dc).IsEmpty)
    (hpull : pullC ops T cs.g cs.Dc = (ks, Bi, g1, Dc1, cp))
    (hsubD : subD cs.B' Bi (expand cs.lit ks.toFinset Bi) cs.d φ g1 (B'i, Ui, Dci, d1') φ1 g2 lg)
    (hlU : lUi.toFinset = Ui) (hnd : L'.Nodup)
    (hmem : ∀ e, e ∈ L' ↔ G.src e ∈ Ui ∧ Bi ≤ ext (d1' (G.src e)) e ∧ ext (d1' (G.src e)) e < B)
    (hres : Reselect cs.lit Ui (L'.foldl (relaxInsCc ops T B (some Bi))
      ⟨d1', (delC g2 lUi).1, (ops.merge T Dc1 Dci).1, 0⟩).d piv')
    (hlres : lres.toFinset = reselected cs.lit Ui piv') :
    ∃ lgi, subC cs.lit.B' Bi (expand cs.lit ks.toFinset Bi) cs.lit.d φ
        (B'i, Ui, g2.view Dci, d1') φ1 lgi ∧ Log.strip lgi = Log.strip lg ∧
      PullSpec cs.lit.D B ks.toFinset Bi (g1.view Dc1) ∧ ks.toFinset.card ≤ DC.M (l + 1) ∧
      Reselect cs.lit Ui (L'.foldl (relaxIns G s B (some Bi))
        (d1', ((g1.view Dc1).merge (g2.view Dci)).deleteSet Ui)).1 piv' ∧
      (nextD ops T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).lit = nextState B cs.lit Bi B'i Ui (g1.view Dc1) (g2.view Dci) d1' L' piv' ∧
      LInv G s B S d0 d1 P0 B'0 (nextD ops T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).lit ∧ Inv φ1 ∧
      SInv G s ops B g0.fresh (nextD ops T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).g (nextD ops T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).Dc ∧ (nextD ops T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).Dc.M = Mf (l + 1) ∧
      DB.KeyInj (nextD ops T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).g.L (kof G s) ∧ CallChange g0.fresh B g0.L (nextD ops T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).g.L ∧
      (∀ y, (nextD ops T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).g.L y ≠ g0.L y → y ∈ (nextD ops T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).U ∨ ∃ a, (nextD ops T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).g.view (nextD ops T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).Dc y = some a ∧ a ≤ d0 y) ∧
      (1 ≤ τ l → Ui.Nonempty) ∧ Disjoint Ui cs.U ∧
      (ks.toFinset.card < DC.M (l + 1) → (g1.view Dc1).IsEmpty ∧ Bi = B) ∧
      entCount (nextD ops T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).Dc ≤ entCount cs.Dc + entCount Dci + L'.length + lres.length := by
    -- (1) pull
    obtain ⟨hPS, hS0M, hS1, hK1, hfr1, hL1, hlive1, hsep1, habove, hM1⟩ := pull_sim hS hK hpull
    have hPS' : PullSpec cs.lit.D B ks.toFinset Bi (g1.view Dc1) := hPS
    -- (2) the literal sub-call precondition
    have hsp : CallPre Bi (expand cs.lit ks.toFinset Bi) cs.lit.d := step_pre hpre hfp h hPS'
    have hlowdis : ∀ x ∈ expand cs.lit ks.toFinset Bi, cs.lit.B' ≤ dis (s := s) x :=
      fun x hx => (Si_facts h hPS' hx).1.2.2
    have hSne : ks.toFinset.Nonempty := by
      apply hPS'.nonempty
      have hne' : ¬ cs.lit.D.IsEmpty := hne
      simp only [DS.IsEmpty, not_forall] at hne'
      exact hne'
    obtain ⟨x0, hx0⟩ := hSne
    have hx0S : x0 ∈ expand cs.lit ks.toFinset Bi := mem_expand.mpr (Or.inl hx0)
    have hBlt : cs.lit.B' < Bi := by
      obtain ⟨⟨-, -, hB⟩, hlt⟩ := Si_facts h hPS' hx0S
      exact lt_of_le_of_lt (hB.trans (h.walk.sound x0)) hlt
    -- (3) the concrete sub-call simulates a literal one
    obtain ⟨lgi, hsubCi, hstripi, hDP⟩ := hsimsub cs.B' Bi (expand cs.lit ks.toFinset Bi) cs.d φ g1
      (B'i, Ui, Dci, d1') φ1 g2 lg hsp hI hlowdis hBlt.le hK1 habove hsubD
    have hsubCi' : subC cs.lit.B' Bi (expand cs.lit ks.toFinset Bi) cs.lit.d φ
        (B'i, Ui, g2.view Dci, d1') φ1 lgi := hsubCi
    obtain ⟨hpost, hI1, -⟩ := hsubC _ _ _ _ _ _ _ _ hsp hI hlowdis hBlt.le hsubCi'
    -- (4) merge + FIX-STALE
    have hUiU : ∀ y, y ∈ lUi ↔ y ∈ Ui := by
      intro y; rw [← hlU, List.mem_toFinset]
    have htouch : ∀ y, g2.L y ≠ g1.L y → y ∉ lUi →
        ∃ a, g2.view Dci y = some a ∧ ∀ b, g1.view Dc1 y = some b → a ≤ b := by
      intro y hy hyU
      have hyUi : y ∉ Ui := fun h' => hyU ((hUiU y).mpr h')
      rcases hDP.touch y hy with h' | ⟨a, ha, hale⟩
      · exact absurd h' hyUi
      · refine ⟨a, ha, fun b hb => hale.trans ?_⟩
        obtain ⟨hb', -⟩ := pull_rest_some hPS' hb
        exact h.storedGe y b hb'
    have hMM : ops.mergeM Dc1.M Dci.M := by
      have hMi : Dci.M = Mf l := hDP.M
      rw [hM1, hMc, hMi]; exact hMf l
    obtain ⟨hvm, hSm, hKm, hfrm, hLm⟩ := merge_sim (T := T) hS1 hlive1 hsep1 hPS.bound hDP.sinv
      hDP.kinj hDP.chg hMM lUi htouch
    rw [hlU] at hvm
    -- (5) the window scan
    have hw1 : WalkInv d1' := hpost.walk
    obtain ⟨fd, fv, hSf, hKf, hmf, hCCf, hTf⟩ := fold_sim (T := T) (some Bi) L'
      ⟨d1', (delC g2 lUi).1, (ops.merge T Dc1 Dci).1, 0⟩ hSm hKm hw1
    have hlit0 : ((⟨d1', (delC g2 lUi).1, (ops.merge T Dc1 Dci).1, 0⟩ : RSt G s).d,
        (⟨d1', (delC g2 lUi).1, (ops.merge T Dc1 Dci).1, 0⟩ : RSt G s).g.view
          (⟨d1', (delC g2 lUi).1, (ops.merge T Dc1 Dci).1, 0⟩ : RSt G s).Dc) =
        (d1', ((g1.view Dc1).merge (g2.view Dci)).deleteSet Ui) := by
      show (d1', (delC g2 lUi).1.view (ops.merge T Dc1 Dci).1) = _
      rw [hvm]
    rw [hlit0] at fd fv
    set fst := L'.foldl (relaxInsCc ops T B (some Bi)) ⟨d1', (delC g2 lUi).1, (ops.merge T Dc1 Dci).1, 0⟩
      with hfst
    set D0 := ((g1.view Dc1).merge (g2.view Dci)).deleteSet Ui with hD0
    have hres' : Reselect cs.lit Ui (L'.foldl (relaxIns G s B (some Bi)) (d1', D0)).1 piv' := by
      rw [← fd]; exact hres
    -- (6) the literal loop invariant for the next state
    have hmem' : ∀ e, e ∈ L' ↔ G.src e ∈ Ui ∧ Bi ≤ ext (dis (s := s) (G.src e)) e ∧
        ext (dis (s := s) (G.src e)) e < B := by
      intro e
      rw [hmem e]
      constructor
      · rintro ⟨hu, h1, h2⟩
        have hc : d1' (G.src e) = dis (s := s) (G.src e) := hpost.U_complete _ hu
        rw [hc] at h1 h2
        exact ⟨hu, h1, h2⟩
      · rintro ⟨hu, h1, h2⟩
        have hc : d1' (G.src e) = dis (s := s) (G.src e) := hpost.U_complete _ hu
        rw [← hc] at h1 h2
        exact ⟨hu, h1, h2⟩
    obtain ⟨Lall, hLall, hfold⟩ := window_scan_step hPS.bound hpost D0 hnd hmem'
    have hres'' : Reselect cs.lit Ui (Lall.foldl (relaxIns G s B (some Bi)) (d1', D0)).1 piv' := by
      rw [hfold]; exact hres'
    have hne' : ¬ cs.lit.D.IsEmpty := hne
    have hnext := step_post hpre hfp h hne' hPS' hpost hLall hres''
    rw [hfold] at hnext
    -- (7) the re-selection insertions
    have hdle : ∀ z, d1' z ≤ d0 z := fun z => (hpost.mono z).trans ((h.mono z).trans (hfp.le z))
    have hfle : ∀ z, fst.d z ≤ d0 z := by
      intro z; rw [fd]; exact (foldl_relaxIns_fst_le B (some Bi) L' _ z).trans (hdle z)
    have hfw : WalkInv fst.d := by rw [fd]; exact foldl_relaxIns_walk B (some Bi) L' _ hw1
    have hlres' : ∀ y ∈ lres, fst.d y < B ∧ kof G s (fst.d y) = y := by
      intro y hy
      have hy' : y ∈ reselected cs.lit Ui piv' := by rw [← hlres]; exact List.mem_toFinset.mpr hy
      obtain ⟨j, rfl, hpj, hne''⟩ := mem_reselected.mp hy'
      have hmemP : piv' j ∈ cs.lit.P j \ Ui := (hres.resel j hpj hne'').1
      have hmemS : piv' j ∈ S := (hfp.groups j).2 (h.Psub j (Finset.mem_sdiff.mp hmemP).1)
      have hlt : fst.d (piv' j) < B := lt_of_le_of_lt (hfle _) (hpre.inRange _ hmemS)
      exact ⟨hlt, kof_of_walk hfw (ne_top_of_lt hlt)⟩
    obtain ⟨hvn, hSn, hKn, hmn, hCCn, hTn⟩ := insMany_sim (T := T) fst.d lres fst.g fst.Dc hSf hKf
      hlres'
    -- (8) the next concrete state is the literal next state
    have hlitnext : (nextD ops T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).lit =
        nextState B cs.lit Bi B'i Ui (g1.view Dc1) (g2.view Dci) d1' L' piv' := by
      show ({ d := fst.d, D := (insManyC ops T fst.d lres fst.g fst.Dc).1.view
                (insManyC ops T fst.d lres fst.g fst.Dc).2.1,
              P := fun j => cs.P j \ Ui, piv := piv', U := cs.U ∪ Ui, B' := B'i } : LState G s p) =
        nextState B cs.lit Bi B'i Ui (g1.view Dc1) (g2.view Dci) d1' L' piv'
      rw [hvn, fv, fd, hlres]
      rfl
    set csn := nextD ops T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres with hcsn
    have hSn' : SInv G s ops B g0.fresh csn.g csn.Dc := hSn
    have hMn' : csn.Dc.M = Mf (l + 1) := by
      show (insManyC ops T fst.d lres fst.g fst.Dc).2.1.M = Mf (l + 1)
      rw [insManyC_M, hfst, fold_M]
      show (ops.merge T Dc1 Dci).1.M = Mf (l + 1)
      rw [merge_M, hM1, hMc]
    have hKn' : DB.KeyInj csn.g.L (kof G s) := hKn
    have hCCn' : CallChange g0.fresh B g0.L csn.g.L := by
      have c1 : CallChange g0.fresh B cs.g.L g1.L := by
        rw [hL1]; exact callChange_clearKeys _ _ _ _
      have c2 : CallChange g0.fresh B g1.L g2.L := hDP.chg.mono hS1.f0_le hPS.bound
      have c3 : CallChange g0.fresh B g2.L (delC g2 lUi).1.L := by
        rw [hLm]; exact callChange_clearKeys _ _ _ _
      have c4 : CallChange g0.fresh B (delC g2 lUi).1.L fst.g.L := hCCf.mono hSm.f0_le le_rfl
      have c5 : CallChange g0.fresh B fst.g.L csn.g.L := hCCn.mono hSf.f0_le le_rfl
      exact hCC.trans (c1.trans (c2.trans (c3.trans (c4.trans c5))))
    have hDn : csn.g.view csn.Dc =
        (nextState B cs.lit Bi B'i Ui (g1.view Dc1) (g2.view Dci) d1' L' piv').D := by
      rw [← hlitnext]; rfl
    have hTn' : ∀ y, csn.g.L y ≠ g0.L y →
        y ∈ csn.U ∨ ∃ a, csn.g.view csn.Dc y = some a ∧ a ≤ d0 y := by
      intro y hy
      rw [hDn]
      by_cases hU : y ∈ Ui
      · exact Or.inl (Finset.mem_union_right _ hU)
      have hyl : y ∉ lUi := fun h' => hU ((hUiU y).mp h')
      by_cases hn : csn.g.L y = fst.g.L y
      · by_cases hf : fst.g.L y = (delC g2 lUi).1.L y
        · have h32 : (delC g2 lUi).1.L y = g2.L y := by
            rw [hLm]; unfold DB.clearKeys; rw [if_neg hyl]
          by_cases h21 : g2.L y = g1.L y
          · by_cases h1c : g1.L y = cs.g.L y
            · have hc0 : cs.g.L y ≠ g0.L y := by
                intro h'; apply hy; rw [hn, hf, h32, h21, h1c, h']
              rcases hT y hc0 with hcU | ⟨a, ha, hale⟩
              · exact Or.inl (Finset.mem_union_left _ hcU)
              · have hyks : y ∉ ks := by
                  intro hyk
                  have hnone : g1.L y = none := by
                    rw [hL1]; unfold DB.clearKeys; rw [if_pos hyk]
                  obtain ⟨e, he, hek⟩ := hasKey_of_view ha
                  have hl := (DB.mem_liveVals.mp he).2
                  unfold DB.Entry.IsLive at hl
                  rw [hek] at hl
                  rw [h1c, hl] at hnone
                  exact absurd hnone (Option.some_ne_none _)
                have hD1 : (g1.view Dc1) y = some a := by
                  rw [hPS.rest y, if_neg (fun h' => hyks (List.mem_toFinset.mp h'))]
                  exact ha
                obtain ⟨a', ha', hle⟩ := nextState_D_le_left B cs.lit Bi B'i Ui _ _ d1' L' piv' hU hD1
                exact Or.inr ⟨a', ha', hle.trans hale⟩
            · have hyks : y ∈ ks := by
                by_contra hyk; apply h1c; rw [hL1]; unfold DB.clearKeys; rw [if_neg hyk]
              have hyS : y ∈ expand cs.lit ks.toFinset Bi :=
                mem_expand.mpr (Or.inl (List.mem_toFinset.mpr hyks))
              obtain ⟨k, hk, hkle⟩ := hpost.S_keys y hyS hU
              obtain ⟨a', ha', hle⟩ := nextState_D_le_right B cs.lit Bi B'i Ui _ _ d1' L' piv' hU hk
              exact Or.inr ⟨a', ha', hle.trans (hkle.trans ((h.mono y).trans (hfp.le y)))⟩
          · rcases hDP.touch y h21 with hyU' | ⟨a, ha, hale⟩
            · exact absurd hyU' hU
            · obtain ⟨a', ha', hle⟩ := nextState_D_le_right B cs.lit Bi B'i Ui _ _ d1' L' piv' hU ha
              exact Or.inr ⟨a', ha', hle.trans (hale.trans ((h.mono y).trans (hfp.le y)))⟩
        · obtain ⟨a, ha, hale⟩ := hTf y hf
          rw [fv] at ha
          obtain ⟨a', ha', hle⟩ := insertMany_le (reselected cs.lit Ui piv')
            (L'.foldl (relaxIns G s B (some Bi)) (d1', D0)).1 ha
          exact Or.inr ⟨a', ha', hle.trans (hale.trans (hdle y))⟩
      · have hyl' := hTn y hn
        have hyr : y ∈ reselected cs.lit Ui piv' := by
          rw [← hlres]; exact List.mem_toFinset.mpr hyl'
        obtain ⟨k, hk, hkle⟩ := DSx.mergeVal_le_right
          (a := (L'.foldl (relaxIns G s B (some Bi)) (d1', D0)).2 y)
          (b := some ((L'.foldl (relaxIns G s B (some Bi)) (d1', D0)).1 y)) rfl
        refine Or.inr ⟨k, ?_, hkle.trans ?_⟩
        · show insertMany G s _ _ _ y = some k
          rw [insertMany_apply, if_pos hyr]; exact hk
        · rw [← fd]; exact hfle y
    have hUi_disj : Disjoint Ui cs.U := by
      rw [Finset.disjoint_left]
      intro v hv hvU
      have hv' : v ∈ Utilde Bi (expand cs.lit ks.toFinset Bi : Set (Fin G.n)) :=
        utilde_mono_bound hpost.B'_le ((hpost.U_eq v).mp hv)
      exact (UKi_sub h hPS' hv').2.1 hvU
    have hUine : 1 ≤ τ l → Ui.Nonempty := by
      intro hτ1
      by_cases hfull : B'i = Bi
      · refine ⟨x0, (hpost.U_eq x0).mpr ?_⟩
        obtain ⟨-, hlt⟩ := Si_facts h hPS' hx0S
        have hdis : dis (s := s) x0 < Bi := lt_of_le_of_lt (h.walk.sound x0) hlt
        have hreach : G.Reachable s x0 := by
          by_contra hc
          rw [dis_of_not_reachable hc] at hdis
          exact absurd hdis (not_lt.mpr le_top)
        refine ⟨?_, x0, Finset.mem_coe.mpr hx0S, onPath_self hreach⟩
        show dis (s := s) x0 < B'i
        rw [hfull]; exact hdis
      · have hlt : B'i < Bi := lt_of_le_of_ne hpost.B'_le hfull
        have hcard := hpost.partial_card hlt
        exact Finset.card_pos.mp (lt_of_lt_of_le hτ1 hcard)
    have hstrong : ks.toFinset.card < DC.M (l + 1) → (g1.view Dc1).IsEmpty ∧ Bi = B := by
      intro hlt
      simp only [pullC, Prod.mk.injEq] at hpull
      obtain ⟨hks, hBi, hg1, hDc1, -⟩ := hpull
      have hnd' : ks.Nodup := hks ▸ ops.pull_nodup T hS.ids
      rw [List.toFinset_card_of_nodup hnd', hDC, ← hMc] at hlt
      obtain ⟨-, hor, -, -, -⟩ := ops.pull_post T hS.wf hK hS.ids hS.M1
      have hBiB : Bi = B := by
        rcases hor with h' | h'
        · rw [← hBi, h', hS.Bd]
        · rw [hks] at h'; omega
      refine ⟨?_, hBiB⟩
      intro y
      rw [hPS.rest y]
      split_ifs with hy
      · rfl
      · rcases hv : cs.g.view cs.Dc y with _ | a
        · rfl
        · exfalso
          apply hy
          have hlt' : a < Bi := by
            rw [hBiB, ← hS.Bd]; exact view_lt_Bd hS.wf hv
          exact (hPS.pulled y).mpr ⟨a, hv, hlt'⟩
    have hent : entCount (nextD ops T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).Dc ≤
        entCount cs.Dc + entCount Dci + L'.length + lres.length := by
      have e1 : entCount Dc1 ≤ entCount cs.Dc := by
        have := pull_ent_le (T := T) hS hK
        rw [hpull] at this; exact this
      have e2 : entCount (ops.merge T Dc1 Dci).1 ≤ entCount Dc1 + entCount Dci :=
        merge_ent_le hSm.ids
      have e3 := fold_ent_le (T := T) (some Bi) L' ⟨d1', (delC g2 lUi).1, (ops.merge T Dc1 Dci).1, 0⟩
        hSm hKm hw1
      have e4 := insMany_ent_le (T := T) fst.d lres fst.g fst.Dc hSf hKf hlres'
      show entCount (insManyC ops T fst.d lres fst.g fst.Dc).2.1 ≤ _
      have e3' : entCount fst.Dc ≤ entCount (ops.merge T Dc1 Dci).1 + L'.length := e3
      omega
    exact ⟨lgi, hsubCi', hstripi, hPS', by rw [hDC, ← hMc]; exact hS0M, hres', hlitnext,
      by rw [hlitnext]; exact hnext, hI1, hSn', hMn', hKn', hCCn', hTn', hUine, hUi_disj, hstrong,
      hent⟩

/-- **The loop over the lazy structure simulates the literal loop.** -/
theorem loopD_sim (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W)
    {τ : ℕ → ℕ} {Inv : Φ → Prop} {Mf : ℕ → ℕ}
    (hMf : ∀ l, ops.mergeM (Mf (l + 1)) (Mf l))
    {subD : SubRelD G s Φ Ω} {subC : SubRelC G s Φ Ω} {l : ℕ}
    (hsimsub : SimSub G s ops τ Inv Mf l subD subC) (hsubC : GoodSub G s τ Inv l subC)
    (hDC : DC.M (l + 1) = Mf (l + 1)) {g0 : DGl G s} {τl : ℕ} :
    ∀ i (cs : CSt G s p) φ cs' φ' lg J cm c, LoopD G s ops T subD B τl i cs φ cs' φ' lg J cm c →
      LInv G s B S d0 d1 P0 B'0 cs.lit → Inv φ → SInv G s ops B g0.fresh cs.g cs.Dc →
      cs.Dc.M = Mf (l + 1) → DB.KeyInj cs.g.L (kof G s) → CallChange g0.fresh B g0.L cs.g.L →
      (∀ y, cs.g.L y ≠ g0.L y → y ∈ cs.U ∨ ∃ a, cs.g.view cs.Dc y = some a ∧ a ≤ d0 y) →
      ∃ lgC cmC cC, LoopC G s DC subC (l + 1) B τl i cs.lit φ cs'.lit φ' lgC J cmC cC ∧
        Log.strip lgC = Log.strip lg ∧
        LInv G s B S d0 d1 P0 B'0 cs'.lit ∧ (τl < cs'.U.card ∨ (cs'.g.view cs'.Dc).IsEmpty) ∧
        Inv φ' ∧ SInv G s ops B g0.fresh cs'.g cs'.Dc ∧ cs'.Dc.M = Mf (l + 1) ∧
        DB.KeyInj cs'.g.L (kof G s) ∧ CallChange g0.fresh B g0.L cs'.g.L ∧
        (∀ y, cs'.g.L y ≠ g0.L y → y ∈ cs'.U ∨ ∃ a, cs'.g.view cs'.Dc y = some a ∧ a ≤ d0 y) := by
  intro i cs φ cs' φ' lg J cm c hloop
  induction hloop with
  | stop i cs φ hstop =>
    intro h hI hS hMc hK hCC hT
    exact ⟨[], 0, 1, LoopC.stop i cs.lit φ hstop, rfl, h, hstop, hI, hS, hMc, hK, hCC, hT⟩
  | step i cs cs' φ φ1 φ' ks Bi g1 Dc1 cp B'i Ui Dci d1' g2 lUi L' piv' lres lg lg' J' cm c
      hcard hne hpull hsubD hlUnd hlU hnd hmem hres hlresnd hlres _ ih =>
    intro h hI hS hMc hK hCC hT
    obtain ⟨lgi, hsubCi', hstripi, hPS', hS0M', hres', hlitnext, hnext', hI1, hSn', hMn', hKn',
      hCCn', hTn', -, -, hSP', -⟩ := stepD_inv (T := T) (DC := DC) (g0 := g0) hpre hfp hMf hsimsub hsubC hDC
      h hI hS hMc hK hCC hT hne hpull hsubD hlU hnd hmem hres hlres
    have hne' : ¬ cs.lit.D.IsEmpty := hne
    -- (9) the rest of the loop
    obtain ⟨lgC', cmC', cC', hloopC', hstrip', h', hstop', hI', hS', hM', hK', hCC', hT'⟩ :=
      ih hnext' hI1 hSn' hMn' hKn' hCCn' hTn'
    rw [hlitnext] at hloopC'
    refine ⟨lgi.shift i ++ lgC', _, _, LoopC.step i cs.lit cs'.lit φ φ1 φ' ks.toFinset Bi
      (g1.view Dc1) B'i Ui (g2.view Dci) d1' L' piv' lgi lgC' J' cmC' cC' hcard hne' hPS'
      hS0M' hSP' hsubCi' hnd hmem hres' hloopC', ?_, h', hstop', hI', hS', hM',
      hK', hCC', hT'⟩
    rw [Log.strip_append, Log.strip_append, Log.strip_shift, Log.strip_shift, hstripi, hstrip']

end loopsim


section callsim

variable {Φ Ω : Type} {T : ℕ} {DC : DCost}

/-- **A recursive call over the lazy structure simulates the literal call.** -/
theorem callD_sim {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} (hFPC : FPCSound G s FPC Inv)
    {τ : ℕ → ℕ} {Mf : ℕ → ℕ} (hMf : ∀ l, ops.mergeM (Mf (l + 1)) (Mf l))
    (hM1 : ∀ l, 1 ≤ Mf l)
    {subD : SubRelD G s Φ Ω} {subC : SubRelC G s Φ Ω} {l : ℕ}
    (hsimsub : SimSub G s ops τ Inv Mf l subD subC) (hsubC : GoodSub G s τ Inv l subC)
    (hDC : DC.M (l + 1) = Mf (l + 1))
    {Blow B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} {φ0 φ2 : Φ} {g0 gE : DGl G s}
    {res : ResultD G s} {lg : Log G s Ω}
    (hpre : CallPre B S d0) (hI : Inv φ0) (hlow : ∀ x ∈ S, Blow ≤ dis (s := s) x)
    (hK : DB.KeyInj g0.L (kof G s)) (hab : ∀ v i a, g0.L v = some (i, a) → B ≤ a)
    (hrel : CallD G s ops FPC T Mf subD (l + 1) Blow B S d0 φ0 g0 (τ (l + 1)) res φ2 gE lg) :
    ∃ lgC, CallC G s FPC DC subC (l + 1) Blow B S d0 φ0 (τ (l + 1)) (res.lit gE) φ2 lgC ∧
      Log.strip lgC = Log.strip lg ∧ DPost G s ops B d0 (Mf (l + 1)) g0 gE res := by
  obtain ⟨d1, p, P, Q, W, φ1, ω, cfp, piv, lpiv, cs, lgc, J, cm, cl, L, B'f, lT6, W', lW', hfprel,
    hpiv, hlpnd, hlp, hloop, hB'e, hB'n, hT6nd, hT6, hW', hL, hlWnd, hlW, hres, hgE, hlg⟩ := hrel
  have hlow' : ∀ x ∈ S, Blow ≤ d0 x := fun x hx => (hlow x hx).trans (hpre.walk.sound x)
  obtain ⟨hfp, hI1⟩ := hFPC _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpre hI hlow' hfprel
  -- the initial structure with the pivots
  obtain ⟨hSnew, hvnew⟩ := new_sim (g := g0) (M := Mf (l + 1)) (B := B) (hM1 _) hab
  have hlp' : ∀ y ∈ lpiv, d1 y < B ∧ kof G s (d1 y) = y := by
    intro y hy
    have hy' : y ∈ Finset.univ.image piv := by rw [← hlp]; exact List.mem_toFinset.mpr hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy'
    have hS : piv j ∈ S := (hfp.groups j).2 (hpiv j).1
    have hlt : d1 (piv j) < B := lt_of_le_of_lt (hfp.le _) (hpre.inRange _ hS)
    exact ⟨hlt, kof_of_walk hfp.walk (ne_top_of_lt hlt)⟩
  obtain ⟨hvi, hSi, hKi, hmi, hCCi, hTi⟩ :=
    insMany_sim (T := T) d1 lpiv g0 (newC (Mf (l + 1)) B) hSnew hK hlp'
  have hcs0 :
      ({ d := d1, P := P, piv := piv, U := ∅, B' := initB' B d1 piv,
         g := (initD ops T (Mf (l + 1)) B d1 lpiv g0).1,
         Dc := (initD ops T (Mf (l + 1)) B d1 lpiv g0).2.1 } : CSt G s p).lit =
        initState B d1 P piv := by
    show
      ({ d := d1, D := (insManyC ops T d1 lpiv g0 (newC (Mf (l + 1)) B)).1.view
           (insManyC ops T d1 lpiv g0 (newC (Mf (l + 1)) B)).2.1,
         P := P, piv := piv, U := ∅, B' := initB' B d1 piv } : LState G s p) = _
    rw [hvi, hvnew, hlp]; rfl
  have h0 := linv_init hpre hfp hpiv
  rw [← hcs0] at h0
  have hM0 : (initD ops T (Mf (l + 1)) B d1 lpiv g0).2.1.M = Mf (l + 1) := by
    show (insManyC ops T d1 lpiv g0 (newC (Mf (l + 1)) B)).2.1.M = _
    rw [insManyC_M]; rfl
  have hT0 : ∀ y, (initD ops T (Mf (l + 1)) B d1 lpiv g0).1.L y ≠ g0.L y →
      y ∈ (∅ : Finset (Fin G.n)) ∨ ∃ a, (initD ops T (Mf (l + 1)) B d1 lpiv g0).1.view
        (initD ops T (Mf (l + 1)) B d1 lpiv g0).2.1 y = some a ∧ a ≤ d0 y := by
    intro y hy
    have hyl := hTi y hy
    right
    refine ⟨d1 y, ?_, hfp.le y⟩
    show (insManyC ops T d1 lpiv g0 (newC (Mf (l + 1)) B)).1.view
      (insManyC ops T d1 lpiv g0 (newC (Mf (l + 1)) B)).2.1 y = some (d1 y)
    rw [hvi, hvnew, insertMany_apply, if_pos (List.mem_toFinset.mpr hyl)]
    rfl
  -- the loop
  obtain ⟨lgcC, cmC, cC, hloopC, hstripc, h, hstop, hI2, hS, hM, hKc, hCC, hT⟩ :=
    loopD_sim (T := T) (DC := DC) (g0 := g0) hpre hfp hMf hsimsub hsubC hDC 0 _ φ1 cs φ2 lgc J cm cl
      hloop h0 hI1 hSi hM0 hKi hCCi hT0
  rw [hcs0] at hloopC
  -- the finalization
  have hlT6' : ∀ y ∈ lT6, cs.d y < B ∧ kof G s (cs.d y) = y := by
    intro y hy
    have hlt := ((hT6 y).mp hy).2.2
    exact ⟨hlt, kof_of_walk h.walk (ne_top_of_lt hlt)⟩
  obtain ⟨hv6, hS6, hK6, hm6, hCC6, hTc6⟩ := insMany_sim (T := T) cs.d lT6 cs.g cs.Dc hS hKc hlT6'
  obtain ⟨fd, fv, hSf, hKf, hmf, hCCf, hTf⟩ := fold_sim (T := T) (some B'f) L
    ⟨cs.d, (insManyC ops T cs.d lT6 cs.g cs.Dc).1, (insManyC ops T cs.d lT6 cs.g cs.Dc).2.1, 0⟩ hS6 hK6 h.walk
  have hlit6 : ((⟨cs.d, (insManyC ops T cs.d lT6 cs.g cs.Dc).1, (insManyC ops T cs.d lT6 cs.g cs.Dc).2.1, 0⟩ :
        RSt G s).d,
      (⟨cs.d, (insManyC ops T cs.d lT6 cs.g cs.Dc).1, (insManyC ops T cs.d lT6 cs.g cs.Dc).2.1, 0⟩ :
        RSt G s).g.view
        (⟨cs.d, (insManyC ops T cs.d lT6 cs.g cs.Dc).1, (insManyC ops T cs.d lT6 cs.g cs.Dc).2.1, 0⟩ :
          RSt G s).Dc) = (cs.d, insertMany G s cs.lit.D lT6.toFinset cs.d) := by
    show (cs.d, (insManyC ops T cs.d lT6 cs.g cs.Dc).1.view (insManyC ops T cs.d lT6 cs.g cs.Dc).2.1) = _
    rw [hv6]; rfl
  rw [hlit6] at fd fv
  set fw := L.foldl (relaxInsCc ops T B (some B'f))
    ⟨cs.d, (insManyC ops T cs.d lT6 cs.g cs.Dc).1, (insManyC ops T cs.d lT6 cs.g cs.Dc).2.1, 0⟩ with hfw
  obtain ⟨hvd, hSd, hKd, hfd, hLd⟩ := del_sim hSf hKf lW'
  -- the results agree
  have hres1 : res = (B'f, cs.U ∪ W', fw.Dc, fw.d) := hres
  have hgE1 : gE = (delC fw.g lW').1 := hgE
  have hlitres : res.lit gE = (B'f, cs.lit.U ∪ W',
      ((L.foldl (relaxIns G s B (some B'f)) (cs.lit.d, insertMany G s cs.lit.D lT6.toFinset cs.lit.d)).2).deleteSet W',
      (L.foldl (relaxIns G s B (some B'f)) (cs.lit.d, insertMany G s cs.lit.D lT6.toFinset cs.lit.d)).1) := by
    rw [hres1, hgE1]
    show (B'f, cs.U ∪ W', (delC fw.g lW').1.view fw.Dc, fw.d) = _
    rw [hvd, fv, fd, hlW]
    rfl
  refine ⟨([],
      { lvl := l + 1, Blow := Blow, B := B, S := S, B' := B'f, U := cs.lit.U ∪ W',
        base := false, p := p, Q := Q, W := W, W' := W', J := J, Wr := L.toFinset,
        fp := some ω, cFP := cfp, cMerge := cmC,
        cost := cfp + initCost DC (l + 1) p P + cC + cmC
          + finCost DC (l + 1) p P S W lT6.toFinset W' L.length }) :: lgcC,
    ⟨d1, p, P, Q, W, φ1, ω, cfp, piv, cs.lit, lgcC, J, cmC, cC, L, B'f, lT6.toFinset, W', hfprel,
      hpiv, hloopC, hB'e, hB'n, fun x => by rw [List.mem_toFinset]; exact hT6 x, hW', hL, hlitres,
      rfl⟩, ?_, ?_⟩
  · rw [hlg, Log.strip_cons, Log.strip_cons, hstripc]
    rfl
  · -- the concrete post-condition
    have hmid : ∀ y, y ∉ lW' → (delC fw.g lW').1.L y = fw.g.L y := by
      intro y hy; rw [hLd]; unfold DB.clearKeys; rw [if_neg hy]
    have hdle : ∀ z, cs.d z ≤ d0 z := fun z => (h.mono z).trans (hfp.le z)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hres1, hgE1]; exact hSd
    · rw [hres1]
      show fw.Dc.M = Mf (l + 1)
      rw [hfw, fold_M, insManyC_M, hM]
    · rw [hgE1]; exact hKd
    · rw [hgE1]
      have c1 : CallChange g0.fresh B cs.g.L (insManyC ops T cs.d lT6 cs.g cs.Dc).1.L :=
        hCC6.mono hS.f0_le le_rfl
      have c2 : CallChange g0.fresh B (insManyC ops T cs.d lT6 cs.g cs.Dc).1.L fw.g.L :=
        hCCf.mono hS6.f0_le le_rfl
      have c3 : CallChange g0.fresh B fw.g.L (delC fw.g lW').1.L := by
        rw [hLd]; exact callChange_clearKeys _ _ _ _
      exact hCC.trans (c1.trans (c2.trans c3))
    · intro y hy
      rw [hres1]
      rw [hgE1] at hy ⊢
      by_cases hyW : y ∈ W'
      · exact Or.inl (Finset.mem_union_right _ hyW)
      have hyl : y ∉ lW' := fun h' => hyW (by rw [← hlW]; exact List.mem_toFinset.mpr h')
      have hvfin : ∀ a, fw.g.view fw.Dc y = some a →
          (delC fw.g lW').1.view fw.Dc y = some a := by
        intro a ha
        rw [hvd]; simp only [DS.deleteSet, List.mem_toFinset, if_neg hyl]; exact ha
      rw [hmid y hyl] at hy
      by_cases hf : fw.g.L y = (insManyC ops T cs.d lT6 cs.g cs.Dc).1.L y
      · by_cases h6 : (insManyC ops T cs.d lT6 cs.g cs.Dc).1.L y = cs.g.L y
        · have hc0 : cs.g.L y ≠ g0.L y := by
            intro h'; apply hy; rw [hf, h6, h']
          rcases hT y hc0 with hcU | ⟨a, ha, hale⟩
          · exact Or.inl (Finset.mem_union_left _ hcU)
          · obtain ⟨a1, ha1, hle1⟩ := insertMany_le (D := cs.lit.D) lT6.toFinset cs.d ha
            obtain ⟨a2, ha2, hle2⟩ := foldl_relaxIns_snd_le B (some B'f) L
              (cs.d, insertMany G s cs.lit.D lT6.toFinset cs.d) y a1 ha1
            rw [← fv] at ha2
            exact Or.inr ⟨a2, hvfin a2 ha2, hle2.trans (hle1.trans hale)⟩
        · have hyl6 := hTc6 y h6
          have h61 : insertMany G s cs.lit.D lT6.toFinset cs.d y ≠ none := by
            rw [insertMany_apply, if_pos (List.mem_toFinset.mpr hyl6)]
            obtain ⟨k, hk, -⟩ := DSx.mergeVal_le_right (a := cs.lit.D y) (b := some (cs.d y)) rfl
            rw [hk]; exact Option.some_ne_none _
          obtain ⟨k, hk, hkle⟩ := DSx.mergeVal_le_right (a := cs.lit.D y) (b := some (cs.d y)) rfl
          have hk' : insertMany G s cs.lit.D lT6.toFinset cs.d y = some k := by
            rw [insertMany_apply, if_pos (List.mem_toFinset.mpr hyl6)]; exact hk
          obtain ⟨a2, ha2, hle2⟩ := foldl_relaxIns_snd_le B (some B'f) L
            (cs.d, insertMany G s cs.lit.D lT6.toFinset cs.d) y k hk'
          rw [← fv] at ha2
          exact Or.inr ⟨a2, hvfin a2 ha2, hle2.trans (hkle.trans (hdle y))⟩
      · obtain ⟨a, ha, hale⟩ := hTf y hf
        exact Or.inr ⟨a, hvfin a ha, hale.trans (hdle y)⟩

end callsim


section basesim

variable {Φ Ω : Type} {T : ℕ} {DC : DCost}

theorem kof_of_view {L : LiveM G s} {D : DStrM G s} (hK : DB.KeyInj L (kof G s)) {y : Fin G.n}
    {a : WLab G s} (h : DB.view L D y = some a) : kof G s a = y := by
  obtain ⟨e, he, hek, rfl⟩ := DB.view_eq_some.mp h
  have hl := (DB.mem_liveVals.mp he).2
  unfold DB.Entry.IsLive at hl
  rw [← hek]
  exact hK e.key e.id e.val hl

/-- Stored values stay below `d0` through a relaxation (inserted values are labels). -/
theorem relaxIns_vals_le {B : WLab G s} {lo : Option (WLab G s)} {st : Labels G s × DS G s}
    {d0 : Labels G s} (hd : ∀ z, st.1 z ≤ d0 z) (hD : ∀ y a, st.2 y = some a → a ≤ d0 y)
    (e : Fin G.m) : ∀ y a, (relaxIns G s B lo st e).2 y = some a → a ≤ d0 y := by
  have hins : ∀ y a, (st.2.insert (G.dst e) (ext (st.1 (G.src e)) e)) y = some a →
      ValidRelax G s st.1 B e → a ≤ d0 y := by
    intro y a hy hv
    unfold DS.insert at hy
    by_cases hye : y = G.dst e
    · subst hye
      rw [Function.update_self] at hy
      rcases hold : st.2 (G.dst e) with _ | o
      · rw [hold] at hy
        simp only [DS.mergeVal, Option.some.injEq] at hy
        rw [← hy]; exact hv.1.trans (hd _)
      · rw [hold] at hy
        simp only [DS.mergeVal, Option.some.injEq] at hy
        rw [← hy]; exact (min_le_right _ _).trans (hv.1.trans (hd _))
    · rw [Function.update_of_ne hye] at hy; exact hD y a hy
  intro y a hy
  unfold relaxIns at hy
  split_ifs at hy with hv
  · cases lo with
    | none => exact hins y a hy hv
    | some b =>
      simp only at hy
      split_ifs at hy
      · exact hins y a hy hv
      · exact hD y a hy
  · exact hD y a hy

theorem foldl_relaxIns_vals_le {B : WLab G s} {lo : Option (WLab G s)} {d0 : Labels G s} :
    ∀ (L : List (Fin G.m)) (st : Labels G s × DS G s), (∀ z, st.1 z ≤ d0 z) →
      (∀ y a, st.2 y = some a → a ≤ d0 y) →
      ∀ y a, (L.foldl (relaxIns G s B lo) st).2 y = some a → a ≤ d0 y := by
  intro L
  induction L with
  | nil => intro st _ hD; exact hD
  | cons e L ih =>
    intro st hd hD
    rw [List.foldl_cons]
    exact ih _ (fun z => (relaxIns_fst_le B lo st e z).trans (hd z)) (relaxIns_vals_le hd hD e)

/-- **The base loop over the lazy structure simulates the literal base loop.** -/
theorem baseLoopD_sim {B : WLab G s} {τ : ℕ} {g0 : DGl G s} {d0 : Labels G s} :
    ∀ {st st' : Labels G s × DGl G s × DStrM G s × Finset (Fin G.n)} {c : ℕ},
      BaseLoopD G s ops T B τ st st' c →
      SInv G s ops B g0.fresh st.2.1 st.2.2.1 → DB.KeyInj st.2.1.L (kof G s) → WalkInv st.1 →
      (∀ z, st.1 z ≤ d0 z) → (∀ y a, st.2.1.view st.2.2.1 y = some a → a ≤ d0 y) →
      CallChange g0.fresh B g0.L st.2.1.L →
      (∀ y, st.2.1.L y ≠ g0.L y →
        y ∈ st.2.2.2 ∨ ∃ a, st.2.1.view st.2.2.1 y = some a ∧ a ≤ d0 y) →
      (∃ c', BaseLoopC G s DC B τ (st.1, st.2.1.view st.2.2.1, st.2.2.2)
        (st'.1, st'.2.1.view st'.2.2.1, st'.2.2.2) c') ∧
      SInv G s ops B g0.fresh st'.2.1 st'.2.2.1 ∧ DB.KeyInj st'.2.1.L (kof G s) ∧ WalkInv st'.1 ∧
      (∀ z, st'.1 z ≤ d0 z) ∧ (∀ y a, st'.2.1.view st'.2.2.1 y = some a → a ≤ d0 y) ∧
      CallChange g0.fresh B g0.L st'.2.1.L ∧
      (∀ y, st'.2.1.L y ≠ g0.L y →
        y ∈ st'.2.2.2 ∨ ∃ a, st'.2.1.view st'.2.2.1 y = some a ∧ a ≤ d0 y) ∧
      st'.2.2.1.M = st.2.2.1.M := by
  intro st st' c hloop
  induction hloop with
  | stop st hst =>
    intro hS hK hw hd hv hCC hT
    exact ⟨⟨1, BaseLoopC.stop _ hst⟩, hS, hK, hw, hd, hv, hCC, hT, rfl⟩
  | step d g Dc U u x g1 Dc1 cp L st' c hpull hcard hL _ ih =>
    intro hS hK hw hd hv hCC hT
    obtain ⟨hPS, -, hS1, hK1, hfr1, hL1, -, -, -, hM1⟩ := pull_sim hS hK hpull
    have hu : u ∈ ([u] : List (Fin G.n)).toFinset := by simp
    obtain ⟨val, hval, hvx⟩ := (hPS.pulled u).mp hu
    have hmin : ∀ y v, g.view Dc y = some v → val ≤ v := by
      intro y v hy
      by_cases hyu : y = u
      · subst hyu; rw [hval] at hy; exact le_of_eq (Option.some.inj hy)
      · have hy' : y ∉ ([u] : List (Fin G.n)).toFinset := by simp [hyu]
        have : ¬ v < x := fun hlt => hy' ((hPS.pulled y).mpr ⟨v, hy, hlt⟩)
        exact (hvx.trans_le (not_lt.mp this)).le
    have hdel : (g.view Dc).deleteSet {u} = g1.view Dc1 := by
      funext y
      rw [hPS.rest y]
      simp [DS.deleteSet]
    obtain ⟨fd, fv, hSf, hKf, hmf, hCCf, hTf⟩ := fold_sim (T := T) none L ⟨d, g1, Dc1, 0⟩ hS1 hK1 hw
    have hlit : ((⟨d, g1, Dc1, 0⟩ : RSt G s).d,
        (⟨d, g1, Dc1, 0⟩ : RSt G s).g.view (⟨d, g1, Dc1, 0⟩ : RSt G s).Dc) =
        (d, (g.view Dc).deleteSet {u}) := by
      show (d, g1.view Dc1) = _; rw [hdel]
    rw [hlit] at fd fv
    set fst := L.foldl (relaxInsCc ops T B none) ⟨d, g1, Dc1, 0⟩ with hfst
    have hw' : WalkInv fst.d := by rw [fd]; exact foldl_relaxIns_walk B none L _ hw
    have hd' : ∀ z, fst.d z ≤ d0 z := by
      intro z; rw [fd]; exact (foldl_relaxIns_fst_le B none L _ z).trans (hd z)
    have hv' : ∀ y a, fst.g.view fst.Dc y = some a → a ≤ d0 y := by
      rw [fv]
      refine foldl_relaxIns_vals_le L _ hd ?_
      intro y a hy
      simp only [DS.deleteSet] at hy
      split_ifs at hy
      exact hv y a hy
    have hCC' : CallChange g0.fresh B g0.L fst.g.L := by
      have c1 : CallChange g0.fresh B g.L g1.L := by rw [hL1]; exact callChange_clearKeys _ _ _ _
      exact hCC.trans (c1.trans (hCCf.mono hS1.f0_le le_rfl))
    have hT' : ∀ y, fst.g.L y ≠ g0.L y →
        y ∈ insert u U ∨ ∃ a, fst.g.view fst.Dc y = some a ∧ a ≤ d0 y := by
      intro y hy
      by_cases hf : fst.g.L y = g1.L y
      · by_cases hyu : y = u
        · exact Or.inl (hyu ▸ Finset.mem_insert_self _ _)
        · have hg1 : g1.L y = g.L y := by
            rw [hL1]; unfold DB.clearKeys; rw [if_neg (by simp [hyu])]
          have hc0 : g.L y ≠ g0.L y := fun h' => hy (by rw [hf, hg1, h'])
          rcases hT y hc0 with hU | ⟨a, ha, hale⟩
          · exact Or.inl (Finset.mem_insert_of_mem hU)
          · have ha' : ((g.view Dc).deleteSet {u}) y = some a := by
              simp only [DS.deleteSet, Finset.mem_singleton, if_neg hyu]; exact ha
            obtain ⟨a2, ha2, hle2⟩ := foldl_relaxIns_snd_le B none L (d, (g.view Dc).deleteSet {u}) y
              a ha'
            rw [← fv] at ha2
            exact Or.inr ⟨a2, ha2, hle2.trans hale⟩
      · obtain ⟨a, ha, hale⟩ := hTf y hf
        exact Or.inr ⟨a, ha, hale.trans (hd y)⟩
    obtain ⟨⟨c', hc'⟩, hS', hK', hw'', hd'', hv'', hCC'', hT'', hM'⟩ :=
      ih hSf hKf hw' hd' hv' hCC' hT'
    refine ⟨⟨c' + 1 + DC.bext + L.length * (1 + DC.bins), BaseLoopC.step d (g.view Dc) U u val L
      (st'.1, st'.2.1.view st'.2.2.1, st'.2.2.2) c' hval hmin hcard hL ?_⟩,
      hS', hK', hw'', hd'', hv'', hCC'', hT'', ?_⟩
    · have e1 : (L.foldl (relaxIns G s B none) (d, (g.view Dc).deleteSet {u})).1 = fst.d := fd.symm
      have e2 : (L.foldl (relaxIns G s B none) (d, (g.view Dc).deleteSet {u})).2 =
          fst.g.view fst.Dc := fv.symm
      rw [e1, e2]; exact hc'
    · rw [hM', hfst, fold_M]; exact hM1

end basesim


section basesim2

variable {Φ Ω : Type} {T : ℕ} {DC : DCost}

/-- **A base call over the lazy structure simulates the literal base call.** -/
theorem baseD_sim {τ : ℕ → ℕ} {Mf : ℕ → ℕ} (hM1 : ∀ l, 1 ≤ Mf l)
    {Blow B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} {φ0 φ1 : Φ} {g0 gE : DGl G s}
    {res : ResultD G s} {lg : Log G s Ω}
    (hpre : CallPre B S d0) (hK : DB.KeyInj g0.L (kof G s))
    (hab : ∀ v i a, g0.L v = some (i, a) → B ≤ a)
    (hrel : BaseD G s ops T (Mf 0) Blow B S d0 φ0 g0 (τ 0) res φ1 gE lg) :
    ∃ lgC, BaseC G s DC Blow B S d0 φ0 (τ 0) (res.lit gE) φ1 lgC ∧ Log.strip lgC = Log.strip lg ∧
      DPost G s ops B d0 (Mf 0) g0 gE res := by
  obtain ⟨lS, st, c, cf, hlSnd, hlS, hloop, hU, hd, hemp, hnemp, hφ, hlg⟩ := hrel
  obtain ⟨hSnew, hvnew⟩ := new_sim (g := g0) (M := Mf 0) (B := B) (hM1 0) hab
  have hlS' : ∀ y ∈ lS, d0 y < B ∧ kof G s (d0 y) = y := by
    intro y hy
    have hyS : y ∈ S := by rw [← hlS]; exact List.mem_toFinset.mpr hy
    have hlt := hpre.inRange y hyS
    exact ⟨hlt, kof_of_walk hpre.walk (ne_top_of_lt hlt)⟩
  obtain ⟨hvi, hSi, hKi, hmi, hCCi, hTi⟩ :=
    insMany_sim (T := T) d0 lS g0 (newC (Mf 0) B) hSnew hK hlS'
  have hvi' : (insManyC ops T d0 lS g0 (newC (Mf 0) B)).1.view (insManyC ops T d0 lS g0 (newC (Mf 0) B)).2.1 =
      insertMany G s DS.empty S d0 := by rw [hvi, hvnew, hlS]
  have hv0 : ∀ y a, (insManyC ops T d0 lS g0 (newC (Mf 0) B)).1.view
      (insManyC ops T d0 lS g0 (newC (Mf 0) B)).2.1 y = some a → a ≤ d0 y := by
    intro y a hy
    rw [hvi', insertMany_empty_apply] at hy
    split_ifs at hy
    exact le_of_eq (Option.some.inj hy).symm
  have hT0 : ∀ y, (insManyC ops T d0 lS g0 (newC (Mf 0) B)).1.L y ≠ g0.L y →
      y ∈ (∅ : Finset (Fin G.n)) ∨ ∃ a, (insManyC ops T d0 lS g0 (newC (Mf 0) B)).1.view
        (insManyC ops T d0 lS g0 (newC (Mf 0) B)).2.1 y = some a ∧ a ≤ d0 y := by
    intro y hy
    have hyl := hTi y hy
    have hyS : y ∈ S := by rw [← hlS]; exact List.mem_toFinset.mpr hyl
    right
    refine ⟨d0 y, ?_, le_rfl⟩
    rw [hvi', insertMany_empty_apply, if_pos hyS]
  obtain ⟨⟨c', hc'⟩, hS, hK', hw, hd', hv', hCC, hT, hM⟩ :=
    baseLoopD_sim (T := T) (DC := DC) (g0 := g0) (d0 := d0) hloop hSi hKi hpre.walk (fun _ => le_rfl)
      hv0 hCCi hT0
  rw [hvi'] at hc'
  have hM' : st.2.2.1.M = Mf 0 := by rw [hM]; show (insManyC ops T d0 lS g0 (newC (Mf 0) B)).2.1.M = _
                                     rw [insManyC_M]; rfl
  -- the final structure has the loop's view, and the literal minimum
  have hfinal : gE.view res.2.2.1 = st.2.1.view st.2.2.1 ∧
      (¬ (st.2.1.view st.2.2.1).IsEmpty →
        ∃ y, st.2.1.view st.2.2.1 y = some res.1 ∧
          ∀ z v, st.2.1.view st.2.2.1 z = some v → res.1 ≤ v) ∧
      DPost G s ops B d0 (Mf 0) g0 gE res := by
    by_cases he : (st.2.1.view st.2.2.1).IsEmpty
    · obtain ⟨h1, h2, h3, -⟩ := hemp he
      rw [h2, h3]
      refine ⟨rfl, fun h' => absurd he h', ⟨by rw [h2]; exact hS, by rw [h2]; exact hM', hK', hCC, ?_⟩⟩
      intro y hy
      rw [hU, h2]
      exact hT y hy
    · obtain ⟨u, x, g1, Dc1, cp, hpull, hu, h2, h3, -⟩ := hnemp he
      obtain ⟨hPS, -, hS1, hK1, hfr1, hL1, -, -, -, hM1'⟩ := pull_sim hS hK' hpull
      have hlt : res.1 < B := hS.Bd ▸ view_lt_Bd hS.wf hu
      have hkv : kof G s res.1 = u := kof_of_view hK' hu
      obtain ⟨hvn, hSn, hKn, hmn, hfrn, hLn⟩ := ins_sim (T := T) hS1 hK1 hlt hkv
      have hview : (insC ops T g1 Dc1 u res.1).1.view (insC ops T g1 Dc1 u res.1).2.1 =
          st.2.1.view st.2.2.1 := by
        rw [hvn]
        funext y
        unfold DS.insert
        by_cases hyu : y = u
        · subst hyu
          rw [Function.update_self, hPS.rest y, if_pos (by simp)]
          rw [hu]; rfl
        · rw [Function.update_of_ne hyu, hPS.rest y, if_neg (by simp [hyu])]
      have hmin : ∀ z v, st.2.1.view st.2.2.1 z = some v → res.1 ≤ v := by
        intro z v hz
        by_cases hzu : z = u
        · subst hzu; rw [hu] at hz; exact le_of_eq (Option.some.inj hz)
        · have hz' : z ∉ ([u] : List (Fin G.n)).toFinset := by simp [hzu]
          have hux : ∃ v, st.2.1.view st.2.2.1 u = some v ∧ v < x :=
            (hPS.pulled u).mp (by simp)
          obtain ⟨v0, hv0', hv0x⟩ := hux
          rw [hu] at hv0'
          have hres1 : res.1 = v0 := Option.some.inj hv0'
          have : ¬ v < x := fun hlt' => hz' ((hPS.pulled z).mpr ⟨v, hz, hlt'⟩)
          rw [hres1]; exact (hv0x.trans_le (not_lt.mp this)).le
      refine ⟨by rw [h2, h3]; exact hview, fun _ => ⟨u, hu, hmin⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
      · rw [h2, h3]; exact hSn
      · rw [h2, insC_M, hM1', hM']
      · rw [h3]; exact hKn
      · rw [h3]
        have c1 : CallChange g0.fresh B st.2.1.L g1.L := by
          rw [hL1]; exact callChange_clearKeys _ _ _ _
        have c2 : CallChange g0.fresh B g1.L (insC ops T g1 Dc1 u res.1).1.L := by
          intro z
          by_cases hzu : z = u
          · subst hzu
            rcases hLn with h' | h'
            · exact Or.inl h'
            · exact Or.inr (Or.inr ⟨g1.fresh, res.1, hS1.f0_le, hlt, h'⟩)
          · exact Or.inl (hfrn z hzu)
        exact hCC.trans (c1.trans c2)
      · intro y hy
        rw [h3] at hy
        rw [h2, h3, hview]
        by_cases hyu : y = u
        · subst hyu; exact Or.inr ⟨res.1, hu, hv' y res.1 hu⟩
        · have h1' : (insC ops T g1 Dc1 u res.1).1.L y = st.2.1.L y := by
            rw [hfrn y hyu, hL1]; unfold DB.clearKeys; rw [if_neg (by simp [hyu])]
          rw [h1'] at hy
          rw [hU]; exact hT y hy
  obtain ⟨hfv, hfmin, hDP⟩ := hfinal
  refine ⟨[([],
      { lvl := 0, Blow := Blow, B := B, S := S, B' := (res.lit gE).1, U := (res.lit gE).2.1,
        base := true, p := 0, Q := ∅, W := ∅, W' := ∅, J := ∅, Wr := ∅,
        fp := none, cFP := 0, cMerge := 0, cost := S.card * (1 + DC.bins) + c' + 1 })],
    ⟨(st.1, st.2.1.view st.2.2.1, st.2.2.2), c', hc', hU, hfv, hd, ?_, hfmin, hφ, rfl⟩, ?_, hDP⟩
  · intro he; exact (hemp he).1
  · rw [hlg]; rfl

end basesim2


section basedh

variable {Φ Ω : Type} {T : ℕ} {DC : DCost}

/-- The base loop's cost parameters do not affect its transitions. -/
theorem baseLoopC_recost {DC1 DC2 : DCost} {B : WLab G s} {τ : ℕ} :
    ∀ {st st' : Labels G s × DS G s × Finset (Fin G.n)} {c : ℕ},
      BaseLoopC G s DC1 B τ st st' c → ∃ c', BaseLoopC G s DC2 B τ st st' c' := by
  intro st st' c h
  induction h with
  | stop st hst => exact ⟨1, BaseLoopC.stop st hst⟩
  | step d D U u val L st' c hu hmin hcard hL _ ih =>
    obtain ⟨c', h'⟩ := ih
    exact ⟨_, BaseLoopC.step d D U u val L st' c' hu hmin hcard hL h'⟩

/-- **Totality of the literal base loop** (each step extracts a vertex not yet in `U`). -/
theorem baseLoopC_total {DCb : DCost} {B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s}
    (hpre : CallPre B S d0) {τ0 : ℕ} :
    ∀ (n : ℕ) (st : Labels G s × DS G s × Finset (Fin G.n)), τ0 - st.2.2.card ≤ n →
      BInv G s B S d0 st.1 st.2.1 st.2.2 → ∃ st' c, BaseLoopC G s DCb B τ0 st st' c := by
  intro n
  induction n with
  | zero => intro st hn _; exact ⟨st, 1, BaseLoopC.stop st (Or.inr (by omega))⟩
  | succ n ih =>
    intro st hn hB
    classical
    obtain ⟨d, D, U⟩ := st
    have hn' : τ0 - U.card ≤ n + 1 := hn
    by_cases hstop : D.IsEmpty ∨ τ0 ≤ U.card
    · exact ⟨_, 1, BaseLoopC.stop _ hstop⟩
    obtain ⟨hne, hcard'⟩ := not_or.mp hstop
    have hcard : U.card < τ0 := not_le.mp hcard'
    have hkeys : (Finset.univ.filter fun y => D y ≠ none).Nonempty := by
      simp only [DS.IsEmpty, not_forall] at hne
      obtain ⟨y, hy⟩ := hne
      exact ⟨y, by simp [hy]⟩
    obtain ⟨u, hu, humin⟩ := Finset.exists_min_image _ d hkeys
    have huD : D u ≠ none := (Finset.mem_filter.mp hu).2
    obtain ⟨val, hval⟩ := Option.ne_none_iff_exists'.mp huD
    have hmin : ∀ y v, D y = some v → val ≤ v := by
      intro y v hy
      have h1 := (hB.stored u val hval).1
      have h2 := (hB.stored y v hy).1
      rw [h1, h2]
      exact humin y (by simp [hy])
    set L := (Finset.univ.filter fun e => G.src e = u).toList with hLdef
    have hL : Enumerates G L {u} := ⟨Finset.nodup_toList _, by intro e; simp [hLdef]⟩
    have hB' := bInv_step hpre hB hval hmin hL
    have huU : u ∉ U := hB.keysU u val hval
    have hmeas : τ0 - (insert u U).card ≤ n := by
      rw [Finset.card_insert_of_notMem huU]
      omega
    obtain ⟨st', c, hrest⟩ := ih ((L.foldl (relaxIns G s B none) (d, D.deleteSet {u})).1,
      (L.foldl (relaxIns G s B none) (d, D.deleteSet {u})).2, insert u U) hmeas hB'
    exact ⟨st', _, BaseLoopC.step d D U u val L st' c hval hmin hcard hL hrest⟩

/-- The leftover store of a base run is the view of its conversion into a level-0 structure. -/
theorem baseDH_conv {B : WLab G s} {S : Finset (Fin G.n)} {d0 d : Labels G s} {D : DS G s}
    {U : Finset (Fin G.n)} (hB : BInv G s B S d0 d D U) {lK : List (Fin G.n)}
    (hlK : ∀ y, y ∈ lK ↔ D y ≠ none) : insertMany G s DS.empty lK.toFinset d = D := by
  funext y
  rw [insertMany_empty_apply]
  split_ifs with hy
  · have hy' := (hlK y).mp (List.mem_toFinset.mp hy)
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hy'
    rw [hk, (hB.stored y k hk).1]
  · by_contra hne
    exact hy (List.mem_toFinset.mpr ((hlK y).mpr (Ne.symm hne)))

/-- **The heap base case simulates the literal base case.** -/
theorem baseDH_sim {DCb : DCost} {τ : ℕ → ℕ} {Mf : ℕ → ℕ} (hM1 : ∀ l, 1 ≤ Mf l)
    {Blow B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} {φ0 φ1 : Φ} {g0 gE : DGl G s}
    {res : ResultD G s} {lg : Log G s Ω}
    (hpre : CallPre B S d0) (hK : DB.KeyInj g0.L (kof G s))
    (hab : ∀ v i a, g0.L v = some (i, a) → B ≤ a)
    (hrel : BaseDH G s ops DCb T (Mf 0) Blow B S d0 φ0 g0 (τ 0) res φ1 gE lg) :
    ∃ lgC, BaseC G s DC Blow B S d0 φ0 (τ 0) (res.lit gE) φ1 lgC ∧ Log.strip lgC = Log.strip lg ∧
      DPost G s ops B d0 (Mf 0) g0 gE res := by
  obtain ⟨st, c, lK, hloop, hlKnd, hlK, hU, hd, hDc, hgE, hemp, hnemp, hφ, hlg⟩ := hrel
  obtain ⟨hB, -⟩ := baseLoop_inv hpre _ _ (baseLoopC_erase hloop) (bInv_init hpre)
  obtain ⟨c', hloop'⟩ := baseLoopC_recost (DC2 := DC) hloop
  obtain ⟨hSnew, hvnew⟩ := new_sim (ops := ops) (g := g0) (M := Mf 0) (B := B) (hM1 0) hab
  have hlK' : ∀ y ∈ lK, st.1 y < B ∧ kof G s (st.1 y) = y := by
    intro y hy
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp ((hlK y).mp hy)
    obtain ⟨hkd, hkB⟩ := hB.stored y k hk
    rw [hkd] at hkB
    exact ⟨hkB, kof_of_walk hB.walk (ne_top_of_lt hkB)⟩
  obtain ⟨hvi, hSi, hKi, -, hCCi, hTi⟩ :=
    insMany_sim (T := T) st.1 lK g0 (newC (Mf 0) B) hSnew hK hlK'
  have hview : gE.view res.2.2.1 = st.2.1 := by
    rw [hDc, hgE, hvi, hvnew]; exact baseDH_conv hB hlK
  refine ⟨[([],
      { lvl := 0, Blow := Blow, B := B, S := S, B' := (res.lit gE).1,
        U := (res.lit gE).2.1, base := true, p := 0, Q := ∅, W := ∅, W' := ∅, J := ∅, Wr := ∅,
        fp := none, cFP := 0, cMerge := 0, cost := S.card * (1 + DC.bins) + c' + 1 })],
    ⟨st, c', hloop', hU, hview, hd, hemp, hnemp, hφ, rfl⟩, by rw [hlg]; rfl, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hDc, hgE]; exact hSi
  · rw [hDc, insManyC_M]; rfl
  · rw [hgE]; exact hKi
  · rw [hgE]; exact hCCi
  · intro y hy
    rw [hgE] at hy
    have hyl := hTi y hy
    right
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp ((hlK y).mp hyl)
    refine ⟨k, ?_, ?_⟩
    · rw [hview]; exact hk
    · rw [(hB.stored y k hk).1]; exact hB.mono y

/-- **Totality of the heap base case.** -/
theorem baseDH_total {DCb : DCost} {τ : ℕ → ℕ} {Mf : ℕ → ℕ} (hM1 : ∀ l, 1 ≤ Mf l)
    {Blow B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} {φ0 : Φ} {g0 : DGl G s}
    (hpre : CallPre B S d0) (hK : DB.KeyInj g0.L (kof G s))
    (hab : ∀ v i a, g0.L v = some (i, a) → B ≤ a) :
    ∃ (res : ResultD G s) (φ1 : Φ) (gE : DGl G s) (lg : Log G s Ω),
      BaseDH G s ops DCb T (Mf 0) Blow B S d0 φ0 g0 (τ 0) res φ1 gE lg := by
  classical
  obtain ⟨st, c, hloop⟩ := baseLoopC_total (DCb := DCb) hpre (τ0 := τ 0) (τ 0)
    (d0, insertMany G s DS.empty S d0, ∅) (by simp) (bInv_init hpre)
  obtain ⟨hB, -⟩ := baseLoop_inv hpre _ _ (baseLoopC_erase hloop) (bInv_init hpre)
  set lK := (Finset.univ.filter fun y => st.2.1 y ≠ none).toList with hlKdef
  have hlKnd : lK.Nodup := Finset.nodup_toList _
  have hlK : ∀ y, y ∈ lK ↔ st.2.1 y ≠ none := by intro y; simp [hlKdef]
  by_cases he : st.2.1.IsEmpty
  · refine ⟨(B, st.2.2, (insManyC ops T st.1 lK g0 (newC (Mf 0) B)).2.1, st.1), φ0,
      (insManyC ops T st.1 lK g0 (newC (Mf 0) B)).1, _, st, c, lK, hloop, hlKnd, hlK, rfl, rfl, rfl,
      rfl, fun _ => rfl, fun h => absurd he h, rfl, rfl⟩
  · have hkeys : (Finset.univ.filter fun y => st.2.1 y ≠ none).Nonempty := by
      simp only [DS.IsEmpty, not_forall] at he
      obtain ⟨y, hy⟩ := he
      exact ⟨y, by simp [hy]⟩
    obtain ⟨u, hu, humin⟩ := Finset.exists_min_image _ st.1 hkeys
    obtain ⟨val, hval⟩ := Option.ne_none_iff_exists'.mp (Finset.mem_filter.mp hu).2
    have hmin : ∀ z v, st.2.1 z = some v → val ≤ v := by
      intro z v hz
      rw [(hB.stored u val hval).1, (hB.stored z v hz).1]
      exact humin z (by simp [hz])
    refine ⟨(val, st.2.2, (insManyC ops T st.1 lK g0 (newC (Mf 0) B)).2.1, st.1), φ0,
      (insManyC ops T st.1 lK g0 (newC (Mf 0) B)).1, _, st, c, lK, hloop, hlKnd, hlK, rfl, rfl, rfl,
      rfl, fun h => absurd h he, fun _ => ⟨u, hval, hmin⟩, rfl, rfl⟩

end basedh

section levels

variable {Φ Ω : Type} {T : ℕ → ℕ} {DC DCb : DCost}

/-- **Every call over the lazy structure simulates the literal call** (all levels). -/
theorem bmsspD_sim {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} (hFPC : FPCSound G s FPC Inv)
    (τ : ℕ → ℕ) {Mf : ℕ → ℕ} (hMf : ∀ l, ops.mergeM (Mf (l + 1)) (Mf l))
    (hM1 : ∀ l, 1 ≤ Mf l) (hDC : ∀ l, DC.M l = Mf l) :
    ∀ l, SimSub G s ops τ Inv Mf l (BMSSPD G s ops FPC DCb T Mf τ l) (BMSSPC G s FPC DC τ l)
  | 0 => by
    intro Blow B S d φ g res φ' g' lg hpre _ _ _ hK hab hrel
    exact baseDH_sim (T := T 0) hM1 hpre hK hab hrel
  | l + 1 => by
    intro Blow B S d φ g res φ' g' lg hpre hI hlow _ hK hab hrel
    exact callD_sim (T := T (l + 1)) hFPC hMf hM1 (bmsspD_sim hFPC τ hMf hM1 hDC l)
      (bmsspC_log hFPC τ l) (hDC (l + 1)) hpre hI hlow hK hab hrel

/-- The initial global state: empty live map, fresh id 0. -/
def DGl.init : DGl G s := ⟨fun _ => none, 0⟩

/-- **Top-level correctness over the lazy structure.**  A top-level run `BMSSP(⊤, {s}, l)` with
`τ l > n` from the initial labels and the empty global `D` state returns the canonical labels;
its call log agrees (up to cost fields) with a literal log satisfying `LogInv` (call forest,
ranges, counters). -/
theorem bmsspD_top {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} (hFPC : FPCSound G s FPC Inv)
    (τ : ℕ → ℕ) {Mf : ℕ → ℕ} (hMf : ∀ l, ops.mergeM (Mf (l + 1)) (Mf l))
    (hM1 : ∀ l, 1 ≤ Mf l) (l : ℕ) (hτ : G.n < τ l) {Blow : WLab G s}
    (hlow : Blow ≤ initLabels s s) {φ φ' : Φ} (hI : Inv φ) {res : ResultD G s} {gE : DGl G s}
    {lg : Log G s Ω}
    (hrel : BMSSPD G s ops FPC DCb T Mf τ l Blow ⊤ {s} (initLabels s) φ DGl.init res φ' gE lg) :
    (∀ v, Complete res.2.2.2 v) ∧ Inv φ' ∧
      ∃ lgC : Log G s Ω, LogInv τ l lgC ∧ Log.strip lgC = Log.strip lg := by
  let DC0 : DCost := ⟨Mf, fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, 0, 0⟩
  have hlow' : ∀ x ∈ ({s} : Finset (Fin G.n)), Blow ≤ dis (s := s) x := by
    intro x hx
    rw [Finset.mem_singleton.mp hx, ← initLabels_source]
    exact hlow
  have hK0 : DB.KeyInj (DGl.init (G := G) (s := s)).L (kof G s) := by
    intro v i a h; simp [DGl.init] at h
  have hab0 : ∀ v i a, (DGl.init (G := G) (s := s)).L v = some (i, a) → (⊤ : WLab G s) ≤ a := by
    intro v i a h; simp [DGl.init] at h
  obtain ⟨lgC, hC, hstrip, -⟩ := bmsspD_sim (T := T) (DC := DC0) hFPC τ hMf hM1 (fun _ => rfl) l
    Blow ⊤ {s} (initLabels s) φ DGl.init res φ' gE lg callPre_top hI hlow' le_top hK0 hab0 hrel
  obtain ⟨hex, hI', hlog⟩ := bmsspC_top hFPC τ l hτ hlow hI hC
  exact ⟨hex, hI', lgC, hlog, hstrip⟩

end levels



/-! ## Totality (tracker O14): every call has a run -/

section total

variable {Φ Ω : Type} {T : ℕ} {DC : DCost}

/-- Re-selection choices exist (argmins over the remaining group members). -/
theorem exists_reselect {p : ℕ} (σ : LState G s p) (Ui : Finset (Fin G.n)) (d2 : Labels G s) :
    ∃ piv' : Fin p → Fin G.n, Reselect σ Ui d2 piv' := by
  classical
  have key : ∀ j, ∃ x : Fin G.n, (σ.piv j ∈ Ui ∧ (σ.P j \ Ui).Nonempty →
      x ∈ σ.P j \ Ui ∧ ∀ y ∈ σ.P j \ Ui, d2 x ≤ d2 y) ∧
      (¬ (σ.piv j ∈ Ui ∧ (σ.P j \ Ui).Nonempty) → x = σ.piv j) := by
    intro j
    by_cases hc : σ.piv j ∈ Ui ∧ (σ.P j \ Ui).Nonempty
    · obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image (σ.P j \ Ui) d2 hc.2
      exact ⟨x, fun _ => ⟨hx, hmin⟩, fun h => absurd hc h⟩
    · exact ⟨σ.piv j, fun h => absurd h hc, fun _ => rfl⟩
  choose piv' hpiv' using key
  exact ⟨piv', ⟨fun j h1 h2 => (hpiv' j).1 ⟨h1, h2⟩, fun j h => (hpiv' j).2 h⟩⟩

variable {B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {p : ℕ}
  {P0 : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {B'0 : WLab G s}

variable (G s) in
/-- Concrete sub-calls at level `l` exist from every admissible call. -/
def TotalSub (Inv : Φ → Prop) (subD : SubRelD G s Φ Ω) : Prop :=
  ∀ Blow B S d φ g, CallPre B S d → Inv φ → (∀ x ∈ S, Blow ≤ dis (s := s) x) → Blow ≤ B →
    DB.KeyInj g.L (kof G s) → (∀ v i a, g.L v = some (i, a) → B ≤ a) →
    ∃ res φ' g' lg, subD Blow B S d φ g res φ' g' lg

/-- **Loop totality**: from every admissible loop state, the concrete loop has a run (each
iteration strictly grows `U`, and the loop stops once `|U| > τ`). -/
theorem loopD_total (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W)
    {τ : ℕ → ℕ} {Inv : Φ → Prop} {Mf : ℕ → ℕ}
    (hMf : ∀ l, ops.mergeM (Mf (l + 1)) (Mf l))
    {subD : SubRelD G s Φ Ω} {subC : SubRelC G s Φ Ω} {l : ℕ}
    (hsimsub : SimSub G s ops τ Inv Mf l subD subC) (hsubC : GoodSub G s τ Inv l subC)
    (hDC : DC.M (l + 1) = Mf (l + 1)) (hτ1 : 1 ≤ τ l) (hsubT : TotalSub G s Inv subD)
    {g0 : DGl G s} {τl : ℕ} :
    ∀ (n i : ℕ) (cs : CSt G s p) (φ : Φ), τl + 1 - cs.U.card ≤ n →
      LInv G s B S d0 d1 P0 B'0 cs.lit → Inv φ → SInv G s ops B g0.fresh cs.g cs.Dc →
      cs.Dc.M = Mf (l + 1) → DB.KeyInj cs.g.L (kof G s) → CallChange g0.fresh B g0.L cs.g.L →
      (∀ y, cs.g.L y ≠ g0.L y → y ∈ cs.U ∨ ∃ a, cs.g.view cs.Dc y = some a ∧ a ≤ d0 y) →
      ∃ cs' φ' lg J cm c, LoopD G s ops T subD B τl i cs φ cs' φ' lg J cm c := by
  intro n
  induction n with
  | zero =>
    intro i cs φ hn _ _ _ _ _ _ _
    exact ⟨cs, φ, [], ∅, 0, 1, LoopD.stop i cs φ (Or.inl (by omega))⟩
  | succ n ih =>
    intro i cs φ hn h hI hS hMc hK hCC hT
    classical
    by_cases hstop : τl < cs.U.card ∨ (cs.g.view cs.Dc).IsEmpty
    · exact ⟨cs, φ, [], ∅, 0, 1, LoopD.stop i cs φ hstop⟩
    obtain ⟨hcard', hne⟩ := not_or.mp hstop
    have hcard : cs.U.card ≤ τl := not_lt.mp hcard'
    rcases hp : pullC ops T cs.g cs.Dc with ⟨ks, Bi, g1, Dc1, cp⟩
    obtain ⟨hPS, -, -, hK1, -, -, -, -, habove, -⟩ := pull_sim hS hK hp
    have hPS' : PullSpec cs.lit.D B ks.toFinset Bi (g1.view Dc1) := hPS
    have hsp : CallPre Bi (expand cs.lit ks.toFinset Bi) cs.lit.d := step_pre hpre hfp h hPS'
    have hlowdis : ∀ x ∈ expand cs.lit ks.toFinset Bi, cs.lit.B' ≤ dis (s := s) x :=
      fun x hx => (Si_facts h hPS' hx).1.2.2
    have hSne : ks.toFinset.Nonempty := by
      apply hPS'.nonempty
      have hne' : ¬ cs.lit.D.IsEmpty := hne
      simp only [DS.IsEmpty, not_forall] at hne'
      exact hne'
    obtain ⟨x0, hx0⟩ := hSne
    have hx0S : x0 ∈ expand cs.lit ks.toFinset Bi := mem_expand.mpr (Or.inl hx0)
    have hBlt : cs.lit.B' < Bi := by
      obtain ⟨⟨-, -, hB⟩, hlt⟩ := Si_facts h hPS' hx0S
      exact lt_of_le_of_lt (hB.trans (h.walk.sound x0)) hlt
    obtain ⟨⟨B'i, Ui, Dci, d1'⟩, φ1, g2, lg, hsubD⟩ :=
      hsubT cs.B' Bi (expand cs.lit ks.toFinset Bi) cs.d φ g1 hsp hI hlowdis hBlt.le hK1 habove
    obtain ⟨lUi, hlUnd, hlU⟩ : ∃ lU : List (Fin G.n), lU.Nodup ∧ lU.toFinset = Ui :=
      ⟨Ui.toList, Finset.nodup_toList _, Finset.toList_toFinset _⟩
    obtain ⟨L', hnd, hmem⟩ : ∃ L : List (Fin G.m), L.Nodup ∧ ∀ e, e ∈ L ↔
        G.src e ∈ Ui ∧ Bi ≤ ext (d1' (G.src e)) e ∧ ext (d1' (G.src e)) e < B :=
      ⟨(Finset.univ.filter fun e => G.src e ∈ Ui ∧ Bi ≤ ext (d1' (G.src e)) e ∧
          ext (d1' (G.src e)) e < B).toList, Finset.nodup_toList _, by intro e; simp⟩
    obtain ⟨piv', hres⟩ := exists_reselect cs.lit Ui (L'.foldl (relaxInsCc ops T B (some Bi))
      ⟨d1', (delC g2 lUi).1, (ops.merge T Dc1 Dci).1, 0⟩).d
    obtain ⟨lres, hlresnd, hlres⟩ : ∃ lr : List (Fin G.n), lr.Nodup ∧
        lr.toFinset = reselected cs.lit Ui piv' :=
      ⟨_, Finset.nodup_toList _, Finset.toList_toFinset _⟩
    obtain ⟨-, -, -, -, -, -, -, hnext', hI1, hSn', hMn', hKn', hCCn', hTn', hUine, hUi_disj, -, -⟩ :=
      stepD_inv (T := T) (DC := DC) (g0 := g0) hpre hfp hMf hsimsub hsubC hDC h hI hS hMc hK hCC
        hT hne hp hsubD hlU hnd hmem hres hlres
    have hgrow : cs.U.card < (nextD ops T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).U.card := by
      show cs.U.card < (cs.U ∪ Ui).card
      rw [Finset.card_union_of_disjoint (disjoint_comm.mp hUi_disj)]
      have := (hUine hτ1).card_pos
      omega
    have hmeas : τl + 1 - (nextD ops T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).U.card ≤ n := by
      omega
    obtain ⟨cs', φ', lg', J', cm, c, hrest⟩ :=
      ih (i + 1) (nextD ops T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres) φ1 hmeas hnext' hI1
        hSn' hMn' hKn' hCCn' hTn'
    exact ⟨cs', φ', _, _, _, _, LoopD.step i cs cs' φ φ1 φ' ks Bi g1 Dc1 cp B'i Ui Dci d1' g2
      lUi L' piv' lres lg lg' J' cm c hcard hne hp hsubD hlUnd hlU hnd hmem hres hlresnd hlres hrest⟩

end total


section total2

variable {Φ Ω : Type} {T : ℕ} {DC : DCost}

variable (G s) in
/-- A cost-indexed FindPivots relation has a run on every admissible call. -/
def FPCTotal (FPC : FPRelC G s Φ Ω) (Inv : Φ → Prop) : Prop :=
  ∀ l Blow B S d0 φ, CallPre B S d0 → Inv φ →
    ∃ d1 p P Q W φ' ω c, FPC l Blow B S d0 φ d1 p P Q W φ' ω c

/-- **Call totality**. -/
theorem callD_total {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} (hFPC : FPCSound G s FPC Inv)
    (hFPCt : FPCTotal G s FPC Inv)
    {τ : ℕ → ℕ} {Mf : ℕ → ℕ} (hMf : ∀ l, ops.mergeM (Mf (l + 1)) (Mf l)) (hM1 : ∀ l, 1 ≤ Mf l)
    {subD : SubRelD G s Φ Ω} {subC : SubRelC G s Φ Ω} {l : ℕ}
    (hsimsub : SimSub G s ops τ Inv Mf l subD subC) (hsubC : GoodSub G s τ Inv l subC)
    (hDC : DC.M (l + 1) = Mf (l + 1)) (hτ1 : 1 ≤ τ l) (hsubT : TotalSub G s Inv subD)
    {Blow B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} {φ0 : Φ} {g0 : DGl G s}
    (hpre : CallPre B S d0) (hI : Inv φ0) (hlow : ∀ x ∈ S, Blow ≤ dis (s := s) x)
    (hK : DB.KeyInj g0.L (kof G s)) (hab : ∀ v i a, g0.L v = some (i, a) → B ≤ a) :
    ∃ res φ2 gE lg, CallD G s ops FPC T Mf subD (l + 1) Blow B S d0 φ0 g0 (τ (l + 1)) res φ2 gE lg := by
  classical
  have hlow' : ∀ x ∈ S, Blow ≤ d0 x := fun x hx => (hlow x hx).trans (hpre.walk.sound x)
  obtain ⟨d1, p, P, Q, W, φ1, ω, cfp, hfprel⟩ := hFPCt (l + 1) Blow B S d0 φ0 hpre hI
  obtain ⟨hfp, hI1⟩ := hFPC _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpre hI hlow' hfprel
  -- pivots: argmins of the groups
  have hpiv0 : ∀ j, ∃ x, x ∈ P j ∧ ∀ y ∈ P j, d1 x ≤ d1 y := fun j =>
    Finset.exists_min_image (P j) d1 (hfp.groups j).1
  choose piv hpiv using hpiv0
  set lpiv := (Finset.univ.image piv).toList with hlpivdef
  have hlpnd : lpiv.Nodup := Finset.nodup_toList _
  have hlp : lpiv.toFinset = Finset.univ.image piv := Finset.toList_toFinset _
  -- the initial state and its invariants (as in `callD_sim`)
  obtain ⟨hSnew, hvnew⟩ := new_sim (ops := ops) (g := g0) (M := Mf (l + 1)) (B := B) (hM1 _) hab
  have hlp' : ∀ y ∈ lpiv, d1 y < B ∧ kof G s (d1 y) = y := by
    intro y hy
    have hy' : y ∈ Finset.univ.image piv := by rw [← hlp]; exact List.mem_toFinset.mpr hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy'
    have hS : piv j ∈ S := (hfp.groups j).2 (hpiv j).1
    have hlt : d1 (piv j) < B := lt_of_le_of_lt (hfp.le _) (hpre.inRange _ hS)
    exact ⟨hlt, kof_of_walk hfp.walk (ne_top_of_lt hlt)⟩
  obtain ⟨hvi, hSi, hKi, -, hCCi, hTi⟩ :=
    insMany_sim (T := T) d1 lpiv g0 (newC (Mf (l + 1)) B) hSnew hK hlp'
  set cs0 : CSt G s p :=
    { d := d1, P := P, piv := piv, U := ∅, B' := initB' B d1 piv,
      g := (initD ops T (Mf (l + 1)) B d1 lpiv g0).1,
      Dc := (initD ops T (Mf (l + 1)) B d1 lpiv g0).2.1 } with hcs0def
  have hcs0 : cs0.lit = initState B d1 P piv := by
    show
      ({ d := d1, D := (insManyC ops T d1 lpiv g0 (newC (Mf (l + 1)) B)).1.view
           (insManyC ops T d1 lpiv g0 (newC (Mf (l + 1)) B)).2.1,
         P := P, piv := piv, U := ∅, B' := initB' B d1 piv } : LState G s p) = _
    rw [hvi, hvnew, hlp]; rfl
  have hpiv' : ∀ j, piv j ∈ P j ∧ ∀ x ∈ P j, d1 (piv j) ≤ d1 x := fun j => hpiv j
  have h0 := linv_init hpre hfp hpiv'
  rw [← hcs0] at h0
  have hM0 : cs0.Dc.M = Mf (l + 1) := by
    show (insManyC ops T d1 lpiv g0 (newC (Mf (l + 1)) B)).2.1.M = _
    rw [insManyC_M]; rfl
  have hT0 : ∀ y, cs0.g.L y ≠ g0.L y → y ∈ cs0.U ∨ ∃ a, cs0.g.view cs0.Dc y = some a ∧ a ≤ d0 y := by
    intro y hy
    have hyl := hTi y hy
    right
    refine ⟨d1 y, ?_, hfp.le y⟩
    show (insManyC ops T d1 lpiv g0 (newC (Mf (l + 1)) B)).1.view
      (insManyC ops T d1 lpiv g0 (newC (Mf (l + 1)) B)).2.1 y = some (d1 y)
    rw [hvi, hvnew, insertMany_apply, if_pos (List.mem_toFinset.mpr hyl)]
    rfl
  -- the loop
  obtain ⟨cs, φ2, lgc, J, cm, cl, hloop⟩ :=
    loopD_total (T := T) (DC := DC) (g0 := g0) (τl := τ (l + 1)) hpre hfp hMf hsimsub hsubC hDC hτ1
      hsubT (τ (l + 1) + 1) 0 cs0 φ1 (by omega) h0 hI1 hSi hM0 hKi hCCi hT0
  -- the finalization choices
  set B'f : WLab G s := if (cs.g.view cs.Dc).IsEmpty then B else cs.B' with hB'fdef
  have hB'e : (cs.g.view cs.Dc).IsEmpty → B'f = B := fun he => by rw [hB'fdef, if_pos he]
  have hB'n : ¬ (cs.g.view cs.Dc).IsEmpty → B'f = cs.B' := fun he => by rw [hB'fdef, if_neg he]
  set lT6 := (S.filter fun x => B'f ≤ cs.d x ∧ cs.d x < B).toList with hlT6def
  have hT6nd : lT6.Nodup := Finset.nodup_toList _
  have hT6 : ∀ x, x ∈ lT6 ↔ x ∈ S ∧ B'f ≤ cs.d x ∧ cs.d x < B := by
    intro x; rw [hlT6def, Finset.mem_toList, Finset.mem_filter]
  set W' := W.filter fun x => x ∉ cs.U ∧ cs.d x < B'f with hW'def
  have hW' : ∀ x, x ∈ W' ↔ (x ∈ W ∧ x ∉ cs.U) ∧ cs.d x < B'f := by
    intro x; rw [hW'def, Finset.mem_filter, and_assoc]
  set L := (Finset.univ.filter fun e => G.src e ∈ W').toList with hLdef
  have hL : Enumerates G L W' := ⟨Finset.nodup_toList _, by intro e; simp [hLdef]⟩
  set lW' := W'.toList with hlW'def
  have hlWnd : lW'.Nodup := Finset.nodup_toList _
  have hlW : lW'.toFinset = W' := Finset.toList_toFinset _
  exact ⟨_, φ2, _, _, d1, p, P, Q, W, φ1, ω, cfp, piv, lpiv, cs, lgc, J, cm, cl, L, B'f, lT6, W', lW',
    hfprel, hpiv', hlpnd, hlp, hloop, hB'e, hB'n, hT6nd, hT6, hW', hL, hlWnd, hlW, rfl, rfl, rfl⟩

end total2


section total3

variable {Φ Ω : Type} {T : ℕ} {DC : DCost}

/-- With `M = 1`, a pull of a nonempty structure returns exactly one key. -/
theorem pull_single {B : WLab G s} {f0 : ℕ} {g : DGl G s} {Dc : DStrM G s}
    (hS : SInv G s ops B f0 g Dc) (hK : DB.KeyInj g.L (kof G s)) (hM : Dc.M = 1)
    (hne : ¬ (g.view Dc).IsEmpty) : ∃ u, (pullC ops T g Dc).1 = [u] := by
  obtain ⟨hlen, -, hne', -, -⟩ := ops.pull_post T hS.wf hK hS.ids hS.M1
  have hk : ∃ y, DB.HasKey g.L Dc y := by
    simp only [DS.IsEmpty, not_forall] at hne
    obtain ⟨y, hy⟩ := hne
    exact ⟨y, view_ne_none_iff.mp hy⟩
  have h1 := hne' hk
  have h2 : (ops.pull T g.L Dc).1.length = 1 := by
    have := List.length_pos_of_ne_nil h1
    rw [hM] at hlen
    omega
  exact List.length_eq_one_iff.mp h2

/-- **Base-loop totality** (`M = 1`): each step extracts a vertex not yet in `U`. -/
theorem baseLoopD_total {B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s}
    (hpre : CallPre B S d0) {τ0 : ℕ} {f0 : ℕ} :
    ∀ (n : ℕ) (st : Labels G s × DGl G s × DStrM G s × Finset (Fin G.n)),
      τ0 - st.2.2.2.card ≤ n → BInv G s B S d0 st.1 (st.2.1.view st.2.2.1) st.2.2.2 →
      SInv G s ops B f0 st.2.1 st.2.2.1 → st.2.2.1.M = 1 → DB.KeyInj st.2.1.L (kof G s) →
      ∃ st' c, BaseLoopD G s ops T B τ0 st st' c := by
  intro n
  induction n with
  | zero =>
    intro st hn _ _ _ _
    exact ⟨st, 1, BaseLoopD.stop st (Or.inr (by omega))⟩
  | succ n ih =>
    intro st hn hB hS hM hK
    classical
    obtain ⟨d, g, Dc, U⟩ := st
    have hn' : τ0 - U.card ≤ n + 1 := hn
    by_cases hstop : (g.view Dc).IsEmpty ∨ τ0 ≤ U.card
    · exact ⟨_, 1, BaseLoopD.stop _ hstop⟩
    obtain ⟨hne, hcard'⟩ := not_or.mp hstop
    have hcard : U.card < τ0 := not_le.mp hcard'
    obtain ⟨u, hu⟩ := pull_single (T := T) hS hK hM hne
    rcases hp : pullC ops T g Dc with ⟨ks, x, g1, Dc1, cp⟩
    have hks : ks = [u] := by rw [← hu, hp]
    subst hks
    obtain ⟨hPS, -, hS1, hK1, -, -, -, -, -, hM1⟩ := pull_sim hS hK hp
    obtain ⟨val, hval, hvx⟩ := (hPS.pulled u).mp (by simp)
    have hmin : ∀ y v, g.view Dc y = some v → val ≤ v := by
      intro y v hy
      by_cases hyu : y = u
      · subst hyu; rw [hval] at hy; exact le_of_eq (Option.some.inj hy)
      · have hy' : y ∉ ([u] : List (Fin G.n)).toFinset := by simp [hyu]
        have : ¬ v < x := fun hlt => hy' ((hPS.pulled y).mpr ⟨v, hy, hlt⟩)
        exact (hvx.trans_le (not_lt.mp this)).le
    have hdel : (g.view Dc).deleteSet {u} = g1.view Dc1 := by
      funext y
      rw [hPS.rest y]
      simp [DS.deleteSet]
    set L := (Finset.univ.filter fun e => G.src e = u).toList with hLdef
    have hL : Enumerates G L {u} := ⟨Finset.nodup_toList _, by intro e; simp [hLdef]⟩
    obtain ⟨fd, fv, hSf, hKf, -, -, -⟩ := fold_sim (T := T) none L ⟨d, g1, Dc1, 0⟩ hS1 hK1 hB.walk
    have hlit : ((⟨d, g1, Dc1, 0⟩ : RSt G s).d,
        (⟨d, g1, Dc1, 0⟩ : RSt G s).g.view (⟨d, g1, Dc1, 0⟩ : RSt G s).Dc) =
        (d, (g.view Dc).deleteSet {u}) := by
      show (d, g1.view Dc1) = _; rw [hdel]
    rw [hlit] at fd fv
    have hB' := bInv_step hpre hB hval hmin hL
    rw [← fd, ← fv] at hB'
    have huU : u ∉ U := hB.keysU u val hval
    have hM' : (L.foldl (relaxInsCc ops T B none) ⟨d, g1, Dc1, 0⟩).Dc.M = 1 := by
      rw [fold_M]; show Dc1.M = 1; rw [hM1, hM]
    obtain ⟨st', c, hrest⟩ := ih ((L.foldl (relaxInsCc ops T B none) ⟨d, g1, Dc1, 0⟩).d,
      (L.foldl (relaxInsCc ops T B none) ⟨d, g1, Dc1, 0⟩).g,
      (L.foldl (relaxInsCc ops T B none) ⟨d, g1, Dc1, 0⟩).Dc, insert u U)
      (by
        show τ0 - (insert u U).card ≤ n
        rw [Finset.card_insert_of_notMem huU]
        exact (by omega))
      hB' hSf hM' hKf
    exact ⟨st', _, BaseLoopD.step d g Dc U u x g1 Dc1 cp L st' c hp hcard hL hrest⟩

/-- **Base-call totality** (level-0 structure with `M = 1`). -/
theorem baseD_total {τ : ℕ → ℕ} {Mf : ℕ → ℕ} (hM0 : Mf 0 = 1)
    {Blow B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} {φ0 : Φ} {g0 : DGl G s}
    (hpre : CallPre B S d0) (hK : DB.KeyInj g0.L (kof G s))
    (hab : ∀ v i a, g0.L v = some (i, a) → B ≤ a) :
    ∃ (res : ResultD G s) (φ1 : Φ) (gE : DGl G s) (lg : Log G s Ω),
      BaseD G s ops T (Mf 0) Blow B S d0 φ0 g0 (τ 0) res φ1 gE lg := by
  classical
  set lS := S.toList with hlSdef
  have hlSnd : lS.Nodup := Finset.nodup_toList _
  have hlS : lS.toFinset = S := Finset.toList_toFinset _
  obtain ⟨hSnew, hvnew⟩ := new_sim (ops := ops) (g := g0) (M := Mf 0) (B := B) (by rw [hM0]) hab
  have hlS' : ∀ y ∈ lS, d0 y < B ∧ kof G s (d0 y) = y := by
    intro y hy
    have hyS : y ∈ S := by rw [← hlS]; exact List.mem_toFinset.mpr hy
    have hlt := hpre.inRange y hyS
    exact ⟨hlt, kof_of_walk hpre.walk (ne_top_of_lt hlt)⟩
  obtain ⟨hvi, hSi, hKi, -, -, -⟩ :=
    insMany_sim (T := T) d0 lS g0 (newC (Mf 0) B) hSnew hK hlS'
  have hvi' : (insManyC ops T d0 lS g0 (newC (Mf 0) B)).1.view
      (insManyC ops T d0 lS g0 (newC (Mf 0) B)).2.1 = insertMany G s DS.empty S d0 := by
    rw [hvi, hvnew, hlS]
  have hB0 : BInv G s B S d0 d0 ((insManyC ops T d0 lS g0 (newC (Mf 0) B)).1.view
      (insManyC ops T d0 lS g0 (newC (Mf 0) B)).2.1) ∅ := by
    rw [hvi']; exact bInv_init hpre
  have hMi : (insManyC ops T d0 lS g0 (newC (Mf 0) B)).2.1.M = 1 := by
    rw [insManyC_M]; exact hM0
  obtain ⟨st, c, hloop⟩ := baseLoopD_total (T := T) hpre (τ0 := τ 0) (τ 0)
    (d0, (insManyC ops T d0 lS g0 (newC (Mf 0) B)).1, (insManyC ops T d0 lS g0 (newC (Mf 0) B)).2.1,
      ∅) (by simp) hB0 hSi hMi hKi
  -- the final invariants
  obtain ⟨-, hS, hK', -, -, -, -, -, hM⟩ :=
    baseLoopD_sim (T := T) (DC := ⟨fun _ => 1, fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0,
      fun _ _ => 0, 0, 0⟩) (g0 := g0) (d0 := d0) hloop hSi hKi hpre.walk (fun _ => le_rfl)
      (by
        intro y a hy
        rw [hvi', insertMany_empty_apply] at hy
        split_ifs at hy
        exact le_of_eq (Option.some.inj hy).symm)
      (by
        obtain ⟨-, -, -, -, h5, -⟩ := insMany_sim (T := T) d0 lS g0 (newC (Mf 0) B) hSnew hK hlS'
        exact h5)
      (by
        intro y hy
        obtain ⟨-, -, -, -, -, h6⟩ := insMany_sim (T := T) d0 lS g0 (newC (Mf 0) B) hSnew hK hlS'
        have hyl := h6 y hy
        have hyS : y ∈ S := by rw [← hlS]; exact List.mem_toFinset.mpr hyl
        right
        refine ⟨d0 y, ?_, le_rfl⟩
        rw [hvi', insertMany_empty_apply, if_pos hyS])
  have hM1 : st.2.2.1.M = 1 := by rw [hM]; exact hMi
  by_cases he : (st.2.1.view st.2.2.1).IsEmpty
  · refine ⟨(B, st.2.2.2, st.2.2.1, st.1), φ0, st.2.1, _, lS, st, c, 0, hlSnd, hlS, hloop, rfl, rfl,
      fun _ => ⟨rfl, rfl, rfl, rfl⟩, fun h => absurd he h, rfl, rfl⟩
  · obtain ⟨u, hu⟩ := pull_single (T := T) hS hK' hM1 he
    rcases hp : pullC ops T st.2.1 st.2.2.1 with ⟨ks, x, g1, Dc1, cp⟩
    have hks : ks = [u] := by rw [← hu, hp]
    subst hks
    obtain ⟨hPS, -, -, -, -, -, -, -, -, -⟩ := pull_sim hS hK' hp
    obtain ⟨v, hv, -⟩ := (hPS.pulled u).mp (by simp)
    refine ⟨(v, st.2.2.2, (insC ops T g1 Dc1 u v).2.1, st.1), φ0, (insC ops T g1 Dc1 u v).1, _, lS, st,
      c, cp + (insC ops T g1 Dc1 u v).2.2, hlSnd, hlS, hloop, rfl, rfl, fun h => absurd h he,
      fun _ => ⟨u, x, g1, Dc1, cp, hp, hv, rfl, rfl, rfl⟩, rfl, rfl⟩

end total3

section total4

variable {Φ Ω : Type} {T : ℕ → ℕ} {DCb : DCost}

/-- **Totality (tracker O14)**: every admissible call of the concrete relation has a run, at every
level (for `τ l ≥ 1`, base parameter `M = 1`, and a total FindPivots relation). -/
theorem bmsspD_total {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} (hFPC : FPCSound G s FPC Inv)
    (hFPCt : FPCTotal G s FPC Inv) (τ : ℕ → ℕ) (hτ : ∀ l, 1 ≤ τ l) {Mf : ℕ → ℕ}
    (hMf : ∀ l, ops.mergeM (Mf (l + 1)) (Mf l)) (hM1 : ∀ l, 1 ≤ Mf l) :
    ∀ l, TotalSub G s Inv (BMSSPD G s ops FPC DCb T Mf τ l (Ω := Ω))
  | 0 => by
    intro Blow B S d φ g hpre _ _ _ hK hab
    let DC0 : DCost := ⟨Mf, fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, 0, 0⟩
    exact baseDH_total (T := T 0) (τ := τ) hM1 hpre hK hab
  | l + 1 => by
    intro Blow B S d φ g hpre hI hlow _ hK hab
    let DC0 : DCost := ⟨Mf, fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, 0, 0⟩
    exact callD_total (T := T (l + 1)) (DC := DC0) hFPC hFPCt hMf hM1
      (bmsspD_sim (DC := DC0) (DCb := DCb) hFPC τ hMf hM1 (fun _ => rfl) l) (bmsspC_log hFPC τ l) rfl (hτ l)
      (bmsspD_total hFPC hFPCt τ hτ hMf hM1 l) hpre hI hlow hK hab

/-- **The top-level run exists** (from the initial labels and the empty global state). -/
theorem bmsspD_top_exists {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} (hFPC : FPCSound G s FPC Inv)
    (hFPCt : FPCTotal G s FPC Inv) (τ : ℕ → ℕ) (hτ : ∀ l, 1 ≤ τ l) {Mf : ℕ → ℕ}
    (hMf : ∀ l, ops.mergeM (Mf (l + 1)) (Mf l)) (hM1 : ∀ l, 1 ≤ Mf l) (l : ℕ)
    {Blow : WLab G s} (hlow : Blow ≤ initLabels s s) {φ : Φ} (hI : Inv φ) :
    ∃ (res : ResultD G s) (φ' : Φ) (gE : DGl G s) (lg : Log G s Ω),
      BMSSPD G s ops FPC DCb T Mf τ l Blow ⊤ {s} (initLabels s) φ DGl.init res φ' gE lg := by
  have hlow' : ∀ x ∈ ({s} : Finset (Fin G.n)), Blow ≤ dis (s := s) x := by
    intro x hx
    rw [Finset.mem_singleton.mp hx, ← initLabels_source]
    exact hlow
  have hK0 : DB.KeyInj (DGl.init (G := G) (s := s)).L (kof G s) := by
    intro v i a h; simp [DGl.init] at h
  have hab0 : ∀ v i a, (DGl.init (G := G) (s := s)).L v = some (i, a) → (⊤ : WLab G s) ≤ a := by
    intro v i a h; simp [DGl.init] at h
  exact bmsspD_total hFPC hFPCt τ hτ hMf hM1 l Blow ⊤ {s} (initLabels s) φ DGl.init
    callPre_top hI hlow' le_top hK0 hab0

end total4

/-! ## The DBlocks instance (agent-04's L3-3 structure) -/

section dbinst

variable (T : ℕ)

theorem dbInsert_L (L : LiveM G s) (fresh : ℕ) (D : DStrM G s) (v : Fin G.n) (lam : WLab G s) :
    (DB.insert T L fresh D v lam).1 =
      if DB.skipIns L v lam then L else Function.update L v (some (fresh, lam)) := by
  unfold DB.insert; split_ifs <;> rfl

theorem dbInsert_fresh (L : LiveM G s) (fresh : ℕ) (D : DStrM G s) (v : Fin G.n)
    (lam : WLab G s) :
    (DB.insert T L fresh D v lam).2.1 = if DB.skipIns L v lam then fresh else fresh + 1 := by
  unfold DB.insert; split_ifs <;> rfl

theorem dbInsert_ents (L : LiveM G s) (fresh : ℕ) (D : DStrM G s) (v : Fin G.n)
    (lam : WLab G s) :
    ∀ x ∈ DB.allEnts (DB.insert T L fresh D v lam).2.2.1.blocks,
      x ∈ DB.allEnts D.blocks ∨ x = ⟨fresh, v, lam⟩ := by
  intro x hx
  unfold DB.insert at hx
  split_ifs at hx
  · exact Or.inl hx
  · exact DB.mem_allEnts_addTo T hx

theorem dbPull_ents (L : LiveM G s) (D : DStrM G s) :
    ∀ x ∈ DB.allEnts (DB.pull T L D).2.2.2.1.blocks, x ∈ DB.allEnts D.blocks := by
  unfold DB.pull
  obtain ⟨pre, hbs, hacc, -, -, -, -⟩ := DB.collect_spec L D.M D.blocks []
  simp only [List.nil_append] at hacc
  split_ifs with hsmall
  · intro x hx; simp [DB.allEnts] at hx
  · intro x hx
    simp only [DB.allEnts, List.map_cons, List.flatten_cons, List.mem_append] at hx
    have hsplit : DB.allEnts D.blocks = DB.allEnts pre ++ DB.allEnts (DB.collect L D.M [] D.blocks).2.1 := by
      conv_lhs => rw [hbs]
      simp [DB.allEnts]
    rw [hsplit, List.mem_append]
    rcases hx with hx | hx
    · left
      have h1 := (List.mem_filter.mp hx).1
      rw [hacc] at h1
      exact (DB.liveVals_sublist_allEnts L pre).subset h1
    · right; exact hx

theorem dbMerge_ents (D D' : DStrM G s) :
    ∀ x ∈ DB.allEnts (DB.merge T D D').1.blocks, x ∈ DB.allEnts D.blocks ∨ x ∈ DB.allEnts D'.blocks := by
  intro x hx
  unfold DB.merge at hx
  rcases hD : D.blocks with _ | ⟨f, rest⟩
  · rw [hD] at hx
    dsimp only at hx
    rw [hD] at hx
    exact Or.inl hx
  · rw [hD] at hx
    simp only [DB.allEnts, List.map_append, List.flatten_append, List.mem_append] at hx
    rcases hx with hx | hx
    · right
      have := (DB.mem_allEnts_groupAux (g := D.M / 3) (cur := none) (bs := D'.blocks)).mp hx
      simpa using this
    · left
      split_ifs at hx
      · simp only [List.map_cons, List.flatten_cons, List.mem_append] at hx
        simp only [DB.allEnts, List.map_cons, List.flatten_cons, List.mem_append]
        exact hx
      · simp only [DB.allEnts, List.map_cons, List.flatten_cons, List.mem_append]
        exact Or.inr hx


/-- Live entries with distinct ids have distinct keys. -/
theorem keys_nodup_of_live {L : LiveM G s} {l : List (DB.Entry (Fin G.n) (WLab G s))}
    (hid : (l.map (·.id)).Nodup) (hl : ∀ e ∈ l, e.IsLive L) : (l.map (·.key)).Nodup := by
  refine List.Nodup.map_on ?_ (List.Nodup.of_map _ hid)
  intro x hx y hy hxy
  obtain ⟨h1, h2⟩ := DB.live_key_unique (hl x hx) (hl y hy) hxy
  cases x; cases y
  simp only at h1 h2 hxy
  subst h1 h2 hxy
  rfl

theorem dbPull_nodup {L : LiveM G s} {D : DStrM G s} (hid : DB.IdsNodup D) :
    (DB.pull T L D).1.Nodup := by
  unfold DB.pull
  obtain ⟨pre, hbs, hacc, -, -, -, -⟩ := DB.collect_spec L D.M D.blocks []
  simp only [List.nil_append] at hacc
  have hacc_nodup : ((DB.collect L D.M [] D.blocks).1.map (·.id)).Nodup := by
    rw [hacc]
    have hsplit : (DB.allEnts D.blocks).map (·.id) =
        (DB.allEnts pre).map (·.id) ++ (DB.allEnts (DB.collect L D.M [] D.blocks).2.1).map (·.id) := by
      conv_lhs => rw [hbs]
      simp [DB.allEnts]
    have hid' := hid
    unfold DB.IdsNodup at hid'
    rw [hsplit] at hid'
    exact ((DB.liveVals_sublist_allEnts L pre).map _).nodup (List.nodup_append.mp hid').1
  have hlive : ∀ e ∈ (DB.collect L D.M [] D.blocks).1, e.IsLive L := by
    intro e he; rw [hacc] at he; exact (DB.mem_liveVals.mp he).2
  split_ifs
  · exact keys_nodup_of_live hacc_nodup hlive
  · exact keys_nodup_of_live ((List.filter_sublist.map _).nodup hacc_nodup)
      (fun e he => hlive e (List.mem_of_mem_filter he))

theorem dbInsert_M (L : LiveM G s) (fresh : ℕ) (D : DStrM G s) (v : Fin G.n) (lam : WLab G s) :
    (DB.insert T L fresh D v lam).2.2.1.M = D.M ∧ (DB.insert T L fresh D v lam).2.2.1.Bd = D.Bd := by
  unfold DB.insert; split_ifs <;> exact ⟨rfl, rfl⟩

theorem dbMerge_M (D D' : DStrM G s) :
    (DB.merge T D D').1.M = D.M ∧ (DB.merge T D D').1.Bd = D.Bd := by
  unfold DB.merge; split <;> exact ⟨rfl, rfl⟩

end dbinst

variable (G s) in
/-- **agent-04's `DBlocks` (L3-3) as a `D` implementation.** -/
noncomputable def dbOps : DOps G s where
  SzOK := DB.BlockSizeOK
  mergeM M M' := M / 3 + (2 * M' + 1) ≤ M + 1
  pull T L D := DB.pull T L D
  insert T L fresh D v lam := DB.insert T L fresh D v lam
  merge T D D' := DB.merge T D D'
  sz_new M Bd := by intro b hb; simp at hb; rw [hb]; simp
  pull_spec T _ _ hwf := DB.pull_spec T hwf
  pull_post T _ _ _ hwf hK hid hM := DB.pull_post T hwf hK hid hM
  pull_aux T _ _ _ _ hwf hK hid hM hsz hfr := DB.pull_aux T hwf hK hid hM hsz hfr
  pull_ents T L D := dbPull_ents T L D
  pull_nodup T _ _ hid := dbPull_nodup T hid
  insert_spec T _ _ _ _ _ hwf hfr hB hdisc := by
    obtain ⟨a, b, c, d, -, -, -⟩ := DB.insert_spec T hwf hfr hB hdisc
    exact ⟨a, b, c, d⟩
  insert_aux T _ _ _ _ _ _ hfr hid hK hkv hsz hM := DB.insert_aux T hfr hid hK hkv hsz hM
  insert_L T L fresh D v lam := dbInsert_L T L fresh D v lam
  insert_ents T L fresh D v lam := dbInsert_ents T L fresh D v lam
  insert_M T L fresh D v lam := dbInsert_M T L fresh D v lam
  merge_spec T _ _ _ hwf hwf' h1 h2 h0 := by
    obtain ⟨a, b, c, -, -⟩ := DB.merge_spec T hwf hwf' h1 h2 h0
    exact ⟨a, b, c⟩
  merge_aux T _ _ _ hne hid hid' hd hsz hsz' hMM hfr hfr' :=
    DB.merge_aux T hne hid hid' hd hsz hsz' hMM hfr hfr'
  merge_ents T D D' := dbMerge_ents T D D'
  merge_M T D D' := dbMerge_M T D D'


/-! ## The DLazy instance (agent-04's L3-4 structure: lazy splits, sorted block stack) -/

section dlinst

theorem dlPull_ents (L : LiveM G s) (D : DStrM G s) :
    ∀ x ∈ DB.allEnts (DL.pullL 1 L D).2.2.2.1.blocks, x ∈ DB.allEnts D.blocks := by
  intro x hx
  rw [DL.pullL_eq] at hx
  have h1 := dbPull_ents 1 L (DL.prepD L D) x hx
  exact (DL.prepList_subperm L D.M 0 D.blocks).subset h1

theorem dlInsert_L (L : LiveM G s) (fresh : ℕ) (D : DStrM G s) (v : Fin G.n) (lam : WLab G s) :
    (DL.insertL L fresh D v lam).1 =
      if DB.skipIns L v lam then L else Function.update L v (some (fresh, lam)) :=
  dbInsert_L 0 L fresh { D with M := DL.bigM D } v lam

theorem dlInsert_ents (L : LiveM G s) (fresh : ℕ) (D : DStrM G s) (v : Fin G.n) (lam : WLab G s) :
    ∀ x ∈ DB.allEnts (DL.insertL L fresh D v lam).2.2.1.blocks,
      x ∈ DB.allEnts D.blocks ∨ x = ⟨fresh, v, lam⟩ :=
  dbInsert_ents 0 L fresh { D with M := DL.bigM D } v lam

theorem dlInsert_M (L : LiveM G s) (fresh : ℕ) (D : DStrM G s) (v : Fin G.n) (lam : WLab G s) :
    (DL.insertL L fresh D v lam).2.2.1.M = D.M ∧ (DL.insertL L fresh D v lam).2.2.1.Bd = D.Bd :=
  ⟨rfl, (dbInsert_M 0 L fresh { D with M := DL.bigM D } v lam).2⟩

end dlinst

variable (G s) in
/-- **agent-04's `DLazy` (L3-4: lazy front splits, sorted block stack) as a `D` implementation**:
`pull = pullL 1`, `insert = insertL` (binary search, no split), `merge = DB.merge 1`.  No size
invariant and no parameter relation are needed. -/
noncomputable def dlOps : DOps G s where
  SzOK _ := True
  mergeM _ _ := True
  pull _ L D := DL.pullL 1 L D
  insert _ L fresh D v lam := DL.insertL L fresh D v lam
  merge _ D D' := DB.merge 1 D D'
  sz_new _ _ := trivial
  pull_spec _ _ _ hwf := DL.pullL_spec 1 hwf
  pull_post _ _ _ _ hwf hK hid hM := DL.pullL_post 1 hwf hK hid hM
  pull_aux _ _ _ _ _ _ hK hid _ _ hfr := by
    obtain ⟨a, b, c⟩ := DL.pullL_aux hK hid hfr
    exact ⟨a, trivial, b, c⟩
  pull_ents _ L D := dlPull_ents L D
  pull_nodup _ _ _ hid := by
    rw [DL.pullL_eq]
    exact dbPull_nodup 1 (DL.idsNodup_prepD hid)
  insert_spec _ _ _ _ _ _ hwf hfr hB hdisc := by
    obtain ⟨a, b, c, d, -, -, -⟩ := DL.insertL_spec hwf hfr hB hdisc
    exact ⟨a, b, c, d⟩
  insert_aux _ _ _ _ _ _ _ hfr hid hK hkv _ _ := by
    obtain ⟨a, b⟩ := DL.insertL_aux hfr hid hK hkv
    exact ⟨a, trivial, b⟩
  insert_L _ L fresh D v lam := dlInsert_L L fresh D v lam
  insert_ents _ L fresh D v lam := dlInsert_ents L fresh D v lam
  insert_M _ L fresh D v lam := dlInsert_M L fresh D v lam
  merge_spec _ _ _ _ hwf hwf' h1 h2 h0 := by
    obtain ⟨a, b, c, -, -⟩ := DB.merge_spec 1 hwf hwf' h1 h2 h0
    exact ⟨a, b, c⟩
  merge_aux _ _ _ _ hne hid hid' hd _ _ _ hfr hfr' := by
    obtain ⟨a, b⟩ := DL.merge_ids 1 hne hid hid' hd hfr hfr'
    exact ⟨a, trivial, b⟩
  merge_ents _ D D' := dbMerge_ents 1 D D'
  merge_M _ D D' := dbMerge_M 1 D D'


/-! ## The final Layer-A statements over `DLazy` -/

section dlfinal

variable {Φ Ω : Type} {T : ℕ → ℕ} {DCb : DCost}

/-- **Over agent-04's DLazy**: every top-level run is exact, preserves the persistent invariant,
and its log agrees (up to costs) with a literal log satisfying `LogInv`. -/
theorem bmsspDL_top {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} (hFPC : FPCSound G s FPC Inv)
    (τ : ℕ → ℕ) {Mf : ℕ → ℕ} (hM1 : ∀ l, 1 ≤ Mf l) (l : ℕ) (hτ : G.n < τ l) {Blow : WLab G s}
    (hlow : Blow ≤ initLabels s s) {φ φ' : Φ} (hI : Inv φ) {res : ResultD G s} {gE : DGl G s}
    {lg : Log G s Ω}
    (hrel : BMSSPD G s (dlOps G s) FPC DCb T Mf τ l Blow ⊤ {s} (initLabels s) φ DGl.init res φ' gE lg) :
    (∀ v, Complete res.2.2.2 v) ∧ Inv φ' ∧
      ∃ lgC : Log G s Ω, LogInv τ l lgC ∧ Log.strip lgC = Log.strip lg :=
  bmsspD_top hFPC τ (fun _ => trivial) hM1 l hτ hlow hI hrel

/-- **Over agent-04's DLazy**: the top-level run exists. -/
theorem bmsspDL_top_exists {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} (hFPC : FPCSound G s FPC Inv)
    (hFPCt : FPCTotal G s FPC Inv) (τ : ℕ → ℕ) (hτ : ∀ l, 1 ≤ τ l) {Mf : ℕ → ℕ}
    (hM1 : ∀ l, 1 ≤ Mf l) (l : ℕ) {Blow : WLab G s}
    (hlow : Blow ≤ initLabels s s) {φ : Φ} (hI : Inv φ) :
    ∃ (res : ResultD G s) (φ' : Φ) (gE : DGl G s) (lg : Log G s Ω),
      BMSSPD G s (dlOps G s) FPC DCb T Mf τ l Blow ⊤ {s} (initLabels s) φ DGl.init res φ' gE lg :=
  bmsspD_top_exists hFPC hFPCt τ hτ (fun _ => trivial) hM1 l hlow hI

end dlfinal

end BM
end CHD
end Frontier
