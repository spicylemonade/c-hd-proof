import Frontier.CHD.SpineLink
import Frontier.CHD.SpineBridgeD
import Frontier.CHD.RamBaseCase
import Frontier.CHD.WFrame

/-!
# SpineLoop — the main loop of a recursive BMSSP call (agent-08, B-L4, NON-GATE)

Program text of one iteration (BM.10–BM.24) with inline fragments, the loop (BM.9), and the
phase lemmas of an iteration.  Level `l ≥ 1` in register `lvl`; the child level is `l - 1`.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamSpine

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.RamLevel
  Frontier.CHD.BM Frontier.CHD.RamBaseCase Frontier.CHD.LabTab WExpr Stmt

/-- The ghost history of the label table. -/
abbrev Hist (G : Graph) := Fin G.n → ℕ → List (Fin G.m)

/-! ## Program text -/

/-- `lvl := lvl - 1` -/
def lvlDn : Stmt := wset "lvl" (sub (var "lvl") (lit 1))
/-- `lvl := lvl + 1` -/
def lvlUp : Stmt := wset "lvl" (add (var "lvl") (lit 1))

/-- The child's `S` row is emptied before the pull writes the pulled keys into it. -/
def childReset : Stmt := seq lvlDn (seq (rowReset "S.len") lvlUp)

/-- **One iteration of the main loop** (BM.10–BM.24), fragments inline: `pull` (B-L3, BM.10),
the expansion (BM.11–12), `copyChild` (child slots `B[l-1] := B_i`, `B_low[l-1] := B'`), the
recursive call (BM.13, procedure `P_bmssp`), `merge` (B-L3, BM.14), FIX-STALE deletion and group
removal (BM.15–18), the window scan (BM.19–21), re-selection (BM.23) and the `U` append (BM.24). -/
def iterBody (pull ltBi copyChild merge dsDelB gDelS scan resel appU : Stmt) : Stmt :=
  seq childReset
  (seq pull
  (seq (expand ltBi)
  (seq copyChild
  (seq lvlDn (seq (call P_bmssp) (seq lvlUp
  (seq merge
  (seq (removeU dsDelB gDelS)
  (seq scan (seq resel appU))))))))))

/-- BM.9's test `|U| ≤ τ_l ∧ view(D_l) ≠ ∅` (`sp.em` = the emptiness bit of `dsEmpty`), as
`(1 - [τ_l < |U|]) · [sp.em = 0]` (no arithmetic on `τ_l`, so nothing can overflow). -/
def loopTest : WExpr :=
  mul (sub (lit 1) (lt (load "cp.tau" (var "lvl")) (load "U.len" (var "lvl"))))
    (eq (var "sp.em") (lit 0))

/-- **The main loop** (BM.9–BM.24). -/
def mainLoop (dsEmpty body : Stmt) : Stmt :=
  seq dsEmpty (.while loopTest (seq body dsEmpty))

/-! ## Vertex sets in level rows -/

section rows

variable {G : Graph}

/-- Row `l` of `arr`/`len` holds the vertex set `X` (duplicate-free). -/
def SetRow (st : State ℝ≥0) (arr len : String) (l : ℕ) (X : Finset (Fin G.n)) : Prop :=
  ∃ xs : List ℕ, RowRep st arr len G.n l xs ∧ xs.Nodup ∧ ∀ x : ℕ, x ∈ xs ↔ ∃ u ∈ X, (u : ℕ) = x

end rows

/-! ## The child-row reset -/

section reset

variable {V : Type} {ops : VOps V}

theorem childReset_spec (st : State V) {l n : ℕ} (hl : st.w "lvl" = l) (hl1 : 1 ≤ l)
    (hlen : l - 1 < st.wlen "S.len") (hS : l * n ≤ st.wlen "S") (hcap : l + 1 < st.cap) :
    Runs ops childReset st (fun r => RowRep r "S" "S.len" n (l - 1) [] ∧
      Unchanged st r ["S.len"] [] ["lvl"] [] ∧ r.w "lvl" = l ∧
      (∀ j, j ≠ l - 1 → r.wa "S.len" j = st.wa "S.len" j) ∧ r.wlen = st.wlen ∧
      r.cost = st.cost + 3) := by
  have hc1 : 1 < st.cap := by omega
  refine runs_seq (runs_wset (a := l - 1) (by
    simp only [evalW_sub', evalW_var, evalW_lit', hl, Option.bind_some, fit_of_lt hc1]) ?_)
  set r1 := (st.setW "lvl" (l - 1)).charge 1 with hr1
  have hU1 : Unchanged st r1 [] [] ["lvl"] [] := unch_setW st _ (by simp)
  refine runs_seq ((Runs.wframe (by simp [WS, rowReset]) (RamLevel.rowReset_spec (arr := "S")
    (n := n) (l := l - 1) r1 (by simp [hr1, State.setW, State.charge]) (by rw [(hU1.warr _ (by simp)).2]; exact hlen)
    (by rw [(hU1.warr _ (by simp)).2, show l - 1 + 1 = l by omega]; exact hS)
    (by rw [hU1.cap]; omega))).mono ?_)
  rintro r2 ⟨⟨hR2, hU2, hSL2, -, hc2⟩, hW2⟩
  have hl2 : r2.w "lvl" = l - 1 := by
    rw [hU2.wreg _ (by simp)]; simp [hr1, State.setW, State.charge]
  refine runs_wset (a := l) (by
    rw [evalW_add_of (x := l - 1) (y := 1) (by rw [evalW_var, hl2])
      (evalW_lit_of (by rw [hU2.cap, hU1.cap]; omega)) (by rw [hU2.cap, hU1.cap]; omega),
      show l - 1 + 1 = l by omega]) ?_
  have hU3 : Unchanged r2 ((r2.setW "lvl" l).charge 1) [] [] ["lvl"] [] := unch_setW r2 _ (by simp)
  refine ⟨rowRep_of_unch hR2 hU3 (by simp) (by simp),
    (hU1.mono (by simp) (by simp) (List.Subset.refl _) (by simp)).trans
      (hU2.mono (by simp) (by simp) (by simp) (by simp)) |>.trans
      (hU3.mono (by simp) (by simp) (List.Subset.refl _) (by simp)),
    by simp [State.setW, State.charge], fun j hj => by
      simp only [State.charge_wa, State.setW_wa]; rw [hSL2 j hj]; rfl, ?_, ?_⟩
  · simp only [State.charge_wlen, State.setW_wlen]
    rw [hW2.wlen]; rfl
  · simp only [State.charge_cost, State.setW_cost, hc2, hr1]

end reset

/-! ## Frames: the data of the levels above `l` -/

/-- Arrays holding per-level rows (row `l` = indices `[l n, (l+1) n)`). -/
def rowArrs : List String :=
  ["S", "U", "W", "sp.gm", "sp.gs", "sp.gl", "sp.gp", "sp.gpos", "sp.g", "sp.inU", "sp.mk", "Wp"]
/-- Arrays holding per-level lengths / counts (entry `l`). -/
def lenArrs : List String := ["S.len", "U.len", "W.len", "sp.np", "sp.mk.len", "Wp.len"]

section above

variable {V : Type}

/-- `r` agrees with `st` on everything owned by the levels above `l`: their rows, lengths and
bound slots (slot indices `≥ slotB (l+1)`); no array is reallocated. -/
structure Above (st r : State V) (n l : ℕ) : Prop where
  rows : ∀ a ∈ rowArrs, ∀ i, (l + 1) * n ≤ i → r.wa a i = st.wa a i
  lens : ∀ a ∈ lenArrs, ∀ j, l < j → r.wa a j = st.wa a j
  slots : ∀ i, slotB (l + 1) ≤ i → r.va "sl.l" i = st.va "sl.l" i ∧ ∀ a ∈ slotW, r.wa a i = st.wa a i
  wlen : r.wlen = st.wlen
  vlen : r.vlen = st.vlen

theorem Above.refl (st : State V) (n l : ℕ) : Above st st n l :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => ⟨rfl, fun _ _ => rfl⟩, rfl, rfl⟩

theorem Above.trans {s1 s2 s3 : State V} {n l : ℕ} (h1 : Above s1 s2 n l) (h2 : Above s2 s3 n l) :
    Above s1 s3 n l :=
  ⟨fun a ha i hi => (h2.rows a ha i hi).trans (h1.rows a ha i hi),
    fun a ha j hj => (h2.lens a ha j hj).trans (h1.lens a ha j hj),
    fun i hi => ⟨(h2.slots i hi).1.trans (h1.slots i hi).1,
      fun a ha => ((h2.slots i hi).2 a ha).trans ((h1.slots i hi).2 a ha)⟩,
    h2.wlen.trans h1.wlen, h2.vlen.trans h1.vlen⟩

/-- A fragment writing none of the row/length/slot arrays keeps `Above`. -/
theorem Above.of_unchanged {st r : State V} {n l : ℕ} {wa va wr vr : List String}
    (h : Unchanged st r wa va wr vr) (hw : ∀ a ∈ rowArrs ++ lenArrs ++ slotW, a ∉ wa)
    (hv : "sl.l" ∉ va) (hwl : r.wlen = st.wlen) (hvl : r.vlen = st.vlen) : Above st r n l :=
  ⟨fun a ha i _ => by rw [(h.warr a (hw a (by simp [ha]))).1],
    fun a ha j _ => by rw [(h.warr a (hw a (by simp [ha]))).1],
    fun i _ => ⟨by rw [(h.varr _ hv).1], fun a ha => by rw [(h.warr a (hw a (by simp [ha]))).1]⟩,
    hwl, hvl⟩

/-- Levels below `l` may be written freely: `Above` at `l` follows from `Above` at `l - 1`. -/
theorem Above.up {st r : State V} {n l : ℕ} (h : Above st r n (l - 1)) (hl : 1 ≤ l) :
    Above st r n l :=
  ⟨fun a ha i hi => h.rows a ha i (le_trans (Nat.mul_le_mul_right _ (by omega)) hi),
    fun a ha j hj => h.lens a ha j (by omega),
    fun i hi => h.slots i (le_trans (by unfold slotB; omega) hi), h.wlen, h.vlen⟩

end above

/-! ## The `D` layer as seen by the spine -/

/-- The spine's own word registers (never written by the `D` layer). -/
def spRegs : List String :=
  ["lvl", "n", "gN", "sp.i", "sp.j", "sp.q", "sp.qe", "sp.np0", "px", "sp.em", "sl.i", "ru",
    "re", "mk.i", "sp.lt", "sp.pv", "sp.b", "sp.p", "sp.pe", "sp.go", "tt.ra", "tt.rb", "core.n",
    "core.s", "core.m", "hp_n", "sp.bih", "sp.biv", "sp.bie", "sp.bir", "sp.bif", "sp.ch", "sp.cv",
    "sp.ce", "sp.cr", "sp.cf"]

/-- The spine's own value registers (the label blocks it keeps across `D` operations). -/
def spVRegs : List String := ["sp.bil", "sp.cl"]

/-- The spine's own word arrays (never written by the `D` layer). -/
def spArrs : List String :=
  rowArrs ++ lenArrs ++ slotW ++ ["sp.xm", "sp.ptr", "cp.tau", "cp.M", "gSt", "gHead", "gKeep",
    "gRep", "hp_A", "hp_P"] ++ labW

section dlayer

variable (G : Graph) (s : Fin G.n)

/-- **The `D` layer** (to be instantiated by B-L3 with `DGlobal.DLRep`): `DR st H g Ds lo` — the
active levels `lo, lo+1, …` hold the structures `Ds`, with global lazy state `g` and label history
`H`; stored keys are label versions, so `DR` survives history extensions.  The operations refine
`dlOps` (`pullC`, `DB.merge 1`, `delC`, `insC`) with cost `≤ K · (Layer-A cost + 1)`. -/
structure DLayer (T : ℕ → ℕ) where
  DR : State ℝ≥0 → Hist G → DGl G s → (ℕ → DStrM G s) → ℕ → Prop
  dWA : List String
  dVA : List String
  dWR : List String
  /-- value registers the operations may clobber (scratch label copies) -/
  dVR : List String
  /-- a fragment whose footprint avoids the `D` layer's names keeps `DR` (labels may be
  re-written: the history only extends) -/
  frame : ∀ (st r : State ℝ≥0) (H H' : Hist G) (g : DGl G s) (Ds : ℕ → DStrM G s) (lo : ℕ)
    (wa va wr vr : List String), DR st H g Ds lo → Unchanged st r wa va wr vr →
    (∀ a ∈ dWA, a ∉ wa) → (∀ a ∈ dVA, a ∉ va) → (∀ a ∈ dWR, a ∉ wr) →
    HExt H (vc st) H' (vc r) → DR r H' g Ds lo
  /-- `DR` at `lo` only looks at the levels `≥ lo` -/
  congr : ∀ (st : State ℝ≥0) (H : Hist G) (g : DGl G s) (Ds Ds' : ℕ → DStrM G s) (lo : ℕ),
    (∀ j, lo ≤ j → Ds' j = Ds j) → DR st H g Ds lo → DR st H g Ds' lo
  dWA_ok : ∀ a ∈ dWA, a ∉ spArrs
  dVA_ok : ∀ a ∈ dVA, a ∉ "sl.l" :: "gW" :: labV
  dWR_ok : ∀ a ∈ dWR, a ∉ spRegs
  dVR_ok : ∀ a ∈ dVR, a ∉ spVRegs
  /-- every active level has at most `NB` blocks (they share one stack of capacity `NB`) -/
  NB : ℕ
  nb_le : ∀ (st : State ℝ≥0) (H : Hist G) (g : DGl G s) (Ds : ℕ → DStrM G s) (lo : ℕ),
    DR st H g Ds lo → ∀ j, lo ≤ j → (Ds j).blocks.length ≤ NB
  /-- the resource counter of the `D` layer (entries + block records created) and its capacity:
  the operations that create entries or blocks need room, paid in Layer-A cost units -/
  use : State ℝ≥0 → ℕ
  ucap : ℕ
  use_frame : ∀ (st r : State ℝ≥0) (wa va wr vr : List String), Unchanged st r wa va wr vr →
    (∀ a ∈ dWR, a ∉ wr) → use r = use st
  /-- the top level of the stack (the operations act on the levels `≤ LT`) -/
  LT : ℕ
  K : ℕ
  /-- BM.10: the pulled keys go to the (empty) child `S` row, the separator to slot `B_i[l]` -/
  pull : Stmt
  pull_spec : ∀ (st : State ℝ≥0) (H : Hist G) (g : DGl G s) (Ds : ℕ → DStrM G s) (l : ℕ),
    1 ≤ l → DR st H g Ds l → st.w "lvl" = l → st.w "n" = G.n →
    RowRep st "S" "S.len" G.n (l - 1) [] → SlotLens st (slotBi l) →
    Frontier.CHD.MLab.GoodHist (s := s) H (vc st) →
    use st + ((BM.pullC (dlOps G s) (T l) g (Ds l)).2.2.2.2 + 1) ≤ ucap →
    Runs realOps pull st (fun r =>
      DR r H (BM.pullC (dlOps G s) (T l) g (Ds l)).2.2.1
        (Function.update Ds l (BM.pullC (dlOps G s) (T l) g (Ds l)).2.2.2.1) l ∧
      RowRep r "S" "S.len" G.n (l - 1) ((BM.pullC (dlOps G s) (T l) g (Ds l)).1.map Fin.val) ∧
      SlotHolds r (slotBi l) H (vc r) (BM.pullC (dlOps G s) (T l) g (Ds l)).2.1 ∧
      Unchanged st r (dWA ++ ["S", "S.len"] ++ slotW) (dVA ++ ["sl.l"]) dWR dVR ∧
      (∀ i, (i < (l - 1) * G.n ∨ l * G.n ≤ i) → r.wa "S" i = st.wa "S" i) ∧
      (∀ j, j ≠ l - 1 → r.wa "S.len" j = st.wa "S.len" j) ∧
      (∀ i, i ≠ slotBi l → r.va "sl.l" i = st.va "sl.l" i ∧ ∀ a ∈ slotW, r.wa a i = st.wa a i) ∧
      r.wlen = st.wlen ∧ r.vlen = st.vlen ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + K * ((BM.pullC (dlOps G s) (T l) g (Ds l)).2.2.2.2 + 1) ∧
      use r ≤ use st + ((BM.pullC (dlOps G s) (T l) g (Ds l)).2.2.2.2 + 1))
  /-- BM.14: the child's structure (top, level `l - 1`) is merged into level `l` -/
  merge : Stmt
  merge_spec : ∀ (st : State ℝ≥0) (H : Hist G) (g : DGl G s) (Ds : ℕ → DStrM G s) (l : ℕ),
    1 ≤ l → l ≤ LT → DR st H g Ds (l - 1) → st.w "lvl" = l → st.w "n" = G.n →
    Frontier.CHD.MLab.GoodHist (s := s) H (vc st) →
    (∀ e ∈ DB.liveVals g.L (Ds l).blocks, (Ds (l - 1)).Bd ≤ e.val) →
    (∀ b ∈ (Ds l).blocks.tail, (((Ds (l - 1)).Bd : WLab G s) : WithBot (WLab G s)) < b.sep) →
    (Ds (l - 1)).Bd ≤ (Ds l).Bd →
    Runs realOps merge st (fun r =>
      DR r H g (Function.update Ds l (DB.merge 1 (Ds l) (Ds (l - 1))).1) l ∧
      Unchanged st r dWA dVA dWR dVR ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + K * ((DB.merge 1 (Ds l) (Ds (l - 1))).2 + 1) ∧ use r = use st)
  /-- BM.15 (FIX-STALE): the keys of the child's `U` row leave the live map -/
  delB : Stmt
  delB_spec : ∀ (st : State ℝ≥0) (H : Hist G) (g : DGl G s) (Ds : ℕ → DStrM G s) (l : ℕ)
    (lU : List (Fin G.n)), 1 ≤ l → DR st H g Ds l → st.w "lvl" = l → st.w "n" = G.n →
    RowRep st "U" "U.len" G.n (l - 1) (lU.map Fin.val) →
    Runs realOps delB st (fun r => DR r H (BM.delC g lU).1 Ds l ∧
      Unchanged st r dWA dVA dWR dVR ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + K * ((BM.delC g lU).2 + lU.length + 1) ∧ use r = use st)
  /-- insertion of the vertex in `px` with its current label (BM.6, BM.23) -/
  ins : Stmt
  ins_spec : ∀ (st : State ℝ≥0) (H : Hist G) (g : DGl G s) (Ds : ℕ → DStrM G s) (l : ℕ)
    (d : Labels G s) (c0 : ℕ) (v : Fin G.n), DR st H g Ds l → LabAt st d H c0 →
    st.w "lvl" = l → st.w "n" = G.n → st.w "px" = v → d v < (Ds l).Bd →
    use st + ((BM.insC (dlOps G s) (T l) g (Ds l) v (d v)).2.2 + 1) ≤ ucap →
    Runs realOps ins st (fun r =>
      DR r H (BM.insC (dlOps G s) (T l) g (Ds l) v (d v)).1
        (Function.update Ds l (BM.insC (dlOps G s) (T l) g (Ds l) v (d v)).2.1) l ∧
      Unchanged st r dWA dVA dWR dVR ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + K * ((BM.insC (dlOps G s) (T l) g (Ds l) v (d v)).2.2 + 1) ∧
      use r ≤ use st + ((BM.insC (dlOps G s) (T l) g (Ds l) v (d v)).2.2 + 1))
  /-- BM.5 (call entry): a new level-`l` structure `newC M Bd`, with `M = cp.M[l]` and the bound
  `Bd` in slot `B[l]` -/
  new : Stmt
  new_spec : ∀ (st : State ℝ≥0) (H : Hist G) (g : DGl G s) (Ds : ℕ → DStrM G s) (l : ℕ)
    (M : ℕ) (Bd : WLab G s), DR st H g Ds (l + 1) → st.w "lvl" = l → st.w "n" = G.n →
    st.wa "cp.M" l = M → l < st.wlen "cp.M" → 2 * M + 2 < st.cap → SlotHolds st (slotB l) H (vc st) Bd →
    SlotLens st (slotB l) → use st + 1 ≤ ucap →
    Runs realOps new st (fun r => DR r H g (Function.update Ds l (newC M Bd)) l ∧
      Unchanged st r dWA dVA dWR dVR ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + K ∧ use r ≤ use st + 1)
  /-- BM.9: the emptiness bit of the view of level `l` (constant cost) -/
  empty : Stmt
  empty_spec : ∀ (st : State ℝ≥0) (H : Hist G) (g : DGl G s) (Ds : ℕ → DStrM G s) (l : ℕ),
    DR st H g Ds l → st.w "lvl" = l → st.w "n" = G.n →
    Runs realOps empty st (fun r => DR r H g Ds l ∧
      (r.w "sp.em" = 0 ↔ ¬ (g.view (Ds l)).IsEmpty) ∧
      Unchanged st r dWA dVA (dWR ++ ["sp.em"]) dVR ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost + K ∧ use r = use st)

end dlayer

/-! ## The FindPivots state (deleted edges) as seen by the spine -/

section phi

variable {Φ : Type}

/-- The persistent FindPivots state `φ` (C-HD: the deleted-edge set) is represented by `PhiR`,
owned by B-L2 (arrays `pWA`, registers `pWR`), framed by everything else. -/
structure PhiI (Φ : Type) where
  PhiR : State ℝ≥0 → Φ → Prop
  pWA : List String
  pWR : List String
  /-- a fragment whose footprint avoids B-L2's names keeps `PhiR` -/
  frame : ∀ (st r : State ℝ≥0) (φ : Φ) (wa va wr vr : List String), PhiR st φ →
    Unchanged st r wa va wr vr → (∀ a ∈ pWA, a ∉ wa) → (∀ a ∈ pWR, a ∉ wr) → PhiR r φ
  pWA_ok : ∀ a ∈ pWA, a ∉ spArrs
  pWR_ok : ∀ a ∈ pWR, a ∉ spRegs

end phi

/-! ## Call contract of the recursive procedure -/

section contract

variable {G : Graph} {s : Fin G.n}

/-- The pointer invariant of a returned vertex `u` for the call bound `B` (sorted CSR range
`[gSt u, gSt (u+1))`): the slots before `ptr[u]` have candidate `< B`, the slot at `ptr[u]` (if
inside the range) has candidate `≥ B`.  Definitionally agent-02's `WinScan.PtrAt st (d u) u B`. -/
def PtrOK (st : State ℝ≥0) (d : Labels G s) (B : WLab G s) (u : Fin G.n) : Prop :=
  st.wa "gSt" u ≤ st.wa "sp.ptr" u ∧ st.wa "sp.ptr" u ≤ st.wa "gSt" ((u : ℕ) + 1) ∧
  (∀ j (hj : j < G.m), st.wa "gSt" u ≤ j → j < st.wa "sp.ptr" u → ext (d u) ⟨j, hj⟩ < B) ∧
  (∀ hq : st.wa "sp.ptr" u < G.m, st.wa "sp.ptr" u < st.wa "gSt" ((u : ℕ) + 1) →
    ¬ ext (d u) ⟨st.wa "sp.ptr" u, hq⟩ < B)

/-- The base-case heap (`BaseHeap.heapL`: `hp_n`, `hp_A`, `hp_P`) is empty. -/
def HeapEmpty (st : State ℝ≥0) (n : ℕ) : Prop :=
  st.w "hp_n" = 0 ∧ st.wlen "hp_A" = n ∧ st.wlen "hp_P" = n ∧ ∀ v < n, st.wa "hp_P" v = 0

/-- The spine-wide facts of every state of the spine: registers `n = gN = |V|`, the graph and its
sorted CSR, the procedure table, array sizes for levels `0 … LF+1` and the word capacity. -/
structure Static (st : State ℝ≥0) (G : Graph) (LF : ℕ) (body : Stmt) (τf Mf : ℕ → ℕ) : Prop where
  n : st.w "n" = G.n
  gN : st.w "gN" = G.n
  graph : GraphAt st G
  csr : CSRAt st G
  proc : st.procs[P_bmssp]? = some body
  rows : ∀ a ∈ rowArrs, (LF + 2) * G.n ≤ st.wlen a
  lens : ∀ a ∈ lenArrs, LF + 2 ≤ st.wlen a
  slots : ∀ i < slotB (LF + 2), SlotLens st i
  xm : G.n ≤ st.wlen "sp.xm"
  ptr : G.n ≤ st.wlen "sp.ptr"
  tau : LF + 1 ≤ st.wlen "cp.tau"
  Ml : LF + 2 ≤ st.wlen "cp.M"
  tauv : ∀ l ≤ LF, st.wa "cp.tau" l = τf l
  Mv : ∀ l ≤ LF + 1, st.wa "cp.M" l = Mf l
  /-- the base-case heap is empty between calls -/
  heap : HeapEmpty st G.n
  cap : (LF + 3) * (G.n + G.m + 8) < st.cap
  /-- the per-level caps and block parameters fit in words -/
  tauCap : ∀ l ≤ LF, τf l + 2 < st.cap
  MCap : ∀ l ≤ LF + 1, 2 * Mf l + 2 < st.cap

/-- The scratch rows of all levels `≤ l` are clear (group table rows, `inU` rows), and so are the
marks. -/
structure Clear (st : State ℝ≥0) (n l : ℕ) : Prop where
  g : ∀ l' ≤ l, ∀ x < n, st.wa "sp.g" (l' * n + x) = 0
  inU : ∀ l' ≤ l, ∀ x < n, st.wa "sp.inU" (l' * n + x) = 0
  xm : ∀ x < n, st.wa "sp.xm" x = 0

variable {T : ℕ → ℕ} {Φ : Type}

/-- **The machine state at the entry of a call** at level `l` with arguments
`(Blow, B, S, d, φ, g)`; the structures of the active ancestor levels `> l` are `Ds`. -/
structure CallIn (DL : DLayer G s T) (PhiR : State ℝ≥0 → Φ → Prop) (LF : ℕ) (body : Stmt)
    (τf Mf : ℕ → ℕ)
    (st : State ℝ≥0) (l : ℕ) (Blow B : WLab G s) (S : Finset (Fin G.n)) (d : Labels G s) (φ : Φ)
    (g : DGl G s) (Ds : ℕ → DStrM G s) (H : Hist G) (c0 : ℕ) : Prop where
  lvl : st.w "lvl" = l
  lvl_le : l ≤ LF
  stat : Static st G LF body τf Mf
  lab : LabAt st d H c0
  D : DL.DR st H g Ds (l + 1)
  phi : PhiR st φ
  S : SetRow st "S" "S.len" l S
  sB : SlotHolds st (slotB l) H (vc st) B
  sBlow : SlotHolds st (slotBlow l) H (vc st) Blow
  clr : Clear st G.n l

/-- **The machine state at the return of a call** (entry state `st`): the result `res`, the
returned structure on top of the stack (level `l`), the returned set in the `U` row, the returned
bound in slot `B'[l]`, the pointer invariant of the returned vertices, and nothing above `l`
changed. -/
structure CallOut (DL : DLayer G s T) (PhiR : State ℝ≥0 → Φ → Prop) (LF : ℕ) (body : Stmt)
    (τf Mf : ℕ → ℕ)
    (st r : State ℝ≥0) (l : ℕ) (B : WLab G s) (res : ResultD G s) (φ' : Φ) (g' : DGl G s)
    (Ds : ℕ → DStrM G s) (H' : Hist G) (c0 : ℕ) : Prop where
  lvl : r.w "lvl" = l
  stat : Static r G LF body τf Mf
  lab : LabAt r res.2.2.2 H' c0
  D : DL.DR r H' g' (Function.update Ds l res.2.2.1) l
  phi : PhiR r φ'
  U : SetRow r "U" "U.len" l res.2.1
  sBp : SlotHolds r (slotBp l) H' (vc r) res.1
  ptr : ∀ u ∈ res.2.1, PtrOK r res.2.2.2 B u
  /-- pointers of non-returned vertices are untouched -/
  ptrFr : ∀ x : Fin G.n, x ∉ res.2.1 → r.wa "sp.ptr" x = st.wa "sp.ptr" x
  clr : Clear r G.n l
  above : Above st r G.n l
  /-- the static arrays (CSR, tables, L6 outputs) are untouched -/
  stArr : ∀ a ∈ ["gSt", "gHead", "cp.tau", "cp.M", "gKeep", "gRep"], r.wa a = st.wa a

variable {Ω : Type}

/-- **The contract of `call P_bmssp` at level `l`** (the induction hypothesis of the spine): from
an admissible call entry whose every Layer-A outcome fits the budget, the call returns in a state
representing one Layer-A outcome, at RAM cost at most `K` per unit of Layer-A cost.  The `D` layer's
resource counter grows by at most `2` per unit of Layer-A cost (every operation that creates
entries costs `c + 1 ≤ 2c` of it, `c ≥ 1` its logged cost), given room for every outcome; this
premise has no additive slack, so `ucap` stays `O(Tchd)`. -/
def CallSpec (DL : DLayer G s T) (PhiR : State ℝ≥0 → Φ → Prop) (Inv : Φ → Prop)
    (FPC : FPRelC G s Φ Ω) (DCb : DCost) (Mf τ : ℕ → ℕ) (LF : ℕ) (body : Stmt) (K Sl : ℕ)
    (Sb : ℕ → ℕ) (l : ℕ) : Prop :=
  ∀ (st : State ℝ≥0) (Blow B : WLab G s) (S : Finset (Fin G.n)) (d : Labels G s) (φ : Φ)
    (g : DGl G s) (Ds : ℕ → DStrM G s) (H : Hist G) (c0 : ℕ),
    CallPre B S d → Inv φ → (∀ x ∈ S, Blow ≤ dis (s := s) x) → Blow ≤ B →
    DB.KeyInj g.L (kof G s) → (∀ v i a, g.L v = some (i, a) → B ≤ a) → S.card ≤ Sb l →
    CallIn DL PhiR LF body τ Mf st l Blow B S d φ g Ds H c0 →
    (∀ res φ' g' lg, BMSSPD G s (dlOps G s) FPC DCb T Mf τ l Blow B S d φ g res φ' g' lg →
      st.cost + K * lg.cost + Sl ≤ c0 + st.cap) →
    (∀ res φ' g' lg, BMSSPD G s (dlOps G s) FPC DCb T Mf τ l Blow B S d φ g res φ' g' lg →
      DL.use st + 2 * lg.cost ≤ DL.ucap) →
    Runs realOps (call P_bmssp) st (fun r => ∃ (res : ResultD G s) (φ' : Φ) (g' : DGl G s)
      (lg : Log G s Ω) (H' : Hist G),
      BMSSPD G s (dlOps G s) FPC DCb T Mf τ l Blow B S d φ g res φ' g' lg ∧
      HExt H (vc st) H' (vc r) ∧ CallOut DL PhiR LF body τ Mf st r l B res φ' g' Ds H' c0 ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost + K * lg.cost ∧ DL.use r ≤ DL.use st + 2 * lg.cost)

end contract

/-! ## Layer-A admissibility of the sub-call (from the pull alone) -/

section childPre

variable {G : Graph} {s : Fin G.n} {ops : BM.DOps G s} {T : ℕ} {B : WLab G s}
  {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {p : ℕ} {P0 : Fin p → Finset (Fin G.n)}
  {Q W : Finset (Fin G.n)} {B'0 : WLab G s}

/-- **The sub-call of an iteration is admissible** (the premises of `SimSub` / `TotalSub` /
`CallSpec`), and the pulled keys are distinct — known right after the pull (BM.10). -/
theorem childPre (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W) {f0 : ℕ}
    {cs : BM.CSt G s p} (h : BM.LInv G s B S d0 d1 P0 B'0 cs.lit) (hS : BM.SInv G s ops B f0 cs.g cs.Dc)
    (hK : DB.KeyInj cs.g.L (kof G s)) (hne : ¬ (cs.g.view cs.Dc).IsEmpty)
    {ks : List (Fin G.n)} {Bi : WLab G s} {g1 : BM.DGl G s} {Dc1 : BM.DStrM G s} {cp : ℕ}
    (hpull : BM.pullC ops T cs.g cs.Dc = (ks, Bi, g1, Dc1, cp)) :
    CallPre Bi (BM.expand cs.lit ks.toFinset Bi) cs.d ∧
      (∀ x ∈ BM.expand cs.lit ks.toFinset Bi, cs.B' ≤ dis (s := s) x) ∧ cs.B' ≤ Bi ∧
      DB.KeyInj g1.L (kof G s) ∧ (∀ v i a, g1.L v = some (i, a) → Bi ≤ a) ∧ ks.Nodup := by
  obtain ⟨hPS, -, -, hK1, -, -, -, -, habove, -⟩ := BM.pull_sim hS hK hpull
  have hPS' : PullSpec cs.lit.D B ks.toFinset Bi (g1.view Dc1) := hPS
  have hsp : CallPre Bi (BM.expand cs.lit ks.toFinset Bi) cs.lit.d := BM.step_pre hpre hfp h hPS'
  have hlowdis : ∀ x ∈ BM.expand cs.lit ks.toFinset Bi, cs.lit.B' ≤ dis (s := s) x :=
    fun x hx => (BM.Si_facts h hPS' hx).1.2.2
  have hSne : ks.toFinset.Nonempty := by
    apply hPS'.nonempty
    have hne' : ¬ cs.lit.D.IsEmpty := hne
    simp only [DS.IsEmpty, not_forall] at hne'
    exact hne'
  obtain ⟨x0, hx0⟩ := hSne
  have hx0S : x0 ∈ BM.expand cs.lit ks.toFinset Bi := BM.mem_expand.mpr (Or.inl hx0)
  have hBlt : cs.lit.B' < Bi := by
    obtain ⟨⟨-, -, hB⟩, hlt⟩ := BM.Si_facts h hPS' hx0S
    exact lt_of_le_of_lt (hB.trans (h.walk.sound x0)) hlt
  have hnd : ks.Nodup := by
    have e : ks = (ops.pull T cs.g.L cs.Dc).1 := by
      simp only [BM.pullC, Prod.mk.injEq] at hpull; exact hpull.1.symm
    rw [e]; exact ops.pull_nodup T hS.ids
  exact ⟨hsp, hlowdis, hBlt.le, hK1, habove, hnd⟩

end childPre

/-! ## The main loop: machine representation and Layer-A invariant -/

section loopRep

variable {G : Graph} {s : Fin G.n} {T : ℕ → ℕ} {Φ : Type}

/-- **The machine state during the main loop** of a call at level `l ≥ 1` with bound `B` and cap
`τ` (ancestor structures `Ds`, label history `H`, clock origin `c0`), at loop configuration `c`:
the loop state of `c.cs` is in the level-`l` rows, slots and D structure, the child level `l - 1`
is clear, and the returned vertices satisfy the pointer invariant for `B`. -/
structure LoopRep (DL : DLayer G s T) (PI : PhiI Φ) (LF : ℕ) (body : Stmt) (τf Mf : ℕ → ℕ)
    (st : State ℝ≥0)
    (l : ℕ) (B : WLab G s) (τ : ℕ) (Ds : ℕ → DStrM G s) (H : Hist G) (c0 : ℕ) {p : ℕ}
    (c : LoopCfgD G s Φ p) : Prop where
  lvl : st.w "lvl" = l
  l1 : 1 ≤ l
  lvl_le : l ≤ LF
  stat : Static st G LF body τf Mf
  lab : LabAt st c.cs.d H c0
  D : DL.DR st H c.cs.g (Function.update Ds l c.cs.Dc) l
  phi : PI.PhiR st c.φ
  grp : GrpRep st l G.n p (liftP c.cs.P) (liftPiv c.cs.piv)
  np : NpRep st l p
  U : SetRow st "U" "U.len" l c.cs.U
  inU : ∀ v : Fin G.n, st.wa "sp.inU" (l * G.n + v) = if v ∈ c.cs.U then 1 else 0
  sB : SlotHolds st (slotB l) H (vc st) B
  sBp : SlotHolds st (slotBp l) H (vc st) c.cs.B'
  tau : st.wa "cp.tau" l = τ
  clr : Clear st G.n (l - 1)
  ptr : ∀ u ∈ c.cs.U, PtrOK st c.cs.d B u

variable {Ω : Type}

/-- **The Layer-A loop invariant** of a call at level `l + 1` (the hypotheses of agent-01's
`BMLazy.stepD_inv`, which re-establishes them for the next configuration): `hpre`/`hfp` are the
call's `CallPre` and FindPivots contract, `f0`/`L0` the global lazy state at call entry. -/
structure ALoop (ops : DOps G s) (Inv : Φ → Prop) (Mf : ℕ → ℕ) (l : ℕ) (B : WLab G s)
    (S : Finset (Fin G.n)) (d0 d1 : Labels G s) {p : ℕ} (P0 : Fin p → Finset (Fin G.n))
    (B'0 : WLab G s) (f0 : ℕ) (L0 : LiveM G s) (c : LoopCfgD G s Φ p) : Prop where
  linv : LInv G s B S d0 d1 P0 B'0 c.cs.lit
  inv : Inv c.φ
  sinv : BM.SInv G s ops B f0 c.cs.g c.cs.Dc
  M : c.cs.Dc.M = Mf (l + 1)
  kinj : DB.KeyInj c.cs.g.L (kof G s)
  chg : CallChange f0 B L0 c.cs.g.L
  touch : ∀ y, c.cs.g.L y ≠ L0 y → y ∈ c.cs.U ∨ ∃ a, c.cs.g.view c.cs.Dc y = some a ∧ a ≤ d0 y

end loopRep

end Frontier.CHD.RamSpine
