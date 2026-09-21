import Frontier.CHD.SpineLoop
import Frontier.CHD.RamCopy
import Frontier.CHD.RamPiv
import Frontier.CHD.RamT6
import Frontier.CHD.RamWp
import Frontier.CHD.RamFin
import Frontier.CHD.SpineLab

/-!
# Frontier.CHD.RamBody — the body of a recursive BMSSP call at level `l ≥ 1` (owner: agent-01)

**NON-GATE** (B-L4, the spine's level body, agent-08's assignment 17:48).  Program text of one
recursive call (BM.1–BM.31) and its specification against agent-08's `CallIn`/`CallOut`/
`CallSpec` (`SpineLoop`), with the main loop taken as a black box (`LoopSpecB`).

Phases: FindPivots (`fp`, B-L2) → the groups into the level table (`copyGrp`) → pivots
(`pivProg`) → new structure + pivot insertions (`pivIns`) → `B'_0` (`b8`) → `U := ∅` → main loop →
finalization (BM.24a–31: `B'f`, `T6`, `W'`, relaxations out of `W'`, deletion of `W'`, clears).

The phases owned by others are interfaces (hypotheses), each stated in the exact Layer-A terms of
`BMLazy.CallD`:
* `FPB` (B-L2, agent-09/03): the FindPivots call;
* `LoopSpecB` (agent-08): the main loop;
* `RelWB` (agent-02): the relaxations out of `W'` (BM.27–28, `L.foldl relaxInsCc … (some B'f)`);
* `DelWB` (B-L3): deletion of the `W'` row keys (`delC`);
* `CmpI` / `TestI` (B-LAB): label comparisons.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamBody

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.RamLevel
  Frontier.CHD.BM Frontier.CHD.RamBaseCase Frontier.CHD.LabTab Frontier.CHD.RamSpine
  Frontier.CHD.RamInit WExpr Stmt

/-! ## Program text -/

/-- Setup of BM.8's registers: `b8.p := sp.np[lvl]`, `b8.sB := slotB lvl`, `b8.sBp := slotBp lvl`. -/
def b8Setup : Stmt :=
  seq (wset "b8.p" (load "sp.np" (var "lvl")))
  (seq (wset "b8.sB" (mul (lit 4) (var "lvl")))
       (wset "b8.sBp" (add (mul (lit 4) (var "lvl")) (lit 2))))

/-- The label block used to copy a bound slot. -/
def K24 : LReg := ⟨"f24.kl", "f24.kh", "f24.kv", "f24.ke", "f24.kr"⟩

/-- `slot[slotBp lvl] := slot[slotB lvl]` -/
def copyBtoBp : Stmt :=
  seq (wset "sl.i" (mul (lit 4) (var "lvl")))
  (seq (loadSlot K24 "f24.kf")
  (seq (wset "sl.i" (add (mul (lit 4) (var "lvl")) (lit 2)))
       (storeSlot K24 "f24.kf")))

/-- BM.24a (FIX-EMPTY): `B'f := if view(D) = ∅ then B else B'` (in slot `B'[lvl]`). -/
def bpfProg (dsEmpty : Stmt) : Stmt :=
  seq dsEmpty (ite (var "sp.em") copyBtoBp skip)

/-- BM.30–31 and the clears of the level rows: group memberships (on `S`) and `inU` (on `U`). -/
def clearsProg : Stmt :=
  seq (rowZero "sp.g" "S" "S.len") (rowZero "sp.inU" "U" "U.len")

/-- The finalization BM.24a–31. -/
def finProg (dsEmpty tstT6 dsIns tstWp relW delW : Stmt) : Stmt :=
  seq (bpfProg dsEmpty)
  (seq (t6Prog tstT6 dsIns)
  (seq (wpProg tstWp)
  (seq relW
  (seq delW clearsProg))))

/-- **The body of a recursive call** at level `lvl ≥ 1`. -/
def bodyProg (fp cmp dsNew dsIns dsEmpty iterB tstT6 tstWp relW delW : Stmt) : Stmt :=
  seq fp
  (seq copyGrp
  (seq (pivProg cmp)
  (seq (pivIns dsNew dsIns)
  (seq b8Setup
  (seq Frontier.CHD.SpineLab.b8Prog
  (seq (rowReset "U.len")
  (seq (mainLoop dsEmpty iterB)
       (finProg dsEmpty tstT6 dsIns tstWp relW delW))))))))


/-! ## The interfaces of the phases owned by others -/

section ifaces

variable {G : Graph} {s : Fin G.n} {T : ℕ → ℕ} {Φ Ω : Type}

/-- What FindPivots preserves of the call-entry state at level `l`. -/
structure FPFrame (st r : State ℝ≥0) (LF : ℕ) (body : Stmt) (τf Mf : ℕ → ℕ) (l : ℕ)
    (S : Finset (Fin G.n)) : Prop where
  lvl : r.w "lvl" = l
  stat : Static r G LF body τf Mf
  S : SetRow r "S" "S.len" l S
  slots : ∀ i, r.va "sl.l" i = st.va "sl.l" i ∧ ∀ a ∈ slotW, r.wa a i = st.wa a i
  clr : Clear r G.n l
  above : Above st r G.n l
  ptr : ∀ x, r.wa "sp.ptr" x = st.wa "sp.ptr" x
  tables : ∀ a ∈ ["cp.tau", "cp.M", "sp.np", "U.len", "U", "sp.gp"], ∀ i, r.wa a i = st.wa a i
  /-- the static arrays (CSR, tables, L6 outputs) are untouched, as `CallOut.stArr` needs -/
  stArr : ∀ a ∈ ["gSt", "gHead", "cp.tau", "cp.M", "gKeep", "gRep"], r.wa a = st.wa a

/-- **The FindPivots call** (B-L2): from a call entry, `fp` realizes one outcome of `FPC`, with
the groups in agent-03's `GrpOut` layout, `W` in row `l`, the new labels and `φ`. -/
def FPB (DL : DLayer G s T) (PI : PhiI Φ) (Inv : Φ → Prop) (FPC : FPRelC G s Φ Ω) (LF : ℕ)
    (body fp : Stmt) (τf Mf : ℕ → ℕ) (Kf Cf : ℕ) (l : ℕ) : Prop :=
  ∀ (st : State ℝ≥0) (Blow B : WLab G s) (S : Finset (Fin G.n)) (d0 : Labels G s) (φ : Φ)
    (g : DGl G s) (Ds : ℕ → DStrM G s) (H : Hist G) (c0 : ℕ),
    CallIn DL PI.PhiR LF body τf Mf st l Blow B S d0 φ g Ds H c0 → CallPre B S d0 → Inv φ →
    (∀ x ∈ S, Blow ≤ dis (s := s) x) →
    (∀ d1 p P Q W φ1 ω cfp, FPC l Blow B S d0 φ d1 p P Q W φ1 ω cfp →
      st.cost + Kf * cfp + Cf ≤ c0 + st.cap) →
    Runs realOps fp st (fun r => ∃ (d1 : Labels G s) (p : ℕ) (P : Fin p → Finset (Fin G.n))
      (Q W : Finset (Fin G.n)) (φ1 : Φ) (ω : Ω) (cfp : ℕ) (Gs : List (List (Fin G.n)))
      (wl : List (Fin G.n)) (H1 : Hist G),
      FPC l Blow B S d0 φ d1 p P Q W φ1 ω cfp ∧
      ∃ hp : Gs.length = p, (∀ j (hj : j < p), P ⟨j, hj⟩ = (Gs[j]'(by omega)).toFinset) ∧
      (∀ j (hj : j < Gs.length), (Gs[j]).Nodup) ∧
      Frontier.CHD.PartitionRAM.GrpOut r (Gs.map (List.map Fin.val)) ∧
      ((Gs.map List.length).sum ≤ r.wlen "pt.GV" ∧ Gs.length ≤ r.wlen "pt.GO" ∧
        Gs.length ≤ r.wlen "pt.GL") ∧
      RowRep r "W" "W.len" G.n l (wl.map Fin.val) ∧ wl.Nodup ∧ wl.toFinset = W ∧
      LabAt r d1 H1 c0 ∧ HExt H (vc st) H1 (vc r) ∧ PI.PhiR r φ1 ∧ DL.DR r H1 g Ds (l + 1) ∧
      FPFrame st r LF body τf Mf l S ∧ st.cost ≤ r.cost ∧ r.cost ≤ st.cost + Kf * cfp + Cf ∧
      DL.use r = DL.use st)

/-- What the main loop preserves of the loop-entry state (level `l + 1`). -/
structure LoopFrame (st r : State ℝ≥0) (l : ℕ) : Prop where
  S : ∀ i, (l + 1) * G.n ≤ i → i < (l + 2) * G.n → r.wa "S" i = st.wa "S" i
  Slen : r.wa "S.len" (l + 1) = st.wa "S.len" (l + 1)
  W : ∀ i, (l + 1) * G.n ≤ i → i < (l + 2) * G.n → r.wa "W" i = st.wa "W" i
  Wlen : r.wa "W.len" (l + 1) = st.wa "W.len" (l + 1)
  above : Above st r G.n (l + 1)
  /-- the static arrays (CSR, tables, L6 outputs) are untouched -/
  stArr : ∀ a ∈ ["gSt", "gHead", "cp.tau", "cp.M", "gKeep", "gRep"], r.wa a = st.wa a

/-- **The main loop** (agent-08): from `LoopRep ∧ ALoop` and the budget of every Layer-A outcome,
`mainLoop` realizes one `LoopD` run and ends in `LoopRep` of its final configuration.  Cost: the
sub-calls at the call constant `K` (the induction hypothesis), the loop's own work (`cc + cm`) at
its own constant `Ko` (so that the level body can pay its own finalization from `K - Ko`). -/
def LoopSpecB (DL : DLayer G s T) (PI : PhiI Φ) (Inv : Φ → Prop) (FPC : FPRelC G s Φ Ω)
    (DCb : DCost) (Mf τ : ℕ → ℕ) (LF : ℕ) (body dsEmpty iterB : Stmt) (K Ko Sl : ℕ) (Sb : ℕ → ℕ)
    (l : ℕ) : Prop :=
  ∀ (st : State ℝ≥0) (B : WLab G s) (S : Finset (Fin G.n)) (d0 d1 : Labels G s) (p : ℕ)
    (P0 : Fin p → Finset (Fin G.n)) (Q W : Finset (Fin G.n)) (B'0 : WLab G s) (f0 : ℕ)
    (L0 : LiveM G s) (c : LoopCfgD G s Φ p) (Ds : ℕ → DStrM G s) (H : Hist G) (c0 : ℕ),
    CallPre B S d0 → FPContract B S d0 d1 p P0 Q W →
    LoopRep DL PI LF body τ Mf st (l + 1) B (τ (l + 1)) Ds H c0 c →
    ALoop (dlOps G s) Inv Mf l B S d0 d1 P0 B'0 f0 L0 c →
    (∀ c', ALoop (dlOps G s) Inv Mf l B S d0 d1 P0 B'0 f0 L0 c' → ¬ LoopDoneD (τ (l + 1)) c' →
      ∀ ks Bi g1 Dc1 cp, pullC (dlOps G s) (T (l + 1)) c'.cs.g c'.cs.Dc = (ks, Bi, g1, Dc1, cp) →
      (BM.expand c'.cs.lit ks.toFinset Bi).card ≤ Sb l) →
    (∀ cs' φ' lg J cm cc, LoopD G s (dlOps G s) (T (l + 1)) (BMSSPD G s (dlOps G s) FPC DCb T Mf τ l)
      B (τ (l + 1)) c.i c.cs c.φ cs' φ' lg J cm cc → st.cost + K * lg.cost + Ko * (cc + cm) + Sl ≤ c0 + st.cap) →
    (∀ cs' φ' lg J cm cc, LoopD G s (dlOps G s) (T (l + 1)) (BMSSPD G s (dlOps G s) FPC DCb T Mf τ l)
      B (τ (l + 1)) c.i c.cs c.φ cs' φ' lg J cm cc → DL.use st + 2 * (cc + cm + lg.cost) ≤ DL.ucap) →
    Runs realOps (mainLoop dsEmpty iterB) st (fun r => ∃ (cs' : CSt G s p) (φ' : Φ) (lg : Log G s Ω)
      (J : Finset (Fin G.m)) (cm cc : ℕ) (H' : Hist G),
      LoopD G s (dlOps G s) (T (l + 1)) (BMSSPD G s (dlOps G s) FPC DCb T Mf τ l)
        B (τ (l + 1)) c.i c.cs c.φ cs' φ' lg J cm cc ∧
      LoopRep DL PI LF body τ Mf r (l + 1) B (τ (l + 1)) Ds H' c0 ⟨c.i, cs', φ'⟩ ∧
      ALoop (dlOps G s) Inv Mf l B S d0 d1 P0 B'0 f0 L0 ⟨c.i, cs', φ'⟩ ∧
      HExt H (vc st) H' (vc r) ∧ LoopFrame (G := G) st r l ∧
      (∀ x : Fin G.n, x ∉ cs'.U → x ∉ c.cs.U → r.wa "sp.ptr" x = st.wa "sp.ptr" x) ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost + K * lg.cost + Ko * (cc + cm) ∧
      DL.use r ≤ DL.use st + 2 * (cc + cm + lg.cost))

/-- **The relaxations out of `W'`** (BM.27–28, agent-02): every out-edge of the `W'` row, in CSR
order, relaxed with `lo = some B'f` (Layer A: `L.foldl relaxInsCc`), and the pointers of `W'`
set for the bound `B`.  `RW`/`RV`: the (scratch) registers it may write; the level body needs
only `lvl`, `n`, `gN`, `hp_n` ∉ `RW` and the names of B-L2 disjoint from them. -/
def RelWB (DL : DLayer G s T) (relW : Stmt) (K C : ℕ) (RW RV : List String) : Prop :=
  ∀ (st : State ℝ≥0) (l : ℕ) (B B'f : WLab G s) (d : Labels G s) (g : DGl G s) (Dc : DStrM G s)
    (Ds : ℕ → DStrM G s) (H : Hist G) (c0 : ℕ) (lW : List (Fin G.n)),
    st.w "lvl" = l → st.w "n" = G.n → LabAt st d H c0 → WalkInv d →
    DL.DR st H g (Function.update Ds l Dc) l →
    RowRep st "Wp" "Wp.len" G.n l (lW.map Fin.val) → lW.Nodup →
    SlotHolds st (slotB l) H (vc st) B → SlotHolds st (slotBp l) H (vc st) B'f →
    (∀ L : List (Fin G.m), Enumerates G L lW.toFinset →
      st.cost + K * ((L.foldl (relaxInsCc (dlOps G s) (T l) B (some B'f)) ⟨d, g, Dc, 0⟩).c + 1)
        + C * (lW.length + 1) ≤ c0 + st.cap) →
    Runs realOps relW st (fun r => ∃ (L : List (Fin G.m)) (H' : Hist G),
      Enumerates G L lW.toFinset ∧
      LabAt r (L.foldl (relaxInsCc (dlOps G s) (T l) B (some B'f)) ⟨d, g, Dc, 0⟩).d H' c0 ∧
      HExt H (vc st) H' (vc r) ∧
      DL.DR r H' (L.foldl (relaxInsCc (dlOps G s) (T l) B (some B'f)) ⟨d, g, Dc, 0⟩).g
        (Function.update Ds l (L.foldl (relaxInsCc (dlOps G s) (T l) B (some B'f)) ⟨d, g, Dc, 0⟩).Dc) l ∧
      (∀ u ∈ lW, PtrOK r (L.foldl (relaxInsCc (dlOps G s) (T l) B (some B'f)) ⟨d, g, Dc, 0⟩).d B u) ∧
      (∀ x : Fin G.n, x ∉ lW → r.wa "sp.ptr" x = st.wa "sp.ptr" x) ∧
      Unchanged st r (DL.dWA ++ labW ++ ["sp.ptr"]) (DL.dVA ++ labV) RW RV ∧
      r.wlen = st.wlen ∧ r.vlen = st.vlen ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + K * ((L.foldl (relaxInsCc (dlOps G s) (T l) B (some B'f)) ⟨d, g, Dc, 0⟩).c + 1)
        + C * (lW.length + 1))

/-- **Deletion of the `W'` row keys** (BM.29, B-L3): `delC g lW`. -/
def DelWB (DL : DLayer G s T) (delW : Stmt) : Prop :=
  ∀ (st : State ℝ≥0) (H : Hist G) (g : DGl G s) (Ds : ℕ → DStrM G s) (l : ℕ) (lW : List (Fin G.n)),
    DL.DR st H g Ds l → st.w "lvl" = l → st.w "n" = G.n →
    RowRep st "Wp" "Wp.len" G.n l (lW.map Fin.val) →
    Runs realOps delW st (fun r => DL.DR r H (delC g lW).1 Ds l ∧
      Unchanged st r DL.dWA DL.dVA DL.dWR DL.dVR ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost + DL.K * ((delC g lW).2 + lW.length + 1))

end ifaces

end Frontier.CHD.RamBody
