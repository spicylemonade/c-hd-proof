import Frontier.CHD.SpineLoop
import Frontier.CHD.RelW

/-!
# Frontier.CHD.RamBodyFinDefs — the definitions of the level body's finalization (owner agent-03)

**NON-GATE** (B-L4).  The names agent-01's `body_spec` composes against (the proof of `fin_spec`
is in `RamBodyFin`):
* `bpfOf B cs`: BM.24a's bound (`B` if the level's view is empty, else the loop's `B'`);
* `finRegs` / `finVRegs` / `FinNames`: the finalization's register names and their disjointness
  from the `D` layer and `φ` (decidable on the concrete instances);
* `Kfin`: the finalization's own-work constant;
* `FinPost`: the tail data of `BMLazy.CallD` plus the `CallOut` facts at level `l + 1`, relative
  to the loop-exit state, with the cost and the `D`-layer use.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamBody

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.RamLevel
  Frontier.CHD.BM Frontier.CHD.RamBaseCase Frontier.CHD.LabTab Frontier.CHD.RamSpine
  Frontier.CHD.WinScan WExpr Stmt

variable {G : Graph} {s : Fin G.n} {T : ℕ → ℕ} {Φ : Type}

/-- `B` if `e` holds, else `B'` (classical choice of the branch). -/
noncomputable def pickB (e : Prop) (B B' : WLab G s) : WLab G s := by
  classical exact if e then B else B'

theorem pickB_pos {e : Prop} {B B' : WLab G s} (h : e) : pickB e B B' = B := by
  unfold pickB; exact if_pos h

theorem pickB_neg {e : Prop} {B B' : WLab G s} (h : ¬ e) : pickB e B B' = B' := by
  unfold pickB; exact if_neg h

/-- BM.24a's final bound of a loop state: `B` if the level's view is empty, else its `B'`. -/
noncomputable def bpfOf (B : WLab G s) {p : ℕ} (cs : CSt G s p) : WLab G s :=
  pickB (cs.g.view cs.Dc).IsEmpty B cs.B'

/-- The word registers of agent-01's finalization tests (`RamBodyI.tstW`, literally). -/
def finTstW : List String :=
  ["sl.i", "t6.k1f", "t6.k1h", "t6.k1v", "t6.k1e", "t6.k1r", "t6.k2f", "t6.k2h", "t6.k2v", "t6.k2e",
    "t6.k2r", "t6.yf", "t6.yh", "t6.yv", "t6.ye", "t6.yr", "t6.c1", "t6.c2", "t6.l1", "t6.l2", "t6.b"]

/-- The value registers of the finalization tests (`RamBodyI.tstV`, literally). -/
def finTstV : List String := ["t6.k1l", "t6.k2l", "t6.yl"]

/-- The word registers the finalization writes outside the `D` layer and `spRegs`. -/
def finRegs : List String :=
  ["f24.kh", "f24.kv", "f24.ke", "f24.kr", "f24.kf", "t6.i"] ++ finTstW ++ ["rz.i"] ++ relWRegs

/-- The value registers the finalization writes outside the `D` layer. -/
def finVRegs : List String := ["f24.kl"] ++ finTstV ++ relaxV ++ ["rw.bl", "rw.ll"]

/-- **Name disjointness** of the finalization with the `D` layer and `φ` (decidable on the
concrete instances). -/
structure FinNames (DL : DLayer G s T) (PI : PhiI Φ) : Prop where
  dA : ∀ a ∈ DL.dWA, a ∉ ["Wp", "Wp.len"]
  dR : ∀ a ∈ DL.dWR, a ∉ finRegs ++ rwW ++ ["lab.uselo"]
  dV : ∀ a ∈ DL.dVR, a ∉ finVRegs
  pA : ∀ a ∈ PI.pWA, a ∉ spArrs ++ ["Wp", "Wp.len"] ++ DL.dWA
  pR : ∀ a ∈ PI.pWR, a ∉ finRegs ++ spRegs ++ DL.dWR

/-- **The deletion of the `W'` row keys** (BM.29) with the `D`-layer use kept (a delete creates no
entry or block): agent-01's `DelWB` plus `use r = use st`. -/
def DelWBU (DL : DLayer G s T) (delW : Stmt) : Prop :=
  ∀ (st : State ℝ≥0) (H : Hist G) (g : DGl G s) (Ds : ℕ → DStrM G s) (l : ℕ) (lW : List (Fin G.n)),
    DL.DR st H g Ds l → st.w "lvl" = l → st.w "n" = G.n →
    RowRep st "Wp" "Wp.len" G.n l (lW.map Fin.val) →
    Runs realOps delW st (fun r => DL.DR r H (delC g lW).1 Ds l ∧
      Unchanged st r DL.dWA DL.dVA DL.dWR DL.dVR ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost + DL.K * ((delC g lW).2 + lW.length + 1) ∧
      DL.use r = DL.use st)

/-- The own-work constant of the finalization. -/
def Kfin (K : ℕ) : ℕ := 3 * K + 300

/-- **The facts after the finalization** (the `CallOut` facts at level `l+1` relative to the
loop-exit state `st`, the tail data of `CallD`, the cost and the `D`-layer use). -/
structure FinPost (DL : DLayer G s T) (PI : PhiI Φ) (LF : ℕ) (body : Stmt) (τ Mf : ℕ → ℕ)
    (st r : State ℝ≥0) (l : ℕ) (B : WLab G s) (S W : Finset (Fin G.n)) (Ds : ℕ → DStrM G s)
    (H : Hist G) (c0 : ℕ) {p : ℕ} (c : LoopCfgD G s Φ p) (lT6 : List (Fin G.n))
    (W' : Finset (Fin G.n)) (lW' : List (Fin G.n)) (L : List (Fin G.m)) (H' : Hist G) : Prop where
  t6nd : lT6.Nodup
  t6mem : ∀ x, x ∈ lT6 ↔ x ∈ S ∧ bpfOf B c.cs ≤ c.cs.d x ∧ c.cs.d x < B
  wmem : ∀ x, x ∈ W' ↔ (x ∈ W ∧ x ∉ c.cs.U) ∧ c.cs.d x < bpfOf B c.cs
  enum : Enumerates G L W'
  wnd : lW'.Nodup
  wset : lW'.toFinset = W'
  lab : LabAt r (finD (dlOps G s) (T (l + 1)) B (bpfOf B c.cs) c.cs.d c.cs.g c.cs.Dc lT6 L lW').1 H' c0
  hext : HExt H (vc st) H' (vc r)
  D : DL.DR r H' (finD (dlOps G s) (T (l + 1)) B (bpfOf B c.cs) c.cs.d c.cs.g c.cs.Dc lT6 L lW').2.1
    (Function.update Ds (l + 1)
      (finD (dlOps G s) (T (l + 1)) B (bpfOf B c.cs) c.cs.d c.cs.g c.cs.Dc lT6 L lW').2.2.1) (l + 1)
  phi : PI.PhiR r c.φ
  U : SetRow r "U" "U.len" (l + 1) (c.cs.U ∪ W')
  sBp : SlotHolds r (slotBp (l + 1)) H' (vc r) (bpfOf B c.cs)
  ptr : ∀ u ∈ c.cs.U ∪ W',
    PtrOK r (finD (dlOps G s) (T (l + 1)) B (bpfOf B c.cs) c.cs.d c.cs.g c.cs.Dc lT6 L lW').1 B u
  ptrFr : ∀ x : Fin G.n, x ∉ W' → r.wa "sp.ptr" x = st.wa "sp.ptr" x
  clr : Clear r G.n (l + 1)
  above : Above st r G.n (l + 1)
  stArr : ∀ a ∈ ["gSt", "gHead", "cp.tau", "cp.M", "gKeep", "gRep"], r.wa a = st.wa a
  stat : Static r G LF body τ Mf
  lvl : r.w "lvl" = l + 1
  coreR : ∀ z ∈ ["core.n", "core.s", "core.m"], r.w z = st.w z
  cost1 : st.cost ≤ r.cost
  cost2 : r.cost ≤ st.cost + Kfin DL.K * (1 + S.card + W.card + W'.card +
    (finD (dlOps G s) (T (l + 1)) B (bpfOf B c.cs) c.cs.d c.cs.g c.cs.Dc lT6 L lW').2.2.2) +
    3 * c.cs.U.card + 100
  use : DL.use r ≤ DL.use st + S.card +
    (finD (dlOps G s) (T (l + 1)) B (bpfOf B c.cs) c.cs.d c.cs.g c.cs.Dc lT6 L lW').2.2.2

end Frontier.CHD.RamBody
