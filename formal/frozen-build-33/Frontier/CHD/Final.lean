import Frontier.CHD.L6.FinalGen
import Frontier.CHD.DLayerF
import Frontier.CHD.DDelW
import Frontier.CHD.RamBodyFinB
import Frontier.CHD.RamBodyFin
import Frontier.CHD.DProInst
import Frontier.CHD.CSRSortedOf

/-!
# The C-HD Gate-C theorem: final assembly (agent-10)

`chdProgram`: ONE closed RAM program, uniform over all inputs, with word exponent 160:
* the dispatcher, with the Bellman–Ford fallback;
* L6 preprocessing;
* the core: parameters, per-level tables, the label table, the spine prologue
  `spinePro BL2.fpAlloc dProC`, and the top-level call;
* the output mapping.
Its procedure table is `[bmsspProc (baseProgC dsNew dsIns) recC, selBody entLess 1]`.

`chd_exact_within`: `chdProgram` is exact on every graph and source, and runs within
`C · Tdisp F n m`.  Hence `chd_CHDTarget : GateCTarget.CHDTarget GateCCalc.F` and
`chd_gateC : Frontier.GateC`.

The name-disjointness side conditions are decided by the kernel (`decide +kernel`) on the closed
lists, at a one-vertex dummy instance.  They transfer to every instance by definitional unfolding:
the D-layer, B-L2, base-case and FindPivots name lists do not depend on the instance.
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.Final

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.RamLevel Frontier.CHD.BM
  Frontier.CHD.RamBaseCase Frontier.CHD.LabTab Frontier.CHD.RamSpine Frontier.CHD.RamInit
  Frontier.CHD.RamBody Frontier.CHD.L6 WExpr Stmt

/-! ## The program -/

/-- The D-layer family of the C-HD program (agent-04's `DLayerF.DLf`). -/
noncomputable abbrev DLfC : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), RamSpine.DLayer H src Tz :=
  fun H src cn cm => DLI.DLf (G := H) (s := src) Tz cn cm

/-- The finalization text. -/
abbrev finPC : Stmt := finProg DLI.dsEmpty tstT6 DLI.dsIns tstWp (WinScan.relW DLI.dsIns) DDelW.dsDelW

/-- The level body. -/
abbrev recC : Stmt :=
  recText BL2Inst.fpAtRaw DLI.dsNew DLI.dsIns DLI.dsEmpty
    (iterText DLI.pullD DLI.dsMerge DLI.dsDelB DLI.dsIns) finPC

/-- The procedure table. -/
abbrev psC : List Stmt := chdPs DLI.dsNew DLI.dsIns recC [SelectRAM.selBody SelectRAM.entLess 1]

/-- The core. -/
abbrev coreC : Stmt := coreTop (spineOf (spinePro BL2.fpAlloc DPro.dProC))

/-- **The C-HD witness program.** -/
def chdProgram : Program := chdProg 160 psC coreC

/-- The constants. -/
abbrev KD : ℕ := PullWrap.Kpw + 6
abbrev KoC : ℕ := 4 * KD + 322
abbrev KC : ℕ := 210000

theorem hKD : KD = 23037 := by
  unfold KD PullWrap.Kpw DPull.Kpull DPull.Kcol DPull.Knc; rfl

/-! ## The name facts, at a closed dummy instance -/

/-- A one-vertex dummy graph (only to state the closed name facts). -/
def G1 : Graph := ⟨1, 0, Fin.elim0, Fin.elim0, Fin.elim0⟩
def s1 : Fin G1.n := ⟨0, Nat.one_pos⟩

noncomputable abbrev DL1 : RamSpine.DLayer G1 s1 Tz := DLfC G1 s1 0 0
abbrev PI1 : RamSpine.PhiI (Finset (Fin G1.m)) := PIfOf chdP G1 s1 0 0

set_option maxRecDepth 400000

theorem n_DW : ∀ a ∈ RamBaseCase.baseWR (IHeapLab.heapI G1 s1 (KhF 0 0)) ++ RamSpine.ptrLoopWR,
    a ∉ DL1.dWR := by decide +kernel
theorem n_PW : ∀ a ∈ PI1.pWR,
    a ∉ RamBaseCase.baseWR (IHeapLab.heapI G1 s1 (KhF 0 0)) ++ RamSpine.ptrLoopWR ++ DL1.dWR := by
  decide +kernel
theorem n_PA : ∀ a ∈ PI1.pWA, a ∉ DL1.dWA := by decide +kernel
theorem n_Pb1 : ∀ a ∈ PI1.pWA, a ∉ slotW ++ ["S", "S.len"] := by decide +kernel
theorem n_Pb2 : ∀ a ∈ PI1.pWR, a ∉ blowWR ++ ["lvl"] := by decide +kernel
theorem n_foot : SpineFoot psC :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem n_body : BodyNames DL1 PI1 [] :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem n_post : PostHyg DL1 PI1 ("lab.bit" :: IHeapLab.cmpScratchW) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem n_LWd : ∀ a ∈ WinScan.ltW, a ∉ DL1.dWR := by decide +kernel
theorem n_LWp : ∀ a ∈ WinScan.ltW, a ∉ PI1.pWR := by decide +kernel
theorem n_DP : ∀ a ∈ DL1.dWA, a ∉ PI1.pWA := by decide +kernel
theorem n_DPr : ∀ a ∈ DL1.dWR, a ∉ PI1.pWR := by decide +kernel
theorem n_DLA : ∀ a ∈ DL1.dWA, a ∉ BL2Inst.fpAtWA (G := G1) (s := s1) := by decide +kernel
theorem n_DLV : ∀ a ∈ DL1.dVA, a ∉ BL2Inst.fpAtVA (G := G1) (s := s1) := by decide +kernel
theorem n_DLR : ∀ a ∈ DL1.dWR, a ∉ BL2Inst.fpAtWR (G := G1) (s := s1) := by decide +kernel
theorem n_fin : FinNames DL1 PI1 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## The theorem -/

/-- The run-time constant of the witness. -/
noncomputable abbrev KcC : ℝ :=
  ((KC : ℝ) + (13000 + 34 * ((100 : ℕ) + (DPro.dKd (12 * kmN) : ℝ))) + 0) * (kmaster 1 1 1000 + 1) + 250

set_option maxHeartbeats 8000000 in
/-- **The C-HD witness program is exact and runs within `C · Tdisp F n m`.** -/
theorem chd_exact_within :
    chdProgram.Exact ∧ ∀ (G : Graph) (s : Fin G.n),
      chdProgram.RunsWithin G s ((bodyC KcC + 65536 * 9 + 100) * GateCTarget.Tdisp GateCCalc.F G.n G.m) := by
  have hK := hKD
  have hKC : KC = 210000 := rfl
  have hKoC : KoC = 4 * KD + 322 := rfl
  exact chdProg_of_DLayer 160 (by norm_num) (DLf := DLfC) (newS := DLI.dsNew) (insS := DLI.dsIns)
    (emptyS := DLI.dsEmpty) (pullS := DLI.pullD) (mergeS := DLI.dsMerge) (delBS := DLI.dsDelB)
    (finP := finPC) (dPro := DPro.dProC) [SelectRAM.selBody SelectRAM.entLess 1]
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (KD := KD) (K := KC) (Ko := KoC) (Kfin := RamBody.Kfin KD) (Cfin := 100)
    (fun _ _ _ _ => le_rfl)
    (by unfold RamBody.Kfin; omega) (by omega)
    (fun _ _ _ _ => by show KD + 22 + 71 + postK KD 27 + 1 ≤ KoC; unfold postK; omega)
    (fun _ _ cn cm => DPro.dParC_ucap cn cm)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ _ => by show KD ≤ KC; omega)
    (fun _ _ cn cm => by show CostSkeleton.LF cn cm ≤ CostSkeleton.LF cn cm + 1; omega)
    (DPro.dProSpecC 160 (by norm_num) psC rfl)
    (fun H src cn cm hMI l hl => finB_uniform (DLfC H src cn cm) (PIfOf chdP H src cn cm) rfl rfl
      (fin_spec_stmt (DLfC H src cn cm) (PIfOf chdP H src cn cm)
        ⟨n_fin.dA, n_fin.dR, n_fin.dV, n_fin.pA, n_fin.pR⟩
        (DDelW.delWBU_mkDL _ _ _ _ _ _ _ _ _ _ _ _ _) (WinScan.csrSorted_of_outL hMI.sorted))
      le_rfl l hl)
    (fun _ _ _ _ => n_DW) (fun _ _ _ _ => n_PW) (fun _ _ _ _ => n_PA) (DPro.hPd_dPro chdP)
    (fun _ _ _ _ => ⟨n_Pb1, n_Pb2⟩)
    n_foot
    (RW := [])
    (fun _ _ _ _ => ⟨n_body.dR, n_body.dA, n_body.pR, n_body.pA, n_body.rW⟩)
    (fun _ _ _ _ => ⟨n_post.lab, n_post.vr, n_post.blkW, n_post.blkV, n_post.CWd, n_post.gdel,
      n_post.pA, n_post.pR⟩)
    (fun _ _ _ _ => n_LWd) (fun _ _ _ _ => n_LWp) (fun _ _ _ _ => n_DP) (fun _ _ _ _ => n_DPr)
    (fun _ _ _ _ => n_DLA) (fun _ _ _ _ => n_DLV) (fun _ _ _ _ => n_DLR)
    (hbig160 (by norm_num) (by unfold DPro.dKd; have := kmN_le; omega))

/-- **The frozen Gate-C target.** -/
theorem chd_CHDTarget : GateCTarget.CHDTarget GateCCalc.F :=
  ⟨chdProgram, chd_exact_within.1, bodyC KcC + 65536 * 9 + 100, chd_exact_within.2⟩

/-- **Gate C** (CostModel v2): a strict worst-case improvement over `O(m + n log n)` along a density
profile inside the window where Dijkstra is the best known bound. -/
theorem chd_gateC : Frontier.GateC := GateCTarget.chdTarget_F_imp_gateC chd_CHDTarget

end Frontier.CHD.Final

#print axioms Frontier.CHD.Final.chd_exact_within
#print axioms Frontier.CHD.Final.chd_CHDTarget
#print axioms Frontier.CHD.Final.chd_gateC
