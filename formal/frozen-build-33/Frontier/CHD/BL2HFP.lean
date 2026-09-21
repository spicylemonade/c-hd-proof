import Frontier.CHD.BL2Step
import Frontier.CHD.DLayerF
import Frontier.CHD.L6.Assembly

/-!
# `hFP`, `hD`, `hucapF`, `hPd` for the concrete D layer (owner agent-09, NON-GATE)

`hFP_chd`: agent-10's `hs_of_parts` hypothesis `hFP` for agent-04's `DLI.DLf Tz` (the D layer of
the C-HD spine) and every body text; the three name facts are decided on the concrete lists (the register fact via the closed literal
`fpWRlit`, `fpAtWR_lit := rfl`, and `decide +kernel`). Also the route's `hD` (`dProSpecC`), `hucapF`
and `hPd` in the exact shapes of `chdTarget_of_step` / `chdProg_of_DLayer`.
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM Frontier.CHD

set_option maxRecDepth 200000 in
theorem dlf_fpWA (H : Graph) (src : Fin H.n) :
    ∀ a ∈ DLI.drWA ++ DLI.xWA, a ∉ BL2Inst.fpAtWA (G := H) (s := src) := of_decide_eq_true rfl
set_option maxRecDepth 200000 in
theorem dlf_fpVA (H : Graph) (src : Fin H.n) :
    ∀ a ∈ DLI.drVA ++ DLI.xVA, a ∉ BL2Inst.fpAtVA (G := H) (s := src) := of_decide_eq_true rfl
/-- the FindPivots register write set as a closed literal (with its repetitions) -/
def fpWRlit : List String :=
  ["sl.i", "fp.B#f", "fp.B#h", "fp.B#v", "fp.B#e", "fp.B#r", "fp.sb", "fp.sn", "fp.LX#h", "fp.LX#v", "fp.LX#e", "fp.LX#r", "fp.LX#f", "fp.j", "lab.rv", "lab.yf", "lab.yh", "lab.yv", "lab.ye", "lab.yr", "lab.c1", "lab.c2", "lab.bit", "fp.u", "fp.p", "fp.pp", "fp.v", "fp.go", "fp.res", "fp.kl", "fp.k", "fp.hsz", "fp.cu", "fp.cv", "gM", "ru", "re", "lab.rv", "lab.xh", "lab.xv", "lab.xe", "lab.xr", "lab.c1", "lab.c2", "lab.bit", "lab.yf", "lab.yh", "lab.yv", "lab.ye", "lab.yr", "lab.c1", "lab.c2", "lab.bit", "lab.xh", "lab.xv", "lab.xe", "lab.xr", "lab.yh", "lab.yv", "lab.ye", "lab.yr", "lab.yf", "lab.c1", "lab.c2", "lab.lt", "lab.gt", "lab.lb", "ok", "fp.bi", "fp.i", "fp.t", "fp.u", "fp.hsz", "tt.ra", "tt.rb", "lab.bit", "hq_xf", "hq_yf", "hq_c1", "hq_c2", "hq_xh", "hq_xv", "hq_xe", "hq_xr", "hq_yh", "hq_yv", "hq_ye", "hq_yr", "fp.sres", "fp.sgo", "fp.x", "fp.j", "fp.wl", "fp.ql", "fp.i", "fp.y", "tr.t", "tr.w", "tr.a", "tr.pv", "tr.j", "tr.nt", "tr.c", "tr.f", "tr.u", "tr.x", "tr.nt", "ct.t", "ct.o", "ct.i", "ct.l", "ct.w", "fp.nt", "mk.j", "mk.e", "mk.x", "pt.km1", "pt.v", "pt.p", "pt.ap", "pt.av", "pt.np", "pt.i", "pt.np0", "pt.r", "pt.g", "pt.t", "pt.b", "pt.len", "pt.gs", "pt.x", "pt.c", "pt.gv", "pt.tS", "pt.tQ", "pt.tA", "pt.ng", "pt.g", "pt.j", "fp.i", "fp.y"]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
theorem fpAtWR_lit {G : Graph} {s : Fin G.n} : BL2Inst.fpAtWR (G := G) (s := s) = fpWRlit := rfl

set_option maxRecDepth 200000 in
/-- the D layer's register names avoid FindPivots' register writes (closed lists, kernel-decided) -/
theorem dlf_fpWR_lit : ∀ a ∈ DLI.wrD ++ DLI.xWR, a ∉ fpWRlit := by decide +kernel

theorem dlf_fpWR (H : Graph) (src : Fin H.n) :
    ∀ a ∈ DLI.wrD ++ DLI.xWR, a ∉ BL2Inst.fpAtWR (G := H) (s := src) := by
  rw [fpAtWR_lit]; exact dlf_fpWR_lit

/-- **`hFP` of `hs_of_parts` for the C-HD D layer** (`DLI.DLf Tz`), every body text. -/
theorem hFP_chd (body : Stmt) :
    ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm →
      ∀ l : ℕ, l < CostSkeleton.LF cn cm →
      RamBody.FPB (DLI.DLf (G := H) (s := src) Tz cn cm) (PIfOf chdP H src cn cm) (DelInv H src)
        (fpC H src (outL H) (CostSkeleton.kF cn cm) (chdP cn cm).hins (chdP cn cm).hext)
        (CostSkeleton.LF cn cm) body BL2Inst.fpAtRaw
        (BM.chdTau (CostSkeleton.tF cn cm)) (BM.chdM (CostSkeleton.tF cn cm)) 524 351 (l + 1) :=
  hFP_of (DLf := fun H src cn cm => DLI.DLf (G := H) (s := src) Tz cn cm)
    (fun H src _ _ => dlf_fpWA H src) (fun H src _ _ => dlf_fpVA H src)
    (fun H src _ _ => dlf_fpWR H src) body

/-- **The route's `hD` for the C-HD D layer**, in the exact shape of `chdTarget_of_step` /
`chdProg_of_step` (`DLf := DLI.DLf Tz`, procedure table `chdPs … [selBody entLess 1]`). -/
theorem hD_chd (e : ℕ) (he : 32 ≤ e) (newS insS recC : Stmt) :
    HookSpec e (chdPs newS insS recC [SelectRAM.selBody SelectRAM.entLess 1]) DPro.dProC
      (fun H src cn cm r => (∃ Ds : ℕ → BM.DStrM H src,
          (DLI.DLf (G := H) (s := src) Tz cn cm).DR r (LabRAM.H0 (G := H)) BM.DGl.init Ds
            (CostSkeleton.LF cn cm + 1)) ∧
        (DLI.DLf (G := H) (s := src) Tz cn cm).use r ≤ 2)
      DPro.dProWA DPro.dProVA DPro.dProWR [] (DPro.dKd (12 * kmN)) :=
  DPro.dProSpecC e he _ rfl

/-- **The route's `hucapF`** for the C-HD D layer. -/
theorem hucapF_chd : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ),
    12 * kmN * CostSkeleton.Tnat cn cm + 2 ≤ (DLI.DLf (G := H) (s := src) Tz cn cm).ucap :=
  fun _ _ cn cm => DPro.dParC_ucap cn cm

/-- **The route's `hPd`** for the C-HD cost parameters. -/
theorem hPd_chd : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ),
    (∀ a ∈ (PIfOf chdP H src cn cm).pWA, a ∉ DPro.dProWA) ∧
      (∀ a ∈ (PIfOf chdP H src cn cm).pWR, a ∉ DPro.dProWR) :=
  DPro.hPd_dPro chdP

end Frontier.CHD.L6

#print axioms Frontier.CHD.L6.hFP_chd
#print axioms Frontier.CHD.L6.hD_chd
#print axioms Frontier.CHD.L6.hucapF_chd
#print axioms Frontier.CHD.L6.hPd_chd
