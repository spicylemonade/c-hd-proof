import Frontier.CHD.WinScanE
import Frontier.CHD.SpineLoop

/-!
# WinScanF — agent-08's `DLayer` gives the scans' D interface (agent-02, NON-GATE)

`DInsI.ofDLayer DL` builds the `DInsI` of `WinScanE` from a `RamSpine.DLayer` (fields `DR`,
footprints, frame, `K`, `ins`, `ins_spec`).  Three footprint facts are not (yet) fields of
`DLayer` and are taken as arguments: the D layer does not write the graph weights `gW`, the
B-LAB registers of the relaxation/`lo` test, or the B-LAB value registers `lab.xl/lab.yl`.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.WinScan

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.MLab Frontier.CHD.LabTab
  Frontier.CHD.DIns Frontier.CHD.RelaxIns Frontier.CHD.RamBaseCase WExpr Stmt

variable {G : Graph} {s : Fin G.n}

/-- **The scans' D interface from agent-08's `DLayer`.** -/
def DInsI.ofDLayer {T : ℕ → ℕ} (DL : RamSpine.DLayer G s T) (hgW : "gW" ∉ DL.dVA)
    (hlab : ∀ a ∈ DL.dWR, a ∉ rwW ++ ["lab.uselo"]) (hvr : ∀ a ∈ DL.dVR, a ∉ relaxV) :
    DInsI G s T where
  DR := DL.DR
  dWA := DL.dWA
  dVA := DL.dVA
  dWR := DL.dWR
  dVR := DL.dVR
  frame := fun st r H H' g Ds lo wa va wr vr hD hU hwa hva hwr _ hE =>
    DL.frame st r H H' g Ds lo wa va wr vr hD hU (fun a ha h => hwa a h ha)
      (fun a ha h => hva a h ha) (fun a ha h => hwr a h ha) hE
  K := DL.K
  use := DL.use
  ucap := DL.ucap
  use_frame := fun st r wa va wr vr hU hwr =>
    DL.use_frame st r wa va wr vr hU (fun a ha h => hwr a h ha)
  ins := DL.ins
  ins_spec := DL.ins_spec
  hwa := fun a ha h => DL.dWA_ok a ha
    ((by decide : ∀ b ∈ labW ++ ["gSt", "gHead", "sp.ptr"], b ∈ RamSpine.spArrs) a h)
  hva := fun a ha h => by
    rcases List.mem_append.mp h with h' | h'
    · exact DL.dVA_ok a ha (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h'))
    · rw [List.mem_singleton] at h'; subst h'; exact hgW ha
  hwr := fun a ha h => by
    rcases (by decide : ∀ b ∈ scanRegs, b ∈ rwW ++ ["lab.uselo"] ∨ b ∈ RamSpine.spRegs) a h
      with h' | h'
    · exact hlab a ha h'
    · exact DL.dWR_ok a ha h'
  hvr := hvr

end Frontier.CHD.WinScan
