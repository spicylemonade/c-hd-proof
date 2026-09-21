import Frontier.CHD.L6.StepInst
import Frontier.CHD.RamBodyFin
import Frontier.CHD.RamBodyFinB
import Frontier.CHD.DDelW
import Frontier.CHD.CSRSortedOf

/-!
# FinInst — the finalization input `hFin` of the C-HD level step (agent-01, B-L4, NON-GATE)

`hFin_of_parts` is exactly the `hFin` hypothesis of agent-10's `L6.hs_of_parts`: for every
instance and every level `l < LF`, agent-03's `fin_spec` (as `fin_spec_stmt`) gives agent-01's
`FinB` of the finalization `finProg emptyS tstT6 insS tstWp (relW insS) delW`, with the uniform
own-work constant
`Kfin KD`, `C = 100` and the static constant `finCst H K NB`.  `CSRSorted` is discharged inside
(agent-02's `csrSorted_of_outL`); `delW` with `DelWBU` is `DDelW.dsDelW` on a `mkDL` D layer
(`DDelW.delWBU_mkDL`).  What is left are the closed D texts, the name facts `FinNames`
(decidable on the instance) and `DL.K ≤ KD`.
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.RamLevel Frontier.CHD.BM
  Frontier.CHD.RamBaseCase Frontier.CHD.LabTab Frontier.CHD.RamSpine Frontier.CHD.RamInit
  Frontier.CHD.RamBody Frontier.CHD.WinScan WExpr Stmt

/-- **The finalization input of `hs_of_parts`.** -/
theorem hFin_of_parts
    {DLf : ∀ (H : Graph) (src : Fin H.n) (_cn _cm : ℕ), RamSpine.DLayer H src Tz}
    {emptyS insS delW : Stmt}
    (hemp : ∀ H src cn cm, (DLf H src cn cm).empty = emptyS)
    (hins : ∀ H src cn cm, (DLf H src cn cm).ins = insS)
    (hFN : ∀ H src cn cm, FinNames (DLf H src cn cm) (PIfOf chdP H src cn cm))
    (hDel : ∀ H src cn cm, DelWBU (DLf H src cn cm) delW)
    {KD : ℕ} (hKD : ∀ H src cn cm, (DLf H src cn cm).K ≤ KD) {body : Stmt} :
    ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm →
      ∀ l : ℕ, l < CostSkeleton.LF cn cm →
      FinB (DLf H src cn cm) (PIfOf chdP H src cn cm) (CostSkeleton.LF cn cm) body
        (BM.chdTau (CostSkeleton.tF cn cm)) (BM.chdM (CostSkeleton.tF cn cm))
        (finProg emptyS tstT6 insS tstWp (relW insS) delW) (Kfin KD) 100
        (finCst H (DLf H src cn cm).K (DLf H src cn cm).NB) l := by
  intro H src cn cm hMI l hl
  exact finB_uniform (DLf H src cn cm) (PIfOf chdP H src cn cm) (hemp H src cn cm)
    (hins H src cn cm)
    (fin_spec_stmt (DLf H src cn cm) (PIfOf chdP H src cn cm) (hFN H src cn cm)
      (hDel H src cn cm) (WinScan.csrSorted_of_outL hMI.sorted))
    (hKD H src cn cm) l hl

end Frontier.CHD.L6

#print axioms Frontier.CHD.L6.hFin_of_parts
