import Frontier.CHD.L6.StepInst
import Frontier.CHD.BL2AtRaw

/-!
# B-L2's input to the C-HD level step (owner agent-09, NON-GATE)

`hFP_of`: agent-10's `hs_of_parts` hypothesis `hFP` (FindPivots at level `l + 1` is agent-01's
`FPB`, with `Kf = 524`, `Cf = 351`, `fp = fpAtRaw`) for every body text and every D layer whose
names avoid the FindPivots write sets (three decidable facts on the concrete `DLf`).  Discharged
here: `2 ≤ kF`, `kF ≤ hext` (`chdP.hext = kF`), and the sortedness of the out-lists (`MasterIn`).
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM Frontier.CHD

/-- **`hFP` of `hs_of_parts`** from the D layer's name facts. -/
theorem hFP_of {DLf : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), RamSpine.DLayer H src Tz}
    (hDLA : ∀ H src cn cm, ∀ a ∈ (DLf H src cn cm).dWA, a ∉ BL2Inst.fpAtWA (G := H) (s := src))
    (hDLV : ∀ H src cn cm, ∀ a ∈ (DLf H src cn cm).dVA, a ∉ BL2Inst.fpAtVA (G := H) (s := src))
    (hDLR : ∀ H src cn cm, ∀ a ∈ (DLf H src cn cm).dWR, a ∉ BL2Inst.fpAtWR (G := H) (s := src))
    (body : Stmt) :
    ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm →
      ∀ l : ℕ, l < CostSkeleton.LF cn cm →
      RamBody.FPB (DLf H src cn cm) (PIfOf chdP H src cn cm) (DelInv H src)
        (fpC H src (outL H) (CostSkeleton.kF cn cm) (chdP cn cm).hins (chdP cn cm).hext)
        (CostSkeleton.LF cn cm) body BL2Inst.fpAtRaw
        (BM.chdTau (CostSkeleton.tF cn cm)) (BM.chdM (CostSkeleton.tF cn cm)) 524 351 (l + 1) :=
  fun H src cn cm hMI _ _ => BL2Inst.fpB_raw (DLf H src cn cm) (DelInv H src)
    (CostSkeleton.two_le_kF cn cm) le_rfl hMI.sorted (hDLA H src cn cm) (hDLV H src cn cm)
    (hDLR H src cn cm)

end Frontier.CHD.L6

#print axioms Frontier.CHD.L6.hFP_of
