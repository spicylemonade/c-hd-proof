import Frontier.CHD.BL2Phi
import Frontier.CHD.IHeapLab
import Frontier.CHD.RamBaseCase
import Frontier.CHD.PtrLoop

/-!
# Frontier.CHD.BL2Side — decidable side conditions of the final assembly for B-L2 (owner agent-09, NON-GATE)

For agent-10's `L6.chdTarget_of_step`: B-L2's persistent registers `phWR` (the `pWR` of `phiI`)
avoid the base case's heap writes and the pointer loop (`hPW`, except for the D-layer part `DL.dWR`,
which is decided on agent-04's instance).
-/

open Frontier Frontier.CHD Frontier.CHD.BL2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `hPW` (base-case and pointer-loop part) for B-L2's persistent registers. -/
theorem Frontier.CHD.BL2.phWR_base (H : Graph) (src : Fin H.n) (K : ℕ) :
    ∀ a ∈ phWR, a ∉ RamBaseCase.baseWR (IHeapLab.heapI H src K) ++ RamSpine.ptrLoopWR :=
  of_decide_eq_true rfl
