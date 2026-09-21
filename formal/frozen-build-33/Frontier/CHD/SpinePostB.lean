import Frontier.CHD.SpinePostA
import Frontier.CHD.SpinePostProof
import Frontier.CHD.SpinePostInst

/-!
# SpinePostB — the loop's `PostHalf` for B-LAB's compare (agent-06, B-L4, NON-GATE)

agent-08's adapter `postHalf_of_stmt` applied to the proved `postSpec` and `cmpFam_cmpTT`: the second
half of an iteration, with re-selection by `cmpLab "tt.ra" "tt.rb" "lab.bit"`, is the main loop's
`PostHalf`, with no hypothesis left besides the name facts, the sorted CSR, the sub-call's Layer-A
contracts and the slack.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamSpine

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.IHeapLab

variable {G : Graph} {s : Fin G.n} {T : ℕ → ℕ} {Φ Ω : Type}

/-- **The second half of the iteration is the loop's `PostHalf`** (B-LAB's `cmpTT`). -/
theorem postHalf_cmpTT (DL : DLayer G s T) (PI : PhiI Φ) {LF : ℕ} {body : Stmt} {τf Mf : ℕ → ℕ}
    {Inv : Φ → Prop} {FPC : BM.FPRelC G s Φ Ω} {DCb : BM.DCost} {l Sl : ℕ}
    (hy : PostHyg DL PI ("lab.bit" :: cmpScratchW)) (hsort : WinScan.CSRSorted G s)
    {subC : BM.SubRelC G s Φ Ω}
    (hsimsub : BM.SimSub G s (BM.dlOps G s) τf Inv Mf l (BM.BMSSPD G s (BM.dlOps G s) FPC DCb T Mf τf l)
      subC) (hsubC : BM.GoodSub G s τf Inv l subC)
    (hSl : postS DL.K 27 G.n G.m (2 * DL.NB) ≤ Sl) (hLT : LF ≤ DL.LT) :
    PostHalf DL PI LF body τf Mf Inv FPC DCb l
      (postProg DL.merge DL.delB DL.ins DL.empty (cmpLab ttRa ttRb "lab.bit")) (postK DL.K 27) Sl :=
  postHalf_of_stmt DL PI (postSpec DL PI LF body τf Mf _ 27 _ _ Ω) hy (cmpFam_cmpTT DL) hsort hsimsub
    hsubC hSl hLT

end Frontier.CHD.RamSpine
