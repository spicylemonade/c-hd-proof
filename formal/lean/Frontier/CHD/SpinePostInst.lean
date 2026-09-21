import Frontier.CHD.SpinePost
import Frontier.CHD.CmpTTI

/-!
# SpinePostInst — the B-LAB compare meets `CmpFam` (agent-06, B-L4, NON-GATE)

agent-02's `WinScan.cmpTT_cmpI` (the B-LAB table–table compare `cmpLab "tt.ra" "tt.rb" "lab.bit"` as
agent-01's `RamInit.CmpI`) gives `SpinePost.CmpFam` for every `D` layer: the key representation
`cmpKR` survives the `D` layer's insertion footprint because the `D` layer never writes the label
arrays.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamSpine

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.IHeapLab

variable {G : Graph} {s : Fin G.n} {T : ℕ → ℕ}

/-- **The comparison hypothesis of `postSpec`**, for B-LAB's `cmpTT`. -/
theorem cmpFam_cmpTT (DL : DLayer G s T) (c0 : ℕ) :
    CmpFam DL (cmpLab ttRa ttRb "lab.bit") 27 ("lab.bit" :: cmpScratchW) lessV c0 := by
  intro d H r0 hL
  refine ⟨WinScan.cmpKR d c0 r0.cap, ⟨⟨H, hL⟩, rfl⟩, WinScan.cmpTT_cmpI d H c0 r0 hL, ?_⟩
  intro st r hK hU hc
  refine hK.frame hU (fun a ha h => ?_) (fun h => DL.dVA_ok _ h (by simp [labV])) hc
  rcases List.mem_cons.mp h with h | h
  · subst h; revert ha; decide
  · exact DL.dWA_ok _ h ((by decide : ∀ b ∈ labW, b ∈ spArrs) a ha)

end Frontier.CHD.RamSpine
