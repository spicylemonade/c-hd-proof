import Frontier.CHD.LabI

/-!
# LabIC — the program fields of `labI` are plain computable `Stmt` definitions (agent-02, NON-GATE)

`LabIInst.labI c0` is a `noncomputable def` only because it bundles proofs.  Its `Stmt` fields
reduce by `rfl` to the concrete (computable, axiom-free) B-LAB fragments below, so a final
`Program` can be written with these directly and related to the interface form by `rfl`
(reviewer #1's 16:04 plan: witness `chdProgramC` with `body_eq : … := rfl`).
-/

namespace Frontier.CHD.LabIInst

open Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD.BL2

variable {G : Graph} {s : Fin G.n}

theorem labI_candB (c0 : ℕ) (sl : String) :
    (labI (G := G) (s := s) c0).candB sl = LabRAM.candB (slotBlk sl) (slotF sl) "lab.bit" := rfl

theorem labI_cmpTS (c0 : ℕ) (sl : String) :
    (labI (G := G) (s := s) c0).cmpTS sl =
      headLtB "lab.rv" Y0 (slotBlk sl) "lab.yf" (slotF sl) "lab.c1" "lab.c2" "lab.bit" := rfl

theorem labI_relaxC (c0 : ℕ) : (labI (G := G) (s := s) c0).relaxC = relaxCore := rfl

theorem labI_copySS (c0 : ℕ) (src dst : String) :
    (labI (G := G) (s := s) c0).copySS src dst =
      copyBlk (slotBlk src) (slotBlk dst) (slotF src) (slotF dst) := rfl

theorem labI_loadTS (c0 : ℕ) (dst : String) :
    (labI (G := G) (s := s) c0).loadTS dst = loadLab "lab.rv" (slotBlk dst) (slotF dst) := rfl

end Frontier.CHD.LabIInst
