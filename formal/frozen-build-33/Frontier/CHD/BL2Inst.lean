import Frontier.CHD.BL2Find
import Frontier.CHD.IHeapLab
import Frontier.CHD.TreeRAM7

/-!
# Frontier.CHD.BL2Inst — B-L2 instantiated: `labI c0` (agent-02), `cmpTT` (agent-06), `treeImpl` (agent-03)
(owner agent-09, NON-GATE)

The name hygiene `NamesD` of the FindPivots-HD driver holds for the concrete layers, with the
slots `fp.B` / `fp.LX` and the roots in the spine's `S` row (decided).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.BL2Inst

open Frontier Frontier.RAM Frontier.CHD Frontier.CHD.BL2

variable {G : Graph} {s : Fin G.n}

/-- agent-06's table-vs-table compare as B-L2's `LabX` over agent-02's `labI c0`. -/
noncomputable def labX (c0 : ℕ) : LabX (LabIInst.labI (G := G) (s := s) c0) where
  ra := IHeapLab.ttRa
  rb := IHeapLab.ttRb
  cmpTT := IHeapLab.cmpLab IHeapLab.ttRa IHeapLab.ttRb "lab.bit"
  Ctt := 27
  ttWR := "lab.bit" :: IHeapLab.cmpScratchW
  ttVR := IHeapLab.lessV
  cmpTT_spec hLT ha hb hra hrb hbud := IHeapLab.cmpTT_spec c0 hLT ha hb hra hrb hbud

theorem namesL_inst (c0 : ℕ) :
    NamesL (LabIInst.labI (G := G) (s := s) c0) "S" "fp.B" "fp.LX" := by
  constructor <;> exact of_decide_eq_true rfl

theorem names_inst (c0 : ℕ) :
    Names (LabIInst.labI (G := G) (s := s) c0) "fp.B" "fp.LX" := by
  constructor <;> exact of_decide_eq_true rfl

theorem namesX_inst (c0 : ℕ) :
    NamesX (LabIInst.labI (G := G) (s := s) c0) (labX c0) "fp.B" "fp.LX" := by
  constructor <;> exact of_decide_eq_true rfl

theorem namesT_inst (c0 : ℕ) :
    NamesT (LabIInst.labI (G := G) (s := s) c0) (labX c0) (PartitionRAM.treeImpl ℝ≥0 realOps G s)
      "fp.B" "fp.LX" "S" := by
  constructor <;> exact of_decide_eq_true rfl

theorem namesI_inst (c0 : ℕ) :
    NamesI (LabIInst.labI (G := G) (s := s) c0) (labX c0) (PartitionRAM.treeImpl ℝ≥0 realOps G s)
      "fp.B" "fp.LX" "S" := by
  refine ⟨names_inst c0, namesX_inst c0, namesT_inst c0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact of_decide_eq_true rfl

theorem namesD_inst (c0 : ℕ) :
    NamesD (LabIInst.labI (G := G) (s := s) c0) (labX c0) (PartitionRAM.treeImpl ℝ≥0 realOps G s)
      "fp.B" "fp.LX" "S" := by
  refine ⟨namesL_inst c0, namesI_inst c0, ?_, ?_, ?_, ?_⟩ <;>
    exact of_decide_eq_true rfl

end Frontier.CHD.BL2Inst
