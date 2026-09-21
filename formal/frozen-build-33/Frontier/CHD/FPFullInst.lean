import Frontier.CHD.FPFull
import Frontier.CHD.BL2Inst

/-!
# Frontier.CHD.FPFullInst — name hygiene of the complete FindPivots-HD program, decided (owner agent-03)

**NON-GATE** (Layer B).  For agent-02's `labI c0` with slots `fp.B` / `fp.LX` and roots in the spine's `S` row (as in
agent-09's `BL2Inst.namesD_inst`), the tail's name conditions `NamesTail` and `NamesFull` hold, by kernel evaluation.
Together with `namesD_inst`, every name hypothesis of `fpFull_spec` is discharged for the concrete layers.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.BL2Inst

open Frontier Frontier.RAM Frontier.CHD Frontier.CHD.BL2

variable {G : Graph} {s : Fin G.n}

theorem namesTail_inst (c0 : ℕ) :
    NamesTail (LabIInst.labI (G := G) (s := s) c0) "fp.B" "fp.LX" "S" := by
  constructor <;> exact of_decide_eq_true rfl

theorem namesFull_inst (c0 : ℕ) :
    NamesFull (LabIInst.labI (G := G) (s := s) c0) "fp.B" "fp.LX" "S" :=
  ⟨namesTail_inst c0, of_decide_eq_true rfl⟩

end Frontier.CHD.BL2Inst
