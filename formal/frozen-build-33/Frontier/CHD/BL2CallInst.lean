import Frontier.CHD.BL2Call
import Frontier.CHD.BL2Comp

/-!
# Frontier.CHD.BL2CallInst — the complete FindPivots-HD call, instantiated (owner agent-09, NON-GATE)

* `namesTail_inst`, `namesCall_inst`: the remaining name hygiene of `fpCall_spec` holds for
  `labI c0`, `labX c0`, slots `fp.B` / `fp.LX` and the roots array `S` (kernel evaluation);
* `fpCallC`: the complete call as a closed computable `Stmt`, `rfl`-equal to the interface form.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.BL2Inst

open Frontier Frontier.RAM Frontier.CHD Frontier.CHD.BL2 Frontier.CHD.PartitionRAM

variable {G : Graph} {s : Fin G.n}

set_option maxRecDepth 100000 in
theorem namesTail_inst (c0 : ℕ) :
    NamesTail (LabIInst.labI (G := G) (s := s) c0) "fp.B" "fp.LX" "S" := by
  constructor <;> exact of_decide_eq_true rfl

set_option maxRecDepth 100000 in
theorem namesCall_inst (c0 : ℕ) :
    NamesCall (LabIInst.labI (G := G) (s := s) c0) (labX c0) "fp.B" "fp.LX" "S" := by
  constructor <;> exact of_decide_eq_true rfl

/-- **The complete FindPivots-HD call as a closed, computable `Stmt`.** -/
def fpCallC : Stmt := fpCall (V := ℕ) (ops := natOps) labIP labXP "S" "fp.B" "fp.LX"

/-- The verified interface form of the complete call IS the computable program. -/
theorem fpCall_eq_C {G : Graph} {s : Fin G.n} (c0 : ℕ) :
    fpCall (V := ℝ≥0) (ops := realOps) (LabIInst.labI (G := G) (s := s) c0) (labX c0)
      "S" "fp.B" "fp.LX" = fpCallC := rfl

end Frontier.CHD.BL2Inst
