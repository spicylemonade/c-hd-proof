import Frontier.CHD.BL2Inst
import Frontier.CHD.LabIC

/-!
# Frontier.CHD.BL2Comp — B-L2: FindPivots-HD as a closed computable `Stmt` (owner agent-09, NON-GATE)

`LabIInst.labI c0` and `BL2Inst.labX c0` are `noncomputable` only because they bundle proofs
over `ℝ≥0`; the B-L2 program reads only their `Stmt` / name fields.  `labIP` / `labXP` below are
PROGRAM-ONLY copies: the same fragments, names, costs and write sets, with EMPTY predicates
(their specs hold vacuously), over a computable value domain and a one-vertex graph.  They are
never used in a correctness proof: their only purpose is `fpFindC`, a closed computable `Stmt`,
and `fpFind_eq_C`, which says that the verified interface form of FindPivots-HD
(`fpFind (labI c0) (labX c0) treeImpl "S" "fp.B" "fp.LX"`, for every graph and clock origin) IS
this program, by `rfl` (reviewer #1's 16:04 plan).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.BL2Inst

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.BL2 Frontier.CHD.LabIInst

/-- A computable value domain (only to host the program-only instances). -/
def natOps : VOps ℕ := ⟨0, (· + ·), fun a b => decide (a ≤ b)⟩

/-- A one-vertex graph (only to host the program-only instances). -/
def G1 : Graph := ⟨1, 0, Fin.elim0, Fin.elim0, Fin.elim0⟩

/-- The vertex of `G1`. -/
def s1 : Fin G1.n := ⟨0, Nat.one_pos⟩

/-- **Program-only copy of `labI`** (empty predicates; see the module doc). -/
def labIP : LabI ℕ natOps G1 s1 where
  c0 := 0
  Gh := Unit
  gext _ _ := True
  gext_refl _ := trivial
  gext_trans _ _ := trivial
  LT _ _ _ := False
  LS _ _ _ _ := False
  LC _ _ _ _ := False
  LC_LT h := h.elim
  LS_ext h _ := h.elim
  tabWA := labW ++ ["gHead"]
  tabVA := labV ++ ["gW"]
  cWR := X0.ws
  cVR := [X0.l]
  slWA _ := []
  slVA _ := []
  slWR sl := (slotBlk sl).ws ++ [slotF sl]
  slVR sl := [(slotBlk sl).l]
  LT_frame h _ _ _ _ := h.elim
  LC_frame h _ _ _ _ _ _ := h.elim
  LS_frame h _ _ _ _ _ := h.elim
  ru := "ru"
  re := "re"
  rv := "lab.rv"
  bit := "lab.bit"
  ok := "ok"
  candB sl := LabRAM.candB (slotBlk sl) (slotF sl) "lab.bit"
  cmpTS sl := headLtB "lab.rv" Y0 (slotBlk sl) "lab.yf" (slotF sl) "lab.c1" "lab.c2" "lab.bit"
  relaxC := relaxCore
  Ccand := 32
  Ccmp := 22
  Crel := 42
  candWR := X0.ws ++ ["lab.c1", "lab.c2", "lab.bit"]
  candVR := [X0.l]
  cmpWR := ("lab.yf" :: Y0.ws) ++ ["lab.c1", "lab.c2", "lab.bit"]
  cmpVR := [Y0.l]
  relWR := relaxW
  relVR := relaxV
  relWA := labW
  relVA := labV
  candB_spec h _ _ _ _ _ := h.elim
  cmpTS_spec h _ _ _ := h.elim
  relaxC_spec h _ _ := h.elim
  copySS src dst := copyBlk (slotBlk src) (slotBlk dst) (slotF src) (slotF dst)
  loadTS dst := loadLab "lab.rv" (slotBlk dst) (slotF dst)
  Ccopy := 6
  cpWR := []
  cpVR := []
  copySS_spec h _ := h.elim
  loadTS_spec h _ _ := h.elim
  bit_candWR := by decide
  bit_cmpWR := by decide
  ok_relWR := by decide
  cmp_cWR := by unfold Disj; decide
  cmp_cVR := by unfold Disj; decide
  ru_cWR := by decide
  re_cWR := by decide
  rv_cWR := by decide

/-- **Program-only copy of `labX`** (empty predicates). -/
def labXP : LabX labIP where
  ra := IHeapLab.ttRa
  rb := IHeapLab.ttRb
  cmpTT := IHeapLab.cmpLab IHeapLab.ttRa IHeapLab.ttRb "lab.bit"
  Ctt := 27
  ttWR := "lab.bit" :: IHeapLab.cmpScratchW
  ttVR := IHeapLab.lessV
  cmpTT_spec h _ _ _ _ _ := h.elim

/-- **FindPivots-HD (FH.1–FH.25) as a closed, computable `Stmt`.** -/
def fpFindC : Stmt :=
  fpFind labIP labXP (PartitionRAM.treeImpl ℕ natOps G1 s1) "S" "fp.B" "fp.LX"

/-- **The verified interface form is the computable program**, for every graph, source and
clock origin. -/
theorem fpFind_eq_C {G : Graph} {s : Fin G.n} (c0 : ℕ) :
    fpFind (LabIInst.labI (G := G) (s := s) c0) (labX c0) (PartitionRAM.treeImpl ℝ≥0 realOps G s)
      "S" "fp.B" "fp.LX" = fpFindC := rfl

end Frontier.CHD.BL2Inst
