import Frontier.CHD.BL2InvStep

/-!
# Frontier.CHD.BL2InvRoot — B-L2: a non-tree root: init + search + (grow | fail-output) + clear
(agent-09, scratch, NON-GATE)
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}
variable {LI : LabI V ops G s} {X : LabX LI} {TI : TreeI V ops G s} {c : FPCtx G s}
  {slB slX sA : String} {SL : List (Fin G.n)} {d0 : Labels G s}

/-- Label layer across writes of FindPivots-private names. -/
theorem LabRep.frame_inv (hNI : NamesI LI X TI slB slX sA) {d : Labels G s} {g : LI.Gh}
    {st st' : State V} {wa wr : List String} (h : LabRep LI c slB slX d g st)
    (hu : Unchanged st st' wa [] wr []) (hwa : wa ⊆ invArrs ++ myWArrs)
    (hwr : wr ⊆ invRegs ++ myRegs ++ ["fp.sres", "fp.sgo"]) (hc : st.cost ≤ st'.cost) :
    LabRep LI c slB slX d g st' :=
  h.frame hu (hNI.inv_tab.mono_left hwa) (Disj.nil_left _) (hNI.inv_slB.mono_left hwa)
    (Disj.nil_left _) (hNI.invR_slB.mono_left hwr) (Disj.nil_left _)
    (hNI.inv_slX.mono_left hwa) (Disj.nil_left _) (hNI.invR_slX.mono_left hwr) (Disj.nil_left _) hc

/-- The forest across writes of FindPivots-private names. -/
theorem FR.frame_inv (hNI : NamesI LI X TI slB slX sA) {trees : List (Partition.TreeRec (Fin G.n))}
    {st st' : State V} {wa wr : List String} (h : TI.FR st trees)
    (hu : Unchanged st st' wa [] wr []) (hwa : wa ⊆ invArrs ++ myArrs.erase "fp.fm")
    (hwr : wr ⊆ invRegs ++ ["fp.hsz", "fp.kl", "fp.sres", "fp.sgo"]) : TI.FR st' trees :=
  TI.FR_frame h hu (hNI.namesT.fr_inv.mono_left hwa) (Disj.nil_left _)
    (hNI.namesT.fr_invR.mono_left hwr) (Disj.nil_left _)

theorem myArrs_sub_invWA : myArrs ⊆ invWA LI TI sA := by
  intro x hx; simp only [invWA, srchWA, scanWA, List.mem_append]; tauto
theorem invArrs_sub_invWA : invArrs ⊆ invWA LI TI sA := by
  intro x hx; simp only [invWA, List.mem_append]; tauto
theorem srchWA_sub_invWA : srchWA LI ⊆ invWA LI TI sA := by
  intro x hx; simp only [invWA, List.mem_append]; tauto
theorem gWA_sub_invWA : TI.gWA ⊆ invWA LI TI sA := by
  intro x hx; simp only [invWA, List.mem_append]; tauto
theorem srchVA_sub_invVA : srchVA LI ⊆ invVA LI TI := by
  intro x hx; simp only [invVA, List.mem_append]; tauto
theorem gVA_sub_invVA : TI.gVA ⊆ invVA LI TI := by
  intro x hx; simp only [invVA, List.mem_append]; tauto
theorem srchWR_sub_invWR : srchWR LI X ⊆ invWR LI X TI := by
  intro x hx; simp only [invWR, List.mem_append]; tauto
theorem myRegs_sub_invWR : myRegs ⊆ invWR LI X TI := by
  intro x hx; simp only [invWR, srchWR, scanWR, List.mem_append]; tauto
theorem gWR_sub_invWR : TI.gWR ⊆ invWR LI X TI := by
  intro x hx; simp only [invWR, List.mem_append]; tauto
theorem srchVR_sub_invVR : srchVR LI X ⊆ invVR LI X TI := by
  intro x hx; simp only [invVR, List.mem_append]; tauto
theorem gVR_sub_invVR : TI.gVR ⊆ invVR LI X TI := by
  intro x hx; simp only [invVR, List.mem_append]; tauto

end Frontier.CHD.BL2
