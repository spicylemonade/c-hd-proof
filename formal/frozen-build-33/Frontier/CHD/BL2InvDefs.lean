import Frontier.CHD.BL2InvFail2

/-!
# Frontier.CHD.BL2InvDefs — B-L2: representation and loop invariant of the invocation loop
(agent-09, scratch, NON-GATE)
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}

variable (LI : LabI V ops G s) (X : LabX LI) (TI : TreeI V ops G s)

/-- Machine representation of an invocation state (between roots). -/
structure IRep (c : FPCtx G s) (slB slX : String) (ι : IState G s) (g : LI.Gh) (st : State V) :
    Prop where
  lab : LabRep LI c slB slX ι.d g st
  my : MyRep c ι.tv (emptySt ι.d ι.D) st
  out : OutRep st c ι.D
  fr : TI.FR st ι.trees
  W : WRep st ι.W
  Q : QRep st ι.Q

/-- Write sets of the invocation loop. -/
def invWA (sA : String) : List String := srchWA LI ++ invArrs ++ TI.gWA ++ TI.iWA
def invVA : List String := srchVA LI ++ TI.gVA ++ TI.iVA
/-- Registers WRITTEN by the invocation loop itself (`fp.sb`, `fp.sn`, `fp.ob` are read-only). -/
def invWRegs : List String := ["fp.x", "fp.j", "fp.wl", "fp.ql", "fp.i", "fp.y"]
/-- Registers of the invocation loop that live across a search (`fp.i`, `fp.y` are scratch). -/
def invKeep : List String := ["fp.x", "fp.j", "fp.sb", "fp.sn", "fp.ob", "fp.wl", "fp.ql"]
def invWR : List String := srchWR LI X ++ invWRegs ++ TI.gWR ++ TI.iWR
def invVR : List String := srchVR LI X ++ TI.gVR ++ TI.iVR

/-- Per-root cost factor. -/
def KI : ℕ := KS LI X + TI.Cg + 60

/-- Bookkeeping of the invocation loop. -/
structure IBook (sA : String) (st₀ st : State V) (n : ℕ) : Prop where
  unch : Unchanged st₀ st (invWA LI TI sA) (invVA LI TI) (invWR LI X TI) (invVR LI X TI)
  cost0 : st₀.cost ≤ st.cost
  cost : st.cost ≤ st₀.cost + TI.Cinit + 4 + KI LI X TI * n

/-- Name hygiene of the invocation loop (discharged by `decide` at instantiation). -/
structure NamesI (slB slX sA : String) : Prop where
  names : Names LI slB slX
  namesX : NamesX LI X slB slX
  namesT : NamesT LI X TI slB slX sA
  /-- the search does not clobber the invocation registers / arrays -/
  srch_inv : Disj (srchWR LI X) invKeep
  srch_invA : Disj (srchWA LI) (invArrs ++ [sA])
  /-- the invocation's own arrays/registers are outside the label layer -/
  inv_tab : Disj (invArrs ++ myWArrs) LI.tabWA
  inv_slB : Disj (invArrs ++ myWArrs) (LI.slWA slB)
  inv_slX : Disj (invArrs ++ myWArrs) (LI.slWA slX)
  invR_slB : Disj (invRegs ++ myRegs ++ ["fp.sres", "fp.sgo"]) (LI.slWR slB)
  invR_slX : Disj (invRegs ++ myRegs ++ ["fp.sres", "fp.sgo"]) (LI.slWR slX)
  sA_my : sA ∉ myArrs ++ invArrs

variable (c : FPCtx G s) (slB slX sA : String) (SL : List (Fin G.n)) (d0 : Labels G s)

/-- Running invocation: roots `SL.take j` processed, Layer A at `ι` with accumulated cost `n`. -/
structure IRun (ι₀ : IState G s) (g₀ : LI.Gh) (st₀ : State V) (ι : IState G s) (j n : ℕ)
    (g : LI.Gh) (st : State V) : Prop where
  rep : IRep LI TI c slB slX ι g st
  jreg : st.w "fp.j" = j
  jle : j ≤ SL.length
  walk : WalkInv ι.d
  le : ∀ v, ι.d v ≤ d0 v
  finv : FInv c ι
  Qsub : ∀ q ∈ ι.Q, q ∈ SL.take j
  hist : LI.gext g₀ g
  cont : ∀ ι'' n', Invoke c ι (SL.drop j) ι'' n' → Invoke c ι₀ SL ι'' (n + n')
  book : IBook LI X TI sA st₀ st n

/-- Loop invariant of the invocation loop. -/
def ILoopI (ι₀ : IState G s) (g₀ : LI.Gh) (st₀ : State V) (m : ℕ) (st : State V) : Prop :=
  ∃ ι j n g, m = SL.length - j ∧ IRun LI X TI c slB slX sA SL d0 ι₀ g₀ st₀ ι j n g st

end Frontier.CHD.BL2
