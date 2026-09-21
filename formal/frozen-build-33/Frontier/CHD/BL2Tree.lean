import Frontier.CHD.BL2SearchSpec

/-!
# Frontier.CHD.BL2Tree — B-L2: interface of the RAM tree layer (FH.12 / FH.23)
(owner agent-09; implementation agent-03; NON-GATE)

After a successful or contact search, the forest of the invocation grows exactly as Layer A's
`growForest res trees x σ'` (new tree `⟨x, K, kpar⟩` on success; `mergeTree` into the tree of the
contact head on contact), and the tree-vertex bitmap `fp.fm` grows by `K`.  `TreeI` is what the
B-L2 invocation loop (agent-09) needs from the tree layer (agent-03):

* `FR st trees` : the RAM forest represents the Layer-A forest `trees`;
* `init` : an empty forest;
* `grow` : one `growForest` step, reading the search output left by `fpSearch`:
  `fp.K[0..fp.kl)` (= `K` in arrival order), `fp.kp[v]` (= `kpar v` on `K`), `fp.x` (root),
  `fp.sres` (2 = contact / 3 = success), `(fp.cu, fp.cv)` (= `hit` on contact).
Layer-A hypotheses of `grow_spec` are exactly those of agent-05's `growForest_inv`.
Words of the tree layer are vertex ids / positions (`≤ n`), so only `n + 2 < cap` is assumed.
The tree arrays are allocated ONCE (length `≥ n`, clean marks): predicate `TA` (agent-03's
`TAlloc`), established at program start and preserved by every fragment (`FR_TA`).
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}

/-- **What the B-L2 invocation loop needs from the RAM tree layer.** -/
structure TreeI (V : Type) (ops : VOps V) (G : Graph) (s : Fin G.n) where
  /-- the RAM forest represents a Layer-A forest -/
  FR : State V → List (Partition.TreeRec (Fin G.n)) → Prop
  /-- footprint of `FR` -/
  frWA : List String
  frVA : List String
  frWR : List String
  frVR : List String
  FR_frame : ∀ {st st' : State V} {trees wa va wr vr}, FR st trees →
    Unchanged st st' wa va wr vr → Disj wa frWA → Disj va frVA → Disj wr frWR → Disj vr frVR →
    FR st' trees
  /-- the tree arrays are allocated once (length ≥ n) and clean (agent-03's `TAlloc`) -/
  TA : State V → Prop
  TA_frame : ∀ {st st' : State V} {wa va wr vr}, TA st →
    Unchanged st st' wa va wr vr → Disj wa frWA → Disj va frVA → Disj wr frWR → Disj vr frVR →
    TA st'
  FR_TA : ∀ {st : State V} {trees}, FR st trees → TA st
  /-- the empty forest -/
  init : Stmt
  Cinit : ℕ
  iWA : List String
  iVA : List String
  iWR : List String
  iVR : List String
  init_spec : ∀ {st : State V}, TA st → G.n + 2 < st.cap →
    Runs ops init st (fun st' => FR st' [] ∧ Unchanged st st' iWA iVA iWR iVR ∧
      st.cost ≤ st'.cost ∧ st'.cost ≤ st.cost + Cinit)
  /-- one `growForest` step (FH.12 contact merge / FH.23 new tree) -/
  grow : Stmt
  Cg : ℕ
  gWA : List String
  gVA : List String
  gWR : List String
  gVR : List String
  grow_spec : ∀ {st : State V} {c : FPCtx G s} {ι : IState G s} {x : Fin G.n} {σ' : SSt G s}
    {res : SearchRes} {n : ℕ},
    OutOK c → OutSorted c → x ∉ ι.tv → res ≠ .failed →
    Search c ι.tv (initSt ι.d ι.D x) σ' res n → SInv c (initSt ι.d ι.D x) → FInv c ι →
    FR st ι.trees → Bits st "fp.fm" ι.tv →
    LArr st "fp.K" σ'.K → st.w "fp.kl" = σ'.K.length → σ'.K.length ≤ st.wlen "fp.K" →
    st.wlen "fp.kp" = G.n → (∀ v ∈ σ'.K, st.wa "fp.kp" v = σ'.kpar v) → st.w "fp.x" = x →
    (res = .contact → ∃ a b : Fin G.n, σ'.hit = some (a, b) ∧ st.w "fp.cu" = a ∧
      st.w "fp.cv" = b) →
    SResCode st res → G.n + 2 < st.cap →
    Runs ops grow st (fun st' => FR st' (growForest res ι.trees x σ') ∧
      Bits st' "fp.fm" (ι.tv ∪ σ'.K.toFinset) ∧
      Unchanged st st' gWA gVA gWR gVR ∧
      st.cost ≤ st'.cost ∧ st'.cost ≤ st.cost + Cg * (σ'.K.length + 1))

/-- Registers of the invocation loop (agent-09). -/
def invRegs : List String :=
  ["fp.x", "fp.j", "fp.sb", "fp.sn", "fp.ob", "fp.wl", "fp.ql", "fp.i", "fp.y"]

/-- Arrays of the invocation loop (agent-09). -/
def invArrs : List String := ["fp.W", "fp.inW", "fp.Q"]

/-- Name hygiene between the tree layer and the rest of FindPivots-HD (discharged by `decide`
once the tree layer's names are fixed).  `sA` is the array holding the roots. -/
structure NamesT (LI : LabI V ops G s) (X : LabX LI) (TI : TreeI V ops G s) (slB slX sA : String) :
    Prop where
  /-- the tree layer writes `fp.fm` and its own arrays only -/
  gWA_ok : Disj TI.gWA (List.erase myArrs "fp.fm" ++ invArrs ++ [sA] ++ LI.tabWA ++
    LI.slWA slB ++ LI.slWA slX)
  gWR_ok : Disj TI.gWR (myRegs ++ extRegs ++ ["fp.sres", "fp.sgo"] ++ invRegs ++ LI.slWR slB ++
    LI.slWR slX)
  gVA_ok : Disj TI.gVA (LI.tabVA ++ LI.slVA slB ++ LI.slVA slX)
  gVR_ok : Disj TI.gVR (LI.slVR slB ++ LI.slVR slX)
  iWA_ok : Disj TI.iWA (myArrs ++ invArrs ++ [sA] ++ LI.tabWA ++ LI.slWA slB ++ LI.slWA slX)
  iWR_ok : Disj TI.iWR (myRegs ++ extRegs ++ ["fp.sres", "fp.sgo"] ++ invRegs ++ LI.slWR slB ++
    LI.slWR slX)
  iVA_ok : Disj TI.iVA (LI.tabVA ++ LI.slVA slB ++ LI.slVA slX)
  iVR_ok : Disj TI.iVR (LI.slVR slB ++ LI.slVR slX)
  /-- the rest of FindPivots-HD never writes the forest -/
  fr_srch : Disj (srchWA LI) TI.frWA
  fr_srchR : Disj (srchWR LI X) TI.frWR
  fr_srchV : Disj (srchVA LI) TI.frVA
  fr_srchVR : Disj (srchVR LI X) TI.frVR
  fr_inv : Disj (invArrs ++ myArrs.erase "fp.fm") TI.frWA
  fr_invR : Disj (invRegs ++ ["fp.hsz", "fp.kl", "fp.sres", "fp.sgo"]) TI.frWR

end Frontier.CHD.BL2
