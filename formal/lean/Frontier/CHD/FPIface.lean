import Frontier.CHD.SlotList
import Frontier.CHD.FindPivots

/-!
# Frontier.CHD.FPIface — B-L2 (FindPivots-HD at RAM level): the label-layer interface and the
representation of a local-search state (owner agent-09, NON-GATE)

The RAM FindPivots-HD code never touches values itself: every label operation is a fragment of
the label layer B-LAB (agent-02).  `LabI` lists exactly what B-L2 needs from B-LAB, as abstract
predicates and fragment specifications with write sets (agent-08's `Unchanged` convention):

* `LT st d g` : the label table represents the Layer-A labels `d` under ghost history `g`;
* `LS st sl L g` : the label slot `sl` (e.g. the bound `B`, the threshold `L_X`) represents `L`;
* `LC st d g e` : the table represents `d` AND the candidate registers hold `ext (d (src e)) e`;
* `candB sl` (FH.8): candidate for the edge in register `re` from the tail in `ru`, and
  `bit := [cand < slot]`;
* `cmpTS sl` (FH.9): `bit := [d[rv] < slot]`;
* `relaxC` (FH.11/14/20): from the candidate registers, `ok := [cand ≤ d[rv]]`, and the table
  becomes `relaxL d (src e) e` (write + version bump only on a strict decrease).

Word-cap discipline (agent-08's ruling R1/R2): every fragment spec asks the RELATIVE budget
`st.cost + C ≤ c0 + st.cap`, where `c0` is the clock origin of the label layer (the body's start
cost); B-LAB keeps all growing table words `≤ st.cost - c0`.

Footprints versus write sets: `tabWA`/`tabVA` is the footprint of `LT` (it may include read-only
graph arrays such as `gHead`/`gW`); `relWA`/`relVA` is what `relaxC` actually writes.
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM

/-- Two name lists are disjoint. -/
def Disj (l₁ l₂ : List String) : Prop := ∀ x ∈ l₁, x ∉ l₂

theorem Disj.nil_left (l : List String) : Disj [] l := fun _ h => absurd h List.not_mem_nil

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}

open Classical in
/-- **What B-L2 needs from B-LAB** (to be instantiated by agent-02's LabTab fragments). -/
structure LabI (V : Type) (ops : VOps V) (G : Graph) (s : Fin G.n) where
  /-- clock origin of the label layer (budgets are relative to it) -/
  c0 : ℕ
  /-- ghost history and its extension preorder -/
  Gh : Type
  gext : Gh → Gh → Prop
  gext_refl : ∀ g, gext g g
  gext_trans : ∀ {g₁ g₂ g₃}, gext g₁ g₂ → gext g₂ g₃ → gext g₁ g₃
  /-- the label table represents `d` -/
  LT : State V → Labels G s → Gh → Prop
  /-- label slot `sl` represents `L` -/
  LS : State V → String → WLab G s → Gh → Prop
  /-- table + candidate registers for edge `e` -/
  LC : State V → Labels G s → Gh → Fin G.m → Prop
  LC_LT : ∀ {st d g e}, LC st d g e → LT st d g
  LS_ext : ∀ {st sl L g g'}, LS st sl L g → gext g g' → LS st sl L g'
  /-- footprints: table arrays, candidate registers, slot cells -/
  tabWA : List String
  tabVA : List String
  cWR : List String
  cVR : List String
  slWA : String → List String
  slVA : String → List String
  slWR : String → List String
  slVR : String → List String
  LT_frame : ∀ {st st' : State V} {d g wa va wr vr}, LT st d g → Unchanged st st' wa va wr vr →
    Disj wa tabWA → Disj va tabVA → st.cost ≤ st'.cost → LT st' d g
  LC_frame : ∀ {st st' : State V} {d g e wa va wr vr}, LC st d g e → Unchanged st st' wa va wr vr →
    Disj wa tabWA → Disj va tabVA → Disj wr cWR → Disj vr cVR → st.cost ≤ st'.cost → LC st' d g e
  LS_frame : ∀ {st st' : State V} {sl L g wa va wr vr}, LS st sl L g → Unchanged st st' wa va wr vr →
    Disj wa (slWA sl) → Disj va (slVA sl) → Disj wr (slWR sl) → Disj vr (slVR sl) → LS st' sl L g
  /-- interface registers -/
  ru : String
  re : String
  rv : String
  bit : String
  ok : String
  /-- fragments -/
  candB : String → Stmt
  cmpTS : String → Stmt
  relaxC : Stmt
  Ccand : ℕ
  Ccmp : ℕ
  Crel : ℕ
  /-- register write sets (relaxC also writes the table arrays) -/
  candWR : List String
  candVR : List String
  cmpWR : List String
  cmpVR : List String
  relWR : List String
  relVR : List String
  relWA : List String
  relVA : List String
  candB_spec : ∀ {st : State V} {d g} {sl : String} {B : WLab G s} {e : Fin G.m},
    LT st d g → LS st sl B g → d (G.src e) ≠ ⊤ →
    st.w ru = G.src e → st.w re = e → st.cost + Ccand ≤ c0 + st.cap →
    Runs ops (candB sl) st (fun st' => LC st' d g e ∧
      st'.w bit = (if ext (d (G.src e)) e < B then 1 else 0) ∧
      Unchanged st st' [] [] candWR candVR ∧ st.cost ≤ st'.cost ∧ st'.cost ≤ st.cost + Ccand)
  cmpTS_spec : ∀ {st : State V} {d g} {sl : String} {L : WLab G s} {v : Fin G.n},
    LT st d g → LS st sl L g → st.w rv = v → st.cost + Ccmp ≤ c0 + st.cap →
    Runs ops (cmpTS sl) st (fun st' =>
      st'.w bit = (if d v < L then 1 else 0) ∧
      Unchanged st st' [] [] cmpWR cmpVR ∧ st.cost ≤ st'.cost ∧ st'.cost ≤ st.cost + Ccmp)
  relaxC_spec : ∀ {st : State V} {d g} {e : Fin G.m},
    LC st d g e → st.w rv = G.dst e → st.cost + Crel ≤ c0 + st.cap →
    Runs ops relaxC st (fun st' => ∃ g', gext g g' ∧ LT st' (relaxL d (G.src e) e) g' ∧
      st'.w ok = (if Ok d (G.src e) e then 1 else 0) ∧
      Unchanged st st' relWA relVA relWR relVR ∧ st.cost ≤ st'.cost ∧ st'.cost ≤ st.cost + Crel)
  /-- FH.1 (L_X = d_B[S]): slot copy `dst := src` and slot load `dst := d[rv]` (finite labels) -/
  copySS : String → String → Stmt
  loadTS : String → Stmt
  Ccopy : ℕ
  cpWR : List String
  cpVR : List String
  copySS_spec : ∀ {st : State V} {g} {src dst : String} {L : WLab G s},
    LS st src L g → st.cost + Ccopy ≤ c0 + st.cap →
    Runs ops (copySS src dst) st (fun st' => LS st' dst L g ∧
      Unchanged st st' (slWA dst) (slVA dst) (slWR dst ++ cpWR) (slVR dst ++ cpVR) ∧
      st.cost ≤ st'.cost ∧ st'.cost ≤ st.cost + Ccopy)
  loadTS_spec : ∀ {st : State V} {d g} {dst : String} {v : Fin G.n},
    LT st d g → st.w rv = v → st.cost + Ccopy ≤ c0 + st.cap →
    Runs ops (loadTS dst) st (fun st' => LS st' dst (d v) g ∧
      Unchanged st st' (slWA dst) (slVA dst) (slWR dst ++ cpWR) (slVR dst ++ cpVR) ∧
      st.cost ≤ st'.cost ∧ st'.cost ≤ st.cost + Ccopy)
  /-- structural facts -/
  bit_candWR : bit ∈ candWR
  bit_cmpWR : bit ∈ cmpWR
  ok_relWR : ok ∈ relWR
  cmp_cWR : Disj cmpWR cWR
  cmp_cVR : Disj cmpVR cVR
  ru_cWR : ru ∉ cWR
  re_cWR : re ∉ cWR
  rv_cWR : rv ∉ cWR

end Frontier.CHD.BL2
