import Frontier.CHD.BMPlace
import Frontier.CHD.DLazySharp
import Frontier.CHD.DPsi
import Frontier.CHD.TraceSize

/-!
# Frontier.CHD.BMTele — telescoping the lazy structure's actual costs (L4-COST, O23/O6c glue)

Owner: agent-01.  NON-GATE.

Over agent-04's `DLazy` (`dlOps`), every `D` operation satisfies a FAMILY amortized bound:
`actual + Φ' ≤ Φ + charge`, where `Φ` = `potM` of the operated structure + `2·staleCnt` of all
OTHER structures (whose potential only changes through the live map).  Charges:
* pull: `735|S'| + 950` (agent-06's `pullM_amortized_sharp`);
* insert: `insCharge Dc = bsCost #blocks + 438 + 210·ell M (E+1) + 2` (agent-04's
  `insertM_amortized` + one entry of the others made stale);
* delete: `5|ks| + 1`; merge: `14` (`mergeM_amortized`); new structure: `potM = 3`.

This file proves those family bounds and their scan versions.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

section defs

/-- The potential of the OTHER structures (their blocks `os`): only their stale entries depend on
the live map. -/
noncomputable def othP (L : LiveM G s) (os : List (DB.Block (Fin G.n) (WLab G s))) : ℕ := 2 * DB.staleCnt L os

/-- The amortized charge of one insertion into `Dc` (DLazy). -/
noncomputable def insCharge (Dc : DStrM G s) : ℕ :=
  DL.bsCost Dc.blocks.length + 438 + 210 * DL.ell Dc.M (entCount Dc + 1) + 2

/-- The potential of a structure over the live map of a global state. -/
noncomputable def potG (g : DGl G s) (Dc : DStrM G s) : ℕ := DL.potM g.L Dc

end defs

section ops

variable {T : ℕ}

theorem ins_tele {B : WLab G s} {f0 : ℕ} {g : DGl G s} {Dc : DStrM G s}
    (h : SInv G s (dlOps G s) B f0 g Dc) (v : Fin G.n) (lam : WLab G s)
    {os : List (DB.Block (Fin G.n) (WLab G s))} (hos : ∀ x ∈ DB.allEnts os, x.id < g.fresh)
    (hnd : ((DB.allEnts os).map (·.id)).Nodup) :
    (insC (dlOps G s) T g Dc v lam).2.2 +
        potG (insC (dlOps G s) T g Dc v lam).1 (insC (dlOps G s) T g Dc v lam).2.1 +
        othP (insC (dlOps G s) T g Dc v lam).1.L os ≤
      potG g Dc + othP g.L os + insCharge Dc := by
  have h1 := DL.insertM_amortized (L := g.L) (fresh := g.fresh) (D := Dc) (v := v) (lam := lam)
    h.wf h.fr h.ids h.M1
  have h2 := DL.staleCnt_insertL_others (L := g.L) (fresh := g.fresh) (D := Dc) (v := v)
    (lam := lam) hos hnd
  show (DL.insertL g.L g.fresh Dc v lam).2.2.2 +
      DL.potM (DL.insertL g.L g.fresh Dc v lam).1 (DL.insertL g.L g.fresh Dc v lam).2.2.1 +
      2 * DB.staleCnt (DL.insertL g.L g.fresh Dc v lam).1 os ≤
    DL.potM g.L Dc + 2 * DB.staleCnt g.L os + insCharge Dc
  unfold insCharge entCount
  omega

theorem pull_tele {B : WLab G s} {f0 : ℕ} {g : DGl G s} {Dc : DStrM G s}
    (h : SInv G s (dlOps G s) B f0 g Dc) (hK : DB.KeyInj g.L (kof G s))
    {os : List (DB.Block (Fin G.n) (WLab G s))}
    (hdisj : ∀ x ∈ DB.allEnts Dc.blocks, ∀ z ∈ DB.allEnts os, x.id ≠ z.id) :
    (pullC (dlOps G s) T g Dc).2.2.2.2 +
        potG (pullC (dlOps G s) T g Dc).2.2.1 (pullC (dlOps G s) T g Dc).2.2.2.1 +
        othP (pullC (dlOps G s) T g Dc).2.2.1.L os ≤
      potG g Dc + othP g.L os + (735 * (pullC (dlOps G s) T g Dc).1.length + 950) := by
  have h1 := DL.pullM_amortized_sharp (L := g.L) (D := Dc) h.wf hK h.ids h.M1
  have h2 := DL.staleCnt_pullL_others (L := g.L) (D := Dc) (os := os) h.wf hdisj
  show (DL.pullL 1 g.L Dc).2.2.2.2 + DL.potM (DL.pullL 1 g.L Dc).2.2.1 (DL.pullL 1 g.L Dc).2.2.2.1 +
      2 * DB.staleCnt (DL.pullL 1 g.L Dc).2.2.1 os ≤
    DL.potM g.L Dc + 2 * DB.staleCnt g.L os + (735 * (DL.pullL 1 g.L Dc).1.length + 950)
  omega

theorem del_tele {g : DGl G s} {Dc : DStrM G s} (hid : DB.IdsNodup Dc) (ks : List (Fin G.n))
    {os : List (DB.Block (Fin G.n) (WLab G s))} (hnd : ((DB.allEnts os).map (·.id)).Nodup) :
    (delC g ks).2 + potG (delC g ks).1 Dc + othP (delC g ks).1.L os ≤
      potG g Dc + othP g.L os + (5 * ks.length + 1) := by
  have h1 := DL.deleteKeys_amortizedL (L := g.L) (D := Dc) (ks := ks) hid
  have h2 := DB.staleCnt_clearKeys_le (L := g.L) (ks := ks) (os := os) hnd
  show (DB.deleteKeys g.L ks).2 + DL.potM (DB.deleteKeys g.L ks).1 Dc +
      2 * DB.staleCnt (DB.deleteKeys g.L ks).1 os ≤
    DL.potM g.L Dc + 2 * DB.staleCnt g.L os + (5 * ks.length + 1)
  simp only [DL.potM] at h1 ⊢
  have h3 : (DB.deleteKeys g.L ks).1 = DB.clearKeys g.L ks := rfl
  rw [h3] at h1 ⊢
  omega

theorem merge_tele {L : LiveM G s} {D D' : DStrM G s} (hne : D.blocks ≠ []) (hM' : 1 ≤ D'.M)
    (h3 : 3 * D'.M ≤ D.M) :
    ((dlOps G s).merge T D D').2 + DL.potM L ((dlOps G s).merge T D D').1 ≤
      DL.potM L D + DL.potM L D' + 14 :=
  DL.mergeM_amortized hne hM' h3

/-- The potential of a parent structure plus its others is its `L`-free part plus the others'
potential of the child (whose others are the parent's blocks and the parent's others). -/
theorem potM_split (L : LiveM G s) (D : DStrM G s) (os : List (DB.Block (Fin G.n) (WLab G s))) :
    DL.potM L D + othP L os = (DL.spot D.M D.blocks + DL.epot D) + othP L (D.blocks ++ os) := by
  simp only [DL.potM, DL.potL, othP, DB.staleCnt_append]
  ring

/-- A new structure has potential `3`. -/
theorem potG_newC (g : DGl G s) (M : ℕ) (Bd : WLab G s) : potG g (newC M Bd) = 3 :=
  DL.potM_new g.L M Bd

end ops

section scans

variable {T : ℕ}

/-! ### The block-count potential through the operations -/

theorem ins_psi {B : WLab G s} {f0 : ℕ} {g : DGl G s} {Dc : DStrM G s}
    (h : SInv G s (dlOps G s) B f0 g Dc) (v : Fin G.n) (lam : WLab G s) :
    DL.psi (insC (dlOps G s) T g Dc v lam).2.1 ≤ DL.psi Dc + 2 :=
  DL.psi_insertL (L := g.L) (fresh := g.fresh) (v := v) (lam := lam) h.wf.1

theorem relax_psi {B : WLab G s} {f0 : ℕ} (lo : Option (WLab G s)) (st : RSt G s) (e : Fin G.m)
    (h : SInv G s (dlOps G s) B f0 st.g st.Dc) :
    DL.psi (relaxInsCc (dlOps G s) T B lo st e).Dc ≤ DL.psi st.Dc + 2 := by
  classical
  have hins := ins_psi (T := T) h (G.dst e) (ext (st.d (G.src e)) e)
  unfold relaxInsCc
  split_ifs with hv
  · cases lo with
    | none => exact hins
    | some b =>
      simp only
      split_ifs
      · exact hins
      · show DL.psi st.Dc ≤ _
        omega
  · show DL.psi st.Dc ≤ _
    omega

theorem fold_psi {B : WLab G s} {f0 : ℕ} (lo : Option (WLab G s)) :
    ∀ (L : List (Fin G.m)) (st : RSt G s), SInv G s (dlOps G s) B f0 st.g st.Dc →
      DB.KeyInj st.g.L (kof G s) → WalkInv st.d →
      DL.psi (L.foldl (relaxInsCc (dlOps G s) T B lo) st).Dc ≤ DL.psi st.Dc + 2 * L.length := by
  intro L
  induction L with
  | nil => intro st _ _ _; simp
  | cons e L ih =>
    intro st h hK hw
    rw [List.foldl_cons]
    have h1 := relax_psi (T := T) lo st e h
    obtain ⟨e1, -, hS1, hK1, -⟩ := relax_sim (T := T) lo st e h hK hw
    have hw1 : WalkInv (relaxInsCc (dlOps G s) T B lo st e).d := by
      rw [e1]; exact relaxIns_walk B lo _ e hw
    have h2 := ih _ hS1 hK1 hw1
    rw [List.length_cons]
    omega

theorem insMany_psi {B : WLab G s} {f0 : ℕ} (f : Fin G.n → WLab G s) :
    ∀ (l : List (Fin G.n)) (g : DGl G s) (Dc : DStrM G s), SInv G s (dlOps G s) B f0 g Dc →
      DB.KeyInj g.L (kof G s) → (∀ y ∈ l, f y < B ∧ kof G s (f y) = y) →
      DL.psi (insManyC (dlOps G s) T f l g Dc).2.1 ≤ DL.psi Dc + 2 * l.length := by
  intro l
  induction l with
  | nil => intro g Dc _ _ _; show DL.psi Dc ≤ _; simp
  | cons y l ih =>
    intro g Dc h hK hl
    obtain ⟨hfy, hky⟩ := hl y List.mem_cons_self
    have h1 := ins_psi (T := T) h y (f y)
    obtain ⟨-, hS1, hK1, -⟩ := ins_sim (T := T) h hK hfy hky
    have h2 := ih _ _ hS1 hK1 (fun z hz => hl z (List.mem_cons_of_mem _ hz))
    show DL.psi (insManyC (dlOps G s) T f l (insC (dlOps G s) T g Dc y (f y)).1
      (insC (dlOps G s) T g Dc y (f y)).2.1).2.1 ≤ _
    rw [List.length_cons]
    omega

theorem pull_psi {B : WLab G s} {f0 : ℕ} {g : DGl G s} {Dc : DStrM G s}
    (h : SInv G s (dlOps G s) B f0 g Dc) (hK : DB.KeyInj g.L (kof G s)) :
    DL.psi (pullC (dlOps G s) T g Dc).2.2.2.1 + Dc.M ≤ DL.psi Dc ∨
      DL.psi (pullC (dlOps G s) T g Dc).2.2.2.1 = Dc.M :=
  DL.psi_pullL 1 h.wf hK h.ids h.M1

theorem merge_psi {D D' : DStrM G s} (hM3 : 3 ≤ D.M) :
    DL.psi ((dlOps G s).merge T D D').1 ≤ DL.psi D + D.M + 2 * entCount D' :=
  DL.psi_merge 1 hM3

/-! ### The insertion charge under a `psi` budget -/

/-- The insertion bound for block parameter `M` and `psi` budget `P`. -/
noncomputable def insBound (M P : ℕ) : ℕ :=
  DL.bsCost (P / M + (P / 2) / DL.thr M) + 438 + 210 * DL.ell M (P / 2 + 1) + 2

theorem insCharge_le {Dc : DStrM G s} {P : ℕ} (hP : DL.psi Dc ≤ P) (hM : 1 ≤ Dc.M) :
    insCharge Dc ≤ insBound Dc.M P := by
  have hb := DL.blocks_le_of_psi hP hM
  have he := DL.ents_le_of_psi hP
  unfold insCharge insBound entCount DL.bsCost
  have h1 : Nat.log 2 Dc.blocks.length ≤ Nat.log 2 (P / Dc.M + (P / 2) / DL.thr Dc.M) :=
    Nat.log_mono_right hb
  have h2 : DL.ell Dc.M ((DB.allEnts Dc.blocks).length + 1) ≤ DL.ell Dc.M (P / 2 + 1) :=
    DL.ell_mono (by omega)
  omega

/-- **One relaxation, telescoped**: cost `1` for the test plus at most `insCharge` for an
insertion, given the insertion charge bound `Ibd` for structures within the size budget. -/
theorem relax_tele {B : WLab G s} {f0 : ℕ} (lo : Option (WLab G s)) (st : RSt G s) (e : Fin G.m)
    (h : SInv G s (dlOps G s) B f0 st.g st.Dc) (hK : DB.KeyInj st.g.L (kof G s)) (hw : WalkInv st.d)
    {os : List (DB.Block (Fin G.n) (WLab G s))} (hos : ∀ x ∈ DB.allEnts os, x.id < st.g.fresh)
    (hnd : ((DB.allEnts os).map (·.id)).Nodup) {Ibd : ℕ} (hIbd : insCharge st.Dc ≤ Ibd) :
    (relaxInsCc (dlOps G s) T B lo st e).c + potG (relaxInsCc (dlOps G s) T B lo st e).g
        (relaxInsCc (dlOps G s) T B lo st e).Dc + othP (relaxInsCc (dlOps G s) T B lo st e).g.L os ≤
      st.c + potG st.g st.Dc + othP st.g.L os + (1 + Ibd) := by
  classical
  have hins := ins_tele (T := T) h (G.dst e) (ext (st.d (G.src e)) e) hos hnd
  unfold relaxInsCc
  split_ifs with hv
  · cases lo with
    | none =>
      show st.c + 1 + (insC (dlOps G s) T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).2.2 +
          potG (insC (dlOps G s) T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).1
            (insC (dlOps G s) T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).2.1 +
          othP (insC (dlOps G s) T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).1.L os ≤ _
      omega
    | some b =>
      simp only
      split_ifs
      · show st.c + 1 + (insC (dlOps G s) T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).2.2 +
            potG (insC (dlOps G s) T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).1
              (insC (dlOps G s) T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).2.1 +
            othP (insC (dlOps G s) T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).1.L os ≤ _
        omega
      · show st.c + 1 + potG st.g st.Dc + othP st.g.L os ≤ _
        omega
  · show st.c + 1 + potG st.g st.Dc + othP st.g.L os ≤ _
    omega

/-! ### Telescoped scans under a `psi` budget -/

/-- **A relaxation scan, telescoped**: every insertion happens under the `psi` budget `P`, so it
costs at most `Ibd`. -/
theorem fold_tele {B : WLab G s} {f0 : ℕ} (lo : Option (WLab G s)) {Mlv P Ibd : ℕ}
    (hIns : ∀ D : DStrM G s, D.M = Mlv → DL.psi D ≤ P → insCharge D ≤ Ibd)
    {os : List (DB.Block (Fin G.n) (WLab G s))} (hnd : ((DB.allEnts os).map (·.id)).Nodup) :
    ∀ (L : List (Fin G.m)) (st : RSt G s), SInv G s (dlOps G s) B f0 st.g st.Dc →
      DB.KeyInj st.g.L (kof G s) → WalkInv st.d → st.Dc.M = Mlv →
      DL.psi st.Dc + 2 * L.length ≤ P → (∀ x ∈ DB.allEnts os, x.id < st.g.fresh) →
      (L.foldl (relaxInsCc (dlOps G s) T B lo) st).c +
          potG (L.foldl (relaxInsCc (dlOps G s) T B lo) st).g
            (L.foldl (relaxInsCc (dlOps G s) T B lo) st).Dc +
          othP (L.foldl (relaxInsCc (dlOps G s) T B lo) st).g.L os ≤
        st.c + potG st.g st.Dc + othP st.g.L os + L.length * (1 + Ibd) := by
  intro L
  induction L with
  | nil => intro st _ _ _ _ _ _; simp
  | cons e L ih =>
    intro st h hK hw hM hP hos
    rw [List.foldl_cons]
    have hIb : insCharge st.Dc ≤ Ibd := hIns st.Dc hM (by simp only [List.length_cons] at hP; omega)
    have hstep := relax_tele (T := T) lo st e h hK hw hos hnd hIb
    obtain ⟨e1, -, h1, hK1, hm1, -, -⟩ := relax_sim (T := T) lo st e h hK hw
    have hw1 : WalkInv (relaxInsCc (dlOps G s) T B lo st e).d := by
      rw [e1]; exact relaxIns_walk B lo _ e hw
    have hM1 : (relaxInsCc (dlOps G s) T B lo st e).Dc.M = Mlv := by
      rw [relaxInsCc_M]; exact hM
    have hP1 : DL.psi (relaxInsCc (dlOps G s) T B lo st e).Dc + 2 * L.length ≤ P := by
      have := relax_psi (T := T) lo st e h
      simp only [List.length_cons] at hP
      omega
    have hos1 : ∀ x ∈ DB.allEnts os, x.id < (relaxInsCc (dlOps G s) T B lo st e).g.fresh :=
      fun x hx => lt_of_lt_of_le (hos x hx) hm1
    have hrest := ih (relaxInsCc (dlOps G s) T B lo st e) h1 hK1 hw1 hM1 hP1 hos1
    simp only [List.length_cons]
    nlinarith

/-- **Insertions of a list, telescoped**, under the `psi` budget `P`. -/
theorem insMany_tele {B : WLab G s} {f0 : ℕ} (f : Fin G.n → WLab G s) {Mlv P Ibd : ℕ}
    (hIns : ∀ D : DStrM G s, D.M = Mlv → DL.psi D ≤ P → insCharge D ≤ Ibd)
    {os : List (DB.Block (Fin G.n) (WLab G s))} (hnd : ((DB.allEnts os).map (·.id)).Nodup) :
    ∀ (l : List (Fin G.n)) (g : DGl G s) (Dc : DStrM G s), SInv G s (dlOps G s) B f0 g Dc →
      DB.KeyInj g.L (kof G s) → (∀ y ∈ l, f y < B ∧ kof G s (f y) = y) → Dc.M = Mlv →
      DL.psi Dc + 2 * l.length ≤ P → (∀ x ∈ DB.allEnts os, x.id < g.fresh) →
      (insManyC (dlOps G s) T f l g Dc).2.2 +
          potG (insManyC (dlOps G s) T f l g Dc).1 (insManyC (dlOps G s) T f l g Dc).2.1 +
          othP (insManyC (dlOps G s) T f l g Dc).1.L os ≤
        potG g Dc + othP g.L os + l.length * Ibd := by
  intro l
  induction l with
  | nil => intro g Dc _ _ _ _ _ _; show 0 + potG g Dc + othP g.L os ≤ _; simp
  | cons y l ih =>
    intro g Dc h hK hl hM hP hos
    obtain ⟨hfy, hky⟩ := hl y List.mem_cons_self
    have hIb : insCharge Dc ≤ Ibd := hIns Dc hM (by simp only [List.length_cons] at hP; omega)
    have hstep := ins_tele (T := T) h y (f y) hos hnd
    obtain ⟨-, h1, hK1, hm1, -⟩ := ins_sim (T := T) h hK hfy hky
    have hM1 : (insC (dlOps G s) T g Dc y (f y)).2.1.M = Mlv := by rw [insC_M]; exact hM
    have hP1 : DL.psi (insC (dlOps G s) T g Dc y (f y)).2.1 + 2 * l.length ≤ P := by
      have := ins_psi (T := T) h y (f y)
      simp only [List.length_cons] at hP
      omega
    have hos1 : ∀ x ∈ DB.allEnts os, x.id < (insC (dlOps G s) T g Dc y (f y)).1.fresh :=
      fun x hx => lt_of_lt_of_le (hos x hx) hm1
    have hrest := ih (insC (dlOps G s) T g Dc y (f y)).1 (insC (dlOps G s) T g Dc y (f y)).2.1 h1 hK1
      (fun z hz => hl z (List.mem_cons_of_mem _ hz)) hM1 hP1 hos1
    show (insC (dlOps G s) T g Dc y (f y)).2.2 +
        (insManyC (dlOps G s) T f l (insC (dlOps G s) T g Dc y (f y)).1
          (insC (dlOps G s) T g Dc y (f y)).2.1).2.2 +
        potG (insManyC (dlOps G s) T f l (insC (dlOps G s) T g Dc y (f y)).1
          (insC (dlOps G s) T g Dc y (f y)).2.1).1
          (insManyC (dlOps G s) T f l (insC (dlOps G s) T g Dc y (f y)).1
            (insC (dlOps G s) T g Dc y (f y)).2.1).2.1 +
        othP (insManyC (dlOps G s) T f l (insC (dlOps G s) T g Dc y (f y)).1
          (insC (dlOps G s) T g Dc y (f y)).2.1).1.L os ≤ _
    simp only [List.length_cons]
    nlinarith

end scans

/-! ## The size hypothesis: subtree placement budgets -/

section fits

variable {Ω : Type}

/-- **Every subtree fits its level's budget**: the own-placement sum of the subtree of each record
is at most `Emax` of the record's level. -/
def Fits (Emax : ℕ → ℕ) (lg : Log G s Ω) : Prop :=
  ∀ q r, (q, r) ∈ lg → Log.ownSum (subLog lg q) ≤ Emax r.lvl

theorem subLog_append (l1 l2 : Log G s Ω) (q : List ℕ) :
    subLog (l1 ++ l2) q = subLog l1 q ++ subLog l2 q := by
  unfold subLog; rw [List.filter_append]

theorem subLog_cons (x : List ℕ × CallRec G s Ω) (l : Log G s Ω) (q : List ℕ) :
    Log.ownSum (subLog l q) ≤ Log.ownSum (subLog (x :: l) q) := by
  unfold subLog
  rw [List.filter_cons]
  split_ifs
  · rw [Log.ownSum_cons]; omega
  · exact le_rfl

theorem subLog_shift (i : ℕ) (lg : Log G s Ω) (q : List ℕ) :
    subLog (Log.shift i lg) (i :: q) = Log.shift i (subLog lg q) := by
  unfold subLog Log.shift
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro x _
  simp [List.cons_prefix_cons]

theorem Fits.append_left {Emax : ℕ → ℕ} {l1 l2 : Log G s Ω} (h : Fits Emax (l1 ++ l2)) :
    Fits Emax l1 := by
  intro q r hq
  have := h q r (List.mem_append_left _ hq)
  rw [subLog_append, Log.ownSum_append] at this
  omega

theorem Fits.append_right {Emax : ℕ → ℕ} {l1 l2 : Log G s Ω} (h : Fits Emax (l1 ++ l2)) :
    Fits Emax l2 := by
  intro q r hq
  have := h q r (List.mem_append_right _ hq)
  rw [subLog_append, Log.ownSum_append] at this
  omega

theorem Fits.cons {Emax : ℕ → ℕ} {x : List ℕ × CallRec G s Ω} {l : Log G s Ω}
    (h : Fits Emax (x :: l)) : Fits Emax l := by
  intro q r hq
  exact le_trans (subLog_cons x l q) (h q r (List.mem_cons_of_mem _ hq))

theorem Fits.shift {Emax : ℕ → ℕ} {i : ℕ} {lg : Log G s Ω} (h : Fits Emax (Log.shift i lg)) :
    Fits Emax lg := by
  intro q r hq
  have hm : (i :: q, r) ∈ Log.shift i lg := List.mem_map.mpr ⟨(q, r), hq, rfl⟩
  have := h (i :: q) r hm
  rwa [subLog_shift, Log.ownSum_shift] at this

theorem subLog_nil_eq (lg : Log G s Ω) : subLog lg [] = lg := by
  unfold subLog
  simp

/-- The root record's budget bounds the whole log. -/
theorem Fits.root {Emax : ℕ → ℕ} {r : CallRec G s Ω} {lg : Log G s Ω} (h : Fits Emax (([], r) :: lg)) :
    Log.ownSum (([], r) :: lg) ≤ Emax r.lvl := by
  have := h [] r List.mem_cons_self
  rwa [subLog_nil_eq] at this

end fits



/-! ## Telescoped sub-calls -/

section simsubT

variable {Φ Ω : Type} {T : ℕ}
variable {B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {p : ℕ}
  {P0 : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {B'0 : WLab G s}

variable (G s) in
/-- Concrete sub-calls at level `l` simulate the literal ones, and — when every subtree of their
log fits its level's budget `Emax` — their actual cost telescopes: the actual cost plus the
potential of the returned structure plus the potential `othP` of any family of OTHER structures
(ids below the start's fresh id) is at most the literal cost plus the others' potential at the
start. -/
def SimSubT (τ : ℕ → ℕ) (Inv : Φ → Prop) (Mf Emax : ℕ → ℕ) (l : ℕ) (subD : SubRelD G s Φ Ω)
    (subC : SubRelC G s Φ Ω) : Prop :=
  ∀ Blow B S d φ g res φ' g' lg, CallPre B S d → Inv φ → (∀ x ∈ S, Blow ≤ dis (s := s) x) →
    Blow ≤ B → DB.KeyInj g.L (kof G s) → (∀ v i a, g.L v = some (i, a) → B ≤ a) → S.Nonempty →
    subD Blow B S d φ g res φ' g' lg →
    ∃ lgC, subC Blow B S d φ (res.lit g') φ' lgC ∧ Log.strip lgC = Log.strip lg ∧
      DPost G s (dlOps G s) B d (Mf l) g g' res ∧
      (Fits Emax lg → ∀ os : List (DB.Block (Fin G.n) (WLab G s)),
        (∀ x ∈ DB.allEnts os, x.id < g.fresh) → ((DB.allEnts os).map (·.id)).Nodup →
        lg.cost + potG g' res.2.2.1 + othP g'.L os ≤ lgC.cost + othP g.L os)

end simsubT


end BM
end CHD
end Frontier
