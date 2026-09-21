import Frontier.CHD.KeyLists
import Frontier.CHD.DInsDL
import Frontier.CHD.SpineLoop
import Frontier.CHD.SynFrame

/-!
# DLayerInst — the D layer of the spine: representation predicate and frames (B-L3, agent-04,
NON-GATE)

`DRI P st H g Ds lo`: the active levels `lo..P.top` hold the lazy structures `Ds` (agent-04's
`DGlobal.DLRep`), with the per-level bounds and parameters in D-owned arrays, the per-level
circular live-key lists (`KeyLists`), the Layer-A invariants the operations need, and the
resource counter `ds.fresh + blk.fresh ≤ P.ucap`.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.DLI

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.DB Frontier.CHD.DIns
  Frontier.CHD.DList Frontier.CHD.DGlob Frontier.CHD.MLab Frontier.CHD.LabTab Frontier.CHD.BM
open Frontier.RAM.WExpr Frontier.RAM.Stmt Frontier.CHD.RamBaseCase Frontier.CHD.RamLevel

variable {G : Graph} {s : Fin G.n}

theorem runs_and {ops : VOps ℝ≥0} {c : Stmt} {st : State ℝ≥0} {Q₁ Q₂ : State ℝ≥0 → Prop}
    (h₁ : Runs ops c st Q₁) (h₂ : Runs ops c st Q₂) : Runs ops c st (fun r => Q₁ r ∧ Q₂ r) := by
  obtain ⟨f₁, r₁, e₁, q₁⟩ := h₁
  obtain ⟨f₂, r₂, e₂, q₂⟩ := h₂
  obtain rfl := exec_det ops e₁ e₂
  exact ⟨f₁, r₁, e₁, q₁, q₂⟩

/-- the per-level bound label arrays -/
def bdA : LArr := ⟨"dsl.bl", "dsl.bh", "dsl.bv", "dsl.be", "dsl.br"⟩

/-- the D-owned bound of level `j` (flag `dsl.bf[j] = 0` iff `⊤`), in the shape of `SlotHolds` -/
def BdHolds (st : State ℝ≥0) (j : ℕ) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (b : WLab G s) : Prop :=
  (st.wa "dsl.bf" j = 0 ↔ b = ⊤) ∧ ∀ q : List (Fin G.m), b = ((toW q : WalkOrd G s) : WLab G s) →
    ∃ x : MLabel G, AHolds st bdA j x ∧ Rep (s := s) H V x q

/-- the top level and the capacities of the D layer -/
structure DPar where
  top : ℕ
  ecap : ℕ
  bcap : ℕ
  ucap : ℕ
  /-- the procedure index and body of the selection routine used by the pull -/
  psel : ℕ
  sel : Stmt

/-- word arrays `DLRep` reads -/
def dlWA : List String := dW ++ ["dsl.base"]
/-- word arrays `DRI` reads -/
def drWA : List String :=
  dlWA ++ ["dsl.M", "dsl.bf", "dsl.bh", "dsl.bv", "dsl.be", "dsl.br", "lk.n", "lk.p", "sel.w"]
/-- value arrays `DRI` reads -/
def drVA : List String := dV ++ ["dsl.bl"]
/-- registers `DRI` reads -/
def drWR : List String := ["ds.fresh", "blk.fresh"]

/-- static sizes of the D arrays (all allocated once by the prologue) -/
structure DLens (P : DPar) (st : State ℝ≥0) : Prop where
  bf : P.top < st.wlen "dsl.bf"
  bl : P.top < st.vlen "dsl.bl"
  bh : P.top < st.wlen "dsl.bh"
  bv : P.top < st.wlen "dsl.bv"
  be : P.top < st.wlen "dsl.be"
  br : P.top < st.wlen "dsl.br"
  M : P.top < st.wlen "dsl.M"
  lkn : G.n + P.top < st.wlen "lk.n"
  lkp : G.n + P.top < st.wlen "lk.p"
  sz : P.top < st.wlen "dsl.sz"
  ent : st.wlen "ent.nxt" = P.ecap ∧ st.wlen "ent.key" = P.ecap ∧ st.vlen "ent.len" = P.ecap ∧
    st.wlen "ent.h" = P.ecap ∧ st.wlen "ent.v" = P.ecap ∧ st.wlen "ent.e" = P.ecap ∧
    st.wlen "ent.r" = P.ecap
  stk : P.bcap ≤ st.wlen "dsl.stk"
  live : G.n ≤ st.wlen "live"
  ue : P.ucap + 2 ≤ P.ecap
  ub : P.ucap + 2 ≤ P.bcap
  cap : 4 * P.bcap + 2 * P.ecap + 2 * G.n + 4 * P.top + 300 < st.cap
  rowcap : (P.top + 2) * (G.n + 2) + 2 * P.ecap + 300 < st.cap
  stkl : st.wlen "dsl.stk" = P.bcap
  selw : 6 * P.ecap + 60 ≤ st.wlen "sel.w"
  selc : st.wlen "sel.w" + 1 < st.cap

/-- **the D layer** of the spine -/
structure DRI (P : DPar) (st : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (g : DGl G s)
    (Ds : ℕ → DStrM G s) (lo : ℕ) : Prop where
  lo_le : lo ≤ P.top
  dl : DLRep st H (vc st) P.ecap P.bcap g.L g.fresh Ds lo (P.top - lo)
  bd : ∀ j, lo ≤ j → j ≤ P.top → BdHolds st j H (vc st) (Ds j).Bd
  mv : ∀ j, lo ≤ j → j ≤ P.top → st.wa "dsl.M" j = (Ds j).M
  kl : ∃ K : ℕ → List ℕ, KL.LL (st.wa "lk.n") (st.wa "lk.p") G.n lo P.top K ∧
    ∀ j, lo ≤ j → j ≤ P.top → ∀ v : Fin G.n, (v : ℕ) ∈ K j ↔ DB.HasKey g.L (Ds j) v
  wf : ∀ j, lo ≤ j → j ≤ P.top → DB.WF g.L (Ds j)
  fr : ∀ j, lo ≤ j → j ≤ P.top → DB.FreshOK g.fresh (Ds j)
  lf : ∀ u i a, g.L u = some (i, a) → i < g.fresh
  use : st.w "ds.fresh" + st.w "blk.fresh" ≤ P.ucap
  lens : DLens (G := G) P st
  /-- the (inactive) levels above the top hold small structures -/
  hib : ∀ j, P.top < j → (Ds j).blocks.length ≤ P.ucap
  /-- the pull's selection routine is procedure `psel` -/
  procs : st.procs[P.psel]? = some P.sel
  /-- every pool cell holds a vertex key -/
  keys : ∀ i, i < P.ecap → st.wa "ent.key" i < G.n
  /-- the pull's split threshold fits in a word -/
  mc : ∀ j, lo ≤ j → j ≤ P.top → 2 * (Ds j).M + 2 < st.cap

/-! ## History extensions -/

section ext

variable {st : State ℝ≥0} {H H' : Fin G.n → ℕ → List (Fin G.m)} {V V' : Fin G.n → ℕ}

theorem SepRep.ext {bid : ℕ} {sp : WithBot (WLab G s)} (h : SepRep st H V bid sp)
    (hE : HExt H V H' V') : SepRep st H' V' bid sp := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  rcases h2 with h2 | ⟨m, q, hm, hq, hsp⟩
  · exact Or.inl h2
  · exact Or.inr ⟨m, q, hm, Rep.ext hq hE, hsp⟩

theorem BlkRep.ext {bid : ℕ} {b : Block (Fin G.n) (WLab G s)} (h : BlkRep st H V bid b)
    (hE : HExt H V H' V') : BlkRep st H' V' bid b := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨SepRep.ext h1 hE, h2, fun x hx => (h3 x hx).ext hE, h4, h5⟩

theorem DRep.ext {bcap lv bse : ℕ} {D : DStr (Fin G.n) (WLab G s)} (h : DRep st H V bcap lv bse D)
    (hE : HExt H V H' V') : DRep st H' V' bcap lv bse D :=
  ⟨h.sz, h.szb, h.stkb, fun i hi => BlkRep.ext (h.blk i hi) hE, h.inj, h.bidb⟩

theorem LiveRep.ext {L : Live (Fin G.n) (WLab G s)} (h : LiveRep st H V L) (hE : HExt H V H' V') :
    LiveRep st H' V' L :=
  ⟨h.1, fun v => ⟨(h.2 v).1, fun i a hv => ((h.2 v).2 i a hv).ext hE⟩⟩

theorem RecsOK.ext {recs : List (ℕ × Block (Fin G.n) (WLab G s))} (h : RecsOK st H V recs)
    (hE : HExt H V H' V') : RecsOK st H' V' recs :=
  ⟨h.1, fun p hp => BlkRep.ext (h.2.1 p hp) hE, h.2.2⟩

theorem DLRep.ext {ecap bcap : ℕ} {L : Live (Fin G.n) (WLab G s)} {fresh : ℕ}
    {Ds : ℕ → DStr (Fin G.n) (WLab G s)} {lo k : ℕ} (h : DLRep st H V ecap bcap L fresh Ds lo k)
    (hE : HExt H V H' V') : DLRep st H' V' ecap bcap L fresh Ds lo k :=
  ⟨LiveRep.ext h.live hE, h.pool, h.barr, h.basel, h.base0, h.chain,
    fun j hj => DRep.ext (h.drep j hj) hE, RecsOK.ext h.recs hE, h.bfresh, h.bfcap⟩

theorem BdHolds.ext {j : ℕ} {b : WLab G s} (h : BdHolds st j H V b) (hE : HExt H V H' V') :
    BdHolds st j H' V' b := by
  refine ⟨h.1, fun q hq => ?_⟩
  obtain ⟨x, hx, hxq⟩ := h.2 q hq
  exact ⟨x, hx, Rep.ext hxq hE⟩

end ext

/-! ## Frames -/

section frame

variable {st r : State ℝ≥0} {wa va wr vr : List String}

theorem wa_of (hu : Unchanged st r wa va wr vr) (hw : ∀ a ∈ drWA, a ∉ wa) {a : String}
    (ha : a ∈ drWA) : r.wa a = st.wa a ∧ r.wlen a = st.wlen a :=
  hu.warr a (fun h => hw a ha h)

theorem va_of (hu : Unchanged st r wa va wr vr) (hv : ∀ a ∈ drVA, a ∉ va) {a : String}
    (ha : a ∈ drVA) : r.va a = st.va a ∧ r.vlen a = st.vlen a :=
  hu.varr a (fun h => hv a ha h)

theorem wr_of (hu : Unchanged st r wa va wr vr) (hr : ∀ a ∈ drWR, a ∉ wr) {a : String}
    (ha : a ∈ drWR) : r.w a = st.w a :=
  hu.wreg a (fun h => hr a ha h)

theorem dW_sub : ∀ a ∈ dW, a ∈ dlWA := fun a ha => List.mem_append_left _ ha
theorem dlWA_sub : ∀ a ∈ dlWA, a ∈ drWA := fun a ha => List.mem_append_left _ ha

theorem wa_ofl (hu : Unchanged st r wa va wr vr) (hw : ∀ a ∈ dlWA, a ∉ wa) {a : String}
    (ha : a ∈ dlWA) : r.wa a = st.wa a ∧ r.wlen a = st.wlen a :=
  hu.warr a (fun h => hw a ha h)
theorem dV_sub : ∀ a ∈ dV, a ∈ drVA := fun a ha => List.mem_append_left _ ha

variable {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}

theorem DLRep.of_unch {ecap bcap : ℕ} {L : Live (Fin G.n) (WLab G s)} {fresh : ℕ}
    {Ds : ℕ → DStr (Fin G.n) (WLab G s)} {lo k : ℕ} (h : DLRep st H V ecap bcap L fresh Ds lo k)
    (hu : Unchanged st r wa va wr vr) (hw : ∀ a ∈ dlWA, a ∉ wa) (hv : ∀ a ∈ dV, a ∉ va)
    (hr : ∀ a ∈ drWR, a ∉ wr) : DLRep r H V ecap bcap L fresh Ds lo k := by
  have hw' : ∀ a ∈ wa, a ∉ dW := fun a ha hd => hw a (dW_sub a hd) ha
  have hv' : ∀ a ∈ va, a ∉ dV := fun a ha hd => hv a hd ha
  have ebase := wa_ofl hu hw (a := "dsl.base") (by simp [dlWA])
  have hb : ∀ l, base r l = base st l := fun l => by unfold base; rw [ebase.1]
  have estk := wa_ofl hu hw (a := "dsl.stk") (by simp [dlWA, dW])
  have hrf : recsFrom r Ds lo (k + 1) = recsFrom st Ds lo (k + 1) :=
    recsFrom_of_wa Ds ebase.1 estk.1 (k + 1) lo
  have hbf := wr_of hu hr (a := "blk.fresh") (by simp [drWR])
  have hdf := wr_of hu hr (a := "ds.fresh") (by simp [drWR])
  obtain ⟨hl1, hl2⟩ := h.live
  refine ⟨⟨by rw [(wa_ofl hu hw (a := "live") (by simp [dlWA, dW])).2]; exact hl1, fun v =>
      ⟨by rw [(wa_ofl hu hw (a := "live") (by simp [dlWA, dW])).1]; exact (hl2 v).1,
        fun i a hva => ((hl2 v).2 i a hva).of_unchanged hu hw' hv'⟩⟩, ?_,
    h.barr.of_unchanged hu hw' hv', by rw [ebase.2]; exact h.basel, by rw [hb]; exact h.base0,
    fun j hj => by rw [hb, hb]; exact h.chain j hj, fun j hj => by rw [hb]; exact (h.drep j hj).of_unchanged hu hw' hv',
    ?_, fun p hp => ?_, by rw [hbf]; exact h.bfcap⟩
  · obtain ⟨h1, h2, a1, a2, a3, a4, a5, a6, a7⟩ := h.pool
    refine ⟨by rw [hdf]; exact h1, h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [(wa_ofl hu hw (a := "ent.key") (by simp [dlWA, dW])).2]; exact a1
    · rw [(wa_ofl hu hw (a := "ent.nxt") (by simp [dlWA, dW])).2]; exact a2
    · rw [(hu.varr entA.l (fun h' => hv _ (by simp [dV, entA]) h')).2]; exact a3
    · rw [(wa_ofl hu hw (a := entA.h) (by simp [dlWA, dW, entA])).2]; exact a4
    · rw [(wa_ofl hu hw (a := entA.v) (by simp [dlWA, dW, entA])).2]; exact a5
    · rw [(wa_ofl hu hw (a := entA.e) (by simp [dlWA, dW, entA])).2]; exact a6
    · rw [(wa_ofl hu hw (a := entA.r) (by simp [dlWA, dW, entA])).2]; exact a7
  · rw [hrf]
    exact ⟨h.recs.1, fun p hp => (h.recs.2.1 p hp).of_unchanged hu hw' hv', h.recs.2.2⟩
  · rw [hrf] at hp; rw [hbf]; exact h.bfresh p hp

theorem BdHolds.of_unch {j : ℕ} {b : WLab G s} (h : BdHolds st j H V b)
    (hu : Unchanged st r wa va wr vr) (hw : ∀ a ∈ drWA, a ∉ wa) (hv : ∀ a ∈ drVA, a ∉ va) :
    BdHolds r j H V b := by
  refine ⟨by rw [(wa_of hu hw (a := "dsl.bf") (by simp [drWA])).1]; exact h.1, fun q hq => ?_⟩
  obtain ⟨x, ⟨x1, x2, x3, x4, x5⟩, hxq⟩ := h.2 q hq
  refine ⟨x, ⟨?_, ?_, ?_, ?_, ?_⟩, hxq⟩
  · rw [(va_of hu hv (a := bdA.l) (by simp [drVA, bdA])).1]; exact x1
  · rw [(wa_of hu hw (a := bdA.h) (by simp [drWA, bdA])).1]; exact x2
  · rw [(wa_of hu hw (a := bdA.v) (by simp [drWA, bdA])).1]; exact x3
  · rw [(wa_of hu hw (a := bdA.e) (by simp [drWA, bdA])).1]; exact x4
  · rw [(wa_of hu hw (a := bdA.r) (by simp [drWA, bdA])).1]; exact x5

theorem DLens.of_unch {P : DPar} (h : DLens (G := G) P st) (hu : Unchanged st r wa va wr vr)
    (hw : ∀ a ∈ drWA, a ∉ wa) (hv : ∀ a ∈ drVA, a ∉ va) : DLens (G := G) P r := by
  have L : ∀ a ∈ drWA, r.wlen a = st.wlen a := fun a ha => (wa_of hu hw ha).2
  have LV : ∀ a ∈ drVA, r.vlen a = st.vlen a := fun a ha => (va_of hu hv ha).2
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := h.ent
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, h.ue, h.ub, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [L _ (by simp [drWA])]; exact h.bf
  · rw [LV _ (by simp [drVA])]; exact h.bl
  · rw [L _ (by simp [drWA])]; exact h.bh
  · rw [L _ (by simp [drWA])]; exact h.bv
  · rw [L _ (by simp [drWA])]; exact h.be
  · rw [L _ (by simp [drWA])]; exact h.br
  · rw [L _ (by simp [drWA])]; exact h.M
  · rw [L _ (by simp [drWA])]; exact h.lkn
  · rw [L _ (by simp [drWA])]; exact h.lkp
  · rw [L _ (by simp [drWA, dlWA, dW])]; exact h.sz
  · rw [L _ (by simp [drWA, dlWA, dW])]; exact e1
  · rw [L _ (by simp [drWA, dlWA, dW])]; exact e2
  · rw [LV _ (by simp [drVA, dV])]; exact e3
  · rw [L _ (by simp [drWA, dlWA, dW])]; exact e4
  · rw [L _ (by simp [drWA, dlWA, dW])]; exact e5
  · rw [L _ (by simp [drWA, dlWA, dW])]; exact e6
  · rw [L _ (by simp [drWA, dlWA, dW])]; exact e7
  · rw [L _ (by simp [drWA, dlWA, dW])]; exact h.stk
  · rw [L _ (by simp [drWA, dlWA, dW])]; exact h.live
  · rw [hu.cap]; exact h.cap
  · rw [hu.cap]; exact h.rowcap
  · rw [L _ (by simp [drWA, dlWA, dW])]; exact h.stkl
  · rw [L _ (by simp [drWA])]; exact h.selw
  · rw [L _ (by simp [drWA]), hu.cap]; exact h.selc

/-- **frame of the D layer** (DLayer.frame) -/
theorem DRI.frame {P : DPar} {H' : Fin G.n → ℕ → List (Fin G.m)} {g : DGl G s}
    {Ds : ℕ → DStrM G s} {lo : ℕ} (h : DRI P st H g Ds lo) (hu : Unchanged st r wa va wr vr)
    (hw : ∀ a ∈ drWA, a ∉ wa) (hv : ∀ a ∈ drVA, a ∉ va) (hr : ∀ a ∈ drWR, a ∉ wr)
    (hE : HExt H (vc st) H' (vc r)) : DRI P r H' g Ds lo := by
  obtain ⟨K, hK, hKk⟩ := h.kl
  have en := wa_of hu hw (a := "lk.n") (by simp [drWA])
  have ep := wa_of hu hw (a := "lk.p") (by simp [drWA])
  refine ⟨h.lo_le, DLRep.ext (DLRep.of_unch h.dl hu (fun a ha => hw a (dlWA_sub a ha)) (fun a ha => hv a (dV_sub a ha)) hr) hE, fun j h1 h2 =>
    BdHolds.ext ((h.bd j h1 h2).of_unch hu hw hv) hE, fun j h1 h2 => ?_, ⟨K, by rw [en.1, ep.1]; exact hK, hKk⟩,
    h.wf, h.fr, h.lf, ?_, h.lens.of_unch hu hw hv, h.hib, by rw [hu.procs]; exact h.procs,
    fun i hi => by rw [(wa_of hu hw (a := "ent.key") (by simp [drWA, dlWA, dW])).1]; exact h.keys i hi,
    fun j h1 h2 => by rw [hu.cap]; exact h.mc j h1 h2⟩
  · rw [(wa_of hu hw (a := "dsl.M") (by simp [drWA])).1]; exact h.mv j h1 h2
  · rw [wr_of hu hr (a := "ds.fresh") (by simp [drWR]), wr_of hu hr (a := "blk.fresh") (by simp [drWR])]
    exact h.use

end frame

/-! ## Only the levels `≥ lo` matter -/

theorem DRI.congr {P : DPar} {st : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {g : DGl G s}
    {Ds Ds' : ℕ → DStrM G s} {lo : ℕ} (hD : ∀ j, lo ≤ j → Ds' j = Ds j) (h : DRI P st H g Ds lo) :
    DRI P st H g Ds' lo := by
  have hrf : ∀ n l, lo ≤ l → recsFrom st Ds' l n = recsFrom st Ds l n := by
    intro n l hl
    exact recsFrom_congr st st Ds Ds' n l (fun l' h1 _ => ⟨hD l' (by omega), rfl, fun _ _ _ => rfl⟩)
  obtain ⟨K, hK, hKk⟩ := h.kl
  have dl := h.dl
  refine ⟨h.lo_le, ⟨dl.live, dl.pool, dl.barr, dl.basel, dl.base0, fun j hj => ?_, fun j hj => ?_,
      by rw [hrf _ _ le_rfl]; exact dl.recs, fun p hp => dl.bfresh p (by rw [← hrf _ _ le_rfl]; exact hp),
      dl.bfcap⟩, fun j h1 h2 => ?_, fun j h1 h2 => ?_, ⟨K, hK, fun j h1 h2 v => ?_⟩,
    fun j h1 h2 => ?_, fun j h1 h2 => ?_, h.lf, h.use, h.lens, fun j hj => ?_, h.procs, h.keys,
    fun j h1 h2 => by rw [hD j h1]; exact h.mc j h1 h2⟩
  · rw [hD _ (by omega)]; exact dl.chain j hj
  · rw [hD _ (by omega)]; exact dl.drep j hj
  · rw [hD j h1]; exact h.bd j h1 h2
  · rw [hD j h1]; exact h.mv j h1 h2
  · rw [hD j h1]; exact hKk j h1 h2 v
  · rw [hD j h1]; exact h.wf j h1 h2
  · rw [hD j h1]; exact h.fr j h1 h2
  · rw [hD j (by have := h.lo_le; omega)]; exact h.hib j hj

/-! ## The syntactic frame of an allocation-free statement -/

theorem exec_sframe {V : Type} (ops : VOps V) :
    ∀ (f : ℕ) (c : Stmt) (st r : State V), NoAlloc c → exec ops f c st = some r →
      Unchanged st r (sWA c) (sVA c) (sWR c) (sVR c) := by
  intro f
  induction f with
  | zero => intro c st r _ h; simp [exec] at h
  | succ f ih =>
    intro c st r hc h
    cases c with
    | skip => simp [exec] at h; subst h; exact (unch_charge 1).mpr (Unchanged.refl _ _ _ _ _)
    | wset x e =>
      cases he : evalW st e with
      | none => simp [exec, he] at h
      | some a =>
        simp [exec, he] at h; subst h
        rw [unch_charge, unch_setW (by simp [sWR])]; exact Unchanged.refl _ _ _ _ _
    | vset x e =>
      cases he : evalV ops st e with
      | none => simp [exec, he] at h
      | some a =>
        simp [exec, he] at h; subst h
        rw [unch_charge, unch_setV (by simp [sVR])]; exact Unchanged.refl _ _ _ _ _
    | vle x a b =>
      cases h1 : evalV ops st a with
      | none => simp [exec, h1] at h
      | some p =>
        cases h2 : evalV ops st b with
        | none => simp [exec, h1, h2] at h
        | some q =>
          cases h3 : fit st.cap (if ops.le p q then 1 else 0) with
          | none => simp [exec, h1, h2, h3] at h
          | some bit =>
            simp [exec, h1, h2, h3] at h; subst h
            rw [unch_charge, unch_setW (by simp [sWR])]; exact Unchanged.refl _ _ _ _ _
    | wstore arr i e =>
      cases h1 : evalW st i with
      | none => simp [exec, h1] at h
      | some j =>
        cases h2 : evalW st e with
        | none => simp [exec, h1, h2] at h
        | some a =>
          by_cases hj : j < st.wlen arr
          · simp [exec, h1, h2, hj] at h; subst h
            rw [unch_charge, unch_storeW (by simp [sWA])]; exact Unchanged.refl _ _ _ _ _
          · simp [exec, h1, h2, hj] at h
    | vstore arr i e =>
      cases h1 : evalW st i with
      | none => simp [exec, h1] at h
      | some j =>
        cases h2 : evalV ops st e with
        | none => simp [exec, h1, h2] at h
        | some a =>
          by_cases hj : j < st.vlen arr
          · simp [exec, h1, h2, hj] at h; subst h
            rw [unch_charge, unch_storeV (by simp [sVA])]; exact Unchanged.refl _ _ _ _ _
          · simp [exec, h1, h2, hj] at h
    | walloc arr e => exact absurd hc (by simp [NoAlloc])
    | valloc arr e => exact absurd hc (by simp [NoAlloc])
    | call p => exact absurd hc (by simp [NoAlloc])
    | seq a b =>
      rw [exec_seq, Option.bind_eq_some_iff] at h
      obtain ⟨s', h1, h2⟩ := h
      exact (ih a st s' hc.1 h1).comp (ih b s' r hc.2 h2)
    | ite c a b =>
      rw [exec_ite, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, h2⟩ := h
      split_ifs at h2
      · exact ((unch_charge 1).mpr (Unchanged.refl st [] [] [] [])).comp (ih a _ r hc.1 h2) |>.mono
          (by simp [sWA]) (by simp [sVA]) (by simp [sWR]) (by simp [sVR])
      · exact ((unch_charge 1).mpr (Unchanged.refl st [] [] [] [])).comp (ih b _ r hc.2 h2) |>.mono
          (by simp [sWA]) (by simp [sVA]) (by simp [sWR]) (by simp [sVR])
    | «while» c b =>
      rw [exec_while, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, h2⟩ := h
      split_ifs at h2
      · rw [Option.bind_eq_some_iff] at h2
        obtain ⟨s', h3, h4⟩ := h2
        have e1 := ((unch_charge 1).mpr (Unchanged.refl st [] [] [] [])).comp (ih b _ s' hc h3)
        have e2 := ih _ s' r hc h4
        exact (e1.mono (by simp [sWA]) (by simp [sVA]) (by simp [sWR]) (by simp [sVR])).trans e2
      · simp at h2; subst h2; exact (unch_charge 1).mpr (Unchanged.refl _ _ _ _ _)

/-- `Runs` of an allocation-free statement changes nothing outside its text footprint -/
theorem Runs.sframe {ops : VOps ℝ≥0} {c : Stmt} {st : State ℝ≥0} {Q : State ℝ≥0 → Prop}
    (h : Runs ops c st Q) (hc : NoAlloc c) :
    Runs ops c st (fun r => Q r ∧ Unchanged st r (sWA c) (sVA c) (sWR c) (sVR c) ∧
      r.wlen = st.wlen ∧ r.vlen = st.vlen) := by
  obtain ⟨f, r, h1, h2⟩ := h
  have hl := exec_noalloc_len ops f c st r hc h1
  simp only [Lens, Prod.mk.injEq] at hl
  exact ⟨f, r, h1, h2, exec_sframe ops f c st r hc h1, hl.1, hl.2⟩

/-! ## Frames with an unchanged label table -/

theorem vc_of {st r : State ℝ≥0} {wa va wr vr : List String} (hu : Unchanged st r wa va wr vr)
    (h : "vcnt" ∉ wa) : vc (G := G) r = vc st := by
  funext v; unfold vc; rw [(hu.warr _ h).1]

theorem DRI.frame_same {P : DPar} {st r : State ℝ≥0} {wa va wr vr : List String}
    {H : Fin G.n → ℕ → List (Fin G.m)} {g : DGl G s} {Ds : ℕ → DStrM G s} {lo : ℕ}
    (h : DRI P st H g Ds lo) (hu : Unchanged st r wa va wr vr)
    (hw : ∀ a ∈ drWA, a ∉ wa) (hv : ∀ a ∈ drVA, a ∉ va) (hr : ∀ a ∈ drWR, a ∉ wr)
    (hvc : "vcnt" ∉ wa) : DRI P r H g Ds lo :=
  h.frame hu hw hv hr (by rw [vc_of hu hvc]; exact HExt.refl _ _)

/-! ## BM.9: the emptiness test -/

/-- `sp.em := [the live-key list of level lvl is empty]` -/
def dsEmpty : Stmt := seq (wset "kl.s" (add (var "n") (var "lvl"))) KL.klTest

theorem isEmpty_iff (g : DGl G s) (D : DStrM G s) :
    (g.view D).IsEmpty ↔ ∀ y, ¬ DB.HasKey g.L D y := by
  unfold DS.IsEmpty DGl.view
  exact forall_congr' (fun y => view_eq_none)

theorem dsEmpty_spec {ops : VOps ℝ≥0} (P : DPar) (st : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m))
    (g : DGl G s) (Ds : ℕ → DStrM G s) (l : ℕ) (hD : DRI P st H g Ds l) (hl : st.w "lvl" = l)
    (hn : st.w "n" = G.n) :
    Runs ops dsEmpty st (fun r => DRI P r H g Ds l ∧
      (r.w "sp.em" = 0 ↔ ¬ (g.view (Ds l)).IsEmpty) ∧
      Unchanged st r [] [] ["kl.s", "sp.em"] [] ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost + 2) := by
  have hc := hD.lens.cap
  have hlt := hD.lo_le
  obtain ⟨K, hK, hKk⟩ := hD.kl
  refine runs_seq (runs_wset (a := G.n + l) (by simp [hl, hn, fit]; omega) ?_)
  set q := (st.setW "kl.s" (G.n + l)).charge 1 with hq
  have hK1 : KL.LL (q.wa "lk.n") (q.wa "lk.p") G.n l P.top K := by simpa [hq] using hK
  refine (KL.klTest_LL (ops := ops) q hK1 (by simp [hq]) le_rfl hlt
    (by simpa [hq] using hD.lens.lkn) (by simp [hq]; omega)).mono ?_
  rintro r ⟨he, hU, hwl, hcost⟩
  have hUq : Unchanged st q [] [] ["kl.s"] [] := by
    rw [hq, unch_charge, unch_setW (List.mem_singleton_self _)]; exact Unchanged.refl _ _ _ _ _
  have hU' : Unchanged st r [] [] ["kl.s", "sp.em"] [] :=
    (hUq.comp hU).mono (by simp) (by simp) (by simp) (by simp)
  refine ⟨hD.frame_same hU' (by simp) (by simp) (by simp [drWR]) (by simp), ?_, hU', ?_, ?_, ?_, ?_⟩
  · rw [he]
    rw [isEmpty_iff]
    by_cases hKl : K l = []
    · simp only [hKl, if_true, one_ne_zero, false_iff, not_not]
      intro y hy
      have := (hKk l le_rfl hlt y).mpr hy
      rw [hKl] at this; simp at this
    · simp only [hKl, if_false, true_iff, not_forall, not_not]
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hKl
      have hxn := hK.lt l le_rfl hlt x hx
      exact ⟨⟨x, hxn⟩, (hKk l le_rfl hlt ⟨x, hxn⟩).mp hx⟩
  · rw [hwl]; simp [hq]
  · funext a; exact (hU'.varr a (by simp)).2
  · have : q.cost = st.cost + 1 := by simp [hq]
    omega
  · have : q.cost = st.cost + 1 := by simp [hq]
    omega

/-! ## Stack size and the new-structure fragment -/

theorem recsOf_length (st : State ℝ≥0) (bse : ℕ) (P : List (Block (Fin G.n) (WLab G s))) :
    (recsOf st bse P).length = P.length := by simp [recsOf]

theorem recsFrom_length {st : State ℝ≥0} {Ds : ℕ → DStrM G s} :
    ∀ (k lo : ℕ), base st (lo + k) = 0 →
      (∀ j < k, base st (lo + j) = base st (lo + j + 1) + (Ds (lo + j + 1)).blocks.length) →
      (recsFrom st Ds lo (k + 1)).length = base st lo + (Ds lo).blocks.length
  | 0, lo, hb0, _ => by simp [recsFrom, recsOf_length]; simpa using hb0
  | k + 1, lo, hb0, hch => by
      have ih := recsFrom_length k (lo + 1) (by rw [show lo + 1 + k = lo + (k + 1) by omega]; exact hb0)
        (fun j hj => by
          have := hch (j + 1) (by omega)
          rw [show lo + (j + 1) = lo + 1 + j by omega] at this
          exact this)
      have h0 := hch 0 (by omega)
      simp only [add_zero] at h0
      have e : recsFrom st Ds lo (k + 1 + 1) =
          recsOf st (base st lo) (Ds lo).blocks ++ recsFrom st Ds (lo + 1) (k + 1) := rfl
      rw [e, List.length_append, recsOf_length, ih]
      omega

/-- the active blocks fit below the block counter -/
theorem DLRep.stack_le {st : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {ecap bcap : ℕ} {L : Live (Fin G.n) (WLab G s)} {fresh : ℕ} {Ds : ℕ → DStrM G s} {lo k : ℕ}
    (h : DLRep st H V ecap bcap L fresh Ds lo k) :
    base st lo + (Ds lo).blocks.length ≤ st.w "blk.fresh" := by
  rw [← recsFrom_length k lo h.base0 h.chain]
  have hnd := h.recs.1
  have hlt : ∀ x ∈ (recsFrom st Ds lo (k + 1)).map Prod.fst, x < st.w "blk.fresh" := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact h.bfresh p hp
  calc (recsFrom st Ds lo (k + 1)).length = ((recsFrom st Ds lo (k + 1)).map Prod.fst).length := by
        simp
    _ = ((recsFrom st Ds lo (k + 1)).map Prod.fst).toFinset.card :=
        (List.toFinset_card_of_nodup hnd).symm
    _ ≤ (Finset.range (st.w "blk.fresh")).card :=
        Finset.card_le_card (fun x hx => by
          simp only [List.mem_toFinset] at hx
          simp only [Finset.mem_range]; exact hlt x hx)
    _ = st.w "blk.fresh" := Finset.card_range _

/-- `newChildS` increments the block counter -/
theorem newChildS_fresh {ops : VOps ℝ≥0} (st0 : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m))
    (V : Fin G.n → ℕ) (ecap bcap : ℕ) (L : Live (Fin G.n) (WLab G s)) (fresh : ℕ)
    (Ds : ℕ → DStr (Fin G.n) (WLab G s)) (lo k : ℕ) (hlo : 1 ≤ lo)
    (hDL : DLRep st0 H V ecap bcap L fresh Ds lo k)
    (hpl : st0.w "nw.pl" = lo) (hlv : st0.w "nw.lv" = lo - 1)
    (hstk : base st0 lo + (Ds lo).blocks.length < st0.wlen "dsl.stk")
    (hbf : st0.w "blk.fresh" < bcap) (hszl : lo - 1 < st0.wlen "dsl.sz")
    (hcap : base st0 lo + (Ds lo).blocks.length + bcap + 2 < st0.cap) :
    Runs ops newChildS st0 (fun r => r.w "blk.fresh" = st0.w "blk.fresh" + 1) := by
  set b := base st0 lo + (Ds lo).blocks.length with hb
  set nb := st0.w "blk.fresh" with hnb
  have hbl := hDL.basel
  have hszlo : lo < st0.wlen "dsl.sz" := (hDL.drep 0 (by omega)).szb
  have hbase_lo : st0.wa "dsl.base" lo = base st0 lo := rfl
  have hsz_lo : st0.wa "dsl.sz" lo = (Ds lo).blocks.length := by
    have := (hDL.drep 0 (by omega)).sz; simpa using this
  have hc0 : 0 < st0.cap := by omega
  have hc1 : 1 < st0.cap := by omega
  obtain ⟨ba1, ba2, ba3, ba4, -, -, -, -, -⟩ := hDL.barr
  apply wp_sound
  simp [newChildS, wp, hpl, hlv, fit, hc0, hc1, show lo < st0.wlen "dsl.base" by omega, hbase_lo,
    hszlo, hsz_lo, show b < st0.cap by omega, show lo - 1 < st0.wlen "dsl.base" by omega,
    show nb + 1 < st0.cap by omega, show nb < st0.wlen "blk.hd" by omega,
    show nb < st0.wlen "blk.tl" by omega, show nb < st0.wlen "blk.cnt" by omega,
    show nb < st0.wlen "blk.bot" by omega, hstk, hszl, hb.symm, hnb.symm]

/-- copy slot `B[lvl]` (index `4·lvl`) into the D-owned bound of level `lvl`, and `cp.M[lvl]`
into `dsl.M[lvl]` -/
def copyBdM : Stmt :=
  seq (wstore "dsl.M" (var "lvl") (load "cp.M" (var "lvl")))
  (seq (vstore "dsl.bl" (var "lvl") (.load "sl.l" (mul (lit 4) (var "lvl"))))
  (seq (wstore "dsl.bh" (var "lvl") (load "sl.h" (mul (lit 4) (var "lvl"))))
  (seq (wstore "dsl.bv" (var "lvl") (load "sl.v" (mul (lit 4) (var "lvl"))))
  (seq (wstore "dsl.be" (var "lvl") (load "sl.e" (mul (lit 4) (var "lvl"))))
  (seq (wstore "dsl.br" (var "lvl") (load "sl.r" (mul (lit 4) (var "lvl"))))
       (wstore "dsl.bf" (var "lvl") (load "sl.f" (mul (lit 4) (var "lvl")))))))))

theorem copyBdM_spec {ops : VOps ℝ≥0} (q : State ℝ≥0) (l : ℕ) (hl : q.w "lvl" = l)
    (h1 : l < q.wlen "dsl.M") (h2 : l < q.wlen "cp.M") (h3 : l < q.vlen "dsl.bl")
    (h4 : l < q.wlen "dsl.bh") (h5 : l < q.wlen "dsl.bv") (h6 : l < q.wlen "dsl.be")
    (h7 : l < q.wlen "dsl.br") (h8 : l < q.wlen "dsl.bf") (hSL : SlotLens q (4 * l))
    (hc' : 4 * l + 4 < q.cap) :
    Runs ops copyBdM q (fun r =>
      r.wa "dsl.M" = Function.update (q.wa "dsl.M") l (q.wa "cp.M" l) ∧
      r.va "dsl.bl" = Function.update (q.va "dsl.bl") l (q.va "sl.l" (4 * l)) ∧
      r.wa "dsl.bh" = Function.update (q.wa "dsl.bh") l (q.wa "sl.h" (4 * l)) ∧
      r.wa "dsl.bv" = Function.update (q.wa "dsl.bv") l (q.wa "sl.v" (4 * l)) ∧
      r.wa "dsl.be" = Function.update (q.wa "dsl.be") l (q.wa "sl.e" (4 * l)) ∧
      r.wa "dsl.br" = Function.update (q.wa "dsl.br") l (q.wa "sl.r" (4 * l)) ∧
      r.wa "dsl.bf" = Function.update (q.wa "dsl.bf") l (q.wa "sl.f" (4 * l)) ∧
      r.cost = q.cost + 7) := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := hSL
  have hc4 : 4 < q.cap := by omega
  have hc : 4 * l < q.cap := by omega
  apply wp_sound
  simp [copyBdM, wp, evalW, evalV, hl, fit, hc, hc4, h1, h2, h3, h4, h5, h6, h7, h8, s1, s2, s3, s4,
    s5, s6, State.storeW, State.storeV, State.charge]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (funext j; simp [Function.update_apply])

theorem DLens.of_len {P : DPar} {st r : State ℝ≥0} (h : DLens (G := G) P st)
    (hl : r.wlen = st.wlen) (hvl : r.vlen = st.vlen) (hc : r.cap = st.cap) : DLens (G := G) P r := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20⟩ := h
  exact ⟨by rw [hl]; exact a1, by rw [hvl]; exact a2, by rw [hl]; exact a3, by rw [hl]; exact a4,
    by rw [hl]; exact a5, by rw [hl]; exact a6, by rw [hl]; exact a7, by rw [hl]; exact a8,
    by rw [hl]; exact a9, by rw [hl]; exact a10, by rw [hl, hvl]; exact a11, by rw [hl]; exact a12,
    by rw [hl]; exact a13, a14, a15, by rw [hc]; exact a16, by rw [hc]; exact a17,
    by rw [hl]; exact a18, by rw [hl]; exact a19, by rw [hl, hc]; exact a20⟩

theorem BdHolds.of_eq {st r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {j : ℕ} {b : WLab G s} (h : BdHolds st j H V b) (hf : r.wa "dsl.bf" j = st.wa "dsl.bf" j)
    (hl : r.va "dsl.bl" j = st.va "dsl.bl" j) (hh : r.wa "dsl.bh" j = st.wa "dsl.bh" j)
    (hv : r.wa "dsl.bv" j = st.wa "dsl.bv" j) (he : r.wa "dsl.be" j = st.wa "dsl.be" j)
    (hr : r.wa "dsl.br" j = st.wa "dsl.br" j) : BdHolds r j H V b := by
  refine ⟨by rw [hf]; exact h.1, fun q hq => ?_⟩
  obtain ⟨x, ⟨x1, x2, x3, x4, x5⟩, hxq⟩ := h.2 q hq
  exact ⟨x, ⟨hl.trans x1, hh.trans x2, hv.trans x3, he.trans x4, hr.trans x5⟩, hxq⟩

theorem hasKey_newC (L : LiveM G s) (M : ℕ) (Bd : WLab G s) (v : Fin G.n) :
    ¬ DB.HasKey L (newC M Bd) v := by
  rintro ⟨e, he, -⟩
  simp [newC, liveVals, liveOf] at he

theorem wf_newC (L : LiveM G s) (M : ℕ) (Bd : WLab G s) : DB.WF L (newC M Bd) := by
  refine ⟨by simp [newC], ?_⟩
  show IntervalOK L [⟨⊥, []⟩] ⊥ (Bd : WithBot (WLab G s))
  exact ⟨rfl, WithBot.bot_lt_coe _, fun e he => absurd he (List.not_mem_nil)⟩

theorem freshOK_newC (f M : ℕ) (Bd : WLab G s) : DB.FreshOK f (newC M Bd) := by
  intro x hx; simp [newC, allEnts] at hx

/-- BM.5: a new structure `newC M Bd` at level `lvl`, on top of level `lvl + 1` -/
def dsNew : Stmt :=
  seq (wset "nw.pl" (add (var "lvl") (lit 1)))
  (seq (wset "nw.lv" (var "lvl"))
  (seq newChildS
  (seq copyBdM
  (seq (wset "kl.s" (add (var "n") (var "lvl"))) KL.klInit))))

theorem dsNew_noalloc : NoAlloc dsNew := by
  simp [NoAlloc, dsNew, newChildS, copyBdM, KL.klInit]

theorem dsNew_main {ops : VOps ℝ≥0} (P : DPar) (st : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m))
    (g : DGl G s) (Ds : ℕ → DStrM G s) (l M : ℕ) (Bd : WLab G s)
    (hD : DRI P st H g Ds (l + 1)) (hl : st.w "lvl" = l) (hn : st.w "n" = G.n)
    (hM : st.wa "cp.M" l = M) (hML : l < st.wlen "cp.M") (hSB : SlotHolds st (slotB l) H (vc st) Bd)
    (hSL : SlotLens st (slotB l)) (hroom : st.w "ds.fresh" + st.w "blk.fresh" + 1 ≤ P.ucap)
    (hMc : 2 * M + 2 < st.cap) :
    Runs ops dsNew st (fun r => DRI P r H g (Function.update Ds l (newC M Bd)) l ∧
      r.cost = st.cost + 22 ∧
      r.w "ds.fresh" + r.w "blk.fresh" = st.w "ds.fresh" + st.w "blk.fresh" + 1) := by
  have hc := hD.lens.cap
  have htop := hD.lo_le
  have hLn := hD.lens
  obtain ⟨K, hK, hKk⟩ := hD.kl
  have h1c : 1 < st.cap := by omega
  have hlc : l + 1 < st.cap := by omega
  refine runs_seq (runs_wset (a := l + 1) (by simp [hl, fit, h1c, hlc]) ?_)
  set q1 := (st.setW "nw.pl" (l + 1)).charge 1 with hq1
  refine runs_seq (runs_wset (a := l) (by simp [hq1, hl]) ?_)
  set q2 := (q1.setW "nw.lv" l).charge 1 with hq2
  have hU2 : Unchanged st q2 [] [] ["nw.pl", "nw.lv"] [] := by
    rw [hq2, unch_charge, unch_setW (by simp), hq1, unch_charge, unch_setW (by simp)]
    exact Unchanged.refl _ _ _ _ _
  have hdl2 : DLRep q2 H (vc st) P.ecap P.bcap g.L g.fresh Ds (l + 1) (P.top - (l + 1)) :=
    DLRep.of_unch hD.dl hU2 (by simp) (by simp) (by simp [drWR])
  have hq2w : ∀ x, x ≠ "nw.pl" → x ≠ "nw.lv" → q2.w x = st.w x := by
    intro x h1 h2; simp [hq2, hq1, h1, h2]
  have hq2wl : q2.wlen = st.wlen := by simp [hq2, hq1]
  have hq2c : q2.cap = st.cap := by simp [hq2, hq1]
  have hsl := DLRep.stack_le hdl2
  have hbf2 : q2.w "blk.fresh" = st.w "blk.fresh" := hq2w _ (by simp) (by simp)
  have hstk : base q2 (l + 1) + (Ds (l + 1)).blocks.length < q2.wlen "dsl.stk" := by
    rw [hq2wl]; have := hLn.stk; have := hLn.ub; omega
  have hbfc : q2.w "blk.fresh" < P.bcap := by have := hLn.ub; omega
  have hszl : l + 1 - 1 < q2.wlen "dsl.sz" := by rw [hq2wl]; have := hLn.sz; omega
  have hcap2 : base q2 (l + 1) + (Ds (l + 1)).blocks.length + P.bcap + 2 < q2.cap := by
    rw [hq2c]; have := hLn.ub; omega
  have hN := newDL (ops := ops) q2 H (vc st) P.ecap P.bcap g.L g.fresh Ds (l + 1) (P.top - (l + 1))
    M Bd (by omega) hdl2 (by simp [hq2, hq1]) (by simp [hq2]) hstk hbfc hszl hcap2
  have hF := newChildS_fresh (ops := ops) q2 H (vc st) P.ecap P.bcap g.L g.fresh Ds (l + 1)
    (P.top - (l + 1)) (by omega) hdl2 (by simp [hq2, hq1]) (by simp [hq2]) hstk hbfc hszl hcap2
  refine runs_seq ((Runs.sframe (runs_and hN hF) (by simp [NoAlloc, newChildS])).mono
    (fun r3 hr3 => ?_))
  obtain ⟨⟨⟨hDL3, hc3⟩, hbf3⟩, hU3, hwl3, hvl3⟩ := hr3
  have e1 : l + 1 - 1 = l := by omega
  have e2 : P.top - (l + 1) + 1 = P.top - l := by omega
  rw [e1, e2] at hDL3
  have hU3w : ∀ x, x ∉ ["nw.b", "nw.id", "blk.fresh"] → r3.w x = q2.w x := fun x hx =>
    hU3.wreg x (by simpa [sWR, newChildS] using hx)
  have hU3a : ∀ a, a ∉ ["dsl.base", "blk.hd", "blk.tl", "blk.cnt", "blk.bot", "dsl.stk", "dsl.sz"] →
      r3.wa a = q2.wa a := fun a ha => (hU3.warr a (by simpa [sWA, newChildS] using ha)).1
  have hU3v : r3.va = q2.va := by funext a; exact (hU3.varr a (by simp [sVA, newChildS])).1
  have hr3l : r3.w "lvl" = l := by rw [hU3w _ (by simp), hq2w _ (by simp) (by simp), hl]
  have hr3n : r3.w "n" = G.n := by rw [hU3w _ (by simp), hq2w _ (by simp) (by simp), hn]
  have hr3wl : r3.wlen = st.wlen := by rw [hwl3, hq2wl]
  have hr3vl : r3.vlen = st.vlen := by rw [hvl3]; simp [hq2, hq1]
  have hr3c : r3.cap = st.cap := by rw [hU3.cap, hq2c]
  have hq2a : q2.wa = st.wa := by simp [hq2, hq1]
  have hq2va : q2.va = st.va := by simp [hq2, hq1]
  have hSL3 : SlotLens r3 (4 * l) := by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hSL
    exact ⟨by rw [hr3vl]; exact a1, by rw [hr3wl]; exact a2, by rw [hr3wl]; exact a3,
      by rw [hr3wl]; exact a4, by rw [hr3wl]; exact a5, by rw [hr3wl]; exact a6⟩
  refine runs_seq ((Runs.sframe (copyBdM_spec (ops := ops) r3 l hr3l (by rw [hr3wl]; have := hLn.M; omega)
    (by rw [hr3wl]; exact hML) (by rw [hr3vl]; have := hLn.bl; omega)
    (by rw [hr3wl]; have := hLn.bh; omega) (by rw [hr3wl]; have := hLn.bv; omega)
    (by rw [hr3wl]; have := hLn.be; omega) (by rw [hr3wl]; have := hLn.br; omega)
    (by rw [hr3wl]; have := hLn.bf; omega) hSL3 (by rw [hr3c]; omega))
    (by simp [NoAlloc, copyBdM])).mono (fun r4 hr4 => ?_))
  obtain ⟨⟨hM4, hbl4, hbh4, hbv4, hbe4, hbr4, hbf4, hc4⟩, hU4, hwl4, hvl4⟩ := hr4
  have hr4w : r4.w = r3.w := by funext x; exact hU4.wreg x (by simp [sWR, copyBdM])
  have hU4a : ∀ a, a ∉ ["dsl.M", "dsl.bh", "dsl.bv", "dsl.be", "dsl.br", "dsl.bf"] →
      r4.wa a = r3.wa a := fun a ha => (hU4.warr a (by simpa [sWA, copyBdM] using ha)).1
  have hU4v : ∀ a, a ≠ "dsl.bl" → r4.va a = r3.va a := fun a ha =>
    (hU4.varr a (by simpa [sVA, copyBdM] using ha)).1
  refine runs_seq (runs_wset (a := G.n + l) (by
    simp [hr4w, hr3l, hr3n, fit]; rw [hU4.cap, hr3c]; omega) ?_)
  set q5 := (r4.setW "kl.s" (G.n + l)).charge 1 with hq5
  -- the lists are untouched so far
  have hlkn : q5.wa "lk.n" = st.wa "lk.n" := by
    simp only [hq5, State.charge_wa, State.setW_wa]
    rw [hU4a _ (by simp), hU3a _ (by simp), hq2a]
  have hlkp : q5.wa "lk.p" = st.wa "lk.p" := by
    simp only [hq5, State.charge_wa, State.setW_wa]
    rw [hU4a _ (by simp), hU3a _ (by simp), hq2a]
  have hq5wl : q5.wlen = st.wlen := by simp [hq5, hwl4, hr3wl]
  have hK5 : KL.LL (q5.wa "lk.n") (q5.wa "lk.p") G.n (l + 1) P.top K := by rw [hlkn, hlkp]; exact hK
  refine (Runs.sframe (KL.klInit_LL (ops := ops) q5 hK5 (by omega) (by simp [hq5, e1]) htop
    (by rw [hq5wl]; exact hLn.lkn) (by rw [hq5wl]; exact hLn.lkp))
    (by simp [NoAlloc, KL.klInit])).mono ?_
  rintro r ⟨⟨hL, hU6, hwl6, hc6⟩, hU6', hwl6', hvl6'⟩
  rw [e1] at hL
  -- facts about the final state
  have hrw : ∀ x, x ≠ "kl.s" → r.w x = r4.w x := by
    intro x hx; rw [hU6.wreg x (by simp)]; simp [hq5, hx]
  have hra : ∀ a, a ≠ "lk.n" → a ≠ "lk.p" → r.wa a = r4.wa a := by
    intro a h1 h2; rw [(hU6.warr a (by simp [h1, h2])).1]; simp [hq5]
  have hrva : r.va = r4.va := by funext a; rw [(hU6.varr a (by simp)).1]; simp [hq5]
  have hrwl : r.wlen = st.wlen := by rw [hwl6, hq5wl]
  have hrvl : r.vlen = st.vlen := by rw [hvl6', hq5]; simp [hvl4, hr3vl]
  have hrc : r.cap = st.cap := by rw [hU6.cap]; simp [hq5, hU4.cap, hr3c]
  have hvc : vc (G := G) r = vc st := by
    funext v; unfold vc
    rw [hra _ (by simp) (by simp), hU4a _ (by simp), hU3a _ (by simp), hq2a]
  -- the D arrays of the new level
  have hbfl : r.wa "dsl.bf" = Function.update (st.wa "dsl.bf") l (st.wa "sl.f" (4 * l)) := by
    rw [hra _ (by simp) (by simp), hbf4, hU3a _ (by simp), hU3a _ (by simp), hq2a]
  have hbll : r.va "dsl.bl" = Function.update (st.va "dsl.bl") l (st.va "sl.l" (4 * l)) := by
    rw [hrva, hbl4, hU3v, hq2va]
  have hbhl : r.wa "dsl.bh" = Function.update (st.wa "dsl.bh") l (st.wa "sl.h" (4 * l)) := by
    rw [hra _ (by simp) (by simp), hbh4, hU3a _ (by simp), hU3a _ (by simp), hq2a]
  have hbvl : r.wa "dsl.bv" = Function.update (st.wa "dsl.bv") l (st.wa "sl.v" (4 * l)) := by
    rw [hra _ (by simp) (by simp), hbv4, hU3a _ (by simp), hU3a _ (by simp), hq2a]
  have hbel : r.wa "dsl.be" = Function.update (st.wa "dsl.be") l (st.wa "sl.e" (4 * l)) := by
    rw [hra _ (by simp) (by simp), hbe4, hU3a _ (by simp), hU3a _ (by simp), hq2a]
  have hbrl : r.wa "dsl.br" = Function.update (st.wa "dsl.br") l (st.wa "sl.r" (4 * l)) := by
    rw [hra _ (by simp) (by simp), hbr4, hU3a _ (by simp), hU3a _ (by simp), hq2a]
  have hMl : r.wa "dsl.M" = Function.update (st.wa "dsl.M") l M := by
    rw [hra _ (by simp) (by simp), hM4, hU3a _ (by simp), hU3a _ (by simp), hq2a, hM]
  have hU45 : Unchanged r4 q5 [] [] ["kl.s"] [] := by
    rw [hq5, unch_charge, unch_setW (by simp)]; exact Unchanged.refl _ _ _ _ _
  have hUall := (hU4.comp hU45).comp hU6
  have hbfr : r.w "blk.fresh" = st.w "blk.fresh" + 1 := by
    rw [hrw _ (by simp), hr4w, hbf3, hbf2]
  have hdfr : r.w "ds.fresh" = st.w "ds.fresh" := by
    rw [hrw _ (by simp), hr4w, hU3w _ (by simp), hq2w _ (by simp) (by simp)]
  refine ⟨⟨by omega, ?_, fun j h1 h2 => ?_, fun j h1 h2 => ?_, ⟨Function.update K l [], hL,
      fun j h1 h2 v => ?_⟩, fun j h1 h2 => ?_, fun j h1 h2 => ?_, hD.lf, ?_,
      hLn.of_len hrwl hrvl hrc, fun j hj => by
        rw [Function.update_of_ne (show j ≠ l by omega)]; exact hD.hib j hj,
      by rw [hU6'.procs, hU45.procs, hU4.procs, hU3.procs, hU2.procs]; exact hD.procs,
      fun i hi => by
        rw [hra _ (by decide) (by decide), hU4a _ (by decide), hU3a _ (by decide), hq2a]
        exact hD.keys i hi,
      fun j h1 h2 => by
        rw [hrc]
        by_cases hjl : j = l
        · subst hjl; rw [Function.update_self]; exact hMc
        · rw [Function.update_of_ne hjl]; exact hD.mc j (by omega) h2⟩, ?_⟩
  · -- the DLRep of the new layer
    rw [hvc]
    exact DLRep.of_unch hDL3 hUall (by decide) (by decide) (by decide)
  · rw [hvc]
    by_cases hjl : j = l
    · subst hjl
      rw [Function.update_self]
      show BdHolds r j H (vc st) Bd
      obtain ⟨hs1, hs2⟩ := hSB
      unfold slotB at hs1 hs2
      refine ⟨by rw [hbfl, Function.update_self]; exact hs1, fun q hq => ?_⟩
      obtain ⟨x, ⟨x1, x2, x3, x4, x5⟩, hxq⟩ := hs2 q hq
      refine ⟨x, ⟨?_, ?_, ?_, ?_, ?_⟩, hxq⟩
      · show r.va "dsl.bl" j = x.len; rw [hbll, Function.update_self]; exact x1
      · show r.wa "dsl.bh" j = x.hops; rw [hbhl, Function.update_self]; exact x2
      · show r.wa "dsl.bv" j = x.v; rw [hbvl, Function.update_self]; exact x3
      · show r.wa "dsl.be" j = encE x.e; rw [hbel, Function.update_self]; exact x4
      · show r.wa "dsl.br" j = x.ver; rw [hbrl, Function.update_self]; exact x5
    · rw [Function.update_of_ne hjl]
      exact (hD.bd j (by omega) h2).of_eq (by rw [hbfl, Function.update_of_ne hjl])
        (by rw [hbll, Function.update_of_ne hjl]) (by rw [hbhl, Function.update_of_ne hjl])
        (by rw [hbvl, Function.update_of_ne hjl]) (by rw [hbel, Function.update_of_ne hjl])
        (by rw [hbrl, Function.update_of_ne hjl])
  · by_cases hjl : j = l
    · subst hjl; rw [Function.update_self, hMl, Function.update_self]; rfl
    · rw [Function.update_of_ne hjl, hMl, Function.update_of_ne hjl]; exact hD.mv j (by omega) h2
  · by_cases hjl : j = l
    · subst hjl
      simp only [Function.update_self, List.not_mem_nil, false_iff]
      exact hasKey_newC _ _ _ _
    · rw [Function.update_of_ne hjl, Function.update_of_ne hjl]; exact hKk j (by omega) h2 v
  · by_cases hjl : j = l
    · subst hjl; rw [Function.update_self]; exact wf_newC _ _ _
    · rw [Function.update_of_ne hjl]; exact hD.wf j (by omega) h2
  · by_cases hjl : j = l
    · subst hjl; rw [Function.update_self]; exact freshOK_newC _ _ _
    · rw [Function.update_of_ne hjl]; exact hD.fr j (by omega) h2
  · rw [hdfr, hbfr]; omega
  · refine ⟨?_, by rw [hdfr, hbfr]; omega⟩
    rw [hc6]; simp only [hq5, State.charge_cost, State.setW_cost]
    rw [hc4, hc3]; simp [hq2, hq1]

theorem dsNew_spec {ops : VOps ℝ≥0} (P : DPar) (st : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m))
    (g : DGl G s) (Ds : ℕ → DStrM G s) (l M : ℕ) (Bd : WLab G s)
    (hD : DRI P st H g Ds (l + 1)) (hl : st.w "lvl" = l) (hn : st.w "n" = G.n)
    (hM : st.wa "cp.M" l = M) (hML : l < st.wlen "cp.M") (hSB : SlotHolds st (slotB l) H (vc st) Bd)
    (hSL : SlotLens st (slotB l)) (hroom : st.w "ds.fresh" + st.w "blk.fresh" + 1 ≤ P.ucap)
    (hMc : 2 * M + 2 < st.cap) :
    Runs ops dsNew st (fun r => DRI P r H g (Function.update Ds l (newC M Bd)) l ∧
      Unchanged st r (sWA dsNew) (sVA dsNew) (sWR dsNew) (sVR dsNew) ∧ r.wlen = st.wlen ∧
      r.vlen = st.vlen ∧ st.cost ≤ r.cost ∧ r.cost = st.cost + 22 ∧
      r.w "ds.fresh" + r.w "blk.fresh" = st.w "ds.fresh" + st.w "blk.fresh" + 1) :=
  (Runs.sframe (dsNew_main P st H g Ds l M Bd hD hl hn hM hML hSB hSL hroom hMc) dsNew_noalloc).mono
    (fun _ ⟨⟨h1, h2, h3⟩, hU, hwl, hvl⟩ => ⟨h1, hU, hwl, hvl, by omega, h2, h3⟩)

/-! ## Unlinking the keys of a row (FIX-STALE deletion, pulled keys) -/

def ulBody (arr : String) : Stmt :=
  seq (wset "kl.v" (load arr (add (var "ul.off") (var "ul.j"))))
  (seq KL.klUnlink (wset "ul.j" (add (var "ul.j") (lit 1))))

def ulLoop (arr : String) : Stmt := .while (lt (var "ul.j") (var "ul.len")) (ulBody arr)

/-- unlink the keys `arr[ul.off, ul.off + ul.len)` from the live-key lists -/
def unlinkRow (arr : String) : Stmt := seq (wset "ul.j" (lit 0)) (ulLoop arr)

structure UInv (st0 q : State ℝ≥0) (ks : List ℕ) (lo top : ℕ) (K : ℕ → List ℕ) (j : ℕ) : Prop where
  jr : q.w "ul.j" = j
  jle : j ≤ ks.length
  ll : ∃ K' : ℕ → List ℕ, KL.LL (q.wa "lk.n") (q.wa "lk.p") G.n lo top K' ∧
    ∀ i, lo ≤ i → i ≤ top → ∀ x, x ∈ K' i ↔ x ∈ K i ∧ x ∉ ks.take j
  unch : Unchanged st0 q ["lk.n", "lk.p"] [] ["ul.j", "kl.v", "kl.a", "kl.b"] []
  wl : q.wlen = st0.wlen

theorem ul_loop {ops : VOps ℝ≥0} (st0 : State ℝ≥0) (arr : String) (ks : List ℕ) (off lo top : ℕ)
    (K : ℕ → List ℕ) (hsp : Spells st0 arr off ks) (hoff : st0.w "ul.off" = off)
    (hlen : st0.w "ul.len" = ks.length) (harr : off + ks.length ≤ st0.wlen arr)
    (hks : ∀ x ∈ ks, x < G.n) (hl1 : G.n + top < st0.wlen "lk.n") (hl2 : G.n + top < st0.wlen "lk.p")
    (hcap : off + ks.length + 1 < st0.cap) (harrne : arr ≠ "lk.n" ∧ arr ≠ "lk.p") :
    ∀ (n j : ℕ) (q : State ℝ≥0), ks.length - j = n → UInv (G := G) st0 q ks lo top K j →
      Runs ops (ulLoop arr) q (fun r => UInv (G := G) st0 r ks lo top K ks.length ∧
        r.cost = q.cost + 9 * n + 1)
  | 0, j, q, hn, hI => by
      have hj : j = ks.length := by have := hI.jle; omega
      subst hj
      have hc1 : 1 < q.cap := by rw [hI.unch.cap]; omega
      have hlq : q.w "ul.len" = ks.length := by rw [hI.unch.wreg _ (by simp)]; exact hlen
      refine Frontier.CHD.DList.runs_while_exit (by simp [hI.jr, hlq, fit, hc1,
        show q.cap ≠ 0 by omega]) ?_
      obtain ⟨K', hK', hK'm⟩ := hI.ll
      exact ⟨⟨by simp [hI.jr], le_rfl, ⟨K', by simpa using hK', hK'm⟩, (unch_charge 1).mpr hI.unch,
        by simp [hI.wl]⟩, by simp⟩
  | n + 1, j, q, hn, hI => by
      have hj : j < ks.length := by omega
      have hcq : q.cap = st0.cap := hI.unch.cap
      have hc1 : 1 < q.cap := by omega
      have hlq : q.w "ul.len" = ks.length := by rw [hI.unch.wreg _ (by simp)]; exact hlen
      have hoq : q.w "ul.off" = off := by rw [hI.unch.wreg _ (by simp)]; exact hoff
      have harrq : q.wa arr = st0.wa arr := (hI.unch.warr arr (by simpa using harrne)).1
      have harrl : q.wlen arr = st0.wlen arr := (hI.unch.warr arr (by simpa using harrne)).2
      have hkj : q.wa arr (off + j) = ks[j] := by rw [harrq]; exact hsp j hj
      refine Frontier.CHD.DList.runs_while_step (x := 1) (by simp [hI.jr, hlq, fit, hc1, hj])
        one_ne_zero ?_
      refine runs_seq (runs_wset (a := ks[j]) (by
        simp [hoq, hI.jr, fit, show off + j < q.cap by omega, show off + j < q.wlen arr by omega, hkj]) ?_)
      set q1 := ((q.charge 1).setW "kl.v" ks[j]).charge 1 with hq1
      obtain ⟨K', hK', hK'm⟩ := hI.ll
      have hK1 : KL.LL (q1.wa "lk.n") (q1.wa "lk.p") G.n lo top K' := by simpa [hq1] using hK'
      have hvN : ks[j] < G.n := hks _ (List.getElem_mem hj)
      have hq1wl : q1.wlen = st0.wlen := by simp [hq1, hI.wl]
      refine runs_seq ((KL.klUnlink_LL (ops := ops) q1 hK1 (by simp [hq1]) hvN
        (by rw [hq1wl]; exact hl1) (by rw [hq1wl]; exact hl2)).mono (fun q2 hq2 => ?_))
      obtain ⟨hL2, hU2, hwl2, hc2⟩ := hq2
      have hj2 : q2.w "ul.j" = j := by rw [hU2.wreg _ (by simp)]; simp [hq1, hI.jr]
      have hc2' : q2.cap = st0.cap := by rw [hU2.cap]; simp [hq1, hcq]
      refine runs_wset (a := j + 1) (by
        simp [hj2, fit, hc2', show 1 < st0.cap by omega, show j + 1 < st0.cap by omega]) ?_
      refine (ul_loop st0 arr ks off lo top K hsp hoff hlen harr hks hl1 hl2 hcap harrne n (j + 1) _
        (by omega) ⟨by simp, by omega, ⟨fun i => (K' i).erase ks[j], by simpa using hL2, ?_⟩, ?_, ?_⟩).mono ?_
      · intro i hi1 hi2 x
        have hnd : (K' i).Nodup := (List.nodup_cons.mp (hK'.cl i hi1 hi2).2).2
        rw [hnd.mem_erase_iff, hK'm i hi1 hi2 x, List.take_succ_eq_append_getElem hj]
        simp only [List.mem_append, List.mem_singleton, not_or]
        tauto
      · have hUq1 : Unchanged q q1 [] [] ["kl.v"] [] := by
          rw [hq1, unch_charge, unch_setW (show "kl.v" ∈ ["kl.v"] by simp), unch_charge]
          exact Unchanged.refl _ _ _ _ _
        rw [unch_charge, unch_setW (by simp)]
        exact ((hI.unch.comp hUq1).comp hU2).mono (fun x hx => by simp at hx ⊢; tauto)
          (fun x hx => by simp at hx) (fun x hx => by simp at hx ⊢; tauto) (fun x hx => by simp at hx)
      · simp [hwl2, hq1wl]
      · rintro r ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rw [h2]; simp [hc2, hq1]; omega

theorem unlinkRow_spec {ops : VOps ℝ≥0} (st0 : State ℝ≥0) (arr : String) (ks : List ℕ)
    (off lo top : ℕ) (K : ℕ → List ℕ) (hK : KL.LL (st0.wa "lk.n") (st0.wa "lk.p") G.n lo top K)
    (hsp : Spells st0 arr off ks) (hoff : st0.w "ul.off" = off) (hlen : st0.w "ul.len" = ks.length)
    (harr : off + ks.length ≤ st0.wlen arr) (hks : ∀ x ∈ ks, x < G.n)
    (hl1 : G.n + top < st0.wlen "lk.n") (hl2 : G.n + top < st0.wlen "lk.p")
    (hcap : off + ks.length + 1 < st0.cap) (harrne : arr ≠ "lk.n" ∧ arr ≠ "lk.p") :
    Runs ops (unlinkRow arr) st0 (fun r => (∃ K' : ℕ → List ℕ,
        KL.LL (r.wa "lk.n") (r.wa "lk.p") G.n lo top K' ∧
        ∀ i, lo ≤ i → i ≤ top → ∀ x, x ∈ K' i ↔ x ∈ K i ∧ x ∉ ks) ∧
      Unchanged st0 r ["lk.n", "lk.p"] [] ["ul.j", "kl.v", "kl.a", "kl.b"] [] ∧
      r.wlen = st0.wlen ∧ r.cost = st0.cost + 9 * ks.length + 2) := by
  have hc0 : 0 < st0.cap := by omega
  refine runs_seq (runs_wset (a := 0) (by simp [fit, hc0]) ?_)
  set q := (st0.setW "ul.j" 0).charge 1 with hq
  have hI : UInv (G := G) st0 q ks lo top K 0 := by
    refine ⟨by simp [hq], Nat.zero_le _, ⟨K, by simpa [hq] using hK, fun i _ _ x => by simp⟩, ?_,
      by simp [hq]⟩
    rw [hq, unch_charge, unch_setW (by simp)]; exact Unchanged.refl _ _ _ _ _
  refine (ul_loop (ops := ops) st0 arr ks off lo top K hsp hoff hlen harr hks hl1 hl2 hcap harrne
    ks.length 0 q (by simp) hI).mono ?_
  rintro r ⟨hI', hc⟩
  obtain ⟨K', hK', hK'm⟩ := hI'.ll
  refine ⟨⟨K', hK', fun i h1 h2 x => by rw [hK'm i h1 h2 x, List.take_length]⟩, hI'.unch, hI'.wl, ?_⟩
  rw [hc]; simp [hq]; omega

theorem hasKey_clearKeys (L : LiveM G s) (D : DStrM G s) (ks : List (Fin G.n)) (v : Fin G.n) :
    DB.HasKey (DB.clearKeys L ks) D v ↔ DB.HasKey L D v ∧ v ∉ ks := by
  constructor
  · rintro ⟨e, he, hk⟩
    obtain ⟨hb, hl⟩ := mem_liveVals.mp he
    obtain ⟨hl1, hl2⟩ := isLive_clearKeys.mp hl
    exact ⟨⟨e, mem_liveVals.mpr ⟨hb, hl1⟩, hk⟩, hk ▸ hl2⟩
  · rintro ⟨⟨e, he, hk⟩, hv⟩
    obtain ⟨hb, hl⟩ := mem_liveVals.mp he
    exact ⟨e, mem_liveVals.mpr ⟨hb, isLive_clearKeys.mpr ⟨hl, hk ▸ hv⟩⟩, hk⟩

/-- BM.15 (FIX-STALE): the keys of the child's `U` row leave the live map and the live-key lists -/
def dsDelB : Stmt :=
  seq (wset "dd.off" (mul (sub (var "lvl") (lit 1)) (var "n")))
  (seq (wset "dd.len" (load "U.len" (sub (var "lvl") (lit 1))))
  (seq (delS "U")
  (seq (wset "ul.off" (var "dd.off"))
  (seq (wset "ul.len" (var "dd.len")) (unlinkRow "U")))))

theorem dsDelB_noalloc : NoAlloc dsDelB := by
  simp [NoAlloc, dsDelB, delS, delLoop, delBody, unlinkRow, ulLoop, ulBody, KL.klUnlink]

theorem delC_L (g : DGl G s) (ks : List (Fin G.n)) : (BM.delC g ks).1.L = DB.clearKeys g.L ks := rfl
theorem delC_fresh (g : DGl G s) (ks : List (Fin G.n)) : (BM.delC g ks).1.fresh = g.fresh := rfl

theorem dsDelB_main {ops : VOps ℝ≥0} (P : DPar) (st : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m))
    (g : DGl G s) (Ds : ℕ → DStrM G s) (l : ℕ) (lU : List (Fin G.n)) (hl1 : 1 ≤ l)
    (hD : DRI P st H g Ds l) (hl : st.w "lvl" = l) (hn : st.w "n" = G.n)
    (hU : RowRep st "U" "U.len" G.n (l - 1) (lU.map Fin.val)) :
    Runs ops dsDelB st (fun r => DRI P r H (BM.delC g lU).1 Ds l ∧
      r.cost ≤ st.cost + 13 * lU.length + 9) := by
  have hc := hD.lens.cap
  have hrc := hD.lens.rowcap
  have htop := hD.lo_le
  have hLn := hD.lens
  obtain ⟨hUlen, hUarr, hUl, hUv, hUs⟩ := hU
  simp only [List.length_map] at hUlen hUv hUs
  set off := (l - 1) * G.n with hoff
  have hl' : l - 1 ≤ P.top := by omega
  have hmul1 : (l - 1) * G.n ≤ P.top * G.n := Nat.mul_le_mul_right _ hl'
  have hmul2 : P.top * G.n + G.n + 1 ≤ (P.top + 2) * (G.n + 2) := by nlinarith
  have hoffc : off + lU.length + 1 < st.cap := by omega
  have h1c : 1 < st.cap := by omega
  refine runs_seq (runs_wset (a := off) (by simp [hl, hn, fit, h1c]; omega) ?_)
  set q1 := (st.setW "dd.off" off).charge 1 with hq1
  refine runs_seq (runs_wset (a := lU.length) (by
    simp [hq1, hl, fit, h1c, hUl, hUv]) ?_)
  set q2 := (q1.setW "dd.len" lU.length).charge 1 with hq2
  have hU2 : Unchanged st q2 [] [] ["dd.off", "dd.len"] [] := by
    rw [hq2, unch_charge, unch_setW (by simp), hq1, unch_charge, unch_setW (by simp)]
    exact Unchanged.refl _ _ _ _ _
  have hdl2 : DLRep q2 H (vc st) P.ecap P.bcap g.L g.fresh Ds l (P.top - l) :=
    DLRep.of_unch hD.dl hU2 (by simp) (by simp) (by simp [drWR])
  have hsp : Spells q2 "U" off (lU.map Fin.val) := by
    intro r hr; simp only [hq2, hq1, State.charge_wa, State.setW_wa]; simpa using hUs r (by simpa using hr)
  have hsucc : (l - 1 + 1) * G.n = off + G.n := by rw [hoff, Nat.succ_mul]
  have harr0 : off + lU.length ≤ st.wlen "U" := by omega
  have harr : off + lU.length ≤ q2.wlen "U" := by
    simp only [hq2, hq1, State.charge_wlen, State.setW_wlen]; exact harr0
  refine runs_seq ((Runs.sframe (delDL (ops := ops) q2 H (vc st) P.ecap P.bcap g.L g.fresh Ds l
    (P.top - l) hdl2 "U" lU off hsp (by simp [hq2, hq1]) (by simp [hq2]) harr
    (by simp [hq2, hq1]; omega) (by decide)) (by simp [NoAlloc, delS, delLoop, delBody])).mono
    (fun r3 hr3 => ?_))
  obtain ⟨⟨hDL3, hU3, hc3⟩, hU3', hwl3, hvl3⟩ := hr3
  refine runs_seq (runs_wset (a := off) (by
    simp only [evalW]; rw [hU3.wreg _ (by simp)]; simp [hq2, hq1]) ?_)
  set q4 := (r3.setW "ul.off" off).charge 1 with hq4
  refine runs_seq (runs_wset (a := lU.length) (by
    simp only [evalW, hq4, State.charge_w, State.setW_w]; rw [hU3.wreg _ (by simp)]; simp [hq2]) ?_)
  set q5 := (q4.setW "ul.len" lU.length).charge 1 with hq5
  have hU45 : Unchanged r3 q5 [] [] ["ul.off", "ul.len"] [] := by
    rw [hq5, unch_charge, unch_setW (by simp), hq4, unch_charge, unch_setW (by simp)]
    exact Unchanged.refl _ _ _ _ _
  obtain ⟨K, hK, hKk⟩ := hD.kl
  have hq5a : ∀ a, a ≠ "live" → q5.wa a = st.wa a := by
    intro a ha
    rw [(hU45.warr a (by simp)).1, (hU3.warr a (by simpa using ha)).1, (hU2.warr a (by simp)).1]
  have hq5wl : q5.wlen = st.wlen := by
    rw [show q5.wlen = r3.wlen by simp [hq5, hq4], hwl3]; simp [hq2, hq1]
  have hq5c : q5.cap = st.cap := by rw [hU45.cap, hU3.cap, hU2.cap]
  have hK5 : KL.LL (q5.wa "lk.n") (q5.wa "lk.p") G.n l P.top K := by
    rw [hq5a _ (by simp), hq5a _ (by simp)]; exact hK
  have hsp5 : Spells q5 "U" off (lU.map Fin.val) := by
    intro r hr; rw [hq5a _ (by simp)]; simpa using hUs r (by simpa using hr)
  refine (Runs.sframe (unlinkRow_spec (ops := ops) q5 "U" (lU.map Fin.val) off l P.top K hK5 hsp5
    (by simp [hq5, hq4]) (by simp [hq5]) (by rw [hq5wl]; simpa using harr0)
    (fun x hx => by obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx; exact v.isLt)
    (by rw [hq5wl]; exact hLn.lkn) (by rw [hq5wl]; exact hLn.lkp) (by rw [hq5c]; simpa using hoffc)
    (by decide)) (by simp [NoAlloc, unlinkRow, ulLoop, ulBody, KL.klUnlink])).mono ?_
  rintro r ⟨⟨⟨K', hK', hK'm⟩, hU6, hwl6, hc6⟩, hU6', hwl6', hvl6'⟩
  have hUall : Unchanged r3 r ["lk.n", "lk.p"] [] (["ul.off", "ul.len"] ++ ["ul.j", "kl.v", "kl.a", "kl.b"]) [] :=
    (hU45.comp hU6).mono (by simp) (by simp) (by simp) (by simp)
  have hra : ∀ a, a ≠ "lk.n" → a ≠ "lk.p" → r.wa a = q5.wa a := by
    intro a h1 h2; exact (hU6.warr a (by simp [h1, h2])).1
  have hrva : r.va = st.va := by
    funext a; rw [(hU6.varr a (by simp)).1, (hU45.varr a (by simp)).1, (hU3.varr a (by simp)).1,
      (hU2.varr a (by simp)).1]
  have hrwl : r.wlen = st.wlen := by rw [hwl6, hq5wl]
  have hrvl : r.vlen = st.vlen := by
    rw [hvl6', show q5.vlen = r3.vlen by simp [hq5, hq4], hvl3]; simp [hq2, hq1]
  have hrc : r.cap = st.cap := by rw [hU6.cap, hq5c]
  have hvc : vc (G := G) r = vc st := by
    funext v; unfold vc; rw [hra _ (by simp) (by simp), hq5a _ (by simp)]
  have hrw : ∀ x ∈ drWR, r.w x = st.w x := by
    intro x hx; simp [drWR] at hx
    rcases hx with rfl | rfl <;>
    · rw [hU6.wreg _ (by simp), hU45.wreg _ (by simp), hU3.wreg _ (by simp), hU2.wreg _ (by simp)]
  have hbdeq : ∀ a ∈ ["dsl.bf", "dsl.bh", "dsl.bv", "dsl.be", "dsl.br", "dsl.M"], r.wa a = st.wa a := by
    intro a ha; rw [hra a (by intro e; subst e; simp at ha) (by intro e; subst e; simp at ha),
      hq5a a (by intro e; subst e; simp at ha)]
  refine ⟨⟨htop, ?_, fun j h1 h2 => ?_, fun j h1 h2 => ?_, ⟨K', hK', fun j h1 h2 v => ?_⟩,
      fun j h1 h2 => ?_, fun j h1 h2 => hD.fr j h1 h2, ?_, ?_, hLn.of_len hrwl hrvl hrc, hD.hib,
      by rw [hU6.procs, hU45.procs, hU3.procs, hU2.procs]; exact hD.procs,
      fun i hi => by rw [hra _ (by decide) (by decide), hq5a _ (by decide)]; exact hD.keys i hi,
      fun j h1 h2 => by rw [hrc]; exact hD.mc j h1 h2⟩, ?_⟩
  · rw [hvc, delC_L, delC_fresh]
    exact DLRep.of_unch hDL3 hUall (by decide) (by decide) (by decide)
  · rw [hvc]
    exact (hD.bd j h1 h2).of_eq (by rw [hbdeq _ (by simp)]) (by rw [hrva])
      (by rw [hbdeq _ (by simp)]) (by rw [hbdeq _ (by simp)]) (by rw [hbdeq _ (by simp)])
      (by rw [hbdeq _ (by simp)])
  · rw [hbdeq _ (by simp)]; exact hD.mv j h1 h2
  · rw [hK'm j h1 h2 v, hKk j h1 h2 v, delC_L, hasKey_clearKeys]
    have hm : ((v : ℕ) ∈ lU.map Fin.val) ↔ v ∈ lU :=
      ⟨fun h => by obtain ⟨w, hw, e⟩ := List.mem_map.mp h; exact (Fin.ext e) ▸ hw,
        fun h => List.mem_map_of_mem h⟩
    rw [hm]
  · rw [delC_L]; exact (deleteKeys_spec (hD.wf j h1 h2)).2
  · intro u i a hu
    rw [delC_L] at hu; rw [delC_fresh]
    simp only [DB.clearKeys] at hu
    split_ifs at hu
    exact hD.lf u i a hu
  · rw [hrw _ (by simp [drWR]), hrw _ (by simp [drWR])]; exact hD.use
  · simp only [List.length_map] at hc6
    rw [hc6]
    have hq5c' : q5.cost = r3.cost + 2 := by simp [hq5, hq4]
    have hq2c : q2.cost = st.cost + 2 := by simp [hq2, hq1]
    omega

theorem dsDelB_spec {ops : VOps ℝ≥0} (P : DPar) (st : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m))
    (g : DGl G s) (Ds : ℕ → DStrM G s) (l : ℕ) (lU : List (Fin G.n)) (hl1 : 1 ≤ l)
    (hD : DRI P st H g Ds l) (hl : st.w "lvl" = l) (hn : st.w "n" = G.n)
    (hU : RowRep st "U" "U.len" G.n (l - 1) (lU.map Fin.val)) :
    Runs ops dsDelB st (fun r => DRI P r H (BM.delC g lU).1 Ds l ∧
      Unchanged st r (sWA dsDelB) (sVA dsDelB) (sWR dsDelB) (sVR dsDelB) ∧ r.wlen = st.wlen ∧
      r.vlen = st.vlen ∧ st.cost ≤ r.cost ∧ r.cost ≤ st.cost + 13 * lU.length + 9) :=
  (Runs.sframe (Runs.cost_mono (dsDelB_main P st H g Ds l lU hl1 hD hl hn hU)) dsDelB_noalloc).mono
    (fun _ ⟨⟨⟨h1, h2⟩, h3⟩, hU', hwl, hvl⟩ => ⟨h1, hU', hwl, hvl, h3, h2⟩)

/-! ## Family facts for the insertion -/

theorem recsOf_snd (st : State ℝ≥0) (bse : ℕ) (P : List (Block (Fin G.n) (WLab G s))) :
    (recsOf st bse P).map Prod.snd = P := by
  unfold recsOf
  exact List.map_snd_zip (by simp)

theorem mem_recsFrom_inv {st : State ℝ≥0} {Ds : ℕ → DStrM G s} :
    ∀ (n l0 : ℕ) (p : ℕ × Block (Fin G.n) (WLab G s)), p ∈ recsFrom st Ds l0 n →
      ∃ j, l0 ≤ j ∧ j < l0 + n ∧ p.2 ∈ (Ds j).blocks
  | 0, _, p, hp => by simp [recsFrom] at hp
  | n + 1, l0, p, hp => by
      simp only [recsFrom, List.mem_append] at hp
      rcases hp with hp | hp
      · refine ⟨l0, le_rfl, by omega, ?_⟩
        rw [← recsOf_snd st (base st l0) (Ds l0).blocks]
        exact List.mem_map_of_mem hp
      · obtain ⟨j, h1, h2, h3⟩ := mem_recsFrom_inv n (l0 + 1) p hp
        exact ⟨j, by omega, by omega, h3⟩

theorem entIds_eq_allEnts (bs : List (Block (Fin G.n) (WLab G s))) :
    entIds bs = (allEnts bs).map (·.id) := by
  induction bs with
  | nil => simp [entIds, allEnts]
  | cons b bs ih => rw [entIds_cons, ih]; simp [allEnts]

/-- the entries of the deepest level have distinct ids -/
theorem DLRep.ids_lo {st : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {ecap bcap : ℕ} {L : Live (Fin G.n) (WLab G s)} {fresh : ℕ} {Ds : ℕ → DStrM G s} {lo k : ℕ}
    (h : DLRep st H V ecap bcap L fresh Ds lo k) : DB.IdsNodup (Ds lo) := by
  have hnd := h.recs.2.2
  have e : recsFrom st Ds lo (k + 1) = recsOf st (base st lo) (Ds lo).blocks ++
      recsFrom st Ds (lo + 1) k := rfl
  rw [e, List.map_append, recsOf_snd, entIds_append] at hnd
  unfold DB.IdsNodup
  rw [← entIds_eq_allEnts]
  exact hnd.of_append_left

/-- all entry ids of the family are below the counter -/
theorem fam_fresh {st : State ℝ≥0} {Ds : ℕ → DStrM G s} {lo k f : ℕ}
    (hfr : ∀ j, lo ≤ j → j ≤ lo + k → DB.FreshOK f (Ds j)) :
    ∀ x ∈ entIds ((recsFrom st Ds lo (k + 1)).map Prod.snd), x < f := by
  intro x hx
  unfold entIds at hx
  obtain ⟨b, hb, hxb⟩ := List.mem_flatMap.mp hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
  obtain ⟨j, h1, h2, h3⟩ := mem_recsFrom_inv (k + 1) lo p hp
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hxb
  exact hfr j h1 (by omega) e (mem_allEnts.mpr ⟨p.2, h3, he⟩)

/-! ## BM.6 / BM.23: insertion -/

/-- insert `px` with its current label `d[px]` into the level-`lvl` structure; afterwards, if the
entry was created, `px` moves to the live-key list of level `lvl` -/
def dsIns : Stmt :=
  seq (loadLab "px" DIns.KB "ins.kf")
  (seq (wset "ds.v" (var "px"))
  (seq (wset "ds.lv" (var "lvl"))
  (seq (wset "ds.b" (load "dsl.base" (var "lvl")))
  (seq (wset "di.f0" (var "ds.fresh"))
  (seq insRAM
  (ite (eq (var "ds.fresh") (var "di.f0")) skip
    (seq (wset "kl.v" (var "px"))
    (seq KL.klUnlink
    (seq (wset "kl.s" (add (var "n") (var "lvl"))) KL.klLink)))))))))

theorem insC_eq (T' : ℕ) (g : DGl G s) (D : DStrM G s) (v : Fin G.n) (lam : WLab G s) :
    (BM.insC (dlOps G s) T' g D v lam).1 =
      ⟨(insertNS g.L g.fresh D v lam).1, (insertNS g.L g.fresh D v lam).2.1⟩ ∧
    (BM.insC (dlOps G s) T' g D v lam).2.1 = (insertNS g.L g.fresh D v lam).2.2 ∧
    (BM.insC (dlOps G s) T' g D v lam).2.2 = (DL.insertL g.L g.fresh D v lam).2.2.2 := by
  have h := insertL_eq_insertNS g.L g.fresh D v lam
  have e1 : (insertNS g.L g.fresh D v lam).1 = (DL.insertL g.L g.fresh D v lam).1 := by rw [← h]
  have e2 : (insertNS g.L g.fresh D v lam).2.1 = (DL.insertL g.L g.fresh D v lam).2.1 := by rw [← h]
  have e3 : (insertNS g.L g.fresh D v lam).2.2 = (DL.insertL g.L g.fresh D v lam).2.2.1 := by rw [← h]
  exact ⟨by rw [e1, e2]; rfl, by rw [e3]; rfl, rfl⟩

theorem insRAM_noalloc : NoAlloc insRAM := by
  simp [NoAlloc, insRAM, skipTest, insBody, loadA, LabRAM.cmp, LabRAM.cmpW, BSearch.bsearch, probe,
    insTail, storeA]

/-- the Layer-A facts of a non-skipped insertion at the deepest level, for every level -/
theorem ins_hasKey {L : LiveM G s} {fresh : ℕ} {D : DStrM G s} {v : Fin G.n} {lam : WLab G s}
    (hwf : DB.WF L D) (hfr : DB.FreshOK fresh D) (hB : lam < D.Bd) (hsk : skipIns L v lam = false) :
    (∀ y, DB.HasKey (insertNS L fresh D v lam).1 (insertNS L fresh D v lam).2.2 y ↔
      y = v ∨ DB.HasKey L D y) ∧
    (∀ D' : DStrM G s, DB.FreshOK fresh D' → ∀ y,
      DB.HasKey (insertNS L fresh D v lam).1 D' y ↔ y ≠ v ∧ DB.HasKey L D' y) := by
  have hNS := insertL_eq_insertNS L fresh D v lam
  have e1 : (insertNS L fresh D v lam).1 = (DL.insertL L fresh D v lam).1 := by rw [← hNS]
  have e3 : (insertNS L fresh D v lam).2.2 = (DL.insertL L fresh D v lam).2.2.1 := by rw [← hNS]
  obtain ⟨hv, -, -, -, -, -, hoth⟩ := DL.insertL_spec hwf hfr hB (fun h => absurd (h.symm.trans hsk) (by simp))
  have hL' : (insertNS L fresh D v lam).1 = Function.update L v (some (fresh, lam)) := by
    simp [insertNS, hsk]
  refine ⟨fun y => ?_, fun D' hD' y => ?_⟩
  · rw [e1, e3]
    by_cases hy : y = v
    · subst hy
      have := hv y
      rw [if_pos rfl] at this
      refine iff_of_true ?_ (Or.inl rfl)
      by_contra hk
      rw [← view_eq_none] at hk
      rw [hk] at this; simp at this
    · have := hv y
      rw [if_neg hy] at this
      have hk : DB.HasKey (DL.insertL L fresh D v lam).1 (DL.insertL L fresh D v lam).2.2.1 y ↔
          DB.HasKey L D y := by
        rw [← not_iff_not, ← view_eq_none, ← view_eq_none, this]
      rw [hk]; simp [hy]
  · by_cases hy : y = v
    · subst hy
      simp only [ne_eq, not_true_eq_false, false_and, iff_false]
      rintro ⟨e, he, hk⟩
      obtain ⟨⟨b, hb, heb⟩, hl⟩ := mem_liveVals.mp he
      unfold Entry.IsLive at hl
      rw [hL', hk, Function.update_self] at hl
      simp only [Option.some.injEq, Prod.mk.injEq] at hl
      have := hD' e (mem_allEnts.mpr ⟨b, hb, heb⟩)
      omega
    · rw [e1]
      have := hoth D' hD' y hy
      simp only [ne_eq, hy, not_false_eq_true, true_and]
      rw [← not_iff_not, ← view_eq_none, ← view_eq_none, this]

theorem wf_ins_other {L : LiveM G s} {fresh : ℕ} {D D' : DStrM G s} {v : Fin G.n} {lam : WLab G s}
    (hsk : skipIns L v lam = false) (hwf : DB.WF L D') (hfr : DB.FreshOK fresh D') :
    DB.WF (insertNS L fresh D v lam).1 D' := by
  have hL' : (insertNS L fresh D v lam).1 = Function.update L v (some (fresh, lam)) := by
    simp [insertNS, hsk]
  refine ⟨hwf.1, IntervalOK.mono' (fun b hb e he hl => ?_) hwf.2⟩
  unfold Entry.IsLive at hl ⊢
  rw [hL'] at hl
  by_cases hk : e.key = v
  · rw [hk, Function.update_self] at hl
    simp only [Option.some.injEq, Prod.mk.injEq] at hl
    have := hfr e (mem_allEnts.mpr ⟨b, hb, he⟩)
    omega
  · rwa [Function.update_of_ne hk] at hl

/-- `insRAM` stores only the key `v` into `ent.key` -/
theorem insRAM_keys (st0 : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (hH : GoodHist (s := s) H V) (ecap bcap : ℕ) (L : Live (Fin G.n) (WLab G s)) (fresh : ℕ)
    (Ds : ℕ → DStr (Fin G.n) (WLab G s)) (lo k : ℕ) (hDL : DLRep st0 H V ecap bcap L fresh Ds lo k)
    (hwf : WF L (Ds lo)) (hfr : FreshOK fresh (Ds lo)) (hid : IdsNodup (Ds lo))
    (hLf : ∀ u i a, L u = some (i, a) → i < fresh)
    (v : Fin G.n) (hv : st0.w "ds.v" = v) (hlv : st0.w "ds.lv" = lo) (hb : st0.w "ds.b" = base st0 lo)
    (km : MLabel G) (p : List (Fin G.m)) (hK : Holds st0 DIns.KB km) (hKp : Rep (s := s) H V km p)
    (hfr1 : fresh + 1 < ecap) (hcap : 2 * (Ds lo).blocks.length + ecap + base st0 lo + 4 < st0.cap) :
    Runs realOps insRAM st0 (fun r => ∀ j, r.wa "ent.key" j = st0.wa "ent.key" j ∨
      r.wa "ent.key" j = v) := by
  have hc1 : 1 < st0.cap := by omega
  have hEA := hDL.pool.2.2
  have hLf' : ∀ u i a, L u = some (i, a) → i < ecap := fun u i a h => by have := hLf u i a h; omega
  by_cases hskip : skipIns L v ((toW p : WalkOrd G s) : WLab G s) = true
  · refine (insRAM_skip H V hH L ecap st0 hDL.live hEA hLf' v hv km p hK hKp hc1 hskip).mono ?_
    rintro r ⟨hU, -⟩
    intro j; left; rw [(hU.warr _ (by simp)).1]
  · have hsk : skipIns L v ((toW p : WalkOrd G s) : WLab G s) = false := by simpa using hskip
    have hD0 : DRep st0 H V bcap lo (base st0 lo) (Ds lo) := by simpa using hDL.drep 0 (by omega)
    refine (insRAM_spec H V hH bcap ecap lo (base st0 lo) fresh (Ds lo) L st0 hD0 hDL.barr hDL.live
      hDL.pool hwf hfr hid hLf v hv hlv hb km p hK hKp hfr1 hcap).mono ?_
    rintro r ⟨-, -, -, -, -, hF, -⟩
    obtain ⟨o, -, hFo⟩ := hF hsk
    intro j
    by_cases hj : j = fresh
    · subst hj; right; exact hFo.nkey
    · left; exact hFo.ekey j hj

theorem dsIns_main (P : DPar) (st : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m))
    (g : DGl G s) (Ds : ℕ → DStrM G s) (l : ℕ) (d : Labels G s) (c0 : ℕ) (v : Fin G.n) (T' : ℕ)
    (hD : DRI P st H g Ds l) (hL : LabAt st d H c0) (hl : st.w "lvl" = l) (hn : st.w "n" = G.n)
    (hpx : st.w "px" = v) (hB : d v < (Ds l).Bd)
    (hroom : st.w "ds.fresh" + st.w "blk.fresh" +
      ((BM.insC (dlOps G s) T' g (Ds l) v (d v)).2.2 + 1) ≤ P.ucap) :
    Runs realOps dsIns st (fun r =>
      DRI P r H (BM.insC (dlOps G s) T' g (Ds l) v (d v)).1
        (Function.update Ds l (BM.insC (dlOps G s) T' g (Ds l) v (d v)).2.1) l ∧
      r.cost ≤ st.cost + 40 * ((BM.insC (dlOps G s) T' g (Ds l) v (d v)).2.2 + 1) ∧
      r.w "ds.fresh" + r.w "blk.fresh" ≤ st.w "ds.fresh" + st.w "blk.fresh" + 1) := by
  obtain ⟨e1, e2, e3⟩ := insC_eq T' g (Ds l) v (d v)
  rw [e1, e2, e3]
  rw [e3] at hroom
  have hlt := hD.lo_le
  have hLn := hD.lens
  have hc := hLn.cap
  obtain ⟨K, hK, hKk⟩ := hD.kl
  have hdl := hD.dl
  have hvt : d v ≠ ⊤ := _root_.ne_top_of_lt hB
  obtain ⟨p, hp⟩ : ∃ p : List (Fin G.m), d v = ((toW p : WalkOrd G s) : WLab G s) := by
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hvt; exact ⟨q, hq.symm⟩
  -- 1. load the label
  refine runs_seq ((wp_sound _ _ _ (loadLab_wp "px" DIns.KB "ins.kf" ⟨by decide, by decide⟩ st v
    hL.lens hpx)).mono (fun s1 hs1 => ?_))
  obtain ⟨hLd, hU1, hc1⟩ := hs1
  have hKh : Holds s1 DIns.KB ((tabOf st).lab v) := hLd.holds hL.rep hvt
  have hKr : Rep (s := s) H (vc st) ((tabOf st).lab v) p := hL.rep.rep v p hp
  have hw1 : ∀ x, x ∉ "ins.kf" :: DIns.KB.ws → s1.w x = st.w x := hU1.wreg
  have hwa1 : s1.wa = st.wa := by funext a; exact (hU1.warr a (by simp)).1
  have hwl1 : s1.wlen = st.wlen := by funext a; exact (hU1.warr a (by simp)).2
  have hcap1 : s1.cap = st.cap := hU1.cap
  have hbl := hdl.basel
  have hfr0 : st.w "ds.fresh" = g.fresh := hdl.pool.1
  -- 2. the insertion registers
  refine runs_seq (runs_wset (a := v) (by
    simp only [evalW]; rw [hw1 _ (by decide), hpx]) ?_)
  set s2 := (s1.setW "ds.v" v).charge 1 with hs2
  refine runs_seq (runs_wset (a := l) (by
    simp only [evalW, hs2, State.charge_w, State.setW_w]; rw [if_neg (by decide), hw1 _ (by decide), hl])
    ?_)
  set s3 := (s2.setW "ds.lv" l).charge 1 with hs3
  have hs3l : s3.w "lvl" = l := by
    simp only [hs3, hs2, State.charge_w, State.setW_w]; rw [if_neg (by decide), if_neg (by decide),
      hw1 _ (by decide), hl]
  have hl3 : l < s3.wlen "dsl.base" := by simp [hs3, hs2, hwl1]; omega
  refine runs_seq (runs_wset (a := base st l) (by
    simp [evalW, hs3l, hl3]; simp [hs3, hs2, hwa1, base]) ?_)
  set s4 := (s3.setW "ds.b" (base st l)).charge 1 with hs4
  refine runs_seq (runs_wset (a := g.fresh) (by
    simp only [evalW, hs4, hs3, hs2, State.charge_w, State.setW_w]
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), hw1 _ (by decide), hfr0]) ?_)
  set s5 := (s4.setW "di.f0" g.fresh).charge 1 with hs5
  have hU25 : Unchanged s1 s5 [] [] ["ds.v", "ds.lv", "ds.b", "di.f0"] [] := by
    rw [hs5, unch_charge, unch_setW (by simp), hs4, unch_charge, unch_setW (by simp), hs3,
      unch_charge, unch_setW (by simp), hs2, unch_charge, unch_setW (by simp)]
    exact Unchanged.refl _ _ _ _ _
  have hU15 := hU1.comp hU25
  have hK5 : Holds s5 DIns.KB ((tabOf st).lab v) :=
    hKh.of_unchanged hU25 (by decide) (by simp)
  have hdl5 : DLRep s5 H (vc st) P.ecap P.bcap g.L g.fresh Ds l (P.top - l) :=
    DLRep.of_unch hdl hU15 (by simp) (by simp) (by decide)
  have hs5wa : s5.wa = st.wa := by simp [hs5, hs4, hs3, hs2, hwa1]
  have hs5wl : s5.wlen = st.wlen := by simp [hs5, hs4, hs3, hs2, hwl1]
  have hs5c : s5.cap = st.cap := by simp [hs5, hs4, hs3, hs2, hcap1]
  have hbase5 : base s5 l = base st l := by simp [base, hs5wa]
  have hsl := DLRep.stack_le hdl5
  have hbf5 : s5.w "blk.fresh" = st.w "blk.fresh" := by
    simp only [hs5, hs4, hs3, hs2, State.charge_w, State.setW_w]
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
      hw1 _ (by decide)]
  have hfr1 : g.fresh + 1 < P.ecap := by have := hD.use; have := hLn.ue; omega
  have hcap5 : 2 * (Ds l).blocks.length + P.ecap + base s5 l + 4 < s5.cap := by
    rw [hs5c]; have := hD.use; have := hLn.ub; omega
  -- 3. the insertion
  refine runs_seq ((Runs.sframe (runs_and (insertDL s5 H (vc st) hL.rep.hist P.ecap P.bcap g.L g.fresh Ds l
    (P.top - l) hdl5 (hD.wf l le_rfl hlt) (hD.fr l le_rfl hlt) (DLRep.ids_lo hdl5) hD.lf
    (fam_fresh (fun j h1 h2 => hD.fr j h1 (by omega))) v
    (by simp [hs5, hs4, hs3, hs2]) (by simp [hs5, hs4, hs3]) (by rw [hbase5]; simp [hs5, hs4])
    _ p hK5 hKr hfr1 hcap5) (insRAM_keys s5 H (vc st) hL.rep.hist P.ecap P.bcap g.L g.fresh Ds l
    (P.top - l) hdl5 (hD.wf l le_rfl hlt) (hD.fr l le_rfl hlt) (DLRep.ids_lo hdl5) hD.lf v
    (by simp [hs5, hs4, hs3, hs2]) (by simp [hs5, hs4, hs3]) (by rw [hbase5]; simp [hs5, hs4])
    _ p hK5 hKr hfr1 hcap5)) insRAM_noalloc).mono (fun s6 hs6 => ?_))
  obtain ⟨⟨⟨hDL6, hc6⟩, hkey6⟩, hU6, hwl6, hvl6⟩ := hs6
  have hkeys6 : ∀ i, i < P.ecap → s6.wa "ent.key" i < G.n := by
    intro i hi
    rcases hkey6 i with h | h
    · rw [h, hs5wa]; exact hD.keys i hi
    · rw [h]; exact v.isLt
  have hprocs6 : s6.procs = st.procs := by rw [hU6.procs, hU15.procs]
  rw [← hp] at hDL6 hc6
  have hU6w : ∀ x, x ∉ sWR insRAM → s6.w x = s5.w x := fun x hx => hU6.wreg x hx
  have hf6 : s6.w "ds.fresh" = (insertNS g.L g.fresh (Ds l) v (d v)).2.1 := hDL6.pool.1
  have hf06 : s6.w "di.f0" = g.fresh := by rw [hU6w _ (by decide)]; simp [hs5]
  have hc6' : s6.cap = st.cap := by rw [hU6.cap, hs5c]
  have hs6wl : s6.wlen = st.wlen := by rw [hwl6, hs5wl]
  have hs6vl : s6.vlen = st.vlen := by rw [hvl6]; simp [hs5, hs4, hs3, hs2]; funext a; exact (hU1.varr a (by simp)).2
  have hU6a : ∀ a, a ∉ sWA insRAM → s6.wa a = st.wa a := fun a ha => by rw [(hU6.warr a ha).1, hs5wa]
  have hU6v : ∀ a, a ∉ sVA insRAM → s6.va a = st.va a := fun a ha => by
    rw [(hU6.varr a ha).1]; simp [hs5, hs4, hs3, hs2]; exact (hU1.varr a (by simp)).1
  have hbf6 : s6.w "blk.fresh" = st.w "blk.fresh" := by rw [hU6w _ (by decide), hbf5]
  have hpx6 : s6.w "px" = v := by
    rw [hU6w _ (by decide)]
    simp only [hs5, hs4, hs3, hs2, State.charge_w, State.setW_w]
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
      hw1 _ (by decide), hpx]
  have hl6 : s6.w "lvl" = l := by
    rw [hU6w _ (by decide)]
    simp only [hs5, hs4, State.charge_w, State.setW_w]
    rw [if_neg (by decide), if_neg (by decide)]; exact hs3l
  have hn6 : s6.w "n" = G.n := by
    rw [hU6w _ (by decide)]
    simp only [hs5, hs4, hs3, hs2, State.charge_w, State.setW_w]
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
      hw1 _ (by decide), hn]
  have hvc6 : vc (G := G) s6 = vc st := by funext u; unfold vc; rw [hU6a _ (by decide)]
  have hbd6 : ∀ j, l ≤ j → j ≤ P.top → BdHolds s6 j H (vc st) (Ds j).Bd := fun j h1 h2 =>
    (hD.bd j h1 h2).of_eq (by rw [hU6a _ (by decide)]) (by rw [hU6v _ (by decide)])
      (by rw [hU6a _ (by decide)]) (by rw [hU6a _ (by decide)]) (by rw [hU6a _ (by decide)])
      (by rw [hU6a _ (by decide)])
  have hmv6 : ∀ j, l ≤ j → j ≤ P.top → s6.wa "dsl.M" j = (Ds j).M := fun j h1 h2 => by
    rw [hU6a _ (by decide)]; exact hD.mv j h1 h2
  have hK6 : KL.LL (s6.wa "lk.n") (s6.wa "lk.p") G.n l P.top K := by
    rw [hU6a _ (by decide), hU6a _ (by decide)]; exact hK
  have hc1' : 1 < s6.cap := by omega
  by_cases hsk : skipIns g.L v (d v) = true
  · -- the entry is not created: nothing else changes
    have hNS : insertNS g.L g.fresh (Ds l) v (d v) = (g.L, g.fresh, Ds l) := by simp [insertNS, hsk]
    refine runs_ite_true (x := 1) (by simp [evalW, hf6, hf06, hNS, fit, hc1']) one_ne_zero
      (runs_skip ?_)
    rw [hNS] at hDL6 ⊢
    simp only [Function.update_eq_self] at hDL6 ⊢
    set r := (s6.charge 1).charge 1 with hr
    have hvcr : vc (G := G) r = vc st := by rw [← hvc6]; rfl
    have hUr : Unchanged s6 r [] [] [] [] := by
      rw [hr, unch_charge, unch_charge]; exact Unchanged.refl _ _ _ _ _
    refine ⟨⟨hlt, by rw [hvcr]; exact DLRep.of_unch hDL6 hUr (by simp) (by simp) (by simp),
      fun j h1 h2 => by rw [hvcr]; exact (hbd6 j h1 h2).of_eq rfl rfl rfl rfl rfl rfl,
      fun j h1 h2 => hmv6 j h1 h2, ⟨K, hK6, hKk⟩, hD.wf, hD.fr, hD.lf, ?_,
      hLn.of_len hs6wl hs6vl hc6', hD.hib, by rw [show r.procs = s6.procs from rfl, hprocs6]; exact hD.procs,
      hkeys6, fun j h1 h2 => by rw [show r.cap = s6.cap from rfl, hc6']; exact hD.mc j h1 h2⟩, ?_⟩
    · show s6.w "ds.fresh" + s6.w "blk.fresh" ≤ P.ucap
      rw [hf6, hNS, hbf6, ← hfr0]; exact hD.use
    · refine ⟨?_, by
        show s6.w "ds.fresh" + s6.w "blk.fresh" ≤ st.w "ds.fresh" + st.w "blk.fresh" + 1
        have hdf6 : s6.w "ds.fresh" = st.w "ds.fresh" := by rw [hf6, hNS]; exact hfr0.symm
        rw [hdf6, hbf6]; omega⟩
      have hi : (DL.insertL g.L g.fresh (Ds l) v (d v)).2.2.2 = 2 := by simp [DL.insertL, hsk]
      rw [hi]
      simp only [hr, State.charge_cost]
      rw [if_pos hsk] at hc6
      have : s5.cost = st.cost + 10 := by simp [hs5, hs4, hs3, hs2, hc1]
      omega
  · have hsk' : skipIns g.L v (d v) = false := by simpa using hsk
    have hNS1 : (insertNS g.L g.fresh (Ds l) v (d v)).2.1 = g.fresh + 1 := by simp [insertNS, hsk']
    have hNSL : (insertNS g.L g.fresh (Ds l) v (d v)).1 = Function.update g.L v (some (g.fresh, d v)) := by
      simp [insertNS, hsk']
    refine runs_ite_false (by simp [evalW, hf6, hf06, hNS1, fit, show 0 < s6.cap by omega]) ?_
    set q0 := s6.charge 1 with hq0
    refine runs_seq (runs_wset (a := v) (by simp [evalW, hq0, hpx6]) ?_)
    set q1 := (q0.setW "kl.v" v).charge 1 with hq1
    have hK1 : KL.LL (q1.wa "lk.n") (q1.wa "lk.p") G.n l P.top K := by simpa [hq1, hq0] using hK6
    have hq1wl : q1.wlen = st.wlen := by simp [hq1, hq0, hs6wl]
    refine runs_seq ((KL.klUnlink_LL (ops := realOps) q1 hK1 (by simp [hq1]) v.isLt
      (by rw [hq1wl]; exact hLn.lkn) (by rw [hq1wl]; exact hLn.lkp)).mono (fun q2 hq2 => ?_))
    obtain ⟨hL2, hU2, hwl2, hc2⟩ := hq2
    have hq2l : q2.w "lvl" = l := by rw [hU2.wreg _ (by decide)]; simp [hq1, hq0, hl6]
    have hq2n : q2.w "n" = G.n := by rw [hU2.wreg _ (by decide)]; simp [hq1, hq0, hn6]
    have hq2v : q2.w "kl.v" = v := by rw [hU2.wreg _ (by decide)]; simp [hq1]
    have hq2c : q2.cap = st.cap := by rw [hU2.cap]; simp [hq1, hq0, hc6']
    refine runs_seq (runs_wset (a := G.n + l) (by
      simp [evalW, hq2l, hq2n, fit, hq2c, show G.n + l < st.cap by omega]) ?_)
    set q3 := (q2.setW "kl.s" (G.n + l)).charge 1 with hq3
    have hK3 : KL.LL (q3.wa "lk.n") (q3.wa "lk.p") G.n l P.top (fun j => (K j).erase v) := by
      simpa [hq3] using hL2
    have hq3wl : q3.wlen = st.wlen := by simp [hq3, hwl2, hq1wl]
    have hfree : ∀ i, l ≤ i → i ≤ P.top → (v : ℕ) ∉ (fun j => (K j).erase (v : ℕ)) i :=
      fun i h1 h2 => (List.nodup_cons.mp (hK.cl i h1 h2).2).2.not_mem_erase
    refine (KL.klLink_LL (ops := realOps) q3 hK3 (by simp [hq3, hq2v]) v.isLt hfree (by simp [hq3])
      le_rfl hlt (by rw [hq3wl]; exact hLn.lkn) (by rw [hq3wl]; exact hLn.lkp)).mono ?_
    rintro r ⟨hL4, hU4, hwl4, hc4⟩
    -- the frame from `s6` to `r`
    have hUq0 : Unchanged s6 q1 [] [] ["kl.v"] [] := by
      rw [hq1, unch_charge, unch_setW (by simp), hq0, unch_charge]; exact Unchanged.refl _ _ _ _ _
    have hUq3 : Unchanged q2 q3 [] [] ["kl.s"] [] := by
      rw [hq3, unch_charge, unch_setW (by simp)]; exact Unchanged.refl _ _ _ _ _
    have hUr := ((hUq0.comp hU2).comp hUq3).comp hU4
    have hra : ∀ a, a ≠ "lk.n" → a ≠ "lk.p" → r.wa a = s6.wa a := fun a h1 h2 =>
      (hUr.warr a (by simp [h1, h2])).1
    have hrva : r.va = s6.va := by funext a; exact (hUr.varr a (by simp)).1
    have hrw : ∀ x ∈ drWR, r.w x = s6.w x := fun x hx =>
      hUr.wreg x (by simp [drWR] at hx; rcases hx with rfl | rfl <;> decide)
    have hvcr : vc (G := G) r = vc st := by
      funext u; unfold vc; rw [hra _ (by decide) (by decide), hU6a _ (by decide)]
    obtain ⟨hself, hother⟩ := ins_hasKey (hD.wf l le_rfl hlt) (hD.fr l le_rfl hlt) hB hsk'
    obtain ⟨-, hwfI, hfrI, -, -, -, -⟩ := DL.insertL_spec (hD.wf l le_rfl hlt) (hD.fr l le_rfl hlt) hB
      (fun h => absurd (h.symm.trans hsk') (by simp))
    have hNSe := insertL_eq_insertNS g.L g.fresh (Ds l) v (d v)
    have hwfNS : DB.WF (insertNS g.L g.fresh (Ds l) v (d v)).1 (insertNS g.L g.fresh (Ds l) v (d v)).2.2 := by
      rw [← hNSe]; exact hwfI
    have hfrNS : DB.FreshOK (insertNS g.L g.fresh (Ds l) v (d v)).2.1
        (insertNS g.L g.fresh (Ds l) v (d v)).2.2 := by rw [← hNSe]; exact hfrI
    refine ⟨⟨hlt, ?_, fun j h1 h2 => ?_, fun j h1 h2 => ?_,
      ⟨_, hL4, fun j h1 h2 w => ?_⟩, fun j h1 h2 => ?_, fun j h1 h2 => ?_, ?_, ?_,
      hLn.of_len (by rw [hwl4, hq3wl]) (by
        funext a; rw [(hUr.varr a (by simp)).2]; exact congrFun hs6vl a) (by
        rw [hU4.cap]; simp [hq3, hq2c]), fun j hj => by
          rw [Function.update_of_ne (show j ≠ l by omega)]; exact hD.hib j hj,
      by rw [hUr.procs, hprocs6]; exact hD.procs,
      fun i hi => by rw [hra _ (by decide) (by decide)]; exact hkeys6 i hi,
      fun j h1 h2 => by
        rw [hUr.cap, hc6']
        by_cases hjl : j = l
        · subst hjl; rw [Function.update_self]
          have hM : (insertNS g.L g.fresh (Ds j) v (d v)).2.2.M = (Ds j).M := by simp [insertNS, hsk']
          rw [hM]; exact hD.mc j h1 h2
        · rw [Function.update_of_ne hjl]; exact hD.mc j h1 h2⟩, ?_⟩
    · rw [hvcr]; exact DLRep.of_unch hDL6 hUr (by decide) (by decide) (by decide)
    · rw [hvcr]
      by_cases hjl : j = l
      · subst hjl
        rw [Function.update_self]
        have hBd : (insertNS g.L g.fresh (Ds j) v (d v)).2.2.Bd = (Ds j).Bd := by
          simp [insertNS, hsk']
        rw [hBd]
        exact (hbd6 j h1 h2).of_eq (by rw [hra _ (by decide) (by decide)]) (by rw [hrva])
          (by rw [hra _ (by decide) (by decide)]) (by rw [hra _ (by decide) (by decide)])
          (by rw [hra _ (by decide) (by decide)]) (by rw [hra _ (by decide) (by decide)])
      · rw [Function.update_of_ne hjl]
        exact (hbd6 j h1 h2).of_eq (by rw [hra _ (by decide) (by decide)]) (by rw [hrva])
          (by rw [hra _ (by decide) (by decide)]) (by rw [hra _ (by decide) (by decide)])
          (by rw [hra _ (by decide) (by decide)]) (by rw [hra _ (by decide) (by decide)])
    · rw [hra _ (by decide) (by decide), hmv6 j h1 h2]
      by_cases hjl : j = l
      · subst hjl; rw [Function.update_self]; simp [insertNS, hsk']
      · rw [Function.update_of_ne hjl]
    · have hvw : ((w : ℕ) = (v : ℕ)) ↔ w = v := Fin.val_inj
      by_cases hjl : j = l
      · subst hjl
        rw [Function.update_self, Function.update_self, hself w]
        have hnd : (K j).Nodup := (List.nodup_cons.mp (hK.cl j h1 h2).2).2
        simp only [List.mem_cons, hnd.mem_erase_iff, hKk j h1 h2 w, hvw]
        tauto
      · rw [Function.update_of_ne hjl, Function.update_of_ne hjl, hother (Ds j) (hD.fr j h1 h2) w]
        have hnd : (K j).Nodup := (List.nodup_cons.mp (hK.cl j h1 h2).2).2
        rw [hnd.mem_erase_iff, hKk j h1 h2 w]
        simp only [ne_eq, hvw]
        first | done | tauto
    · by_cases hjl : j = l
      · subst hjl; rw [Function.update_self]; exact hwfNS
      · rw [Function.update_of_ne hjl]; exact wf_ins_other hsk' (hD.wf j h1 h2) (hD.fr j h1 h2)
    · by_cases hjl : j = l
      · subst hjl; rw [Function.update_self]; exact hfrNS
      · rw [Function.update_of_ne hjl]
        show DB.FreshOK (insertNS g.L g.fresh (Ds l) v (d v)).2.1 (Ds j)
        rw [hNS1]
        intro x hx; have := hD.fr j h1 h2 x hx; omega
    · show ∀ u i a, (insertNS g.L g.fresh (Ds l) v (d v)).1 u = some (i, a) →
        i < (insertNS g.L g.fresh (Ds l) v (d v)).2.1
      intro u i a hu
      rw [hNSL] at hu; rw [hNS1]
      by_cases huv : u = v
      · subst huv; rw [Function.update_self] at hu
        simp only [Option.some.injEq, Prod.mk.injEq] at hu; omega
      · rw [Function.update_of_ne huv] at hu; have := hD.lf u i a hu; omega
    · show r.w "ds.fresh" + r.w "blk.fresh" ≤ P.ucap
      rw [hrw _ (by simp [drWR]), hrw _ (by simp [drWR]), hf6, hNS1, hbf6, ← hfr0]
      omega
    · refine ⟨?_, by
        rw [hrw _ (by simp [drWR]), hrw _ (by simp [drWR]), hf6, hNS1, hbf6, ← hfr0]; omega⟩
      have hi : (DL.insertL g.L g.fresh (Ds l) v (d v)).2.2.2 = DL.bsCost (Ds l).blocks.length + 3 := by
        simp [DL.insertL, hsk']
      rw [hi]
      rw [if_neg (by simpa using hsk)] at hc6
      have hlog : Nat.log 2 ((Ds l).blocks.length - 1) ≤ Nat.log 2 (Ds l).blocks.length :=
        Nat.log_mono_right (Nat.sub_le _ _)
      have h5 : s5.cost = st.cost + 10 := by simp [hs5, hs4, hs3, hs2, hc1]
      have hr : r.cost = s6.cost + 14 := by
        rw [hc4]; simp only [hq3, State.charge_cost, State.setW_cost]; rw [hc2]; simp [hq1, hq0]
      unfold DL.bsCost
      omega

theorem dsIns_noalloc : NoAlloc dsIns := by
  simp [NoAlloc, dsIns, loadLab, insRAM, skipTest, insBody, loadA, LabRAM.cmp, LabRAM.cmpW,
    BSearch.bsearch, probe, insTail, storeA, KL.klUnlink, KL.klLink]

theorem dsIns_spec (P : DPar) (st : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m))
    (g : DGl G s) (Ds : ℕ → DStrM G s) (l : ℕ) (d : Labels G s) (c0 : ℕ) (v : Fin G.n) (T' : ℕ)
    (hD : DRI P st H g Ds l) (hL : LabAt st d H c0) (hl : st.w "lvl" = l) (hn : st.w "n" = G.n)
    (hpx : st.w "px" = v) (hB : d v < (Ds l).Bd)
    (hroom : st.w "ds.fresh" + st.w "blk.fresh" +
      ((BM.insC (dlOps G s) T' g (Ds l) v (d v)).2.2 + 1) ≤ P.ucap) :
    Runs realOps dsIns st (fun r =>
      DRI P r H (BM.insC (dlOps G s) T' g (Ds l) v (d v)).1
        (Function.update Ds l (BM.insC (dlOps G s) T' g (Ds l) v (d v)).2.1) l ∧
      Unchanged st r (sWA dsIns) (sVA dsIns) (sWR dsIns) (sVR dsIns) ∧ r.wlen = st.wlen ∧
      r.vlen = st.vlen ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + 40 * ((BM.insC (dlOps G s) T' g (Ds l) v (d v)).2.2 + 1) ∧
      r.w "ds.fresh" + r.w "blk.fresh" ≤ st.w "ds.fresh" + st.w "blk.fresh" + 1) :=
  (Runs.sframe (Runs.cost_mono (dsIns_main P st H g Ds l d c0 v T' hD hL hl hn hpx hB hroom))
    dsIns_noalloc).mono (fun _ ⟨⟨⟨h1, h2, h4⟩, h3⟩, hU, hwl, hvl⟩ => ⟨h1, hU, hwl, hvl, h3, h2, h4⟩)

/-- every level at or above `lo` has at most `ucap` blocks -/
theorem DRI.nb_le {P : DPar} {st : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {g : DGl G s}
    {Ds : ℕ → DStrM G s} {lo : ℕ} (h : DRI P st H g Ds lo) :
    ∀ j, lo ≤ j → (Ds j).blocks.length ≤ P.ucap := by
  intro j hj
  by_cases hjt : P.top < j
  · exact h.hib j hjt
  · have hsl := DLRep.stack_le h.dl
    have hu := h.use
    have hanti := base_antitone h.dl.chain
    by_cases hjl : j = lo
    · subst hjl; omega
    · -- `|Ds j| ≤ base (j-1) ≤ base lo`
      have hi : j - 1 - lo < P.top - lo := by omega
      have hc := h.dl.chain (j - 1 - lo) hi
      rw [show lo + (j - 1 - lo) + 1 = j by omega] at hc
      have ha := hanti 0 (j - 1 - lo) (by omega) (by omega)
      simp only [add_zero] at ha
      omega

/-! ## The `DLayer` of the spine -/

section inst

open Frontier.CHD.RamSpine

/-- the merge contract on `DRI` (the shape of `DLayer.merge_spec`) -/
def MergeOK (P : DPar) (merge : Stmt) (wa va wr vr : List String) (K : ℕ) : Prop :=
  ∀ (st : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (g : DGl G s) (Ds : ℕ → DStrM G s)
    (l : ℕ), 1 ≤ l → l ≤ P.top → DRI P st H g Ds (l - 1) → st.w "lvl" = l → st.w "n" = G.n →
    GoodHist (s := s) H (vc st) →
    (∀ e ∈ DB.liveVals g.L (Ds l).blocks, (Ds (l - 1)).Bd ≤ e.val) →
    (∀ b ∈ (Ds l).blocks.tail, (((Ds (l - 1)).Bd : WLab G s) : WithBot (WLab G s)) < b.sep) →
    (Ds (l - 1)).Bd ≤ (Ds l).Bd →
    Runs realOps merge st (fun r =>
      DRI P r H g (Function.update Ds l (DB.merge 1 (Ds l) (Ds (l - 1))).1) l ∧
      Unchanged st r wa va wr vr ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + K * ((DB.merge 1 (Ds l) (Ds (l - 1))).2 + 1) ∧
      r.w "ds.fresh" + r.w "blk.fresh" = st.w "ds.fresh" + st.w "blk.fresh")

/-- the pull contract on `DRI` (the shape of `DLayer.pull_spec`) -/
def PullOK (P : DPar) (T : ℕ → ℕ) (pull : Stmt) (wa va wr vr : List String) (K : ℕ) : Prop :=
  ∀ (st : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (g : DGl G s) (Ds : ℕ → DStrM G s)
    (l : ℕ), 1 ≤ l → DRI P st H g Ds l → st.w "lvl" = l → st.w "n" = G.n →
    RowRep st "S" "S.len" G.n (l - 1) [] → SlotLens st (slotBi l) →
    GoodHist (s := s) H (vc st) →
    st.w "ds.fresh" + st.w "blk.fresh" + ((BM.pullC (dlOps G s) (T l) g (Ds l)).2.2.2.2 + 1) ≤
      P.ucap →
    Runs realOps pull st (fun r =>
      DRI P r H (BM.pullC (dlOps G s) (T l) g (Ds l)).2.2.1
        (Function.update Ds l (BM.pullC (dlOps G s) (T l) g (Ds l)).2.2.2.1) l ∧
      RowRep r "S" "S.len" G.n (l - 1) ((BM.pullC (dlOps G s) (T l) g (Ds l)).1.map Fin.val) ∧
      SlotHolds r (slotBi l) H (vc r) (BM.pullC (dlOps G s) (T l) g (Ds l)).2.1 ∧
      Unchanged st r (wa ++ ["S", "S.len"] ++ slotW) (va ++ ["sl.l"]) wr vr ∧
      (∀ i, (i < (l - 1) * G.n ∨ l * G.n ≤ i) → r.wa "S" i = st.wa "S" i) ∧
      (∀ j, j ≠ l - 1 → r.wa "S.len" j = st.wa "S.len" j) ∧
      (∀ i, i ≠ slotBi l → r.va "sl.l" i = st.va "sl.l" i ∧ ∀ a ∈ slotW, r.wa a i = st.wa a i) ∧
      r.wlen = st.wlen ∧ r.vlen = st.vlen ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + K * ((BM.pullC (dlOps G s) (T l) g (Ds l)).2.2.2.2 + 1) ∧
      r.w "ds.fresh" + r.w "blk.fresh" ≤
        st.w "ds.fresh" + st.w "blk.fresh" + ((BM.pullC (dlOps G s) (T l) g (Ds l)).2.2.2.2 + 1))

/-- the name lists of the D layer: everything the representation reads and the four ops write -/
structure DNames (wa va wr vr : List String) : Prop where
  rwa : ∀ a ∈ drWA, a ∈ wa
  rva : ∀ a ∈ drVA, a ∈ va
  rwr : ∀ a ∈ drWR, a ∈ wr
  ins : (∀ a ∈ sWA dsIns, a ∈ wa) ∧ (∀ a ∈ sVA dsIns, a ∈ va) ∧ (∀ a ∈ sWR dsIns, a ∈ wr) ∧
    (∀ a ∈ sVR dsIns, a ∈ vr)
  new : (∀ a ∈ sWA dsNew, a ∈ wa) ∧ (∀ a ∈ sVA dsNew, a ∈ va) ∧ (∀ a ∈ sWR dsNew, a ∈ wr) ∧
    (∀ a ∈ sVR dsNew, a ∈ vr)
  del : (∀ a ∈ sWA dsDelB, a ∈ wa) ∧ (∀ a ∈ sVA dsDelB, a ∈ va) ∧ (∀ a ∈ sWR dsDelB, a ∈ wr) ∧
    (∀ a ∈ sVR dsDelB, a ∈ vr)
  emp : (∀ a ∈ sWA dsEmpty, a ∈ wa) ∧ (∀ a ∈ sVA dsEmpty, a ∈ va) ∧
    (∀ a ∈ sWR dsEmpty, a ∈ wr ++ ["sp.em"]) ∧ (∀ a ∈ sVR dsEmpty, a ∈ vr)
  wa_ok : ∀ a ∈ wa, a ∉ spArrs
  va_ok : ∀ a ∈ va, a ∉ "sl.l" :: "gW" :: labV
  wr_ok : ∀ a ∈ wr, a ∉ spRegs
  vr_ok : ∀ a ∈ vr, a ∉ spVRegs

theorem unch_widen {st r : State ℝ≥0} {wa va wr vr wa' va' wr' vr' : List String}
    (h : Unchanged st r wa va wr vr) (h1 : ∀ a ∈ wa, a ∈ wa') (h2 : ∀ a ∈ va, a ∈ va')
    (h3 : ∀ a ∈ wr, a ∈ wr') (h4 : ∀ a ∈ vr, a ∈ vr') : Unchanged st r wa' va' wr' vr' :=
  h.mono h1 h2 h3 h4

/-- **the D layer of the spine**, from the four proved operations of this file and a merge and a
pull satisfying their contracts -/
def mkDL (P : DPar) (T : ℕ → ℕ) (wa va wr vr : List String) (hN : DNames wa va wr vr)
    (K : ℕ) (hK : 40 ≤ K) (merge pull : Stmt) (hM : MergeOK (G := G) (s := s) P merge wa va wr vr K)
    (hP : PullOK (G := G) (s := s) P T pull wa va wr vr K) : DLayer G s T where
  DR := DRI P
  dWA := wa
  dVA := va
  dWR := wr
  dVR := vr
  frame := fun _ _ _ _ _ _ _ _ _ _ _ h hu hw hv hr hE =>
    h.frame hu (fun a ha => hw a (hN.rwa a ha)) (fun a ha => hv a (hN.rva a ha))
      (fun a ha => hr a (hN.rwr a ha)) hE
  congr := fun _ _ _ _ _ _ hD h => h.congr hD
  dWA_ok := hN.wa_ok
  dVA_ok := hN.va_ok
  dWR_ok := hN.wr_ok
  dVR_ok := hN.vr_ok
  NB := P.ucap
  nb_le := fun _ _ _ _ _ h => h.nb_le
  LT := P.top
  use := fun st => st.w "ds.fresh" + st.w "blk.fresh"
  ucap := P.ucap
  use_frame := fun st r _ _ _ _ hu hr => by
    show r.w "ds.fresh" + r.w "blk.fresh" = st.w "ds.fresh" + st.w "blk.fresh"
    rw [hu.wreg _ (hr _ (hN.rwr _ (by simp [drWR]))), hu.wreg _ (hr _ (hN.rwr _ (by simp [drWR])))]
  K := K
  pull := pull
  pull_spec := fun st H g Ds l h1 hD hl hn hS hSL hH hu => hP st H g Ds l h1 hD hl hn hS hSL hH hu
  merge := merge
  merge_spec := fun st H g Ds l h1 hlt hD hl hn hH hm1 hm2 hm0 =>
    (hM st H g Ds l h1 hlt hD hl hn hH hm1 hm2 hm0).mono
      (fun _ ⟨a1, a2, a3, a4, a5, a6, a7⟩ => ⟨a1, a2, a3, a4, a5, a6, a7⟩)
  delB := dsDelB
  delB_spec := fun st H g Ds l lU h1 hD hl hn hU =>
    (dsDelB_spec (ops := realOps) P st H g Ds l lU h1 hD hl hn hU).mono
      (fun r ⟨a1, a2, a3, a4, a5, a6⟩ => ⟨a1, unch_widen a2 hN.del.1 hN.del.2.1 hN.del.2.2.1 hN.del.2.2.2,
        a3, a4, a5, by
          have e : (BM.delC g lU).2 = lU.length + 1 := rfl
          rw [e]
          have := Nat.mul_le_mul_right (lU.length + 1 + lU.length + 1) hK
          omega,
        by
          show r.w "ds.fresh" + r.w "blk.fresh" = st.w "ds.fresh" + st.w "blk.fresh"
          rw [a2.wreg _ (by decide), a2.wreg _ (by decide)]⟩)
  ins := dsIns
  ins_spec := fun st H g Ds l d c0 v hD hL hl hn hpx hB hu =>
    (dsIns_spec P st H g Ds l d c0 v (T l) hD hL hl hn hpx hB hu).mono
      (fun r ⟨a1, a2, a3, a4, a5, a6, a7⟩ => ⟨a1, unch_widen a2 hN.ins.1 hN.ins.2.1 hN.ins.2.2.1 hN.ins.2.2.2,
        a3, a4, a5, le_trans a6 (Nat.add_le_add_left (Nat.mul_le_mul_right _ hK) _), by
          show r.w "ds.fresh" + r.w "blk.fresh" ≤ st.w "ds.fresh" + st.w "blk.fresh" + _
          omega⟩)
  new := dsNew
  new_spec := fun st H g Ds l M Bd hD hl hn hM' hML hMc hSB hSL hu =>
    (dsNew_spec (ops := realOps) P st H g Ds l M Bd hD hl hn hM' hML hSB hSL hu hMc).mono
      (fun r ⟨a1, a2, a3, a4, a5, a6, a7⟩ => ⟨a1, unch_widen a2 hN.new.1 hN.new.2.1 hN.new.2.2.1 hN.new.2.2.2,
        a3, a4, a5, by omega, by
          show r.w "ds.fresh" + r.w "blk.fresh" ≤ st.w "ds.fresh" + st.w "blk.fresh" + 1
          omega⟩)
  empty := dsEmpty
  empty_spec := fun st H g Ds l hD hl hn =>
    (dsEmpty_spec (ops := realOps) P st H g Ds l hD hl hn).mono
      (fun r ⟨a1, a2, a3, a4, a5, a6, a7⟩ => ⟨a1, a2,
        unch_widen a3 (by simp) (by simp)
          (fun a ha => hN.emp.2.2.1 a (by simpa [dsEmpty, KL.klTest, sWR] using ha)) (by simp),
        a4, a5, a6, by omega, by
          show r.w "ds.fresh" + r.w "blk.fresh" = st.w "ds.fresh" + st.w "blk.fresh"
          rw [a3.wreg _ (by decide), a3.wreg _ (by decide)]⟩)

/-- the word registers of the four proved operations and of the representation -/
def wrD : List String :=
  ((sWR dsIns ++ sWR dsNew ++ sWR dsDelB ++ sWR dsEmpty).filter (· ≠ "sp.em")) ++ drWR
/-- the value registers of the four proved operations -/
def vrD : List String := sVR dsIns ++ sVR dsNew ++ sVR dsDelB ++ sVR dsEmpty

set_option maxRecDepth 100000 in
theorem wrD_ok : ∀ a ∈ wrD, a ∉ spRegs := by decide
set_option maxRecDepth 100000 in
theorem drWA_ok : ∀ a ∈ drWA, a ∉ spArrs := by decide
set_option maxRecDepth 100000 in
theorem drVA_ok : ∀ a ∈ drVA, a ∉ "sl.l" :: "gW" :: labV := by decide
set_option maxRecDepth 100000 in
theorem vrD_ok : ∀ a ∈ vrD, a ∉ spVRegs := by decide
set_option maxRecDepth 100000 in
theorem opsWA_sub : ∀ a ∈ sWA dsIns ++ sWA dsNew ++ sWA dsDelB ++ sWA dsEmpty, a ∈ drWA := by decide
set_option maxRecDepth 100000 in
theorem opsVA_sub : ∀ a ∈ sVA dsIns ++ sVA dsNew ++ sVA dsDelB ++ sVA dsEmpty, a ∈ drVA := by decide

/-- the name lists of the D layer: the representation, the four proved operations, and the extra
names `x*` of the merge and the pull -/
theorem dnames_of (xWA xVA xWR xVR : List String) (h1 : ∀ a ∈ xWA, a ∉ spArrs)
    (h2 : ∀ a ∈ xVA, a ∉ "sl.l" :: "gW" :: labV) (h3 : ∀ a ∈ xWR, a ∉ spRegs)
    (h4 : ∀ a ∈ xVR, a ∉ spVRegs) :
    DNames (drWA ++ xWA) (drVA ++ xVA) (wrD ++ xWR) (vrD ++ xVR) := by
  have hwa : ∀ a, a ∈ sWA dsIns ++ sWA dsNew ++ sWA dsDelB ++ sWA dsEmpty → a ∈ drWA ++ xWA :=
    fun a ha => List.mem_append_left _ (opsWA_sub a ha)
  have hva : ∀ a, a ∈ sVA dsIns ++ sVA dsNew ++ sVA dsDelB ++ sVA dsEmpty → a ∈ drVA ++ xVA :=
    fun a ha => List.mem_append_left _ (opsVA_sub a ha)
  have hwr : ∀ a, a ∈ sWR dsIns ++ sWR dsNew ++ sWR dsDelB ++ sWR dsEmpty → a ≠ "sp.em" →
      a ∈ wrD ++ xWR := fun a ha hne => List.mem_append_left _ (List.mem_append_left _
        (List.mem_filter.mpr ⟨ha, by simpa using hne⟩))
  have hvr : ∀ a, a ∈ sVR dsIns ++ sVR dsNew ++ sVR dsDelB ++ sVR dsEmpty → a ∈ vrD ++ xVR :=
    fun a ha => List.mem_append_left _ ha
  have hne_ins : ∀ a ∈ sWR dsIns, a ≠ "sp.em" := by decide
  have hne_new : ∀ a ∈ sWR dsNew, a ≠ "sp.em" := by decide
  have hne_del : ∀ a ∈ sWR dsDelB, a ≠ "sp.em" := by decide
  refine ⟨fun a ha => List.mem_append_left _ ha, fun a ha => List.mem_append_left _ ha,
    fun a ha => List.mem_append_left _ (List.mem_append_right _ ha), ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro a ha; exact hwa a (by simp [ha]))
    | (intro a ha; exact hva a (by simp [ha]))
    | (intro a ha; exact hvr a (by simp [ha]))
    | skip
  · intro a ha; exact hwr a (by simp [ha]) (hne_ins a ha)
  · intro a ha; exact hwr a (by simp [ha]) (hne_new a ha)
  · intro a ha; exact hwr a (by simp [ha]) (hne_del a ha)
  · intro a ha
    by_cases he : a = "sp.em"
    · subst he; exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact List.mem_append_left _ (hwr a (by simp [ha]) he)
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact drWA_ok a ha
    · exact h1 a ha
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact drVA_ok a ha
    · exact h2 a ha
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact wrD_ok a ha
    · exact h3 a ha
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact vrD_ok a ha
    · exact h4 a ha

end inst

end Frontier.CHD.DLI
