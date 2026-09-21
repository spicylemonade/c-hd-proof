import Frontier.CHD.BMLazy
import Frontier.CHD.DInsertL

/-!
# WinScanA — Layer-A facts for the RAM window scan BM.19–21 / BM.27–28 (agent-02, NON-GATE)

* `DInv`: the D-side invariant the RAM insert needs (WF, fresh ids, distinct ids, live ids below
  `fresh`, keys = label end vertices); preserved by every `relaxInsCc (dlOps)` step whose candidate
  is below the structure's bound (`DInv.relaxInsCc`), and so along any fold.
* Complete labels never change along a fold of relaxations (`foldl_d_complete`), so the candidates
  `d[u] ⊕ e` of the scanned vertices are those of the scan's start state.
* `slots a b`: the edge slots `[a, b)` in increasing order; the window list of the scan is a
  concatenation of such slot lists.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.WinScan

open Frontier Frontier.CHD Frontier.CHD.DB Frontier.CHD.BM

variable {G : Graph} {s : Fin G.n}

/-- The D-side invariant of one level structure and the global state. -/
structure DInv (g : BM.DGl G s) (Dc : BM.DStrM G s) : Prop where
  wf : DB.WF g.L Dc
  fr : DB.FreshOK g.fresh Dc
  ids : DB.IdsNodup Dc
  lf : ∀ u i a, g.L u = some (i, a) → i < g.fresh
  key : DB.KeyInj g.L (BM.kof G s)

theorem kof_ext {lab : WLab G s} (h : lab ≠ ⊤) (e : Fin G.m) :
    BM.kof G s (ext lab e) = G.dst e := by
  obtain ⟨q, hq⟩ : ∃ q : List (Fin G.m), lab = ((toW q : WalkOrd G s) : WLab G s) := by
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp h; exact ⟨q, hq.symm⟩
  rw [hq, ext_coe]
  exact MLab.walk_endV_append e

/-- One insertion keeps the invariant (candidate below the bound, key = its end vertex). -/
theorem DInv.insC {T : ℕ} {g : BM.DGl G s} {Dc : BM.DStrM G s} (h : DInv g Dc) (v : Fin G.n)
    (lam : WLab G s) (hB : lam < Dc.Bd) (hkv : BM.kof G s lam = v) :
    DInv (BM.insC (BM.dlOps G s) T g Dc v lam).1 (BM.insC (BM.dlOps G s) T g Dc v lam).2.1 := by
  have hNS := DIns.insertL_eq_insertNS g.L g.fresh Dc v lam
  simp only [Prod.ext_iff] at hNS
  obtain ⟨e1, e2, e3⟩ := hNS
  have hL := BM.dlInsert_L g.L g.fresh Dc v lam
  have haux := DL.insertL_aux (kof := BM.kof G s) h.fr h.ids h.key hkv
  by_cases hsk : DB.skipIns g.L v lam = true
  · have hins : DIns.insertNS g.L g.fresh Dc v lam = (g.L, g.fresh, Dc) := by
      simp [DIns.insertNS, hsk]
    rw [hins] at e1 e2 e3
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show DB.WF (DL.insertL g.L g.fresh Dc v lam).1 (DL.insertL g.L g.fresh Dc v lam).2.2.1
      rw [e1, e3]; exact h.wf
    · show DB.FreshOK (DL.insertL g.L g.fresh Dc v lam).2.1 (DL.insertL g.L g.fresh Dc v lam).2.2.1
      rw [e2, e3]; exact h.fr
    · exact haux.1
    · show ∀ u i a, (DL.insertL g.L g.fresh Dc v lam).1 u = some (i, a) →
        i < (DL.insertL g.L g.fresh Dc v lam).2.1
      rw [e1, e2]; exact h.lf
    · exact haux.2
  · have hsp := DL.insertL_spec h.wf h.fr hB (fun h' => absurd h' hsk)
    refine ⟨hsp.2.1, hsp.2.2.1, haux.1, ?_, haux.2⟩
    show ∀ u i a, (DL.insertL g.L g.fresh Dc v lam).1 u = some (i, a) →
      i < (DL.insertL g.L g.fresh Dc v lam).2.1
    have hins : DIns.insertNS g.L g.fresh Dc v lam = (Function.update g.L v (some (g.fresh, lam)),
        g.fresh + 1, { Dc with blocks := DIns.prependOwner lam ⟨g.fresh, v, lam⟩ Dc.blocks }) := by
      simp [DIns.insertNS, hsk]
    rw [hins] at e1 e2
    rw [e1, e2]
    intro u i a hu
    simp only at hu ⊢
    by_cases huv : u = v
    · subst huv
      rw [Function.update_self] at hu
      simp only [Option.some.injEq, Prod.mk.injEq] at hu
      obtain ⟨rfl, -⟩ := hu
      omega
    · rw [Function.update_of_ne huv] at hu; have := h.lf u i a hu; omega

theorem insC_Bd {T : ℕ} (g : BM.DGl G s) (Dc : BM.DStrM G s) (v : Fin G.n) (lam : WLab G s) :
    (BM.insC (BM.dlOps G s) T g Dc v lam).2.1.Bd = Dc.Bd ∧
      (BM.insC (BM.dlOps G s) T g Dc v lam).2.1.blocks.length = Dc.blocks.length := by
  have hNS := DIns.insertL_eq_insertNS g.L g.fresh Dc v lam
  simp only [Prod.ext_iff] at hNS
  refine ⟨(BM.dlInsert_M g.L g.fresh Dc v lam).2, ?_⟩
  show (DL.insertL g.L g.fresh Dc v lam).2.2.1.blocks.length = _
  rw [hNS.2.2]
  unfold DIns.insertNS
  split_ifs
  · rfl
  · simp only; rw [DIns.prependOwner_eq, DIns.prependAt_length]

open Classical in
/-- One relaxation step keeps the invariant, the bound and the number of blocks. -/
theorem DInv.relaxInsCc {T : ℕ} {B : WLab G s} {lo : Option (WLab G s)} {st : BM.RSt G s}
    (h : DInv st.g st.Dc) (hBd : st.Dc.Bd = B) (e : Fin G.m) :
    DInv (BM.relaxInsCc (BM.dlOps G s) T B lo st e).g (BM.relaxInsCc (BM.dlOps G s) T B lo st e).Dc ∧
      (BM.relaxInsCc (BM.dlOps G s) T B lo st e).Dc.Bd = B ∧
      (BM.relaxInsCc (BM.dlOps G s) T B lo st e).Dc.blocks.length = st.Dc.blocks.length := by
  unfold BM.relaxInsCc
  by_cases hv : BM.ValidRelax G s st.d B e
  · rw [if_pos hv]
    have hlt : ext (st.d (G.src e)) e < st.Dc.Bd := by rw [hBd]; exact hv.2
    have hne : st.d (G.src e) ≠ ⊤ := by
      intro h0; have := hv.2; rw [h0, ext_top] at this; exact absurd this (not_lt.mpr le_top)
    have hk := kof_ext hne e
    have hI := h.insC (T := T) (G.dst e) _ hlt hk
    have hBl := insC_Bd (T := T) st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)
    cases lo with
    | none => exact ⟨hI, hBl.1.trans hBd, hBl.2⟩
    | some b =>
      by_cases hb : b ≤ ext (st.d (G.src e)) e
      · simp only [if_pos hb]; exact ⟨hI, hBl.1.trans hBd, hBl.2⟩
      · simp only [if_neg hb]; exact ⟨h, hBd, by simp⟩
  · rw [if_neg hv]; exact ⟨h, hBd, rfl⟩

open Classical in
/-- The label part of a relaxation step. -/
theorem relaxInsCc_d {T : ℕ} {B : WLab G s} {lo : Option (WLab G s)} (st : BM.RSt G s)
    (e : Fin G.m) :
    (BM.relaxInsCc (BM.dlOps G s) T B lo st e).d = if BM.ValidRelax G s st.d B e then
      Function.update st.d (G.dst e) (ext (st.d (G.src e)) e) else st.d := by
  unfold BM.relaxInsCc
  by_cases hv : BM.ValidRelax G s st.d B e
  · rw [if_pos hv, if_pos hv]
    cases lo with
    | none => rfl
    | some b => by_cases hb : b ≤ ext (st.d (G.src e)) e <;> simp [hb]
  · rw [if_neg hv, if_neg hv]

open Classical in
/-- A relaxation step keeps walk labels and never changes a complete label. -/
theorem relaxInsCc_d_complete {T : ℕ} {B : WLab G s} {lo : Option (WLab G s)} (st : BM.RSt G s)
    (hw : WalkInv st.d) (e : Fin G.m) :
    WalkInv (BM.relaxInsCc (BM.dlOps G s) T B lo st e).d ∧
      ∀ u, st.d u = dis (s := s) u → (BM.relaxInsCc (BM.dlOps G s) T B lo st e).d u = st.d u := by
  rw [relaxInsCc_d]
  by_cases hv : BM.ValidRelax G s st.d B e
  · rw [if_pos hv]
    refine ⟨walkInv_update hw, fun u hu => ?_⟩
    by_cases hue : u = G.dst e
    · subst hue
      rw [Function.update_self]
      exact le_antisymm hv.1 (by rw [hu]; exact dis_le_ext hw e)
    · rw [Function.update_of_ne hue]
  · rw [if_neg hv]; exact ⟨hw, fun u _ => rfl⟩

/-- The same along a fold. -/
theorem foldl_invs {T : ℕ} {B : WLab G s} {lo : Option (WLab G s)} :
    ∀ (L : List (Fin G.m)) (st : BM.RSt G s), WalkInv st.d → DInv st.g st.Dc → st.Dc.Bd = B →
      WalkInv (L.foldl (BM.relaxInsCc (BM.dlOps G s) T B lo) st).d ∧
      DInv (L.foldl (BM.relaxInsCc (BM.dlOps G s) T B lo) st).g
        (L.foldl (BM.relaxInsCc (BM.dlOps G s) T B lo) st).Dc ∧
      (L.foldl (BM.relaxInsCc (BM.dlOps G s) T B lo) st).Dc.Bd = B ∧
      (L.foldl (BM.relaxInsCc (BM.dlOps G s) T B lo) st).Dc.blocks.length = st.Dc.blocks.length ∧
      ∀ u, st.d u = dis (s := s) u →
        (L.foldl (BM.relaxInsCc (BM.dlOps G s) T B lo) st).d u = st.d u
  | [], st, hw, hI, hB => ⟨hw, hI, hB, rfl, fun _ _ => rfl⟩
  | e :: L, st, hw, hI, hB => by
    obtain ⟨hw1, hd1⟩ := relaxInsCc_d_complete (T := T) (B := B) (lo := lo) st hw e
    obtain ⟨hI1, hB1, hl1⟩ := hI.relaxInsCc (T := T) (lo := lo) hB e
    obtain ⟨a1, a2, a3, a4, a5⟩ := foldl_invs L _ hw1 hI1 hB1
    refine ⟨a1, a2, a3, a4.trans hl1, fun u hu => ?_⟩
    exact (a5 u (by rw [hd1 u hu]; exact hu)).trans (hd1 u hu)

/-! ### Slot lists -/

/-- The edge slots `[a, b)`, increasing. -/
def slots (G : Graph) (a b : ℕ) : List (Fin G.m) :=
  (List.range' a (b - a)).filterMap (fun j => if h : j < G.m then some ⟨j, h⟩ else none)

theorem mem_slots {a b : ℕ} {e : Fin G.m} : e ∈ slots G a b ↔ a ≤ (e : ℕ) ∧ (e : ℕ) < b := by
  simp only [slots, List.mem_filterMap, List.mem_range']
  constructor
  · rintro ⟨j, ⟨k, hk, rfl⟩, hj⟩
    split_ifs at hj with hm
    · simp only [Option.some.injEq] at hj; subst hj; simp; omega
  · rintro ⟨h1, h2⟩
    exact ⟨e, ⟨(e : ℕ) - a, by omega, by omega⟩, by simp [e.isLt]⟩

theorem slots_nodup (a b : ℕ) : (slots G a b).Nodup := by
  unfold slots
  refine List.Nodup.filterMap ?_ List.nodup_range'
  intro j j' e h h'
  split_ifs at h h' <;> simp_all [Fin.ext_iff]

theorem slots_self (a : ℕ) : slots G a a = [] := by simp [slots]

theorem slots_succ {a b : ℕ} (hab : a ≤ b) (hb : b < G.m) :
    slots G a (b + 1) = slots G a b ++ [⟨b, hb⟩] := by
  unfold slots
  have : b + 1 - a = (b - a) + 1 := by omega
  rw [this, List.range'_concat, List.filterMap_append]
  congr 1
  simp [List.range', show a + (b - a) = b by omega, hb]

end Frontier.CHD.WinScan
