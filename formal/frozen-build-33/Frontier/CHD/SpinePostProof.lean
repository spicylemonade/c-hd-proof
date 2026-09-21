import Frontier.CHD.SpinePost

/-!
# SpinePostProof — proof of `PostSpecStmt` (agent-06, B-L4, NON-GATE)

The second half of an iteration of the main loop, composed from `DLayer.merge_spec`,
`removeTail_spec`, `scanP_spec`, `reselect_spec`, `appendU_spec`/`copyBp_spec` and
`DLayer.empty_spec`, with the Layer-A facts of `postA`.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamSpine

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.RamLevel
  Frontier.CHD.BM Frontier.CHD.RamBaseCase Frontier.CHD.LabTab WExpr Stmt

/-! ## Helpers -/

section helpers

variable {G : Graph} {s : Fin G.n}

/-- A vertex-set row as a list of vertices. -/
theorem SetRow.list {st : State ℝ≥0} {arr len : String} {l : ℕ} {X : Finset (Fin G.n)}
    (h : SetRow st arr len l X) :
    ∃ lX : List (Fin G.n), RowRep st arr len G.n l (lX.map Fin.val) ∧ lX.Nodup ∧ lX.toFinset = X ∧
      ∀ x : ℕ, x ∈ lX.map Fin.val ↔ ∃ u ∈ X, (u : ℕ) = x := by
  obtain ⟨xs, hR, hnd, hmem⟩ := h
  have hlt : ∀ x ∈ xs, x < G.n := fun x hx => by
    obtain ⟨u, -, rfl⟩ := (hmem x).mp hx; exact u.isLt
  have hmap : (xs.pmap (fun x hx => (⟨x, hx⟩ : Fin G.n)) hlt).map Fin.val = xs := by
    rw [List.map_pmap]; exact List.pmap_eq_self.mpr (fun _ _ => rfl)
  refine ⟨xs.pmap (fun x hx => (⟨x, hx⟩ : Fin G.n)) hlt, by rw [hmap]; exact hR, ?_, ?_, ?_⟩
  · exact List.Nodup.of_map Fin.val (by rw [hmap]; exact hnd)
  · ext u
    rw [List.mem_toFinset]
    constructor
    · intro hu
      have hu' : (u : ℕ) ∈ xs := by rw [← hmap]; exact List.mem_map_of_mem hu
      obtain ⟨v, hv, hvu⟩ := (hmem u).mp hu'
      rw [← Fin.ext hvu]; exact hv
    · intro hu
      have hu' : (u : ℕ) ∈ xs := (hmem u).mpr ⟨u, hu, rfl⟩
      rw [← hmap, List.mem_map] at hu'
      obtain ⟨v, hv, hvu⟩ := hu'
      rw [← Fin.ext hvu]; exact hv
  · intro x; rw [hmap]; exact hmem x

/-- `GrpRep` only sees the pivots of groups `j < p`. -/
theorem grpRep_piv_congr {V : Type} {st : State V} {l n p : ℕ} {P : ℕ → Finset ℕ} {piv piv' : ℕ → ℕ}
    (h : GrpRep st l n p P piv) (hp : ∀ j < p, piv' j = piv j) : GrpRep st l n p P piv' :=
  { h with pivs := fun j hj => (h.pivs j hj).trans (hp j hj).symm }

/-- The lifted group family after removing `Ui`. -/
theorem liftP_sdiff {p : ℕ} (P : Fin p → Finset (Fin G.n)) (Ui : Finset (Fin G.n)) (xs : List ℕ)
    (hxs : ∀ x, x ∈ xs ↔ ∃ u ∈ Ui, (u : ℕ) = x) (j : ℕ) :
    liftP (fun j => P j \ Ui) j = liftP P j \ xs.toFinset := by
  unfold liftP
  split_ifs with hj
  · ext x
    simp only [Finset.mem_map, Finset.mem_sdiff, Fin.valEmbedding_apply, List.mem_toFinset, hxs]
    constructor
    · rintro ⟨u, ⟨hu, hnu⟩, rfl⟩
      exact ⟨⟨u, hu, rfl⟩, fun ⟨v, hv, hvu⟩ => hnu (Fin.ext hvu ▸ hv)⟩
    · rintro ⟨⟨u, hu, rfl⟩, hn⟩
      exact ⟨u, ⟨hu, fun hu' => hn ⟨u, hu', rfl⟩⟩, rfl⟩
  · simp

/-- An `Unchanged` from its components. -/
theorem unch_of_parts {V : Type} {st r : State V} {wa wr : List String}
    (hwa : ∀ a, a ∉ wa → r.wa a = st.wa a) (hwl : r.wlen = st.wlen) (hva : r.va = st.va)
    (hvl : r.vlen = st.vlen) (hcap : r.cap = st.cap) (hpr : r.procs = st.procs) (hv : r.v = st.v)
    (hwr : ∀ y, y ∉ wr → r.w y = st.w y) : Unchanged st r wa [] wr [] :=
  ⟨fun a ha => ⟨hwa a ha, by rw [hwl]⟩, fun a _ => ⟨by rw [hva], by rw [hvl]⟩, hwr,
    fun a _ => by rw [hv], hcap, hpr⟩

/-- Insertions keep the block count and cost at most `log₂ (#blocks) + 4` each. -/
theorem insManyC_cost_le {T : ℕ} (f : Fin G.n → WLab G s) :
    ∀ (L : List (Fin G.n)) (g : DGl G s) (D : DStrM G s),
      (insManyC (dlOps G s) T f L g D).2.2 ≤ L.length * (Nat.log 2 D.blocks.length + 4) ∧
      (insManyC (dlOps G s) T f L g D).2.1.blocks.length = D.blocks.length
  | [], g, D => by simp [insManyC]
  | y :: L, g, D => by
    obtain ⟨h1, h2⟩ := insManyC_cost_le f L (BM.insC (dlOps G s) T g D y (f y)).1
      (BM.insC (dlOps G s) T g D y (f y)).2.1
    have hb := (WinScan.insC_Bd (T := T) g D y (f y)).2
    have hc := WinScan.insC_cost_le (T := T) g D y (f y)
    rw [hb] at h1 h2
    refine ⟨?_, h2⟩
    show (BM.insC (dlOps G s) T g D y (f y)).2.2 +
      (insManyC (dlOps G s) T f L (BM.insC (dlOps G s) T g D y (f y)).1
        (BM.insC (dlOps G s) T g D y (f y)).2.1).2.2 ≤ (L.length + 1) * (Nat.log 2 D.blocks.length + 4)
    rw [Nat.succ_mul]; omega

end helpers

/-! ## Labels along the window fold -/

section fold

variable {G : Graph} {s : Fin G.n}

open Classical in
theorem relaxInsCc_d_le {T : ℕ} {B : WLab G s} {lo : Option (WLab G s)} (st : RSt G s) (e : Fin G.m)
    (v : Fin G.n) : (relaxInsCc (dlOps G s) T B lo st e).d v ≤ st.d v := by
  rw [WinScan.relaxInsCc_d]
  split_ifs with hv
  · by_cases hve : v = G.dst e
    · subst hve; rw [Function.update_self]; exact hv.1
    · rw [Function.update_of_ne hve]
  · exact le_rfl

theorem foldl_d_le {T : ℕ} {B : WLab G s} {lo : Option (WLab G s)} :
    ∀ (L : List (Fin G.m)) (st : RSt G s) (v : Fin G.n),
      (L.foldl (relaxInsCc (dlOps G s) T B lo) st).d v ≤ st.d v
  | [], _, _ => le_rfl
  | e :: L, st, v => by
    simp only [List.foldl_cons]
    exact (foldl_d_le L _ v).trans (relaxInsCc_d_le st e v)

end fold

/-! ## The re-selection's insertion interface from `DL.ins` -/

section ins

variable {G : Graph} {s : Fin G.n} {T : ℕ → ℕ}

/-- What the re-selection's insertions keep at level `l`: `D` (ancestors `Ds`), the labels `d` in
`LabAt` form, `lvl = l`, `n = |V|`, and the level structure's bound `Bd`. -/
def InsR (DL : DLayer G s T) (Ds : ℕ → DStrM G s) (l : ℕ) (d : Labels G s) (H : Hist G) (c0 : ℕ)
    (Bd : WLab G s) (st : State ℝ≥0) (g : DGl G s) (D : DStrM G s) : Prop :=
  DL.DR st H g (Function.update Ds l D) l ∧ LabAt st d H c0 ∧ st.w "lvl" = l ∧ st.w "n" = G.n ∧
    D.Bd = Bd

theorem labW_sub_spArrs : ∀ a ∈ labW, a ∈ spArrs := by decide
theorem grpArrs_sub_spArrs : ∀ a ∈ grpArrs, a ∈ spArrs := by decide

/-- **`DL.ins` meets `InsI`** (at the labels `d`, level `l`, for vertices below the bound `Bd`,
with the `D` layer's use counter as resource). -/
theorem insI_DL (DL : DLayer G s T) (Ds : ℕ → DStrM G s) (l : ℕ) (d : Labels G s) (H : Hist G)
    (c0 : ℕ) (Bd : WLab G s) :
    RamSpineU.InsI realOps DL.ins (InsR DL Ds l d H c0 Bd) (fun _ _ => True) (fun v => d v < Bd)
      DL.use DL.ucap d (T l) DL.K DL.K DL.dWA DL.dVA DL.dWR DL.dVR where
  run := fun st g D v hD _ hv hpx hu => by
    obtain ⟨hDR, hL, hl, hn, hBd⟩ := hD
    have hlt : d v < (Function.update Ds l D l).Bd := by rw [Function.update_self, hBd]; exact hv
    refine (DL.ins_spec st H g (Function.update Ds l D) l d c0 v hDR hL hl hn hpx hlt
      (by rw [Function.update_self]; exact hu)).mono ?_
    rintro r ⟨hD', hU, hwl, hvl, hc1, hc2, hu2⟩
    rw [Function.update_self, Function.update_idem] at hD'
    rw [Function.update_self] at hc2 hu2
    refine ⟨⟨hD', hL.of_unchanged hU (fun a ha h => DL.dWA_ok a h (labW_sub_spArrs a ha))
      (fun h => DL.dVA_ok _ h (by simp [labV])) hc1,
      by rw [hU.wreg _ (fun h => DL.dWR_ok _ h (by decide))]; exact hl,
      by rw [hU.wreg _ (fun h => DL.dWR_ok _ h (by decide))]; exact hn,
      by rw [(WinScan.insC_Bd (T := T l) g D v (d v)).1, hBd]⟩, hU, hwl, hvl, hc1, ?_, hu2⟩
    rw [Nat.mul_add, Nat.mul_one] at hc2; omega
  regs := fun a ha => ⟨by rintro rfl; exact DL.dWR_ok _ ha (by decide),
    by rintro rfl; exact DL.dWR_ok _ ha (by decide), by rintro rfl; exact DL.dWR_ok _ ha (by decide)⟩
  arrs := fun a ha => ⟨fun h => DL.dWA_ok a ha (grpArrs_sub_spArrs a h),
    by rintro rfl; exact DL.dWA_ok _ ha (by decide), by rintro rfl; exact DL.dWA_ok _ ha (by decide)⟩
  res_frame := fun st r wa va wr vr hU hwr => DL.use_frame st r wa va wr vr hU (fun a ha h => hwr a h ha)

end ins

/-! ## Frames of the spine-wide facts -/

section frames

variable {G : Graph} {s : Fin G.n}

theorem SlotLens.of_len {st r : State ℝ≥0} {i : ℕ} (h : SlotLens st i) (hw : r.wlen = st.wlen)
    (hv : r.vlen = st.vlen) : SlotLens r i :=
  ⟨by rw [hv]; exact h.l, by rw [hw]; exact h.h, by rw [hw]; exact h.v, by rw [hw]; exact h.e,
    by rw [hw]; exact h.r, by rw [hw]; exact h.f⟩

/-- `Static` survives any fragment that keeps all lengths, the procedures, and does not touch the
graph, the tables or the heap. -/
theorem Static.of_unchanged {st r : State ℝ≥0} {LF : ℕ} {body : Stmt} {τf Mf : ℕ → ℕ}
    {wa va wr vr : List String} (h : Static st G LF body τf Mf) (hU : Unchanged st r wa va wr vr)
    (hwl : r.wlen = st.wlen) (hvl : r.vlen = st.vlen)
    (hwa : ∀ a ∈ ["gHead", "gSt", "cp.tau", "cp.M", "hp_P"], a ∉ wa) (hva : "gW" ∉ va)
    (hwr : ∀ a ∈ ["n", "gN", "hp_n"], a ∉ wr) : Static r G LF body τf Mf where
  n := by rw [hU.wreg _ (hwr _ (by simp))]; exact h.n
  gN := by rw [hU.wreg _ (hwr _ (by simp))]; exact h.gN
  graph := graphAt_of_unchanged hU (hwa _ (by simp)) hva h.graph
  csr := CSRAt.of_unchanged h.csr hU (hwa _ (by simp))
  proc := by rw [hU.procs]; exact h.proc
  rows := fun a ha => by rw [hwl]; exact h.rows a ha
  lens := fun a ha => by rw [hwl]; exact h.lens a ha
  slots := fun i hi => SlotLens.of_len (h.slots i hi) hwl hvl
  xm := by rw [hwl]; exact h.xm
  ptr := by rw [hwl]; exact h.ptr
  tau := by rw [hwl]; exact h.tau
  Ml := by rw [hwl]; exact h.Ml
  tauv := fun l hl => by rw [(hU.warr _ (hwa _ (by simp))).1]; exact h.tauv l hl
  Mv := fun l hl => by rw [(hU.warr _ (hwa _ (by simp))).1]; exact h.Mv l hl
  heap := by
    obtain ⟨h1, h2, h3, h4⟩ := h.heap
    refine ⟨by rw [hU.wreg _ (hwr _ (by simp))]; exact h1, by rw [hwl]; exact h2, by rw [hwl]; exact h3,
      fun v hv => by rw [(hU.warr _ (hwa _ (by simp))).1]; exact h4 v hv⟩
  cap := by rw [hU.cap]; exact h.cap
  tauCap := fun l hl => by rw [hU.cap]; exact h.tauCap l hl
  MCap := fun l hl => by rw [hU.cap]; exact h.MCap l hl

end frames

/-! ## Counting the re-selection's work -/

section count

variable {G : Graph} {s : Fin G.n}

open Classical in
theorem resel_count {p : ℕ} (σ : LState G s p) (Ui : Finset (Fin G.n))
    (hdisj : ∀ i j : Fin p, i ≠ j → Disjoint (σ.P i) (σ.P j))
    (xs : List ℕ) (hxs : ∀ x, x ∈ xs ↔ ∃ u ∈ Ui, (u : ℕ) = x)
    (mks : List ℕ) (hmnd : mks.Nodup)
    (hmks : ∀ j, j ∈ mks ↔ j < p ∧ liftPiv σ.piv j ∈ xs ∧ liftPiv σ.piv j ∈ liftP σ.P j) :
    mks.length ≤ (markedGroups σ Ui).card + Ui.card ∧
    (mks.map (fun j => (liftP σ.P j \ xs.toFinset).card)).sum ≤
      ∑ j ∈ markedGroups σ Ui, (σ.P j \ Ui).card ∧
    (mks.filter (fun j => 0 < (liftP σ.P j \ xs.toFinset).card)).length ≤ (markedGroups σ Ui).card := by
  set w : ℕ → ℕ := fun j => (liftP σ.P j \ xs.toFinset).card with hw
  have hwj : ∀ j (hj : j < p), w j = (σ.P ⟨j, hj⟩ \ Ui).card := by
    intro j hj
    simp only [hw]
    rw [← liftP_sdiff σ.P Ui xs hxs j]
    simp [liftP, hj]
  have hpivU : ∀ j (hj : j < p), liftPiv σ.piv j ∈ xs → σ.piv ⟨j, hj⟩ ∈ Ui := by
    intro j hj h
    obtain ⟨u, hu, hux⟩ := (hxs _).mp h
    have : u = σ.piv ⟨j, hj⟩ := Fin.ext (by rw [hux]; simp [liftPiv, hj])
    rw [← this]; exact hu
  set Mf : Finset ℕ := (markedGroups σ Ui).map Fin.valEmbedding with hMf
  have hsub' : mks.toFinset.filter (fun j => 0 < w j) ⊆ Mf := by
    intro j hj
    rw [Finset.mem_filter, List.mem_toFinset] at hj
    obtain ⟨hjm, hjw⟩ := hj
    obtain ⟨hjp, hjx, -⟩ := (hmks j).mp hjm
    rw [hMf, Finset.mem_map]
    refine ⟨⟨j, hjp⟩, ?_, rfl⟩
    simp only [markedGroups, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hpivU j hjp hjx, ?_⟩
    rw [← Finset.card_pos, ← hwj j hjp]; exact hjw
  set A := mks.filter (fun j => decide (0 < w j)) with hA
  set E := mks.filter (fun j => !decide (0 < w j)) with hE
  have hAnd : A.Nodup := hmnd.filter _
  have hAcard : A.length ≤ (markedGroups σ Ui).card := by
    rw [← List.toFinset_card_of_nodup hAnd, hA, List.toFinset_filter]
    refine (Finset.card_le_card (fun j hj => hsub' (by simpa using hj))).trans ?_
    rw [hMf, Finset.card_map]
  -- the empty marked groups: their pivots are distinct vertices of `U_i`
  have hEnd : E.Nodup := hmnd.filter _
  have hEcard : E.length ≤ Ui.card := by
    rw [← List.toFinset_card_of_nodup hEnd]
    have himg : E.toFinset.image (liftPiv σ.piv) ⊆ xs.toFinset := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      rw [List.mem_toFinset, hE, List.mem_filter] at hj
      rw [List.mem_toFinset]; exact ((hmks j).mp hj.1).2.1
    have hinj : Set.InjOn (liftPiv σ.piv) E.toFinset := by
      intro j hj j' hj' he
      rw [Finset.mem_coe, List.mem_toFinset, hE, List.mem_filter] at hj hj'
      obtain ⟨hjp, -, hjP⟩ := (hmks j).mp hj.1
      obtain ⟨hjp', -, hjP'⟩ := (hmks j').mp hj'.1
      by_contra hne
      have hne' : (⟨j, hjp⟩ : Fin p) ≠ ⟨j', hjp'⟩ := fun h => hne (congrArg Fin.val h)
      have h1 : σ.piv ⟨j, hjp⟩ ∈ σ.P ⟨j, hjp⟩ := by
        rw [← val_mem_liftP]; simpa [liftPiv, hjp] using hjP
      have h2 : σ.piv ⟨j', hjp'⟩ ∈ σ.P ⟨j', hjp'⟩ := by
        rw [← val_mem_liftP]; simpa [liftPiv, hjp'] using hjP'
      have heq : σ.piv ⟨j, hjp⟩ = σ.piv ⟨j', hjp'⟩ := Fin.ext (by simpa [liftPiv, hjp, hjp'] using he)
      rw [heq] at h1
      exact Finset.disjoint_left.mp (hdisj _ _ hne') h1 h2
    have hxsU : xs.toFinset = Ui.map Fin.valEmbedding := by
      ext x; simp [hxs]
    calc E.toFinset.card = (E.toFinset.image (liftPiv σ.piv)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ xs.toFinset.card := Finset.card_le_card himg
      _ = Ui.card := by rw [hxsU, Finset.card_map]
  have hlen : mks.length = A.length + E.length := List.length_eq_length_filter_add _
  refine ⟨by omega, ?_, hAcard⟩
  -- the sum over the marks
  calc (mks.map w).sum = ∑ j ∈ mks.toFinset, w j := (List.sum_toFinset w hmnd).symm
    _ = ∑ j ∈ mks.toFinset.filter (fun j => 0 < w j), w j :=
        (Finset.sum_filter_of_ne (fun x _ hx => Nat.pos_of_ne_zero hx)).symm
    _ ≤ ∑ j ∈ Mf, w j := Finset.sum_le_sum_of_subset hsub'
    _ = ∑ j ∈ markedGroups σ Ui, w j := by rw [hMf, Finset.sum_map]; rfl
    _ = ∑ j ∈ markedGroups σ Ui, (σ.P j \ Ui).card :=
        Finset.sum_congr rfl (fun j _ => by rw [hwj j j.2])

end count

theorem length_filterMap_ite {α β : Type*} (l : List α) (q : α → Prop) [DecidablePred q] (g : α → β) :
    l.filterMap (fun a => if q a then some (g a) else none) = (l.filter (fun a => decide (q a))).map g := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : q a <;> simp [List.filterMap_cons, List.filter_cons, h, ih]

/-! ## From RAM pivot choices to Layer-A re-selections -/

section completion

variable {G : Graph} {s : Fin G.n}

open Classical in
/-- **A RAM choice of key-minimal pivots is a Layer-A re-selection**: the pivot family (the RAM's
choice on the marked nonempty groups, the old pivot elsewhere) satisfies `Reselect`, and the RAM's list
of inserted pivots is duplicate-free with the re-selected set. -/
theorem resel_completion {p : ℕ} {cs : CSt G s p} {Ui : Finset (Fin G.n)} {lUi : List (Fin G.n)}
    (hlUmem : ∀ x : ℕ, x ∈ lUi.map Fin.val ↔ ∃ u ∈ Ui, (u : ℕ) = x)
    (hpivots : ∀ j, (cs.P j).Nonempty → cs.piv j ∈ cs.P j)
    (hdisj : ∀ i j : Fin p, i ≠ j → Disjoint (cs.P i) (cs.P j))
    {mks : List ℕ} (hmnd : mks.Nodup)
    (hmks : ∀ j, j ∈ mks ↔ j < p ∧ liftPiv cs.piv j ∈ lUi.map Fin.val ∧ liftPiv cs.piv j ∈ liftP cs.P j)
    (d2 : Labels G s) (pf : ℕ → ℕ)
    (hpf : ∀ j ∈ mks, 0 < (liftP cs.P j \ (lUi.map Fin.val).toFinset).card →
      pf j ∈ liftP cs.P j \ (lUi.map Fin.val).toFinset ∧
        ∀ x ∈ liftP cs.P j \ (lUi.map Fin.val).toFinset, labKey d2 (pf j) ≤ labKey d2 x)
    (Lf : List (Fin G.n))
    (hLf : Lf.map Fin.val = mks.filterMap (fun j =>
      if 0 < (liftP cs.P j \ (lUi.map Fin.val).toFinset).card then some (pf j) else none)) :
    ∃ piv' : Fin p → Fin G.n, Reselect cs.lit Ui d2 piv' ∧ Lf.Nodup ∧
      Lf.toFinset = reselected cs.lit Ui piv' ∧
      (∀ j : Fin p, ((j : ℕ) ∈ mks ∧ 0 < (liftP cs.P j \ (lUi.map Fin.val).toFinset).card) →
        (piv' j : ℕ) = pf j) ∧
      (∀ j : Fin p, ¬ ((j : ℕ) ∈ mks ∧ 0 < (liftP cs.P j \ (lUi.map Fin.val).toFinset).card) →
        piv' j = cs.piv j) := by
  set xs := lUi.map Fin.val with hxs
  have hPmem : ∀ (j : Fin p) (y : Fin G.n), (y : ℕ) ∈ liftP cs.P j \ xs.toFinset ↔ y ∈ cs.P j \ Ui :=
    fun j y => by
      rw [← liftP_sdiff cs.P Ui _ hlUmem j]
      exact val_mem_liftP (fun j => cs.P j \ Ui) j y
  have hPcard : ∀ j : Fin p, (liftP cs.P j \ xs.toFinset).card = (cs.lit.P j \ Ui).card := fun j => by
    rw [← liftP_sdiff cs.P Ui _ hlUmem j]; simp [liftP, j.2, CSt.lit]
  have hlt : ∀ j : Fin p, ((j : ℕ) ∈ mks ∧ 0 < (liftP cs.P j \ xs.toFinset).card) → pf j < G.n := by
    intro j hj
    obtain ⟨u, -, hu⟩ := (mem_liftP cs.P j _).mp (Finset.mem_sdiff.mp (hpf j hj.1 hj.2).1).1
    rw [← hu]; exact u.isLt
  let piv' : Fin p → Fin G.n := fun j =>
    if h : ((j : ℕ) ∈ mks ∧ 0 < (liftP cs.P j \ xs.toFinset).card) then ⟨pf j, hlt j h⟩ else cs.piv j
  have hsel : ∀ j : Fin p, ((j : ℕ) ∈ mks ∧ 0 < (liftP cs.P j \ xs.toFinset).card) → (piv' j : ℕ) = pf j :=
    fun j h => by simp only [piv', dif_pos h]
  have hns : ∀ j : Fin p, ¬ ((j : ℕ) ∈ mks ∧ 0 < (liftP cs.P j \ xs.toFinset).card) → piv' j = cs.piv j :=
    fun j h => by simp only [piv', dif_neg h]
  have hmksj : ∀ j : Fin p, cs.piv j ∈ Ui → (cs.P j \ Ui).Nonempty → (j : ℕ) ∈ mks := by
    intro j hjU hne'
    have hpivP : cs.piv j ∈ cs.P j := hpivots j (hne'.mono Finset.sdiff_subset)
    exact (hmks j).mpr ⟨j.2, by rw [liftPiv_val]; exact (hlUmem _).mpr ⟨_, hjU, rfl⟩,
      by rw [liftPiv_val, val_mem_liftP]; exact hpivP⟩
  have hselU : ∀ j : Fin p, (j : ℕ) ∈ mks → cs.piv j ∈ Ui := by
    intro j hj
    obtain ⟨-, hx, -⟩ := (hmks j).mp hj
    rw [liftPiv_val] at hx
    obtain ⟨u, hu, hux⟩ := (hlUmem _).mp hx
    rw [← Fin.ext hux]; exact hu
  refine ⟨piv', ⟨fun j hjU hne' => ?_, fun j hj => ?_⟩, ?_, ?_, hsel, hns⟩
  · have hpos : 0 < (liftP cs.P j \ xs.toFinset).card := by rw [hPcard]; exact Finset.card_pos.mpr hne'
    have hs : (j : ℕ) ∈ mks ∧ 0 < (liftP cs.P j \ xs.toFinset).card := ⟨hmksj j hjU hne', hpos⟩
    obtain ⟨hm, hmin⟩ := hpf j hs.1 hs.2
    have e : ((piv' j : Fin G.n) : ℕ) = pf j := hsel j hs
    refine ⟨(hPmem j (piv' j)).mp (by rw [e]; exact hm), fun x hx => ?_⟩
    have h := hmin x ((hPmem j x).mpr hx)
    rw [← e] at h
    simp only [labKey, dif_pos (piv' j).isLt, dif_pos x.isLt] at h
    exact h
  · by_cases hjj : (j : ℕ) ∈ mks ∧ 0 < (liftP cs.P j \ xs.toFinset).card
    · exfalso
      apply hj
      refine ⟨hselU j hjj.1, ?_⟩
      rw [← Finset.card_pos, ← hPcard]; exact hjj.2
    · exact hns j hjj
  · -- duplicate-free: distinct marked groups have disjoint member sets
    set q : ℕ → Prop := fun j => 0 < (liftP cs.P j \ xs.toFinset).card
    have hLf' : Lf.map Fin.val = (mks.filter (fun j => decide (q j))).map pf := by
      rw [hLf]; exact length_filterMap_ite mks q pf
    refine List.Nodup.of_map Fin.val ?_
    rw [hLf']
    refine List.Nodup.map_on (fun x hx y hy hxy => ?_) (hmnd.filter _)
    rw [List.mem_filter] at hx hy
    have hxq : q x := of_decide_eq_true hx.2
    have hyq : q y := of_decide_eq_true hy.2
    have hxp := ((hmks x).mp hx.1).1
    have hyp := ((hmks y).mp hy.1).1
    obtain ⟨u, hu, hux⟩ := (mem_liftP cs.P ⟨x, hxp⟩ _).mp (Finset.mem_sdiff.mp (hpf x hx.1 hxq).1).1
    obtain ⟨w, hw, hwy⟩ := (mem_liftP cs.P ⟨y, hyp⟩ _).mp (Finset.mem_sdiff.mp (hpf y hy.1 hyq).1).1
    have huw : u = w := Fin.ext (by rw [hux, hwy]; exact hxy)
    subst huw
    by_contra hne
    exact Finset.disjoint_left.mp (hdisj ⟨x, hxp⟩ ⟨y, hyp⟩ (fun h => hne (congrArg Fin.val h))) hu hw
  · ext x
    rw [List.mem_toFinset, mem_reselected]
    have e : x ∈ Lf ↔ (x : ℕ) ∈ Lf.map Fin.val := ⟨fun h => List.mem_map_of_mem h, fun h => by
      obtain ⟨y, hy, hyx⟩ := List.mem_map.mp h; rw [← Fin.ext hyx]; exact hy⟩
    rw [e, hLf, List.mem_filterMap]
    constructor
    · rintro ⟨j, hj, hjx⟩
      by_cases hq : 0 < (liftP cs.P j \ xs.toFinset).card
      · rw [if_pos hq, Option.some.injEq] at hjx
        have hjp := ((hmks j).mp hj).1
        have hs : (((⟨j, hjp⟩ : Fin p) : ℕ) ∈ mks ∧
            0 < (liftP cs.P ((⟨j, hjp⟩ : Fin p) : ℕ) \ xs.toFinset).card) := ⟨hj, hq⟩
        refine ⟨⟨j, hjp⟩, Fin.ext (by rw [hsel _ hs]; exact hjx), hselU _ hj, ?_⟩
        rw [← Finset.card_pos, ← hPcard]; exact hq
      · rw [if_neg hq] at hjx; exact absurd hjx (by simp)
    · rintro ⟨j, hjx, hjU, hne'⟩
      have hpos : 0 < (liftP cs.P j \ xs.toFinset).card := by rw [hPcard]; exact Finset.card_pos.mpr hne'
      refine ⟨j, hmksj j hjU hne', ?_⟩
      rw [if_pos hpos, ← hsel j ⟨hmksj j hjU hne', hpos⟩, hjx]

end completion

/-! ## The proof of `PostSpecStmt` -/

section main

variable {G : Graph} {s : Fin G.n} {T : ℕ → ℕ} {Φ : Type}

theorem rmArrs_sub : ∀ a ∈ RamSpineU.rmArrs, a ∈ spArrs := by decide

theorem cap_facts {LF l n m cap : ℕ} (hl : l + 1 ≤ LF) (h : (LF + 3) * (n + m + 8) < cap) :
    4 * (l + 1) + 7 < cap ∧ (l + 1 + 1) * n + 2 < cap ∧ (l + 1) * n < cap ∧ n + 2 ≤ cap ∧
      m + 2 ≤ cap := by
  have h1 : (l + 1 + 1) * n ≤ (LF + 2) * n := Nat.mul_le_mul_right _ (by omega)
  have h2 : (LF + 3) * (n + m + 8) = (LF + 2) * n + (n + (LF + 3) * (m + 8)) := by ring
  have h3 : (LF + 3) * 8 ≤ (LF + 3) * (m + 8) := Nat.mul_le_mul_left _ (by omega)
  have h4 : (l + 1) * n ≤ (l + 1 + 1) * n := Nat.mul_le_mul_right _ (by omega)
  have h5 : m + 8 ≤ (LF + 3) * (m + 8) := Nat.le_mul_of_pos_left _ (by omega)
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- Word arrays none of the second half's `D`/group phases write. -/
def fixA : List String :=
  labW ++ slotW ++ ["gSt", "gHead", "sp.ptr", "cp.tau", "cp.M", "hp_P", "sp.np", "S", "S.len", "W",
    "W.len", "U", "U.len", "sp.inU", "sp.xm"]

theorem fixA_sp : ∀ a ∈ fixA, a ∈ spArrs := by decide
theorem fixA_rm : ∀ a ∈ fixA, a ∉ RamSpineU.rmArrs := by decide

theorem sum_marked_le {p : ℕ} (σ : LState G s p) (Ui : Finset (Fin G.n))
    (hdisj : ∀ i j : Fin p, i ≠ j → Disjoint (σ.P i) (σ.P j)) :
    ∑ j ∈ markedGroups σ Ui, (σ.P j \ Ui).card ≤ G.n := by
  rw [← Finset.card_biUnion (fun i _ j _ hij => Finset.disjoint_of_subset_left Finset.sdiff_subset
    (Finset.disjoint_of_subset_right Finset.sdiff_subset (hdisj i j hij)))]
  exact (Finset.card_le_univ _).trans (by simp)

theorem rsRegs_sp : ∀ a ∈ RamSpineU.rsRegs, a ∈ spRegs := by decide

/-- Arrays of the level data kept by the scan. -/
def grpX : List String := grpArrs ++ ["sp.mk", "sp.mk.len", "U", "U.len", "sp.inU", "sp.np", "cp.tau"]

theorem grpX_sp : ∀ a ∈ grpX, a ∈ spArrs := by decide
theorem grpX_lab : ∀ a ∈ grpX, a ∉ labW ++ ["sp.ptr"] := by decide
theorem lvl_n_rs : ∀ y ∈ ["lvl", "n"], y ∉ RamSpineU.rsRegs := by decide

/-- Arrays none of the phases before BM.24 write. -/
def fix5 : List String :=
  slotW ++ ["gSt", "gHead", "cp.tau", "cp.M", "hp_P", "sp.np", "S", "S.len", "W", "W.len", "U", "U.len",
    "sp.inU", "sp.xm"]

theorem fix5_sp : ∀ a ∈ fix5, a ∈ spArrs := by decide
theorem fix5_oth : ∀ a ∈ fix5, a ∉ RamSpineU.rmArrs ++ labW ++ ["sp.ptr", "sp.gp"] := by decide

/-- List-subset goals by membership. -/
macro "lsub" : tactic => `(tactic| (intro a ha; simp only [List.mem_append, List.mem_cons,
  List.mem_singleton, List.not_mem_nil, or_false] at ha ⊢ <;> tauto))

theorem slotW_sp : ∀ a ∈ slotW, a ∈ spArrs := by decide
theorem slotW_oth : ∀ a ∈ slotW, a ∉ labW ∧ a ≠ "sp.ptr" ∧ a ≠ "sp.gp" := by decide
theorem arr56_sp : ∀ a ∈ ["U", "U.len", "sp.inU"] ++ slotW, a ∈ spArrs := by decide
theorem reg56_sp : ∀ a ∈ ["px", "sp.i"] ++ "sl.i" :: "sp.cf" :: KC.ws, a ∈ spRegs := by decide

/-- The concrete word arrays written by the second half (besides the `D` layer's). -/
def wX : List String :=
  RamSpineU.rmArrs ++ labW ++ ["sp.ptr", "sp.gp", "U", "U.len", "sp.inU"] ++ slotW
/-- The concrete word registers written by the second half (besides the `D` layer's and `cmp`'s). -/
def rX : List String :=
  RamSpineU.rmRegs ++ setupW ++ WinScan.allW ++ RamSpineU.rsRegs ++ ["px", "sp.i", "sl.i", "sp.cf"] ++
    KC.ws ++ ["sp.em"]
/-- The concrete value registers written by the second half. -/
def vX : List String := ["sc.bl", "sc.ol"] ++ relaxV ++ [KC.l]

theorem wX_sp : ∀ a ∈ wX, a ∈ spArrs := by decide
theorem rX_cover : ∀ a ∈ rX, a ∈ spRegs ∨ a ∈ WinScan.allW ++ scRegs ++ ["lab.uselo", "sp.t", "sp.y"] := by
  decide

theorem nmA {T : ℕ → ℕ} (DL : DLayer G s T) {X : List String} {a : String} (h1 : a ∈ spArrs)
    (h2 : a ∉ X) : a ∉ DL.dWA ++ X :=
  fun h => (List.mem_append.mp h).elim (fun h => DL.dWA_ok _ h h1) h2

theorem nmR {T : ℕ → ℕ} (DL : DLayer G s T) {CW X : List String}
    (hcw : ∀ a ∈ CW, a ∉ DL.dWR ∧ a ∉ spRegs) {a : String} (h1 : a ∈ spRegs) (h2 : a ∉ X) :
    a ∉ DL.dWR ++ CW ++ X := fun h => by
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · exact DL.dWR_ok _ h h1
    · exact (hcw _ h).2 h1
  · exact h2 h

theorem nmV {T : ℕ → ℕ} (DL : DLayer G s T) {X : List String} {a : String}
    (h1 : a ∈ "sl.l" :: "gW" :: labV) (h2 : a ∉ X) : a ∉ DL.dVA ++ X :=
  fun h => (List.mem_append.mp h).elim (fun h => DL.dVA_ok _ h h1) h2

/-! ### Subset bookkeeping (`A`, `C` abstract, `X`, `Y`, `Z` concrete) -/

theorem ss_AX {A X Y : List String} (h : X ⊆ Y) : A ++ X ⊆ A ++ Y := fun x hx => by
  rcases List.mem_append.mp hx with h' | h'
  · exact List.mem_append_left _ h'
  · exact List.mem_append_right _ (h h')
theorem ss_X {A X Y : List String} (h : X ⊆ Y) : X ⊆ A ++ Y := fun x hx => List.mem_append_right _ (h hx)
theorem ss_A {A Y : List String} : A ⊆ A ++ Y := fun x hx => List.mem_append_left _ hx
theorem ss_XA {A X Y : List String} (h : X ⊆ Y) : X ++ A ⊆ A ++ Y := fun x hx => by
  rcases List.mem_append.mp hx with h' | h'
  · exact List.mem_append_right _ (h h')
  · exact List.mem_append_left _ h'
theorem ss_XAZ {A X Z Y : List String} (h1 : X ⊆ Y) (h2 : Z ⊆ Y) : X ++ A ++ Z ⊆ A ++ Y := fun x hx => by
  rcases List.mem_append.mp hx with h' | h'
  · exact ss_XA h1 h'
  · exact List.mem_append_right _ (h2 h')
theorem ss_AZ {A Z Y : List String} (h : Z ⊆ Y) : A ++ Z ⊆ A ++ Y := ss_AX h
-- with a second abstract block `C` in the middle of the target
theorem ss3_AX {A C X Y : List String} (h : X ⊆ Y) : A ++ X ⊆ A ++ C ++ Y := fun x hx => by
  rcases List.mem_append.mp hx with h' | h'
  · exact List.mem_append_left _ (List.mem_append_left _ h')
  · exact List.mem_append_right _ (h h')
theorem ss3_XA {A C X Y : List String} (h : X ⊆ Y) : X ++ A ⊆ A ++ C ++ Y := fun x hx => by
  rcases List.mem_append.mp hx with h' | h'
  · exact List.mem_append_right _ (h h')
  · exact List.mem_append_left _ (List.mem_append_left _ h')
theorem ss3_XCA {A C X Y : List String} (h : X ⊆ Y) : X ++ C ++ A ⊆ A ++ C ++ Y := fun x hx => by
  rcases List.mem_append.mp hx with h' | h'
  · rcases List.mem_append.mp h' with h'' | h''
    · exact List.mem_append_right _ (h h'')
    · exact List.mem_append_left _ (List.mem_append_right _ h'')
  · exact List.mem_append_left _ (List.mem_append_left _ h')
theorem ss3_X {A C X Y : List String} (h : X ⊆ Y) : X ⊆ A ++ C ++ Y :=
  fun x hx => List.mem_append_right _ (h hx)
theorem ss3_A {A C Y : List String} : A ⊆ A ++ C ++ Y :=
  fun x hx => List.mem_append_left _ (List.mem_append_left _ hx)
theorem ss3_CA {A C Y : List String} : C ++ A ⊆ A ++ C ++ Y := fun x hx => by
  rcases List.mem_append.mp hx with h' | h'
  · exact List.mem_append_left _ (List.mem_append_right _ h')
  · exact List.mem_append_left _ (List.mem_append_left _ h')
theorem ss_nil {Y : List String} : ([] : List String) ⊆ Y := fun _ h => absurd h (by simp)

/-- Word arrays written after the scan / after the re-selection (besides the `D` layer's). -/
def wX4 : List String := ["sp.gp", "U", "U.len", "sp.inU"] ++ slotW
def wX5 : List String := ["U", "U.len", "sp.inU"] ++ slotW

theorem labW_wX5 : ∀ a ∈ labW, a ∉ wX5 := by decide
theorem grp_wX5 : ∀ a ∈ grpArrs, a ∉ wX5 := by decide

theorem rowb_facts : ∀ b ∈ ["sp.gm", "sp.gl", "sp.gpos", "sp.g", "sp.mk"],
    b ∈ grpX ∧ b ∈ grpArrs ++ ["sp.mk"] ∧ b ∈ spArrs ∧ b ∉ wX4 := by decide

theorem rowArrs_sp : ∀ a ∈ rowArrs, a ∈ spArrs := by decide
theorem lenArrs_sp : ∀ a ∈ lenArrs, a ∈ spArrs := by decide
theorem rowArrs_wX : ∀ a ∈ rowArrs, a ≠ "U" → a ≠ "sp.gp" → a ≠ "sp.inU" →
    a ∉ ["sp.gm", "sp.gl", "sp.gpos", "sp.g", "sp.mk"] → a ∉ wX := by decide
theorem lenArrs_wX : ∀ a ∈ lenArrs, a ≠ "U.len" → a ≠ "sp.mk.len" → a ∉ wX := by decide

theorem arith_pre (K C x y u f : ℕ) :
    K * (x + 1) + K * (y + u + 1) + 25 * u + 18 ≤ postK K C * (x + y + 2 * u + f + 1) := by
  unfold postK; ring_nf; omega

theorem arith_scan (K C x y u f : ℕ) :
    K * (x + 1) + K * (y + u + 1) + 63 * u + 20 + (113 + K) * f ≤ postK K C * (x + y + 2 * u + f + 1) := by
  unfold postK; ring_nf; omega

theorem arith_all (K C x y u f sm mk I : ℕ) :
    K * (x + 1) + K * (y + u + 1) + 63 * u + 20 + (113 + K) * f +
      (3 + 8 * (mk + u) + sm * (C + 8) + K * I + mk * (K + 3)) + (7 * u + 2) + 14 + K ≤
      postK K C * (x + y + 2 * u + f + (sm + mk) + I + 1) := by
  unfold postK; ring_nf; omega

set_option maxHeartbeats 4000000 in
theorem postSpec (DL : DLayer G s T) (PI : PhiI Φ) (LF : ℕ) (body : Stmt) (τf Mf : ℕ → ℕ)
    (cmp : Stmt) (C : ℕ) (CW CV : List String) (Ω : Type) :
    PostSpecStmt DL PI LF body τf Mf cmp C CW CV Ω := by
  intro c0 hy hcmp hsort hLT B S d0 d1 p P0 Q W B'0 hpre hfp τ Inv subD subC l hsimsub hsubC f0 L0 c hA
    hne ks Bi g1 Dc1 cp hpull B'i Ui Dci d1' φ1 g2 lg hsubD st0 st τl Ds H hPC hbud huse
  classical
  obtain ⟨hcompA, hdisjA, hUstab, hw1, hmono1, hBiB, hPfin, hm1, hm2, hm3, hm4⟩ :=
    postA (T := T (l + 1)) hpre hfp hsimsub hsubC hA hne hpull hsubD
  have hst := hPC.stat
  have hlv : st.w "lvl" = l + 1 := hPC.lvl
  have hn : st.w "n" = G.n := hst.n
  have hLF : l + 1 ≤ LF := hPC.lvl_le
  obtain ⟨hcA, hcB, hcC, hcD, hcE⟩ := cap_facts hLF hst.cap
  obtain ⟨lUi, hUrow, hlUnd, hlU, hlUmem⟩ := SetRow.list hPC.Urow
  obtain ⟨lU, hUrow1, hlUnd1, hlU1, hlUmem1⟩ := SetRow.list hPC.U
  have hlUlen : lUi.length = Ui.card := by rw [← hlU, List.toFinset_card_of_nodup hlUnd]
  have hmemUi : ∀ u, u ∈ lUi ↔ u ∈ Ui := fun u => by rw [← hlU, List.mem_toFinset]
  set Ds' := Function.update (Function.update Ds (l + 1) Dc1) l Dci with hDs'
  set Dm := (DB.merge 1 Dc1 Dci).1 with hDm
  -- Phase 1: BM.14 merge
  unfold postProg
  apply runs_seq
  have e1 : Ds' (l + 1) = Dc1 := by
    rw [hDs', Function.update_of_ne (by omega), Function.update_self]
  have e2 : Ds' (l + 1 - 1) = Dci := by rw [Nat.add_sub_cancel, hDs', Function.update_self]
  refine runs_seq ((DL.merge_spec st H g2 Ds' (l + 1) (by omega) (by omega)
    (by rw [Nat.add_sub_cancel]; exact hPC.D) hlv hn hPC.lab.rep.hist (by rw [e1, e2]; exact hm1)
    (by rw [e1, e2]; exact hm2) (by rw [e1, e2]; exact hm3)).mono ?_)
  rintro r1 ⟨hD1, hU01, hwl1, hvl1, hc1a, hc1b, hu1⟩
  rw [e1, e2] at hD1 hc1b
  have hD1' : DL.DR r1 H g2 (Function.update Ds (l + 1) Dm) (l + 1) :=
    DL.congr _ _ _ _ _ _ (fun j hj => by
      by_cases hj' : j = l + 1
      · subst hj'; simp [hDm]
      · rw [Function.update_of_ne hj', Function.update_of_ne hj', hDs', Function.update_of_ne (by omega),
          Function.update_of_ne hj']) hD1
  have hUd : ∀ a ∈ ["U", "U.len"], a ∉ DL.dWA := fun a ha h => DL.dWA_ok a h (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl <;> decide)
  have hwR : ∀ a ∈ ["lvl", "n", "gN"], a ∉ DL.dWR := fun a ha h => DL.dWR_ok a h (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl | rfl <;> decide)
  have hlv1 : r1.w "lvl" = l + 1 := by rw [hU01.wreg _ (hwR _ (by simp))]; exact hlv
  have hn1 : r1.w "n" = G.n := by rw [hU01.wreg _ (hwR _ (by simp))]; exact hn
  -- Phase 2: BM.15 FIX-STALE deletion
  rw [show RamSpine.removeU DL.delB gDel = seq DL.delB (RamSpineU.removeTail gDel) from rfl]
  apply runs_seq
  apply runs_seq
  have hUr1 : RowRep r1 "U" "U.len" G.n (l + 1 - 1) (lUi.map Fin.val) := by
    rw [Nat.add_sub_cancel]; exact rowRep_of_unch hUrow hU01 (hUd _ (by simp)) (hUd _ (by simp))
  refine (DL.delB_spec r1 H g2 (Function.update Ds (l + 1) Dm) (l + 1) lUi (by omega) hD1' hlv1 hn1
    hUr1).mono ?_
  rintro r2 ⟨hD2, hU12, hwl2, hvl2, hc2a, hc2b, hu2⟩
  have hU02 : Unchanged st r2 DL.dWA DL.dVA DL.dWR DL.dVR := hU01.trans hU12
  have hwl02 : r2.wlen = st.wlen := hwl2.trans hwl1
  have hvl02 : r2.vlen = st.vlen := hvl2.trans hvl1
  have hlv2 : r2.w "lvl" = l + 1 := by rw [hU02.wreg _ (hwR _ (by simp))]; exact hlv
  have hn2 : r2.w "n" = G.n := by rw [hU02.wreg _ (hwR _ (by simp))]; exact hn
  -- Phase 2': BM.16–18 group removal and marks
  have hG2 : GrpRep r2 (l + 1) G.n p (liftP c.cs.P) (liftPiv c.cs.piv) :=
    RamSpineU.grpRep_of_eq hPC.grp
      (fun a ha => (hU02.warr a (fun h => DL.dWA_ok a h (grpArrs_sub_spArrs a ha))).1)
      (fun a ha => (hU02.warr a (fun h => DL.dWA_ok a h (grpArrs_sub_spArrs a ha))).2)
  have hUr2 : RowRep r2 "U" "U.len" G.n (l + 1 - 1) (lUi.map Fin.val) :=
    rowRep_of_unch hUr1 hU12 (hUd _ (by simp)) (hUd _ (by simp))
  have hmkw : (l + 1 + 1) * G.n ≤ r2.wlen "sp.mk" := by
    rw [hwl02]
    exact le_trans (Nat.mul_le_mul_right _ (by omega)) (hst.rows "sp.mk" (by decide))
  have hmklw : l + 1 < r2.wlen "sp.mk.len" := by
    rw [hwl02]; have := hst.lens "sp.mk.len" (by decide); omega
  refine (RamSpineU.removeTail_spec (ops := realOps) hlv2 (by omega) hn2 hG2 hUr2
    (List.Nodup.map Fin.val_injective hlUnd)
    (fun x hx => by obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx; exact u.isLt) hmkw hmklw
    (by rw [hU02.cap]; exact hcB)).mono ?_
  rintro r3 ⟨hG3, ⟨mks, hmk3, hmnd, hmks⟩, hwa3, hwl3, hva3, hvl3, hcap3, hpr3, hv3, hreg3, hrows3,
    hmkl3, hlv3, hn3, hc3a, hc3b⟩
  have hU23 : Unchanged r2 r3 RamSpineU.rmArrs [] RamSpineU.rmRegs [] :=
    unch_of_parts hwa3 hwl3 hva3 hvl3 hcap3 hpr3 hv3 hreg3
  have hrmR : ∀ a ∈ DL.dWR, a ∉ RamSpineU.rmRegs := fun a ha h => by
    simp only [RamSpineU.rmRegs, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact DL.dWR_ok _ ha (by decide) | exact hy.gdel.1 ha | exact hy.gdel.2 ha
  have hD3 : DL.DR r3 H (delC g2 lUi).1 (Function.update Ds (l + 1) Dm) (l + 1) :=
    DL.frame r2 r3 H H _ _ _ RamSpineU.rmArrs [] RamSpineU.rmRegs [] hD2 hU23
      (fun a ha h => DL.dWA_ok a ha (rmArrs_sub a h)) (by simp) hrmR
      (by rw [vc_of_unchanged hU23 (by decide)]; exact HExt.refl _ _)
  have hU03 : Unchanged st r3 (DL.dWA ++ RamSpineU.rmArrs) DL.dVA (DL.dWR ++ RamSpineU.rmRegs) DL.dVR :=
    (hU02.mono (by simp) (List.Subset.refl _) (by simp) (List.Subset.refl _)).trans
      (hU23.mono (by simp) (by simp) (by simp) (by simp))
  have hwl03 : r3.wlen = st.wlen := hwl3.trans hwl02
  have hvl03 : r3.vlen = st.vlen := hvl3.trans hvl02
  have hvc3 : vc (G := G) r3 = vc st := vc_of_unchanged hU03 (by
    intro h; rcases List.mem_append.mp h with h | h
    · exact DL.dWA_ok _ h (by decide)
    · exact absurd h (by decide))
  have hWA3 : ∀ a ∈ fixA, a ∉ DL.dWA ++ RamSpineU.rmArrs := by
    intro a ha h
    rcases List.mem_append.mp h with h | h
    · exact DL.dWA_ok _ h (fixA_sp a ha)
    · exact fixA_rm a ha h
  have hVA3 : ∀ a ∈ ["dlen", "sl.l", "gW"], a ∉ DL.dVA := fun a ha h => DL.dVA_ok _ h (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> simp [labV])
  have hlab3 : LabAt r3 d1' H c0 :=
    hPC.lab.of_unchanged hU03 (fun a ha => hWA3 a (by simp [fixA, ha])) (hVA3 _ (by simp)) (by omega)
  have hsl3 : ∀ i < slotB (LF + 2), SlotLens r3 i := fun i hi => SlotLens.of_len (hst.slots i hi) hwl03 hvl03
  have hslot3 : ∀ {i : ℕ} {b : WLab G s}, SlotHolds st i H (vc st) b → SlotHolds r3 i H (vc r3) b :=
    fun h => by rw [hvc3]; exact h.of_unchanged hU03 (fun a ha => hWA3 a (by simp [fixA, ha])) (hVA3 _ (by simp))
  have hUr3 : RowRep r3 "U" "U.len" G.n (l + 1 - 1) (lUi.map Fin.val) :=
    rowRep_of_unch hUr2 hU23 (by decide) (by decide)
  have hptr3 : ∀ u ∈ lUi, WinScan.PtrAt r3 (d1' u) u Bi := fun u hu => by
    have h := hPC.ptrUi u ((hmemUi u).mp hu)
    unfold PtrOK at h
    unfold WinScan.PtrAt WinScan.ScanStop
    rw [(hU03.warr "gSt" (hWA3 _ (by decide))).1, (hU03.warr "sp.ptr" (hWA3 _ (by decide))).1]
    exact h
  -- the budget of the scan: from `hbud` at a window list
  obtain ⟨L'0, hL'0nd, hL'0mem⟩ : ∃ L : List (Fin G.m), L.Nodup ∧ ∀ e, e ∈ L ↔
      G.src e ∈ Ui ∧ Bi ≤ ext (d1' (G.src e)) e ∧ ext (d1' (G.src e)) e < B :=
    ⟨(Finset.univ.filter fun e => G.src e ∈ Ui ∧ Bi ≤ ext (d1' (G.src e)) e ∧
        ext (d1' (G.src e)) e < B).toList, Finset.nodup_toList _, by intro e; simp⟩
  have hb0 := hbud lUi L'0 hlUnd hlU hL'0nd hL'0mem
  have hlUn : lUi.length ≤ G.n := by
    have := hlUnd.length_le_card; rwa [Fintype.card_fin] at this
  have hsc1 : (lUi.length + 1) * ((G.m + 1) * WinScan.CED DL.K Dm.blocks.length + 101) ≤
      postS DL.K C G.n G.m Dm.blocks.length := by
    unfold postS
    have := Nat.mul_le_mul_right ((G.m + 1) * WinScan.CED DL.K Dm.blocks.length + 101)
      (show lUi.length + 1 ≤ G.n + 1 by omega)
    omega
  have hpre0 := arith_pre DL.K C (DB.merge 1 Dc1 Dci).2 (delC g2 lUi).2 lUi.length
    (postFold (T (l + 1)) B Bi Dc1 Dci d1' g2 lUi L'0).c
  have hB3 : r3.cost + 15 + (lUi.length + 1) * ((G.m + 1) * WinScan.CED DL.K
      (⟨d1', (delC g2 lUi).1, Dm, 0⟩ : RSt G s).Dc.blocks.length + 101) ≤ c0 + r3.cap := by
    show r3.cost + 15 + (lUi.length + 1) * ((G.m + 1) * WinScan.CED DL.K Dm.blocks.length + 101) ≤
      c0 + r3.cap
    rw [hcap3, hU02.cap]
    unfold preCost at hb0
    rw [← hlUlen] at hb0
    have : r3.cost ≤ st.cost + DL.K * ((DB.merge 1 Dc1 Dci).2 + 1) +
        DL.K * ((delC g2 lUi).2 + lUi.length + 1) + 25 * (lUi.map Fin.val).length + 3 := by omega
    rw [List.length_map] at this
    have e : ((dlOps G s).merge (T (l + 1)) Dc1 Dci).2 = (DB.merge 1 Dc1 Dci).2 := rfl
    have e' : ((dlOps G s).merge (T (l + 1)) Dc1 Dci).1 = Dm := rfl
    rw [e, e'] at hb0
    omega
  have hu3 : DL.use r3 = DL.use st := by
    rw [DL.use_frame r2 r3 _ _ _ _ hU23 hrmR, hu2, hu1]
  have hpostc : ∀ (L' : List (Fin G.m)) (piv' : Fin p → Fin G.n) (lres : List (Fin G.n)),
      (postFold (T (l + 1)) B Bi Dc1 Dci d1' g2 lUi L').c +
        (insManyC (dlOps G s) (T (l + 1)) (postFold (T (l + 1)) B Bi Dc1 Dci d1' g2 lUi L').d lres
          (postFold (T (l + 1)) B Bi Dc1 Dci d1' g2 lUi L').g
          (postFold (T (l + 1)) B Bi Dc1 Dci d1' g2 lUi L').Dc).2.2 +
        (markedGroups c.cs.lit Ui).card ≤ postCost (T (l + 1)) B c.cs Bi Ui Dc1 Dci d1' g2 lUi L' lres := by
    intro L' piv' lres
    unfold postCost preCost
    have : (markedGroups c.cs.lit Ui).card ≤ ∑ j ∈ markedGroups c.cs.lit Ui, ((c.cs.P j \ Ui).card + 1) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]; omega
    omega
  have hUse3 : ∀ L' : List (Fin G.m), L'.Nodup →
      (∀ e, e ∈ L' ↔ G.src e ∈ lUi ∧ Bi ≤ ext ((⟨d1', (delC g2 lUi).1, Dm, 0⟩ : RSt G s).d (G.src e)) e ∧
        ext ((⟨d1', (delC g2 lUi).1, Dm, 0⟩ : RSt G s).d (G.src e)) e < B) →
      DL.use r3 + (L'.foldl (relaxInsCc (dlOps G s) (T (l + 1)) B (some Bi))
        ⟨d1', (delC g2 lUi).1, Dm, 0⟩).c ≤ DL.ucap + (⟨d1', (delC g2 lUi).1, Dm, 0⟩ : RSt G s).c := by
    intro L' hnd hmem
    have hmem' : ∀ e, e ∈ L' ↔ G.src e ∈ Ui ∧ Bi ≤ ext (d1' (G.src e)) e ∧ ext (d1' (G.src e)) e < B :=
      fun e => by rw [hmem e, hmemUi]
    obtain ⟨pv, hpv⟩ := exists_reselect c.cs.lit Ui (postFold (T (l + 1)) B Bi Dc1 Dci d1' g2 lUi L').d
    have h := huse lUi L' pv (reselected c.cs.lit Ui pv).toList hlUnd hlU hnd hmem' hpv
      (Finset.nodup_toList _) (Finset.toList_toFinset _)
    have h2 := hpostc L' pv (reselected c.cs.lit Ui pv).toList
    show DL.use r3 + (postFold (T (l + 1)) B Bi Dc1 Dci d1' g2 lUi L').c ≤ DL.ucap + 0
    rw [hu3]; omega
  -- Phase 3: BM.19–21 the window scan
  apply runs_seq
  refine (scanP_spec DL hy hsort hBiB (Ds := Ds) (c0 := c0) r3 ⟨d1', (delC g2 lUi).1, Dm, 0⟩ H
    (by omega) hlv3 hn3 hlab3 hD3 hw1 (graphAt_of_unchanged hU03 (hWA3 _ (by decide)) (hVA3 _ (by simp)) hst.graph)
    (CSRAt.of_unchanged hst.csr hU03 (hWA3 _ (by decide))) (hslot3 hPC.sB) (hslot3 hPC.sBi)
    (hsl3 _ (by unfold slotB; omega)) (hsl3 _ (by unfold slotBi slotB; omega))
    (by rw [hcap3, hU02.cap]; exact hcA) (by rw [hcap3, hU02.cap]; exact hcC) lUi hlUnd hUr3
    (fun u hu => hcompA u ((hmemUi u).mp hu)) hptr3 (by rw [hwl03]; exact hst.ptr)
    (by rw [hcap3, hU02.cap]; exact hcD) (by rw [hcap3, hU02.cap]; exact hcE) hB3 hm4 hUse3).mono ?_
  rintro r4 ⟨L', H', hL'nd, hL'mem, hE34, hR4, hptr4, hrest4, hU34, hc4a, hc4b, hwl4, hvl4, hu4⟩
  set fs0 : RSt G s := ⟨d1', (delC g2 lUi).1, Dm, 0⟩ with hfs0
  set fold := L'.foldl (relaxInsCc (dlOps G s) (T (l + 1)) B (some Bi)) fs0 with hfold
  have hL'mem' : ∀ e, e ∈ L' ↔ G.src e ∈ Ui ∧ Bi ≤ ext (d1' (G.src e)) e ∧ ext (d1' (G.src e)) e < B :=
    fun e => by rw [hL'mem e, hmemUi]
  have hb1 := hbud lUi L' hlUnd hlU hL'nd hL'mem'
  -- facts at `r4`
  have hgA4 : ∀ a ∈ grpX, a ∉ labW ++ DL.dWA ++ ["sp.ptr"] := by
    intro a ha h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact grpX_lab a ha (List.mem_append_left _ h)
      · exact DL.dWA_ok _ h (grpX_sp a ha)
    · exact grpX_lab a ha (List.mem_append_right _ h)
  have hG4 : GrpRep r4 (l + 1) G.n p (fun j => liftP c.cs.P j \ (lUi.map Fin.val).toFinset)
      (liftPiv c.cs.piv) :=
    RamSpineU.grpRep_of_eq hG3 (fun a ha => (hU34.warr a (hgA4 a (by simp [grpX, ha]))).1)
      (fun a ha => (hU34.warr a (hgA4 a (by simp [grpX, ha]))).2)
  have hmk4 : RowRep r4 "sp.mk" "sp.mk.len" G.n (l + 1) mks :=
    rowRep_of_unch hmk3 hU34 (hgA4 _ (by decide)) (hgA4 _ (by decide))
  have hdisjP : ∀ i j : Fin p, i ≠ j → Disjoint (c.cs.P i) (c.cs.P j) := fun i j hij =>
    Finset.disjoint_of_subset_left (hA.linv.Psub i)
      (Finset.disjoint_of_subset_right (hA.linv.Psub j) (hfp.gdisj i j hij))
  obtain ⟨hcnt1, hcnt2, hcnt3⟩ := resel_count c.cs.lit Ui hdisjP (lUi.map Fin.val) hlUmem mks hmnd hmks
  have hcnt2' : (mks.map (fun j => (liftP c.cs.P j \ (lUi.map Fin.val).toFinset).card)).sum ≤
      ∑ j ∈ markedGroups c.cs.lit Ui, (c.cs.P j \ Ui).card := hcnt2
  have hcnt3' : (mks.filter (fun j => 0 < (liftP c.cs.P j \ (lUi.map Fin.val).toFinset).card)).length ≤
      (markedGroups c.cs.lit Ui).card := hcnt3
  have hsumn : ∑ j ∈ markedGroups c.cs.lit Ui, (c.cs.P j \ Ui).card ≤ G.n :=
    sum_marked_le c.cs.lit Ui hdisjP
  have hgl4 : (mks.map (gl r4 (l + 1) G.n)).sum =
      (mks.map (fun j => (liftP c.cs.P j \ (lUi.map Fin.val).toFinset).card)).sum := by
    congr 1
    refine List.map_congr_left (fun j hj => ?_)
    exact (RamSpineU.GrpRep.card_eq hG4 ((hmks j).mp hj).1).symm
  have hblk : fold.Dc.blocks.length = Dm.blocks.length :=
    (WinScan.foldl_invs' (T := T (l + 1)) (B := B) (lo := some Bi) L' fs0 hw1).2.1
  have hmkn : mks.length ≤ G.n := hmk4.1
  obtain ⟨KR, hK4, hI, hKf⟩ := hcmp fold.d H' r4 hR4.lab
  -- Phase 4: BM.23 re-selection
  apply runs_seq
  rw [RamSpineU.ramSpine_reselect_eq]
  refine (RamSpineU.reselect_spec (ops := realOps) hI (fun a ha => ha)
    (fun h => (hy.CWd _ h).2 (by decide)) (insI_DL DL Ds (l + 1) fold.d H' c0 B)
    (fun st' r' g D hD hU hc => by
      obtain ⟨hDR, hL, hl', hn', hBd'⟩ := hD
      have hnw : ∀ y ∈ ["lvl", "n"], y ∉ RamSpineU.rsRegs ++ CW := fun y hy' h => by
        rcases List.mem_append.mp h with h | h
        · exact lvl_n_rs y hy' h
        · have := (hI.regs _ h)
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy'
          rcases hy' with rfl | rfl
          · exact this.2.1 rfl
          · exact this.2.2.1 rfl
      refine ⟨DL.frame st' r' H' H' g _ _ _ _ _ _ hDR hU (fun a ha h => DL.dWA_ok _ ha (by
          simp only [List.mem_singleton] at h; subst h; decide)) (by simp)
          (fun a ha h => by
            rcases List.mem_append.mp h with h | h
            · exact DL.dWR_ok _ ha (rsRegs_sp a h)
            · exact (hy.CWd _ h).1 ha)
          (by rw [vc_of_unchanged hU (by decide)]; exact HExt.refl _ _),
        hL.of_unchanged hU (by decide) (by simp) hc,
        by rw [hU.wreg _ (hnw _ (by simp))]; exact hl', by rw [hU.wreg _ (hnw _ (by simp))]; exact hn',
        hBd'⟩)
    hKf (fun a ha h => by
      rcases List.mem_append.mp ha with ha | ha
      · exact DL.dWR_ok _ h (rsRegs_sp a ha)
      · exact (hy.CWd _ ha).1 h) hR4.lvl hR4.nn hG4 rfl hmk4 hmnd (fun j hj => ((hmks j).mp hj).1) ?_ hK4
    ⟨hR4.dr, hR4.lab, hR4.lvl, hR4.nn, hR4.bd⟩ ?_ ?_ (fun _ _ => trivial)
    (by rw [hU34.cap, hcap3, hU02.cap]; exact hcB) ?_).mono ?_
  · -- the members of marked groups have finite labels
    intro j hj x hx
    have hjp := ((hmks j).mp hj).1
    obtain ⟨u, hu, rfl⟩ := (mem_liftP c.cs.P ⟨j, hjp⟩ x).mp (Finset.mem_sdiff.mp hx).1
    refine ⟨u.isLt, ?_⟩
    have h1 : fold.d u ≤ d1' u := foldl_d_le L' fs0 u
    exact _root_.ne_top_of_lt (lt_of_le_of_lt h1 (hPfin ⟨j, hjp⟩ u hu))
  · -- the re-selected pivots lie below the bound (`DL.ins`'s `d v < Bd`)
    intro j hj x hx hxn
    have hjp := ((hmks j).mp hj).1
    obtain ⟨u, hu, hux⟩ := (mem_liftP c.cs.P ⟨j, hjp⟩ x).mp (Finset.mem_sdiff.mp hx).1
    have hue : (⟨x, hxn⟩ : Fin G.n) = u := Fin.ext hux.symm
    rw [hue]
    exact lt_of_le_of_lt (foldl_d_le L' fs0 u) (hPfin ⟨j, hjp⟩ u hu)
  · -- the use budget of the insertions: every completion is a Layer-A re-selection
    intro pf Lf hpf hLf
    obtain ⟨pv, hpv, hLfnd, hLfset, -, -⟩ := resel_completion (cs := c.cs) hlUmem
      (fun j hne' => (hA.linv.pivots j hne').1) hdisjP hmnd hmks fold.d pf hpf Lf hLf
    have h := huse lUi L' pv Lf hlUnd hlU hL'nd hL'mem' hpv hLfnd hLfset
    have h2 := hpostc L' pv Lf
    have hLfl : Lf.length ≤ (markedGroups c.cs.lit Ui).card := by
      have := congrArg List.length hLf
      rw [List.length_map, length_filterMap_ite, List.length_map] at this
      rw [this]; exact hcnt3'
    have hu4' : DL.use r4 ≤ DL.use st + fold.c := by
      rw [← hu3]; have := hu4; simp only [hfs0] at this; omega
    have e : (postFold (T (l + 1)) B Bi Dc1 Dci d1' g2 lUi L') = fold := rfl
    rw [e] at h2
    show DL.use r4 + _ + _ ≤ _
    omega
  · -- the budget of the re-selection
    intro L hL
    have hins := (insManyC_cost_le (T := T (l + 1)) fold.d L fold.g fold.Dc).1
    rw [hblk] at hins
    have hLn : L.length ≤ G.n := hL.trans hmkn
    have hglN : (mks.map (gl r4 (l + 1) G.n)).sum ≤ G.n := by rw [hgl4]; omega
    have hK1 : DL.K * (insManyC (dlOps G s) (T (l + 1)) fold.d L fold.g fold.Dc).2.2 ≤
        DL.K * (G.n * (Nat.log 2 Dm.blocks.length + 4)) :=
      Nat.mul_le_mul_left _ (hins.trans (Nat.mul_le_mul_right _ hLn))
    have hK2 : L.length * (DL.K + 3) ≤ G.n * (DL.K + 3) := Nat.mul_le_mul_right _ hLn
    have hK3 : (mks.map (gl r4 (l + 1) G.n)).sum * (C + 8) ≤ G.n * (C + 8) :=
      Nat.mul_le_mul_right _ hglN
    have hsc := arith_scan DL.K C (DB.merge 1 Dc1 Dci).2 (delC g2 lUi).2 lUi.length fold.c
    unfold preCost at hb1
    rw [← hlUlen] at hb1
    have e : ((dlOps G s).merge (T (l + 1)) Dc1 Dci).2 = (DB.merge 1 Dc1 Dci).2 := rfl
    have e' : ((dlOps G s).merge (T (l + 1)) Dc1 Dci).1 = Dm := rfl
    rw [e, e'] at hb1
    have hfc : (postFold (T (l + 1)) B Bi Dc1 Dci d1' g2 lUi L').c = fold.c := rfl
    rw [hfc] at hb1
    unfold postS at hb1
    have h3 : r3.cost ≤ st.cost + DL.K * ((DB.merge 1 Dc1 Dci).2 + 1) +
        DL.K * ((delC g2 lUi).2 + lUi.length + 1) + 25 * lUi.length + 3 := by
      have := hc3b; rw [List.length_map] at this; omega
    have h4 : r4.cost ≤ r3.cost + 15 + (113 + DL.K) * fold.c + 38 * lUi.length + 2 := by
      have := hc4b; rw [show fs0.c = 0 from rfl, Nat.mul_zero, Nat.add_zero] at this; exact this
    rw [hU34.cap, hcap3, hU02.cap]
    omega
  · rintro r5 ⟨piv'', L, hG5, hmin5, hkeep5, hLf5, hD5, hK5, hmk5, hU45, hwl5, hvl5, hgp5, hc5a, hc5b,
      hres5⟩
    obtain ⟨hD5r, hL5, hlv5, hn5, -⟩ := hD5
    have hU05 : Unchanged st r5 (DL.dWA ++ RamSpineU.rmArrs ++ labW ++ ["sp.ptr", "sp.gp"])
        (DL.dVA ++ labV) (DL.dWR ++ RamSpineU.rmRegs ++ setupW ++ WinScan.allW ++ RamSpineU.rsRegs ++ CW)
        (DL.dVR ++ ("sc.bl" :: "sc.ol" :: relaxV) ++ CV) :=
      ((hU03.mono (by lsub) (by lsub) (by lsub) (by lsub)).trans
        (hU34.mono (by lsub) (by lsub) (by lsub) (by lsub))).trans
        (hU45.mono (by lsub) (by lsub) (by lsub) (by lsub))
    have hfix5 : ∀ a ∈ fix5, a ∉ DL.dWA ++ RamSpineU.rmArrs ++ labW ++ ["sp.ptr", "sp.gp"] := by
      intro a ha h
      have h' : a ∈ DL.dWA ∨ a ∈ RamSpineU.rmArrs ++ labW ++ ["sp.ptr", "sp.gp"] := by
        simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h ⊢
        tauto
      rcases h' with h' | h'
      · exact DL.dWA_ok _ h' (fix5_sp a ha)
      · exact fix5_oth a ha h'
    have hwl05 : r5.wlen = st.wlen := hwl5.trans (hwl4.trans hwl03)
    have hvl05 : r5.vlen = st.vlen := hvl5.trans (hvl4.trans hvl03)
    have hUr5 : RowRep r5 "U" "U.len" G.n (l + 1) (lU.map Fin.val) :=
      rowRep_of_unch hUrow1 hU05 (hfix5 _ (by decide)) (hfix5 _ (by decide))
    have hUc5 : RowRep r5 "U" "U.len" G.n (l + 1 - 1) (lUi.map Fin.val) := by
      rw [Nat.add_sub_cancel]; exact rowRep_of_unch hUrow hU05 (hfix5 _ (by decide)) (hfix5 _ (by decide))
    have hlU1len : lU.length = c.cs.U.card := by rw [← hlU1, List.toFinset_card_of_nodup hlUnd1]
    have hunion : (c.cs.U ∪ Ui).card = c.cs.U.card + Ui.card :=
      Finset.card_union_of_disjoint (disjoint_comm.mp hdisjA)
    have hunion_n : (c.cs.U ∪ Ui).card ≤ G.n := (Finset.card_le_univ _).trans (by simp)
    have hroom : (lU.map Fin.val).length + (lUi.map Fin.val).length ≤ G.n := by
      rw [List.length_map, List.length_map]; omega
    have hvc54 : vc (G := G) r5 = vc r4 := vc_of_unchanged hU45 (fun h => by
      rcases List.mem_cons.mp h with h | h
      · exact absurd h (by decide)
      · exact DL.dWA_ok _ h (by decide))
    have hsl4 : ∀ a ∈ slotW, a ∉ labW ++ DL.dWA ++ ["sp.ptr"] := fun a ha h => by
      rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · exact (slotW_oth a ha).1 h
        · exact DL.dWA_ok _ h (slotW_sp a ha)
      · exact (slotW_oth a ha).2.1 (List.mem_singleton.mp h)
    have hsl5 : ∀ a ∈ slotW, a ∉ "sp.gp" :: DL.dWA := fun a ha h => by
      rcases List.mem_cons.mp h with h | h
      · exact (slotW_oth a ha).2.2 h
      · exact DL.dWA_ok _ h (slotW_sp a ha)
    have hslV : "sl.l" ∉ labV ++ DL.dVA := fun h => by
      rcases List.mem_append.mp h with h | h
      · revert h; decide
      · exact DL.dVA_ok _ h (by simp)
    have hsBp5 : SlotHolds r5 (slotBp l) H' (vc r5) B'i := by
      have h4 := ((hslot3 hPC.sBpi).of_unchanged hU34 hsl4 hslV).ext hE34
      rw [hvc54]; exact h4.of_unchanged hU45 hsl5 (fun h => DL.dVA_ok _ h (by simp))
    -- Phase 5: BM.24 `U := U ∪ U_i`, `B' := B'_i`
    rw [RamSpineU.ramSpine_appendU_eq]
    refine (RamSpineU.appendU_spec (ops := realOps) (copyBp := copyBp)
      (Qc := fun t r => SlotHolds r (slotBp (l + 1)) H' (vc t) B'i ∧
        (∀ j, j ≠ slotBp (l + 1) → r.va "sl.l" j = t.va "sl.l" j ∧ ∀ a ∈ slotW, r.wa a j = t.wa a j) ∧
        Unchanged t r slotW ["sl.l"] ("sl.i" :: "sp.cf" :: KC.ws) [KC.l] ∧ r.wlen = t.wlen ∧
        r.vlen = t.vlen ∧ r.cost = t.cost + 14)
      hlv5 (by omega) hn5 hUr5 hUc5
      (fun x hx => by obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx; exact u.isLt) hroom
      (by rw [hwl05]; exact le_trans (Nat.mul_le_mul_right _ (by omega)) (hst.rows "sp.inU" (by decide)))
      (by rw [hU05.cap]; exact hcB) ?_).mono ?_
    · intro t ht
      obtain ⟨-, -, -, -, -, -, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, -, -, -⟩ := ht
      have hU5t : Unchanged r5 t ["U", "U.len", "sp.inU"] [] ["px", "sp.i"] [] :=
        unch_of_parts hA7 hA8 hA9 hA10 hA11 hA12 hA13 hA14
      have hvct : vc (G := G) t = vc r5 := vc_of_unchanged hU5t (by decide)
      have hwlt : t.wlen = st.wlen := hA8.trans hwl05
      have hvlt : t.vlen = st.vlen := hA10.trans hvl05
      refine copyBp_spec t hA15 (SlotLens.of_len (hst.slots _ (by unfold slotBp slotB; omega)) hwlt hvlt)
        (SlotLens.of_len (hst.slots _ (by unfold slotBp slotB; omega)) hwlt hvlt) ?_
        (by rw [hA11, hU05.cap]; exact hcA)
      rw [Nat.add_sub_cancel, hvct]
      exact hsBp5.of_unchanged hU5t (by decide) (by simp)
    · rintro r6 ⟨t, hAP, hsBp6, hF6, hU6, hwl6, hvl6, hc6⟩
      obtain ⟨hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hA17,
        hA18⟩ := hAP
      have hU5t : Unchanged r5 t ["U", "U.len", "sp.inU"] [] ["px", "sp.i"] [] :=
        unch_of_parts hA7 hA8 hA9 hA10 hA11 hA12 hA13 hA14
      have hU56 : Unchanged r5 r6 (["U", "U.len", "sp.inU"] ++ slotW) ["sl.l"]
          (["px", "sp.i"] ++ "sl.i" :: "sp.cf" :: KC.ws) [KC.l] :=
        (hU5t.mono (by lsub) (by lsub) (by lsub) (by lsub)).trans (hU6.mono (by lsub) (by lsub) (by lsub) (by lsub))
      have hvc65 : vc (G := G) r6 = vc r5 := vc_of_unchanged hU56 (by decide)
      have hD6 := DL.frame r5 r6 H' H' _ _ _ _ _ _ _ hD5r hU56
        (fun a ha h => DL.dWA_ok _ ha (arr56_sp a h)) (fun a ha h => DL.dVA_ok _ ha (by
          simp only [List.mem_singleton] at h; subst h; simp))
        (fun a ha h => DL.dWR_ok _ ha (reg56_sp a h))
        (by rw [hvc65]; exact HExt.refl _ _)
      have hlv6 : r6.w "lvl" = l + 1 := by rw [hU56.wreg _ (by decide)]; exact hlv5
      have hn6 : r6.w "n" = G.n := by rw [hU56.wreg _ (by decide)]; exact hn5
      -- Phase 6: BM.9's emptiness bit
      refine (DL.empty_spec r6 H' _ _ (l + 1) hD6 hlv6 hn6).mono ?_
      rintro r ⟨hDr, hem, hU6r, hwlr, hvlr, hcra, hcrb, hur⟩
      -- the global frame
      have hUall : Unchanged st r (DL.dWA ++ wX) (DL.dVA ++ (labV ++ ["sl.l"])) (DL.dWR ++ CW ++ rX)
          (DL.dVR ++ CV ++ vX) := by
        refine (((((hU03.mono (ss_AX (by decide)) ss_A (ss3_AX (by decide)) ss3_A).trans
          (hU34.mono (ss_XAZ (by decide) (by decide)) (ss_XA (by decide)) (ss3_XA (by decide))
            (ss3_XA (by decide)))).trans
          (hU45.mono (show ["sp.gp"] ++ DL.dWA ⊆ _ from ss_XA (by decide)) ss_A (ss3_XCA (by decide))
            ss3_CA)).trans
          (hU56.mono (ss_X (by decide)) (ss_X (by decide)) (ss3_X (by decide)) (ss3_X (by decide)))).trans
          (hU6r.mono ss_A ss_A (ss3_AX (by decide)) ss3_A))
      have hwlr' : r.wlen = st.wlen := hwlr.trans (hwl6.trans (hA8.trans hwl05))
      have hvlr' : r.vlen = st.vlen := hvlr.trans (hvl6.trans (hA10.trans hvl05))
      have hvcr : vc (G := G) r = vc r4 :=
        (vc_of_unchanged hU6r (fun h => DL.dWA_ok _ h (by decide))).trans (hvc65.trans hvc54)
      have hU4r : Unchanged r4 r (DL.dWA ++ wX4) (DL.dVA ++ ["sl.l"]) (DL.dWR ++ CW ++ rX)
          (DL.dVR ++ CV ++ vX) :=
        ((hU45.mono (show ["sp.gp"] ++ DL.dWA ⊆ _ from ss_XA (by decide)) ss_A (ss3_XCA (by decide))
            ss3_CA).trans
          (hU56.mono (ss_X (by decide)) (ss_X (by decide)) (ss3_X (by decide)) (ss3_X (by decide)))).trans
          (hU6r.mono ss_A ss_A (ss3_AX (by decide)) ss3_A)
      have hU5r : Unchanged r5 r (DL.dWA ++ wX5) (DL.dVA ++ ["sl.l"]) (DL.dWR ++ CW ++ rX)
          (DL.dVR ++ CV ++ vX) :=
        (hU56.mono (ss_X (by decide)) (ss_X (by decide)) (ss3_X (by decide)) (ss3_X (by decide))).trans
          (hU6r.mono ss_A ss_A (ss3_AX (by decide)) ss3_A)
      have hUtr : Unchanged t r (DL.dWA ++ slotW) (DL.dVA ++ ["sl.l"]) (DL.dWR ++ CW ++ rX)
          (DL.dVR ++ CV ++ vX) :=
        (hU6.mono (ss_X (by decide)) (ss_X (by decide)) (ss3_X (by decide)) (ss3_X (by decide))).trans
          (hU6r.mono ss_A ss_A (ss3_AX (by decide)) ss3_A)
      have hU5t : Unchanged r5 t ["U", "U.len", "sp.inU"] [] ["px", "sp.i"] [] :=
        unch_of_parts hA7 hA8 hA9 hA10 hA11 hA12 hA13 hA14
      have hvct : vc (G := G) t = vc r5 := vc_of_unchanged hU5t (by decide)
      have hsV : "sl.l" ∉ DL.dVA ++ ["sl.l"] → False := fun h => h (List.mem_append_right _ (by simp))
      have hdlen : "dlen" ∉ DL.dVA ++ ["sl.l"] := nmV DL (by simp [labV]) (by decide)
      have hfoldc : ∀ u, d1' u = dis (s := s) u → fold.d u = d1' u := fun u hu =>
        (WinScan.foldl_invs' (T := T (l + 1)) (B := B) (lo := some Bi) L' fs0 hw1).2.2 u hu
      -- the new pivots and the re-selected list
      obtain ⟨piv', hres, hLnd, hLset, hsel, hns⟩ := resel_completion (cs := c.cs) hlUmem
        (fun j hne' => (hA.linv.pivots j hne').1) hdisjP hmnd hmks fold.d piv'' hmin5 L hLf5
      have hLfl : L.length ≤ (markedGroups c.cs.lit Ui).card := by
        have := congrArg List.length hLf5
        rw [List.length_map, length_filterMap_ite, List.length_map] at this
        rw [this]; exact hcnt3'
      have hpivE : ∀ j < p, piv'' j = liftPiv piv' j := by
        intro j hj
        rw [show liftPiv piv' j = (piv' ⟨j, hj⟩ : ℕ) by simp [liftPiv, hj]]
        by_cases hjj : ((⟨j, hj⟩ : Fin p) : ℕ) ∈ mks ∧
            0 < (liftP c.cs.P ((⟨j, hj⟩ : Fin p) : ℕ) \ (lUi.map Fin.val).toFinset).card
        · exact (hsel ⟨j, hj⟩ hjj).symm
        · rw [hns ⟨j, hj⟩ hjj, hkeep5 j hjj]; simp [liftPiv, hj]
      -- LoopRep at `r`
      have hlvr : r.w "lvl" = l + 1 := by
        rw [hU6r.wreg _ (fun h => by
          rcases List.mem_append.mp h with h | h
          · exact DL.dWR_ok _ h (by decide)
          · exact absurd h (by decide))]; exact hlv6
      have hLr : LabAt r fold.d H' c0 :=
        hL5.of_unchanged hU5r (fun a ha => nmA DL (labW_sub_spArrs a ha) (labW_wX5 a ha)) hdlen
          (by omega)
      have hGr : GrpRep r (l + 1) G.n p (liftP (fun j => c.cs.P j \ Ui)) (liftPiv piv') := by
        have h1 : GrpRep r (l + 1) G.n p (fun j => liftP c.cs.P j \ (lUi.map Fin.val).toFinset) piv'' :=
          RamSpineU.grpRep_of_eq hG5
            (fun a ha => (hU5r.warr a (nmA DL (grpArrs_sub_spArrs a ha) (grp_wX5 a ha))).1)
            (fun a ha => (hU5r.warr a (nmA DL (grpArrs_sub_spArrs a ha) (grp_wX5 a ha))).2)
        exact grpRep_piv_congr (RamSpineU.grpRep_congr h1 (fun j _ => liftP_sdiff c.cs.P Ui _ hlUmem j))
          (fun j hj => (hpivE j hj).symm)
      have hwaR : ∀ a, a ∈ spArrs → a ∉ wX → r.wa a = st.wa a := fun a h1 h2 =>
        (hUall.warr a (nmA DL h1 h2)).1
      have hnpr : NpRep r (l + 1) p :=
        ⟨by rw [hwlr']; exact hPC.np.1, by rw [hwaR _ (by decide) (by decide)]; exact hPC.np.2⟩
      have hUrr : RowRep r "U" "U.len" G.n (l + 1) (lU.map Fin.val ++ lUi.map Fin.val) :=
        rowRep_of_unch hA1 hUtr (nmA DL (by decide) (by decide)) (nmA DL (by decide) (by decide))
      have hSetU : SetRow r "U" "U.len" (l + 1) (c.cs.U ∪ Ui) := by
        refine ⟨_, hUrr, List.Nodup.append (List.Nodup.map Fin.val_injective hlUnd1)
          (List.Nodup.map Fin.val_injective hlUnd) (fun x hx1 hx2 => ?_), fun x => ?_⟩
        · obtain ⟨u, hu, hux⟩ := (hlUmem1 x).mp hx1
          obtain ⟨v, hv, hvx⟩ := (hlUmem x).mp hx2
          have : v = u := Fin.ext (hvx.trans hux.symm)
          subst this
          exact Finset.disjoint_left.mp hdisjA hv hu
        · rw [List.mem_append, hlUmem1, hlUmem]
          constructor
          · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
            · exact ⟨u, Finset.mem_union_left _ hu, rfl⟩
            · exact ⟨u, Finset.mem_union_right _ hu, rfl⟩
          · rintro ⟨u, hu, rfl⟩
            rcases Finset.mem_union.mp hu with hu | hu
            · exact Or.inl ⟨u, hu, rfl⟩
            · exact Or.inr ⟨u, hu, rfl⟩
      have hrt : r.wa "sp.inU" = t.wa "sp.inU" := (hUtr.warr "sp.inU" (nmA DL (by decide) (by decide))).1
      have h5st : r5.wa "sp.inU" = st.wa "sp.inU" := (hU05.warr "sp.inU" (hfix5 _ (by decide))).1
      have hinUr : ∀ v : Fin G.n, r.wa "sp.inU" ((l + 1) * G.n + v) = if v ∈ c.cs.U ∪ Ui then 1 else 0 := by
        intro v
        rw [hrt]
        by_cases hv : v ∈ Ui
        · rw [if_pos (Finset.mem_union_right _ hv)]
          exact hA3 _ ((hlUmem _).mpr ⟨v, hv, rfl⟩)
        · rw [hA4 _ (fun x hx h => hv (by
              obtain ⟨u, hu, hux⟩ := (hlUmem x).mp hx
              have : (u : ℕ) = v := by omega
              rw [← Fin.ext this]; exact hu)), h5st, hPC.inU v]
          simp [Finset.mem_union, hv]
      have hne6 : slotB (l + 1) ≠ slotBp (l + 1) := by unfold slotB slotBp; omega
      have hsBr : SlotHolds r (slotB (l + 1)) H' (vc r) B := by
        have h4 := ((hslot3 hPC.sB).of_unchanged hU34 hsl4 hslV).ext hE34
        have h5 := h4.of_unchanged hU45 hsl5 (fun h => DL.dVA_ok _ h (by simp))
        have ht := h5.of_unchanged hU5t (by decide) (by simp)
        have h6 := SlotHolds.of_slot_eq ht (hF6 _ hne6).1 (hF6 _ hne6).2
        rw [hvcr]
        exact h6.of_unchanged hU6r (fun a ha h => DL.dWA_ok _ h (slotW_sp a ha))
          (fun h => DL.dVA_ok _ h (by simp))
      have hsBpr : SlotHolds r (slotBp (l + 1)) H' (vc r) B'i := by
        have e : vc (G := G) t = vc r := by rw [hvct, hvc54, hvcr]
        rw [← e]
        exact hsBp6.of_unchanged hU6r (fun a ha h => DL.dWA_ok _ h (slotW_sp a ha))
          (fun h => DL.dVA_ok _ h (by simp))
      have htaur : r.wa "cp.tau" (l + 1) = τl := by rw [hwaR _ (by decide) (by decide)]; exact hPC.tau
      have hclr : Clear r G.n (l + 1 - 1) := by
        rw [Nat.add_sub_cancel]
        refine ⟨fun l' hl' x hx => ?_, fun l' hl' x hx => ?_, fun x hx => ?_⟩
        · have hq : l' * G.n + x < (l + 1) * G.n := by
            have h1 : (l' + 1) * G.n ≤ (l + 1) * G.n := Nat.mul_le_mul_right _ (by omega)
            have h2 : (l' + 1) * G.n = l' * G.n + G.n := by ring
            omega
          have e1 : r.wa "sp.g" = r4.wa "sp.g" := (hU4r.warr "sp.g" (nmA DL (by decide) (by decide))).1
          have e2 : r4.wa "sp.g" = r3.wa "sp.g" := (hU34.warr "sp.g" (hgA4 _ (by decide))).1
          rw [e1, e2, hrows3 "sp.g" (by decide) _ (Or.inl hq),
            (hU02.warr "sp.g" (fun h => DL.dWA_ok _ h (by decide))).1]
          exact hPC.clr.g l' hl' x hx
        · have hq : l' * G.n + x < (l + 1) * G.n := by
            have h1 : (l' + 1) * G.n ≤ (l + 1) * G.n := Nat.mul_le_mul_right _ (by omega)
            have h2 : (l' + 1) * G.n = l' * G.n + G.n := by ring
            omega
          rw [hrt, hA4 _ (fun x' _ h => by omega), h5st]
          exact hPC.clr.inU l' hl' x hx
        · rw [hwaR _ (by decide) (by decide)]; exact hPC.clr.xm x hx
      have hgSt : r.wa "gSt" = r4.wa "gSt" := (hU4r.warr "gSt" (nmA DL (by decide) (by decide))).1
      have hptrr : r.wa "sp.ptr" = r4.wa "sp.ptr" := (hU4r.warr "sp.ptr" (nmA DL (by decide) (by decide))).1
      have hgSt34 : r4.wa "gSt" = r3.wa "gSt" := (hU34.warr "gSt" (fun h => by
        rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with h | h
          · exact absurd h (by decide)
          · exact DL.dWA_ok _ h (by decide)
        · exact absurd h (by decide))).1
      have hgSt03 : r3.wa "gSt" = st.wa "gSt" := (hU03.warr "gSt" (hWA3 _ (by decide))).1
      have hptr03 : r3.wa "sp.ptr" = st.wa "sp.ptr" := (hU03.warr "sp.ptr" (hWA3 _ (by decide))).1
      have hptrR : ∀ u ∈ c.cs.U ∪ Ui, PtrOK r fold.d B u := by
        intro u hu
        rcases Finset.mem_union.mp hu with hu | hu
        · have hul : u ∉ lUi := fun h => Finset.disjoint_left.mp hdisjA ((hmemUi u).mp h) hu
          have hpu : r.wa "sp.ptr" u = st.wa "sp.ptr" u := by rw [hptrr, hrest4 u hul, hptr03]
          have hdu : fold.d u = c.cs.d u := by
            have hc : c.cs.d u = dis (s := s) u := hA.linv.U_complete u hu
            rw [hfoldc u (by rw [hUstab u hu]; exact hc), hUstab u hu]
          have h := hPC.ptr u hu
          unfold PtrOK at h ⊢
          rw [hgSt, hgSt34, hgSt03, hpu, hdu]
          exact h
        · have h := hptr4 u ((hmemUi u).mpr hu)
          have hdu : fold.d u = d1' u := hfoldc u (hcompA u hu).1
          unfold WinScan.PtrAt WinScan.ScanStop at h
          unfold PtrOK
          rw [hgSt, hptrr, hdu]
          exact h
      -- the loop frame
      have hAb : Above st r G.n (l + 1) := by
        refine ⟨fun a ha i hi => ?_, fun a ha j hj => ?_, fun i hi => ?_, hwlr', hvlr'⟩
        · have hrow : ∀ b, b ∈ ["sp.gm", "sp.gl", "sp.gpos", "sp.g", "sp.mk"] → r.wa b i = st.wa b i := by
            intro b hb
            obtain ⟨hb1, hb2, hb3, hb4⟩ := rowb_facts b hb
            have e1 : r.wa b = r4.wa b := (hU4r.warr b (nmA DL hb3 hb4)).1
            have e2 : r4.wa b = r3.wa b := (hU34.warr b (hgA4 _ hb1)).1
            rw [e1, e2, hrows3 b hb2 i (Or.inr hi), (hU02.warr b (fun h => DL.dWA_ok _ h hb3)).1]
          by_cases hU' : a = "U"
          · subst hU'
            have e1 : r.wa "U" = t.wa "U" := (hUtr.warr "U" (nmA DL (by decide) (by decide))).1
            rw [e1, hA5 i (Or.inr hi), (hU05.warr "U" (hfix5 _ (by decide))).1]
          by_cases hgp' : a = "sp.gp"
          · subst hgp'
            have e1 : r.wa "sp.gp" = r5.wa "sp.gp" := (hU5r.warr "sp.gp" (nmA DL (by decide) (by decide))).1
            have e2 : r4.wa "sp.gp" = r3.wa "sp.gp" := (hU34.warr "sp.gp" (fun h => by
              rcases List.mem_append.mp h with h | h
              · rcases List.mem_append.mp h with h | h
                · exact absurd h (by decide)
                · exact DL.dWA_ok _ h (by decide)
              · exact absurd h (by decide))).1
            rw [e1, hgp5 i (Or.inr hi), e2, (hU03.warr "sp.gp" (fun h => by
              rcases List.mem_append.mp h with h | h
              · exact DL.dWA_ok _ h (by decide)
              · exact absurd h (by decide))).1]
          by_cases hin' : a = "sp.inU"
          · subst hin'
            have hle : (l + 1) * G.n + G.n ≤ i := by
              have : (l + 1 + 1) * G.n = (l + 1) * G.n + G.n := by ring
              omega
            rw [hrt, hA4 i (fun x hx h => by
              obtain ⟨u, -, hux⟩ := (hlUmem x).mp hx
              have := u.isLt; omega), h5st]
          by_cases hgr' : a ∈ ["sp.gm", "sp.gl", "sp.gpos", "sp.g", "sp.mk"]
          · exact hrow a hgr'
          · exact congrFun (hwaR a (rowArrs_sp a ha) (rowArrs_wX a ha hU' hgp' hin' hgr')) i
        · by_cases hUl : a = "U.len"
          · subst hUl
            have e1 : r.wa "U.len" = t.wa "U.len" := (hUtr.warr "U.len" (nmA DL (by decide) (by decide))).1
            rw [e1, hA6 j (by omega), (hU05.warr "U.len" (hfix5 _ (by decide))).1]
          by_cases hml : a = "sp.mk.len"
          · subst hml
            have e1 : r.wa "sp.mk.len" = r4.wa "sp.mk.len" :=
              (hU4r.warr "sp.mk.len" (nmA DL (by decide) (by decide))).1
            have e2 : r4.wa "sp.mk.len" = r3.wa "sp.mk.len" := (hU34.warr "sp.mk.len" (hgA4 _ (by decide))).1
            rw [e1, e2, hmkl3 j (by omega), (hU02.warr "sp.mk.len" (fun h => DL.dWA_ok _ h (by decide))).1]
          · exact congrFun (hwaR a (lenArrs_sp a ha) (lenArrs_wX a ha hUl hml)) j
        · have hne : i ≠ slotBp (l + 1) := by unfold slotB at hi; unfold slotBp; omega
          have hvr6 : ∀ a ∉ DL.dVA, r.va a = r6.va a := fun a ha => (hU6r.varr a ha).1
          have hwr6 : ∀ a ∈ slotW, r.wa a = r6.wa a := fun a ha =>
            (hU6r.warr a (fun h => DL.dWA_ok _ h (slotW_sp a ha))).1
          have hvt : t.va "sl.l" = st.va "sl.l" := by
            rw [(hU5t.varr "sl.l" (by simp)).1]
            exact (hU05.varr "sl.l" (fun h => by
              rcases List.mem_append.mp h with h | h
              · exact DL.dVA_ok _ h (by simp)
              · exact absurd h (by decide))).1
          have hwt : ∀ a ∈ slotW, t.wa a = st.wa a := fun a ha => by
            rw [(hU5t.warr a (fun h => by revert h; revert ha; revert a; decide)).1]
            exact (hU05.warr a (hfix5 a (by simp [fix5, ha]))).1
          refine ⟨?_, fun a ha => ?_⟩
          · rw [hvr6 _ (fun h => DL.dVA_ok _ h (by simp)), (hF6 i hne).1, hvt]
          · rw [hwr6 a ha, (hF6 i hne).2 a ha, hwt a ha]
      have hLFr : LFrame st0 r G.n l :=
        ⟨fun i h1 h2 => (congrFun (hwaR "S" (by decide) (by decide)) i).trans (hPC.frame.S i h1 h2),
          (congrFun (hwaR "S.len" (by decide) (by decide)) _).trans hPC.frame.Slen,
          fun i h1 h2 => (congrFun (hwaR "W" (by decide) (by decide)) i).trans (hPC.frame.W i h1 h2),
          (congrFun (hwaR "W.len" (by decide) (by decide)) _).trans hPC.frame.Wlen,
          hPC.frame.above.trans hAb,
          fun a ha => (hwaR a (by revert a; decide) (by revert a; decide)).trans (hPC.frame.stArr a ha)⟩
      have hptrF : ∀ x : Fin G.n, x ∉ c.cs.U ∪ Ui → r.wa "sp.ptr" x = st0.wa "sp.ptr" x := by
        intro x hx
        have hxU : x ∉ c.cs.U := fun h => hx (Finset.mem_union_left _ h)
        have hxUi : x ∉ Ui := fun h => hx (Finset.mem_union_right _ h)
        rw [hptrr, hrest4 x (fun h => hxUi ((hmemUi x).mp h)), hptr03]
        exact hPC.ptrFr x hxU hxUi
      have hphi : PI.PhiR r φ1 := PI.frame st r φ1 _ _ _ _ hPC.phi hUall
        (fun a ha h => by
          rcases List.mem_append.mp h with h | h
          · exact hy.pA a ha h
          · exact PI.pWA_ok a ha (wX_sp a h))
        (fun a ha h => by
          have hR := hy.pR a ha
          rcases List.mem_append.mp h with h | h
          · rcases List.mem_append.mp h with h | h
            · exact hR (by simp only [List.mem_append]; tauto)
            · exact hR (by simp only [List.mem_append]; tauto)
          · rcases rX_cover a h with h' | h'
            · exact PI.pWR_ok a ha h'
            · exact hR (by simp only [List.mem_append] at h' ⊢; tauto))
      -- the cost
      have h3 : r3.cost ≤ st.cost + DL.K * ((DB.merge 1 Dc1 Dci).2 + 1) +
          DL.K * ((delC g2 lUi).2 + lUi.length + 1) + 25 * lUi.length + 3 := by
        have := hc3b; rw [List.length_map] at this; omega
      have h4 : r4.cost ≤ r3.cost + 15 + (113 + DL.K) * fold.c + 38 * lUi.length + 2 := by
        have := hc4b; rw [show fs0.c = 0 from rfl, Nat.mul_zero, Nat.add_zero] at this; exact this
      have hLlen : L.length ≤ (markedGroups c.cs.lit Ui).card := hLfl
      have hglS : (mks.map (gl r4 (l + 1) G.n)).sum ≤
          ∑ j ∈ markedGroups c.cs.lit Ui, (c.cs.P j \ Ui).card := by rw [hgl4]; exact hcnt2'
      have hsum1 : ∑ j ∈ markedGroups c.cs.lit Ui, ((c.cs.P j \ Ui).card + 1) =
          ∑ j ∈ markedGroups c.cs.lit Ui, (c.cs.P j \ Ui).card + (markedGroups c.cs.lit Ui).card := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      have hall := arith_all DL.K C (DB.merge 1 Dc1 Dci).2 (delC g2 lUi).2 lUi.length fold.c
        (∑ j ∈ markedGroups c.cs.lit Ui, (c.cs.P j \ Ui).card) (markedGroups c.cs.lit Ui).card
        (insManyC (dlOps G s) (T (l + 1)) fold.d L fold.g fold.Dc).2.2
      have hm1 : mks.length * 8 ≤ 8 * ((markedGroups c.cs.lit Ui).card + lUi.length) := by
        rw [hlUlen]; omega
      have hm2 : (mks.map (gl r4 (l + 1) G.n)).sum * (C + 8) ≤
          (∑ j ∈ markedGroups c.cs.lit Ui, (c.cs.P j \ Ui).card) * (C + 8) := Nat.mul_le_mul_right _ hglS
      have hm3 : L.length * (DL.K + 3) ≤ (markedGroups c.cs.lit Ui).card * (DL.K + 3) :=
        Nat.mul_le_mul_right _ hLlen
      have hcost : r.cost ≤ st.cost + postK DL.K C *
          (postCost (T (l + 1)) B c.cs Bi Ui Dc1 Dci d1' g2 lUi L' L + 1) := by
        unfold postCost preCost
        rw [hsum1, ← hlUlen]
        have e1 : ((dlOps G s).merge (T (l + 1)) Dc1 Dci).2 = (DB.merge 1 Dc1 Dci).2 := rfl
        have e2 : (postFold (T (l + 1)) B Bi Dc1 Dci d1' g2 lUi L').c = fold.c := rfl
        have e3 : (insManyC (dlOps G s) (T (l + 1)) (postFold (T (l + 1)) B Bi Dc1 Dci d1' g2 lUi L').d L
            (postFold (T (l + 1)) B Bi Dc1 Dci d1' g2 lUi L').g
            (postFold (T (l + 1)) B Bi Dc1 Dci d1' g2 lUi L').Dc).2.2 =
            (insManyC (dlOps G s) (T (l + 1)) fold.d L fold.g fold.Dc).2.2 := rfl
        rw [e1, e2, e3]
        have h18 := hA18
        rw [List.length_map] at h18
        omega
      have hem' := hem
      rw [Function.update_self] at hem'
      have hE : HExt H (vc st) H' (vc r) := by rw [hvcr, ← hvc3]; exact hE34
      have hstat : Static r G LF body τf Mf :=
        Static.of_unchanged hst hUall hwlr' hvlr'
          (fun a ha => nmA DL (by revert ha; revert a; decide) (by revert ha; revert a; decide))
          (nmV DL (by simp) (by decide))
          (fun a ha => nmR DL hy.CWd (by revert ha; revert a; decide) (by revert ha; revert a; decide))
      -- the use counter
      have hU5use : DL.use r = DL.use r5 := by
        rw [hur]; exact DL.use_frame r5 r6 _ _ _ _ hU56 (fun a ha h => DL.dWR_ok _ ha (reg56_sp a h))
      have huseR : DL.use r ≤ DL.use st + postCost (T (l + 1)) B c.cs Bi Ui Dc1 Dci d1' g2 lUi L' L := by
        have h2 := hpostc L' piv' L
        have e : (postFold (T (l + 1)) B Bi Dc1 Dci d1' g2 lUi L') = fold := rfl
        rw [e] at h2
        have hu4' : DL.use r4 ≤ DL.use st + fold.c := by
          rw [← hu3]; have := hu4; simp only [hfs0] at this; omega
        rw [hU5use]; omega
      exact ⟨lUi, L', piv', L, H', hlUnd, hlU, hL'nd, hL'mem', hres, hLnd, hLset,
        ⟨hlvr, by omega, hLF, hstat, hLr, hDr, hphi, hGr, hnpr, hSetU, hinUr, hsBr, hsBpr, htaur, hclr,
          hptrR⟩, hem', hE, hLFr, hptrF, by omega, hcost, huseR⟩

end main

end Frontier.CHD.RamSpine
