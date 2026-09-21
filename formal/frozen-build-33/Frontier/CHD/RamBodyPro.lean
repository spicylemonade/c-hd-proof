import Frontier.CHD.RamBodyF

/-!
# Frontier.CHD.RamBodyPro — the prologue of the level body (owner: agent-01)

**NON-GATE** (B-L4, the spine's level body).  From the state after FindPivots, the prologue
`copyGrp ; pivProg ; pivIns ; b8Setup ; b8 ; U := ∅` (BM.4½–8) ends at the main loop's entry in
`LoopRep` of `CallD`'s initial configuration `cs0` (`pro_spec`, continuation style).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamBody

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.RamLevel
  Frontier.CHD.BM Frontier.CHD.RamBaseCase Frontier.CHD.LabTab Frontier.CHD.RamSpine
  Frontier.CHD.RamInit WExpr Stmt

variable {G : Graph} {s : Fin G.n} {T : ℕ → ℕ} {Φ : Type}

/-! ## Names -/

/-- The scratch registers of the level body outside `spRegs`. -/
def bodyRegs : List String :=
  cgRegs ++ ttCmpW ++ ["b8.p", "b8.sB", "b8.sBp"] ++ SpineLab.b8W ++ t6Regs ++ tstW ++
    ["f24.kh", "f24.kv", "f24.ke", "f24.kr", "f24.kf", "rz.i"]

/-- The arrays of the level body outside `spArrs`. -/
def bodyArrs : List String := ["Wp", "Wp.len"]

/-- **Name disjointness** of the level body with the D layer, B-L2 and the relaxations (checked
by `decide` on the concrete instances). -/
structure BodyNames (DL : DLayer G s T) (PI : PhiI Φ) (RW : List String) : Prop where
  dR : ∀ a ∈ DL.dWR, a ∉ bodyRegs
  dA : ∀ a ∈ DL.dWA, a ∉ bodyArrs
  pR : ∀ a ∈ PI.pWR, a ∉ bodyRegs ++ spRegs ++ DL.dWR ++ RW
  pA : ∀ a ∈ PI.pWA, a ∉ spArrs ++ bodyArrs ++ DL.dWA
  rW : "lvl" ∉ RW ∧ "n" ∉ RW ∧ "gN" ∉ RW ∧ "hp_n" ∉ RW

theorem br_cg {a : String} (h : a ∈ cgRegs) : a ∈ bodyRegs := by
  unfold bodyRegs; simp only [List.mem_append]; tauto
theorem br_tt {a : String} (h : a ∈ ttCmpW) : a ∈ bodyRegs := by
  unfold bodyRegs; simp only [List.mem_append]; tauto
theorem br_b3 {a : String} (h : a ∈ ["b8.p", "b8.sB", "b8.sBp"]) : a ∈ bodyRegs := by
  unfold bodyRegs; simp only [List.mem_append]; tauto
theorem br_b8 {a : String} (h : a ∈ SpineLab.b8W) : a ∈ bodyRegs := by
  unfold bodyRegs; simp only [List.mem_append]; tauto
theorem br_t6 {a : String} (h : a ∈ t6Regs) : a ∈ bodyRegs := by
  unfold bodyRegs; simp only [List.mem_append]; tauto
theorem br_tst {a : String} (h : a ∈ tstW) : a ∈ bodyRegs := by
  unfold bodyRegs; simp only [List.mem_append]; tauto
theorem br_f24 {a : String} (h : a ∈ ["f24.kh", "f24.kv", "f24.ke", "f24.kr", "f24.kf", "rz.i"]) :
    a ∈ bodyRegs := by
  unfold bodyRegs; simp only [List.mem_append]; tauto

theorem sa_row {a : String} (h : a ∈ rowArrs) : a ∈ spArrs := by
  unfold spArrs; simp only [List.mem_append]; tauto
theorem sa_len {a : String} (h : a ∈ lenArrs) : a ∈ spArrs := by
  unfold spArrs; simp only [List.mem_append]; tauto
theorem sa_slot {a : String} (h : a ∈ slotW) : a ∈ spArrs := by
  unfold spArrs; simp only [List.mem_append]; tauto
theorem sa_lab {a : String} (h : a ∈ labW) : a ∈ spArrs := by
  unfold spArrs; simp only [List.mem_append]; tauto
theorem sa_st {a : String} (h : a ∈ ["sp.xm", "sp.ptr", "cp.tau", "cp.M", "gSt", "gHead", "gKeep",
    "gRep", "hp_A", "hp_P"]) : a ∈ spArrs := by
  unfold spArrs; simp only [List.mem_append]; tauto

theorem pa_of {PI : PhiI Φ} {DL : DLayer G s T} {RW : List String} (hNm : BodyNames DL PI RW)
    {a : String} (h : a ∈ spArrs ∨ a ∈ DL.dWA) : a ∉ PI.pWA := fun hp =>
  hNm.pA a hp (by rcases h with h | h
                  · exact List.mem_append_left _ (List.mem_append_left _ h)
                  · exact List.mem_append_right _ h)

theorem pr_of {PI : PhiI Φ} {DL : DLayer G s T} {RW : List String} (hNm : BodyNames DL PI RW)
    {a : String} (h : a ∈ bodyRegs ∨ a ∈ spRegs ∨ a ∈ DL.dWR) : a ∉ PI.pWR := fun hp =>
  hNm.pR a hp (by rcases h with h | h | h
                  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))
                  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))
                  · exact List.mem_append_left _ (List.mem_append_right _ h))

theorem dr_of {PI : PhiI Φ} {DL : DLayer G s T} {RW : List String} (hNm : BodyNames DL PI RW)
    {a : String} (h : a ∈ bodyRegs ∨ a ∈ spRegs) : a ∉ DL.dWR := fun hd =>
  h.elim (fun hb => hNm.dR a hd hb) (fun hs => dl_spReg DL hs hd)

/-- list inclusion by membership case analysis -/
macro "lsub" : tactic => `(tactic| (intro a ha; simp (config := { failIfUnchanged := false }) only
  [List.mem_append, List.not_mem_nil, false_or, or_false] at ha ⊢; try tauto))

theorem phi_of_unch (PI : PhiI Φ) {st r : State ℝ≥0} {φ : Φ} {wa va wr vr : List String}
    (h : PI.PhiR st φ) (hU : Unchanged st r wa va wr vr) (hwa : ∀ a ∈ wa, a ∉ PI.pWA)
    (hwr : ∀ a ∈ wr, a ∉ PI.pWR) : PI.PhiR r φ :=
  PI.frame st r φ wa va wr vr h hU (fun a ha h' => hwa a h' ha) (fun a ha h' => hwr a h' ha)

theorem dr_of_unch (DL : DLayer G s T) {st r : State ℝ≥0} {H : Hist G} {g : DGl G s}
    {Ds : ℕ → DStrM G s} {lo : ℕ} {wa va wr vr : List String} (h : DL.DR st H g Ds lo)
    (hU : Unchanged st r wa va wr vr) (hwa : ∀ a ∈ wa, a ∉ DL.dWA) (hva : ∀ a ∈ va, a ∉ DL.dVA)
    (hwr : ∀ a ∈ wr, a ∉ DL.dWR) (hvc : "vcnt" ∉ wa) : DL.DR r H g Ds lo :=
  DL.frame st r H H g Ds lo wa va wr vr h hU (fun a ha h' => hwa a h' ha)
    (fun a ha h' => hva a h' ha) (fun a ha h' => hwr a h' ha)
    (by rw [vc_of_unchanged hU hvc]; exact HExt.refl _ _)

/-! ## The FindPivots groups as rows -/

section groups

variable {B : WLab G s} {S : Finset (Fin G.n)} {d d1 : Labels G s} {p : ℕ}
  {P : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {Gs : List (List (Fin G.n))}

theorem gs_getElem {j : ℕ} (hj : j < (Gs.map (List.map Fin.val)).length) :
    (Gs.map (List.map Fin.val))[j] = (Gs[j]'(by simpa using hj)).map Fin.val := by
  simp

theorem gs_dist (hfp : FPContract B S d d1 p P Q W) (hGsp : Gs.length = p)
    (hPG : ∀ j (hj : j < p), P ⟨j, hj⟩ = (Gs[j]'(by omega)).toFinset)
    (hGnd : ∀ j (hj : j < Gs.length), (Gs[j]).Nodup) :
    ∀ j (h : j < (Gs.map (List.map Fin.val)).length) q (hq : q < (Gs.map (List.map Fin.val))[j].length)
      j' (h' : j' < (Gs.map (List.map Fin.val)).length)
      q' (hq' : q' < (Gs.map (List.map Fin.val))[j'].length),
      (Gs.map (List.map Fin.val))[j][q] = (Gs.map (List.map Fin.val))[j'][q'] → j = j' ∧ q = q' := by
  intro j h q hq j' h' q' hq' e
  have hj : j < Gs.length := by simpa using h
  have hj' : j' < Gs.length := by simpa using h'
  simp only [List.getElem_map, List.length_map] at hq hq' e
  have e' : Gs[j][q] = Gs[j'][q'] := Fin.ext e
  by_cases hjj : j = j'
  · subst hjj
    exact ⟨rfl, (List.Nodup.getElem_inj_iff (hGnd j hj)).mp e'⟩
  · exfalso
    have hm : Gs[j][q] ∈ P ⟨j, by omega⟩ := by
      rw [hPG j (by omega)]; exact List.mem_toFinset.mpr (List.getElem_mem _)
    have hm' : Gs[j'][q'] ∈ P ⟨j', by omega⟩ := by
      rw [hPG j' (by omega)]; exact List.mem_toFinset.mpr (List.getElem_mem _)
    rw [e'] at hm
    exact Finset.disjoint_left.mp (hfp.gdisj ⟨j, by omega⟩ ⟨j', by omega⟩
      (fun h => hjj (congrArg Fin.val h))) hm hm'

theorem gs_ne (hfp : FPContract B S d d1 p P Q W) (hGsp : Gs.length = p)
    (hPG : ∀ j (hj : j < p), P ⟨j, hj⟩ = (Gs[j]'(by omega)).toFinset) :
    ∀ j (h : j < (Gs.map (List.map Fin.val)).length), (Gs.map (List.map Fin.val))[j] ≠ [] := by
  intro j h
  have hj : j < Gs.length := by simpa using h
  simp only [List.getElem_map, ne_eq, List.map_eq_nil_iff]
  intro he
  obtain ⟨x, hx⟩ := (hfp.groups ⟨j, by omega⟩).1
  rw [hPG j (by omega), he] at hx
  simp at hx

theorem gs_card (hGsp : Gs.length = p) (hPG : ∀ j (hj : j < p), P ⟨j, hj⟩ = (Gs[j]'(by omega)).toFinset)
    (hGnd : ∀ j (hj : j < Gs.length), (Gs[j]).Nodup) (j : Fin p) :
    (P j).card = (Gs[(j : ℕ)]'(by omega)).length := by
  rw [show P j = P ⟨j, j.2⟩ from rfl, hPG j j.2, List.toFinset_card_of_nodup (hGnd j (by omega))]

theorem gs_sum (hGsp : Gs.length = p)
    (hPG : ∀ j (hj : j < p), P ⟨j, hj⟩ = (Gs[j]'(by omega)).toFinset)
    (hGnd : ∀ j (hj : j < Gs.length), (Gs[j]).Nodup) :
    ((Gs.map (List.map Fin.val)).map List.length).sum = ∑ j, (P j).card := by
  subst hGsp
  simp only [List.map_map, Function.comp_def, List.length_map]
  rw [Finset.sum_congr rfl (fun j _ => gs_card rfl hPG hGnd j)]
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem gs_tot (hfp : FPContract B S d d1 p P Q W) (hGsp : Gs.length = p)
    (hPG : ∀ j (hj : j < p), P ⟨j, hj⟩ = (Gs[j]'(by omega)).toFinset)
    (hGnd : ∀ j (hj : j < Gs.length), (Gs[j]).Nodup) :
    ((Gs.map (List.map Fin.val)).map List.length).sum ≤ G.n := by
  classical
  rw [gs_sum hGsp hPG hGnd]
  have hdisj : ((Finset.univ : Finset (Fin p)) : Set (Fin p)).PairwiseDisjoint P :=
    fun i _ j _ hij => hfp.gdisj i j hij
  rw [← Finset.card_biUnion hdisj]
  exact (Finset.card_le_univ _).trans (by simp)

theorem grpP_eq (hGsp : Gs.length = p)
    (hPG : ∀ j (hj : j < p), P ⟨j, hj⟩ = (Gs[j]'(by omega)).toFinset) (j : ℕ) :
    grpP (Gs.map (List.map Fin.val)) j = liftP P j := by
  unfold grpP liftP
  by_cases hj : j < p
  · have hj' : j < (Gs.map (List.map Fin.val)).length := by simpa [hGsp] using hj
    rw [dif_pos hj', dif_pos hj, hPG j hj]
    ext x; simp
  · have hj' : ¬ j < (Gs.map (List.map Fin.val)).length := by simpa [hGsp] using hj
    rw [dif_neg hj', dif_neg hj]

end groups

/-- The size of a group is the length of its segment (as agent-06's `GrpRep.card_eq`). -/
theorem grp_card_eq {V : Type} {st : State V} {l n p : ℕ} {P : ℕ → Finset ℕ} {piv : ℕ → ℕ}
    (h : GrpRep st l n p P piv) {j : ℕ} (hj : j < p) : (P j).card = gl st l n j := by
  rw [h.img j hj, Finset.card_image_of_injOn]
  · simp
  · intro q hq q' hq' e
    simp only [Finset.coe_range, Set.mem_Iio] at hq hq'
    have h1 := h.pos j hj q hq
    have h2 := h.pos j hj q' hq'
    simp only at e
    rw [e] at h1
    omega

/-! ## The prologue -/

/-- The pivot comparison program (B-LAB's table–table compare). -/
abbrev cmpTTc : Stmt := IHeapLab.cmpLab IHeapLab.ttRa IHeapLab.ttRb "lab.bit"

/-- The prologue's own cost beyond the insertions (`K` = the D layer's constant). -/
def Kpro (K p σ : ℕ) : ℕ := K + 28 + (K + 53) * p + 41 * σ

/-- **The facts at the loop entry.** -/
structure ProPost (DL : DLayer G s T) (PI : PhiI Φ) (LF : ℕ) (body : Stmt) (τ Mf : ℕ → ℕ)
    (st r : State ℝ≥0) (l : ℕ) (B : WLab G s) (S : Finset (Fin G.n)) (Ds : ℕ → DStrM G s)
    (H1 : Hist G) (c0 : ℕ) (d1 : Labels G s) {p : ℕ} (P : Fin p → Finset (Fin G.n))
    (piv : Fin p → Fin G.n) (lpiv : List (Fin G.n)) (g : DGl G s) (φ1 : Φ)
    (wl : List (Fin G.n)) : Prop where
  loop : LoopRep DL PI LF body τ Mf r (l + 1) B (τ (l + 1)) Ds H1 c0
    (⟨0, cs0 (T (l + 1)) (Mf (l + 1)) B d1 P piv lpiv g, φ1⟩ : LoopCfgD G s Φ p)
  S : SetRow r "S" "S.len" (l + 1) S
  W : RowRep r "W" "W.len" G.n (l + 1) (wl.map Fin.val)
  above : Above st r G.n (l + 1)
  ptr : ∀ x, r.wa "sp.ptr" x = st.wa "sp.ptr" x
  stArr : ∀ a ∈ ["gSt", "gHead", "cp.tau", "cp.M", "gKeep", "gRep"], r.wa a = st.wa a

theorem nat_row_le {l LF n : ℕ} (h : l + 1 ≤ LF) : (l + 1 + 1) * n ≤ (LF + 2) * n :=
  Nat.mul_le_mul_right _ (by omega)

theorem cap_aux1 (LF n m : ℕ) : 8 * (LF + 3) + n + m ≤ (LF + 3) * (n + m + 8) := by nlinarith

/-- The capacity facts used by the prologue, from `Static.cap`. -/
theorem cap_aux2 {l LF n m c : ℕ} (hLF : l + 1 ≤ LF) (hc : (LF + 3) * (n + m + 8) < c) :
    (l + 1 + 1) * n + n + m + 8 < c ∧ 8 * (l + 1) + 16 < c := by
  have hA1 : (l + 1 + 1) * n ≤ (LF + 1) * n := Nat.mul_le_mul_right _ (by omega)
  have hA2 : (LF + 3) * (n + m + 8) = (LF + 1) * n + 2 * n + (LF + 3) * (m + 8) := by ring
  have hA3 : m + 8 ≤ (LF + 3) * (m + 8) := Nat.le_mul_of_pos_left _ (by omega)
  have hA4 := cap_aux1 LF n m
  omega

set_option maxHeartbeats 2000000 in
/-- **The prologue** (BM.4½–8, continuation style): from the state after FindPivots, the
prologue reaches the loop entry with `LoopRep` of `CallD`'s initial configuration. -/
theorem pro_spec (DL : DLayer G s T) (PI : PhiI Φ) {RW : List String} (hNm : BodyNames DL PI RW)
    {LF : ℕ} {body : Stmt} {τ Mf : ℕ → ℕ} {st r1 : State ℝ≥0} {l : ℕ} {B : WLab G s}
    {S : Finset (Fin G.n)} {d : Labels G s} {Ds : ℕ → DStrM G s} {g : DGl G s} {H1 : Hist G}
    {c0 : ℕ} {d1 : Labels G s} {p : ℕ} {P : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)}
    {φ1 : Φ} {Gs : List (List (Fin G.n))} {wl : List (Fin G.n)} {rest : Stmt}
    {Qf : State ℝ≥0 → Prop}
    (hpre : CallPre B S d) (hfp : FPContract B S d d1 p P Q W)
    (hGsp : Gs.length = p) (hPG : ∀ j (hj : j < p), P ⟨j, hj⟩ = (Gs[j]'(by omega)).toFinset)
    (hGnd : ∀ j (hj : j < Gs.length), (Gs[j]).Nodup)
    (hGO : PartitionRAM.GrpOut r1 (Gs.map (List.map Fin.val)))
    (hGl : (Gs.map List.length).sum ≤ r1.wlen "pt.GV" ∧ Gs.length ≤ r1.wlen "pt.GO" ∧
      Gs.length ≤ r1.wlen "pt.GL")
    (hW1 : RowRep r1 "W" "W.len" G.n (l + 1) (wl.map Fin.val))
    (hL1 : LabAt r1 d1 H1 c0) (hPhi : PI.PhiR r1 φ1) (hD1 : DL.DR r1 H1 g Ds (l + 1 + 1))
    (hF : FPFrame st r1 LF body τ Mf (l + 1) S) (hLF : l + 1 ≤ LF)
    (hsB : SlotHolds r1 (slotB (l + 1)) H1 (vc r1) B)
    (hbud : r1.cost + 5 + 15 * p + 41 * (∑ j, (P j).card) ≤ c0 + r1.cap)
    (hM2 : 2 * Mf (l + 1) + 2 < r1.cap)
    (hUbud : ∀ piv : Fin p → Fin G.n, (∀ j, piv j ∈ P j ∧ ∀ x ∈ P j, d1 (piv j) ≤ d1 x) →
      DL.use r1 + 1 + (initD (dlOps G s) (T (l + 1)) (Mf (l + 1)) B d1 (List.ofFn piv) g).2.2 + p ≤
        DL.ucap)
    (hK : ∀ (r7 : State ℝ≥0) (piv : Fin p → Fin G.n) (lpiv : List (Fin G.n)),
      (∀ j, piv j ∈ P j ∧ ∀ x ∈ P j, d1 (piv j) ≤ d1 x) → lpiv.Nodup →
      lpiv.toFinset = Finset.univ.image piv →
      ProPost DL PI LF body τ Mf st r7 l B S Ds H1 c0 d1 P piv lpiv g φ1 wl →
      vc (G := G) r7 = vc r1 → r1.cost ≤ r7.cost →
      r7.cost ≤ r1.cost + Kpro DL.K p (∑ j, (P j).card) +
        DL.K * (initD (dlOps G s) (T (l + 1)) (Mf (l + 1)) B d1 lpiv g).2.2 →
      DL.use r7 ≤ DL.use r1 + 1 + (initD (dlOps G s) (T (l + 1)) (Mf (l + 1)) B d1 lpiv g).2.2 + p →
      r7.cap = r1.cap → Runs realOps rest r7 Qf) :
    Runs realOps (seq copyGrp (seq (pivProg cmpTTc) (seq (pivIns DL.new DL.ins)
      (seq b8Setup (seq SpineLab.b8Prog (seq (rowReset "U.len") rest)))))) r1 Qf := by
  classical
  have hst1 := hF.stat
  have hl1 := hF.lvl
  have hn1 : r1.w "n" = G.n := hst1.n
  have hcapS := hst1.cap
  have hrowle := nat_row_le (n := G.n) hLF
  obtain ⟨hcapA, hcapB⟩ := cap_aux2 hLF hcapS
  have hn2 : (l + 1 + 1) * G.n = (l + 1) * G.n + G.n := Nat.succ_mul _ _
  set Gs' := Gs.map (List.map Fin.val) with hGs'
  have hGs'l : Gs'.length = p := by simp [hGs', hGsp]
  have hsumGs : (Gs'.map List.length).sum = ∑ j, (P j).card := gs_sum hGsp hPG hGnd
  have htot : (Gs'.map List.length).sum ≤ G.n := gs_tot hfp hGsp hPG hGnd
  -- (1) copyGrp
  have hCg : CgHyp r1 (l + 1) G.n Gs' := by
    refine ⟨hGO, hl1, hn1, ?_, gs_dist hfp hGsp hPG hGnd, gs_ne hfp hGsp hPG, htot,
      fun x hx => hF.clr.g (l + 1) le_rfl x hx, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j h q hq
      simp only [hGs', List.getElem_map]; exact Fin.isLt _
    · exact le_trans hrowle (hst1.rows _ (by simp [rowArrs]))
    · exact le_trans hrowle (hst1.rows _ (by simp [rowArrs]))
    · exact le_trans hrowle (hst1.rows _ (by simp [rowArrs]))
    · exact le_trans hrowle (hst1.rows _ (by simp [rowArrs]))
    · exact le_trans hrowle (hst1.rows _ (by simp [rowArrs]))
    · exact le_trans hrowle (hst1.rows _ (by simp [rowArrs]))
    · have := hst1.lens "sp.np" (by simp [lenArrs]); omega
    · simp only [hGs', List.map_map, Function.comp_def, List.length_map]; exact hGl.1
    · simpa [hGs'] using hGl.2.1
    · simpa [hGs'] using hGl.2.2
    · omega
  refine runs_seq ((copyGrp_spec (ops := realOps) hCg).mono ?_)
  rintro r2 ⟨hG2, hNp2, hU12, hwl2, hrows2, hnp2, hc2⟩
  rw [hGs'l] at hG2 hNp2
  have hl2 : r2.w "lvl" = l + 1 := by rw [hU12.wreg _ (by simp [cgRegs])]; exact hl1
  have hn2' : r2.w "n" = G.n := by rw [hU12.wreg _ (by simp [cgRegs])]; exact hn1
  have hvc2 : vc (G := G) r2 = vc r1 := vc_of_unchanged hU12 (by simp [cgArrs])
  have hcap2 : r2.cap = r1.cap := hU12.cap
  have hL2 : LabAt r2 d1 H1 c0 := hL1.of_unchanged hU12 (by simp [cgArrs, labW]) (by simp) (by omega)
  have hGr2 : GraphAt r2 G := graphAt_of_unchanged hU12 (by simp [cgArrs]) (by simp) hst1.graph
  -- sums of group sizes
  have hgl2 : ∀ j (hj : j < p), gl r2 (l + 1) G.n j = (P ⟨j, hj⟩).card := by
    intro j hj
    rw [← grp_card_eq hG2 hj, grpP_eq hGsp hPG, liftP, dif_pos hj, Finset.card_map]
  have hsum2 : ∑ j ∈ Finset.range p, gl r2 (l + 1) G.n j = ∑ j, (P j).card := by
    rw [Finset.sum_range]; exact Finset.sum_congr rfl (fun j _ => hgl2 j j.2)
  -- (2) pivProg
  have hKR2 : KRp d1 H1 (vc r1) c0 r1.cap (fun _ => True) r2 :=
    ⟨⟨hL2, hvc2, hGr2, by rw [hcap2]; omega⟩, hcap2, trivial⟩
  have hI := cmpI_tt d1 H1 (vc r1) c0 r1.cap (fun _ => True) (fun _ _ _ _ _ => trivial)
  have hne : ∀ j < p, 0 < gl r2 (l + 1) G.n j := by
    intro j hj; rw [hgl2 j hj]; exact Finset.card_pos.mpr (hfp.groups _).1
  have hdom : ∀ j < p, ∀ x ∈ grpP Gs' j, ∃ h : x < G.n, d1 ⟨x, h⟩ ≠ ⊤ := by
    intro j hj x hx
    rw [grpP_eq hGsp hPG] at hx
    obtain ⟨u, hu, rfl⟩ := (mem_liftP P ⟨j, hj⟩ x).mp hx
    refine ⟨u.2, BM.ne_top_of_lt (lt_of_le_of_lt (hfp.le u) (hpre.inRange u ((hfp.groups _).2 hu)))⟩
  refine runs_seq ((pivProg_spec (ops := realOps) hI (fun a ha => ha) (by simp) r2 hG2 hl2 hn2'
    hNp2.2 hNp2.1 hne hdom hKR2 (by rw [hcap2]; omega) (by rw [hcap2]; omega)
    (by rw [hsum2, hc2, hsumGs, hGs'l]; omega)).mono ?_)
  rintro r3 ⟨hG3, hpiv3, hKR3, hU23, hgp3, hwl3, hc3a, hc3b⟩
  have hvl3 : r3.vlen = r2.vlen := funext fun a => (hU23.varr a (by simp)).2
  have hvl2 : r2.vlen = r1.vlen := funext fun a => (hU12.varr a (by simp)).2
  have hl3 : r3.w "lvl" = l + 1 := by
    rw [hU23.wreg _ (by simp [pvRegs, gmRegs, ttCmpW, IHeapLab.cmpScratchW])]; exact hl2
  have hn3 : r3.w "n" = G.n := by
    rw [hU23.wreg _ (by simp [pvRegs, gmRegs, ttCmpW, IHeapLab.cmpScratchW])]; exact hn2'
  have hcap3 : r3.cap = r1.cap := hU23.cap.trans hcap2
  have hvc3 : vc (G := G) r3 = vc r1 := (vc_of_unchanged hU23 (by simp)).trans hvc2
  have hnp3 : r3.wa "sp.np" (l + 1) = p := by rw [(hU23.warr _ (by simp)).1]; exact hNp2.2
  have hnpl3 : l + 1 < r3.wlen "sp.np" := by rw [hwl3]; exact hNp2.1
  have hL3 : LabAt r3 d1 H1 c0 := hKR3.1.1
  -- the pivots
  have hpvlt : ∀ j : Fin p, r3.wa "sp.gp" ((l + 1) * G.n + j) < G.n := by
    intro j
    have hm := (hpiv3 j j.2).1
    rw [grpP_eq hGsp hPG] at hm
    obtain ⟨u, -, hu⟩ := (mem_liftP P j _).mp hm
    rw [← hu]; exact u.2
  set piv : Fin p → Fin G.n := fun j => ⟨r3.wa "sp.gp" ((l + 1) * G.n + j), hpvlt j⟩ with hpivdef
  have hpiv : ∀ j, piv j ∈ P j ∧ ∀ x ∈ P j, d1 (piv j) ≤ d1 x := by
    intro j
    obtain ⟨hm, hmin⟩ := hpiv3 j j.2
    rw [grpP_eq hGsp hPG] at hm hmin
    obtain ⟨u, hu, hue⟩ := (mem_liftP P j _).mp hm
    have hpu : piv j = u := Fin.ext hue.symm
    refine ⟨hpu ▸ hu, fun x hx => ?_⟩
    have := hmin x ((mem_liftP P j x).mpr ⟨x, hx, rfl⟩)
    simp only [keyOf, dif_pos (hpvlt j), dif_pos x.2] at this
    exact this
  have hinj : Function.Injective piv := by
    intro i j hij
    by_contra hne
    exact Finset.disjoint_left.mp (hfp.gdisj i j hne) (hpiv i).1 (hij ▸ (hpiv j).1)
  have hlpnd : (List.ofFn piv).Nodup := List.nodup_ofFn.mpr hinj
  have hlp : (List.ofFn piv).toFinset = Finset.univ.image piv := by
    ext x; simp [List.mem_ofFn]
  -- (3) pivIns: the new structure and the pivots
  have hU13 : Unchanged r1 r3 (cgArrs ++ ["sp.gp"]) [] (cgRegs ++ (pvRegs ++ ttCmpW))
      IHeapLab.lessV :=
    (hU12.mono (by simp) (by simp) (by simp) (by simp)).trans
      (hU23.mono (by simp) (by simp) (by simp) (by simp))
  have hsp13 : ∀ a ∈ cgArrs ++ ["sp.gp"], a ∈ spArrs := by
    intro a ha
    simp only [cgArrs, List.cons_append, List.nil_append, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at ha
    rcases ha with h | h | h | h | h | h | h <;> subst h <;> simp [spArrs, rowArrs, lenArrs]
  have hbr13 : ∀ a ∈ cgRegs ++ (pvRegs ++ ttCmpW), a ∈ bodyRegs ∨ a ∈ spRegs := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact Or.inl (br_cg h)
    · rcases List.mem_append.mp h with h | h
      · right
        simp only [pvRegs, gmRegs, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at h
        rcases h with h | h | h | h | h | h <;> subst h <;> simp [spRegs]
      · exact Or.inl (br_tt h)
  have hD3 : DL.DR r3 H1 g Ds (l + 1 + 1) :=
    dr_of_unch DL hD1 hU13 (fun a ha => dl_spArr DL (hsp13 a ha)) (by simp)
      (fun a ha h => (hbr13 a ha).elim (fun hb => hNm.dR a h hb) (fun hs => dl_spReg DL hs h))
      (by simp [cgArrs])
  have hM3 : r3.wa "cp.M" (l + 1) = Mf (l + 1) := by
    rw [(hU13.warr _ (by simp [cgArrs])).1]; exact hst1.Mv _ (by omega)
  have hsB3 : SlotHolds r3 (slotB (l + 1)) H1 (vc r3) B := by
    rw [hvc3]; exact hsB.of_unchanged hU13 (by simp [cgArrs, slotW]) (by simp)
  have hFRp : ∀ a ∈ DL.dWR, a ∉ piRegs := fun a ha h =>
    dl_spReg DL (by simp [piRegs] at h; rcases h with rfl | rfl <;> simp [spRegs]) ha
  have hNI := dNewI_of DL H1 Ds (l + 1) d1 c0 (fun _ => True) (Mf (l + 1)) B
    (fun _ _ _ _ _ _ _ => trivial)
  have hII := dInsI_of DL H1 Ds (l + 1) d1 c0 (fun _ => True) (FR := piRegs) B
    (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial) hFRp (by simp [piRegs])
    (by simp [piRegs])
  have hMl3 : l + 1 < r3.wlen "cp.M" := by
    rw [hwl3, hwl2]; have := hst1.Ml; omega
  have hsBl3 : SlotLens r3 (slotB (l + 1)) := by
    have h := hst1.slots (slotB (l + 1)) (by unfold slotB; omega)
    exact slotLens_of_unch h hU13 (by rw [hwl3, hwl2]) (by rw [hvl3, hvl2])
  have hus3 : DL.use r3 = DL.use r1 := DL.use_frame r1 r3 _ _ _ _ hU13
    (fun a ha h => (hbr13 a h).elim (fun hb => hNm.dR a ha hb) (fun hs => dl_spReg DL hs ha))
  have hPv : ∀ j, d1 (piv j) < B := fun j =>
    lt_of_le_of_lt (hfp.le _) (hpre.inRange _ ((hfp.groups j).2 (hpiv j).1))
  have hgpl3 : (l + 1) * G.n + p ≤ r3.wlen "sp.gp" := by
    have := hG3.len_gp; have := hG3.p_le; rw [hn2] at *; omega
  refine runs_seq ((pivIns_spec (ops := realOps) hNI hII
    (fun a ha => ⟨fun h => dl_spReg DL (by simp [spRegs]) (h ▸ ha),
      fun h => dl_spReg DL (by simp [spRegs]) (h ▸ ha)⟩)
    (fun a ha => ⟨fun h => dl_spArr DL (by simp [spArrs, rowArrs]) (h ▸ ha),
      fun h => dl_spArr DL (by simp [spArrs, lenArrs]) (h ▸ ha)⟩)
    r3 g ⟨hD3, hL3, hl3, hn3, hM3, hMl3, by rw [hcap3]; exact hM2, hsB3, hsBl3, trivial⟩ piv hl3 hn3 hnp3 hnpl3
    (fun j hj => rfl) hgpl3 (by rw [hcap3]; have := hG3.p_le; omega)
    (fun k _ => by show (BM.insManyC _ _ _ _ _ _).2.1.Bd = B; rw [insManyC_Bd']; rfl) hPv
    (by rw [hus3]; exact hUbud piv hpiv)).mono ?_)
  rintro r4 ⟨⟨hD4, hL4, hl4, hn4, -⟩, hU34, hc4a, hc4b, hwl4, hvl4, hu4⟩
  have hcap4 : r4.cap = r1.cap := hU34.cap.trans hcap3
  have hvc4 : vc (G := G) r4 = vc r1 :=
    (vc_of_unchanged hU34 (by simp only [List.mem_append, or_self]; exact dl_vcnt DL)).trans hvc3
  have hnDA : ∀ a ∈ spArrs, a ∉ DL.dWA ++ DL.dWA := fun a ha => by
    simp only [List.mem_append, or_self]; exact dl_spArr DL ha
  have hwa34 : ∀ a ∈ spArrs, r4.wa a = r3.wa a := fun a ha => (hU34.warr a (hnDA a ha)).1
  have hnp4 : r4.wa "sp.np" (l + 1) = p := by rw [hwa34 _ (by simp [spArrs, lenArrs])]; exact hnp3
  have hnpl4 : l + 1 < r4.wlen "sp.np" := by rw [hwl4]; exact hnpl3
  -- (4) b8Setup
  have e1 : evalW r4 (load "sp.np" (var "lvl")) = some p := by
    simp [hl4, hnp4, hnpl4]
  refine runs_seq (runs_seq (runs_wset (a := p) e1 (runs_seq (runs_wset (a := 4 * (l + 1))
    (by simp [hl4, fit_of_lt (show 4 < r4.cap by rw [hcap4]; omega),
      fit_of_lt (show 4 * (l + 1) < r4.cap by rw [hcap4]; omega)])
    (runs_wset (a := 4 * (l + 1) + 2)
    (by simp [hl4, fit_of_lt (show 4 < r4.cap by rw [hcap4]; omega),
      fit_of_lt (show 4 * (l + 1) < r4.cap by rw [hcap4]; omega),
      fit_of_lt (show 2 < r4.cap by rw [hcap4]; omega),
      fit_of_lt (show 4 * (l + 1) + 2 < r4.cap by rw [hcap4]; omega)]) ?_)))))
  set r5 := (((((r4.setW "b8.p" p).charge 1).setW "b8.sB" (4 * (l + 1))).charge 1).setW "b8.sBp"
    (4 * (l + 1) + 2)).charge 1 with hr5
  have hU45 : Unchanged r4 r5 [] [] ["b8.p", "b8.sB", "b8.sBp"] [] := by
    rw [hr5, unch_charge, Frontier.RAM.unch_setW (by simp), unch_charge,
      Frontier.RAM.unch_setW (by simp), unch_charge, Frontier.RAM.unch_setW (by simp)]
    exact Unchanged.refl _ _ _ _ _
  have hc5 : r5.cost = r4.cost + 3 := by simp [hr5]
  have hwl5 : r5.wlen = r4.wlen := by simp [hr5]
  have hvl5 : r5.vlen = r4.vlen := by simp [hr5]
  have hcap5 : r5.cap = r1.cap := by simp [hr5, hcap4]
  have hvc5 : vc (G := G) r5 = vc r1 := by rw [← hvc4]; rfl
  -- the composite frame so far
  set WA := cgArrs ++ ["sp.gp"] ++ (DL.dWA ++ DL.dWA) with hWA
  set VA := ([] : List String) ++ (DL.dVA ++ DL.dVA) with hVA
  set WR := cgRegs ++ (pvRegs ++ ttCmpW) ++ (piRegs ++ DL.dWR ++ DL.dWR) ++ ["b8.p", "b8.sB", "b8.sBp"]
    with hWR
  set VR := IHeapLab.lessV ++ (DL.dVR ++ DL.dVR) with hVR
  have hU15 : Unchanged r1 r5 WA VA WR VR := by
    rw [hWA, hVA, hWR, hVR]
    refine ((hU13.mono ?_ ?_ ?_ ?_).trans (hU34.mono ?_ ?_ ?_ ?_)).trans (hU45.mono ?_ ?_ ?_ ?_) <;>
      lsub
  have nWA : ∀ a, a ∈ spArrs → a ∉ cgArrs → a ≠ "sp.gp" → a ∉ WA := by
    intro a h1 h2 h3 h
    rw [hWA] at h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact h2 h
      · exact h3 (List.mem_singleton.mp h)
    · rcases List.mem_append.mp h with h | h <;> exact dl_spArr DL h1 h
  have nWR : ∀ a, a ∈ spRegs → a ∉ cgRegs ++ (pvRegs ++ ttCmpW) → a ∉ piRegs →
      a ∉ ["b8.p", "b8.sB", "b8.sBp"] → a ∉ WR := by
    intro a h1 h2 h3 h4 h
    rw [hWR] at h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact h2 h
      · rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with h | h
          · exact h3 h
          · exact dl_spReg DL h1 h
        · exact dl_spReg DL h1 h
    · exact h4 h
  have hl5 : r5.w "lvl" = l + 1 := by simp [hr5, hl4]
  have hgN5 : r5.w "gN" = G.n := by
    rw [hU15.wreg _ (nWR _ (by simp [spRegs]) (by decide) (by decide) (by decide))]; exact hst1.gN
  have hwl15 : r5.wlen = r1.wlen := by rw [hwl5, hwl4, hwl3, hwl2]
  have hvl15 : r5.vlen = r1.vlen := by rw [hvl5, hvl4, hvl3, hvl2]
  have hsl1 : ∀ i < slotB (LF + 2), SlotLens r5 i := fun i hi =>
    slotLens_of_unch (hst1.slots i hi) hU15 hwl15 hvl15
  have hpv5 : ∀ j (hj : j < p), r5.wa "sp.gp" ((l + 1) * G.n + j) = piv ⟨j, hj⟩ := by
    intro j hj
    have e : r5.wa "sp.gp" = r3.wa "sp.gp" := by
      simp only [hr5, State.charge_wa, State.setW_wa]
      exact hwa34 _ (by simp [spArrs, rowArrs])
    rw [e]
  have hgp5 : (l + 1) * G.n + p ≤ r5.wlen "sp.gp" := by rw [hwl5, hwl4]; exact hgpl3
  have hsB5 : SlotHolds r5 (slotB (l + 1)) H1 (vc r5) B := by
    rw [hvc5]; exact hsB.of_unchanged hU15 (fun a ha => nWA a (by simp [spArrs, ha]) (by
      simp [slotW] at ha; rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide) (by
      simp [slotW] at ha; rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide))
      (by simp only [hVA, List.nil_append, List.mem_append, or_self]; exact dl_sll DL)
  have hL5 : LabAt r5 d1 H1 c0 := hL4.of_unchanged hU45 (by simp) (by simp) (by omega)
  -- (5) BM.8
  have hslot_lt : ∀ k < 4, 4 * (l + 1) + k < slotB (LF + 2) := fun k hk => by
    unfold slotB; omega
  refine runs_seq ((Runs.cost_mono (Runs.lens (by decide) (SpineLab.b8Prog_spec r5 d1 H1 c0 hL5 piv (l + 1) G.n
    hl5 hgN5 (by simp [hr5]) hpv5 hgp5 (slotB (l + 1)) (slotBp (l + 1)) (by simp [hr5, slotB])
    (by simp [hr5, slotBp]) (hsl1 _ (by have := hslot_lt 0 (by omega); simpa [slotB] using this))
    (hsl1 _ (by have := hslot_lt 2 (by omega); simpa [slotBp, slotB] using this)) B hsB5
    (by rw [hcap5]; have := hG3.p_le; omega)))).mono ?_)
  rintro r6 ⟨⟨⟨hsBp6, hL6, hsl6, hU56, hc6⟩, hwl6, hvl6⟩, hc6a⟩
  have hl6 : r6.w "lvl" = l + 1 := by rw [hU56.wreg _ (by simp [SpineLab.b8W])]; exact hl5
  have hwl16 : r6.wlen = r1.wlen := hwl6.trans hwl15
  have hUlen6 : l + 1 < r6.wlen "U.len" := by
    rw [hwl16]; have := hst1.lens "U.len" (by simp [lenArrs]); omega
  have hUl6 : (l + 1 + 1) * G.n ≤ r6.wlen "U" := by
    rw [hwl16]; exact le_trans hrowle (hst1.rows _ (by simp [rowArrs]))
  -- (6) U := ∅
  refine runs_seq ((Runs.lens (by decide) (rowReset_spec (ops := realOps) r6 (arr := "U")
    (n := G.n) (l := l + 1) hl6 hUlen6 hUl6 (by rw [hU56.cap, hcap5]; omega))).mono ?_)
  rintro r7 ⟨⟨hUrow7, hU67, hlen7, hwa7, hc7⟩, hwl7, hvl7⟩
  -- the composite frame r1 → r7
  have hU17 : Unchanged r1 r7 (WA ++ slotW ++ ["U.len"]) (VA ++ ["sl.l"]) (WR ++ SpineLab.b8W)
      (VR ++ SpineLab.b8V) := by
    refine ((hU15.mono ?_ ?_ ?_ ?_).trans (hU56.mono ?_ ?_ ?_ ?_)).trans (hU67.mono ?_ ?_ ?_ ?_) <;>
      lsub
  have nWA7 : ∀ a, a ∈ spArrs → a ∉ cgArrs → a ≠ "sp.gp" → a ∉ slotW → a ≠ "U.len" →
      a ∉ WA ++ slotW ++ ["U.len"] := by
    intro a h1 h2 h3 h4 h5 h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact nWA a h1 h2 h3 h
      · exact h4 h
    · exact h5 (List.mem_singleton.mp h)
  have nWR7 : ∀ a, a ∈ spRegs → a ∉ cgRegs ++ (pvRegs ++ ttCmpW) → a ∉ piRegs →
      a ∉ ["b8.p", "b8.sB", "b8.sBp"] → a ∉ SpineLab.b8W → a ∉ WR ++ SpineLab.b8W := by
    intro a h1 h2 h3 h4 h5 h
    rcases List.mem_append.mp h with h | h
    · exact nWR a h1 h2 h3 h4 h
    · exact h5 h
  have hVA7 : ∀ a, a ∉ DL.dVA → a ≠ "sl.l" → a ∉ VA ++ ["sl.l"] := by
    intro a h1 h2 h
    simp only [hVA, List.nil_append, List.mem_append, or_self, List.mem_singleton] at h
    rcases h with h | h
    · exact h1 h
    · exact h2 h
  have hwl17 : r7.wlen = r1.wlen := hwl7.trans hwl16
  have hvl17 : r7.vlen = r1.vlen := hvl7.trans (hvl6.trans hvl15)
  have hunA : ∀ a, a ∈ spArrs → a ∉ cgArrs → a ≠ "sp.gp" → a ∉ slotW → a ≠ "U.len" →
      r7.wa a = r1.wa a := fun a h1 h2 h3 h4 h5 => (hU17.warr a (nWA7 a h1 h2 h3 h4 h5)).1
  have hl7 : r7.w "lvl" = l + 1 := by rw [hU67.wreg _ (by simp)]; exact hl6
  have hvc7 : vc (G := G) r7 = vc r1 := by
    have := hunA "vcnt" (by simp [spArrs, labW]) (by simp [cgArrs]) (by simp) (by simp [slotW])
      (by simp)
    funext v; simp [vc, this]
  have hvc57 : vc (G := G) r7 = vc r5 := hvc7.trans hvc5.symm
  have hst7 : Static r7 G LF body τ Mf := by
    refine static_frame hst1 (fun a _ => by rw [hwl17]) (by rw [hvl17])
      (fun a ha => ?_) (hU17.varr _ (hVA7 _ (fun h => DL.dVA_ok _ h (by simp)) (by simp))).1
      (by rw [hvl17]) (hU17.wreg _ (nWR7 _ (by simp [spRegs]) (by decide) (by decide) (by decide)
        (by decide))) (hU17.wreg _ (nWR7 _ (by simp [spRegs]) (by decide) (by decide) (by decide)
        (by decide))) (hU17.wreg _ (nWR7 _ (by simp [spRegs]) (by decide) (by decide) (by decide)
        (by decide))) hU17.procs hU17.cap
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;>
      exact hunA _ (by simp [spArrs]) (by simp [cgArrs]) (by simp) (by simp [slotW]) (by simp)
  -- the name classes of the prologue's writes (for the frames of D and B-L2)
  have cA : ∀ a ∈ WA ++ slotW ++ ["U.len"], a ∈ spArrs ∨ a ∈ DL.dWA := by
    intro a h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · rw [hWA] at h
        rcases List.mem_append.mp h with h | h
        · exact Or.inl (hsp13 a h)
        · rcases List.mem_append.mp h with h | h <;> exact Or.inr h
      · exact Or.inl (sa_slot h)
    · rw [List.mem_singleton.mp h]; exact Or.inl (sa_len (by simp [lenArrs]))
  have cR : ∀ a ∈ WR ++ SpineLab.b8W, a ∈ bodyRegs ∨ a ∈ spRegs ∨ a ∈ DL.dWR := by
    intro a h
    rcases List.mem_append.mp h with h | h
    · rw [hWR] at h
      rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · exact (hbr13 a h).elim Or.inl (fun h => Or.inr (Or.inl h))
        · rcases List.mem_append.mp h with h | h
          · rcases List.mem_append.mp h with h | h
            · right; left
              simp only [piRegs, List.mem_cons, List.mem_singleton, List.not_mem_nil,
                or_false] at h
              rcases h with rfl | rfl <;> simp [spRegs]
            · exact Or.inr (Or.inr h)
          · exact Or.inr (Or.inr h)
      · exact Or.inl (br_b3 h)
    · exact Or.inl (br_b8 h)
  have hPhi7 : PI.PhiR r7 φ1 := phi_of_unch PI hPhi hU17
    (fun a ha => pa_of hNm (cA a ha)) (fun a ha => pr_of hNm (cR a ha))
  -- the D layer
  have hU47 : Unchanged r4 r7 (slotW ++ ["U.len"]) ["sl.l"]
      (["b8.p", "b8.sB", "b8.sBp"] ++ SpineLab.b8W) SpineLab.b8V := by
    refine ((hU45.mono ?_ ?_ ?_ ?_).trans (hU56.mono ?_ ?_ ?_ ?_)).trans (hU67.mono ?_ ?_ ?_ ?_) <;>
      lsub
  have hD7 : DL.DR r7 H1 (cs0 (T (l + 1)) (Mf (l + 1)) B d1 P piv (List.ofFn piv) g).g
      (Function.update Ds (l + 1) (cs0 (T (l + 1)) (Mf (l + 1)) B d1 P piv (List.ofFn piv) g).Dc)
      (l + 1) :=
    dr_of_unch DL hD4 hU47
      (fun a ha => dl_spArr DL (by
        rcases List.mem_append.mp ha with h | h
        · exact sa_slot h
        · rw [List.mem_singleton.mp h]; exact sa_len (by simp [lenArrs])))
      (fun a ha => by rw [List.mem_singleton.mp ha]; exact dl_sll DL)
      (fun a ha => dr_of hNm (by
        rcases List.mem_append.mp ha with h' | h'
        · exact Or.inl (br_b3 h')
        · exact Or.inl (br_b8 h')))
      (by simp [slotW])
  have hL7 : LabAt r7 d1 H1 c0 := hL6.of_unchanged hU67 (by simp [labW]) (by simp) (by omega)
  -- the group table at r7
  have hU37 : Unchanged r3 r7 ((DL.dWA ++ DL.dWA) ++ slotW ++ ["U.len"]) ((DL.dVA ++ DL.dVA) ++ ["sl.l"])
      ((piRegs ++ DL.dWR ++ DL.dWR) ++ ["b8.p", "b8.sB", "b8.sBp"] ++ SpineLab.b8W)
      ((DL.dVR ++ DL.dVR) ++ SpineLab.b8V) := by
    refine (((hU34.mono ?_ ?_ ?_ ?_).trans (hU45.mono ?_ ?_ ?_ ?_)).trans
      (hU56.mono ?_ ?_ ?_ ?_)).trans (hU67.mono ?_ ?_ ?_ ?_) <;> lsub
  have n37 : ∀ a, a ∈ spArrs → a ∉ slotW → a ≠ "U.len" →
      a ∉ (DL.dWA ++ DL.dWA) ++ slotW ++ ["U.len"] := by
    intro a h1 h2 h3 h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h <;> exact dl_spArr DL h1 h
      · exact h2 h
    · exact h3 (List.mem_singleton.mp h)
  have hgA : ∀ a ∈ grpArrs, a ∉ (DL.dWA ++ DL.dWA) ++ slotW ++ ["U.len"] := by
    intro a ha
    simp only [grpArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact n37 _ (sa_row (by simp [rowArrs])) (by simp [slotW]) (by simp)
  have hG7 : GrpRep r7 (l + 1) G.n p (liftP P) (liftPiv piv) := by
    have h1 : GrpRep r3 (l + 1) G.n p (grpP Gs') (liftPiv piv) :=
      GrpRep.of_arrays' hG3 (fun a _ => rfl) (fun a _ => rfl)
        (fun j hj => by simp [liftPiv, hj, hpivdef])
    rw [show grpP Gs' = liftP P from funext (grpP_eq hGsp hPG)] at h1
    exact grpRep_of_unch h1 hU37 hgA
  have hnp7 : NpRep r7 (l + 1) p :=
    ⟨by rw [hwl17, ← hwl2]; exact hNp2.1,
      by rw [(hU37.warr _ (n37 _ (sa_len (by simp [lenArrs])) (by simp [slotW]) (by simp))).1]
         exact hnp3⟩
  have hUs7 : SetRow r7 "U" "U.len" (l + 1) (∅ : Finset (Fin G.n)) := by
    have h := SetRow.ofList (st := r7) (arr := "U") (len := "U.len") (l := l + 1)
      (lX := ([] : List (Fin G.n))) (by simpa using hUrow7) List.nodup_nil
    simpa using h
  have hinU7 : ∀ v : Fin G.n,
      r7.wa "sp.inU" ((l + 1) * G.n + v) = if v ∈ (∅ : Finset (Fin G.n)) then 1 else 0 := by
    intro v
    rw [hunA "sp.inU" (sa_row (by simp [rowArrs])) (by simp [cgArrs]) (by simp) (by simp [slotW])
      (by simp)]
    simp only [Finset.notMem_empty, if_false]
    exact hF.clr.inU (l + 1) le_rfl v v.2
  have hsB6 : SlotHolds r6 (slotB (l + 1)) H1 (vc r5) B :=
    hsB5.of_slot_eq (hsl6 _ (by unfold slotB slotBp; omega)).1
      (hsl6 _ (by unfold slotB slotBp; omega)).2
  have hsB7 : SlotHolds r7 (slotB (l + 1)) H1 (vc r7) B := by
    rw [hvc57]; exact hsB6.of_unchanged hU67 (by simp [slotW]) (by simp)
  have hsBp7 : SlotHolds r7 (slotBp (l + 1)) H1 (vc r7) (initB' B d1 piv) := by
    rw [hvc57]; exact hsBp6.of_unchanged hU67 (by simp [slotW]) (by simp)
  have hg37 : r7.wa "sp.g" = r2.wa "sp.g" := by
    rw [(hU37.warr _ (n37 _ (sa_row (by simp [rowArrs])) (by simp [slotW]) (by simp))).1,
      (hU23.warr _ (by simp)).1]
  have hclr7 : Clear r7 G.n (l + 1 - 1) := by
    rw [show l + 1 - 1 = l by omega]
    refine clear_frame (clear_mono hF.clr (by omega)) (fun i hi => ?_) (fun i _ => ?_)
      (fun x _ => ?_)
    · rw [hg37]; exact hrows2 "sp.g" (by simp [cgArrs]) (by simp) i (Or.inl hi)
    · rw [hunA "sp.inU" (sa_row (by simp [rowArrs])) (by simp [cgArrs]) (by simp) (by simp [slotW])
        (by simp)]
    · rw [hunA "sp.xm" (sa_st (by simp)) (by simp [cgArrs]) (by simp) (by simp [slotW]) (by simp)]
  have hLR : LoopRep DL PI LF body τ Mf r7 (l + 1) B (τ (l + 1)) Ds H1 c0
      (⟨0, cs0 (T (l + 1)) (Mf (l + 1)) B d1 P piv (List.ofFn piv) g, φ1⟩ : LoopCfgD G s Φ p) :=
    { lvl := hl7, l1 := by omega, lvl_le := hLF, stat := hst7, lab := hL7, D := hD7,
      phi := hPhi7, grp := hG7, np := hnp7, U := hUs7, inU := hinU7, sB := hsB7, sBp := hsBp7,
      tau := hst7.tauv _ hLF, clr := hclr7, ptr := fun u hu => absurd hu (Finset.notMem_empty u) }
  -- the frames relative to the call entry
  have hS7 : SetRow r7 "S" "S.len" (l + 1) S :=
    setRow_of_unch hF.S hU17 (nWA7 _ (sa_row (by simp [rowArrs])) (by simp [cgArrs]) (by simp)
      (by simp [slotW]) (by simp)) (nWA7 _ (sa_len (by simp [lenArrs])) (by simp [cgArrs])
      (by simp) (by simp [slotW]) (by simp))
  have hW7 : RowRep r7 "W" "W.len" G.n (l + 1) (wl.map Fin.val) :=
    rowRep_of_unch hW1 hU17 (nWA7 _ (sa_row (by simp [rowArrs])) (by simp [cgArrs]) (by simp)
      (by simp [slotW]) (by simp)) (nWA7 _ (sa_len (by simp [lenArrs])) (by simp [cgArrs])
      (by simp) (by simp [slotW]) (by simp))
  have hU16 : Unchanged r1 r6 (WA ++ slotW) (VA ++ ["sl.l"]) (WR ++ SpineLab.b8W)
      (VR ++ SpineLab.b8V) := by
    refine (hU15.mono ?_ ?_ ?_ ?_).trans (hU56.mono ?_ ?_ ?_ ?_) <;> lsub
  have hAb : Above r1 r7 G.n (l + 1) := by
    refine ⟨fun a ha i hi => ?_, fun a ha j hj => ?_, fun i hi => ?_, hwl17, hvl17⟩
    · by_cases ha1 : a ∈ cgArrs
      · have hnp : a ≠ "sp.np" := by rintro rfl; simp [rowArrs] at ha
        have e : r7.wa a = r2.wa a := by
          rw [(hU37.warr a (n37 a (sa_row ha) (fun h => by
              simp [slotW] at h; rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [rowArrs] at ha)
              (by rintro rfl; simp [rowArrs] at ha))).1,
            (hU23.warr a (fun h => by
              simp only [List.mem_singleton] at h; subst h; simp [cgArrs] at ha1)).1]
        rw [e]; exact hrows2 a ha1 hnp i (Or.inr hi)
      · by_cases ha2 : a = "sp.gp"
        · subst ha2
          have e : r7.wa "sp.gp" = r3.wa "sp.gp" :=
            (hU37.warr _ (n37 _ (sa_row ha) (by simp [slotW]) (by simp))).1
          have hp := hG3.p_le
          rw [e, hgp3 i (Or.inr (by rw [hn2] at hi; omega)), (hU12.warr _ (by simp [cgArrs])).1]
        · exact congrFun (hunA a (sa_row ha) ha1 ha2 (fun h => by
            simp [slotW] at h; rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [rowArrs] at ha)
            (by rintro rfl; simp [rowArrs] at ha)) i
    · by_cases hnp : a = "sp.np"
      · subst hnp
        rw [(hU37.warr _ (n37 _ (sa_len ha) (by simp [slotW]) (by simp))).1,
          (hU23.warr _ (by simp)).1]
        exact hnp2 j (by omega)
      · by_cases hul : a = "U.len"
        · subst hul
          rw [hlen7 j (by omega), (hU16.warr _ ?_).1]
          intro h
          rcases List.mem_append.mp h with h | h
          · exact nWA _ (sa_len ha) (by simp [cgArrs]) (by simp) h
          · simp [slotW] at h
        · exact congrFun (hunA a (sa_len ha) (fun h => by
            simp [cgArrs] at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
              simp [lenArrs] at ha <;> exact hnp rfl)
            (by rintro rfl; simp [lenArrs] at ha) (fun h => by
            simp [slotW] at h; rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [lenArrs] at ha)
            hul) j
    · have hne : i ≠ slotBp (l + 1) := by unfold slotB at hi; unfold slotBp; omega
      obtain ⟨e1, e2⟩ := hsl6 i hne
      have hs5 : r5.va "sl.l" i = r1.va "sl.l" i := by
        rw [(hU15.varr _ (by
          simp only [hVA, List.nil_append, List.mem_append, or_self]; exact dl_sll DL)).1]
      refine ⟨?_, fun a ha => ?_⟩
      · rw [(hU67.varr _ (by simp)).1, e1, hs5]
      · rw [(hU67.warr _ (by simp [slotW] at ha ⊢; rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp)).1,
          e2 a ha, (hU15.warr a (nWA a (sa_slot ha) (by
            simp [slotW] at ha; rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp [cgArrs])
            (by simp [slotW] at ha; rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp))).1]
  have hptr7 : ∀ x, r7.wa "sp.ptr" x = st.wa "sp.ptr" x := fun x => by
    rw [hunA "sp.ptr" (sa_st (by simp)) (by simp [cgArrs]) (by simp) (by simp [slotW]) (by simp)]
    exact hF.ptr x
  have hstA7 : ∀ a ∈ ["gSt", "gHead", "cp.tau", "cp.M", "gKeep", "gRep"], r7.wa a = st.wa a := by
    intro a ha
    have e : r7.wa a = r1.wa a := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hunA _ (sa_st (by simp)) (by simp [cgArrs]) (by simp) (by simp [slotW]) (by simp)
    rw [e]; exact hF.stArr a ha
  -- the cost
  have hsum3 := hc3b
  rw [hsum2] at hsum3
  have hc2' := hc2
  rw [hsumGs, hGs'l] at hc2'
  have hring : p * (DL.K + 5) + 33 * p + 7 * p + 8 * p = (DL.K + 53) * p := by ring
  have hus7 : DL.use r7 = DL.use r4 := DL.use_frame r4 r7 _ _ _ _ hU47 (fun a ha h => by
    rcases List.mem_append.mp h with h' | h'
    · exact hNm.dR a ha (br_b3 h')
    · exact hNm.dR a ha (br_b8 h'))
  refine hK r7 piv (List.ofFn piv) hpiv hlpnd hlp ⟨hLR, hS7, hW7, hF.above.trans hAb, hptr7, hstA7⟩
    hvc7 (by omega) ?_ (by rw [hus7, ← hus3]; exact hu4) hU17.cap
  unfold Kpro
  show r7.cost ≤ r1.cost + (DL.K + 28 + (DL.K + 53) * p + 41 * ∑ j, (P j).card) +
    DL.K * (BM.insManyC (dlOps G s) (T (l + 1)) d1 (List.ofFn piv) g (newC (Mf (l + 1)) B)).2.2
  omega

end Frontier.CHD.RamBody
