import Frontier.CHD.LabRAM
import Frontier.CHD.BaseGlue
import Frontier.CHD.RamLevel
import Frontier.CHD.RamSlot

/-!
# HeapIface — what the base case (agent-08) consumes from the indexed heap (agent-06, IHeap)

NON-GATE scratch interface.  Keys are the CURRENT labels of the label table (`LabAt st d H c0`),
because in `BMCost.BaseLoopC` every stored key equals the current label (`BInv.stored`).  The heap
holds a finite vertex set `T`; its order invariant is w.r.t. a key function `key`; the caller may
lower the label of ONE vertex `v` and then `push` it (push-or-decrease).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamBaseCase

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD.LabTab

variable {G : Graph} {s : Fin G.n}

/-- The heap interface consumed by the base case. -/
structure HeapI (G : Graph) (s : Fin G.n) where
  /-- the heap holds `T`, heap-ordered by `key` -/
  HR : State ℝ≥0 → Finset (Fin G.n) → (Fin G.n → WLab G s) → Prop
  /-- programs: push-or-decrease the vertex in `hp_x`; pop the minimum into `hp_v`; read the
  minimum into `hp_v` -/
  push : Stmt
  pop : Stmt
  top : Stmt
  /-- write sets (word arrays, value arrays, word registers, value registers) -/
  wa : List String
  va : List String
  wr : List String
  vr : List String
  /-- the write sets avoid the label table and the interface registers of the base case -/
  wa_lab : ∀ a ∈ labW, a ∉ wa
  va_lab : "dlen" ∉ va
  /-- size bound of the heap during one base call (`|S| + δ τ₀`) -/
  hsz : ℕ
  /-- cost bound per operation on a heap of size `≤ hsz` (`O(log hsz)` for IHeap) -/
  Cop : ℕ
  /-- footprint of `HR` (word arrays, word registers) -/
  fwa : List String
  fwr : List String
  /-- the heap is stable under writes outside its footprint -/
  HR_frame : ∀ {st st' : State ℝ≥0} {T key wa' va' wr' vr'}, HR st T key →
    Unchanged st st' wa' va' wr' vr' → (∀ a ∈ fwa, a ∉ wa') → (∀ a ∈ fwr, a ∉ wr') →
    HR st' T key
  /-- the size register -/
  size : ∀ {st T key}, HR st T key → st.w "hp_n" = T.card
  /-- `hp_x := v; push` after lowering (or keeping) the key of `v` only -/
  push_spec : ∀ (st : State ℝ≥0) (T : Finset (Fin G.n)) (key : Fin G.n → WLab G s)
    (d : Labels G s) (Hh : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ) (v : Fin G.n),
    HR st T key → LabAt st d Hh c0 → (∀ y, y ≠ v → d y = key y) → d v ≤ key v →
    (∀ y ∈ T, d y ≠ ⊤) → d v ≠ ⊤ → st.w "hp_x" = v → st.cost + Cop ≤ c0 + st.cap →
    2 * G.n + 3 < st.cap → T.card + 1 ≤ hsz →
    Runs realOps push st (fun r => HR r (insert v T) d ∧ Unchanged st r wa va wr vr ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost + Cop)
  /-- `pop`: a minimum `u` of `T` (keys = current labels) into `hp_v`, removed -/
  pop_spec : ∀ (st : State ℝ≥0) (T : Finset (Fin G.n)) (d : Labels G s)
    (Hh : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ),
    HR st T d → LabAt st d Hh c0 → T.Nonempty → (∀ y ∈ T, d y ≠ ⊤) →
    st.cost + Cop ≤ c0 + st.cap → 2 * G.n + 3 < st.cap → T.card ≤ hsz →
    Runs realOps pop st (fun r => ∃ u ∈ T, (∀ y ∈ T, d u ≤ d y) ∧ r.w "hp_v" = u ∧
      HR r (T.erase u) d ∧ Unchanged st r wa va wr vr ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + Cop)
  /-- `top`: a minimum of `T` into `hp_v`, nothing removed -/
  top_spec : ∀ (st : State ℝ≥0) (T : Finset (Fin G.n)) (d : Labels G s)
    (Hh : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ),
    HR st T d → LabAt st d Hh c0 → T.Nonempty → (∀ y ∈ T, d y ≠ ⊤) →
    st.cost + Cop ≤ c0 + st.cap → 2 * G.n + 3 < st.cap → T.card ≤ hsz →
    Runs realOps top st (fun r => ∃ u ∈ T, (∀ y ∈ T, d u ≤ d y) ∧ r.w "hp_v" = u ∧
      HR r T d ∧ Unchanged st r wa va wr vr ∧ st.cost ≤ r.cost ∧ r.cost ≤ st.cost + Cop)

end Frontier.CHD.RamBaseCase

namespace Frontier.CHD.RamBaseCase

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD.LabTab WExpr Stmt

variable {G : Graph} {s : Fin G.n}

/-! ## The CSR ranges of L6 v2 -/

/-- `gSt[u] .. gSt[u+1]` are exactly the out-edges of `u`. -/
structure CSRAt (st : State ℝ≥0) (G : Graph) : Prop where
  len : G.n + 1 ≤ st.wlen "gSt"
  le : ∀ u : Fin G.n, st.wa "gSt" u ≤ st.wa "gSt" (u + 1)
  le_m : ∀ u : Fin G.n, st.wa "gSt" (u + 1) ≤ G.m
  src : ∀ (e : Fin G.m) (u : Fin G.n), G.src e = u ↔ st.wa "gSt" u ≤ e ∧ (e : ℕ) < st.wa "gSt" (u + 1)

/-! ## The relaxation loop over the out-edges of the extracted vertex (BC.7) -/

/-- The bound block of the base case. -/
def KB : LReg := ⟨"bc.bl", "bc.bh", "bc.bv", "bc.be", "bc.br"⟩

theorem boundRegs_KB : BoundRegs KB "bc.bf" :=
  ⟨by decide, by decide, by decide⟩

/-- One edge: `re := p; relaxBM; if ok then (hp_x := gHead[p]; push); p := p + 1`. -/
def edgeBody (H : HeapI G s) : Stmt :=
  seq (wset "re" (var "bc.p"))
  (seq (relaxBM KB "bc.bf")
  (seq (ite (var "ok") (seq (wset "hp_x" (load "gHead" (var "bc.p"))) H.push) skip)
       (wset "bc.p" (add (var "bc.p") (lit 1)))))

/-- `while p < pe do edgeBody` -/
def edgeLoop (H : HeapI G s) : Stmt := .while (lt (var "bc.p") (var "bc.pe")) (edgeBody H)

open Classical in
/-- **One edge of BC.7**: relax edge `e` (in `bc.p`) out of `u` (in `ru`) with the bound in
`KB`, and push-or-decrease its head on success.  Layer A: one `relaxIns B none` step on the store
`Dof T d` (keys = current labels). -/
theorem edgeBody_spec (H : HeapI G s) (st : State ℝ≥0) (d : Labels G s)
    (Hh : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ) (T : Finset (Fin G.n)) (u : Fin G.n)
    (B : WLab G s) (e : Fin G.m)
    (hL : LabAt st d Hh c0) (hg : GraphAt st G) (hHR : H.HR st T d)
    (hK : WHolds st KB "bc.bf" Hh (vc st) B)
    (hru : st.w "ru" = u) (hp : st.w "bc.p" = e) (hsrc : G.src e = u)
    (hu : d u ≠ ⊤) (hT : ∀ y ∈ T, d y ≠ ⊤)
    (hbud : st.cost + H.Cop + 80 ≤ c0 + st.cap) (hm : G.m + 2 ≤ st.cap)
    (hcapN : 2 * G.n + 3 < st.cap) (hsz : T.card + 1 ≤ H.hsz)
    (hHwr : ∀ a ∈ H.wr, a ∉ ["ru", "bc.p", "bc.pe", "bc.bf", "bc.bh", "bc.bv", "bc.be", "bc.br"])
    (hHvr : "bc.bl" ∉ H.vr) (hHwa : ∀ a ∈ H.wa, a ∉ ["gHead", "gSt"]) (hHva : "gW" ∉ H.va)
    (hfwa : ∀ a ∈ H.fwa, a ∉ labW) (hfwr : ∀ a ∈ H.fwr, a ∉ "re" :: "hp_x" :: "bc.p" :: relaxW) :
    Runs realOps (edgeBody H) st (fun r => ∃ (Hh' : Fin G.n → ℕ → List (Fin G.m))
      (T' : Finset (Fin G.n)), T'.card ≤ T.card + 1 ∧
      (BM.relaxIns G s B none (d, BM.Dof T d) e).2 =
        BM.Dof T' (BM.relaxIns G s B none (d, BM.Dof T d) e).1 ∧
      LabAt r (BM.relaxIns G s B none (d, BM.Dof T d) e).1 Hh' c0 ∧
      HExt Hh (vc st) Hh' (vc r) ∧ H.HR r T' (BM.relaxIns G s B none (d, BM.Dof T d) e).1 ∧
      GraphAt r G ∧ WHolds r KB "bc.bf" Hh' (vc r) B ∧
      (∀ y ∈ T', (BM.relaxIns G s B none (d, BM.Dof T d) e).1 y ≠ ⊤) ∧
      (BM.relaxIns G s B none (d, BM.Dof T d) e).1 u ≠ ⊤ ∧ r.w "bc.p" = (e : ℕ) + 1 ∧
      Unchanged st r (labW ++ H.wa) (labV ++ H.va) ("re" :: "hp_x" :: "bc.p" :: (relaxW ++ H.wr))
        (relaxV ++ H.vr) ∧ st.cost ≤ r.cost ∧ r.cost ≤ st.cost + H.Cop + 76) := by
  have hA := BM.relaxIns_Dof B T d e
  have hsrcu : G.src e = u := hsrc
  -- step 1: `re := p`
  refine runs_seq (runs_wset (a := (e : ℕ)) (by rw [evalW_var, hp]) ?_)
  set st1 := (st.setW "re" e).charge 1 with hst1
  have hU1 : Unchanged st st1 [] [] ["re"] [] :=
    ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun z hz => by
      simp only [List.mem_singleton] at hz; simp [hst1, State.setW, State.charge, hz],
      fun _ _ => rfl, rfl, rfl⟩
  have hL1 : LabAt st1 d Hh c0 := hL.of_unchanged hU1 (by decide) (by decide)
    (by simp [hst1, State.charge])
  have hg1 : GraphAt st1 G := graphAt_of_unchanged hU1 (by decide) (by decide) hg
  have hvc1 : vc (G := G) st1 = vc st := vc_of_unchanged hU1 (by decide)
  have hK1 : WHolds st1 KB "bc.bf" Hh (vc st1) B := by
    rw [hvc1]; exact hK.of_unchanged hU1 (by decide) (by decide) (by decide)
  have hru1 : st1.w "ru" = G.src e := by
    rw [hsrcu]; simp [hst1, State.setW, State.charge, hru]
  have hre1 : st1.w "re" = e := by simp [hst1, State.setW, State.charge]
  have hc1 : st1.cost = st.cost + 1 := by simp [hst1, State.charge]
  have hcap1 : st1.cap = st.cap := rfl
  -- step 2: `relaxBM`
  refine runs_seq (((relaxBM_spec st1 d Hh c0 hL1 hg1 e hru1 hre1 (by rw [hsrcu]; exact hu) KB
    "bc.bf" boundRegs_KB B hK1 (by rw [hc1, hcap1]; omega) (by rw [hcap1]; exact hm)).cost_mono).mono ?_)
  rintro r2 ⟨⟨H2, hL2, hext2, hok2, -, -, hg2, hU2, hc2⟩, hc2l⟩
  set d2 := (if BM.ValidRelax G s d B e then
      Function.update d (G.dst e) (ext (d (G.src e)) e) else d) with hd2
  have hd2A : (BM.relaxIns G s B none (d, BM.Dof T d) e).1 = d2 := by
    rw [hA, hd2]; split_ifs <;> rfl
  have hK2 : WHolds r2 KB "bc.bf" H2 (vc r2) B :=
    (hK1.of_unchanged hU2 (by decide) (by decide) (by decide)).ext hext2
  have hHR2 : H.HR r2 T d := H.HR_frame (H.HR_frame hHR hU1 (by simp) (fun a ha h => by
      simp only [List.mem_singleton] at h; exact hfwr a ha (by simp [h]))) hU2
    (fun a ha h => hfwa a ha h) (fun a ha h => hfwr a ha (by simp [h]))
  have hru2 : r2.w "ru" = u := by rw [hU2.wreg "ru" (by decide), hru1, hsrcu]
  have hp2 : r2.w "bc.p" = e := by
    rw [hU2.wreg "bc.p" (by decide)]; simp [hst1, State.setW, State.charge, hp]
  have hcap2 : r2.cap = st.cap := hU2.cap.trans hcap1
  have hdu_fin : d (G.src e) ≠ ⊤ := by rw [hsrcu]; exact hu
  have hcand_fin : ext (d (G.src e)) e ≠ ⊤ := by
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hdu_fin
    rw [← hq]; simp only [ext, WithTop.map_coe]; exact WithTop.coe_ne_top
  have hc2' : r2.cost ≤ st.cost + 71 := by rw [hc1] at hc2; omega
  have hc2l' : st.cost + 1 ≤ r2.cost := by rw [hc1] at hc2l; exact hc2l
  have hvc2 : ∀ r : State ℝ≥0, Unchanged r2 r H.wa H.va H.wr H.vr → vc (G := G) r = vc r2 :=
    fun r hU => vc_of_unchanged hU (fun h => H.wa_lab "vcnt" (by simp [labW]) h)
  have hsetp : ∀ (r : State ℝ≥0), r.w "bc.p" = e → (e : ℕ) + 1 < r.cap →
      evalW r (add (var "bc.p") (lit 1)) = some ((e : ℕ) + 1) := by
    intro r hr hc
    rw [evalW_add_of (by rw [evalW_var, hr]) (evalW_lit_of (by omega)) hc]
  have hecap : (e : ℕ) + 1 < st.cap := by have := e.isLt; omega
  have hvne : ∀ y, (BM.relaxIns G s B none (d, BM.Dof T d) e).1 y ≠ ⊤ → True := fun _ _ => trivial
  by_cases hv : BM.ValidRelax G s d B e
  · -- valid relaxation: push the head
    have hd2v : d2 = Function.update d (G.dst e) (ext (d (G.src e)) e) := by rw [hd2, if_pos hv]
    have hok : r2.w "ok" = 1 := by rw [hok2, if_pos hv]
    refine runs_seq (runs_ite_true (x := 1) (by rw [evalW_var, hok]) one_ne_zero ?_)
    set r3 := r2.charge 1 with hr3
    have hhead : evalW r3 (load "gHead" (var "bc.p")) = some ((G.dst e : Fin G.n) : ℕ) := by
      have h1 := hg2.head.read e
      have hlen : (e : ℕ) < r3.wlen "gHead" := by
        simp only [hr3, State.charge_wlen]; have := hg2.head.1; have := e.isLt; omega
      rw [evalW_load_of (j := (e : ℕ)) (by rw [evalW_var]; simp [hr3, State.charge, hp2]) hlen]
      simp only [hr3, State.charge_wa]; rw [h1]
    refine runs_seq (runs_wset hhead ?_)
    set r4 := (r3.setW "hp_x" (G.dst e)).charge 1 with hr4
    have hU34 : Unchanged r2 r4 [] [] ["hp_x"] [] :=
      ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun z hz => by
        simp only [List.mem_singleton] at hz; simp [hr4, hr3, State.setW, State.charge, hz],
        fun _ _ => rfl, rfl, rfl⟩
    have hL4 : LabAt r4 d2 H2 c0 := hL2.of_unchanged hU34 (by decide) (by decide)
      (by simp only [hr4, hr3, State.charge_cost, State.setW_cost]; omega)
    have hHR4 : H.HR r4 T d := H.HR_frame hHR2 hU34 (by simp)
      (fun a ha h => hfwr a ha (by simp only [List.mem_singleton] at h; simp [h]))
    have hc4 : r4.cost = r2.cost + 2 := by simp [hr4, hr3, State.charge]
    have hcap4 : r4.cap = st.cap := hcap2
    refine ((H.push_spec r4 T d d2 H2 c0 (G.dst e) hHR4 hL4 (fun y hy => by
        rw [hd2v, Function.update_of_ne hy]) (by rw [hd2v, Function.update_self]; exact hv.1)
      (fun y hy => by
        rw [hd2v]
        by_cases hyv : y = G.dst e
        · rw [hyv, Function.update_self]; exact hcand_fin
        · rw [Function.update_of_ne hyv]; exact hT y hy)
      (by rw [hd2v, Function.update_self]; exact hcand_fin)
      (by simp [hr4, State.setW, State.charge]) (by rw [hc4, hcap4]; omega)
      (by rw [hcap4]; exact hcapN) hsz).mono ?_)
    rintro r5 ⟨hHR5, hU5, hc5l, hc5⟩
    -- step 4: `bc.p := bc.p + 1`
    have hp5 : r5.w "bc.p" = e := by
      rw [hU5.wreg "bc.p" (fun h => hHwr _ h (by simp)), hU34.wreg "bc.p" (by decide), hp2]
    have hcap5 : r5.cap = st.cap := hU5.cap.trans hcap4
    refine runs_wset (hsetp r5 hp5 (by rw [hcap5]; exact hecap)) ?_
    set r6 := (r5.setW "bc.p" ((e : ℕ) + 1)).charge 1 with hr6
    have hU56 : Unchanged r5 r6 [] [] ["bc.p"] [] :=
      ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun z hz => by
        simp only [List.mem_singleton] at hz; simp [hr6, State.setW, State.charge, hz],
        fun _ _ => rfl, rfl, rfl⟩
    have hU46 : Unchanged r4 r6 H.wa H.va (H.wr ++ ["bc.p"]) H.vr := by
      have := hU5.comp hU56; simpa using this
    refine ⟨H2, insert (G.dst e) T, Finset.card_insert_le _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · rw [hA, if_pos hv]
    · rw [hd2A]
      exact hL4.of_unchanged hU46 (fun a ha h => H.wa_lab a ha h) (fun h => H.va_lab h)
        (by simp [hr6, State.charge]; omega)
    · rw [hvc1] at hext2
      have e6 : vc (G := G) r6 = vc r2 := by
        have := vc_of_unchanged (G := G) (hU34.comp hU46) (by
          simp only [List.nil_append]; exact fun h => H.wa_lab "vcnt" (by simp [labW]) h)
        exact this
      rw [e6]; exact hext2
    · rw [hd2A]; exact H.HR_frame hHR5 hU56 (by simp)
        (fun a ha h => hfwr a ha (by simp only [List.mem_singleton] at h; simp [h]))
    · exact graphAt_of_unchanged (hU34.comp hU46) (fun h => by
        simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
        exact hHwa _ h (by simp)) (fun h => by simpa using hHva h) hg2
    · have e6 : vc (G := G) r6 = vc r2 := vc_of_unchanged (G := G) (hU34.comp hU46) (by
        simp only [List.nil_append]; exact fun h => H.wa_lab "vcnt" (by simp [labW]) h)
      rw [e6]
      have hU26 : Unchanged r2 r6 H.wa H.va ("hp_x" :: "bc.p" :: H.wr) H.vr :=
        (hU34.comp hU46).mono (by simp) (by simp) (by intro a; simp; tauto) (by simp)
      refine hK2.of_unchanged hU26 (fun a ha h => ?_) ?_ ?_
      · simp only [KB, LReg.ws, List.mem_cons, List.not_mem_nil, or_false] at ha
        simp only [List.mem_cons] at h
        rcases h with h | h | h
        · subst h; rcases ha with h' | h' | h' | h' <;> exact absurd h' (by decide)
        · subst h; rcases ha with h' | h' | h' | h' <;> exact absurd h' (by decide)
        · exact hHwr a h (by rcases ha with rfl | rfl | rfl | rfl <;> simp)
      · show ("bc.bl" : String) ∉ H.vr; exact hHvr
      · intro h
        simp only [List.mem_cons] at h
        rcases h with h | h | h
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · exact hHwr _ h (by simp)
    · intro y hy
      rw [hd2A, hd2v]
      rcases Finset.mem_insert.mp hy with rfl | hy
      · rw [Function.update_self]; exact hcand_fin
      · by_cases hyv : y = G.dst e
        · rw [hyv, Function.update_self]; exact hcand_fin
        · rw [Function.update_of_ne hyv]; exact hT y hy
    · rw [hd2A, hd2v]
      by_cases hyv : u = G.dst e
      · rw [hyv, Function.update_self]; exact hcand_fin
      · rw [Function.update_of_ne hyv]; exact hu
    · simp [hr6, State.setW, State.charge]
    · -- the frame
      have h01 : Unchanged st r2 labW labV ("re" :: relaxW) relaxV := by
        have := hU1.comp hU2; simpa using this
      have := (h01.comp (hU34.comp hU46))
      refine this.mono (by intro a; first | (simp; done) | (simp; tauto))
        (by intro a; first | (simp; done) | (simp; tauto))
        (by intro a; first | (simp; done) | (simp; tauto))
        (by intro a; first | (simp; done) | (simp; tauto))
    · have := hc5l; simp [hr6, State.charge]; omega
    · have := hc5; simp [hr6, State.charge]; omega
  · -- invalid relaxation: nothing to push
    have hd2v : d2 = d := by rw [hd2, if_neg hv]
    have hok : r2.w "ok" = 0 := by rw [hok2, if_neg hv]
    refine runs_seq (runs_ite_false (by rw [evalW_var, hok]) (runs_skip ?_))
    set r3 := (r2.charge 1).charge 1 with hr3
    have hp3 : r3.w "bc.p" = e := by simp [hr3, State.charge, hp2]
    have hcap3 : r3.cap = st.cap := hcap2
    refine runs_wset (hsetp r3 hp3 (by rw [hcap3]; exact hecap)) ?_
    set r6 := (r3.setW "bc.p" ((e : ℕ) + 1)).charge 1 with hr6
    have hU26 : Unchanged r2 r6 [] [] ["bc.p"] [] :=
      ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun z hz => by
        simp only [List.mem_singleton] at hz; simp [hr6, hr3, State.setW, State.charge, hz],
        fun _ _ => rfl, rfl, rfl⟩
    have e6 : vc (G := G) r6 = vc r2 := vc_of_unchanged (G := G) hU26 (by simp)
    refine ⟨H2, T, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hA, if_neg hv]
    · rw [hd2A, hd2v]; rw [hd2v] at hL2
      exact hL2.of_unchanged hU26 (by simp) (by simp)
        (by simp only [hr6, hr3, State.charge_cost, State.setW_cost]; omega)
    · rw [hvc1] at hext2; rw [e6]; exact hext2
    · rw [hd2A, hd2v]; exact H.HR_frame hHR2 hU26 (by simp)
        (fun a ha h => hfwr a ha (by simp only [List.mem_singleton] at h; simp [h]))
    · exact graphAt_of_unchanged hU26 (by simp) (by simp) hg2
    · rw [e6]; exact hK2.of_unchanged hU26 (by decide) (by decide) (by decide)
    · intro y hy; rw [hd2A, hd2v]; exact hT y hy
    · rw [hd2A, hd2v]; exact hu
    · simp [hr6, State.setW, State.charge]
    · have h01 : Unchanged st r2 labW labV ("re" :: relaxW) relaxV := by
        have := hU1.comp hU2; simpa using this
      have := h01.comp hU26
      refine this.mono (by intro a; first | (simp; done) | (simp; tauto))
        (by intro a; first | (simp; done) | (simp; tauto))
        (by intro a; first | (simp; done) | (simp; tauto))
        (by intro a; first | (simp; done) | (simp; tauto))
    · simp [hr6, hr3, State.charge]; omega
    · simp [hr6, hr3, State.charge]; omega

/-- The frame lists of the relaxation loop. -/
def eWA (H : HeapI G s) : List String := labW ++ H.wa
def eVA (H : HeapI G s) : List String := labV ++ H.va
def eWR (H : HeapI G s) : List String := "re" :: "hp_x" :: "bc.p" :: (relaxW ++ H.wr)
def eVR (H : HeapI G s) : List String := relaxV ++ H.vr

open Classical in
/-- **BC.7, the whole relaxation loop** over the CSR range `[a, b)` of `u`: the fold of
`relaxIns B none` over a list `P` enumerating the range, on the store `Dof T d`. -/
theorem edgeLoop_spec (H : HeapI G s) (st : State ℝ≥0) (d : Labels G s)
    (Hh : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ) (T : Finset (Fin G.n)) (u : Fin G.n)
    (B : WLab G s) (a b : ℕ)
    (hL : LabAt st d Hh c0) (hg : GraphAt st G) (hHR : H.HR st T d)
    (hK : WHolds st KB "bc.bf" Hh (vc st) B)
    (hru : st.w "ru" = u) (hpa : st.w "bc.p" = a) (hpb : st.w "bc.pe" = b)
    (hab : a ≤ b) (hbm : b ≤ G.m) (hsrc : ∀ e : Fin G.m, a ≤ e → (e : ℕ) < b → G.src e = u)
    (hu : d u ≠ ⊤) (hT : ∀ y ∈ T, d y ≠ ⊤)
    (hbud : st.cost + (b - a) * (H.Cop + 77) + H.Cop + 81 ≤ c0 + st.cap) (hm : G.m + 2 ≤ st.cap)
    (hcapN : 2 * G.n + 3 < st.cap) (hsz : T.card + (b - a) ≤ H.hsz)
    (hHwr : ∀ a ∈ H.wr, a ∉ ["ru", "bc.p", "bc.pe", "bc.bf", "bc.bh", "bc.bv", "bc.be", "bc.br"])
    (hHvr : "bc.bl" ∉ H.vr) (hHwa : ∀ a ∈ H.wa, a ∉ ["gHead", "gSt"]) (hHva : "gW" ∉ H.va)
    (hfwa : ∀ a ∈ H.fwa, a ∉ labW) (hfwr : ∀ a ∈ H.fwr, a ∉ "re" :: "hp_x" :: "bc.p" :: relaxW) :
    Runs realOps (edgeLoop H) st (fun r => ∃ (P : List (Fin G.m)) (Hh' : Fin G.n → ℕ → List (Fin G.m)) (T' : Finset (Fin G.n))
      (d' : Labels G s), T'.card ≤ T.card + (b - a) ∧
      P.Nodup ∧ (∀ e : Fin G.m, e ∈ P ↔ a ≤ e ∧ (e : ℕ) < b) ∧
      P.foldl (BM.relaxIns G s B none) (d, BM.Dof T d) = (d', BM.Dof T' d') ∧
      LabAt r d' Hh' c0 ∧ HExt Hh (vc st) Hh' (vc r) ∧ H.HR r T' d' ∧ GraphAt r G ∧
      WHolds r KB "bc.bf" Hh' (vc r) B ∧ (∀ y ∈ T', d' y ≠ ⊤) ∧ d' u ≠ ⊤ ∧
      r.w "ru" = u ∧ Unchanged st r (eWA H) (eVA H) (eWR H) (eVR H) ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost + (b - a) * (H.Cop + 77) + 1) := by
  have hcap1 : 1 < st.cap := by omega
  refine runs_while_nat (fun k r => ∃ (p : ℕ) (P : List (Fin G.m)) (Hh' : Fin G.n → ℕ → List (Fin G.m))
      (T' : Finset (Fin G.n)) (d' : Labels G s), T'.card ≤ T.card + (p - a) ∧
      r.w "bc.p" = p ∧ k = b - p ∧ a ≤ p ∧ p ≤ b ∧
      P.Nodup ∧ (∀ e : Fin G.m, e ∈ P ↔ a ≤ e ∧ (e : ℕ) < p) ∧
      P.foldl (BM.relaxIns G s B none) (d, BM.Dof T d) = (d', BM.Dof T' d') ∧
      LabAt r d' Hh' c0 ∧ HExt Hh (vc st) Hh' (vc r) ∧ H.HR r T' d' ∧ GraphAt r G ∧
      WHolds r KB "bc.bf" Hh' (vc r) B ∧ (∀ y ∈ T', d' y ≠ ⊤) ∧ d' u ≠ ⊤ ∧
      r.w "ru" = u ∧ r.w "bc.pe" = b ∧ Unchanged st r (eWA H) (eVA H) (eWR H) (eVR H) ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost + (p - a) * (H.Cop + 77)) _ ?_ (b - a) st
    ⟨a, [], Hh, T, d, by simp, hpa, rfl, le_rfl, hab, List.nodup_nil, fun e => by simp <;> omega, rfl, hL,
      HExt.refl _ _, hHR, hg, hK, hT, hu, hru, hpb, Unchanged.refl _ _ _ _ _, le_rfl, by simp⟩
  rintro k r ⟨p, P, Hh', T', d', hTc, hp, rfl, hap, hpb', hnd, hmem, hfold, hL', hext, hHR', hg',
    hK', hT', hu', hru', hpe', hU', hcl, hch⟩
  have hcapr : r.cap = st.cap := hU'.cap
  refine ⟨if p < b then 1 else 0, by
    rw [evalW_lt_of (by rw [evalW_var, hp]) (by rw [evalW_var, hpe']) (by rw [hcapr]; exact hcap1)],
    fun hx => ?_, fun hx => ?_⟩
  · -- one more edge
    have hpb2 : p < b := by by_contra h; rw [if_neg h] at hx; exact hx rfl
    set e : Fin G.m := ⟨p, by omega⟩ with he
    have hsrce : G.src e = u := hsrc e hap hpb2
    have hbud' : (r.charge 1).cost + H.Cop + 80 ≤ c0 + (r.charge 1).cap := by
      simp only [State.charge_cost, State.charge_cap, hcapr]
      have : (p - a) * (H.Cop + 77) + (H.Cop + 77) ≤ (b - a) * (H.Cop + 77) := by
        have h1 : p - a + 1 ≤ b - a := by omega
        calc (p - a) * (H.Cop + 77) + (H.Cop + 77) = (p - a + 1) * (H.Cop + 77) := by ring
          _ ≤ (b - a) * (H.Cop + 77) := Nat.mul_le_mul_right _ h1
      omega
    have hU1 : Unchanged r (r.charge 1) [] [] [] [] := Unchanged.charge r 1 [] [] [] []
    refine ((edgeBody_spec H (r.charge 1) d' Hh' c0 T' u B e
      (hL'.of_unchanged hU1 (by simp) (by simp) (by simp [State.charge]))
      (graphAt_of_unchanged hU1 (by simp) (by simp) hg') (H.HR_frame hHR' hU1 (by simp) (by simp))
      (by have := hK'.of_unchanged hU1 (by simp) (by simp) (by simp)
          rwa [show vc (G := G) (r.charge 1) = vc r from rfl])
      (by simp [State.charge, hru']) (by simp [State.charge, hp, he]) hsrce
      hu' hT' hbud'
      (by simp only [State.charge_cap, hcapr]; exact hm)
      (by simp only [State.charge_cap, hcapr]; exact hcapN) (by omega) hHwr hHvr hHwa hHva hfwa
      hfwr).mono ?_)
    rintro r' ⟨Hh'', T'', hTc'', hstore, hL'', hext', hHR'', hg'', hK'', hT'', hu'', hp', hU'', hcl',
      hch'⟩
    refine ⟨b - (p + 1), by omega, p + 1, P ++ [e], Hh'', T'',
      (BM.relaxIns G s B none (d', BM.Dof T' d') e).1, by omega, hp', rfl, by omega, by omega, ?_,
      ?_, ?_,
      hL'', ?_, hHR'', hg'', hK'', hT'', hu'', ?_, ?_, ?_, ?_, ?_⟩
    · refine List.nodup_append.mpr ⟨hnd, List.nodup_singleton _, fun x hx y hy => ?_⟩
      rw [List.mem_singleton] at hy
      intro hxe
      rw [hxe, hy] at hx
      have := (hmem e).mp hx
      simp [he] at this
    · intro e'
      rw [List.mem_append, hmem, List.mem_singleton]
      constructor
      · rintro (⟨h1, h2⟩ | rfl)
        · exact ⟨h1, by omega⟩
        · exact ⟨hap, by simp [he]⟩
      · rintro ⟨h1, h2⟩
        by_cases h3 : (e' : ℕ) < p
        · exact Or.inl ⟨h1, h3⟩
        · right; ext; simp [he]; omega
    · rw [List.foldl_append, hfold]
      simp only [List.foldl_cons, List.foldl_nil]
      exact Prod.ext rfl hstore
    · have e1 : vc (G := G) (r.charge 1) = vc r := rfl
      rw [e1] at hext'
      exact hext.trans hext'
    · rw [hU''.wreg "ru" (by simp [eWR, relaxW]; intro h; exact hHwr _ h (by simp))]
      simp [State.charge, hru']
    · rw [hU''.wreg "bc.pe" (by simp [eWR, relaxW]; intro h; exact hHwr _ h (by simp))]
      simp [State.charge, hpe']
    · exact (hU'.trans ((Unchanged.charge r 1 _ _ _ _).trans hU''))
    · have := hcl'; simp [State.charge] at this; omega
    · have h1 : (p + 1 - a) * (H.Cop + 77) = (p - a) * (H.Cop + 77) + (H.Cop + 77) := by
        rw [show p + 1 - a = p - a + 1 by omega]; ring
      rw [h1]; have := hch'; simp [State.charge] at this; omega
  · -- the range is exhausted
    have hpb2 : p = b := by
      by_contra h; rw [if_pos (by omega)] at hx; exact one_ne_zero hx
    subst hpb2
    refine ⟨P, Hh', T', d', by omega, hnd, hmem, hfold, hL'.of_unchanged (Unchanged.charge r 1 [] [] [] [])
      (by simp) (by simp) (by simp [State.charge]), by
        have e1 : vc (G := G) (r.charge 1) = vc r := rfl
        rw [e1]; exact hext,
      H.HR_frame hHR' (Unchanged.charge r 1 [] [] [] []) (by simp) (by simp),
      graphAt_of_unchanged (Unchanged.charge r 1 [] [] [] []) (by simp) (by simp) hg', ?_, hT', hu',
      by simp [State.charge, hru'], hU'.trans (Unchanged.charge r 1 _ _ _ _), by
        simp [State.charge]; omega, by simp [State.charge]; omega⟩
    have := hK'.of_unchanged (Unchanged.charge r 1 [] [] [] []) (by simp) (by simp) (by simp)
    exact this

theorem length_of_mem_Ico {m a b : ℕ} (hb : b ≤ m) {L : List (Fin m)} (hnd : L.Nodup)
    (hmem : ∀ e : Fin m, e ∈ L ↔ a ≤ e ∧ (e : ℕ) < b) : L.length = b - a := by
  have h1 : L.length = (L.toFinset.map Fin.valEmbedding).card := by
    rw [Finset.card_map, List.toFinset_card_of_nodup hnd]
  have h2 : L.toFinset.map Fin.valEmbedding = Finset.Ico a b := by
    ext x
    simp only [Finset.mem_map, List.mem_toFinset, Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨e, he, rfl⟩; exact (hmem e).mp he
    · rintro ⟨h1, h2⟩; exact ⟨⟨x, by omega⟩, (hmem _).mpr ⟨h1, h2⟩, rfl⟩
  rw [h1, h2, Nat.card_Ico]

/-! ## One extraction (BC.3–BC.7) -/

open Frontier.CHD.RamLevel in
/-- `pop u; U.append u; ru := u; bc.p := gSt[u]; bc.pe := gSt[u+1]; relax the range`. -/
def extractBody (H : HeapI G s) : Stmt :=
  seq H.pop
  (seq (rowAppend "U" "U.len" (var "hp_v"))
  (seq (wset "ru" (var "hp_v"))
  (seq (wset "bc.p" (load "gSt" (var "hp_v")))
  (seq (wset "bc.pe" (load "gSt" (add (var "hp_v") (lit 1))))
       (edgeLoop H)))))

/-- The U row (level 0) lists the finite set `U` without repetition. -/
def URow (st : State ℝ≥0) (U : Finset (Fin G.n)) : Prop :=
  ∃ xs : List ℕ, RamLevel.RowRep st "U" "U.len" G.n 0 xs ∧ xs.Nodup ∧
    ∀ x : ℕ, x ∈ xs ↔ ∃ u ∈ U, (u : ℕ) = x

/-- The heap stays out of the base case's own arrays and registers. -/
structure HeapOK (H : HeapI G s) : Prop where
  wr : ∀ a ∈ H.wr, a ∉ ["ru", "bc.p", "bc.pe", "bc.bf", "bc.bh", "bc.bv", "bc.be", "bc.br", "lvl",
    "n", "re", "bc.go", "bc.tau", "bc.k", "sl.i", "bc.mf", "bc.mh", "bc.mv", "bc.me", "bc.mr"]
  vr : "bc.bl" ∉ H.vr ∧ "bc.ml" ∉ H.vr
  wa : ∀ a ∈ H.wa, a ∉ ["gHead", "gSt", "U", "U.len", "S", "S.len", "sl.h", "sl.v", "sl.e", "sl.r",
    "sl.f"]
  va : "gW" ∉ H.va ∧ "sl.l" ∉ H.va
  fwa : ∀ a ∈ H.fwa, a ∉ labW ∧ a ∉ ["U", "U.len", "sl.h", "sl.v", "sl.e", "sl.r", "sl.f"]
  fwr : ∀ a ∈ H.fwr, a ∉ "re" :: "hp_x" :: "bc.p" :: "bc.pe" :: "ru" :: "bc.go" :: "sl.i" ::
    "bc.k" :: "bc.bf" :: "bc.bh" :: "bc.bv" :: "bc.be" :: "bc.br" :: "bc.mf" :: "bc.mh" ::
    "bc.mv" :: "bc.me" :: "bc.mr" :: "bc.tau" :: relaxW

theorem CSRAt.of_unchanged {st r : State ℝ≥0} {wa va wr vr : List String} (h : CSRAt st G)
    (hu : Unchanged st r wa va wr vr) (hg : "gSt" ∉ wa) : CSRAt r G := by
  have e := hu.warr "gSt" hg
  exact ⟨by rw [e.2]; exact h.len, fun u => by rw [e.1]; exact h.le u,
    fun u => by rw [e.1]; exact h.le_m u, fun e' u => by rw [e.1]; exact h.src e' u⟩

theorem URow.of_unchanged {st r : State ℝ≥0} {U : Finset (Fin G.n)} {wa va wr vr : List String}
    (h : URow st U) (hu : Unchanged st r wa va wr vr) (h1 : "U" ∉ wa) (h2 : "U.len" ∉ wa) :
    URow r U := by
  obtain ⟨xs, hR, hnd, hmem⟩ := h
  have e1 := hu.warr "U" h1
  have e2 := hu.warr "U.len" h2
  exact ⟨xs, RamLevel.RowRep.of_eq hR e1.2 e2.2 (by rw [e2.1]) (fun i _ => by rw [e1.1]), hnd,
    hmem⟩

theorem HeapOK.edge {H : HeapI G s} (h : HeapOK H) :
    (∀ a ∈ H.wr, a ∉ ["ru", "bc.p", "bc.pe", "bc.bf", "bc.bh", "bc.bv", "bc.be", "bc.br"]) ∧
    "bc.bl" ∉ H.vr ∧ (∀ a ∈ H.wa, a ∉ ["gHead", "gSt"]) ∧ "gW" ∉ H.va ∧
    (∀ a ∈ H.fwa, a ∉ labW) ∧ (∀ a ∈ H.fwr, a ∉ "re" :: "hp_x" :: "bc.p" :: relaxW) := by
  refine ⟨fun a ha hm => h.wr a ha ?_, h.vr.1, fun a ha hm => h.wa a ha ?_, h.va.1,
    fun a ha => (h.fwa a ha).1, fun a ha hm => h.fwr a ha ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; tauto
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; tauto
  · simp only [List.mem_cons] at hm ⊢; tauto


theorem card_lt_of_notMem {U : Finset (Fin G.n)} {u : Fin G.n} (hu : u ∉ U) : U.card < G.n := by
  have h := Finset.card_le_card (Finset.subset_univ (insert u U))
  rw [Finset.card_insert_of_notMem hu, Finset.card_univ, Fintype.card_fin] at h
  omega

theorem length_of_mem_image {U : Finset (Fin G.n)} {xs : List ℕ} (hnd : xs.Nodup)
    (hmem : ∀ x : ℕ, x ∈ xs ↔ ∃ u ∈ U, (u : ℕ) = x) : xs.length = U.card := by
  rw [← List.toFinset_card_of_nodup hnd]
  have : xs.toFinset = U.map Fin.valEmbedding := by
    ext x; simp only [List.mem_toFinset, Finset.mem_map, Fin.valEmbedding_apply, hmem]
  rw [this, Finset.card_map]

/-- Slack of one extraction (worst-case degree `G.m`). -/
def exSlack (H : HeapI G s) (G : Graph) : ℕ := (G.m + 1) * (H.Cop + 77) + 2 * H.Cop + 100

open Classical in
/-- **One extraction** (BC.3–BC.7): pops a minimum `u` of `T`, appends it to `U`, and relaxes its
out-edges; Layer A: exactly the data of `BaseLoopC.step` on the store `Dof T d`. -/
theorem extractBody_spec (H : HeapI G s) (hok : HeapOK H) (st : State ℝ≥0) (d : Labels G s)
    (Hh : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ) (T U : Finset (Fin G.n)) (B : WLab G s)
    (hL : LabAt st d Hh c0) (hg : GraphAt st G) (hcsr : CSRAt st G) (hHR : H.HR st T d)
    (hK : WHolds st KB "bc.bf" Hh (vc st) B) (hU : URow st U) (hlvl : st.w "lvl" = 0)
    (hn : st.w "n" = G.n) (hTne : T.Nonempty) (hTfin : ∀ y ∈ T, d y ≠ ⊤)
    (hTU : ∀ y ∈ T, y ∉ U) (hbud : st.cost + exSlack H G ≤ c0 + st.cap) (hm : G.m + 2 ≤ st.cap)
    (hcapN : 2 * G.n + 3 < st.cap) (δ : ℕ)
    (hdeg : ∀ u : Fin G.n, st.wa "gSt" ((u : ℕ) + 1) - st.wa "gSt" u ≤ δ)
    (hszT : T.card + δ ≤ H.hsz) :
    Runs realOps (extractBody H) st (fun r => ∃ (u : Fin G.n) (L : List (Fin G.m))
      (Hh' : Fin G.n → ℕ → List (Fin G.m)) (T' : Finset (Fin G.n)) (d' : Labels G s),
      T'.card + 1 ≤ T.card + δ ∧ u ∈ T ∧ (∀ y ∈ T, d u ≤ d y) ∧ BM.Enumerates G L {u} ∧
      L.foldl (BM.relaxIns G s B none) (d, BM.Dof (T.erase u) d) = (d', BM.Dof T' d') ∧
      LabAt r d' Hh' c0 ∧ HExt Hh (vc st) Hh' (vc r) ∧ H.HR r T' d' ∧ GraphAt r G ∧
      CSRAt r G ∧ WHolds r KB "bc.bf" Hh' (vc r) B ∧ URow r (insert u U) ∧
      (∀ y ∈ T', d' y ≠ ⊤) ∧ r.w "lvl" = 0 ∧ r.w "n" = G.n ∧
      Unchanged st r (eWA H ++ ["U", "U.len"]) (eVA H) ("ru" :: "bc.pe" :: eWR H) (eVR H) ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost + H.Cop + 7 + L.length * (H.Cop + 77) ∧
      (∀ i, G.n ≤ i → r.wa "U" i = st.wa "U" i) ∧ (∀ j, j ≠ 0 → r.wa "U.len" j = st.wa "U.len" j)) := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hok.edge
  -- step 1: pop
  refine runs_seq ((H.pop_spec st T d Hh c0 hHR hL hTne hTfin (by unfold exSlack at hbud; omega)
    hcapN (by omega)).mono ?_)
  rintro r1 ⟨u, huT, hmin, hv1, hHR1, hU1, hc1l, hc1⟩
  have hL1 : LabAt r1 d Hh c0 := hL.of_unchanged hU1 (fun a ha h => H.wa_lab a ha h) H.va_lab (by omega)
  have hg1 : GraphAt r1 G := graphAt_of_unchanged hU1 (fun h => e3 _ h (by simp)) e4 hg
  have hcsr1 : CSRAt r1 G := hcsr.of_unchanged hU1 (fun h => e3 _ h (by simp))
  have hvc1 : vc (G := G) r1 = vc st := vc_of_unchanged hU1 (fun h => H.wa_lab "vcnt" (by simp [labW]) h)
  have hK1 : WHolds r1 KB "bc.bf" Hh (vc r1) B := by
    rw [hvc1]; exact hK.of_unchanged hU1 (fun a ha h => e1 a h (by
      simp only [KB, LReg.ws, List.mem_cons, List.not_mem_nil, or_false] at ha ⊢; tauto)) e2
      (fun h => e1 _ h (by simp))
  have hU1' : URow r1 U := hU.of_unchanged hU1 (fun h => hok.wa _ h (by simp)) (fun h => hok.wa _ h (by simp))
  have hlvl1 : r1.w "lvl" = 0 := by rw [hU1.wreg "lvl" (fun h => hok.wr _ h (by simp)), hlvl]
  have hn1 : r1.w "n" = G.n := by rw [hU1.wreg "n" (fun h => hok.wr _ h (by simp)), hn]
  have hcap1 : r1.cap = st.cap := hU1.cap
  have hu_fin : d u ≠ ⊤ := hTfin u huT
  have huU : u ∉ U := hTU u huT
  obtain ⟨xs, hR1, hnd1, hmem1⟩ := hU1'
  have hxl : xs.length < G.n := by rw [length_of_mem_image hnd1 hmem1]; exact card_lt_of_notMem huU
  -- step 2: append `u` to the U row
  refine runs_seq ((RamLevel.rowAppend_spec r1 (by decide) hR1 hlvl1 hn1 hxl
    (by rw [evalW_var, hv1]) (by rw [hcap1]; omega)).mono ?_)
  rintro r2 ⟨hR2, hU2, hUi2, hUl2, -, hc2, -⟩
  have hL2 : LabAt r2 d Hh c0 := hL1.of_unchanged hU2 (by decide) (by decide) (by omega)
  have hg2 : GraphAt r2 G := graphAt_of_unchanged hU2 (by decide) (by decide) hg1
  have hcsr2 : CSRAt r2 G := hcsr1.of_unchanged hU2 (by decide)
  have hvc2 : vc (G := G) r2 = vc r1 := vc_of_unchanged hU2 (by decide)
  have hK2 : WHolds r2 KB "bc.bf" Hh (vc r2) B := by
    rw [hvc2]; exact hK1.of_unchanged hU2 (by decide) (by decide) (by decide)
  have hHR2 : H.HR r2 (T.erase u) d := H.HR_frame hHR1 hU2
    (fun a ha h => (hok.fwa a ha).2 (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto))
    (by simp)
  have hv2 : r2.w "hp_v" = u := by rw [hU2.wreg _ (by simp), hv1]
  have hlvl2 : r2.w "lvl" = 0 := by rw [hU2.wreg _ (by simp), hlvl1]
  have hn2 : r2.w "n" = G.n := by rw [hU2.wreg _ (by simp), hn1]
  have hcap2 : r2.cap = st.cap := hU2.cap.trans hcap1
  -- steps 3–5: `ru := u; bc.p := gSt[u]; bc.pe := gSt[u+1]`
  have hul : (u : ℕ) + 1 < r2.wlen "gSt" := by have := hcsr2.len; have := u.isLt; omega
  refine runs_seq (runs_wset (a := (u : ℕ)) (by rw [evalW_var, hv2]) ?_)
  set r3 := (r2.setW "ru" u).charge 1 with hr3
  refine runs_seq (runs_wset (a := r2.wa "gSt" u) (evalW_load_of (by
    rw [evalW_var]; simp [hr3, State.setW, State.charge, hv2]) (by
    simp only [hr3, State.charge_wlen, State.setW_wlen]; omega)) ?_)
  set r4 := (r3.setW "bc.p" (r2.wa "gSt" u)).charge 1 with hr4
  have hcap4 : r4.cap = st.cap := hcap2
  refine runs_seq (runs_wset (a := r2.wa "gSt" ((u : ℕ) + 1)) (evalW_load_of (evalW_add_of (by
    rw [evalW_var]; simp [hr4, hr3, State.setW, State.charge, hv2]) (evalW_lit_of (by
    rw [hcap4]; omega)) (by rw [hcap4]; have := u.isLt; omega)) (by
    simp only [hr4, hr3, State.charge_wlen, State.setW_wlen]; omega)) ?_)
  set r5 := (r4.setW "bc.pe" (r2.wa "gSt" ((u : ℕ) + 1))).charge 1 with hr5
  have hU25 : Unchanged r2 r5 [] [] ["ru", "bc.p", "bc.pe"] [] :=
    ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      simp [hr5, hr4, hr3, State.setW, State.charge, hz.1, hz.2.1, hz.2.2],
      fun _ _ => rfl, rfl, rfl⟩
  have hc5 : r5.cost = r2.cost + 3 := by simp [hr5, hr4, hr3, State.charge]
  have ha := hcsr2.le u
  have hgSt2 : r2.wa "gSt" = st.wa "gSt" := by
    rw [(hU2.warr "gSt" (by decide)).1, (hU1.warr "gSt" (fun h => e3 _ h (by simp))).1]
  have hdegu : r2.wa "gSt" ((u : ℕ) + 1) - r2.wa "gSt" u ≤ δ := by rw [hgSt2]; exact hdeg u
  have hcardE : (T.erase u).card + 1 = T.card := Finset.card_erase_add_one huT
  have hb := hcsr2.le_m u
  -- step 6: the relaxation loop
  refine (edgeLoop_spec H r5 d Hh c0 (T.erase u) u B (r2.wa "gSt" u) (r2.wa "gSt" ((u : ℕ) + 1))
    (hL2.of_unchanged hU25 (by simp) (by simp) (by omega))
    (graphAt_of_unchanged hU25 (by simp) (by simp) hg2)
    (H.HR_frame hHR2 hU25 (by simp) (fun a ha h => hok.fwr a ha (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)))
    (by rw [show vc (G := G) r5 = vc r2 from vc_of_unchanged hU25 (by simp)]
        exact hK2.of_unchanged hU25 (by decide) (by decide) (by decide))
    (by simp [hr5, hr4, hr3, State.setW, State.charge]) (by simp [hr5, hr4, State.setW, State.charge])
    (by simp [hr5, State.setW, State.charge]) ha hb
    (fun e h1 h2 => (hcsr2.src e u).mpr ⟨h1, h2⟩) hu_fin
    (fun y hy => hTfin y (Finset.mem_of_mem_erase hy))
    (by
      rw [hc5]
      have hdeg : r2.wa "gSt" ((u : ℕ) + 1) - r2.wa "gSt" u ≤ G.m := by omega
      have : (r2.wa "gSt" ((u : ℕ) + 1) - r2.wa "gSt" u) * (H.Cop + 77) ≤ (G.m + 1) * (H.Cop + 77) :=
        Nat.mul_le_mul_right _ (by omega)
      unfold exSlack at hbud
      simp only [show r5.cap = st.cap from hcap4]
      omega)
    (by rw [show r5.cap = st.cap from hcap4]; exact hm)
    (by rw [show r5.cap = st.cap from hcap4]; exact hcapN) (by omega) e1 e2 e3 e4 e5 e6).mono ?_
  rintro r ⟨P, Hh', T', d', hTc, hnd, hmem, hfold, hL', hext, hHR', hg', hK', hT', hu', hru', hU',
    hcl, hch⟩
  have hvc5 : vc (G := G) r5 = vc st := by
    rw [show vc (G := G) r5 = vc r2 from vc_of_unchanged hU25 (by simp), hvc2, hvc1]
  have hU5r : Unchanged r2 r (eWA H) (eVA H) ("ru" :: "bc.pe" :: eWR H) (eVR H) :=
    (hU25.comp hU').mono (by simp) (by simp)
      (List.append_subset.mpr ⟨List.cons_subset.mpr ⟨List.mem_cons_self,
        List.cons_subset.mpr ⟨by simp [eWR], List.cons_subset.mpr ⟨by simp,
          List.nil_subset _⟩⟩⟩,
        List.subset_cons_of_subset _ (List.subset_cons_of_subset _ (List.Subset.refl _))⟩)
      (by simp)
  have hlen := length_of_mem_Ico hb hnd hmem
  refine ⟨u, P, Hh', T', d', by omega, huT, hmin, ⟨hnd, fun e => by
      rw [hmem e, Finset.mem_singleton]; exact (hcsr2.src e u).symm⟩, hfold, hL', ?_, hHR', hg',
    hcsr2.of_unchanged hU5r (by simp [eWA, labW]; intro h; exact e3 _ h (by simp)), hK', ?_, hT',
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hvc5] at hext; exact hext
  · refine ⟨xs ++ [(u : ℕ)], ?_, ?_, ?_⟩
    · have e7 := hU5r.warr "U" (by simp [eWA, labW]; intro h; exact hok.wa _ h (by simp))
      have e8 := hU5r.warr "U.len" (by simp [eWA, labW]; intro h; exact hok.wa _ h (by simp))
      exact RamLevel.RowRep.of_eq hR2 e7.2 e8.2 (by rw [e8.1]) (fun i _ => by rw [e7.1])
    · refine List.nodup_append.mpr ⟨hnd1, List.nodup_singleton _, fun x hx y hy => ?_⟩
      rw [List.mem_singleton] at hy
      intro hxy
      obtain ⟨w, hw, hwx⟩ := (hmem1 x).mp hx
      apply huU
      have : w = u := Fin.ext (by rw [hwx, hxy, hy])
      rw [← this]; exact hw
    · intro x
      rw [List.mem_append, hmem1, List.mem_singleton]
      constructor
      · rintro (⟨w, hw, rfl⟩ | rfl)
        · exact ⟨w, Finset.mem_insert_of_mem hw, rfl⟩
        · exact ⟨u, Finset.mem_insert_self _ _, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        rcases Finset.mem_insert.mp hw with rfl | hw
        · right; rfl
        · left; exact ⟨w, hw, rfl⟩
  · rw [hU5r.wreg "lvl" (by simp [eWR, relaxW]; intro h; exact hok.wr _ h (by simp)), hlvl2]
  · rw [hU5r.wreg "n" (by simp [eWR, relaxW]; intro h; exact hok.wr _ h (by simp)), hn2]
  · have h12 : Unchanged st r2 (H.wa ++ ["U", "U.len"]) (H.va ++ []) (H.wr ++ []) (H.vr ++ []) :=
      hU1.comp hU2
    refine (h12.comp hU5r).mono ?_ ?_ ?_ ?_
    · exact List.append_subset.mpr ⟨List.append_subset.mpr ⟨List.subset_append_of_subset_left _
        (List.subset_append_right _ _), List.subset_append_right _ _⟩,
        List.subset_append_left _ _⟩
    · exact List.append_subset.mpr ⟨List.append_subset.mpr ⟨List.subset_append_right _ _,
        List.nil_subset _⟩, List.Subset.refl _⟩
    · refine List.append_subset.mpr ⟨List.append_subset.mpr ⟨?_, List.nil_subset _⟩,
        List.Subset.refl _⟩
      intro a ha
      simp only [eWR, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ha)))))
    · exact List.append_subset.mpr ⟨List.append_subset.mpr ⟨List.subset_append_right _ _,
        List.nil_subset _⟩, List.Subset.refl _⟩
  · omega
  · rw [hlen]; omega
  · intro i hi
    rw [(hU5r.warr "U" (by simp [eWA, labW]; intro h; exact hok.wa _ h (by simp))).1,
      hUi2 i (by simp; omega), (hU1.warr "U" (fun h => hok.wa _ h (by simp))).1]
  · intro j hj
    rw [(hU5r.warr "U.len" (by simp [eWA, labW]; intro h; exact hok.wa _ h (by simp))).1,
      hUl2 j hj, (hU1.warr "U.len" (fun h => hok.wa _ h (by simp))).1]

/-! ## The base loop (BC.3–BC.7) -/

/-- `while (hp_n > 0) * (U.len[0] < τ) do extractBody` -/
def baseLoop (H : HeapI G s) : Stmt :=
  .while (mul (lt (lit 0) (var "hp_n")) (lt (load "U.len" (lit 0)) (var "bc.tau"))) (extractBody H)

theorem URow.len {st : State ℝ≥0} {U : Finset (Fin G.n)} (h : URow st U) :
    st.wa "U.len" 0 = U.card ∧ 0 < st.wlen "U.len" := by
  obtain ⟨xs, hR, hnd, hmem⟩ := h
  exact ⟨by rw [hR.2.2.2.1, length_of_mem_image hnd hmem], by have := hR.2.2.1; omega⟩

open Classical in
/-- One Layer-A step of the base loop from the data of `extractBody_spec`. -/
theorem baseStep {DC : BM.DCost} {B : WLab G s} {τ : ℕ} {d d' : Labels G s}
    {T T' U : Finset (Fin G.n)} {u : Fin G.n} {L : List (Fin G.m)}
    (huT : u ∈ T) (hmin : ∀ y ∈ T, d u ≤ d y) (hcard : U.card < τ) (hL : BM.Enumerates G L {u})
    (hfold : L.foldl (BM.relaxIns G s B none) (d, BM.Dof (T.erase u) d) = (d', BM.Dof T' d'))
    {st' : Labels G s × DS G s × Finset (Fin G.n)} {c : ℕ}
    (hrest : BM.BaseLoopC G s DC B τ (d', BM.Dof T' d', insert u U) st' c) :
    BM.BaseLoopC G s DC B τ (d, BM.Dof T d, U) st' (c + 1 + DC.bext + L.length * (1 + DC.bins)) := by
  have hD : BM.Dof T d u = some (d u) := by simp [BM.Dof_apply, huT]
  refine BM.BaseLoopC.step d (BM.Dof T d) U u (d u) L st' c hD (fun y v hy => ?_) hcard hL ?_
  · rw [BM.Dof_apply] at hy
    split_ifs at hy with hyT
    simp only [Option.some.injEq] at hy
    rw [← hy]; exact hmin y hyT
  · rw [BM.Dof_deleteSet, hfold]; exact hrest

theorem BInv.fin_of_Dof {B : WLab G s} {S : Finset (Fin G.n)} {d0 d : Labels G s}
    {T U : Finset (Fin G.n)} (h : BM.BInv G s B S d0 d (BM.Dof T d) U) : ∀ y ∈ T, d y ≠ ⊤ := by
  intro y hy
  have := (h.stored y (d y) (by simp [BM.Dof_apply, hy])).2
  exact ne_top_of_lt this

open Classical in
/-- **The base loop** (BC.3–BC.7): refines `BaseLoopC` with factor `1` (the heap costs are
charged to `DC.bext` / `DC.bins`), keeping `BInv`. -/
theorem baseLoop_spec (H : HeapI G s) (hok : HeapOK H) (DC : BM.DCost)
    (hbext : H.Cop + 7 ≤ DC.bext) (hbins : H.Cop + 76 ≤ DC.bins)
    (st0 : State ℝ≥0) (B : WLab G s) (S : Finset (Fin G.n)) (d0 : Labels G s)
    (hpre : CallPre B S d0) (τ δ : ℕ) (d : Labels G s) (Hh : Fin G.n → ℕ → List (Fin G.m))
    (c0 : ℕ) (T U : Finset (Fin G.n))
    (hBI : BM.BInv G s B S d0 d (BM.Dof T d) U) (hUτ : U.card ≤ τ)
    (hL : LabAt st0 d Hh c0) (hg : GraphAt st0 G) (hcsr : CSRAt st0 G) (hHR : H.HR st0 T d)
    (hK : WHolds st0 KB "bc.bf" Hh (vc st0) B) (hU : URow st0 U) (hlvl : st0.w "lvl" = 0)
    (hn : st0.w "n" = G.n) (htau : st0.w "bc.tau" = τ)
    (hdeg : ∀ u : Fin G.n, st0.wa "gSt" ((u : ℕ) + 1) - st0.wa "gSt" u ≤ δ)
    (hsz : T.card + δ * (τ - U.card) ≤ H.hsz)
    (hbud : st0.cost + (τ - U.card + 1) * exSlack H G ≤ c0 + st0.cap) (hm : G.m + 2 ≤ st0.cap)
    (hcapN : 2 * G.n + 3 < st0.cap) (hτcap : τ + 2 ≤ st0.cap) :
    Runs realOps (baseLoop H) st0 (fun r => ∃ (d' : Labels G s) (T' U' : Finset (Fin G.n))
      (Hh' : Fin G.n → ℕ → List (Fin G.m)) (c : ℕ),
      BM.BaseLoopC G s DC B τ (d, BM.Dof T d, U) (d', BM.Dof T' d', U') c ∧
      BM.BInv G s B S d0 d' (BM.Dof T' d') U' ∧ (T' = ∅ ∨ τ ≤ U'.card) ∧ T'.card ≤ H.hsz ∧
      LabAt r d' Hh' c0 ∧ HExt Hh (vc st0) Hh' (vc r) ∧ H.HR r T' d' ∧ GraphAt r G ∧
      CSRAt r G ∧ WHolds r KB "bc.bf" Hh' (vc r) B ∧ URow r U' ∧ r.w "lvl" = 0 ∧
      r.w "n" = G.n ∧ r.w "bc.tau" = τ ∧
      Unchanged st0 r (eWA H ++ ["U", "U.len"]) (eVA H) ("ru" :: "bc.pe" :: eWR H) (eVR H) ∧
      st0.cost ≤ r.cost ∧ r.cost ≤ st0.cost + c ∧
      r.cost ≤ st0.cost + (τ - U.card + 1) * exSlack H G ∧
      (∀ i, G.n ≤ i → r.wa "U" i = st0.wa "U" i) ∧ (∀ j, j ≠ 0 → r.wa "U.len" j = st0.wa "U.len" j)) := by
  have hcap1 : 1 < st0.cap := by omega
  refine runs_while_nat (fun k st => ∃ (d' : Labels G s) (T' U' : Finset (Fin G.n))
      (Hh' : Fin G.n → ℕ → List (Fin G.m)) (acc : ℕ),
      k = τ - U'.card ∧ U'.card ≤ τ ∧ U.card ≤ U'.card ∧
      BM.BInv G s B S d0 d' (BM.Dof T' d') U' ∧
      (∀ st' c, BM.BaseLoopC G s DC B τ (d', BM.Dof T' d', U') st' c →
        BM.BaseLoopC G s DC B τ (d, BM.Dof T d, U) st' (acc + c)) ∧
      LabAt st d' Hh' c0 ∧ HExt Hh (vc st0) Hh' (vc st) ∧ H.HR st T' d' ∧ GraphAt st G ∧
      CSRAt st G ∧ WHolds st KB "bc.bf" Hh' (vc st) B ∧ URow st U' ∧ st.w "lvl" = 0 ∧
      st.w "n" = G.n ∧ st.w "bc.tau" = τ ∧
      (∀ u : Fin G.n, st.wa "gSt" ((u : ℕ) + 1) - st.wa "gSt" u ≤ δ) ∧
      T'.card + δ * (τ - U'.card) ≤ H.hsz ∧
      Unchanged st0 st (eWA H ++ ["U", "U.len"]) (eVA H) ("ru" :: "bc.pe" :: eWR H) (eVR H) ∧
      st0.cost ≤ st.cost ∧ st.cost ≤ st0.cost + acc ∧
      st.cost ≤ st0.cost + (U'.card - U.card) * exSlack H G ∧
      (∀ i, G.n ≤ i → st.wa "U" i = st0.wa "U" i) ∧
      (∀ j, j ≠ 0 → st.wa "U.len" j = st0.wa "U.len" j)) _ ?_ (τ - U.card) st0
    ⟨d, T, U, Hh, 0, rfl, hUτ, le_rfl, hBI, fun st' c h => by simpa using h, hL, HExt.refl _ _,
      hHR, hg, hcsr, hK, hU, hlvl, hn, htau, hdeg, hsz, Unchanged.refl _ _ _ _ _, le_rfl, by simp,
      by simp, fun _ _ => rfl, fun _ _ => rfl⟩
  rintro k st ⟨d', T', U', Hh', acc, rfl, hU'τ, hUU', hBI', hpref, hL', hext, hHR', hg', hcsr', hK',
    hUr', hlvl', hn', htau', hdeg', hsz', hUn', hcl, hca, hcb, hFU, hFL⟩
  have hcapst : st.cap = st0.cap := hUn'.cap
  have hn_eq : st.w "hp_n" = T'.card := H.size hHR'
  obtain ⟨hUlen, hUlenl⟩ := hUr'.len
  -- the loop test
  have hev : evalW st (mul (lt (lit 0) (var "hp_n")) (lt (load "U.len" (lit 0)) (var "bc.tau"))) =
      some ((if 0 < T'.card then 1 else 0) * (if U'.card < τ then 1 else 0)) := by
    have e1 : evalW st (lt (lit 0) (var "hp_n")) = some (if 0 < T'.card then 1 else 0) := by
      rw [evalW_lt_of (evalW_lit_of (by omega)) (by rw [evalW_var]) (by omega), hn_eq]
    have e2 : evalW st (lt (load "U.len" (lit 0)) (var "bc.tau")) =
        some (if U'.card < τ then 1 else 0) := by
      rw [evalW_lt_of (evalW_load_of (evalW_lit_of (by omega)) hUlenl) (by rw [evalW_var])
        (by omega), hUlen, htau']
    rw [evalW_mul', e1, e2]
    simp only [Option.bind_some]
    apply fit_of_lt
    split_ifs <;> omega
  refine ⟨_, hev, fun hx => ?_, fun hx => ?_⟩
  · -- one more extraction
    have hT'ne : 0 < T'.card := by
      by_contra h; simp only [h, if_false, zero_mul, ne_eq, not_true_eq_false] at hx
    have hUlt : U'.card < τ := by
      by_contra h; simp only [h, if_false, mul_zero, ne_eq, not_true_eq_false] at hx
    have hTne : T'.Nonempty := Finset.card_pos.mp hT'ne
    have hTfin := BInv.fin_of_Dof hBI'
    have hTU : ∀ y ∈ T', y ∉ U' := fun y hy => BM.notMem_U_of_bInv hBI' hy
    have hU1 : Unchanged st (st.charge 1) [] [] [] [] := Unchanged.charge st 1 [] [] [] []
    have hbud' : (st.charge 1).cost + exSlack H G ≤ c0 + (st.charge 1).cap := by
      simp only [State.charge_cost, State.charge_cap, hcapst]
      have e1 : (U'.card - U.card) * exSlack H G + exSlack H G = (U'.card - U.card + 1) * exSlack H G := by
        ring
      have h2 : (U'.card - U.card + 1) * exSlack H G ≤ (τ - U.card) * exSlack H G :=
        Nat.mul_le_mul_right _ (by omega)
      have e2 : (τ - U.card) * exSlack H G + exSlack H G = (τ - U.card + 1) * exSlack H G := by ring
      have h3 : 1 ≤ exSlack H G := by unfold exSlack; omega
      omega
    have hsz1 : T'.card + δ ≤ H.hsz := by
      have : δ ≤ δ * (τ - U'.card) := Nat.le_mul_of_pos_right δ (by omega)
      omega
    refine ((extractBody_spec H hok (st.charge 1) d' Hh' c0 T' U' B
      (hL'.of_unchanged hU1 (by simp) (by simp) (by simp [State.charge]))
      (graphAt_of_unchanged hU1 (by simp) (by simp) hg') (hcsr'.of_unchanged hU1 (by simp))
      (H.HR_frame hHR' hU1 (by simp) (by simp))
      (by have := hK'.of_unchanged hU1 (by simp) (by simp) (by simp)
          rwa [show vc (G := G) (st.charge 1) = vc st from rfl])
      (hUr'.of_unchanged hU1 (by simp) (by simp)) (by simp [State.charge, hlvl'])
      (by simp [State.charge, hn']) hTne hTfin hTU hbud'
      (by simp only [State.charge_cap, hcapst]; exact hm)
      (by simp only [State.charge_cap, hcapst]; exact hcapN) δ
      (by intro u; simp only [State.charge_wa]; exact hdeg' u) hsz1).mono ?_)
    rintro r ⟨u, L, Hh'', T'', d'', hTc, huT, hmin, hLe, hfold, hL'', hext', hHR'', hg'', hcsr'',
      hK'', hUr'', hT'', hlvl'', hn'', hUn'', hcl', hch', hFU', hFL'⟩
    have huU : u ∉ U' := hTU u huT
    have hcardU : (insert u U').card = U'.card + 1 := Finset.card_insert_of_notMem huU
    -- Layer A: the invariant and the step
    have hBI'' : BM.BInv G s B S d0 d'' (BM.Dof T'' d'') (insert u U') := by
      have hDu : BM.Dof T' d' u = some (d' u) := by simp [BM.Dof_apply, huT]
      have := BM.bInv_step hpre hBI' hDu (fun y v hy => by
        rw [BM.Dof_apply] at hy
        split_ifs at hy with hyT
        simp only [Option.some.injEq] at hy
        rw [← hy]; exact hmin y hyT) hLe
      rw [BM.Dof_deleteSet, hfold] at this
      exact this
    have hdeg'' : ∀ w : Fin G.n, r.wa "gSt" ((w : ℕ) + 1) - r.wa "gSt" w ≤ δ := by
      have hnot : "gSt" ∉ eWA H ++ ["U", "U.len"] := by
        intro h
        simp only [eWA, List.mem_append] at h
        rcases h with (h | h) | h
        · exact absurd h (by decide)
        · exact hok.wa _ h (by simp)
        · exact absurd h (by decide)
      have e := hUn''.warr "gSt" hnot
      intro w; rw [e.1]; exact hdeg' w
    refine ⟨τ - (U'.card + 1), by omega, d'', T'', insert u U', Hh'',
      acc + (1 + DC.bext + L.length * (1 + DC.bins)), by rw [hcardU], by omega,
      le_trans hUU' (Finset.card_le_card (Finset.subset_insert _ _)), hBI'', fun st' c h => ?_,
      hL'', ?_, hHR'', hg'', hcsr'', hK'', hUr'', hlvl'', hn'', ?_, hdeg'', ?_, ?_, ?_, ?_, ?_,
      fun i hi => (hFU' i hi).trans (hFU i hi), fun j hj => (hFL' j hj).trans (hFL j hj)⟩
    · have := hpref st' _ (baseStep huT hmin hUlt hLe hfold h)
      have e : acc + (c + 1 + DC.bext + L.length * (1 + DC.bins)) =
          acc + (1 + DC.bext + L.length * (1 + DC.bins)) + c := by ring
      rwa [e] at this
    · have e1 : vc (G := G) (st.charge 1) = vc st := rfl
      rw [e1] at hext'; exact hext.trans hext'
    · rw [hUn''.wreg "bc.tau" (by
        simp only [eWR, relaxW, List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or]
        refine ⟨by decide, by decide, by decide, by decide, by decide, ⟨by decide, by decide,
          by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, by decide, by decide, by decide⟩, fun h => hok.wr _ h (by simp)⟩)]
      simp [State.charge, htau']
    · rw [hcardU]
      have : T''.card + δ * (τ - (U'.card + 1)) + 1 ≤ T'.card + δ * (τ - U'.card) := by
        have e : δ * (τ - U'.card) = δ * (τ - (U'.card + 1)) + δ := by
          rw [show τ - U'.card = τ - (U'.card + 1) + 1 by omega]; ring
        omega
      omega
    · exact hUn'.trans ((Unchanged.charge st 1 _ _ _ _).trans hUn'')
    · simp only [State.charge_cost] at hcl'; omega
    · simp only [State.charge_cost] at hch'
      have : L.length * (H.Cop + 77) ≤ L.length * (1 + DC.bins) := Nat.mul_le_mul_left _ (by omega)
      omega
    · simp only [State.charge_cost] at hch'
      rw [hcardU]
      have hlen : L.length ≤ G.m := by
        have := hLe.1.length_le_card
        simpa using this
      have hex : L.length * (H.Cop + 77) + H.Cop + 8 ≤ exSlack H G := by
        have : L.length * (H.Cop + 77) ≤ (G.m + 1) * (H.Cop + 77) :=
          Nat.mul_le_mul_right _ (by omega)
        unfold exSlack; omega
      have e : (U'.card + 1 - U.card) * exSlack H G = (U'.card - U.card) * exSlack H G + exSlack H G := by
        rw [show U'.card + 1 - U.card = U'.card - U.card + 1 by omega]; ring
      omega
  · -- exit: the heap is empty or the cap is reached
    have hstop : T' = ∅ ∨ τ ≤ U'.card := by
      by_cases h1 : 0 < T'.card
      · right; by_contra h2
        rw [if_pos h1, if_pos (by omega)] at hx; exact one_ne_zero hx
      · left; exact Finset.card_eq_zero.mp (by omega)
    refine ⟨d', T', U', Hh', acc + 1, hpref _ 1 (BM.BaseLoopC.stop _ (by
        rcases hstop with h | h
        · left; exact (BM.Dof_isEmpty_iff T' d').mpr h
        · right; exact h)), hBI', hstop, by omega,
      hL'.of_unchanged (Unchanged.charge st 1 [] [] [] []) (by simp) (by simp) (by simp [State.charge]),
      by have e1 : vc (G := G) (st.charge 1) = vc st := rfl
         rw [e1]; exact hext,
      H.HR_frame hHR' (Unchanged.charge st 1 [] [] [] []) (by simp) (by simp),
      graphAt_of_unchanged (Unchanged.charge st 1 [] [] [] []) (by simp) (by simp) hg',
      hcsr'.of_unchanged (Unchanged.charge st 1 [] [] [] []) (by simp),
      by have := hK'.of_unchanged (Unchanged.charge st 1 [] [] [] []) (by simp) (by simp) (by simp)
         rwa [show vc (G := G) (st.charge 1) = vc st from rfl],
      hUr'.of_unchanged (Unchanged.charge st 1 [] [] [] []) (by simp) (by simp),
      by simp [State.charge, hlvl'], by simp [State.charge, hn'], by simp [State.charge, htau'],
      hUn'.trans (Unchanged.charge st 1 _ _ _ _), by simp [State.charge]; omega,
      by simp [State.charge]; omega, ?_, fun i hi => hFU i hi, fun j hj => hFL j hj⟩
    have h1 : (U'.card - U.card) * exSlack H G ≤ (τ - U.card) * exSlack H G :=
      Nat.mul_le_mul_right _ (by omega)
    have e2 : (τ - U.card + 1) * exSlack H G = (τ - U.card) * exSlack H G + exSlack H G := by ring
    have h3 : 1 ≤ exSlack H G := by unfold exSlack; omega
    simp only [State.charge_cost]; omega

/-! ## BC.1: the frontier `S` enters the heap -/

/-- The S row (level 0) lists the finite set `S` without repetition. -/
def SRow (st : State ℝ≥0) (S : Finset (Fin G.n)) : Prop :=
  ∃ xs : List ℕ, RamLevel.RowRep st "S" "S.len" G.n 0 xs ∧ xs.Nodup ∧
    ∀ x : ℕ, x ∈ xs ↔ ∃ u ∈ S, (u : ℕ) = x

/-- The vertices of a list of ids. -/
def Tof (l : List ℕ) : Finset (Fin G.n) := Finset.univ.filter fun u => (u : ℕ) ∈ l

/-- `k := 0; while k < S.len[0] do (hp_x := S[k]; push; k := k + 1)` -/
def pushS (H : HeapI G s) : Stmt :=
  seq (wset "bc.k" (lit 0))
  (.while (lt (var "bc.k") (load "S.len" (lit 0)))
     (seq (wset "hp_x" (load "S" (var "bc.k")))
     (seq H.push (wset "bc.k" (add (var "bc.k") (lit 1))))))

theorem Tof_take_succ {xs : List ℕ} {i : ℕ} (hi : i < xs.length) (hx : xs[i] < G.n) :
    Tof (G := G) (xs.take (i + 1)) = insert ⟨xs[i], hx⟩ (Tof (xs.take i)) := by
  ext u
  simp only [Tof, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  rw [List.take_succ, List.mem_append]
  simp only [List.getElem?_eq_getElem hi, Option.toList_some, List.mem_singleton]
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · left; exact Fin.ext h
  · rintro (h | h)
    · right; rw [h]
    · exact Or.inl h

theorem Tof_card_le {l : List ℕ} : (Tof (G := G) l).card ≤ l.length := by
  classical
  have h1 : (Tof (G := G) l).map Fin.valEmbedding ⊆ l.toFinset := by
    intro x hx
    simp only [Finset.mem_map, Tof, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    exact List.mem_toFinset.mpr hu
  calc (Tof (G := G) l).card = ((Tof (G := G) l).map Fin.valEmbedding).card :=
        (Finset.card_map _).symm
    _ ≤ l.toFinset.card := Finset.card_le_card h1
    _ ≤ l.length := List.toFinset_card_le l

theorem Tof_eq {xs : List ℕ} {S : Finset (Fin G.n)} (hmem : ∀ x : ℕ, x ∈ xs ↔ ∃ u ∈ S, (u : ℕ) = x) :
    Tof (G := G) xs = S := by
  ext u
  simp only [Tof, Finset.mem_filter, Finset.mem_univ, true_and, hmem]
  constructor
  · rintro ⟨w, hw, hwu⟩; rw [← Fin.ext hwu]; exact hw
  · intro hu; exact ⟨u, hu, rfl⟩

/-- **BC.1**: every vertex of `S` enters the (empty) heap, keyed by the initial labels. -/
theorem pushS_spec (H : HeapI G s) (hok : HeapOK H) (st : State ℝ≥0) (S : Finset (Fin G.n))
    (d0 : Labels G s) (Hh : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ)
    (hS : SRow st S) (hHR : H.HR st ∅ d0) (hL : LabAt st d0 Hh c0) (hSfin : ∀ y ∈ S, d0 y ≠ ⊤)
    (hsz : S.card ≤ H.hsz) (hbud : st.cost + (S.card + 1) * (H.Cop + 3) + 2 ≤ c0 + st.cap)
    (hcapN : 2 * G.n + 3 < st.cap) :
    Runs realOps (pushS H) st (fun r => H.HR r S d0 ∧ LabAt r d0 Hh c0 ∧
      Unchanged st r H.wa H.va ("bc.k" :: "hp_x" :: H.wr) H.vr ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + S.card * (H.Cop + 3) + 2) := by
  obtain ⟨xs, hR, hnd, hmem⟩ := hS
  have hlen : xs.length = S.card := length_of_mem_image hnd hmem
  have hxn : ∀ i (h : i < xs.length), xs[i] < G.n := by
    intro i h
    obtain ⟨u, -, hu⟩ := (hmem xs[i]).mp (List.getElem_mem h)
    rw [← hu]; exact u.isLt
  have hxS : ∀ i (h : i < xs.length), (⟨xs[i], hxn i h⟩ : Fin G.n) ∈ S := by
    intro i h
    obtain ⟨u, hu, hux⟩ := (hmem xs[i]).mp (List.getElem_mem h)
    have : u = ⟨xs[i], hxn i h⟩ := Fin.ext hux
    rw [← this]; exact hu
  have hc0 : 0 < st.cap := by omega
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of hc0) ?_)
  set st1 := (st.setW "bc.k" 0).charge 1 with hst1
  have hU01 : Unchanged st st1 [] [] ["bc.k"] [] :=
    ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun z hz => by
      simp only [List.mem_singleton] at hz; simp [hst1, State.setW, State.charge, hz],
      fun _ _ => rfl, rfl, rfl⟩
  refine runs_while_nat (fun k r => ∃ i, k = xs.length - i ∧ i ≤ xs.length ∧ r.w "bc.k" = i ∧
      H.HR r (Tof (xs.take i)) d0 ∧ LabAt r d0 Hh c0 ∧
      RamLevel.RowRep r "S" "S.len" G.n 0 xs ∧
      Unchanged st r H.wa H.va ("bc.k" :: "hp_x" :: H.wr) H.vr ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + 1 + i * (H.Cop + 3)) _ ?_ (xs.length) st1
    ⟨0, by simp, Nat.zero_le _, by simp [hst1, State.setW, State.charge], by
      rw [show Tof (G := G) (xs.take 0) = ∅ by ext u; simp [Tof]]
      exact H.HR_frame hHR hU01 (by simp) (fun a ha h => by
        rw [List.mem_singleton] at h
        exact (hok.fwr a ha) (by rw [h]; simp)),
      hL.of_unchanged hU01 (by simp) (by simp) (by simp [hst1, State.charge]),
      hR.of_eq rfl rfl rfl (fun _ _ => rfl),
      hU01.mono (by simp) (by simp) (by simp) (by simp), by simp [hst1, State.charge],
      by simp [hst1, State.charge]⟩
  rintro k r ⟨i, rfl, hi, hk, hHR', hL', hR', hU', hcl, hch⟩
  have hcapr : r.cap = st.cap := hU'.cap
  have hSl : r.wa "S.len" 0 = xs.length := hR'.2.2.2.1
  have hSll : 0 < r.wlen "S.len" := by have := hR'.2.2.1; omega
  refine ⟨if i < xs.length then 1 else 0, by
    rw [evalW_lt_of (by rw [evalW_var, hk]) (evalW_load_of (evalW_lit_of (by omega)) hSll)
      (by omega), hSl], fun hx => ?_, fun hx => ?_⟩
  · have hilt : i < xs.length := by by_contra h; rw [if_neg h] at hx; exact hx rfl
    set v : Fin G.n := ⟨xs[i], hxn i hilt⟩ with hv
    have hTc : (Tof (G := G) (xs.take i)).card + 1 ≤ H.hsz := by
      have := Tof_card_le (G := G) (l := xs.take i)
      simp only [List.length_take] at this
      omega
    -- `hp_x := S[k]`
    have hload : evalW (r.charge 1) (load "S" (var "bc.k")) = some (xs[i]) := by
      have hidx : i < (r.charge 1).wlen "S" := by
        simp only [State.charge_wlen]; have := hR'.2.1
        have : xs.length ≤ G.n := hR'.1
        nlinarith
      rw [evalW_load_of (j := i) (by rw [evalW_var]; simp [State.charge, hk]) hidx]
      have := hR'.2.2.2.2 i hilt
      simp only [zero_mul, zero_add] at this
      simp only [State.charge_wa]; rw [this]
    refine runs_seq (runs_wset hload ?_)
    set r2 := ((r.charge 1).setW "hp_x" xs[i]).charge 1 with hr2
    have hU12 : Unchanged r r2 [] [] ["hp_x"] [] :=
      ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun z hz => by
        simp only [List.mem_singleton] at hz; simp [hr2, State.setW, State.charge, hz],
        fun _ _ => rfl, rfl, rfl⟩
    have hL2 : LabAt r2 d0 Hh c0 := hL'.of_unchanged hU12 (by simp) (by simp)
      (by simp only [hr2, State.charge_cost, State.setW_cost]; omega)
    have hHR2 : H.HR r2 (Tof (xs.take i)) d0 := H.HR_frame hHR' hU12 (by simp)
      (fun a ha h => by rw [List.mem_singleton] at h; exact (hok.fwr a ha) (by rw [h]; simp))
    have hc2 : r2.cost = r.cost + 2 := by simp [hr2, State.charge]
    have hcap2 : r2.cap = st.cap := hcapr
    refine runs_seq ((H.push_spec r2 (Tof (xs.take i)) d0 d0 Hh c0 v hHR2 hL2 (fun _ _ => rfl)
      le_rfl (fun y hy => hSfin y (by
        simp only [Tof, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        obtain ⟨u, hu, hux⟩ := (hmem y).mp (List.mem_of_mem_take hy)
        rw [← Fin.ext hux]; exact hu)) (hSfin v (hxS i hilt))
      (by simp [hr2, State.setW, State.charge, hv]) (by
        rw [hc2, hcap2]
        have : i * (H.Cop + 3) + (H.Cop + 3) ≤ (S.card + 1) * (H.Cop + 3) := by
          have h1 : i + 1 ≤ S.card + 1 := by omega
          calc i * (H.Cop + 3) + (H.Cop + 3) = (i + 1) * (H.Cop + 3) := by ring
            _ ≤ (S.card + 1) * (H.Cop + 3) := Nat.mul_le_mul_right _ h1
        nlinarith) (by rw [hcap2]; exact hcapN) hTc).mono ?_)
    rintro r3 ⟨hHR3, hU3, hc3l, hc3⟩
    have hk3 : r3.w "bc.k" = i := by
      rw [hU3.wreg "bc.k" (fun h => hok.wr _ h (by simp)), hU12.wreg "bc.k" (by simp)]
      simp [State.charge, hk]
    have hxlen : xs.length ≤ G.n := hR'.1
    refine runs_wset (a := i + 1) (evalW_add_of (by rw [evalW_var, hk3])
      (evalW_lit_of (by rw [hU3.cap, hcap2]; omega)) (by rw [hU3.cap, hcap2]; omega)) ?_
    set r4 := (r3.setW "bc.k" (i + 1)).charge 1 with hr4
    have hU34 : Unchanged r3 r4 [] [] ["bc.k"] [] :=
      ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun z hz => by
        simp only [List.mem_singleton] at hz; simp [hr4, State.setW, State.charge, hz],
        fun _ _ => rfl, rfl, rfl⟩
    refine ⟨xs.length - (i + 1), by omega, i + 1, rfl, by omega, by simp [hr4, State.setW, State.charge],
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Tof_take_succ hilt (hxn i hilt)]
      exact H.HR_frame hHR3 hU34 (by simp)
        (fun a ha h => by rw [List.mem_singleton] at h; exact (hok.fwr a ha) (by rw [h]; simp))
    · exact (hL2.of_unchanged hU3 (fun a ha h => H.wa_lab a ha h) H.va_lab hc3l).of_unchanged hU34
        (by simp) (by simp) (by simp [hr4, State.charge])
    · have e1 := hU3.warr "S" (fun h => hok.wa _ h (by simp))
      have e2 := hU3.warr "S.len" (fun h => hok.wa _ h (by simp))
      exact RamLevel.RowRep.of_eq hR' (by rw [show r4.wlen = r3.wlen from rfl, e1.2]; rfl)
        (by rw [show r4.wlen = r3.wlen from rfl, e2.2]; rfl) (by rw [show r4.wa = r3.wa from rfl, e2.1]; rfl)
        (fun j _ => by rw [show r4.wa = r3.wa from rfl, e1.1]; rfl)
    · refine hU'.trans ((hU12.mono (by simp) (by simp) (by simp) (by simp)).trans
        ((hU3.mono (by simp) (by simp) (List.subset_cons_of_subset _ (List.subset_cons_of_subset _
          (List.Subset.refl _))) (by simp)).trans (hU34.mono (by simp) (by simp) (by simp) (by simp))))
    · simp only [hr4, State.charge_cost, State.setW_cost]; omega
    · simp only [hr4, State.charge_cost, State.setW_cost]
      have e : (i + 1) * (H.Cop + 3) = i * (H.Cop + 3) + (H.Cop + 3) := by ring
      omega
  · -- exit
    have hieq : i = xs.length := by
      by_contra h; rw [if_pos (by omega)] at hx; exact one_ne_zero hx
    subst hieq
    refine ⟨?_, hL'.of_unchanged (Unchanged.charge r 1 [] [] [] []) (by simp) (by simp)
      (by simp [State.charge]), hU'.trans (Unchanged.charge r 1 _ _ _ _), by simp [State.charge]; omega, ?_⟩
    · rw [List.take_length, Tof_eq hmem] at hHR'
      exact H.HR_frame hHR' (Unchanged.charge r 1 [] [] [] []) (by simp) (by simp)
    · simp only [State.charge_cost]; rw [← hlen]; omega

/-! ## BC.8–BC.9: the returned bound `B'` -/

/-- Slot numbering: `B`, `B_low`, `B'`, `B_i` of level `l`. -/
def slotB (l : ℕ) : ℕ := 4 * l
def slotBlow (l : ℕ) : ℕ := 4 * l + 1
def slotBp (l : ℕ) : ℕ := 4 * l + 2
def slotBi (l : ℕ) : ℕ := 4 * l + 3

/-- The block receiving the minimum's label. -/
def KM : LReg := ⟨"bc.ml", "bc.mh", "bc.mv", "bc.me", "bc.mr"⟩

/-- `sl.i := slot B'[0]; if hp_n ≠ 0 then (top; KM := d[hp_v]; B'[0] := KM) else B'[0] := KB` -/
def setBp (H : HeapI G s) : Stmt :=
  seq (wset "sl.i" (lit (slotBp 0)))
  (ite (var "hp_n")
     (seq H.top (seq (loadLab "hp_v" KM "bc.mf") (storeSlot KM "bc.mf")))
     (storeSlot KB "bc.bf"))

open Classical in
/-- The loaded label of `v` is held, with its flag, as a (possibly infinite) bound block. -/
theorem wholds_of_loaded {st : State ℝ≥0} {d : Labels G s} {Hh : Fin G.n → ℕ → List (Fin G.m)}
    {X : LReg} {xf : String} {v : Fin G.n}
    (hl : Loaded st (tabOf (G := G) st) X xf v) (hR : Represents (s := s) (tabOf (G := G) st) d Hh) :
    WHolds st X xf Hh (vc st) (d v) := by
  refine ⟨?_, fun q hq => ⟨(tabOf (G := G) st).lab v, ?_, hR.rep v q hq⟩⟩
  · rw [hl.2.2.2.2.2]; exact hR.fin_iff v
  · have hne : d v ≠ ⊤ := by rw [hq]; exact WithTop.coe_ne_top
    exact Loaded.holds hl hR hne

theorem SlotLens.of_unchanged {st r : State ℝ≥0} {i : ℕ} {wa va wr vr : List String}
    (h : SlotLens st i) (hu : Unchanged st r wa va wr vr) (hw : ∀ a ∈ slotW, a ∉ wa)
    (hv : "sl.l" ∉ va) : SlotLens r i :=
  ⟨by rw [(hu.varr _ hv).2]; exact h.l, by rw [(hu.warr _ (hw _ (by simp [slotW]))).2]; exact h.h,
    by rw [(hu.warr _ (hw _ (by simp [slotW]))).2]; exact h.v,
    by rw [(hu.warr _ (hw _ (by simp [slotW]))).2]; exact h.e,
    by rw [(hu.warr _ (hw _ (by simp [slotW]))).2]; exact h.r,
    by rw [(hu.warr _ (hw _ (by simp [slotW]))).2]; exact h.f⟩

open Classical in
/-- **BC.8–BC.9**: `B'` is `B` for an empty heap, else the least label in the heap. -/
theorem setBp_spec (H : HeapI G s) (hok : HeapOK H) (st : State ℝ≥0) (d : Labels G s)
    (Hh : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ) (T : Finset (Fin G.n)) (B : WLab G s)
    (hHR : H.HR st T d) (hL : LabAt st d Hh c0) (hK : WHolds st KB "bc.bf" Hh (vc st) B)
    (hTfin : ∀ y ∈ T, d y ≠ ⊤) (hsl : SlotLens st (slotBp 0))
    (hbud : st.cost + H.Cop + 20 ≤ c0 + st.cap) (hcapN : 2 * G.n + 3 < st.cap)
    (hszT : T.card ≤ H.hsz) (hKM : ∀ a ∈ ["bc.mh", "bc.mv", "bc.me", "bc.mr", "bc.mf", "sl.i"], a ∉ H.wr)
    (hKMv : "bc.ml" ∉ H.vr) :
    Runs realOps (setBp H) st (fun r => ∃ B' : WLab G s, SlotHolds r (slotBp 0) Hh (vc r) B' ∧
      (T = ∅ → B' = B) ∧ (T.Nonempty → ∃ u ∈ T, B' = d u ∧ ∀ y ∈ T, d u ≤ d y) ∧
      H.HR r T d ∧ LabAt r d Hh c0 ∧ vc (G := G) r = vc st ∧
      Unchanged st r (slotW ++ H.wa) ("sl.l" :: H.va) ("sl.i" :: "bc.mf" :: KM.ws ++ H.wr)
        (KM.l :: H.vr) ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost + 20 + (if T.Nonempty then H.Cop else 0) ∧
      (∀ i, i ≠ slotBp 0 → r.va "sl.l" i = st.va "sl.l" i ∧ ∀ a ∈ slotW, r.wa a i = st.wa a i)) := by
  have hc2 : 2 < st.cap := by omega
  refine runs_seq (runs_wset (a := slotBp 0) (evalW_lit_of (by simp [slotBp]; omega)) ?_)
  set st1 := (st.setW "sl.i" (slotBp 0)).charge 1 with hst1
  have hU1 : Unchanged st st1 [] [] ["sl.i"] [] :=
    ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun z hz => by
      simp only [List.mem_singleton] at hz; simp [hst1, State.setW, State.charge, hz],
      fun _ _ => rfl, rfl, rfl⟩
  have hn1 : st1.w "hp_n" = T.card := by
    rw [hU1.wreg "hp_n" (by simp)]; exact H.size hHR
  have hi1 : st1.w "sl.i" = slotBp 0 := by simp [hst1, State.setW, State.charge]
  have hvc1 : vc (G := G) st1 = vc st := rfl
  by_cases hT : T.Nonempty
  · have hTc : T.card ≠ 0 := (Finset.card_pos.mpr hT).ne'
    refine runs_ite_true (x := T.card) (by rw [evalW_var, hn1]) hTc ?_
    set st2 := st1.charge 1 with hst2
    have hU02 : Unchanged st st2 [] [] ["sl.i"] [] := hU1.trans (Unchanged.charge _ 1 _ _ _ _)
    have hL2 : LabAt st2 d Hh c0 := hL.of_unchanged hU02 (by simp) (by simp)
      (by simp only [hst2, hst1, State.charge_cost, State.setW_cost]; omega)
    have hHR2 : H.HR st2 T d := H.HR_frame hHR hU02 (by simp) (fun a ha h => by
      rw [List.mem_singleton] at h; exact (hok.fwr a ha) (by rw [h]; simp))
    refine runs_seq ((H.top_spec st2 T d Hh c0 hHR2 hL2 hT hTfin (by
      simp only [hst2, hst1, State.charge_cost, State.charge_cap, State.setW_cost, State.setW_cap]
      omega) (by simp only [hst2, hst1, State.charge_cap, State.setW_cap]; exact hcapN) hszT).mono ?_)
    rintro r2 ⟨u, huT, hmin, hv2, hHR3, hU3, hc3l, hc3⟩
    have hL3 : LabAt r2 d Hh c0 := hL2.of_unchanged hU3 (fun a ha h => H.wa_lab a ha h) H.va_lab hc3l
    refine runs_seq ((wp_sound _ _ _ (loadLab_wp "hp_v" KM "bc.mf" ⟨by decide, by decide⟩ r2 u
      hL3.lens hv2)).mono ?_)
    rintro r3 ⟨hld, hU4, hc4⟩
    have htab : tabOf (G := G) r3 = tabOf r2 :=
      (tabOf_of_unchanged (G := G) hU4 (by decide) (by decide)).1
    have hL4 : LabAt r3 d Hh c0 := hL3.of_unchanged hU4 (by decide) (by decide) (by omega)
    have hW : WHolds r3 KM "bc.mf" Hh (vc r3) (d u) := by
      rw [← htab] at hld
      exact wholds_of_loaded hld hL4.rep
    have hi3 : r3.w "sl.i" = slotBp 0 := by
      rw [hU4.wreg "sl.i" (by decide), hU3.wreg "sl.i" (fun h => hKM _ (by simp) h)]
      simp [hst2, hi1]
    have hslw : ∀ a ∈ slotW, a ∉ H.wa := fun a ha h => hok.wa a h (by
      simp only [slotW, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp)
    have hsl3 : SlotLens r3 (slotBp 0) :=
      SlotLens.of_unchanged (SlotLens.of_unchanged (SlotLens.of_unchanged hsl hU02 (by simp)
        (by simp)) hU3 hslw (fun h => hok.va.2 h)) hU4 (by simp) (by simp)
    refine (storeSlot_spec KM "bc.mf" r3 hi3 hsl3 hW).mono ?_
    rintro r ⟨hSH, hfr5, hU5, hc5⟩
    have v5 : vc (G := G) r = vc r3 := vc_of_unchanged (G := G) hU5 (by decide)
    have v4 : vc (G := G) r3 = vc r2 := vc_of_unchanged (G := G) hU4 (by decide)
    have v3 : vc (G := G) r2 = vc st2 :=
      vc_of_unchanged (G := G) hU3 (fun h => H.wa_lab "vcnt" (by simp [labW]) h)
    have hvc5 : vc (G := G) r = vc st := by rw [v5, v4, v3]; rfl
    have hc02 : st2.cost = st.cost + 2 := by simp [hst2, hst1, State.charge]
    refine ⟨d u, by rw [v5]; exact hSH,
      fun h => absurd h (Finset.nonempty_iff_ne_empty.mp hT), fun _ => ⟨u, huT, rfl, hmin⟩,
      H.HR_frame (H.HR_frame hHR3 hU4 (by simp) (fun a ha h => (hok.fwr a ha) (by
        simp only [List.mem_cons, KM, LReg.ws, List.not_mem_nil, or_false] at h ⊢
        rcases h with h | h | h | h | h <;> simp [h]))) hU5
        (fun a ha h => (hok.fwa a ha).2 (by
          simp only [slotW, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
          rcases h with rfl | rfl | rfl | rfl | rfl <;> simp)) (by simp),
      hL4.of_unchanged hU5 (by decide) (by decide) (by omega), hvc5, ?_, by omega,
      by rw [if_pos hT]; omega, ?_⟩
    have h02 : Unchanged st r2 H.wa H.va ("sl.i" :: H.wr) H.vr :=
      (hU02.comp hU3).mono (by simp) (by simp) (by simp) (by simp)
    refine ((h02.comp hU4).comp hU5).mono ?_ ?_ ?_ ?_
    · intro a ha; simp only [List.mem_append, List.nil_append, List.append_nil] at ha ⊢; tauto
    · intro a ha; simp only [List.mem_append, List.mem_cons, List.nil_append, List.append_nil,
        List.not_mem_nil, or_false] at ha ⊢; tauto
    · intro a ha
      simp only [List.mem_append, List.mem_cons, List.nil_append, List.append_nil,
        List.not_mem_nil, or_false] at ha ⊢
      tauto
    · intro a ha; simp only [List.mem_append, List.mem_cons, List.nil_append, List.append_nil,
        List.not_mem_nil, or_false] at ha ⊢; tauto
    · intro i hi
      obtain ⟨e1, e2⟩ := hfr5 i hi
      refine ⟨?_, fun a ha => ?_⟩
      · rw [e1, (hU4.varr "sl.l" (by simp)).1, (hU3.varr "sl.l" (fun h => hok.va.2 h)).1,
          (hU02.varr "sl.l" (by simp)).1]
      · rw [e2 a ha, (hU4.warr a (by simp)).1, (hU3.warr a (hslw a ha)).1, (hU02.warr a (by simp)).1]
  · -- empty heap: `B' := B`
    have hT0 : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    refine runs_ite_false (by rw [evalW_var, hn1, hT0, Finset.card_empty]) ?_
    set st2 := st1.charge 1 with hst2
    have hU02 : Unchanged st st2 [] [] ["sl.i"] [] := hU1.trans (Unchanged.charge _ 1 _ _ _ _)
    have hK2 : WHolds st2 KB "bc.bf" Hh (vc st2) B := by
      rw [show vc (G := G) st2 = vc st from rfl]
      exact hK.of_unchanged hU02 (by decide) (by decide) (by decide)
    refine (storeSlot_spec KB "bc.bf" st2 (by simp [hst2, hi1])
      (SlotLens.of_unchanged hsl hU02 (by simp) (by simp)) hK2).mono ?_
    rintro r ⟨hSH, hfr5, hU5, hc5⟩
    have v5 : vc (G := G) r = vc st2 := vc_of_unchanged (G := G) hU5 (by decide)
    have hvc5 : vc (G := G) r = vc st := by rw [v5]; rfl
    refine ⟨B, by rw [v5]; exact hSH,
      fun _ => rfl, fun h => absurd hT0 (Finset.nonempty_iff_ne_empty.mp h),
      H.HR_frame (H.HR_frame hHR hU02 (by simp) (fun a ha h => by
        rw [List.mem_singleton] at h; exact (hok.fwr a ha) (by rw [h]; simp))) hU5
        (fun a ha h => (hok.fwa a ha).2 (by
          simp only [slotW, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
          rcases h with rfl | rfl | rfl | rfl | rfl <;> simp)) (by simp),
      (hL.of_unchanged hU02 (by simp) (by simp)
        (by simp only [hst2, hst1, State.charge_cost, State.setW_cost]; omega)).of_unchanged
        hU5 (by decide) (by decide) (by omega), hvc5, ?_, by simp [hst2, hst1, State.charge] at hc5 ⊢; omega,
      by rw [if_neg hT]; simp [hst2, hst1, State.charge] at hc5 ⊢; omega, ?_⟩
    refine (hU02.comp hU5).mono ?_ ?_ ?_ ?_
    · intro a ha; simp only [List.mem_append, List.nil_append, List.append_nil] at ha ⊢; tauto
    · intro a ha; simp only [List.mem_append, List.mem_cons, List.nil_append, List.append_nil,
        List.not_mem_nil, or_false] at ha ⊢; tauto
    · intro a ha; simp only [List.mem_append, List.mem_cons, List.nil_append, List.append_nil,
        List.not_mem_nil, or_false] at ha ⊢; tauto
    · intro a ha; simp at ha
    · intro i hi
      obtain ⟨e1, e2⟩ := hfr5 i hi
      exact ⟨by rw [e1, (hU02.varr "sl.l" (by simp)).1], fun a ha => by rw [e2 a ha, (hU02.warr a (by simp)).1]⟩

/-! ## The base case (BC.1–BC.9) -/

theorem baseLoopC_of_empty {DC : BM.DCost} {B : WLab G s} {τ : ℕ} {d : Labels G s}
    {U : Finset (Fin G.n)} {st' : Labels G s × DS G s × Finset (Fin G.n)} {c : ℕ}
    (h : BM.BaseLoopC G s DC B τ (d, BM.Dof ∅ d, U) st' c) : st' = (d, BM.Dof ∅ d, U) ∧ c = 1 := by
  cases h with
  | stop _ _ => exact ⟨rfl, rfl⟩
  | step _ _ _ u val _ _ _ hu _ _ _ _ => simp [BM.Dof_apply] at hu

theorem Dof_eq_empty {T : Finset (Fin G.n)} {d d' : Labels G s} (h : BM.Dof T d = BM.Dof ∅ d') :
    T = ∅ := by
  ext y
  simp only [Finset.notMem_empty, iff_false]
  intro hy
  have := congrFun h y
  simp [BM.Dof_apply, hy] at this

/-- The base case body: bound into `KB`, `τ₀` into `bc.tau`, `U := []`, BC.1, BC.3–BC.7, BC.8–9. -/
def baseBody (H : HeapI G s) : Stmt :=
  seq (wset "sl.i" (lit (slotB 0)))
  (seq (loadSlot KB "bc.bf")
  (seq (wset "bc.tau" (load "cp.tau" (lit 0)))
  (seq (RamLevel.rowReset "U.len")
  (seq (pushS H)
  (seq (baseLoop H)
       (setBp H))))))

theorem notMem_cons2 {x a b : String} {l : List String} (h1 : x ≠ a) (h2 : x ≠ b) (h3 : x ∉ l) :
    x ∉ a :: b :: l := by
  simp only [List.mem_cons, not_or]; exact ⟨h1, h2, h3⟩

/-- The write sets of the base case (the concatenation over its steps). -/
def baseWA (H : HeapI G s) : List String :=
  [] ++ [] ++ [] ++ ["U.len"] ++ H.wa ++ (eWA H ++ ["U", "U.len"]) ++ (slotW ++ H.wa)
def baseVA (H : HeapI G s) : List String :=
  [] ++ [] ++ [] ++ [] ++ H.va ++ eVA H ++ ("sl.l" :: H.va)
def baseWR (H : HeapI G s) : List String :=
  ["sl.i"] ++ ("bc.bf" :: KB.ws) ++ ["bc.tau"] ++ [] ++ ("bc.k" :: "hp_x" :: H.wr) ++
    ("ru" :: "bc.pe" :: eWR H) ++ ("sl.i" :: "bc.mf" :: KM.ws ++ H.wr)
def baseVR (H : HeapI G s) : List String :=
  [] ++ [KB.l] ++ [] ++ [] ++ H.vr ++ eVR H ++ (KM.l :: H.vr)

/-- The log record of a base call (as in `BMCost.BaseC`). -/
def baseRec {Ω : Type} (DC : BM.DCost) (Blow B : WLab G s) (S : Finset (Fin G.n)) (B' : WLab G s)
    (U : Finset (Fin G.n)) (c : ℕ) : BM.CallRec G s Ω :=
  { lvl := 0, Blow := Blow, B := B, S := S, B' := B', U := U, base := true, p := 0, Q := ∅,
    W := ∅, W' := ∅, J := ∅, Wr := ∅, fp := none, cFP := 0, cMerge := 0,
    cost := S.card * (1 + DC.bins) + c + 1 }

/-- The budget of one base call. -/
def baseBud (H : HeapI G s) (G : Graph) (S : ℕ) (τ : ℕ) : ℕ :=
  (S + 1) * (H.Cop + 3) + (τ + 1) * exSlack H G + H.Cop + 60

set_option maxHeartbeats 1000000 in
open Classical in
/-- **The RAM base case refines `BMCost.BaseC`** (BC.1–BC.9, keys = current labels, IHeap-style
heap).  The returned store is the heap's set with keys = labels; `B'` is in slot `slotBp 0`;
cost `≤ lg.cost + 32` for the call's log `lg`. -/
theorem baseBody_spec (H : HeapI G s) (hok : HeapOK H) (DC : BM.DCost)
    (hbext : H.Cop + 7 ≤ DC.bext) (hbins : 2 * H.Cop + 76 ≤ DC.bins) {Φ Ω : Type} (φ0 : Φ)
    (st : State ℝ≥0) (Blow B : WLab G s) (S : Finset (Fin G.n)) (d0 : Labels G s)
    (hpre : CallPre B S d0) (τ δ : ℕ) (Hh : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ)
    (hL : LabAt st d0 Hh c0) (hg : GraphAt st G) (hcsr : CSRAt st G) (hHR : H.HR st ∅ d0)
    (hS : SRow st S) (hB : SlotHolds st (slotB 0) Hh (vc st) B)
    (hslB : SlotLens st (slotB 0)) (hslBp : SlotLens st (slotBp 0))
    (hlvl : st.w "lvl" = 0) (hn : st.w "n" = G.n) (htl : 0 < st.wlen "cp.tau")
    (htau : st.wa "cp.tau" 0 = τ) (hUl : G.n ≤ st.wlen "U") (hUll : 0 < st.wlen "U.len")
    (hdeg : ∀ u : Fin G.n, st.wa "gSt" ((u : ℕ) + 1) - st.wa "gSt" u ≤ δ)
    (hsz : S.card + δ * τ ≤ H.hsz) (hbud : st.cost + baseBud H G S.card τ ≤ c0 + st.cap)
    (hm : G.m + 2 ≤ st.cap) (hcapN : 2 * G.n + 3 < st.cap) (hτcap : τ + 2 ≤ st.cap) :
    Runs realOps (baseBody H) st (fun r => ∃ (res : BM.Result G s) (lg : BM.Log G s Ω)
      (T' : Finset (Fin G.n)) (Hh' : Fin G.n → ℕ → List (Fin G.m)),
      BM.BaseC G s DC Blow B S d0 φ0 τ res φ0 lg ∧ res.2.2.1 = BM.Dof T' res.2.2.2 ∧
      LabAt r res.2.2.2 Hh' c0 ∧ HExt Hh (vc st) Hh' (vc r) ∧ H.HR r T' res.2.2.2 ∧
      URow r res.2.1 ∧ SlotHolds r (slotBp 0) Hh' (vc r) res.1 ∧ GraphAt r G ∧ CSRAt r G ∧
      Unchanged st r (baseWA H) (baseVA H) (baseWR H) (baseVR H) ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost + BM.Log.cost lg + 32 ∧
      (∀ i, G.n ≤ i → r.wa "U" i = st.wa "U" i) ∧ (∀ j, j ≠ 0 → r.wa "U.len" j = st.wa "U.len" j) ∧
      (∀ i, i ≠ slotBp 0 → r.va "sl.l" i = st.va "sl.l" i ∧ ∀ a ∈ slotW, r.wa a i = st.wa a i)) := by
  have hc1 : 1 < st.cap := by omega
  have hSfin : ∀ y ∈ S, d0 y ≠ ⊤ := fun y hy => ne_top_of_lt (hpre.inRange y hy)
  -- 1. `sl.i := slotB 0`
  refine runs_seq (runs_wset (a := slotB 0) (evalW_lit_of (by simp [slotB]; omega)) ?_)
  set st1 := (st.setW "sl.i" (slotB 0)).charge 1 with hst1
  have hU1 : Unchanged st st1 [] [] ["sl.i"] [] :=
    ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun z hz => by
      simp only [List.mem_singleton] at hz; simp [hst1, State.setW, State.charge, hz],
      fun _ _ => rfl, rfl, rfl⟩
  -- 2. `KB := slot B[0]`
  refine runs_seq ((loadSlot_spec KB "bc.bf" ⟨by decide⟩ st1
    (by simp [hst1, State.setW, State.charge]) (SlotLens.of_unchanged hslB hU1 (by simp) (by simp))
    (hB.of_unchanged hU1 (by simp) (by simp))).mono ?_)
  rintro r2 ⟨hK2, hU2, hc2⟩
  have hU02 : Unchanged st r2 [] [] (["sl.i"] ++ ("bc.bf" :: KB.ws)) ([] ++ [KB.l]) := hU1.comp hU2
  have hvc2 : vc (G := G) r2 = vc st := vc_of_unchanged hU02 (by simp)
  rw [← hvc2] at hK2
  -- 3. `bc.tau := tau[0]`
  have htl2 : 0 < r2.wlen "cp.tau" := by rw [(hU02.warr "cp.tau" (by simp)).2]; exact htl
  have htau2 : r2.wa "cp.tau" 0 = τ := by rw [(hU02.warr "cp.tau" (by simp)).1]; exact htau
  refine runs_seq (runs_wset (evalW_load_of (evalW_lit_of (by rw [hU02.cap]; omega)) htl2) ?_)
  set r3 := (r2.setW "bc.tau" (r2.wa "cp.tau" 0)).charge 1 with hr3
  have hU23 : Unchanged r2 r3 [] [] ["bc.tau"] [] :=
    ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun z hz => by
      simp only [List.mem_singleton] at hz; simp [hr3, State.setW, State.charge, hz],
      fun _ _ => rfl, rfl, rfl⟩
  have hU03 := hU02.comp hU23
  -- 4. `U.len[0] := 0`
  refine runs_seq ((RamLevel.rowReset_spec (arr := "U") (n := G.n) (l := 0) r3
    (by rw [hU03.wreg "lvl" (by simp [KB, LReg.ws])]; exact hlvl)
    (by rw [(hU03.warr "U.len" (by simp)).2]; exact hUll)
    (by rw [(hU03.warr "U" (by simp)).2]; simpa using hUl) (by rw [hU03.cap]; omega)).mono ?_)
  rintro r4 ⟨hRU4, hU4, hUl4, -, hc4⟩
  have hU04 := hU03.comp hU4
  have hURow4 : URow r4 ∅ := ⟨[], hRU4, List.nodup_nil, by simp⟩
  have hcap4 : r4.cap = st.cap := hU04.cap
  have hc04 : r4.cost = st.cost + 9 := by
    simp only [hc4, hr3, State.charge_cost, State.setW_cost, hc2, hst1]
  have hL4 : LabAt r4 d0 Hh c0 := hL.of_unchanged hU04 (by decide) (by simp) (by omega)
  have hvc4 : vc (G := G) r4 = vc st := vc_of_unchanged hU04 (by simp)
  have hHR4 : H.HR r4 ∅ d0 := H.HR_frame hHR hU04 (fun a ha h => (hok.fwa a ha).2 (by
      simp only [List.mem_append, List.nil_append, List.mem_singleton] at h ⊢; simp [h]))
    (fun a ha h => (hok.fwr a ha) (by
      simp only [List.mem_append, List.nil_append, List.mem_cons, List.mem_singleton, KB,
        LReg.ws, List.not_mem_nil, or_false, List.append_nil] at h ⊢
      rcases h with ((h | h | h | h | h | h) | h) <;> simp [h]))
  have hS4 : SRow r4 S := by
    obtain ⟨xs, hR, hnd, hmem⟩ := hS
    have e1 := hU04.warr "S" (by simp)
    have e2 := hU04.warr "S.len" (by simp)
    exact ⟨xs, RamLevel.RowRep.of_eq hR e1.2 e2.2 (by rw [e2.1]) (fun i _ => by rw [e1.1]), hnd, hmem⟩
  have hK4 : WHolds r4 KB "bc.bf" Hh (vc r4) B := by
    rw [hvc4, ← hvc2]
    exact hK2.of_unchanged (hU23.comp hU4) (by decide) (by decide) (by decide)
  have htau4 : r4.w "bc.tau" = τ := by
    rw [hU4.wreg "bc.tau" (by simp), ← htau2]; simp [hr3, State.setW, State.charge]
  -- 5. BC.1
  refine runs_seq ((pushS_spec H hok r4 S d0 Hh c0 hS4 hHR4 hL4 hSfin (by omega)
    (by rw [hc04, hcap4]; unfold baseBud at hbud; omega) (by rw [hcap4]; exact hcapN)).mono ?_)
  rintro r5 ⟨hHR5, hL5, hU5, hc5l, hc5⟩
  have hcap5 : r5.cap = st.cap := hU5.cap.trans hcap4
  have hvc5 : vc (G := G) r5 = vc r4 := vc_of_unchanged hU5 (fun h => H.wa_lab "vcnt" (by simp [labW]) h)
  have hK5 : WHolds r5 KB "bc.bf" Hh (vc r5) B := by
    rw [hvc5]; exact hK4.of_unchanged hU5 (fun a ha h => by
      simp only [List.mem_cons] at h
      simp only [KB, LReg.ws, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases h with h | h | h
      · subst h; rcases ha with h' | h' | h' | h' <;> exact absurd h' (by decide)
      · subst h; rcases ha with h' | h' | h' | h' <;> exact absurd h' (by decide)
      · exact hok.wr a h (by rcases ha with rfl | rfl | rfl | rfl <;> simp))
      hok.vr.1 (notMem_cons2 (by decide) (by decide) (fun h => hok.wr _ h (by simp)))
  have hnotw5 : ∀ a ∈ ["gSt", "gHead", "U", "U.len", "S", "S.len"], a ∉ H.wa := by
    intro a ha h; exact hok.wa a h (by simp only [List.mem_cons, List.not_mem_nil, or_false] at ha ⊢; tauto)
  have hg5 : GraphAt r5 G := graphAt_of_unchanged (hU04.comp hU5) (fun h => by
      simp only [List.mem_append, List.nil_append, List.mem_singleton] at h
      exact h.elim (fun h => absurd h (by decide)) (fun h => hnotw5 "gHead" (by simp) h)) (by simp; exact hok.va.1) hg
  have hcsr5 : CSRAt r5 G := hcsr.of_unchanged (hU04.comp hU5) (fun h => by
      simp only [List.mem_append, List.nil_append, List.mem_singleton] at h
      exact h.elim (fun h => absurd h (by decide)) (fun h => hnotw5 "gSt" (by simp) h))
  have hURow5 : URow r5 ∅ := hURow4.of_unchanged hU5 (hnotw5 "U" (by simp)) (hnotw5 "U.len" (by simp))
  have hlvl5 : r5.w "lvl" = 0 := by
    rw [hU5.wreg "lvl" (notMem_cons2 (by decide) (by decide) (fun h => hok.wr _ h (by simp))),
      hU04.wreg "lvl" (by simp [KB, LReg.ws])]; exact hlvl
  have hn5 : r5.w "n" = G.n := by
    rw [hU5.wreg "n" (notMem_cons2 (by decide) (by decide) (fun h => hok.wr _ h (by simp))),
      hU04.wreg "n" (by simp [KB, LReg.ws])]; exact hn
  have htau5 : r5.w "bc.tau" = τ := by
    rw [hU5.wreg "bc.tau" (notMem_cons2 (by decide) (by decide) (fun h => hok.wr _ h (by simp))), htau4]
  have hgSt5 : r5.wa "gSt" = st.wa "gSt" := by
    rw [((hU04.comp hU5).warr "gSt" (fun h => by
      simp only [List.mem_append, List.nil_append, List.mem_singleton] at h
      exact h.elim (fun h => absurd h (by decide)) (fun h => hnotw5 "gSt" (by simp) h))).1]
  -- 6. BC.3–BC.7
  have hBI0 : BM.BInv G s B S d0 d0 (BM.Dof S d0) ∅ := by
    have := BM.bInv_init (G := G) (s := s) hpre
    rwa [BM.insertMany_empty_Dof] at this
  refine runs_seq ((baseLoop_spec H hok DC hbext (by omega) r5 B S d0 hpre τ δ d0 Hh c0 S ∅ hBI0
    (Nat.zero_le _) hL5 hg5 hcsr5 hHR5 hK5 hURow5 hlvl5 hn5 htau5
    (by intro u; rw [hgSt5]; exact hdeg u) (by simpa using hsz)
    (by
      rw [hcap5]; unfold baseBud at hbud; simp only [Finset.card_empty, Nat.sub_zero]
      have e : (S.card + 1) * (H.Cop + 3) = S.card * (H.Cop + 3) + (H.Cop + 3) := by ring
      omega)
    (by rw [hcap5]; exact hm) (by rw [hcap5]; exact hcapN) (by rw [hcap5]; exact hτcap)).mono ?_)
  rintro r6 ⟨d', T', U', Hh', c, hloop, hBI', hstop, hTc', hL6, hext6, hHR6, hg6, hcsr6, hK6, hURow6,
    -, -, -, hU6, hc6l, hc6, hc6s, hFU6, hFL6⟩
  have hcap6 : r6.cap = st.cap := hU6.cap.trans hcap5
  -- 7. BC.8–BC.9
  have hslBp6 : SlotLens r6 (slotBp 0) := by
    refine SlotLens.of_unchanged (SlotLens.of_unchanged (SlotLens.of_unchanged hslBp hU04 (by
      intro a ha h; simp only [slotW, List.mem_cons, List.not_mem_nil, or_false, List.mem_append,
        List.nil_append] at ha h; rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp at h) (by simp))
      hU5 (fun a ha h => hok.wa a h (by
        simp only [slotW, List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
        rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp)) (fun h => hok.va.2 h)) hU6 ?_ ?_
    · intro a ha h
      simp only [eWA, labW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
      simp only [slotW, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases h with ((h | h) | h) <;>
        (try (rcases ha with rfl | rfl | rfl | rfl | rfl <;> rcases h with h | h | h | h | h <;>
          exact absurd h (by decide))) <;>
        (try (exact hok.wa a h (by rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp))) <;>
        (try (rcases ha with rfl | rfl | rfl | rfl | rfl <;> rcases h with h | h <;>
          exact absurd h (by decide)))
    · intro h
      simp only [eVA, labV, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
      exact h.elim (fun h => absurd h (by decide)) (fun h => hok.va.2 h)
  refine (setBp_spec H hok r6 d' Hh' c0 T' B hHR6 hL6 hK6 (BInv.fin_of_Dof hBI') hslBp6
    (by
      rw [hcap6]; unfold baseBud at hbud
      simp only [Finset.card_empty, Nat.sub_zero] at hc6s
      have e : (S.card + 1) * (H.Cop + 3) = S.card * (H.Cop + 3) + (H.Cop + 3) := by ring
      omega) (by rw [hcap6]; exact hcapN) hTc'
    (fun a ha h => hok.wr a h (by simp only [List.mem_cons, List.not_mem_nil, or_false] at ha ⊢; tauto))
    hok.vr.2).mono ?_
  rintro r ⟨B', hSH, hBe, hBn, hHR7, hL7, hvc7, hU7, hc7l, hc7, hFS7⟩
  have hnot7 : ∀ a ∈ ["U", "U.len", "gSt", "gHead"], a ∉ slotW ++ H.wa := by
    intro a ha h
    rcases List.mem_append.mp h with h | h
    · simp only [slotW, List.mem_cons, List.not_mem_nil, or_false] at ha h
      rcases ha with rfl | rfl | rfl | rfl <;> rcases h with h | h | h | h | h <;>
        exact absurd h (by decide)
    · exact hok.wa a h (by simp only [List.mem_cons, List.not_mem_nil, or_false] at ha ⊢; tauto)
  have hSne : T'.Nonempty → S.Nonempty := by
    intro hT'
    by_contra hS0
    rw [Finset.not_nonempty_iff_eq_empty] at hS0
    subst hS0
    obtain ⟨he, -⟩ := baseLoopC_of_empty hloop
    have h2 : BM.Dof T' d' = BM.Dof ∅ d0 := congrArg (fun x => x.2.1) he
    exact (Finset.nonempty_iff_ne_empty.mp hT') (Dof_eq_empty h2)
  refine ⟨(B', U', BM.Dof T' d', d'), [([], baseRec DC Blow B S B' U' c)], T', Hh', ?_, rfl, hL7,
    ?_, hHR7, hURow6.of_unchanged hU7 (hnot7 "U" (by simp)) (hnot7 "U.len" (by simp)), hSH,
    graphAt_of_unchanged hU7 (hnot7 "gHead" (by simp)) (by
      simp only [List.mem_cons, not_or]; exact ⟨by decide, hok.va.1⟩) hg6,
    hcsr6.of_unchanged hU7 (hnot7 "gSt" (by simp)), ((hU04.comp hU5).comp hU6).comp hU7, ?_, ?_,
    ?_, ?_, ?_⟩
  · refine ⟨(d', BM.Dof T' d', U'), c, by rw [BM.insertMany_empty_Dof]; exact hloop, rfl, rfl, rfl,
      fun hE => hBe ((BM.Dof_isEmpty_iff T' d').mp hE), fun hNE => ?_, rfl, rfl⟩
    have hT' : T'.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro h; exact hNE ((BM.Dof_isEmpty_iff T' d').mpr h)
    obtain ⟨u, huT, hBu, hmin⟩ := hBn hT'
    refine ⟨u, by simp [BM.Dof_apply, huT, hBu], fun z v hz => ?_⟩
    change BM.Dof T' d' z = some v at hz
    rw [BM.Dof_apply] at hz
    split_ifs at hz with hzT
    simp only [Option.some.injEq] at hz
    rw [hBu, ← hz]; exact hmin z hzT
  · have e5 : vc (G := G) r5 = vc st := hvc5.trans hvc4
    rw [e5] at hext6; rw [hvc7]; exact hext6
  · omega
  · show r.cost ≤ st.cost + ((baseRec (Ω := Ω) DC Blow B S B' U' c).cost + 0) + 32
    simp only [baseRec]
    by_cases hT' : T'.Nonempty
    · rw [if_pos hT'] at hc7
      have hS1 : 1 ≤ S.card := Finset.card_pos.mpr (hSne hT')
      have : S.card * (H.Cop + 3) + H.Cop ≤ S.card * (1 + DC.bins) := by
        have h1 : S.card * (H.Cop + 3) + S.card * (H.Cop) ≤ S.card * (1 + DC.bins) := by
          rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
        have h2 : H.Cop ≤ S.card * H.Cop := Nat.le_mul_of_pos_left _ hS1
        omega
      omega
    · rw [if_neg hT'] at hc7
      have : S.card * (H.Cop + 3) ≤ S.card * (1 + DC.bins) := Nat.mul_le_mul_left _ (by omega)
      omega
  · intro i hi
    rw [(hU7.warr "U" (hnot7 "U" (by simp))).1, hFU6 i hi, (hU5.warr "U" (hnotw5 "U" (by simp))).1,
      (hU04.warr "U" (by simp [KB, LReg.ws])).1]
  · intro j hj
    rw [(hU7.warr "U.len" (hnot7 "U.len" (by simp))).1, hFL6 j hj,
      (hU5.warr "U.len" (hnotw5 "U.len" (by simp))).1, hUl4 j hj, (hU03.warr "U.len" (by simp [KB, LReg.ws])).1]
  · intro i hi
    obtain ⟨e1, e2⟩ := hFS7 i hi
    have hvl : "sl.l" ∉ eVA H := by
      simp only [eVA, labV, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨by decide, hok.va.2⟩
    refine ⟨?_, fun a ha => ?_⟩
    · rw [e1, (hU6.varr "sl.l" hvl).1, (hU5.varr "sl.l" (fun h => hok.va.2 h)).1,
        (hU04.varr "sl.l" (by simp)).1]
    · simp only [slotW, List.mem_cons, List.not_mem_nil, or_false] at ha
      have hHa : a ∉ H.wa := fun h => hok.wa a h (by rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp)
      have hA6 : a ∉ eWA H ++ ["U", "U.len"] := by
        simp only [eWA, labW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
        refine ⟨⟨?_, hHa⟩, ?_⟩ <;> rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide
      have hA4 : a ∉ ([] ++ [] ++ [] ++ ["U.len"] : List String) := by
        rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [e2 a (by simp only [slotW, List.mem_cons, List.not_mem_nil, or_false]; exact ha),
        (hU6.warr a hA6).1, (hU5.warr a hHa).1, (hU04.warr a hA4).1]

end Frontier.CHD.RamBaseCase
