import Frontier.CHD.SpineLoop
import Frontier.CHD.DLazyFacts
import Frontier.CHD.BaseConv
import Frontier.CHD.BaseDHGlue

/-!
# Frontier.CHD.BaseConvDL — the level-0 leftover conversion against the spine's `DLayer` (owner agent-03)

**NON-GATE** (B-L4, Layer B).  At the end of a base call (level 0) the leftover heap keys (IHeap slots `hp_A[0, hp_n)`)
are inserted, with their final labels `d`, into a fresh level-0 structure: `DL.new` (`newC M Bd`, `M = cp.M[0]`, bound
in slot `B[0]`), then `DL.ins` per slot.  `convDL_spec`: the D layer ends in
`DR r H g' (update Ds 0 D') 0` with `(g', D', c) = insManyC (dlOps G s) (T 0) d lK g (newC M Bd)` for the slot list `lK`
(duplicate-free, enumerating the heap set) — agent-01's `BaseDH` conversion (`BaseDHGlue.baseDH_of_baseC`).

The loop uses spine registers (`sp.qe`, `sp.i`, `px` ∈ `spRegs`), which the D layer never writes.  The D layer's frame
is B-L3's orientation (others' writes disjoint from the D names): `DFrame DL`, which the fixed `DLayer.frame`
(SpineLoop 6666f2ae) provides (`dframe_of`).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamSpine

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.RamLevel Frontier.CHD.BM
  Frontier.CHD.RamBaseCase Frontier.CHD.LabTab WExpr Stmt

variable {G : Graph} {s : Fin G.n} {T : ℕ → ℕ}

/-- The registers written by the conversion loop itself. -/
def convRegs : List String := ["sp.qe", "sp.i", "px"]

/-- (Base return) New level-0 structure, then insert the heap's slots in order. -/
def convDL (new ins : Stmt) : Stmt :=
  seq (wset "sp.qe" (var "hp_n"))
  (seq new
  (seq (wset "sp.i" (lit 0))
  (.while (lt (var "sp.i") (var "sp.qe"))
    (seq (wset "px" (load "hp_A" (var "sp.i")))
    (seq ins (wset "sp.i" (add (var "sp.i") (lit 1))))))))

/-- The D layer's frame in B-L3's orientation (writes of others, disjoint from the D names). -/
def DFrame (DL : DLayer G s T) : Prop :=
  ∀ (st r : State ℝ≥0) (H H' : Hist G) (g : DGl G s) (Ds : ℕ → DStrM G s) (lo : ℕ) (wa va wr vr : List String),
    DL.DR st H g Ds lo → Unchanged st r wa va wr vr → (∀ a ∈ wa, a ∉ DL.dWA) → (∀ a ∈ va, a ∉ DL.dVA) →
    (∀ a ∈ wr, a ∉ DL.dWR) → HExt H (vc st) H' (vc r) → DL.DR r H' g Ds lo

/-- The (fixed) `DLayer.frame` is `DFrame`. -/
theorem dframe_of (DL : DLayer G s T) : DFrame DL :=
  fun st r H H' g Ds lo wa va wr vr h hu h1 h2 h3 hx =>
    DL.frame st r H H' g Ds lo wa va wr vr h hu (fun a ha h' => h1 a h' ha) (fun a ha h' => h2 a h' ha)
      (fun a ha h' => h3 a h' ha) hx

theorem convRegs_not_dWR (DL : DLayer G s T) : ∀ a ∈ convRegs, a ∉ DL.dWR := by
  intro a ha h
  exact DL.dWR_ok a h (by simp [convRegs] at ha; rcases ha with rfl | rfl | rfl <;> simp [spRegs])

theorem lvln_not_dWR (DL : DLayer G s T) : "lvl" ∉ DL.dWR ∧ "n" ∉ DL.dWR :=
  ⟨fun h => DL.dWR_ok _ h (by simp [spRegs]), fun h => DL.dWR_ok _ h (by simp [spRegs])⟩

theorem labW_not_dWA (DL : DLayer G s T) : ∀ a ∈ labW, a ∉ DL.dWA :=
  fun a ha h => DL.dWA_ok a h (by simp only [spArrs, List.mem_append]; exact Or.inr ha)

theorem dlen_not_dVA (DL : DLayer G s T) : "dlen" ∉ DL.dVA :=
  fun h => DL.dVA_ok _ h (by simp [labV])

/-- A register write outside the D layer keeps `DR` (with the corrected frame). -/
theorem DR_setW {DL : DLayer G s T} (hframe : DFrame DL) {st : State ℝ≥0} {H : Hist G} {g : DGl G s}
    {Ds : ℕ → DStrM G s} {lo : ℕ} (h : DL.DR st H g Ds lo) {x : String} (hx : x ∉ DL.dWR) (a k : ℕ) :
    DL.DR ((st.setW x a).charge k) H g Ds lo := by
  refine hframe st _ H H g Ds lo [] [] [x] [] h ?_ (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil) (fun a ha => by rw [List.mem_singleton] at ha; subst ha; exact hx) ?_
  · rw [Frontier.RAM.unch_charge, Frontier.RAM.unch_setW (by simp)]; exact Unchanged.refl _ _ _ _ _
  · have : vc (G := G) ((st.setW x a).charge k) = vc st := rfl
    rw [this]; exact HExt.refl _ _

/-- Writes of the conversion's own registers keep `DR`. -/
theorem DR_unch {DL : DLayer G s T} (hframe : DFrame DL) {st r : State ℝ≥0} {H : Hist G} {g : DGl G s}
    {Ds : ℕ → DStrM G s} {lo : ℕ} (h : DL.DR st H g Ds lo) (hu : Unchanged st r [] [] convRegs [])
    (hvc : vc (G := G) r = vc st) : DL.DR r H g Ds lo :=
  hframe st r H H g Ds lo [] [] convRegs [] h hu (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil) (convRegs_not_dWR DL) (by rw [hvc]; exact HExt.refl _ _)

/-- **The level-0 leftover conversion** refines `insManyC … lK g (newC M Bd)` on the D layer. -/
theorem convDL_spec (DL : DLayer G s T) (hframe : DFrame DL) (st : State ℝ≥0) (H : Hist G) (g : DGl G s)
    (Ds : ℕ → DStrM G s) (d : Labels G s) (c0 M : ℕ) (Bd : WLab G s) {Hs : Finset (Fin G.n)}
    {key : Fin G.n → WLab G s}
    (hD : DL.DR st H g Ds 1) (hL : LabAt st d H c0) (hlvl : st.w "lvl" = 0) (hn : st.w "n" = G.n)
    (hM : st.wa "cp.M" 0 = M) (hMl : 0 < st.wlen "cp.M") (hM2 : 2 * M + 2 < st.cap)
    (hB : SlotHolds st (slotB 0) H (vc st) Bd)
    (hBl : SlotLens st (slotB 0)) (hH : IHeapLab.HRL st Hs key) (hA : "hp_A" ∉ DL.dWA)
    (hlt : ∀ v ∈ Hs, d v < Bd)
    (huse : ∀ lK : List (Fin G.n), lK.Nodup → lK.toFinset = Hs →
      DL.use st + 1 + (BM.insManyC (dlOps G s) (T 0) d lK g (newC M Bd)).2.2 + lK.length ≤ DL.ucap) :
    Runs realOps (convDL DL.new DL.ins) st (fun r => ∃ lK : List (Fin G.n), lK.Nodup ∧ lK.toFinset = Hs ∧
      DL.DR r H (BM.insManyC (dlOps G s) (T 0) d lK g (newC M Bd)).1
        (Function.update Ds 0 (BM.insManyC (dlOps G s) (T 0) d lK g (newC M Bd)).2.1) 0 ∧
      LabAt r d H c0 ∧ r.w "lvl" = 0 ∧
      Unchanged st r DL.dWA DL.dVA (convRegs ++ DL.dWR) DL.dVR ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen ∧
      st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + DL.K + 3 + DL.K * (BM.insManyC (dlOps G s) (T 0) d lK g (newC M Bd)).2.2 +
        lK.length * (DL.K + 3) ∧
      DL.use r ≤ DL.use st + 1 + (BM.insManyC (dlOps G s) (T 0) d lK g (newC M Bd)).2.2 + lK.length) := by
  classical
  obtain ⟨lK, hnd, hset, hlen, hslot⟩ := IHeapLab.HRL.slots hH
  obtain ⟨hhn, hlA, -, hcapH, -, -, -⟩ := hH
  have hHn : Hs.card ≤ G.n := IHeapLab.card_le_n Hs
  have hcap : 2 * G.n + 3 < st.cap := hcapH
  have ⟨hlvlD, hnD⟩ := lvln_not_dWR DL
  have hcR := convRegs_not_dWR DL
  set IM := fun k : ℕ => BM.insManyC (dlOps G s) (T 0) d (lK.take k) g (newC M Bd) with hIM
  suffices Hmain : Runs realOps (convDL DL.new DL.ins) st (fun r =>
      DL.DR r H (BM.insManyC (dlOps G s) (T 0) d lK g (newC M Bd)).1
        (Function.update Ds 0 (BM.insManyC (dlOps G s) (T 0) d lK g (newC M Bd)).2.1) 0 ∧
      LabAt r d H c0 ∧ r.w "lvl" = 0 ∧
      Unchanged st r DL.dWA DL.dVA (convRegs ++ DL.dWR) DL.dVR ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen ∧
      st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + DL.K + 3 + DL.K * (BM.insManyC (dlOps G s) (T 0) d lK g (newC M Bd)).2.2 +
        lK.length * (DL.K + 3) ∧
      DL.use r ≤ DL.use st + 1 + (BM.insManyC (dlOps G s) (T 0) d lK g (newC M Bd)).2.2 + lK.length) by
    exact Hmain.mono (fun r h => ⟨lK, hnd, hset, h⟩)
  have huse0 := huse lK hnd hset
  have hcRd : ∀ a ∈ DL.dWR, a ∉ convRegs := fun a ha h => convRegs_not_dWR DL a h ha
  -- `sp.qe := hp_n`
  refine runs_seq (runs_wset (a := lK.length) (by simp [hhn, hlen]) ?_)
  set s1 := (st.setW "sp.qe" lK.length).charge 1 with hs1
  have hU1 : Unchanged st s1 [] [] convRegs [] := by
    rw [hs1, Frontier.RAM.unch_charge, Frontier.RAM.unch_setW (by simp [convRegs])]; exact Unchanged.refl _ _ _ _ _
  have hD1 : DL.DR s1 H g Ds 1 := DR_setW hframe hD (hcR _ (by simp [convRegs])) _ _
  have hL1 : LabAt s1 d H c0 := hL.of_unchanged hU1 (fun _ _ h => absurd h List.not_mem_nil) (by simp)
    (by simp [hs1])
  have hvc1 : vc (G := G) s1 = vc st := rfl
  have hB1 : SlotHolds s1 (slotB 0) H (vc s1) Bd := by
    rw [hvc1]; exact hB.of_unchanged hU1 (fun _ _ h => absurd h List.not_mem_nil) (by simp)
  -- `DL.new`
  have hus1 : DL.use s1 = DL.use st := DL.use_frame st s1 _ _ _ _ hU1 hcRd
  refine runs_seq ((DL.new_spec s1 H g Ds 0 M Bd hD1 (by simp [hs1, hlvl]) (by simp [hs1, hn])
    (by simp [hs1, hM]) (by simp [hs1]; exact hMl) (by simp [hs1]; exact hM2) hB1
    (RamBaseCase.SlotLens.of_unchanged hBl hU1 (by simp) (by simp))
    (by rw [hus1]; omega)).mono ?_)
  rintro r0 ⟨hDR0, hU0, hwl0, hvl0, hc0a, hc0b, hus0⟩
  have hcap0 : r0.cap = st.cap := by rw [hU0.cap]; simp [hs1]
  have hlvl0 : r0.w "lvl" = 0 := by rw [hU0.wreg _ hlvlD]; simp [hs1, hlvl]
  have hn0 : r0.w "n" = G.n := by rw [hU0.wreg _ hnD]; simp [hs1, hn]
  have hqe0 : r0.w "sp.qe" = lK.length := by rw [hU0.wreg _ (hcR _ (by simp [convRegs]))]; simp [hs1]
  have hA0 : r0.wa "hp_A" = st.wa "hp_A" := by rw [(hU0.warr _ hA).1]; simp [hs1]
  have hAl0 : r0.wlen "hp_A" = st.wlen "hp_A" := by rw [(hU0.warr _ hA).2]; simp [hs1]
  have hL0 : LabAt r0 d H c0 := hL1.of_unchanged hU0 (labW_not_dWA DL) (dlen_not_dVA DL) hc0a
  -- `sp.i := 0`
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by rw [hcap0]; omega)) ?_)
  set r1 := (r0.setW "sp.i" 0).charge 1 with hr1
  have hIM0 : IM 0 = (g, newC M Bd, 0) := by simp [hIM, BM.insManyC]
  have hDR1 : DL.DR r1 H (IM 0).1 (Function.update Ds 0 (IM 0).2.1) 0 := by
    rw [hIM0]; exact DR_setW hframe hDR0 (hcR _ (by simp [convRegs])) _ _
  have htake : ∀ j (hj : j < lK.length), lK.take (j + 1) = lK.take j ++ [lK[j]] := by
    intro j hj
    rw [List.take_succ, List.getElem?_eq_getElem hj]
    simp
  have hUall1 : Unchanged st r1 DL.dWA DL.dVA (convRegs ++ DL.dWR) DL.dVR := by
    rw [hr1, Frontier.RAM.unch_charge, Frontier.RAM.unch_setW (by simp [convRegs])]
    exact (hU1.mono (by simp) (by simp) (by simp) (by simp)).trans
      (hU0.mono (by simp) (by simp) (by simp) (by simp))
  refine runs_while_nat (fun m r => ∃ j, m = lK.length - j ∧ j ≤ lK.length ∧ r.w "sp.i" = j ∧
      r.w "sp.qe" = lK.length ∧ r.w "lvl" = 0 ∧ r.w "n" = G.n ∧ r.wa "hp_A" = st.wa "hp_A" ∧
      r.wlen "hp_A" = st.wlen "hp_A" ∧ LabAt r d H c0 ∧
      DL.DR r H (IM j).1 (Function.update Ds 0 (IM j).2.1) 0 ∧
      Unchanged st r DL.dWA DL.dVA (convRegs ++ DL.dWR) DL.dVR ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost + DL.K + 2 + DL.K * (IM j).2.2 + j * (DL.K + 3) ∧
      DL.use r ≤ DL.use st + 1 + (IM j).2.2 + j) _ ?_ lK.length r1 ?_
  swap
  · refine ⟨0, by simp, by omega, by simp [hr1], by simp [hr1, hqe0], by simp [hr1, hlvl0], by simp [hr1, hn0],
      by simp [hr1, hA0], by simp [hr1, hAl0], ?_, hDR1, hUall1, by simp [hr1, hwl0, hs1], by simp [hr1, hvl0, hs1],
      by simp [hr1, hs1] at hc0a ⊢; omega, ?_, ?_⟩
    · exact hL0.of_unchanged (show Unchanged r0 r1 [] [] convRegs [] by
        rw [hr1, Frontier.RAM.unch_charge, Frontier.RAM.unch_setW (by simp [convRegs])]; exact Unchanged.refl _ _ _ _ _)
        (fun _ _ h => absurd h List.not_mem_nil) (by simp) (by simp [hr1])
    · rw [hIM0]; simp [hr1, hs1] at hc0b ⊢; omega
    · have hu1 : DL.use r1 = DL.use r0 := DL.use_frame r0 r1 _ _ _ _ (show Unchanged r0 r1 [] [] convRegs [] by
        rw [hr1, Frontier.RAM.unch_charge, Frontier.RAM.unch_setW (by simp [convRegs])]; exact Unchanged.refl _ _ _ _ _) hcRd
      rw [hIM0, hu1]; simp only [Nat.add_zero]; omega
  rintro m r ⟨j, rfl, hjL, hjr, hqer, hlvlr, hnr, hAr, hAlr, hLr, hDRr, hUr, hwlr, hvlr, hc1, hc2, husr⟩
  have hcapr : r.cap = st.cap := hUr.cap
  have eT : evalW r (lt (var "sp.i") (var "sp.qe")) = some (if j < lK.length then 1 else 0) := by
    simp only [evalW_lt', evalW_var, hjr, hqer, Option.bind_some]
    split_ifs <;> simp [fit_of_lt (show 1 < r.cap by rw [hcapr]; omega), fit_of_lt (show 0 < r.cap by omega)]
  refine ⟨if j < lK.length then 1 else 0, eT, fun hx => ?_, fun hx => ?_⟩
  · have hj : j < lK.length := by by_contra hc; rw [if_neg hc] at hx; exact hx rfl
    -- `px := hp_A[sp.i]`
    have eP : evalW (r.charge 1) (load "hp_A" (var "sp.i")) = some (lK[j] : ℕ) := by
      simp [hjr, hAlr, hlA, show j < G.n by omega, hAr, hslot j hj]
    refine runs_seq (runs_wset eP ?_)
    set r2 := ((r.charge 1).setW "px" (lK[j] : ℕ)).charge 1 with hr2
    have hU12 : Unchanged r r2 [] [] convRegs [] := by
      rw [hr2, Frontier.RAM.unch_charge, Frontier.RAM.unch_setW (by simp [convRegs]), Frontier.RAM.unch_charge]; exact Unchanged.refl _ _ _ _ _
    have hDR2 : DL.DR r2 H (IM j).1 (Function.update Ds 0 (IM j).2.1) 0 := DR_unch hframe hDRr hU12 rfl
    have hL2 : LabAt r2 d H c0 := hLr.of_unchanged hU12 (fun _ _ h => absurd h List.not_mem_nil) (by simp)
      (by rw [hr2]; simp only [State.charge_cost, State.setW_cost]; omega)
    have hIMs0 : IM (j + 1) =
        ((BM.insC (dlOps G s) (T 0) (IM j).1 (IM j).2.1 lK[j] (d lK[j])).1,
         (BM.insC (dlOps G s) (T 0) (IM j).1 (IM j).2.1 lK[j] (d lK[j])).2.1,
         (IM j).2.2 + (BM.insC (dlOps G s) (T 0) (IM j).1 (IM j).2.1 lK[j] (d lK[j])).2.2) := by
      simp only [hIM]
      rw [htake j hj, RamInit.insManyC_snoc]
    have hu2 : DL.use r2 = DL.use r := DL.use_frame r r2 _ _ _ _ hU12 hcRd
    have hpre : (IM (j + 1)).2.2 ≤ (BM.insManyC (dlOps G s) (T 0) d lK g (newC M Bd)).2.2 :=
      insManyC_take_le (T 0) d lK (j + 1) g (newC M Bd)
    have hBdj : ((Function.update Ds 0 (IM j).2.1) 0).Bd = Bd := by
      rw [Function.update_self]; simp only [hIM]; rw [insManyC_Bd]; rfl
    have hltj : d lK[j] < ((Function.update Ds 0 (IM j).2.1) 0).Bd := by
      rw [hBdj]; exact hlt _ (by rw [← hset, List.mem_toFinset]; exact List.getElem_mem hj)
    refine runs_seq ((DL.ins_spec r2 H (IM j).1 (Function.update Ds 0 (IM j).2.1) 0 d c0 lK[j] hDR2 hL2
      (by simp [hr2, hlvlr]) (by simp [hr2, hnr]) (by simp [hr2]) hltj (by
        rw [Function.update_self, hu2]
        rw [hIMs0] at hpre; simp only at hpre
        omega)).mono ?_)
    rintro r3 ⟨hDR3, hU3, hwl3, hvl3, hc3a, hc3b, hus3⟩
    rw [Function.update_self, Function.update_idem] at hDR3
    rw [Function.update_self] at hc3b hus3
    have hIMs : IM (j + 1) =
        ((BM.insC (dlOps G s) (T 0) (IM j).1 (IM j).2.1 lK[j] (d lK[j])).1,
         (BM.insC (dlOps G s) (T 0) (IM j).1 (IM j).2.1 lK[j] (d lK[j])).2.1,
         (IM j).2.2 + (BM.insC (dlOps G s) (T 0) (IM j).1 (IM j).2.1 lK[j] (d lK[j])).2.2) := by
      simp only [hIM]
      rw [htake j hj, RamInit.insManyC_snoc]
    have hj3 : r3.w "sp.i" = j := by
      rw [hU3.wreg "sp.i" (hcR _ (by simp [convRegs]))]; simp [hr2, hjr]
    have hqe3 : r3.w "sp.qe" = lK.length := by
      rw [hU3.wreg "sp.qe" (hcR _ (by simp [convRegs]))]; simp [hr2, hqer]
    have hlvl3 : r3.w "lvl" = 0 := by rw [hU3.wreg _ hlvlD]; simp [hr2, hlvlr]
    have hn3 : r3.w "n" = G.n := by rw [hU3.wreg _ hnD]; simp [hr2, hnr]
    have hA3 : r3.wa "hp_A" = st.wa "hp_A" := by rw [(hU3.warr _ hA).1]; simp [hr2, hAr]
    have hAl3 : r3.wlen "hp_A" = st.wlen "hp_A" := by rw [(hU3.warr _ hA).2]; simp [hr2, hAlr]
    have hcap3 : r3.cap = st.cap := by rw [hU3.cap]; simp [hr2, hcapr]
    have hL3 : LabAt r3 d H c0 := hL2.of_unchanged hU3 (labW_not_dWA DL) (dlen_not_dVA DL) hc3a
    have e5 : evalW r3 (add (var "sp.i") (lit 1)) = some (j + 1) := by
      simp [hj3, hcap3, fit_of_lt (show j + 1 < st.cap by omega), fit_of_lt (show 1 < st.cap by omega)]
    refine runs_wset e5 ?_
    set r4 := (r3.setW "sp.i" (j + 1)).charge 1 with hr4
    have hDR4 : DL.DR r4 H (IM (j + 1)).1 (Function.update Ds 0 (IM (j + 1)).2.1) 0 := by
      rw [hIMs]; exact DR_setW hframe hDR3 (hcR _ (by simp [convRegs])) _ _
    refine ⟨lK.length - (j + 1), by omega, j + 1, rfl, by omega, by simp [hr4], by simp [hr4, hqe3],
      by simp [hr4, hlvl3], by simp [hr4, hn3], by simp [hr4, hA3], by simp [hr4, hAl3], ?_, hDR4, ?_,
      by simp [hr4, hwl3, hr2, hwlr], by simp [hr4, hvl3, hr2, hvlr], ?_, ?_, ?_⟩
    · exact hL3.of_unchanged (show Unchanged r3 r4 [] [] convRegs [] by
        rw [hr4, Frontier.RAM.unch_charge, Frontier.RAM.unch_setW (by simp [convRegs])]; exact Unchanged.refl _ _ _ _ _)
        (fun _ _ h => absurd h List.not_mem_nil) (by simp) (by simp [hr4])
    · rw [hr4, Frontier.RAM.unch_charge, Frontier.RAM.unch_setW (by simp [convRegs])]
      refine (hUr.trans ?_)
      refine (Unchanged.charge r 1 _ _ _ _).trans ?_
      refine (show Unchanged (r.charge 1) r2 DL.dWA DL.dVA (convRegs ++ DL.dWR) DL.dVR by
        rw [hr2, Frontier.RAM.unch_charge, Frontier.RAM.unch_setW (by simp [convRegs])]; exact Unchanged.refl _ _ _ _ _).trans ?_
      exact hU3.mono (by simp) (by simp) (by simp) (by simp)
    · simp [hr4]; simp [hr2] at hc3a; omega
    · rw [hIMs]
      simp only [hr4, State.charge_cost, State.setW_cost]
      simp only [hr2, State.charge_cost, State.setW_cost] at hc3b
      rw [Nat.mul_add, Nat.mul_one] at hc3b
      rw [Nat.mul_add, Nat.add_mul]
      omega
    · have hu4 : DL.use r4 = DL.use r3 := DL.use_frame r3 r4 _ _ _ _ (show Unchanged r3 r4 [] [] convRegs [] by
        rw [hr4, Frontier.RAM.unch_charge, Frontier.RAM.unch_setW (by simp [convRegs])]
        exact Unchanged.refl _ _ _ _ _) hcRd
      rw [hu4, hIMs]; simp only; omega
  · have hj : j = lK.length := by by_contra hc; rw [if_pos (by omega)] at hx; exact one_ne_zero hx
    subst hj
    have htk : lK.take lK.length = lK := List.take_length
    have hIMp : IM lK.length = BM.insManyC (dlOps G s) (T 0) d lK g (newC M Bd) := by
      simp only [hIM, htk]
    rw [hIMp] at hDRr hc2 husr
    refine ⟨?_, hLr.of_unchanged (Unchanged.charge r 1 [] [] [] []) (fun _ _ h => absurd h List.not_mem_nil)
      (by simp) (by simp), by simp [hlvlr], by rw [Frontier.RAM.unch_charge]; exact hUr, by simp [hwlr], by simp [hvlr],
      by simp; omega, by simp; omega, by
        rw [DL.use_frame r (r.charge 1) _ _ _ _ (Unchanged.charge r 1 [] [] [] []) (by simp)]; exact husr⟩
    exact hframe r _ H H _ _ 0 [] [] [] [] hDRr (Unchanged.charge r 1 [] [] [] [])
      (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)
      (fun _ h => absurd h List.not_mem_nil) (HExt.refl _ _)

end Frontier.CHD.RamSpine
