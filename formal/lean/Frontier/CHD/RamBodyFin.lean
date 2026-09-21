import Frontier.CHD.RamBodyI
import Frontier.CHD.RamBodySpec
import Frontier.CHD.RamBodyFinB
import Frontier.CHD.RamBodyFinDefs
import Frontier.CHD.RamBodyF
import Frontier.CHD.RamBodyA
import Frontier.CHD.RelW
import Frontier.CHD.RamFin
import Frontier.CHD.WinScanF
import Frontier.CHD.BaseUtil
import Frontier.CHD.PtrLoop
import Frontier.CHD.DLazyFacts

/-!
# Frontier.CHD.RamBodyFin — the finalization of a level-`(l+1)` call (owner agent-03)

**NON-GATE** (B-L4, the level body's last phase, COORD G2-13 (c)).  From the main loop's exit
(`LoopRep` at the final configuration `c`), `finProg` (BM.24a–31) realizes the tail of
`BMLazy.CallD`:
* BM.24a `B'f := if view(D) = ∅ then B else B'` (`bpfProg` with `DL.empty`, `copyBtoBp`);
* BM.25 the T6 insertions (`t6Prog tstT6 DL.ins`, agent-01's `testI_T6` / `dInsI_of`);
* BM.26 `W'` into the `Wp` row and the `U` row (`wpProg tstWp`, `testI_Wp`);
* BM.27–28 the relaxations out of `W'` with `lo = B'f` (agent-02's `relW_spec`);
* BM.29 the deletion of `W'`'s keys (`DelWB`);
* BM.30–31 the clears (`clearsProg`, two `rowZero`s),
and ends in the `CallOut` facts at level `l+1` (`FinPost`), at cost
`≤ Kfin · (1 + |S| + |W| + |W'| + finD cost) + 3 |U| + Efin`.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamBody

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.RamLevel
  Frontier.CHD.BM Frontier.CHD.RamBaseCase Frontier.CHD.LabTab Frontier.CHD.RamSpine
  Frontier.CHD.RamInit Frontier.CHD.WinScan WExpr Stmt

variable {G : Graph} {s : Fin G.n} {T : ℕ → ℕ} {Φ : Type}

theorem pickB_bpfB (B : WLab G s) {p : ℕ} (cs : CSt G s p) :
    pickB (cs.g.view cs.Dc).IsEmpty B cs.B' = bpfB B cs := by
  by_cases h : (cs.g.view cs.Dc).IsEmpty
  · rw [pickB_pos h, bpfB_empty h]
  · rw [pickB_neg h, bpfB_ne h]

/-! ## BM.24a: `B'f` into slot `B'[l]` -/

theorem slotFresh_K24 : SlotFresh K24 "f24.kf" := ⟨by decide⟩

/-- `slot[B'[lvl]] := slot[B[lvl]]`. -/
theorem copyBtoBp_spec (st : State ℝ≥0) {lv : ℕ} (hl : st.w "lvl" = lv) (hc : 4 * lv + 8 < st.cap)
    {H : Hist G} {V : Fin G.n → ℕ} {b : WLab G s} (hB : SlotHolds st (slotB lv) H V b)
    (hsl : SlotLens st (slotB lv)) (hslp : SlotLens st (slotBp lv)) :
    Runs realOps copyBtoBp st (fun r => SlotHolds r (slotBp lv) H V b ∧
      (∀ j, j ≠ slotBp lv → r.va "sl.l" j = st.va "sl.l" j ∧ ∀ a ∈ slotW, r.wa a j = st.wa a j) ∧
      Unchanged st r slotW ["sl.l"] ("sl.i" :: "f24.kf" :: K24.ws) [K24.l] ∧
      r.cost = st.cost + 14) := by
  refine runs_seq (runs_wset (a := 4 * lv) (evalW_mul_of' (evalW_lit_of (by omega))
    (by rw [evalW_var, hl]) (by omega)) ?_)
  set s1 := (st.setW "sl.i" (4 * lv)).charge 1 with hs1
  have hU1 : Unchanged st s1 [] [] ["sl.i"] [] := by
    rw [hs1, Frontier.RAM.unch_charge, Frontier.RAM.unch_setW (by simp)]; exact Unchanged.refl _ _ _ _ _
  refine runs_seq ((loadSlot_spec K24 "f24.kf" slotFresh_K24 s1 (by simp [hs1, slotB])
    (SlotLens.of_unchanged hsl hU1 (by simp) (by simp)) (hB.of_unchanged hU1 (by simp) (by simp))).mono ?_)
  rintro s2 ⟨hK2, hU2, hc2⟩
  have hU02 := hU1.comp hU2
  have hl2 : s2.w "lvl" = lv := by rw [hU02.wreg "lvl" (by simp [K24, LReg.ws])]; exact hl
  refine runs_seq (runs_wset (a := 4 * lv + 2) (evalW_slotSet hl2 (by rw [hU02.cap]; omega)) ?_)
  set s3 := (s2.setW "sl.i" (4 * lv + 2)).charge 1 with hs3
  have hU23 : Unchanged s2 s3 [] [] ["sl.i"] [] := by
    rw [hs3, Frontier.RAM.unch_charge, Frontier.RAM.unch_setW (by simp)]; exact Unchanged.refl _ _ _ _ _
  have hU03 := hU02.comp hU23
  have hK3 : WHolds s3 K24 "f24.kf" H V b := hK2.of_unchanged hU23 (by decide) (by simp) (by decide)
  have hslp3 : SlotLens s3 (slotBp lv) := SlotLens.of_unchanged hslp hU03 (by simp) (by simp)
  refine (storeSlot_spec K24 "f24.kf" s3 (by simp [hs3, slotBp]) hslp3 hK3).mono ?_
  rintro r ⟨hSH, hfr, hU4, hc4⟩
  have hU04 := hU03.comp hU4
  refine ⟨hSH, fun j hj => ⟨?_, fun a ha => ?_⟩, ?_, ?_⟩
  · rw [(hfr j hj).1, (hU03.varr "sl.l" (by simp)).1]
  · rw [(hfr j hj).2 a ha, (hU03.warr a (by simp)).1]
  · exact hU04.mono (by intro a ha; simp at ha ⊢; tauto) (by intro a ha; simp at ha ⊢; exact ha)
      (by intro a ha; simp [K24, LReg.ws] at ha ⊢; tauto) (by intro a ha; simp [K24, LReg.ws] at ha ⊢; exact ha)
  · simp only [hc4, hs3, State.charge_cost, State.setW_cost, hc2, hs1]

/-- **BM.24a** (FIX-EMPTY): after `bpfProg DL.empty`, slot `B'[lv]` holds `B` if the level's view
is empty, and its previous content `B'` otherwise. -/
theorem bpf_spec (DL : DLayer G s T) (st : State ℝ≥0) (H : Hist G) (g : DGl G s)
    (Ds : ℕ → DStrM G s) (lv : ℕ) (B B' : WLab G s) (hD : DL.DR st H g Ds lv)
    (hl : st.w "lvl" = lv) (hn : st.w "n" = G.n)
    (hB : SlotHolds st (slotB lv) H (vc st) B) (hBp : SlotHolds st (slotBp lv) H (vc st) B')
    (hsl : SlotLens st (slotB lv)) (hslp : SlotLens st (slotBp lv)) (hc : 4 * lv + 8 < st.cap)
    (hK : ∀ a ∈ "f24.kf" :: K24.ws, a ∉ DL.dWR) :
    Runs realOps (bpfProg DL.empty) st (fun r => DL.DR r H g Ds lv ∧
      SlotHolds r (slotBp lv) H (vc r) (pickB (g.view (Ds lv)).IsEmpty B B') ∧
      (∀ j, j ≠ slotBp lv → r.va "sl.l" j = st.va "sl.l" j ∧ ∀ a ∈ slotW, r.wa a j = st.wa a j) ∧
      Unchanged st r (DL.dWA ++ slotW) (DL.dVA ++ ["sl.l"])
        (DL.dWR ++ ["sp.em"] ++ ("sl.i" :: "f24.kf" :: K24.ws)) (DL.dVR ++ [K24.l]) ∧
      vc (G := G) r = vc st ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + DL.K + 16 ∧ DL.use r = DL.use st) := by
  refine runs_seq ((DL.empty_spec st H g Ds lv hD hl hn).mono ?_)
  rintro r1 ⟨hD1, hem, hU1, hwl1, hvl1, hc1l, hc1, hus1⟩
  have hslW : ∀ a ∈ slotW, a ∉ DL.dWA := fun a ha h => DL.dWA_ok a h (by
    simp only [slotW, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide)
  have hsll : "sl.l" ∉ DL.dVA := fun h => DL.dVA_ok _ h (by simp)
  have hvc1 : vc (G := G) r1 = vc st := vc_of_unchanged hU1 (fun h => DL.dWA_ok _ h (by decide))
  have hB1 : SlotHolds r1 (slotB lv) H (vc r1) B := by rw [hvc1]; exact hB.of_unchanged hU1 hslW hsll
  have hBp1 : SlotHolds r1 (slotBp lv) H (vc r1) B' := by
    rw [hvc1]; exact hBp.of_unchanged hU1 hslW hsll
  have hsl1 := RamSpine.SlotLens.of_len hsl hwl1 hvl1
  have hslp1 := RamSpine.SlotLens.of_len hslp hwl1 hvl1
  have hlv : "lvl" ∉ DL.dWR ++ ["sp.em"] := by
    intro h; rcases List.mem_append.mp h with h | h
    · exact DL.dWR_ok _ h (by decide)
    · simp at h
  have hl1 : r1.w "lvl" = lv := by rw [hU1.wreg "lvl" hlv]; exact hl
  have hcap1 : r1.cap = st.cap := hU1.cap
  by_cases he : (g.view (Ds lv)).IsEmpty
  · -- the view is empty: `B'[lv] := B`
    have hx : r1.w "sp.em" ≠ 0 := fun h0 => (hem.mp h0) he
    refine runs_ite_true (x := r1.w "sp.em") (by rw [evalW_var]) hx ?_
    refine ((Frontier.RAM.Runs.noAl (by decide) (copyBtoBp_spec (r1.charge 1) (by simp [hl1])
      (by simp [hcap1]; omega) hB1 (RamSpine.SlotLens.of_len hsl1 rfl rfl)
      (RamSpine.SlotLens.of_len hslp1 rfl rfl))).mono ?_)
    rintro r ⟨⟨hSH, hfr, hU2, hc2⟩, hwl2, hvl2⟩
    have hU12 := (Unchanged.charge r1 1 [] [] [] []).comp hU2
    have hvc2 : vc (G := G) r = vc r1 := vc_of_unchanged hU12 (by decide)
    refine ⟨DL.frame r1 r H H g Ds lv _ _ _ _ hD1 hU12 (fun a ha h => hslW a h ha)
      (fun a ha h => by simp at h; subst h; exact hsll ha)
      (fun a ha h => by
        have h' : a ∈ "sl.i" :: "f24.kf" :: K24.ws := by simpa using h
        rcases List.mem_cons.mp h' with h | h
        · subst h; exact DL.dWR_ok _ ha (by decide)
        · exact hK a h ha)
      (by rw [hvc2]; exact HExt.refl _ _), by rw [pickB_pos he, hvc2]; exact hSH,
      fun j hj => ⟨by rw [(hfr j hj).1]; exact congrFun (hU1.varr "sl.l" hsll).1 j,
        fun a ha => by rw [(hfr j hj).2 a ha]; exact congrFun (hU1.warr a (hslW a ha)).1 j⟩, ?_,
      by rw [hvc2, hvc1], ?_, ?_, by simp at hc2; omega, by simp at hc2; omega, ?_⟩
    · exact (hU1.comp hU12).mono (by intro a ha; simp at ha ⊢; tauto) (by intro a ha; simp at ha ⊢; tauto)
        (by intro a ha; simp [K24, LReg.ws] at ha ⊢; tauto) (by intro a ha; simp [K24, LReg.ws] at ha ⊢; tauto)
    · rw [hwl2]; exact hwl1
    · rw [hvl2]; exact hvl1
    · rw [← hus1]
      exact DL.use_frame r1 r _ _ _ _ hU12 (fun a ha h => by
        have h' : a ∈ "sl.i" :: "f24.kf" :: K24.ws := by simpa using h
        rcases List.mem_cons.mp h' with h | h
        · subst h; exact DL.dWR_ok _ ha (by decide)
        · exact hK a h ha)
  · -- the view is not empty: `B'[lv]` stays
    have hx : r1.w "sp.em" = 0 := hem.mpr he
    refine runs_ite_false (by rw [evalW_var, hx]) (runs_skip ?_)
    have hU12 : Unchanged r1 ((r1.charge 1).charge 1) [] [] [] [] :=
      (Unchanged.charge r1 1 [] [] [] []).trans (Unchanged.charge _ 1 [] [] [] [])
    refine ⟨DL.frame r1 _ H H g Ds lv _ _ _ _ hD1 hU12 (by simp) (by simp) (by simp)
      (HExt.refl _ _), by rw [pickB_neg he]; exact hBp1,
      fun j _ => ⟨congrFun (hU1.varr "sl.l" hsll).1 j, fun a ha => congrFun (hU1.warr a (hslW a ha)).1 j⟩, ?_,
      hvc1, hwl1, hvl1, by simp; omega, by simp; omega, ?_⟩
    · exact (hU1.comp hU12).mono (by intro a ha; simp at ha ⊢; tauto) (by intro a ha; simp at ha ⊢; tauto)
        (by intro a ha; simp at ha ⊢; tauto) (by intro a ha; simp at ha ⊢; tauto)
    · rw [← hus1]; exact DL.use_frame r1 _ _ _ _ _ hU12 (by simp)

/-! ## BM.25: the T6 insertions -/

/-- **BM.25**: the T6 vertices of the `S` row (`B'f ≤ d x < B`) into the level's structure. -/
theorem t6_spec (DL : DLayer G s T) (st : State ℝ≥0) (H : Hist G) (Ds : ℕ → DStrM G s) (lv : ℕ)
    (d : Labels G s) (c0 : ℕ) (B B'f : WLab G s) (g : DGl G s) (D : DStrM G s)
    (hD : DL.DR st H g (Function.update Ds lv D) lv) (hL : LabAt st d H c0)
    (hl : st.w "lvl" = lv) (hn : st.w "n" = G.n)
    (hB : SlotHolds st (slotB lv) H (vc st) B) (hBp : SlotHolds st (slotBp lv) H (vc st) B'f)
    (hsl : SlotLens st (slotB lv)) (hslp : SlotLens st (slotBp lv)) (hc4 : 4 * lv + 8 < st.cap)
    {lS : List (Fin G.n)} (hS : RowRep st "S" "S.len" G.n lv (lS.map Fin.val))
    (hcap : (lv + 1) * G.n + 2 < st.cap)
    (hTW : ∀ a ∈ DL.dWR, a ∉ tstW) (hFR : ∀ a ∈ DL.dWR, a ∉ t6Regs) (hDBd : D.Bd = B)
    (hUb : DL.use st +
      (BM.insManyC (dlOps G s) (T lv) d (lS.filter fun x => decide (PT6 d B B'f x)) g D).2.2 +
      lS.length ≤ DL.ucap) :
    Runs realOps (t6Prog tstT6 DL.ins) st (fun r =>
      DL.DR r H (BM.insManyC (dlOps G s) (T lv) d (lS.filter fun x => decide (PT6 d B B'f x)) g D).1
        (Function.update Ds lv
          (BM.insManyC (dlOps G s) (T lv) d (lS.filter fun x => decide (PT6 d B B'f x)) g D).2.1) lv ∧
      LabAt r d H c0 ∧ r.w "lvl" = lv ∧ r.w "n" = G.n ∧ SlotsE H lv B B'f (fun _ => True) r ∧
      Unchanged st r DL.dWA DL.dVA (t6Regs ++ tstW ++ DL.dWR) (tstV ++ DL.dVR) ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + 2 +
        DL.K * (BM.insManyC (dlOps G s) (T lv) d (lS.filter fun x => decide (PT6 d B B'f x)) g D).2.2 +
        lS.length * (59 + DL.K + 6) ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen ∧
      DL.use r ≤ DL.use st +
        (BM.insManyC (dlOps G s) (T lv) d (lS.filter fun x => decide (PT6 d B B'f x)) g D).2.2 +
        lS.length) := by
  have hE1 : ∀ st r, SlotsE H lv B B'f (fun _ => True) st →
      Unchanged st r DL.dWA DL.dVA DL.dWR DL.dVR → r.wlen = st.wlen → r.vlen = st.vlen →
      st.cost ≤ r.cost → SlotsE H lv B B'f (fun _ => True) r :=
    fun st r h hU hwl hvl _ => slotsE_of_unch h hU (dl_slotW DL) (dl_sll DL) (dl_vcnt DL) hwl hvl trivial
  have hE2 : ∀ st r, SlotsE H lv B B'f (fun _ => True) st → Unchanged st r [] [] t6Regs [] →
      st.cost ≤ r.cost → SlotsE H lv B B'f (fun _ => True) r :=
    fun st r h hU _ => slotsE_of_unch h hU (by simp) (by simp) (by simp)
      (funext fun a => (hU.warr a (by simp)).2) (funext fun a => (hU.varr a (by simp)).2) trivial
  have hI := dInsI_of DL H Ds lv d c0 (SlotsE H lv B B'f (fun _ => True)) (FR := t6Regs) B hE1 hE2 hFR
    (by decide) (by decide)
  have hT := testI_T6 DL H Ds lv d c0 B B'f (fun _ => True) hTW (fun _ _ _ _ _ => trivial)
  refine (t6Prog_spec (ops := realOps) hT hI st g D ⟨hD, hL, hl, hn, hB, hBp, hsl, hslp, hc4, trivial⟩
    hS hl hn hcap (fun k hk _ => by rw [insManyC_Bd]; exact hDBd)
    (fun k hk hP => by obtain ⟨h, -, h2⟩ := hP; exact h2)
    (fun a ha h => hTW a h ha) hUb).mono ?_
  rintro r ⟨⟨hD', hL', hl', hn', hE'⟩, hU, hc1, hc2, hwl, hvl, hus⟩
  exact ⟨hD', hL', hl', hn', hE', hU, hc1, hc2, hwl, hvl, hus⟩

/-! ## BM.26: `W'` into the `Wp` and `U` rows -/

/-- **BM.26**: the members `x ∉ U` of the `W` row with `d x < B'f`, appended to the `Wp` and `U`
rows (agent-01's `wpProg_spec` with `testI_Wp`). -/
theorem wp_spec (DL : DLayer G s T) (hdA : ∀ a ∈ DL.dWA, a ∉ ["Wp", "Wp.len"])
    (st : State ℝ≥0) (H : Hist G) (Ds : ℕ → DStrM G s) (lv : ℕ) (d : Labels G s) (c0 : ℕ)
    (B B'f : WLab G s) (g : DGl G s) (D : DStrM G s)
    (hDR : DRl DL H Ds lv d c0 (SlotsE H lv B B'f (fun _ => True)) st g D)
    {lW lU : List (Fin G.n)} (hW : lW.Nodup) (hU : lU.Nodup)
    (hWr : RowRep st "W" "W.len" G.n lv (vals lW)) (hUr : RowRep st "U" "U.len" G.n lv (vals lU))
    (hinU : ∀ x < G.n, st.wa "sp.inU" (lv * G.n + x) = if x ∈ vals lU then 1 else 0)
    (hWpl : (lv + 1) * G.n ≤ st.wlen "Wp") (hWpll : lv < st.wlen "Wp.len")
    (hinUl : (lv + 1) * G.n ≤ st.wlen "sp.inU") (hcap : (lv + 1) * G.n + G.n + 2 < st.cap)
    (hTW : ∀ a ∈ DL.dWR, a ∉ tstW) (hFR : ∀ a ∈ DL.dWR, a ∉ t6Regs) :
    Runs realOps (wpProg tstWp) st (fun r =>
      WpInv st r lv G.n lW lU (fun x => x ∉ lU ∧ PWp d B'f (x : ℕ)) lW.length ∧
      DRl DL H Ds lv d c0 (SlotsE H lv B B'f (fun _ => True)) r g D ∧
      Unchanged st r wpArrs [] (t6Regs ++ tstW) tstV ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + 3 + lW.length * (29 + 16) ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen) := by
  have hT := testI_Wp DL H Ds lv d c0 B B'f (fun _ => True) hTW (fun _ _ _ _ _ => trivial)
  have hwA : ∀ a ∈ wpArrs, a ∉ DL.dWA := by
    intro a ha h
    simp only [wpArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact hdA _ h (by simp)
    · exact hdA _ h (by simp)
    all_goals exact DL.dWA_ok _ h (by decide)
  have hDRf : ∀ st r, DRl DL H Ds lv d c0 (SlotsE H lv B B'f (fun _ => True)) st g D →
      Unchanged st r wpArrs [] t6Regs [] → st.cost ≤ r.cost →
      DRl DL H Ds lv d c0 (SlotsE H lv B B'f (fun _ => True)) r g D := by
    intro st r h hU hc
    obtain ⟨hD, hL, hl, hn, hB, hBp, hsl, hslp, hc4, -⟩ := h
    have hvc : vc (G := G) r = vc st := vc_of_unchanged hU (by decide)
    refine ⟨DL.frame st r H H g _ lv _ _ _ _ hD hU (fun a ha h => hwA a h ha) (by simp)
        (fun a ha h => hFR a ha h) (by rw [hvc]; exact HExt.refl _ _),
      hL.of_unchanged hU (by decide) (by simp) hc, by rw [hU.wreg _ (by decide)]; exact hl,
      by rw [hU.wreg _ (by decide)]; exact hn,
      by rw [hvc]; exact hB.of_unchanged hU (by decide) (by simp),
      by rw [hvc]; exact hBp.of_unchanged hU (by decide) (by simp),
      RamBaseCase.SlotLens.of_unchanged hsl hU (by decide) (by simp),
      RamBaseCase.SlotLens.of_unchanged hslp hU (by decide) (by simp), by rw [hU.cap]; exact hc4,
      trivial⟩
  refine (Frontier.RAM.Runs.noAl (by decide) (wpProg_spec (ops := realOps) hT hDRf st hDR hW hU hWr hUr
    hinU hWpl hWpll hinUl hDR.2.2.1 hDR.2.2.2.1 le_rfl hcap)).mono ?_
  rintro r ⟨⟨hWI, hDR', hU', hc1, hc2⟩, hwl, hvl⟩
  exact ⟨hWI, hDR', hU', hc1, hc2, hwl, hvl⟩

/-! ## BM.30–31: the clears -/

/-- **BM.30–31**: the group memberships over the `S` row and the `inU` marks over the `U` row. -/
theorem clears_spec (st : State ℝ≥0) {lv : ℕ} {xs ys : List ℕ}
    (hS : RowRep st "S" "S.len" G.n lv xs) (hU : RowRep st "U" "U.len" G.n lv ys)
    (hl : st.w "lvl" = lv) (hn : st.w "n" = G.n) (hxs : ∀ x ∈ xs, x < G.n) (hys : ∀ y ∈ ys, y < G.n)
    (hg : (lv + 1) * G.n ≤ st.wlen "sp.g") (hu : (lv + 1) * G.n ≤ st.wlen "sp.inU")
    (hcap : (lv + 1) * G.n + 1 < st.cap) :
    Runs realOps clearsProg st (fun r =>
      (∀ i, r.wa "sp.g" i = if ∃ x ∈ xs, i = lv * G.n + x then 0 else st.wa "sp.g" i) ∧
      (∀ i, r.wa "sp.inU" i = if ∃ y ∈ ys, i = lv * G.n + y then 0 else st.wa "sp.inU" i) ∧
      Unchanged st r ["sp.g", "sp.inU"] [] ["rz.i"] [] ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen ∧
      r.cost = st.cost + 3 * xs.length + 3 * ys.length + 4) := by
  refine runs_seq ((rowZero_spec (ops := realOps) st (arr := "sp.g") (by decide) (by decide) hS hl hn hxs hg
    hcap).mono ?_)
  rintro r1 ⟨hz1, hU1, hwl1, hc1⟩
  have e1 := hU1.warr "U" (by decide)
  have e2 := hU1.warr "U.len" (by decide)
  have hU' : RowRep r1 "U" "U.len" G.n lv ys :=
    RamLevel.RowRep.of_eq hU e1.2 e2.2 (by rw [e2.1]) (fun i _ => by rw [e1.1])
  refine ((rowZero_spec (ops := realOps) r1 (arr := "sp.inU") (by decide) (by decide) hU'
    (by rw [hU1.wreg "lvl" (by decide)]; exact hl) (by rw [hU1.wreg "n" (by decide)]; exact hn) hys
    (by rw [hwl1]; exact hu) (by rw [hU1.cap]; exact hcap)).mono ?_)
  rintro r ⟨hz2, hU2, hwl2, hc2⟩
  refine ⟨fun i => ?_, fun i => ?_, ?_, hwl2.trans hwl1, ?_, by rw [hc2, hc1]; ring⟩
  · rw [show r.wa "sp.g" = r1.wa "sp.g" from (hU2.warr "sp.g" (by decide)).1, hz1 i]
  · rw [hz2 i, show r1.wa "sp.inU" = st.wa "sp.inU" from (hU1.warr "sp.inU" (by decide)).1]
  · exact (hU1.comp hU2).mono (by intro a ha; simp at ha ⊢; tauto) (by simp)
      (by intro a ha; simp at ha ⊢; exact ha) (by simp)
  · funext a
    rw [(hU2.varr a (by simp)).2, (hU1.varr a (by simp)).2]

set_option maxHeartbeats 4000000 in
/-- **The finalization** (BM.24a–31) of a call at level `l+1`, from the main loop's exit. -/
theorem fin_spec (DL : DLayer G s T) (PI : PhiI Φ) (hN : FinNames DL PI) {delW : Stmt}
    (hDel : DelWBU DL delW) (hsort : CSRSorted G s) {LF : ℕ} {body : Stmt} {τ Mf : ℕ → ℕ}
    (st : State ℝ≥0) (l : ℕ) (B : WLab G s) (S W : Finset (Fin G.n)) (wl : List (Fin G.n))
    (Ds : ℕ → DStrM G s) (H : Hist G) (c0 : ℕ) {p : ℕ} (c : LoopCfgD G s Φ p)
    (hloop : LoopRep DL PI LF body τ Mf st (l + 1) B (τ (l + 1)) Ds H c0 c)
    (hS : SetRow st "S" "S.len" (l + 1) S)
    (hW : RowRep st "W" "W.len" G.n (l + 1) (wl.map Fin.val)) (hwnd : wl.Nodup) (hwset : wl.toFinset = W)
    (hWp : (l + 2) * G.n ≤ st.wlen "Wp" ∧ l + 1 < st.wlen "Wp.len")
    -- Layer-A facts of the loop exit (from `ALoop` / `LInv`: agent-01's `wp_complete`, `bodyA_fold_d`)
    (hwalk : WalkInv c.cs.d)
    (hUc : ∀ u ∈ c.cs.U, c.cs.d u = dis (s := s) u)
    (hW'c : ∀ x ∈ W, x ∉ c.cs.U → c.cs.d x < bpfB B c.cs → c.cs.d x = dis (s := s) x)
    (hPS : ∀ j, ∀ x ∈ c.cs.P j, x ∈ S)
    (hBd : c.cs.Dc.Bd = B)
    -- the `D`-layer use of every completion of the tail (∀-outcome form)
    (hUse : ∀ (lT6 : List (Fin G.n)) (L : List (Fin G.m)) (lW' : List (Fin G.n)), lT6.Nodup →
      (∀ x, x ∈ lT6 ↔ x ∈ S ∧ bpfB B c.cs ≤ c.cs.d x ∧ c.cs.d x < B) → lW'.Nodup →
      (∀ x, x ∈ lW' ↔ (x ∈ W ∧ x ∉ c.cs.U) ∧ c.cs.d x < bpfB B c.cs) →
      Enumerates G L lW'.toFinset →
      DL.use st + S.card +
        (finD (dlOps G s) (T (l + 1)) B (bpfB B c.cs) c.cs.d c.cs.g c.cs.Dc lT6 L lW').2.2.2 ≤ DL.ucap)
    -- the static budget of the T6 inserts and of the relaxations (agent-02's `relW_spec`)
    (hbud : st.cost + Kfin DL.K * (1 + S.card + W.card) + DL.K * (S.card * (Nat.log 2 DL.NB + 4)) +
      (W.card + 1) * ((G.m + 1) * CED DL.K DL.NB + 101) ≤ c0 + st.cap) :
    Runs realOps (finProg DL.empty tstT6 DL.ins tstWp (relW DL.ins) delW) st (fun r =>
      ∃ (lT6 : List (Fin G.n)) (W' : Finset (Fin G.n)) (lW' : List (Fin G.n)) (L : List (Fin G.m))
        (H' : Hist G), FinOut DL PI LF body τ Mf st r l B S W Ds H c0 c lT6 W' lW' L H' (Kfin DL.K) 100) := by
  classical
  obtain ⟨hlvl, hl1, hlLF, hstat, hlab, hD, hphi, hgrp, hnp, hU, hinU, hsB, hsBp, htau, hclr, hptr⟩ :=
    hloop
  -- capacities
  have hcapS := hstat.cap
  have hA1 : (l + 2) * G.n ≤ (LF + 1) * G.n := Nat.mul_le_mul_right _ (by omega)
  have hA2 : (LF + 3) * (G.n + G.m + 8) = (LF + 1) * G.n + 2 * G.n + (LF + 3) * (G.m + 8) := by ring
  have hA3 : (LF + 3) * 8 ≤ (LF + 3) * (G.m + 8) := Nat.mul_le_mul_left _ (by omega)
  have hA4 : G.m + 8 ≤ (LF + 3) * (G.m + 8) := Nat.le_mul_of_pos_left _ (by omega)
  have hcapA : (l + 2) * G.n + G.n + G.m + 8 < st.cap := by omega
  have hc4 : 4 * (l + 1) + 8 < st.cap := by omega
  have hn2 : (l + 1 + 1) * G.n = (l + 2) * G.n := rfl
  have hsl0 : SlotLens st (slotB (l + 1)) := hstat.slots _ (by simp [slotB]; omega)
  have hsl2 : SlotLens st (slotBp (l + 1)) := hstat.slots _ (by simp [slotB, slotBp]; omega)
  -- names
  have hfinR : ∀ a ∈ ["f24.kh", "f24.kv", "f24.ke", "f24.kr", "f24.kf", "t6.i", "rz.i"] ++ tstW ++ relWRegs,
      a ∈ finRegs := by
    intro a ha; simp only [finRegs, List.mem_append] at ha ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha ⊢; tauto
  have hdR : ∀ a ∈ DL.dWR, a ∉ ["f24.kh", "f24.kv", "f24.ke", "f24.kr", "f24.kf", "t6.i", "rz.i"] ++ tstW ++
      relWRegs := fun a h hm => hN.dR a h (List.mem_append_left _ (List.mem_append_left _ (hfinR a hm)))
  have hK24 : ∀ a ∈ "f24.kf" :: K24.ws, a ∉ DL.dWR := fun a ha h => hdR a h (by
    simp only [K24, LReg.ws, List.mem_cons, List.not_mem_nil, or_false] at ha
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp)
  have hTW : ∀ a ∈ DL.dWR, a ∉ tstW := fun a h ht => hdR a h (by simp only [List.mem_append]; tauto)
  have hFR : ∀ a ∈ DL.dWR, a ∉ t6Regs := fun a h ht => by
    simp only [t6Regs, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact hdR _ h (by simp)
    · exact DL.dWR_ok _ h (by decide)
  have hgW : "gW" ∉ DL.dVA := fun h => DL.dVA_ok _ h (by simp)
  have hlab' : ∀ a ∈ DL.dWR, a ∉ rwW ++ ["lab.uselo"] := fun a h hm => hN.dR a h (by
    rcases List.mem_append.mp hm with hm | hm
    · exact List.mem_append_left _ (List.mem_append_right _ hm)
    · exact List.mem_append_right _ hm)
  have hvr : ∀ a ∈ DL.dVR, a ∉ relaxV := fun a h hm => hN.dV a h (by
    simp only [finVRegs, List.mem_append]; tauto)
  set DI := DInsI.ofDLayer DL hgW hlab' hvr with hDI
  -- 1. BM.24a
  refine runs_seq ((bpf_spec DL st H c.cs.g (Function.update Ds (l + 1) c.cs.Dc) (l + 1) B c.cs.B' hD hlvl
    hstat.n hsB hsBp hsl0 hsl2 hc4 hK24).mono ?_)
  rintro r1 ⟨hD1, hBp1, hfr1, hU1, hvc1, hwl1, hvl1, hc1l, hc1, hus1'⟩
  simp only [Function.update_self] at hBp1
  rw [pickB_bpfB] at hBp1
  set B'f := bpfB B c.cs with hB'f
  have hcap1 : r1.cap = st.cap := hU1.cap
  have hwa1 : ∀ a, a ∈ spArrs → a ∉ slotW → a ∉ DL.dWA ++ slotW := fun a ha hs h => by
    rcases List.mem_append.mp h with h | h
    · exact DL.dWA_ok a h ha
    · exact hs h
  have hreg1 : ∀ a ∈ spRegs, a ∉ ["sp.em", "sl.i"] → a ∉ DL.dWR ++ ["sp.em"] ++ ("sl.i" :: "f24.kf" :: K24.ws) :=
    fun a ha hne h => by
      rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · exact DL.dWR_ok a h ha
        · exact hne (by simp at h; simp [h])
      · simp only [K24, LReg.ws, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hne (by simp)
        all_goals (revert ha; decide)
  have hl1' : r1.w "lvl" = l + 1 := by rw [hU1.wreg _ (hreg1 _ (by decide) (by decide))]; exact hlvl
  have hn1 : r1.w "n" = G.n := by rw [hU1.wreg _ (hreg1 _ (by decide) (by decide))]; exact hstat.n
  have hL1 : LabAt r1 c.cs.d H c0 := hlab.of_unchanged hU1
    (fun a ha => hwa1 a (by revert ha; revert a; decide) (by revert ha; revert a; decide))
    (fun h => by rcases List.mem_append.mp h with h | h
                 · exact DL.dVA_ok _ h (by simp [labV])
                 · simp at h) hc1l
  have hB1 : SlotHolds r1 (slotB (l + 1)) H (vc r1) B := by
    rw [hvc1]; exact SlotHolds.of_idx hsB (hfr1 _ (by simp [slotB, slotBp])).1
      (hfr1 _ (by simp [slotB, slotBp])).2
  have hsl1 := RamSpine.SlotLens.of_len hsl0 hwl1 hvl1
  have hslp1 := RamSpine.SlotLens.of_len hsl2 hwl1 hvl1
  -- the rows as lists
  obtain ⟨lS, hSr, hlSnd, hlSset⟩ := SetRow.toList hS
  obtain ⟨lU, hUr, hlUnd, hlUset⟩ := SetRow.toList hU
  have hrow1 : ∀ a ∈ ["S", "S.len", "W", "W.len", "U", "U.len", "sp.inU", "sp.g", "gSt", "gHead", "sp.ptr",
      "sp.xm", "cp.tau", "cp.M", "gKeep", "gRep"], r1.wa a = st.wa a ∧ r1.wlen a = st.wlen a := fun a ha =>
    hU1.warr a (hwa1 a (by revert ha; revert a; decide) (by revert ha; revert a; decide))
  have hS1 : RowRep r1 "S" "S.len" G.n (l + 1) (lS.map Fin.val) :=
    RamLevel.RowRep.of_eq hSr (hrow1 "S" (by simp)).2 (hrow1 "S.len" (by simp)).2
      (by rw [(hrow1 "S.len" (by simp)).1]) (fun i _ => by rw [(hrow1 "S" (by simp)).1])
  -- the tail lists (CallD's lT6, W', lW')
  set lT6 := lS.filter fun x : Fin G.n => decide (PT6 c.cs.d B B'f (x : ℕ)) with hlT6
  set lW' := wl.filter (fun x : Fin G.n => decide (x ∉ lU ∧ PWp c.cs.d B'f (x : ℕ))) with hlW'
  have hlT6nd : lT6.Nodup := by rw [hlT6]; exact hlSnd.filter _
  have hlT6mem : ∀ x, x ∈ lT6 ↔ x ∈ S ∧ B'f ≤ c.cs.d x ∧ c.cs.d x < B := by
    intro x
    have e1 : x ∈ lS ↔ x ∈ S := by rw [← hlSset, List.mem_toFinset]
    have e3 : PT6 c.cs.d B B'f (x : ℕ) ↔ B'f ≤ c.cs.d x ∧ c.cs.d x < B :=
      ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.isLt, h⟩⟩
    simp only [hlT6, List.mem_filter, decide_eq_true_iff, e1, e3]
  have hlW'nd : lW'.Nodup := by rw [hlW']; exact hwnd.filter _
  have hlW'mem : ∀ x, x ∈ lW' ↔ (x ∈ W ∧ x ∉ c.cs.U) ∧ c.cs.d x < B'f := by
    intro x
    have e1 : x ∈ wl ↔ x ∈ W := by rw [← hwset, List.mem_toFinset]
    have e2 : x ∈ lU ↔ x ∈ c.cs.U := by rw [← hlUset, List.mem_toFinset]
    have e3 : PWp c.cs.d B'f (x : ℕ) ↔ c.cs.d x < B'f := ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.isLt, h⟩⟩
    simp only [hlW', List.mem_filter, decide_eq_true_iff, e1, e2, e3]
    exact and_assoc.symm
  obtain ⟨L0, hL0⟩ : ∃ L0 : List (Fin G.m), Enumerates G L0 lW'.toFinset :=
    ⟨(Finset.univ.filter (fun e => G.src e ∈ lW'.toFinset)).toList, Finset.nodup_toList _,
      fun e => by simp⟩
  have hU0 := hUse lT6 L0 lW' hlT6nd hlT6mem hlW'nd hlW'mem hL0
  have hfinD : ∀ L lW, (BM.insManyC (dlOps G s) (T (l + 1)) c.cs.d lT6 c.cs.g c.cs.Dc).2.2 ≤
      (finD (dlOps G s) (T (l + 1)) B B'f c.cs.d c.cs.g c.cs.Dc lT6 L lW).2.2.2 := by
    intro L lW; unfold finD; dsimp only; omega
  have hlSl : lS.length = S.card := by rw [← hlSset, List.toFinset_card_of_nodup hlSnd]
  -- 2. BM.25
  refine runs_seq ((t6_spec DL r1 H Ds (l + 1) c.cs.d c0 B B'f c.cs.g c.cs.Dc hD1 hL1 hl1' hn1 hB1 hBp1
    hsl1 hslp1 (by rw [hcap1]; exact hc4) hS1 (by rw [hcap1]; omega) hTW hFR hBd
    (by
      show DL.use r1 + (BM.insManyC (dlOps G s) (T (l + 1)) c.cs.d lT6 c.cs.g c.cs.Dc).2.2 +
        lS.length ≤ DL.ucap
      rw [hus1']; have := hfinD L0 lW'; omega)).mono ?_)
  rintro r2 ⟨hD2, hL2, hl2, hn2', hE2, hU2, hc2l, hc2, hwl2, hvl2, hus2⟩
  set g2 := (BM.insManyC (dlOps G s) (T (l + 1)) c.cs.d lT6 c.cs.g c.cs.Dc).1 with hg2
  set D2 := (BM.insManyC (dlOps G s) (T (l + 1)) c.cs.d lT6 c.cs.g c.cs.Dc).2.1 with hD2def
  have hD2' : DL.DR r2 H g2 (Function.update Ds (l + 1) D2) (l + 1) := hD2
  have hc2' : r2.cost ≤ r1.cost + 2 +
      DL.K * (BM.insManyC (dlOps G s) (T (l + 1)) c.cs.d lT6 c.cs.g c.cs.Dc).2.2 +
      lS.length * (59 + DL.K + 6) := hc2
  have hus2' : DL.use r2 ≤ DL.use st + (BM.insManyC (dlOps G s) (T (l + 1)) c.cs.d lT6 c.cs.g c.cs.Dc).2.2 +
      lS.length := by rw [← hus1']; exact hus2
  have hcap2 : r2.cap = st.cap := hU2.cap.trans hcap1
  have hwa2 : ∀ a, a ∈ spArrs → a ∉ slotW → r2.wa a = st.wa a ∧ r2.wlen a = st.wlen a := fun a ha hs => by
    have e1 := hU1.warr a (hwa1 a ha hs)
    have e2 := hU2.warr a (fun h => DL.dWA_ok a h ha)
    exact ⟨e2.1.trans e1.1, e2.2.trans e1.2⟩
  have hWr2 : RowRep r2 "W" "W.len" G.n (l + 1) (vals wl) :=
    RamLevel.RowRep.of_eq hW (hwa2 "W" (by decide) (by decide)).2 (hwa2 "W.len" (by decide) (by decide)).2
      (by rw [(hwa2 "W.len" (by decide) (by decide)).1]) (fun i _ => by rw [(hwa2 "W" (by decide) (by decide)).1])
  have hUr2 : RowRep r2 "U" "U.len" G.n (l + 1) (vals lU) :=
    RamLevel.RowRep.of_eq hUr (hwa2 "U" (by decide) (by decide)).2 (hwa2 "U.len" (by decide) (by decide)).2
      (by rw [(hwa2 "U.len" (by decide) (by decide)).1]) (fun i _ => by rw [(hwa2 "U" (by decide) (by decide)).1])
  have hinU2 : ∀ x < G.n, r2.wa "sp.inU" ((l + 1) * G.n + x) = if x ∈ vals lU then 1 else 0 := by
    intro x hx
    rw [(hwa2 "sp.inU" (by decide) (by decide)).1]
    have := hinU ⟨x, hx⟩
    simp only [Fin.val_mk] at this
    rw [this]
    have e : (⟨x, hx⟩ : Fin G.n) ∈ c.cs.U ↔ x ∈ vals lU := by
      rw [← hlUset, List.mem_toFinset]
      simp only [vals, List.mem_map]
      exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨y, hy, e⟩ => by rw [show (⟨x, hx⟩ : Fin G.n) = y from Fin.ext e.symm]; exact hy⟩
    by_cases h : (⟨x, hx⟩ : Fin G.n) ∈ c.cs.U
    · rw [if_pos h, if_pos (e.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (e.mpr h'))]
  have hrowc : ∀ a ∈ rowArrs, a ∈ spArrs ∧ a ∉ slotW := by decide
  have hlenc : ∀ a ∈ lenArrs, a ∈ spArrs ∧ a ∉ slotW := by decide
  have hstatW : ∀ a ∈ rowArrs, (LF + 2) * G.n ≤ r2.wlen a := fun a ha => by
    rw [(hwa2 a (hrowc a ha).1 (hrowc a ha).2).2]
    exact hstat.rows a ha
  have hWpl2 : (l + 1 + 1) * G.n ≤ r2.wlen "Wp" := by
    have e1 := hU1.warr "Wp" (fun h => by
      rcases List.mem_append.mp h with h | h
      · exact hN.dA _ h (by simp)
      · simp [slotW] at h)
    have e2 := hU2.warr "Wp" (fun h => hN.dA _ h (by simp))
    rw [e2.2, e1.2]; exact hWp.1
  have hWpll2 : l + 1 < r2.wlen "Wp.len" := by
    have e1 := hU1.warr "Wp.len" (fun h => by
      rcases List.mem_append.mp h with h | h
      · exact hN.dA _ h (by simp)
      · simp [slotW] at h)
    have e2 := hU2.warr "Wp.len" (fun h => hN.dA _ h (by simp))
    rw [e2.2, e1.2]; exact hWp.2
  -- 3. BM.26
  refine runs_seq ((wp_spec DL hN.dA r2 H Ds (l + 1) c.cs.d c0 B B'f g2 D2 ⟨hD2', hL2, hl2, hn2', hE2⟩
    hwnd hlUnd hWr2 hUr2 hinU2 hWpl2 hWpll2 (le_trans (Nat.mul_le_mul_right _ (by omega))
      (hstatW "sp.inU" (by simp [rowArrs]))) (by rw [hcap2]; omega) hTW hFR).mono ?_)
  rintro r3 ⟨hWI, ⟨hD3, hL3, hl3, hn3, hB3, hBp3, hsl3, hslp3, hc43, -⟩, hU3, hc3l, hc3, hwl3, hvl3⟩
  have hcap3 : r3.cap = st.cap := hU3.cap.trans hcap2
  have hWp3 : RowRep r3 "Wp" "Wp.len" G.n (l + 1) (lW'.map Fin.val) := by
    have := hWI.wp; rw [List.take_length] at this; exact this
  have hus3 : DL.use r3 = DL.use r2 := DL.use_frame r2 r3 _ _ _ _ hU3 (fun a ha h => by
    rcases List.mem_append.mp h with h | h
    · exact hFR a ha h
    · exact hTW a ha h)
  -- the frames of the graph through phases 1–3
  have hgw : ∀ (x y : State ℝ≥0) (wa va wr vr : List String), Unchanged x y wa va wr vr →
      "gHead" ∉ wa → "gW" ∉ va → "gSt" ∉ wa → GraphAt x G → CSRAt x G → GraphAt y G ∧ CSRAt y G :=
    fun x y wa va wr vr hU h1 h2 h3 hg hc => ⟨graphAt_of_unchanged hU h1 h2 hg, hc.of_unchanged hU h3⟩
  have hnotA : ∀ a ∈ ["gHead", "gSt"], a ∉ DL.dWA := fun a ha h => DL.dWA_ok a h (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl <;> decide)
  obtain ⟨hgr1, hcsr1⟩ := hgw st r1 _ _ _ _ hU1
    (fun h => by rcases List.mem_append.mp h with h | h
                 · exact hnotA "gHead" (by simp) h
                 · simp [slotW] at h)
    (fun h => by rcases List.mem_append.mp h with h | h
                 · exact hgW h
                 · simp at h)
    (fun h => by rcases List.mem_append.mp h with h | h
                 · exact hnotA "gSt" (by simp) h
                 · simp [slotW] at h) hstat.graph hstat.csr
  obtain ⟨hgr2, hcsr2⟩ := hgw r1 r2 _ _ _ _ hU2 (hnotA "gHead" (by simp)) hgW (hnotA "gSt" (by simp)) hgr1 hcsr1
  obtain ⟨hgr3, hcsr3⟩ := hgw r2 r3 _ _ _ _ hU3 (by decide) (by simp) (by decide) hgr2 hcsr2
  -- names for `relW_spec`
  have hWd : "Wp" ∉ DI.dWA ∧ "Wp.len" ∉ DI.dWA :=
    ⟨fun h => hN.dA _ h (by simp), fun h => hN.dA _ h (by simp)⟩
  have hKd : ∀ a ∈ ["rw.bl", "rw.bh", "rw.bv", "rw.be", "rw.br", "rw.bf", "rw.ll", "rw.lh", "rw.lv",
      "rw.le", "rw.lr", "rw.lf", "sl.i"], a ∉ DI.dWR := by
    intro a ha h
    by_cases hsl : a = "sl.i"
    · subst hsl; exact DL.dWR_ok _ h (by decide)
    · refine hdR a h (List.mem_append_right _ ?_)
      simp only [relWRegs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
      tauto
  have hKdl : "rw.bl" ∉ DI.dVR ∧ "rw.ll" ∉ DI.dVR :=
    ⟨fun h => hN.dV _ h (by simp [finVRegs]), fun h => hN.dV _ h (by simp [finVRegs])⟩
  -- Layer A: W' is complete; the block count; the budgets
  have hcomp : ∀ u ∈ lW', c.cs.d u = dis (s := s) u ∧ c.cs.d u ≠ ⊤ := fun u hu => by
    obtain ⟨⟨h1, h2⟩, h3⟩ := (hlW'mem u).mp hu
    exact ⟨hW'c u h1 h2 h3, _root_.ne_top_of_lt h3⟩
  have hnb0 : c.cs.Dc.blocks.length ≤ DL.NB := by
    have := DL.nb_le st H c.cs.g (Function.update Ds (l + 1) c.cs.Dc) (l + 1) hD (l + 1) le_rfl
    rwa [Function.update_self] at this
  have hnb2 : D2.blocks.length ≤ DL.NB := by rw [hD2def, insManyC_blocks]; exact hnb0
  have hI6 : (BM.insManyC (dlOps G s) (T (l + 1)) c.cs.d lT6 c.cs.g c.cs.Dc).2.2 ≤
      lT6.length * (Nat.log 2 DL.NB + 4) := insManyC_cost_le _ _ _ _ _ _ hnb0
  have hlT6l : lT6.length ≤ lS.length := by rw [hlT6]; exact List.length_filter_le _ _
  have hlW'l : lW'.length ≤ W.card := by
    rw [← hwset, List.toFinset_card_of_nodup hwnd, hlW']; exact List.length_filter_le _ _
  have hwll : wl.length = W.card := by rw [← hwset, List.toFinset_card_of_nodup hwnd]
  have hCED : CED DL.K D2.blocks.length ≤ CED DL.K DL.NB := by
    unfold CED
    have := Nat.log_mono_right (b := 2) hnb2
    have := Nat.mul_le_mul_left DL.K (show Nat.log 2 D2.blocks.length + 5 ≤ Nat.log 2 DL.NB + 5 by omega)
    omega
  have hbudW : r3.cost + 30 + (lW'.length + 1) * ((G.m + 1) * CED DI.K D2.blocks.length + 101) ≤
      c0 + r3.cap := by
    rw [hcap3]
    have e1 : (lW'.length + 1) * ((G.m + 1) * CED DI.K D2.blocks.length + 101) ≤
        (W.card + 1) * ((G.m + 1) * CED DL.K DL.NB + 101) :=
      Nat.mul_le_mul (by omega) (by
        have := Nat.mul_le_mul_left (G.m + 1) hCED; show (G.m + 1) * CED DL.K _ + 101 ≤ _; omega)
    have e2 : DL.K * (BM.insManyC (dlOps G s) (T (l + 1)) c.cs.d lT6 c.cs.g c.cs.Dc).2.2 ≤
        DL.K * (S.card * (Nat.log 2 DL.NB + 4)) := Nat.mul_le_mul_left _ (by
      have := Nat.mul_le_mul_right (Nat.log 2 DL.NB + 4) (show lT6.length ≤ S.card by omega); omega)
    have e3 : lS.length * (59 + DL.K + 6) ≤ S.card * Kfin DL.K := by
      rw [hlSl]; exact Nat.mul_le_mul_left _ (by unfold Kfin; omega)
    have e4 : wl.length * (29 + 16) ≤ W.card * Kfin DL.K := by
      rw [hwll]; exact Nat.mul_le_mul_left _ (by unfold Kfin; omega)
    have e5 : Kfin DL.K * (1 + S.card + W.card) = Kfin DL.K + S.card * Kfin DL.K + W.card * Kfin DL.K := by
      ring
    have e6 : DL.K + 16 + 2 + 3 + 30 ≤ Kfin DL.K := by unfold Kfin; omega
    omega
  have hUse3 : ∀ L : List (Fin G.m), Enumerates G L lW'.toFinset →
      DI.use r3 + (L.foldl (relaxInsCc (dlOps G s) (T (l + 1)) B (some B'f)) ⟨c.cs.d, g2, D2, 0⟩).c ≤
        DI.ucap := by
    intro L hL
    have h1 := hUse lT6 L lW' hlT6nd hlT6mem hlW'nd hlW'mem hL
    have h2 : (BM.insManyC (dlOps G s) (T (l + 1)) c.cs.d lT6 c.cs.g c.cs.Dc).2.2 +
        (L.foldl (relaxInsCc (dlOps G s) (T (l + 1)) B (some B'f)) ⟨c.cs.d, g2, D2, 0⟩).c ≤
        (finD (dlOps G s) (T (l + 1)) B B'f c.cs.d c.cs.g c.cs.Dc lT6 L lW').2.2.2 := by
      rw [hg2, hD2def]; unfold finD; dsimp only; omega
    show DL.use r3 + _ ≤ DL.ucap
    rw [hus3]; omega
  -- 4. BM.27–28
  refine runs_seq ((relW_spec DI hsort hWd hKd hKdl r3 (l + 1) B B'f c.cs.d g2 D2 Ds H c0 lW' hl3 hn3 hL3
    hwalk hD3 hWp3 hlW'nd hB3 hBp3 ⟨hsl3, hslp3⟩ hcomp hgr3 hcsr3
    (by rw [hwl3, hwl2, hwl1]; exact hstat.ptr) (by rw [hcap3]; omega) (by rw [hcap3]; omega)
    (by rw [hcap3]; omega) (by rw [hcap3]; exact hc4) hbudW
    (by rw [hD2def, insManyC_Bd]; exact hBd) hUse3).mono ?_)
  rintro r4 ⟨L, H', hEnum, hL4, hext4, hD4, hPtr4, hfr4, hU4, hwl4, hvl4, hc4l, hc4, hus4⟩
  set F := L.foldl (relaxInsCc (dlOps G s) (T (l + 1)) B (some B'f)) ⟨c.cs.d, g2, D2, 0⟩ with hF
  have hcap4 : r4.cap = st.cap := hU4.cap.trans hcap3
  have hreg4c : ∀ a ∈ ["lvl", "n", "gN", "core.n", "core.s", "core.m", "hp_n"],
      a ∉ relWRegs ∧ a ∈ spRegs := by decide
  have hreg4 : ∀ a ∈ ["lvl", "n", "gN", "core.n", "core.s", "core.m", "hp_n"], a ∉ relWRegs ++ DI.dWR := by
    intro a ha h
    rcases List.mem_append.mp h with h | h
    · exact (hreg4c a ha).1 h
    · exact DL.dWR_ok a h (hreg4c a ha).2
  have hl4 : r4.w "lvl" = l + 1 := by rw [hU4.wreg _ (hreg4 _ (by simp))]; exact hl3
  have hn4 : r4.w "n" = G.n := by rw [hU4.wreg _ (hreg4 _ (by simp))]; exact hn3
  have hwp4c : ∀ a ∈ ["Wp", "Wp.len"], a ∉ labW ∧ a ∉ ["sp.ptr"] := by decide
  have hwp4 : ∀ a ∈ ["Wp", "Wp.len"], a ∉ labW ++ DI.dWA ++ ["sp.ptr"] := by
    intro a ha h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact (hwp4c a ha).1 h
      · exact hN.dA a h ha
    · exact (hwp4c a ha).2 h
  have hWp4 : RowRep r4 "Wp" "Wp.len" G.n (l + 1) (lW'.map Fin.val) :=
    RamLevel.RowRep.of_eq hWp3 (hU4.warr "Wp" (hwp4 _ (by simp))).2 (hU4.warr "Wp.len" (hwp4 _ (by simp))).2
      (by rw [(hU4.warr "Wp.len" (hwp4 _ (by simp))).1]) (fun i _ => by rw [(hU4.warr "Wp" (hwp4 _ (by simp))).1])
  -- 5. BM.29
  refine runs_seq ((hDel r4 H' F.g (Function.update Ds (l + 1) F.Dc) (l + 1) lW' hD4 hl4 hn4 hWp4).mono ?_)
  rintro r5 ⟨hD5, hU5, hwl5, hvl5, hc5l, hc5, hus5⟩
  have hcap5 : r5.cap = st.cap := hU5.cap.trans hcap4
  have hl5 : r5.w "lvl" = l + 1 := by rw [hU5.wreg _ (fun h => DL.dWR_ok _ h (by decide))]; exact hl4
  have hn5 : r5.w "n" = G.n := by rw [hU5.wreg _ (fun h => DL.dWR_ok _ h (by decide))]; exact hn4
  -- the rows at `r5`
  have hwaS : ∀ a, a ∈ spArrs → a ∉ slotW → a ∉ wpArrs → a ∉ labW → a ≠ "sp.ptr" →
      r5.wa a = st.wa a ∧ r5.wlen a = st.wlen a := fun a ha hs hw hl hp => by
    have e2 := hwa2 a ha hs
    have e3 := hU3.warr a hw
    have e4 := hU4.warr a (fun h => by
      rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · exact hl h
        · exact DL.dWA_ok a h ha
      · exact hp (List.mem_singleton.mp h))
    have e5 := hU5.warr a (fun h => DL.dWA_ok a h ha)
    exact ⟨e5.1.trans (e4.1.trans (e3.1.trans e2.1)), e5.2.trans (e4.2.trans (e3.2.trans e2.2))⟩
  have hS5 : RowRep r5 "S" "S.len" G.n (l + 1) (lS.map Fin.val) :=
    RamLevel.RowRep.of_eq hSr (hwaS "S" (by decide) (by decide) (by decide) (by decide) (by decide)).2
      (hwaS "S.len" (by decide) (by decide) (by decide) (by decide) (by decide)).2
      (by rw [(hwaS "S.len" (by decide) (by decide) (by decide) (by decide) (by decide)).1])
      (fun i _ => by rw [(hwaS "S" (by decide) (by decide) (by decide) (by decide) (by decide)).1])
  have hwU45c : ∀ a ∈ ["U", "U.len", "sp.inU", "sp.g"], a ∈ spArrs ∧ a ∉ labW ∧ a ∉ ["sp.ptr"] := by
    decide
  have hwU45 : ∀ a ∈ ["U", "U.len", "sp.inU", "sp.g"], r5.wa a = r3.wa a ∧ r5.wlen a = r3.wlen a := by
    intro a ha
    have hsp : a ∈ spArrs := (hwU45c a ha).1
    have e4 := hU4.warr a (fun h => by
      rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · exact (hwU45c a ha).2.1 h
        · exact DL.dWA_ok a h hsp
      · exact (hwU45c a ha).2.2 h)
    have e5 := hU5.warr a (fun h => DL.dWA_ok a h hsp)
    exact ⟨e5.1.trans e4.1, e5.2.trans e4.2⟩
  have hUrow5 : RowRep r5 "U" "U.len" G.n (l + 1) (vals (lU ++ lW')) := by
    have := hWI.u; rw [List.take_length] at this
    exact RamLevel.RowRep.of_eq this (hwU45 "U" (by simp)).2 (hwU45 "U.len" (by simp)).2
      (by rw [(hwU45 "U.len" (by simp)).1]) (fun i _ => by rw [(hwU45 "U" (by simp)).1])
  have hwl5A : r5.wlen = st.wlen := hwl5.trans (hwl4.trans (hwl3.trans (hwl2.trans hwl1)))
  have hvl5A : r5.vlen = st.vlen := hvl5.trans (hvl4.trans (hvl3.trans (hvl2.trans hvl1)))
  -- 6. BM.30–31
  refine ((clears_spec r5 (lv := l + 1) hS5 hUrow5 hl5 hn5
    (fun x hx => by obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx; exact u.isLt)
    (fun y hy => by obtain ⟨u, -, rfl⟩ := List.mem_map.mp hy; exact u.isLt)
    (by rw [hwl5A]; exact le_trans (Nat.mul_le_mul_right _ (by omega)) (hstat.rows "sp.g" (by simp [rowArrs])))
    (by rw [hwl5A]; exact le_trans (Nat.mul_le_mul_right _ (by omega)) (hstat.rows "sp.inU" (by simp [rowArrs])))
    (by rw [hcap5]; omega)).mono ?_)
  rintro r ⟨hz1, hz2, hU6, hwl6, hvl6, hc6⟩
  -- frames of the last two phases and the whole run
  have hwa56 : ∀ a, a ∉ DL.dWA → a ∉ ["sp.g", "sp.inU"] → r.wa a = r4.wa a ∧ r.wlen a = r4.wlen a :=
    fun a h1 h2 => by
      have e5 := hU5.warr a h1
      have e6 := hU6.warr a h2
      exact ⟨e6.1.trans e5.1, e6.2.trans e5.2⟩
  have hwaR : ∀ a, a ∈ spArrs → a ∉ slotW → a ∉ wpArrs → a ∉ labW → a ≠ "sp.ptr" →
      a ∉ ["sp.g", "sp.inU"] → r.wa a = st.wa a ∧ r.wlen a = st.wlen a := fun a ha hs hw hl hp hg => by
    have e5 := hwaS a ha hs hw hl hp
    have e6 := hU6.warr a hg
    exact ⟨e6.1.trans e5.1, e6.2.trans e5.2⟩
  have hvcr : vc (G := G) r = vc r4 := by
    rw [vc_of_unchanged hU6 (by decide), vc_of_unchanged hU5 (dl_vcnt DL)]
  have hvc3 : vc (G := G) r3 = vc st := by
    rw [vc_of_unchanged hU3 (by decide), vc_of_unchanged hU2 (dl_vcnt DL), hvc1]
  have hcapr : r.cap = st.cap := hU6.cap.trans hcap5
  have hwlR : r.wlen = st.wlen := hwl6.trans hwl5A
  have hvlR : r.vlen = st.vlen := hvl6.trans hvl5A
  have hrz : "rz.i" ∉ DL.dWR := fun h => hdR _ h (by simp)
  have hU56 := hU5.comp hU6
  have hlW'U : ∀ x ∈ lW', x ∉ lU := fun x hx hu => by
    have := ((hlW'mem x).mp hx).1.2
    exact this (by rw [← hlUset, List.mem_toFinset]; exact hu)
  -- the registers through the whole run
  have hzc : ∀ z ∈ ["lvl", "n", "gN", "core.n", "core.s", "core.m", "hp_n"], z ∉ t6Regs ∧ z ∉ tstW ∧
      z ∉ ["sp.em"] ∧ z ∉ ("sl.i" :: "f24.kf" :: K24.ws) ∧ z ∉ ["rz.i"] ∧ z ∈ spRegs := by decide
  have hregR : ∀ z ∈ ["lvl", "n", "gN", "core.n", "core.s", "core.m", "hp_n"], r.w z = st.w z := by
    intro z hz
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hzc z hz
    have h3 : z ∉ t6Regs ++ tstW := fun h => by
      rcases List.mem_append.mp h with h | h
      · exact c1 h
      · exact c2 h
    have h2 : z ∉ t6Regs ++ tstW ++ DL.dWR := fun h => by
      rcases List.mem_append.mp h with h | h
      · exact h3 h
      · exact DL.dWR_ok z h c6
    have h1 : z ∉ DL.dWR ++ ["sp.em"] ++ ("sl.i" :: "f24.kf" :: K24.ws) := fun h => by
      rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · exact DL.dWR_ok z h c6
        · exact c3 h
      · exact c4 h
    rw [hU6.wreg z c5, hU5.wreg z (fun h => DL.dWR_ok z h c6), hU4.wreg z (hreg4 z hz), hU3.wreg z h3,
      hU2.wreg z h2, hU1.wreg z h1]
  refine ⟨lT6, lW'.toFinset, lW', L, H', ?_⟩
  -- the `D`-layer frame of the clears
  have hD6 : DL.DR r H' (delC F.g lW').1 (Function.update Ds (l + 1) F.Dc) (l + 1) :=
    DL.frame r5 r H' H' _ _ _ _ _ _ _ hD5 hU6
      (fun a ha h => DL.dWA_ok a ha (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> decide))
      (fun a _ h => by simp at h)
      (fun a ha h => by rw [List.mem_singleton] at h; subst h; exact hrz ha)
      (by rw [vc_of_unchanged hU6 (by decide)]; exact HExt.refl _ _)
  -- phi through all phases
  have hPf : ∀ (x y : State ℝ≥0) (wa va wr vr : List String), Unchanged x y wa va wr vr →
      (∀ a ∈ wa, a ∈ spArrs ++ ["Wp", "Wp.len"] ++ DL.dWA) →
      (∀ a ∈ wr, a ∈ finRegs ++ spRegs ++ DL.dWR) → PI.PhiR x c.φ → PI.PhiR y c.φ :=
    fun x y wa va wr vr hU hA hR hp => PI.frame x y c.φ wa va wr vr hp hU
      (fun a ha h => hN.pA a ha (hA a h)) (fun a ha h => hN.pR a ha (hR a h))
  have mA : ∀ a ∈ spArrs, a ∈ spArrs ++ ["Wp", "Wp.len"] ++ DL.dWA := fun a ha =>
    List.mem_append_left _ (List.mem_append_left _ ha)
  have mAd : ∀ a ∈ DL.dWA, a ∈ spArrs ++ ["Wp", "Wp.len"] ++ DL.dWA := fun a ha => List.mem_append_right _ ha
  have mR : ∀ a ∈ spRegs, a ∈ finRegs ++ spRegs ++ DL.dWR := fun a ha =>
    List.mem_append_left _ (List.mem_append_right _ ha)
  have mRf : ∀ a ∈ finRegs, a ∈ finRegs ++ spRegs ++ DL.dWR := fun a ha =>
    List.mem_append_left _ (List.mem_append_left _ ha)
  have mRd : ∀ a ∈ DL.dWR, a ∈ finRegs ++ spRegs ++ DL.dWR := fun a ha => List.mem_append_right _ ha
  have cSlot : ∀ a ∈ slotW, a ∈ spArrs := by decide
  have cWp : ∀ a ∈ wpArrs, a ∈ spArrs := by decide
  have cLab : ∀ a ∈ labW ++ ["sp.ptr"], a ∈ spArrs := by decide
  have cGI : ∀ a ∈ ["sp.g", "sp.inU"], a ∈ spArrs := by decide
  have cT6 : ∀ a ∈ t6Regs ++ tstW, a ∈ finRegs ∨ a ∈ spRegs := by decide
  have cR1 : ∀ a ∈ ["sp.em"] ++ ("sl.i" :: "f24.kf" :: K24.ws), a ∈ finRegs ∨ a ∈ spRegs := by decide
  have cRW : ∀ a ∈ relWRegs, a ∈ finRegs := by decide
  have hphiR : PI.PhiR r c.φ := by
    refine hPf r5 r _ _ _ _ hU6 (fun a ha => mA a (cGI a ha)) (fun a ha => by
      rw [List.mem_singleton] at ha; subst ha; exact mRf _ (by decide)) ?_
    refine hPf r4 r5 _ _ _ _ hU5 mAd mRd ?_
    refine hPf r3 r4 _ _ _ _ hU4 (fun a ha => by
      rcases List.mem_append.mp ha with h | h
      · rcases List.mem_append.mp h with h | h
        · exact mA a (cLab a (List.mem_append_left _ h))
        · exact mAd a h
      · exact mA a (cLab a (List.mem_append_right _ h)))
      (fun a ha => by
        rcases List.mem_append.mp ha with h | h
        · exact mRf a (cRW a h)
        · exact mRd a h) ?_
    refine hPf r2 r3 _ _ _ _ hU3 (fun a ha => mA a (cWp a ha))
      (fun a ha => by rcases cT6 a ha with h | h; exact mRf a h; exact mR a h) ?_
    refine hPf r1 r2 _ _ _ _ hU2 mAd (fun a ha => by
      rcases List.mem_append.mp ha with h | h
      · rcases cT6 a h with h | h; exact mRf a h; exact mR a h
      · exact mRd a h) ?_
    refine hPf st r1 _ _ _ _ hU1 (fun a ha => by
      rcases List.mem_append.mp ha with h | h
      · exact mAd a h
      · exact mA a (cSlot a h))
      (fun a ha => by
        rcases List.mem_append.mp ha with h | h
        · rcases List.mem_append.mp h with h | h
          · exact mRd a h
          · rcases cR1 a (List.mem_append_left _ h) with h | h; exact mRf a h; exact mR a h
        · rcases cR1 a (List.mem_append_right _ h) with h | h; exact mRf a h; exact mR a h) hphi
  -- labels, pointers and the static arrays at `r`
  have hLr : LabAt r F.d H' c0 :=
    (hL4.of_unchanged hU5 (dl_labW DL) (dl_dlen DL) hc5l).of_unchanged hU6 (by decide) (by simp)
      (by rw [hc6]; omega)
  have hstc : ∀ a ∈ ["gSt", "gHead", "cp.tau", "cp.M", "gKeep", "gRep", "hp_P", "sp.xm"],
      a ∈ spArrs ∧ a ∉ slotW ∧ a ∉ wpArrs ∧ a ∉ labW ∧ a ≠ "sp.ptr" ∧ a ∉ ["sp.g", "sp.inU"] := by decide
  have hwst : ∀ a ∈ ["gSt", "gHead", "cp.tau", "cp.M", "gKeep", "gRep", "hp_P", "sp.xm"],
      r.wa a = st.wa a := fun a ha => by
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hstc a ha
    exact (hwaR a c1 c2 c3 c4 c5 c6).1
  have hgS : r.wa "gSt" = st.wa "gSt" := hwst "gSt" (by simp)
  have hgS4 : r.wa "gSt" = r4.wa "gSt" := (hwa56 "gSt" (fun h => DL.dWA_ok _ h (by decide)) (by decide)).1
  have hsp4 : r.wa "sp.ptr" = r4.wa "sp.ptr" :=
    (hwa56 "sp.ptr" (fun h => DL.dWA_ok _ h (by decide)) (by decide)).1
  have hsp3 : r3.wa "sp.ptr" = st.wa "sp.ptr" := by
    rw [(hU3.warr "sp.ptr" (by decide)).1, (hU2.warr "sp.ptr" (fun h => DL.dWA_ok _ h (by decide))).1,
      (hU1.warr "sp.ptr" (hwa1 _ (by decide) (by decide))).1]
  have hptrF : ∀ x : Fin G.n, x ∉ lW' → r.wa "sp.ptr" x = st.wa "sp.ptr" x := fun x hx => by
    rw [hsp4, hfr4 x hx, hsp3]
  -- the finD cost
  have hfeq : (finD (dlOps G s) (T (l + 1)) B B'f c.cs.d c.cs.g c.cs.Dc lT6 L lW').2.2.2 =
      (BM.insManyC (dlOps G s) (T (l + 1)) c.cs.d lT6 c.cs.g c.cs.Dc).2.2 + F.c + (delC F.g lW').2 := by
    rw [hF, hg2, hD2def]; unfold finD; rfl
  have hlUl : lU.length = c.cs.U.card := by rw [← hlUset, List.toFinset_card_of_nodup hlUnd]
  have hlW'l2 : lW'.toFinset.card = lW'.length := List.toFinset_card_of_nodup hlW'nd
  refine
    { t6nd := hlT6nd
      t6mem := hlT6mem
      wmem := fun x => by rw [List.mem_toFinset]; exact hlW'mem x
      enum := hEnum
      wnd := hlW'nd
      wset := rfl
      lab := hLr
      hext := by rw [hvcr]; rw [hvc3] at hext4; exact hext4
      D := hD6
      phi := hphiR
      U := ?_
      sBp := ?_
      ptr := ?_
      ptrFr := fun x hx => hptrF x (fun h => hx (List.mem_toFinset.mpr h))
      clr := ?_
      above := ?_
      stArr := fun a ha => hwst a (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha ⊢; tauto)
      stat := ?_
      lvl := by rw [hregR "lvl" (by simp)]; exact hlvl
      cost1 := by rw [hc6]; omega
      cost2 := ?_
      use := ?_ }
  · -- U
    have hUr6 : RowRep r "U" "U.len" G.n (l + 1) ((lU ++ lW').map Fin.val) :=
      RamLevel.RowRep.of_eq hUrow5 (hU6.warr "U" (by decide)).2 (hU6.warr "U.len" (by decide)).2
        (by rw [(hU6.warr "U.len" (by decide)).1]) (fun i _ => by rw [(hU6.warr "U" (by decide)).1])
    have hnd : (lU ++ lW').Nodup :=
      List.nodup_append.mpr ⟨hlUnd, hlW'nd, fun x hx y hy hxy => hlW'U y hy (hxy ▸ hx)⟩
    have := SetRow.ofList hUr6 hnd
    rwa [List.toFinset_append, hlUset] at this
  · -- sBp
    have h4 : SlotHolds r4 (slotBp (l + 1)) H (vc r3) B'f := hBp3.of_unchanged hU4 (fun a ha h => by
        rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with h | h
          · exact (by decide : ∀ a ∈ slotW, a ∉ labW) a ha h
          · exact DL.dWA_ok a h (cSlot a ha)
        · exact (by decide : ∀ a ∈ slotW, a ∉ ["sp.ptr"]) a ha h)
      (fun h => by
        rcases List.mem_append.mp h with h | h
        · simp [labV] at h
        · exact DL.dVA_ok _ h (by simp))
    have h4' := h4.ext hext4
    rw [hvcr]
    exact (h4'.of_unchanged hU5 (fun a ha h => DL.dWA_ok a h (cSlot a ha))
      (fun h => DL.dVA_ok _ h (by simp))).of_unchanged hU6
      (fun a ha h => (by decide : ∀ a ∈ slotW, a ∉ ["sp.g", "sp.inU"]) a ha h) (by simp)
  · -- ptr
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · have hu' : u ∉ lW' := fun h => hlW'U u h (by rw [← hlUset] at hu; exact List.mem_toFinset.mp hu)
      have hd : F.d u = c.cs.d u := bodyA_fold_d L ⟨c.cs.d, g2, D2, 0⟩ hwalk u (hUc u hu)
      exact ptrOK_congr (hptr u hu) hgS (hptrF u hu') hd
    · have hu' : u ∈ lW' := List.mem_toFinset.mp hu
      have := RamSpine.PtrAt.of_eq (hPtr4 u hu') hgS4 (by rw [hsp4])
      exact this
  · -- clr
    have hinU3 := hWI.inU
    simp only [List.take_length] at hinU3
    refine ⟨fun l' hl' x hx => ?_, fun l' hl' x hx => ?_, fun x hx => ?_⟩
    · rw [hz1]
      split_ifs with h
      · rfl
      · rw [(hwaS "sp.g" (by decide) (by decide) (by decide) (by decide) (by decide)).1]
        by_cases hll : l' ≤ l
        · exact hclr.g l' (by omega) x hx
        · have hl'e : l' = l + 1 := by omega
          subst hl'e
          rcases hgrp.nomemb x hx with h0 | ⟨j, hj, -, hxj⟩
          · exact h0
          · exfalso; apply h
            obtain ⟨u, huP, hux⟩ := (mem_liftP c.cs.P ⟨j, hj⟩ x).mp hxj
            refine ⟨x, ?_, rfl⟩
            rw [← hux]
            exact List.mem_map_of_mem (List.mem_toFinset.mp (by rw [hlSset]; exact hPS _ u huP))
    · rw [hz2]
      split_ifs with h
      · rfl
      · rw [(hwU45 "sp.inU" (by simp)).1]
        by_cases hll : l' ≤ l
        · have hi : l' * G.n + x < (l + 1) * G.n := by
            have : (l' + 1) * G.n ≤ (l + 1) * G.n := Nat.mul_le_mul_right _ (by omega)
            rw [Nat.succ_mul] at this; omega
          rw [hWI.rows "sp.inU" (by simp) _ (Or.inl hi), (hwa2 "sp.inU" (by decide) (by decide)).1]
          exact hclr.inU l' (by omega) x hx
        · have hl'e : l' = l + 1 := by omega
          subst hl'e
          rw [hinU3 x hx, if_neg]
          intro hm; exact h ⟨x, hm, rfl⟩
    · rw [hwst "sp.xm" (by simp)]; exact hclr.xm x hx
  · -- above
    have hrowc2 : ∀ a ∈ rowArrs, a ∉ ["U", "sp.inU", "Wp", "sp.g"] →
        a ∈ spArrs ∧ a ∉ slotW ∧ a ∉ wpArrs ∧ a ∉ labW ∧ a ≠ "sp.ptr" ∧ a ∉ ["sp.g", "sp.inU"] := by
      decide
    have hlenc2 : ∀ a ∈ lenArrs, a ∉ ["U.len", "Wp.len"] →
        a ∈ spArrs ∧ a ∉ slotW ∧ a ∉ wpArrs ∧ a ∉ labW ∧ a ≠ "sp.ptr" ∧ a ∉ ["sp.g", "sp.inU"] := by
      decide
    have hWpc : ∀ a ∈ ["Wp", "Wp.len"], a ∉ ["sp.g", "sp.inU"] ∧ a ∉ slotW := by decide
    have hWp45 : ∀ a ∈ ["Wp", "Wp.len"], r.wa a = r3.wa a := fun a ha => by
      rw [(hU6.warr a (hWpc a ha).1).1, (hU5.warr a (fun h => hN.dA a h ha)).1, (hU4.warr a (hwp4 a ha)).1]
    have hWp12 : ∀ a ∈ ["Wp", "Wp.len"], r2.wa a = st.wa a := fun a ha => by
      rw [(hU2.warr a (fun h => hN.dA a h ha)).1, (hU1.warr a (fun h => by
        rcases List.mem_append.mp h with h | h
        · exact hN.dA a h ha
        · exact (hWpc a ha).2 h)).1]
    have hn2' : (l + 1 + 1) * G.n = (l + 1) * G.n + G.n := Nat.succ_mul _ _
    refine ⟨fun a ha i hi => ?_, fun a ha j hj => ?_, fun i hi => ?_, hwlR, hvlR⟩
    · have hi' : (l + 1 + 1) * G.n ≤ i := hi
      by_cases hA : a ∈ ["U", "sp.inU", "Wp", "sp.g"]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
        rcases hA with rfl | rfl | rfl | rfl
        · rw [(hU6.warr "U" (by decide)).1, (hwU45 "U" (by simp)).1, hWI.rows "U" (by simp) i (Or.inr hi'),
            (hwa2 "U" (by decide) (by decide)).1]
        · rw [hz2, if_neg, (hwU45 "sp.inU" (by simp)).1, hWI.rows "sp.inU" (by simp) i (Or.inr hi'),
            (hwa2 "sp.inU" (by decide) (by decide)).1]
          rintro ⟨y, hy, rfl⟩
          have : y < G.n := by
            obtain ⟨u, -, rfl⟩ := List.mem_map.mp hy; exact u.isLt
          omega
        · rw [hWp45 "Wp" (by simp), hWI.rows "Wp" (by simp) i (Or.inr hi'), hWp12 "Wp" (by simp)]
        · rw [hz1, if_neg, (hwaS "sp.g" (by decide) (by decide) (by decide) (by decide) (by decide)).1]
          rintro ⟨y, hy, rfl⟩
          have : y < G.n := by
            obtain ⟨u, -, rfl⟩ := List.mem_map.mp hy; exact u.isLt
          omega
      · obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hrowc2 a ha hA
        exact congrFun (hwaR a c1 c2 c3 c4 c5 c6).1 i
    · by_cases hA : a ∈ ["U.len", "Wp.len"]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
        rcases hA with rfl | rfl
        · rw [(hU6.warr "U.len" (by decide)).1, (hwU45 "U.len" (by simp)).1,
            hWI.lens "U.len" (by simp) j (by omega), (hwa2 "U.len" (by decide) (by decide)).1]
        · rw [hWp45 "Wp.len" (by simp), hWI.lens "Wp.len" (by simp) j (by omega), hWp12 "Wp.len" (by simp)]
      · obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hlenc2 a ha hA
        exact congrFun (hwaR a c1 c2 c3 c4 c5 c6).1 j
    · have hi2 : i ≠ slotBp (l + 1) := by simp [slotB, slotBp] at hi ⊢; omega
      obtain ⟨e1, e2⟩ := hfr1 i hi2
      have hv26 : r.va "sl.l" = r1.va "sl.l" := by
        rw [(hU6.varr "sl.l" (by simp)).1, (hU5.varr "sl.l" (fun h => DL.dVA_ok _ h (by simp))).1,
          (hU4.varr "sl.l" (fun h => by
            rcases List.mem_append.mp h with h | h
            · simp [labV] at h
            · exact DL.dVA_ok _ h (by simp))).1,
          (hU3.varr "sl.l" (by simp)).1, (hU2.varr "sl.l" (fun h => DL.dVA_ok _ h (by simp))).1]
      have hw26 : ∀ a ∈ slotW, r.wa a = r1.wa a := fun a ha => by
        rw [(hU6.warr a ((by decide : ∀ a ∈ slotW, a ∉ ["sp.g", "sp.inU"]) a ha)).1,
          (hU5.warr a (fun h => DL.dWA_ok a h (cSlot a ha))).1,
          (hU4.warr a (fun h => by
            rcases List.mem_append.mp h with h | h
            · rcases List.mem_append.mp h with h | h
              · exact (by decide : ∀ a ∈ slotW, a ∉ labW) a ha h
              · exact DL.dWA_ok a h (cSlot a ha)
            · exact (by decide : ∀ a ∈ slotW, a ∉ ["sp.ptr"]) a ha h)).1,
          (hU3.warr a ((by decide : ∀ a ∈ slotW, a ∉ wpArrs) a ha)).1,
          (hU2.warr a (fun h => DL.dWA_ok a h (cSlot a ha))).1]
      exact ⟨by rw [hv26]; exact e1, fun a ha => by rw [hw26 a ha]; exact e2 a ha⟩
  · -- stat
    have hgWr : r.va "gW" = st.va "gW" ∧ r.vlen "gW" = st.vlen "gW" := by
      have n1 := hU1.varr "gW" (fun h => by
        rcases List.mem_append.mp h with h | h
        · exact hgW h
        · simp at h)
      have n2 := hU2.varr "gW" hgW
      have n3 := hU3.varr "gW" (by simp)
      have n4 := hU4.varr "gW" (fun h => by
        rcases List.mem_append.mp h with h | h
        · simp [labV] at h
        · exact hgW h)
      have n5 := hU5.varr "gW" hgW
      have n6 := hU6.varr "gW" (by simp)
      exact ⟨n6.1.trans (n5.1.trans (n4.1.trans (n3.1.trans (n2.1.trans n1.1)))),
        n6.2.trans (n5.2.trans (n4.2.trans (n3.2.trans (n2.2.trans n1.2))))⟩
    have hpr : r.procs = st.procs :=
      hU6.procs.trans (hU5.procs.trans (hU4.procs.trans (hU3.procs.trans (hU2.procs.trans hU1.procs))))
    exact static_frame hstat (fun a _ => by rw [hwlR]) (by rw [hvlR])
      (fun a ha => hwst a (by simp only [List.mem_cons, List.not_mem_nil, or_false] at ha ⊢; tauto))
      hgWr.1 hgWr.2 (hregR "n" (by simp)) (hregR "gN" (by simp)) (hregR "hp_n" (by simp)) hpr hcapr
  · -- cost2
    rw [hfeq, hlW'l2]
    have hxsl : (lS.map Fin.val).length = S.card := by rw [List.length_map, hlSl]
    have hysl : (vals (lU ++ lW')).length = c.cs.U.card + lW'.length := by simp [vals, hlUl]
    rw [hxsl, hysl] at hc6
    set I6 := (BM.insManyC (dlOps G s) (T (l + 1)) c.cs.d lT6 c.cs.g c.cs.Dc).2.2 with hI6def
    set Fc := F.c with hFc
    set dc := (delC F.g lW').2 with hdc
    have e2 : lS.length * (59 + DL.K + 6) = 65 * S.card + DL.K * S.card := by rw [hlSl]; ring
    have e3 : wl.length * (29 + 16) = 45 * W.card := by rw [hwll]; ring
    have e4 : (113 + DI.K) * (Fc + 1) = 113 * Fc + DL.K * Fc + 113 + DL.K := by
      show (113 + DL.K) * (Fc + 1) = _; ring
    have e5 : DL.K * (dc + lW'.length + 1) = DL.K * dc + DL.K * lW'.length + DL.K := by ring
    have eK : Kfin DL.K * (1 + S.card + W.card + lW'.length + (I6 + Fc + dc)) =
        3 * DL.K + 300 + 3 * (DL.K * S.card) + 300 * S.card + 3 * (DL.K * W.card) + 300 * W.card +
        3 * (DL.K * lW'.length) + 300 * lW'.length + 3 * (DL.K * I6) + 300 * I6 + 3 * (DL.K * Fc) +
        300 * Fc + 3 * (DL.K * dc) + 300 * dc := by unfold Kfin; ring
    rw [e2] at hc2'; rw [e3] at hc3; rw [e4] at hc4; rw [e5] at hc5
    rw [eK]
    omega
  · -- use
    have hus6 : DL.use r = DL.use r5 := DL.use_frame r5 r _ _ _ _ hU6 (fun a ha h => by
      rw [List.mem_singleton] at h; subst h; exact hrz ha)
    have hus4' : DL.use r4 ≤ DL.use r3 + F.c := hus4
    rw [hfeq, hus6, hus5]
    rw [hus3] at hus4'
    omega

/-- **agent-01's `FinSpecStmt`** (RamBodyFinB) holds: `fin_spec` with its instance hypotheses.  With
`finB_of_finSpec` this is the level body's `FinB` at `Kf = Kfin DL.K`, `C = 100`,
`Cst = finCst G DL.K DL.NB`. -/
theorem fin_spec_stmt (DL : DLayer G s T) (PI : PhiI Φ) (hN : FinNames DL PI) {delW : Stmt}
    (hDel : DelWBU DL delW) (hsort : CSRSorted G s) {LF : ℕ} {body : Stmt} {τ Mf : ℕ → ℕ} :
    FinSpecStmt DL PI LF body τ Mf delW :=
  fun st l B S W wl Ds H c0 _ c => fin_spec DL PI hN hDel hsort st l B S W wl Ds H c0 c

/-- The constant part of the finalization's budget: the T6 insertions and the static worst case of
agent-02's relaxations out of `W'` (for `|S|, |W| ≤ n` and the `D` layer's block capacity `NB`); the
summands of agent-01's `finCst G DL.K DL.NB` in the other order. -/
def finCstDL (DL : DLayer G s T) : ℕ :=
  (G.n + 1) * ((G.m + 1) * CED DL.K DL.NB + 101) + DL.K * (G.n * (Nat.log 2 DL.NB + 4))

/-- **agent-01's `FinB`** for `finProg` directly, at `Kf = Kfin DL.K`, `C = 100`, `Cst = finCstDL DL`
(kept for agent-05's `FinalChk`; `finB_of_finSpec (fin_spec_stmt …)` is the same fact with `finCst`). -/
theorem fin_B (DL : DLayer G s T) (PI : PhiI Φ) (hN : FinNames DL PI) {delW : Stmt}
    (hDel : DelWBU DL delW) (hsort : CSRSorted G s) {LF : ℕ} {body : Stmt} {τ Mf : ℕ → ℕ} (l : ℕ) :
    FinB DL PI LF body τ Mf (finProg DL.empty tstT6 DL.ins tstWp (relW DL.ins) delW) (Kfin DL.K) 100
      (finCstDL DL) l := by
  intro st B S W wl Ds H c0 p c hloop hS hW hwnd hwset hwalk hUc hW'c hPS hBd hbudF hUseF
  have hWp : (l + 2) * G.n ≤ st.wlen "Wp" ∧ l + 1 < st.wlen "Wp.len" := by
    have h1 := hloop.stat.rows "Wp" (by simp [rowArrs])
    have h2 := hloop.stat.lens "Wp.len" (by simp [lenArrs])
    have hl := hloop.lvl_le
    exact ⟨le_trans (Nat.mul_le_mul_right _ (by omega)) h1, by omega⟩
  have hSn : S.card ≤ G.n := by simpa using Finset.card_le_univ S
  have hWn : W.card ≤ G.n := by simpa using Finset.card_le_univ W
  refine fin_spec DL PI hN hDel hsort st l B S W wl Ds H c0 c hloop hS hW hwnd hwset hWp hwalk hUc hW'c
    hPS hBd (fun lT6 L lW' h1 h2 h3 h4 h5 => by
      have := hUseF lT6 L lW' h1 h2 h5 h3 (fun x => by rw [List.mem_toFinset]; exact h4 x)
      omega) ?_
  unfold finCstDL at hbudF
  have e1 : DL.K * (S.card * (Nat.log 2 DL.NB + 4)) ≤ DL.K * (G.n * (Nat.log 2 DL.NB + 4)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hSn)
  have e2 : (W.card + 1) * ((G.m + 1) * CED DL.K DL.NB + 101) ≤
      (G.n + 1) * ((G.m + 1) * CED DL.K DL.NB + 101) := Nat.mul_le_mul_right _ (by omega)
  omega

end Frontier.CHD.RamBody
