import Frontier.CHD.RamBodyA
import Frontier.CHD.IHeapLab

/-!
# Frontier.CHD.RamBodyI — instances of the level body's abstract phase interfaces (owner: agent-01)

**NON-GATE** (B-L4, the spine's level body).
* `dNewI_of` / `dInsI_of`: `RamPiv.DNewI` / `DInsI` from agent-08's `DLayer.new_spec` /
  `DLayer.ins_spec`, for the state predicate `DRl` (the D stack with the level-`lv` structure on
  top, the label table, `lvl`, `n`, and an extra part `E`);
* `tstT6` / `tstWp`: the finalization tests `B'f ≤ d[px] < B` (BM.25) and `d[px] < B'f` (BM.26)
  against the bound slots, with `TestI` instances;
* `cmpI_tt`: `RamInit.CmpI` for the label comparison `cmpLab tt.ra tt.rb lab.bit` (BM.7).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamBody

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.RamLevel
  Frontier.CHD.BM Frontier.CHD.RamBaseCase Frontier.CHD.LabTab Frontier.CHD.RamSpine
  Frontier.CHD.RamInit WExpr Stmt

variable {G : Graph} {s : Fin G.n} {T : ℕ → ℕ}

/-! ## Names of the D layer -/

section names

variable (DL : DLayer G s T)

theorem dl_labW : ∀ a ∈ labW, a ∉ DL.dWA :=
  fun a ha h => DL.dWA_ok a h (by simp only [spArrs, List.mem_append]; exact Or.inr ha)

theorem dl_slotW : ∀ a ∈ slotW, a ∉ DL.dWA :=
  fun a ha h => DL.dWA_ok a h (by simp only [spArrs, List.mem_append]; exact Or.inl (Or.inl (Or.inr ha)))

theorem dl_spArr {a : String} (ha : a ∈ spArrs) : a ∉ DL.dWA := fun h => DL.dWA_ok a h ha

theorem dl_dlen : "dlen" ∉ DL.dVA := fun h => DL.dVA_ok _ h (by simp [labV])

theorem dl_sll : "sl.l" ∉ DL.dVA := fun h => DL.dVA_ok _ h (by simp)

theorem dl_spReg {a : String} (ha : a ∈ spRegs) : a ∉ DL.dWR := fun h => DL.dWR_ok a h ha

theorem dl_vcnt : "vcnt" ∉ DL.dWA := dl_labW DL _ (by simp [labW])

end names

/-! ## The D-layer state predicate of the insertion loops -/

/-- The D stack with the level-`lv` structure `D` on top, the label table (labels `d`, history
`H`, clock `c0`), `lvl = lv`, `n = |V|`, and an extra part `E`. -/
def DRl (DL : DLayer G s T) (H : Hist G) (Ds : ℕ → DStrM G s) (lv : ℕ) (d : Labels G s) (c0 : ℕ)
    (E : State ℝ≥0 → Prop) (st : State ℝ≥0) (g : DGl G s) (D : DStrM G s) : Prop :=
  DL.DR st H g (Function.update Ds lv D) lv ∧ LabAt st d H c0 ∧ st.w "lvl" = lv ∧
    st.w "n" = G.n ∧ E st

section inst

variable (DL : DLayer G s T) (H : Hist G) (Ds : ℕ → DStrM G s) (lv : ℕ) (d : Labels G s) (c0 : ℕ)
  (E : State ℝ≥0 → Prop)

/-- Insertions keep the structure's bound. -/
theorem insManyC_Bd' (T : ℕ) (f : Fin G.n → WLab G s) :
    ∀ (l : List (Fin G.n)) (g : DGl G s) (Dc : DStrM G s),
      (BM.insManyC (dlOps G s) T f l g Dc).2.1.Bd = Dc.Bd
  | [], _, _ => rfl
  | y :: l, g, Dc => by
    show (BM.insManyC (dlOps G s) T f l (BM.insC (dlOps G s) T g Dc y (f y)).1
      (BM.insC (dlOps G s) T g Dc y (f y)).2.1).2.1.Bd = Dc.Bd
    rw [insManyC_Bd' T f l, BM.insC_Bd]

/-- **`DInsI` from `DLayer.ins_spec`** (keys below the structure's bound `Bd`; the D layer's
resource counter `use` against `ucap`). -/
theorem dInsI_of {FR : List String} (Bd : WLab G s)
    (hE1 : ∀ st r, E st → Unchanged st r DL.dWA DL.dVA DL.dWR DL.dVR → r.wlen = st.wlen →
      r.vlen = st.vlen → st.cost ≤ r.cost → E r)
    (hE2 : ∀ st r, E st → Unchanged st r [] [] FR [] → st.cost ≤ r.cost → E r)
    (hFR : ∀ a ∈ DL.dWR, a ∉ FR) (hFl : "lvl" ∉ FR) (hFn : "n" ∉ FR) :
    DInsI realOps DL.ins (DRl DL H Ds lv d c0 E) (fun _ D => D.Bd = Bd) d (T lv) DL.K DL.K
      DL.dWA DL.dVA DL.dWR DL.dVR FR (fun v => d v < Bd) DL.use DL.ucap where
  run := by
    intro st g D v hDR hInv hPv hpx hub
    obtain ⟨hD, hL, hl, hn, hE⟩ := hDR
    refine (DL.ins_spec st H g (Function.update Ds lv D) lv d c0 v hD hL hl hn hpx
      (by simp only [Function.update_self]; rw [hInv]; exact hPv)
      (by simpa only [Function.update_self] using hub)).mono ?_
    rintro r ⟨hD', hU, hwl, hvl, hc1, hc2, hu⟩
    simp only [Function.update_self, Function.update_idem] at hD' hc2 hu
    refine ⟨⟨hD', hL.of_unchanged hU (dl_labW DL) (dl_dlen DL) hc1,
      by rw [hU.wreg _ (dl_spReg DL (by simp [spRegs]))]; exact hl,
      by rw [hU.wreg _ (dl_spReg DL (by simp [spRegs]))]; exact hn, hE1 st r hE hU hwl hvl hc1⟩,
      hU, hc1, by rw [Nat.mul_add, Nat.mul_one] at hc2; omega, hwl, hvl, hu⟩
  frame := by
    intro st r g D hDR hU hc
    obtain ⟨hD, hL, hl, hn, hE⟩ := hDR
    refine ⟨DL.frame st r H H g _ lv [] [] FR [] hD hU (by simp) (by simp) hFR ?_,
      hL.of_unchanged hU (by simp) (by simp) hc, by rw [hU.wreg _ hFl]; exact hl,
      by rw [hU.wreg _ hFn]; exact hn, hE2 st r hE hU hc⟩
    rw [vc_of_unchanged hU (by simp)]; exact HExt.refl _ _
  uframe := fun st r wa va wr vr hU hwr =>
    DL.use_frame st r wa va wr vr hU (fun a ha h => hwr a h ha)
  regs := fun a ha => ⟨hFR a ha, fun h => dl_spReg DL (by simp [spRegs]) (h ▸ ha),
    fun h => dl_spReg DL (by simp [spRegs]) (h ▸ ha)⟩
  arrs := fun a ha => ⟨fun h => dl_spArr DL (by simp [spArrs, rowArrs]) (h ▸ ha),
    fun h => dl_spArr DL (by simp [spArrs, lenArrs]) (h ▸ ha),
    fun h => dl_spArr DL (by simp [spArrs, rowArrs]) (h ▸ ha),
    fun h => dl_spArr DL (by simp [spArrs, lenArrs]) (h ▸ ha)⟩

/-- **`DNewI` from `DLayer.new_spec`** (the structure `newC M Bd` at level `lv`, `M = cp.M[lv]`,
bound in slot `B[lv]`). -/
theorem dNewI_of (M : ℕ) (Bd : WLab G s)
    (hE1 : ∀ st r, E st → Unchanged st r DL.dWA DL.dVA DL.dWR DL.dVR → r.wlen = st.wlen →
      r.vlen = st.vlen → st.cost ≤ r.cost → E r) :
    DNewI realOps DL.new (fun st g => DL.DR st H g Ds (lv + 1) ∧ LabAt st d H c0 ∧
        st.w "lvl" = lv ∧ st.w "n" = G.n ∧ st.wa "cp.M" lv = M ∧ lv < st.wlen "cp.M" ∧
        2 * M + 2 < st.cap ∧ SlotHolds st (slotB lv) H (vc st) Bd ∧ SlotLens st (slotB lv) ∧ E st)
      (DRl DL H Ds lv d c0 E) M Bd DL.K DL.dWA DL.dVA DL.dWR DL.dVR DL.use DL.ucap where
  run := by
    intro st g hDR0 hub
    obtain ⟨hD, hL, hl, hn, hM, hMl, hM2, hB, hBl, hE⟩ := hDR0
    refine (DL.new_spec st H g Ds lv M Bd hD hl hn hM hMl hM2 hB hBl hub).mono ?_
    rintro r ⟨hD', hU, hwl, hvl, hc1, hc2, hu⟩
    exact ⟨⟨hD', hL.of_unchanged hU (dl_labW DL) (dl_dlen DL) hc1,
      by rw [hU.wreg _ (dl_spReg DL (by simp [spRegs]))]; exact hl,
      by rw [hU.wreg _ (dl_spReg DL (by simp [spRegs]))]; exact hn, hE1 st r hE hU hwl hvl hc1⟩,
      hU, hc1, hc2, hwl, hvl, hu⟩

end inst

/-! ## The finalization tests -/

/-- Register blocks of the finalization tests. -/
def KT1 : LReg := ⟨"t6.k1l", "t6.k1h", "t6.k1v", "t6.k1e", "t6.k1r"⟩
def KT2 : LReg := ⟨"t6.k2l", "t6.k2h", "t6.k2v", "t6.k2e", "t6.k2r"⟩
def YT : LReg := ⟨"t6.yl", "t6.yh", "t6.yv", "t6.ye", "t6.yr"⟩

/-- `sl.i := 4·lvl + k` -/
def slotSet (k : ℕ) : Stmt := wset "sl.i" (add (mul (lit 4) (var "lvl")) (lit k))

/-- BM.25's test `t6.b := [B'f ≤ d[px] < B]` (slots `B'[lvl]`, `B[lvl]`). -/
def tstT6 : Stmt :=
  seq (seq (slotSet 2) (loadSlot KT1 "t6.k1f"))
  (seq (seq (slotSet 0) (loadSlot KT2 "t6.k2f"))
  (seq (headLtB "px" YT KT1 "t6.yf" "t6.k1f" "t6.c1" "t6.c2" "t6.l1")
  (seq (headLtB "px" YT KT2 "t6.yf" "t6.k2f" "t6.c1" "t6.c2" "t6.l2")
       (wset "t6.b" (mul (eq (var "t6.l1") (lit 0)) (var "t6.l2"))))))

/-- BM.26's test `t6.b := [d[px] < B'f]` (slot `B'[lvl]`). -/
def tstWp : Stmt :=
  seq (seq (slotSet 2) (loadSlot KT1 "t6.k1f"))
       (headLtB "px" YT KT1 "t6.yf" "t6.k1f" "t6.c1" "t6.c2" "t6.b")

/-- Word registers written by the tests. -/
def tstW : List String :=
  ["sl.i", "t6.k1f", "t6.k1h", "t6.k1v", "t6.k1e", "t6.k1r", "t6.k2f", "t6.k2h", "t6.k2v", "t6.k2e",
    "t6.k2r", "t6.yf", "t6.yh", "t6.yv", "t6.ye", "t6.yr", "t6.c1", "t6.c2", "t6.l1", "t6.l2", "t6.b"]
/-- Value registers written by the tests. -/
def tstV : List String := ["t6.k1l", "t6.k2l", "t6.yl"]

theorem evalW_slotSet {st : State ℝ≥0} {l k : ℕ} (hl : st.w "lvl" = l) (hc : 4 * l + k + 4 < st.cap) :
    evalW st (add (mul (lit 4) (var "lvl")) (lit k)) = some (4 * l + k) := by
  simp only [evalW_add', evalW_mul', evalW_lit', evalW_var, hl, fit_of_lt (show 4 < st.cap by omega),
    Option.bind_some, fit_of_lt (show 4 * l < st.cap by omega), fit_of_lt (show k < st.cap by omega),
    fit_of_lt (show 4 * l + k < st.cap by omega)]

theorem slotLens_of_unch {st r : State ℝ≥0} {i : ℕ} {wa va wr vr : List String} (h : SlotLens st i)
    (hu : Unchanged st r wa va wr vr) (hwl : r.wlen = st.wlen) (hvl : r.vlen = st.vlen) :
    SlotLens r i :=
  ⟨by rw [hvl]; exact h.l, by rw [hwl]; exact h.h, by rw [hwl]; exact h.v, by rw [hwl]; exact h.e,
    by rw [hwl]; exact h.r, by rw [hwl]; exact h.f⟩

/-- Load slot `4·lvl + k` into a test block. -/
theorem loadAt_spec (st : State ℝ≥0) {K : LReg} {kf : String} (hF : SlotFresh K kf) {l k : ℕ}
    (hl : st.w "lvl" = l) (hc : 4 * l + k + 4 < st.cap) (hsl : SlotLens st (4 * l + k))
    {H : Hist G} {b : WLab G s} (hb : SlotHolds st (4 * l + k) H (vc st) b) :
    Runs realOps (seq (slotSet k) (loadSlot K kf)) st (fun r => WHolds r K kf H (vc st) b ∧
      Unchanged st r [] [] ("sl.i" :: kf :: K.ws) [K.l] ∧ r.cost = st.cost + 7) := by
  refine runs_seq (runs_wset (a := 4 * l + k) (evalW_slotSet hl hc) ?_)
  have hU1 : Unchanged st ((st.setW "sl.i" (4 * l + k)).charge 1) [] [] ["sl.i"] [] :=
    unch_setW st _ (by simp)
  refine ((loadSlot_spec K kf hF ((st.setW "sl.i" (4 * l + k)).charge 1)
    (by simp [State.setW, State.charge]) ⟨hsl.l, hsl.h, hsl.v, hsl.e, hsl.r, hsl.f⟩
    (hb.of_unchanged hU1 (by simp) (by simp))).mono ?_)
  rintro r ⟨hW, hU2, hc2⟩
  refine ⟨hW, (hU1.mono (by simp) (by simp) (by simp) (by simp)).trans
    (hU2.mono (by simp) (by simp) (by intro a ha; simp at ha ⊢; tauto) (by simp)), ?_⟩
  rw [hc2]; simp only [State.charge_cost, State.setW_cost]

theorem slotFresh_KT1 : SlotFresh KT1 "t6.k1f" := ⟨by decide⟩
theorem slotFresh_KT2 : SlotFresh KT2 "t6.k2f" := ⟨by decide⟩

/-- **BM.25's test.** -/
theorem tstT6_spec (st : State ℝ≥0) (d : Labels G s) (H : Hist G) (c0 : ℕ) {lv : ℕ}
    {B B'f : WLab G s} (hL : LabAt st d H c0) (hl : st.w "lvl" = lv) (v : Fin G.n)
    (hv : st.w "px" = v) (hB : SlotHolds st (slotB lv) H (vc st) B)
    (hBp : SlotHolds st (slotBp lv) H (vc st) B'f) (hlB : SlotLens st (slotB lv))
    (hlBp : SlotLens st (slotBp lv)) (hcap : 4 * lv + 8 < st.cap) :
    Runs realOps tstT6 st (fun r => r.w "t6.b" = (if B'f ≤ d v ∧ d v < B then 1 else 0) ∧
      Unchanged st r [] [] tstW tstV ∧ st.cost ≤ r.cost ∧ r.cost ≤ st.cost + 59) := by
  have hc1 : 1 < st.cap := by omega
  -- K1 := slot B'[lvl]
  refine runs_seq ((loadAt_spec st slotFresh_KT1 hl (by omega) hlBp hBp).mono ?_)
  rintro r2 ⟨hK1, hU2, hc2⟩
  have hl2 : r2.w "lvl" = lv := by rw [hU2.wreg _ (by simp [KT1, LReg.ws])]; exact hl
  have hvc2 : vc (G := G) r2 = vc st := vc_of_unchanged hU2 (by simp)
  have hwl2 : r2.wlen = st.wlen := funext fun a => (hU2.warr a (by simp)).2
  have hvl2 : r2.vlen = st.vlen := funext fun a => (hU2.varr a (by simp)).2
  -- K2 := slot B[lvl]
  refine runs_seq ((loadAt_spec r2 slotFresh_KT2 hl2 (by rw [hU2.cap]; omega)
    (slotLens_of_unch hlB hU2 hwl2 hvl2)
    (by rw [hvc2]; exact hB.of_unchanged hU2 (by simp) (by simp))).mono ?_)
  rintro r4 ⟨hK2, hU4, hc4⟩
  rw [hvc2] at hK2
  have hvc4 : vc (G := G) r4 = vc st := (vc_of_unchanged hU4 (by simp)).trans hvc2
  have hK14 : WHolds r4 KT1 "t6.k1f" H (vc st) B'f :=
    hK1.of_unchanged hU4 (by decide) (by decide) (by decide)
  have hU04 : Unchanged st r4 [] [] tstW tstV :=
    (hU2.mono (by simp) (by simp) (by simp [tstW, KT1, LReg.ws]) (by simp [tstV, KT1])).trans
      (hU4.mono (by simp) (by simp) (by simp [tstW, KT2, LReg.ws]) (by simp [tstV, KT2]))
  have hL4 : LabAt r4 d H c0 := hL.of_unchanged hU04 (by simp) (by simp) (by omega)
  have hpx4 : r4.w "px" = v := by rw [hU04.wreg _ (by simp [tstW])]; exact hv
  have hcap4 : r4.cap = st.cap := hU04.cap
  -- t6.l1 := [d px < B'f]
  refine runs_seq ((Runs.cost_mono (wp_sound _ _ _ (headLtB_wp "px" YT KT1 "t6.yf" "t6.k1f" "t6.c1" "t6.c2"
    "t6.l1" ⟨by decide, by decide⟩ ⟨by decide, by decide, by decide, by decide, by decide⟩
    (by decide) (by decide) (by decide) r4 d H c0 hL4 v hpx4 B'f (by rw [hvc4]; exact hK14)
    (by rw [hcap4]; omega)))).mono ?_)
  rintro r5 ⟨⟨hl1, hU5, hc5⟩, hc5'⟩
  have hK25 : WHolds r5 KT2 "t6.k2f" H (vc st) B :=
    hK2.of_unchanged hU5 (by decide) (by decide) (by decide)
  have hU05 : Unchanged st r5 [] [] tstW tstV :=
    hU04.trans (hU5.mono (by simp) (by simp) (by simp [tstW, YT, LReg.ws]) (by simp [tstV, YT]))
  have hvc5 : vc (G := G) r5 = vc st := vc_of_unchanged hU05 (by simp)
  have hL5 : LabAt r5 d H c0 := hL4.of_unchanged hU5 (by simp) (by simp) hc5'
  have hpx5 : r5.w "px" = v := by rw [hU05.wreg _ (by simp [tstW])]; exact hv
  -- t6.l2 := [d px < B]
  refine runs_seq ((Runs.cost_mono (wp_sound _ _ _ (headLtB_wp "px" YT KT2 "t6.yf" "t6.k2f" "t6.c1" "t6.c2"
    "t6.l2" ⟨by decide, by decide⟩ ⟨by decide, by decide, by decide, by decide, by decide⟩
    (by decide) (by decide) (by decide) r5 d H c0 hL5 v hpx5 B (by rw [hvc5]; exact hK25)
    (by rw [hU05.cap]; omega)))).mono ?_)
  rintro r6 ⟨⟨hl2', hU6, hc6⟩, hc6'⟩
  have hU06 : Unchanged st r6 [] [] tstW tstV :=
    hU05.trans (hU6.mono (by simp) (by simp) (by simp [tstW, YT, LReg.ws]) (by simp [tstV, YT]))
  have hl16 : r6.w "t6.l1" = if d v < B'f then 1 else 0 := by
    rw [hU6.wreg _ (by simp [YT, LReg.ws])]; exact hl1
  have hcap6 : r6.cap = st.cap := hU06.cap
  -- t6.b := [t6.l1 = 0] * t6.l2
  have hval : (if (if d v < B'f then 1 else 0) = 0 then 1 else 0) * (if d v < B then 1 else 0) =
      (if B'f ≤ d v ∧ d v < B then 1 else 0 : ℕ) := by
    by_cases h1 : d v < B'f <;> by_cases h2 : d v < B <;> simp [h1, h2, not_lt.mp, not_lt.mpr]
  refine runs_wset (a := if B'f ≤ d v ∧ d v < B then 1 else 0) ?_ ?_
  · simp only [evalW_mul', evalW_eq', evalW_var, evalW_lit', hl16, hl2', Option.bind_some,
      fit_of_lt (show 0 < r6.cap by omega), fit_of_lt (show 1 < r6.cap by omega)]
    rw [← hval]
    split_ifs <;> simp [fit_of_lt (show 0 < r6.cap by omega), fit_of_lt (show 1 < r6.cap by omega)]
  refine ⟨by simp, ?_, by simp; omega, by simp; omega⟩
  rw [unch_charge, Frontier.RAM.unch_setW (by simp [tstW])]; exact hU06

/-- **BM.26's test.** -/
theorem tstWp_spec (st : State ℝ≥0) (d : Labels G s) (H : Hist G) (c0 : ℕ) {lv : ℕ}
    {B'f : WLab G s} (hL : LabAt st d H c0) (hl : st.w "lvl" = lv) (v : Fin G.n)
    (hv : st.w "px" = v) (hBp : SlotHolds st (slotBp lv) H (vc st) B'f)
    (hlBp : SlotLens st (slotBp lv)) (hcap : 4 * lv + 8 < st.cap) :
    Runs realOps tstWp st (fun r => r.w "t6.b" = (if d v < B'f then 1 else 0) ∧
      Unchanged st r [] [] tstW tstV ∧ st.cost ≤ r.cost ∧ r.cost ≤ st.cost + 29) := by
  refine runs_seq ((loadAt_spec st slotFresh_KT1 hl (by omega) hlBp hBp).mono ?_)
  rintro r2 ⟨hK1, hU2, hc2⟩
  have hvc2 : vc (G := G) r2 = vc st := vc_of_unchanged hU2 (by simp)
  have hU02 : Unchanged st r2 [] [] tstW tstV :=
    hU2.mono (by simp) (by simp) (by simp [tstW, KT1, LReg.ws]) (by simp [tstV, KT1])
  have hL2 : LabAt r2 d H c0 := hL.of_unchanged hU02 (by simp) (by simp) (by omega)
  have hpx2 : r2.w "px" = v := by rw [hU02.wreg _ (by simp [tstW])]; exact hv
  refine (Runs.cost_mono (wp_sound _ _ _ (headLtB_wp "px" YT KT1 "t6.yf" "t6.k1f" "t6.c1" "t6.c2"
    "t6.b" ⟨by decide, by decide⟩ ⟨by decide, by decide, by decide, by decide, by decide⟩
    (by decide) (by decide) (by decide) r2 d H c0 hL2 v hpx2 B'f (by rw [hvc2]; exact hK1)
    (by rw [hU02.cap]; omega)))).mono ?_
  rintro r3 ⟨⟨hb, hU3, hc3⟩, hc3'⟩
  exact ⟨hb, hU02.trans (hU3.mono (by simp) (by simp) (by simp [tstW, YT, LReg.ws]) (by simp [tstV, YT])),
    by omega, by omega⟩

/-! ## `TestI` instances of the tests -/

/-- BM.25's predicate on vertex numbers. -/
def PT6 (d : Labels G s) (B B'f : WLab G s) (n : ℕ) : Prop :=
  ∃ h : n < G.n, B'f ≤ d ⟨n, h⟩ ∧ d ⟨n, h⟩ < B

noncomputable instance (d : Labels G s) (B B'f : WLab G s) : DecidablePred (PT6 d B B'f) := fun n => by
  unfold PT6; infer_instance

/-- BM.26's predicate on vertex numbers. -/
def PWp (d : Labels G s) (B'f : WLab G s) (n : ℕ) : Prop := ∃ h : n < G.n, d ⟨n, h⟩ < B'f

noncomputable instance (d : Labels G s) (B'f : WLab G s) : DecidablePred (PWp d B'f) := fun n => by
  unfold PWp; infer_instance

/-- The slot part of the finalization's state predicate. -/
def SlotsE (H : Hist G) (lv : ℕ) (B B'f : WLab G s) (E' : State ℝ≥0 → Prop) (st : State ℝ≥0) :
    Prop :=
  SlotHolds st (slotB lv) H (vc st) B ∧ SlotHolds st (slotBp lv) H (vc st) B'f ∧
    SlotLens st (slotB lv) ∧ SlotLens st (slotBp lv) ∧ 4 * lv + 8 < st.cap ∧ E' st

theorem slotsE_of_unch {H : Hist G} {lv : ℕ} {B B'f : WLab G s} {E' : State ℝ≥0 → Prop}
    {st r : State ℝ≥0} {wa va wr vr : List String} (h : SlotsE H lv B B'f E' st)
    (hu : Unchanged st r wa va wr vr) (hw : ∀ a ∈ slotW, a ∉ wa) (hv : "sl.l" ∉ va)
    (hvc : "vcnt" ∉ wa) (hwl : r.wlen = st.wlen) (hvl : r.vlen = st.vlen) (hE : E' r) :
    SlotsE H lv B B'f E' r := by
  obtain ⟨hB, hBp, hlB, hlBp, hcap, -⟩ := h
  have hvc' : vc (G := G) r = vc st := vc_of_unchanged hu hvc
  exact ⟨by rw [hvc']; exact hB.of_unchanged hu hw hv, by rw [hvc']; exact hBp.of_unchanged hu hw hv,
    slotLens_of_unch hlB hu hwl hvl, slotLens_of_unch hlBp hu hwl hvl, by rw [hu.cap]; exact hcap, hE⟩

section testI

variable (DL : DLayer G s T) (H : Hist G) (Ds : ℕ → DStrM G s) (lv : ℕ) (d : Labels G s) (c0 : ℕ)
  (B B'f : WLab G s) (E' : State ℝ≥0 → Prop)

theorem tstW_regs : ∀ a ∈ tstW, a ≠ "t6.i" ∧ a ≠ "px" ∧ a ≠ "lvl" ∧ a ≠ "n" := by
  intro a ha; simp only [tstW, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> decide

/-- The tests keep the D-layer state predicate. -/
theorem drl_of_test {st r : State ℝ≥0} {g : DGl G s} {D : DStrM G s}
    (hTW : ∀ a ∈ DL.dWR, a ∉ tstW)
    (hE' : ∀ st r, E' st → Unchanged st r [] [] tstW tstV → st.cost ≤ r.cost → E' r)
    (h : DRl DL H Ds lv d c0 (SlotsE H lv B B'f E') st g D) (hU : Unchanged st r [] [] tstW tstV)
    (hc : st.cost ≤ r.cost) : DRl DL H Ds lv d c0 (SlotsE H lv B B'f E') r g D := by
  obtain ⟨hD, hL, hl, hn, hE⟩ := h
  have hvc : vc (G := G) r = vc st := vc_of_unchanged hU (by simp)
  have hwl : r.wlen = st.wlen := funext fun a => (hU.warr a (by simp)).2
  have hvl : r.vlen = st.vlen := funext fun a => (hU.varr a (by simp)).2
  exact ⟨DL.frame st r H H g _ lv [] [] tstW tstV hD hU (by simp) (by simp) hTW
      (by rw [hvc]; exact HExt.refl _ _),
    hL.of_unchanged hU (by simp) (by simp) hc, by rw [hU.wreg _ (by simp [tstW])]; exact hl,
    by rw [hU.wreg _ (by simp [tstW])]; exact hn,
    slotsE_of_unch hE hU (by simp) (by simp) (by simp) hwl hvl (hE' st r hE.2.2.2.2.2 hU hc)⟩

/-- **`TestI` for BM.25's test.** -/
theorem testI_T6 (hTW : ∀ a ∈ DL.dWR, a ∉ tstW)
    (hE' : ∀ st r, E' st → Unchanged st r [] [] tstW tstV → st.cost ≤ r.cost → E' r) :
    TestI realOps tstT6 (DRl DL H Ds lv d c0 (SlotsE H lv B B'f E')) (PT6 d B B'f) 59 tstW tstV where
  run := by
    intro st g D hDR hpx
    obtain ⟨hD, hL, hl, hn, hB, hBp, hlB, hlBp, hcap, hE⟩ := hDR
    refine (tstT6_spec st d H c0 hL hl ⟨st.w "px", hpx⟩ rfl hB hBp hlB hlBp hcap).mono ?_
    rintro r ⟨hb, hU, hc1, hc2⟩
    refine ⟨?_, hU, hc1, hc2, drl_of_test DL H Ds lv d c0 B B'f E' hTW hE'
      ⟨hD, hL, hl, hn, hB, hBp, hlB, hlBp, hcap, hE⟩ hU hc1⟩
    rw [hb]
    exact if_congr ⟨fun h => ⟨hpx, h⟩, fun ⟨_, h⟩ => h⟩ rfl rfl
  regs := tstW_regs
  bit := by simp [tstW]

/-- **`TestI` for BM.26's test.** -/
theorem testI_Wp (hTW : ∀ a ∈ DL.dWR, a ∉ tstW)
    (hE' : ∀ st r, E' st → Unchanged st r [] [] tstW tstV → st.cost ≤ r.cost → E' r) :
    TestI realOps tstWp (DRl DL H Ds lv d c0 (SlotsE H lv B B'f E')) (PWp d B'f) 29 tstW tstV where
  run := by
    intro st g D hDR hpx
    obtain ⟨hD, hL, hl, hn, hB, hBp, hlB, hlBp, hcap, hE⟩ := hDR
    refine (tstWp_spec st d H c0 hL hl ⟨st.w "px", hpx⟩ rfl hBp hlBp hcap).mono ?_
    rintro r ⟨hb, hU, hc1, hc2⟩
    refine ⟨?_, hU, hc1, hc2, drl_of_test DL H Ds lv d c0 B B'f E' hTW hE'
      ⟨hD, hL, hl, hn, hB, hBp, hlB, hlBp, hcap, hE⟩ hU hc1⟩
    rw [hb]
    exact if_congr ⟨fun h => ⟨hpx, h⟩, fun ⟨_, h⟩ => h⟩ rfl rfl
  regs := tstW_regs
  bit := by simp [tstW]

end testI

/-! ## `CmpI` for the pivot comparison -/

/-- Scratch word registers of the pivot comparison. -/
def ttCmpW : List String := "lab.bit" :: IHeapLab.cmpScratchW

/-- The key of a vertex number (labels `d`; `⊤` outside the range). -/
noncomputable def keyOf (d : Labels G s) (x : ℕ) : WLab G s := if h : x < G.n then d ⟨x, h⟩ else ⊤

/-- The state predicate of the pivot comparisons: the label table (fixed labels, history and
counters), the graph, the word capacity, and an extra part `E`. -/
def KRp (d : Labels G s) (H : Hist G) (V0 : Fin G.n → ℕ) (c0 cap0 : ℕ) (E : State ℝ≥0 → Prop)
    (st : State ℝ≥0) : Prop :=
  LabIInst.LTp c0 st d (H, V0) ∧ st.cap = cap0 ∧ E st

theorem cmpW_regs : ∀ a ∈ ttCmpW, a ∉ gmRegs ∧ a ≠ "lvl" ∧ a ≠ "n" ∧ a ≠ "sp.j" := by
  intro a ha; simp only [ttCmpW, IHeapLab.cmpScratchW, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

/-- **`CmpI` for `cmpLab tt.ra tt.rb lab.bit`** (B-LAB's `cmpTT_spec`). -/
theorem cmpI_tt (d : Labels G s) (H : Hist G) (V0 : Fin G.n → ℕ) (c0 cap0 : ℕ)
    (E : State ℝ≥0 → Prop)
    (hE : ∀ st r, E st → Unchanged st r ["sp.gp"] [] (pvRegs ++ ttCmpW) IHeapLab.lessV →
      st.cost ≤ r.cost → E r) :
    CmpI realOps (IHeapLab.cmpLab IHeapLab.ttRa IHeapLab.ttRb "lab.bit") (KRp d H V0 c0 cap0 E)
      (keyOf d) (fun x => ∃ h : x < G.n, d ⟨x, h⟩ ≠ ⊤) 27 (c0 + cap0) ttCmpW IHeapLab.lessV
      ["sp.gp"] (pvRegs ++ ttCmpW) where
  run := by
    intro st hK ha hb hbud
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    obtain ⟨hLT, hcap, hE0⟩ := hK
    refine (IHeapLab.cmpTT_spec (a := ⟨st.w "tt.ra", ha1⟩) (b := ⟨st.w "tt.rb", hb1⟩) c0 hLT ha2 hb2
      rfl rfl (by rw [hcap]; exact hbud)).mono ?_
    rintro r ⟨hbit, hU, hc1, hc2⟩
    obtain ⟨hL, hvc, hGr, hm⟩ := hLT
    refine ⟨?_, hU, hc1, hc2, ⟨hL.of_unchanged hU (by simp) (by simp) hc1,
      (vc_of_unchanged hU (by simp)).trans hvc, graphAt_of_unchanged hU (by simp) (by simp) hGr,
      by rw [hU.cap]; exact hm⟩, by rw [hU.cap]; exact hcap,
      hE st r hE0 (hU.mono (by simp) (by simp) (by intro a ha; simp [ttCmpW] at ha ⊢; tauto) (by simp))
        hc1⟩
    rw [hbit]
    simp only [keyOf, dif_pos ha1, dif_pos hb1]
  frame := by
    intro st r hK hU hc
    obtain ⟨⟨hL, hvc, hGr, hm⟩, hcap, hE0⟩ := hK
    exact ⟨⟨hL.of_unchanged hU (by simp [labW]) (by simp) hc,
      (vc_of_unchanged hU (by simp)).trans hvc, graphAt_of_unchanged hU (by simp) (by simp) hGr,
      by rw [hU.cap]; exact hm⟩, by rw [hU.cap]; exact hcap,
      hE st r hE0 (hU.mono (by simp) (by simp) (by simp) (by simp)) hc⟩
  bit_mem := by simp [ttCmpW]
  regs := cmpW_regs

end Frontier.CHD.RamBody
