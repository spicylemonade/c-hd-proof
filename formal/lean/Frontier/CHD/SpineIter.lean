import Frontier.CHD.SpineLoop
import Frontier.CHD.DGlobal

/-!
# SpineIter — one iteration of the main loop (agent-08, B-L4, NON-GATE)

Slot plumbing of an iteration: `loadBi` (the pull bound `B_i` into the register block `KBi`, for
the expansion's label test) and `copyChild` (the child's bound slots `B[l-1] := B_i[l]`,
`B_low[l-1] := B'[l]`).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamSpine

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.RamLevel
  Frontier.CHD.BM Frontier.CHD.RamBaseCase Frontier.CHD.LabTab WExpr Stmt

variable {G : Graph} {s : Fin G.n}

/-- The register block holding `B_i` during the expansion. -/
def KBi : LReg := ⟨"sp.bil", "sp.bih", "sp.biv", "sp.bie", "sp.bir"⟩
/-- The register block of the slot copies. -/
def KC : LReg := ⟨"sp.cl", "sp.ch", "sp.cv", "sp.ce", "sp.cr"⟩

/-- `sl.i := 4·lvl + k` -/
def slotAt (k : ℕ) : Stmt := wset "sl.i" (add (mul (lit 4) (var "lvl")) (lit k))
/-- `sl.i := 4·(lvl - 1) + k` -/
def slotAtC (k : ℕ) : Stmt := wset "sl.i" (add (mul (lit 4) (sub (var "lvl") (lit 1))) (lit k))

/-- `KBi := slot B_i[lvl]` -/
def loadBi : Stmt := seq (slotAt 3) (loadSlot KBi "sp.bif")

/-- `B[lvl-1] := B_i[lvl]; B_low[lvl-1] := B'[lvl]` -/
def copyChild : Stmt :=
  seq (slotAt 3) (seq (loadSlot KC "sp.cf") (seq (slotAtC 0) (seq (storeSlot KC "sp.cf")
  (seq (slotAt 2) (seq (loadSlot KC "sp.cf") (seq (slotAtC 1) (storeSlot KC "sp.cf")))))))

theorem evalW_slotAt {st : State ℝ≥0} {l k : ℕ} (hl : st.w "lvl" = l) (hc : 4 * l + k + 4 < st.cap) :
    evalW st (add (mul (lit 4) (var "lvl")) (lit k)) = some (4 * l + k) := by
  simp only [evalW_add', evalW_mul', evalW_lit', evalW_var, hl, fit_of_lt (show 4 < st.cap by omega),
    Option.bind_some, fit_of_lt (show 4 * l < st.cap by omega), fit_of_lt (show k < st.cap by omega),
    fit_of_lt (show 4 * l + k < st.cap by omega)]

theorem evalW_slotAtC {st : State ℝ≥0} {l k : ℕ} (hl : st.w "lvl" = l) (hc : 4 * l + k + 4 < st.cap) :
    evalW st (add (mul (lit 4) (sub (var "lvl") (lit 1))) (lit k)) = some (4 * (l - 1) + k) := by
  have h1 : 4 * (l - 1) ≤ 4 * l := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  simp only [evalW_add', evalW_mul', evalW_sub', evalW_lit', evalW_var, hl,
    fit_of_lt (show 4 < st.cap by omega), fit_of_lt (show 1 < st.cap by omega), Option.bind_some,
    fit_of_lt (show 4 * (l - 1) < st.cap by omega), fit_of_lt (show k < st.cap by omega),
    fit_of_lt (show 4 * (l - 1) + k < st.cap by omega)]

theorem slotFresh_KBi : SlotFresh KBi "sp.bif" := ⟨by decide⟩
theorem slotFresh_KC : SlotFresh KC "sp.cf" := ⟨by decide⟩

/-- **`loadBi`**: the pull bound of slot `B_i[l]` is loaded into `KBi`. -/
theorem loadBi_spec (st : State ℝ≥0) {l : ℕ} (hl : st.w "lvl" = l) (hsl : SlotLens st (slotBi l))
    {H : Hist G} {V : Fin G.n → ℕ} {b : WLab G s} (hb : SlotHolds st (slotBi l) H V b)
    (hc : 4 * l + 7 < st.cap) :
    Runs realOps loadBi st (fun r => WHolds r KBi "sp.bif" H V b ∧
      Unchanged st r [] [] ("sl.i" :: "sp.bif" :: KBi.ws) [KBi.l] ∧ r.cost = st.cost + 7) := by
  refine runs_seq (runs_wset (a := slotBi l) (by rw [evalW_slotAt hl (by omega)]; rfl) ?_)
  have hU1 : Unchanged st ((st.setW "sl.i" (slotBi l)).charge 1) [] [] ["sl.i"] [] :=
    unch_setW st _ (by simp)
  refine ((loadSlot_spec KBi "sp.bif" slotFresh_KBi ((st.setW "sl.i" (slotBi l)).charge 1)
    (by simp [State.setW, State.charge]) ⟨hsl.l, hsl.h, hsl.v, hsl.e, hsl.r, hsl.f⟩
    (hb.of_unchanged hU1 (by simp) (by simp))).mono ?_)
  rintro r ⟨hW, hU2, hc2⟩
  refine ⟨hW, (hU1.mono (by simp) (by simp) (by simp) (by simp)).trans
    (hU2.mono (by simp) (by simp) (by simp) (by simp)), ?_⟩
  rw [hc2]; simp only [State.charge_cost, State.setW_cost]

/-- **`copyChild`**: the child's bound slots get `B_i[l]` and `B'[l]`; all other slots are kept. -/
theorem copyChild_spec (st : State ℝ≥0) {l : ℕ} (hl : st.w "lvl" = l) (hl1 : 1 ≤ l)
    (hsl : ∀ i ≤ slotBi l, SlotLens st i) {H : Hist G} {V : Fin G.n → ℕ} {bi bp : WLab G s}
    (hbi : SlotHolds st (slotBi l) H V bi) (hbp : SlotHolds st (slotBp l) H V bp)
    (hc : 4 * l + 7 < st.cap) :
    Runs realOps copyChild st (fun r => SlotHolds r (slotB (l - 1)) H V bi ∧
      SlotHolds r (slotBlow (l - 1)) H V bp ∧
      (∀ j, j ≠ slotB (l - 1) → j ≠ slotBlow (l - 1) →
        r.va "sl.l" j = st.va "sl.l" j ∧ ∀ a ∈ slotW, r.wa a j = st.wa a j) ∧
      Unchanged st r slotW ["sl.l"] ("sl.i" :: "sp.cf" :: KC.ws) [KC.l] ∧ r.wlen = st.wlen ∧
      r.vlen = st.vlen ∧ r.cost = st.cost + 28) := by
  have hne1 : slotB (l - 1) ≠ slotBp l := by unfold slotB slotBp; omega
  have hne2 : slotBlow (l - 1) ≠ slotB (l - 1) := by unfold slotB slotBlow; omega
  have hle1 : slotB (l - 1) ≤ slotBi l := by unfold slotB slotBi; omega
  have hle2 : slotBlow (l - 1) ≤ slotBi l := by unfold slotBlow slotBi; omega
  have hle3 : slotBp l ≤ slotBi l := by unfold slotBp slotBi; omega
  -- 1–2: `KC := slot B_i[l]`
  refine runs_seq (runs_wset (a := slotBi l) (by rw [evalW_slotAt hl (by omega)]; rfl) ?_)
  set s1 := (st.setW "sl.i" (slotBi l)).charge 1 with hs1
  have hU1 : Unchanged st s1 [] [] ["sl.i"] [] := unch_setW st _ (by simp)
  have hsl1 := hsl _ le_rfl
  refine runs_seq ((loadSlot_spec KC "sp.cf" slotFresh_KC s1 (by simp [hs1, State.setW, State.charge])
    ⟨hsl1.l, hsl1.h, hsl1.v, hsl1.e, hsl1.r, hsl1.f⟩
    (hbi.of_unchanged hU1 (by simp) (by simp))).mono ?_)
  rintro s2 ⟨hW2, hU2, hc2⟩
  have hl2 : s2.w "lvl" = l := by
    rw [hU2.wreg _ (by simp [KC, LReg.ws])]; simp [hs1, State.setW, State.charge, hl]
  -- 3–4: `slot B[l-1] := KC`
  refine runs_seq (runs_wset (a := slotB (l - 1)) (by
    rw [show slotB (l - 1) = 4 * (l - 1) + 0 from rfl]
    exact evalW_slotAtC hl2 (by rw [hU2.cap, hU1.cap]; omega)) ?_)
  set s3 := (s2.setW "sl.i" (slotB (l - 1))).charge 1 with hs3
  have hU3 : Unchanged s2 s3 [] [] ["sl.i"] [] := unch_setW s2 _ (by simp)
  have hsl3 : SlotLens s3 (slotB (l - 1)) := by
    have h := hsl _ hle1
    have e : s3.wlen = st.wlen := by
      rw [show s3.wlen = s2.wlen from rfl]
      exact funext fun a => (hU2.warr a (by simp)).2.trans (hU1.warr a (by simp)).2
    have e' : s3.vlen = st.vlen := by
      rw [show s3.vlen = s2.vlen from rfl]
      exact funext fun a => (hU2.varr a (by simp)).2.trans (hU1.varr a (by simp)).2
    exact ⟨by rw [e']; exact h.l, by rw [e]; exact h.h, by rw [e]; exact h.v, by rw [e]; exact h.e,
      by rw [e]; exact h.r, by rw [e]; exact h.f⟩
  refine runs_seq ((DGlob.Runs.keep_len (storeSlot_spec KC "sp.cf" s3
    (by simp [hs3, State.setW, State.charge]) hsl3
    (hW2.of_unchanged hU3 (by simp [KC, LReg.ws]) (by simp [KC]) (by simp)))
    (by simp [DGlob.NoAlloc, storeSlot])).mono ?_)
  rintro s4 ⟨⟨hS4, hF4, hU4, hc4⟩, hwl4, hvl4⟩
  have e2w : s2.wlen = st.wlen := funext fun a => (hU2.warr a (by simp)).2.trans (hU1.warr a (by simp)).2
  have e2v : s2.vlen = st.vlen := funext fun a => (hU2.varr a (by simp)).2.trans (hU1.varr a (by simp)).2
  have hwl4' : s4.wlen = st.wlen := funext fun a => (hwl4 a).trans (by rw [show s3.wlen = s2.wlen from rfl, e2w])
  have hvl4' : s4.vlen = st.vlen := funext fun a => (hvl4 a).trans (by rw [show s3.vlen = s2.vlen from rfl, e2v])
  -- the other slots between `st` and `s4`
  have hsl34 : ∀ j, j ≠ slotB (l - 1) → s4.va "sl.l" j = st.va "sl.l" j ∧
      ∀ a ∈ slotW, s4.wa a j = st.wa a j := by
    intro j hj
    obtain ⟨e1, e2⟩ := hF4 j hj
    refine ⟨by rw [e1, show s3.va = s2.va from rfl, (hU2.varr "sl.l" (by simp [KC])).1]; rfl,
      fun a ha => by
        rw [e2 a ha, show s3.wa = s2.wa from rfl, (hU2.warr a (by simp)).1]; rfl⟩
  have hU04 : Unchanged st s4 slotW ["sl.l"] ("sl.i" :: "sp.cf" :: KC.ws) [KC.l] :=
    (((hU1.mono (by simp) (by simp) (by simp) (by simp)).trans
      (hU2.mono (by simp) (by simp) (by simp) (by simp))).trans
      (hU3.mono (by simp) (by simp) (by simp) (by simp))).trans
      (hU4.mono (List.Subset.refl _) (List.Subset.refl _) (by simp) (by simp))
  have hl4 : s4.w "lvl" = l := by rw [hU04.wreg _ (by simp [KC, LReg.ws])]; exact hl
  -- 5–6: `KC := slot B'[l]`
  refine runs_seq (runs_wset (a := slotBp l) (by
    rw [evalW_slotAt hl4 (by rw [hU04.cap]; omega)]; rfl) ?_)
  set s5 := (s4.setW "sl.i" (slotBp l)).charge 1 with hs5
  have hU5 : Unchanged s4 s5 [] [] ["sl.i"] [] := unch_setW s4 _ (by simp)
  have hbp5 : SlotHolds s5 (slotBp l) H V bp := by
    refine SlotHolds.of_slot_eq hbp ?_ ?_
    · rw [show s5.va = s4.va from rfl]; exact (hsl34 _ hne1.symm).1
    · intro a ha; rw [show s5.wa = s4.wa from rfl]; exact (hsl34 _ hne1.symm).2 a ha
  have hsl5 : SlotLens s5 (slotBp l) := by
    have h := hsl _ hle3
    have e : s5.wlen = st.wlen := by rw [show s5.wlen = s4.wlen from rfl, hwl4']
    have e' : s5.vlen = st.vlen := by rw [show s5.vlen = s4.vlen from rfl, hvl4']
    exact ⟨by rw [e']; exact h.l, by rw [e]; exact h.h, by rw [e]; exact h.v, by rw [e]; exact h.e,
      by rw [e]; exact h.r, by rw [e]; exact h.f⟩
  refine runs_seq ((loadSlot_spec KC "sp.cf" slotFresh_KC s5 (by simp [hs5, State.setW, State.charge])
    hsl5 hbp5).mono ?_)
  rintro s6 ⟨hW6, hU6, hc6⟩
  have hl6 : s6.w "lvl" = l := by
    rw [hU6.wreg _ (by simp [KC, LReg.ws])]; simp [hs5, State.setW, State.charge, hl4]
  -- 7–8: `slot B_low[l-1] := KC`
  refine runs_seq (runs_wset (a := slotBlow (l - 1)) (by
    rw [show slotBlow (l - 1) = 4 * (l - 1) + 1 from rfl]
    exact evalW_slotAtC hl6 (by rw [hU6.cap, hU5.cap, hU04.cap]; omega)) ?_)
  set s7 := (s6.setW "sl.i" (slotBlow (l - 1))).charge 1 with hs7
  have hU7 : Unchanged s6 s7 [] [] ["sl.i"] [] := unch_setW s6 _ (by simp)
  have e6w : s6.wlen = st.wlen := by
    rw [funext fun a => (hU6.warr a (by simp)).2, show s5.wlen = s4.wlen from rfl, hwl4']
  have e6v : s6.vlen = st.vlen := by
    rw [funext fun a => (hU6.varr a (by simp)).2, show s5.vlen = s4.vlen from rfl, hvl4']
  have hsl7 : SlotLens s7 (slotBlow (l - 1)) := by
    have h := hsl _ hle2
    have e : s7.wlen = st.wlen := by rw [show s7.wlen = s6.wlen from rfl, e6w]
    have e' : s7.vlen = st.vlen := by rw [show s7.vlen = s6.vlen from rfl, e6v]
    exact ⟨by rw [e']; exact h.l, by rw [e]; exact h.h, by rw [e]; exact h.v, by rw [e]; exact h.e,
      by rw [e]; exact h.r, by rw [e]; exact h.f⟩
  refine (DGlob.Runs.keep_len (storeSlot_spec KC "sp.cf" s7
    (by simp [hs7, State.setW, State.charge]) hsl7
    (hW6.of_unchanged hU7 (by simp [KC, LReg.ws]) (by simp [KC]) (by simp)))
    (by simp [DGlob.NoAlloc, storeSlot])).mono ?_
  rintro r ⟨⟨hS8, hF8, hU8, hc8⟩, hwl8, hvl8⟩
  have hU68 : Unchanged s4 r slotW ["sl.l"] ("sl.i" :: "sp.cf" :: KC.ws) [KC.l] :=
    (((hU5.mono (by simp) (by simp) (by simp) (by simp)).trans
      (hU6.mono (by simp) (by simp) (by simp) (by simp))).trans
      (hU7.mono (by simp) (by simp) (by simp) (by simp))).trans
      (hU8.mono (List.Subset.refl _) (List.Subset.refl _) (by simp) (by simp))
  -- slots of `r` vs `s4` away from `slotBlow (l-1)`
  have hsl48 : ∀ j, j ≠ slotBlow (l - 1) → r.va "sl.l" j = s4.va "sl.l" j ∧
      ∀ a ∈ slotW, r.wa a j = s4.wa a j := by
    intro j hj
    obtain ⟨e1, e2⟩ := hF8 j hj
    refine ⟨by rw [e1, show s7.va = s6.va from rfl, (hU6.varr "sl.l" (by simp [KC])).1]; rfl,
      fun a ha => by rw [e2 a ha, show s7.wa = s6.wa from rfl, (hU6.warr a (by simp)).1]; rfl⟩
  refine ⟨SlotHolds.of_slot_eq hS4 (hsl48 _ hne2.symm).1 (hsl48 _ hne2.symm).2, hS8,
    fun j hj1 hj2 => ⟨(hsl48 j hj2).1.trans (hsl34 j hj1).1,
      fun a ha => ((hsl48 j hj2).2 a ha).trans ((hsl34 j hj1).2 a ha)⟩,
    hU04.trans hU68, ?_, ?_, ?_⟩
  · exact funext fun a => (hwl8 a).trans (by rw [show s7.wlen = s6.wlen from rfl, e6w])
  · exact funext fun a => (hvl8 a).trans (by rw [show s7.vlen = s6.vlen from rfl, e6v])
  · rw [hc8]; simp only [hs7, State.charge_cost, State.setW_cost, hc6, hs5, hc4, hs3, hc2, hs1]

/-! ## The hand-off between the two halves of an iteration

After the recursive call (BM.13) and `lvlUp`, the machine is in a state `PostCall`: the child's
result is in the child level (its structure on top of the stack, its `U` in the child's `U` row,
its bound in slot `B'[l]`), the labels are the child's, and the level-`(l+1)` data of the loop
state `c` are untouched.  The **first half** (`childReset … lvlUp`, agent-08) establishes it; the
**second half** (`merge; removeU; scan; resel; appU; dsEmpty`) goes from it to `LoopRep` of the
successor configuration. -/

section postCall

variable {T : ℕ → ℕ} {Φ : Type}

/-- What the main loop preserves of the loop-entry state `st0` (level `l + 1`): the level-`(l+1)`
`S` and `W` rows and everything above (agent-01's `RamBody.LoopFrame`, restated here). -/
structure LFrame (st0 r : State ℝ≥0) (n l : ℕ) : Prop where
  S : ∀ i, (l + 1) * n ≤ i → i < (l + 2) * n → r.wa "S" i = st0.wa "S" i
  Slen : r.wa "S.len" (l + 1) = st0.wa "S.len" (l + 1)
  W : ∀ i, (l + 1) * n ≤ i → i < (l + 2) * n → r.wa "W" i = st0.wa "W" i
  Wlen : r.wa "W.len" (l + 1) = st0.wa "W.len" (l + 1)
  above : Above st0 r n (l + 1)
  /-- the static arrays (CSR, tables, L6 outputs) are untouched, as `CallOut.stArr` needs -/
  stArr : ∀ a ∈ ["gSt", "gHead", "cp.tau", "cp.M", "gKeep", "gRep"], r.wa a = st0.wa a

/-- **The state after the recursive call** of an iteration at level `l + 1` from configuration
`c`, with pull bound `Bi` and remaining level structure `Dc1`, and the child's result
`(B'i, Ui, Dci, d1)`, `φ1`, `g2` (history `H`). -/
structure PostCall (DL : DLayer G s T) (PI : PhiI Φ) (LF : ℕ) (body : Stmt) (τf Mf : ℕ → ℕ)
    (st0 : State ℝ≥0) (l : ℕ) (B : WLab G s) (τl : ℕ) (Ds : ℕ → DStrM G s) (c0 : ℕ) {p : ℕ}
    (c : LoopCfgD G s Φ p) (Bi : WLab G s) (Dc1 : DStrM G s) (B'i : WLab G s)
    (Ui : Finset (Fin G.n)) (Dci : DStrM G s) (d1 : Labels G s) (φ1 : Φ) (g2 : DGl G s)
    (H : Hist G) (r : State ℝ≥0) : Prop where
  lvl : r.w "lvl" = l + 1
  lvl_le : l + 1 ≤ LF
  stat : Static r G LF body τf Mf
  lab : LabAt r d1 H c0
  D : DL.DR r H g2 (Function.update (Function.update Ds (l + 1) Dc1) l Dci) l
  phi : PI.PhiR r φ1
  -- the child's result (level `l`)
  Urow : SetRow r "U" "U.len" l Ui
  sBpi : SlotHolds r (slotBp l) H (vc r) B'i
  ptrUi : ∀ u ∈ Ui, PtrOK r d1 Bi u
  clr : Clear r G.n l
  -- the level-`(l+1)` data of `c` (untouched by the first half)
  grp : GrpRep r (l + 1) G.n p (liftP c.cs.P) (liftPiv c.cs.piv)
  np : NpRep r (l + 1) p
  U : SetRow r "U" "U.len" (l + 1) c.cs.U
  inU : ∀ v : Fin G.n, r.wa "sp.inU" ((l + 1) * G.n + v) = if v ∈ c.cs.U then 1 else 0
  sB : SlotHolds r (slotB (l + 1)) H (vc r) B
  sBp : SlotHolds r (slotBp (l + 1)) H (vc r) c.cs.B'
  sBi : SlotHolds r (slotBi (l + 1)) H (vc r) Bi
  tau : r.wa "cp.tau" (l + 1) = τl
  ptr : ∀ u ∈ c.cs.U, PtrOK r c.cs.d B u
  ptrFr : ∀ x : Fin G.n, x ∉ c.cs.U → x ∉ Ui → r.wa "sp.ptr" x = st0.wa "sp.ptr" x
  frame : LFrame st0 r G.n l

end postCall

end Frontier.CHD.RamSpine
