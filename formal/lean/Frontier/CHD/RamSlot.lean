import Frontier.CHD.LabRAM

/-!
# Frontier.CHD.RamSlot — label slots of the spine (bounds `B`, `B_low`, `B'`, `B_i` per level)

Owner: agent-08.  NON-GATE.

A *slot* `i` stores a snapshot of a (possibly infinite) label in the arrays `sl.l` (value), `sl.h`,
`sl.v`, `sl.e`, `sl.r` and the finiteness flag `sl.f` (`0` = `⊤`), in agent-02's machine-label
format.  `SlotHolds st i H V b` mirrors B-LAB's `WHolds` (register blocks): the snapshot represents
the walk of `b` for the ghost history `H` and counters `V` (hence stays valid when the history is
extended, `SlotHolds.ext`).  `loadSlot` / `storeSlot` move a snapshot between a slot (index in
register `sl.i`) and a register block.
-/

open scoped ENNReal NNReal

namespace Frontier.RAM.LabRAM

open Frontier.CHD Frontier.CHD.MLab Frontier.CHD.LabTab WExpr Stmt

variable {G : Graph}

/-- Slot `i` holds the machine label `x`. -/
def SlotAt (st : State ℝ≥0) (i : ℕ) (x : MLabel G) : Prop :=
  st.va "sl.l" i = x.len ∧ st.wa "sl.h" i = x.hops ∧ st.wa "sl.v" i = x.v ∧
    st.wa "sl.e" i = encE x.e ∧ st.wa "sl.r" i = x.ver

/-- Slot `i` holds a snapshot of the label `b` (flag `0` iff `b = ⊤`). -/
def SlotHolds {s : Fin G.n} (st : State ℝ≥0) (i : ℕ) (H : Fin G.n → ℕ → List (Fin G.m))
    (V : Fin G.n → ℕ) (b : WLab G s) : Prop :=
  (st.wa "sl.f" i = 0 ↔ b = ⊤) ∧ ∀ q : List (Fin G.m), b = ((toW q : WalkOrd G s) : WLab G s) →
    ∃ x : MLabel G, SlotAt st i x ∧ Rep (s := s) H V x q

/-- The slot arrays. -/
def slotW : List String := ["sl.h", "sl.v", "sl.e", "sl.r", "sl.f"]

theorem SlotHolds.ext {s : Fin G.n} {st : State ℝ≥0} {i : ℕ}
    {H H' : Fin G.n → ℕ → List (Fin G.m)} {V V' : Fin G.n → ℕ} {b : WLab G s}
    (h : SlotHolds st i H V b) (hE : HExt H V H' V') : SlotHolds st i H' V' b := by
  refine ⟨h.1, fun q hq => ?_⟩
  obtain ⟨x, hx, hxq⟩ := h.2 q hq
  exact ⟨x, hx, Rep.ext hxq hE⟩

/-- A slot is kept by every fragment that writes none of the slot arrays. -/
theorem SlotHolds.of_unchanged {s : Fin G.n} {st r : State ℝ≥0} {i : ℕ}
    {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {b : WLab G s}
    {wa va wr vr : List String} (h : SlotHolds st i H V b) (hu : Unchanged st r wa va wr vr)
    (hw : ∀ a ∈ slotW, a ∉ wa) (hv : "sl.l" ∉ va) : SlotHolds r i H V b := by
  have e1 := hu.warr "sl.h" (hw _ (by simp [slotW]))
  have e2 := hu.warr "sl.v" (hw _ (by simp [slotW]))
  have e3 := hu.warr "sl.e" (hw _ (by simp [slotW]))
  have e4 := hu.warr "sl.r" (hw _ (by simp [slotW]))
  have e5 := hu.warr "sl.f" (hw _ (by simp [slotW]))
  have e6 := hu.varr "sl.l" hv
  refine ⟨by rw [e5.1]; exact h.1, fun q hq => ?_⟩
  obtain ⟨x, ⟨h1, h2, h3, h4, h5⟩, hxq⟩ := h.2 q hq
  exact ⟨x, ⟨by rw [e6.1]; exact h1, by rw [e1.1]; exact h2, by rw [e2.1]; exact h3,
    by rw [e3.1]; exact h4, by rw [e4.1]; exact h5⟩, hxq⟩

/-- `K := slot[sl.i]`, `kf := flag[sl.i]` (6 statements). -/
def loadSlot (K : LReg) (kf : String) : Stmt :=
  seq (vset K.l (.load "sl.l" (var "sl.i")))
  (seq (wset K.h (load "sl.h" (var "sl.i")))
  (seq (wset K.v (load "sl.v" (var "sl.i")))
  (seq (wset K.e (load "sl.e" (var "sl.i")))
  (seq (wset K.r (load "sl.r" (var "sl.i")))
       (wset kf (load "sl.f" (var "sl.i")))))))

/-- `slot[sl.i] := K`, `flag[sl.i] := kf` (6 statements). -/
def storeSlot (K : LReg) (kf : String) : Stmt :=
  seq (vstore "sl.l" (var "sl.i") (.var K.l))
  (seq (wstore "sl.h" (var "sl.i") (var K.h))
  (seq (wstore "sl.v" (var "sl.i") (var K.v))
  (seq (wstore "sl.e" (var "sl.i") (var K.e))
  (seq (wstore "sl.r" (var "sl.i") (var K.r))
       (wstore "sl.f" (var "sl.i") (var kf))))))

/-- The slot arrays are long enough for slot `i`. -/
structure SlotLens (st : State ℝ≥0) (i : ℕ) : Prop where
  l : i < st.vlen "sl.l"
  h : i < st.wlen "sl.h"
  v : i < st.wlen "sl.v"
  e : i < st.wlen "sl.e"
  r : i < st.wlen "sl.r"
  f : i < st.wlen "sl.f"

/-- Freshness for `loadSlot`: distinct target registers, none of them `sl.i`. -/
structure SlotFresh (K : LReg) (kf : String) : Prop where
  nd : [K.h, K.v, K.e, K.r, kf, "sl.i"].Nodup

theorem loadSlot_spec {s : Fin G.n} (K : LReg) (kf : String) (hF : SlotFresh K kf)
    (st : State ℝ≥0) {i : ℕ} (hi : st.w "sl.i" = i) (hl : SlotLens st i)
    {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {b : WLab G s}
    (hb : SlotHolds st i H V b) :
    Runs realOps (loadSlot K kf) st (fun r => WHolds r K kf H V b ∧
      Unchanged st r [] [] (kf :: K.ws) [K.l] ∧ r.cost = st.cost + 6) := by
  have hnd := hF.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hnd
  obtain ⟨⟨n12, n13, n14, n15, n16⟩, ⟨n23, n24, n25, n26⟩, ⟨n34, n35, n36⟩, ⟨n45, n46⟩, n56⟩ := hnd
  apply wp_sound
  simp only [loadSlot, wp, evalV_load', evalW_var, evalW_load', State.charge_w, State.charge_wa,
    State.charge_va, State.charge_wlen, State.charge_vlen, State.setV_w, State.setV_wa,
    State.setV_va, State.setV_wlen, State.setV_vlen, State.setW_w, State.setW_wa, State.setW_va,
    State.setW_wlen, State.setW_vlen, hi, hl.l, hl.h, hl.v, hl.e, hl.r, hl.f, ↓reduceIte,
    Option.bind_some, Ne.symm n16, Ne.symm n26, Ne.symm n36, Ne.symm n46, Ne.symm n56]
  refine ⟨⟨?_, fun q hq => ?_⟩, ?_, ?_⟩
  · simp [State.setW, State.setV, State.charge]; exact hb.1
  · obtain ⟨x, ⟨h1, h2, h3, h4, h5⟩, hxq⟩ := hb.2 q hq
    refine ⟨x, ⟨?_, ?_, ?_, ?_, ?_⟩, hxq⟩
    · simp [State.setW, State.setV, State.charge]; exact h1
    · simp [State.setW, State.setV, State.charge, n12, n13, n14, n15]; exact h2
    · simp [State.setW, State.setV, State.charge, n23, n24, n25]; exact h3
    · simp [State.setW, State.setV, State.charge, n34, n35, Ne.symm n23]; exact h4
    · simp [State.setW, State.setV, State.charge, n45, Ne.symm n24, Ne.symm n34]; exact h5
  · refine ⟨fun a _ => ⟨rfl, rfl⟩, fun a _ => ⟨rfl, rfl⟩, fun z hz => ?_, fun z hz => ?_, rfl, rfl⟩
    · simp only [LReg.ws, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      simp [State.setW, State.setV, State.charge, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2]
    · simp only [List.mem_singleton] at hz
      simp [State.setW, State.setV, State.charge, hz]
  · simp [State.setW, State.setV, State.charge]

/-- Slots other than the written one are kept. -/
theorem SlotHolds.of_slot_eq {s : Fin G.n} {st r : State ℝ≥0} {j : ℕ}
    {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {b : WLab G s}
    (h : SlotHolds st j H V b) (hl : r.va "sl.l" j = st.va "sl.l" j)
    (hw : ∀ a ∈ slotW, r.wa a j = st.wa a j) : SlotHolds r j H V b := by
  have e1 := hw "sl.h" (by simp [slotW])
  have e2 := hw "sl.v" (by simp [slotW])
  have e3 := hw "sl.e" (by simp [slotW])
  have e4 := hw "sl.r" (by simp [slotW])
  have e5 := hw "sl.f" (by simp [slotW])
  refine ⟨by rw [e5]; exact h.1, fun q hq => ?_⟩
  obtain ⟨x, ⟨h1, h2, h3, h4, h5⟩, hxq⟩ := h.2 q hq
  exact ⟨x, ⟨by rw [hl]; exact h1, by rw [e1]; exact h2, by rw [e2]; exact h3,
    by rw [e3]; exact h4, by rw [e4]; exact h5⟩, hxq⟩

/-- The five word stores of `storeSlot` (generic value type). -/
def storeSlotW (K : LReg) (kf : String) : Stmt :=
  seq (wstore "sl.h" (var "sl.i") (var K.h))
  (seq (wstore "sl.v" (var "sl.i") (var K.v))
  (seq (wstore "sl.e" (var "sl.i") (var K.e))
  (seq (wstore "sl.r" (var "sl.i") (var K.r))
       (wstore "sl.f" (var "sl.i") (var kf)))))

theorem storeSlot_eq (K : LReg) (kf : String) :
    storeSlot K kf = seq (vstore "sl.l" (var "sl.i") (.var K.l)) (storeSlotW K kf) := rfl

theorem storeSlotW_spec {V : Type} {ops : VOps V} (K : LReg) (kf : String) (st : State V)
    {i : ℕ} (hi : st.w "sl.i" = i) (h1 : i < st.wlen "sl.h") (h2 : i < st.wlen "sl.v")
    (h3 : i < st.wlen "sl.e") (h4 : i < st.wlen "sl.r") (h5 : i < st.wlen "sl.f") :
    Runs ops (storeSlotW K kf) st (fun r => r.wa "sl.h" i = st.w K.h ∧ r.wa "sl.v" i = st.w K.v ∧
      r.wa "sl.e" i = st.w K.e ∧ r.wa "sl.r" i = st.w K.r ∧ r.wa "sl.f" i = st.w kf ∧
      (∀ a j, (a ∉ slotW ∨ j ≠ i) → r.wa a j = st.wa a j) ∧
      r.va = st.va ∧ r.vlen = st.vlen ∧ r.wlen = st.wlen ∧ r.w = st.w ∧ r.v = st.v ∧
      r.cap = st.cap ∧ r.procs = st.procs ∧ r.cost = st.cost + 5) := by
  apply wp_sound
  simp only [storeSlotW, wp, evalW_var, State.charge_w, State.charge_wlen, State.storeW_w,
    State.storeW_wlen, hi, h1, h2, h3, h4, h5, true_and]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun a j haj => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [State.storeW, State.charge]
  · simp [State.storeW, State.charge]
  · simp [State.storeW, State.charge]
  · simp [State.storeW, State.charge]
  · simp [State.storeW, State.charge]
  · rcases haj with ha | hj
    · simp only [slotW, List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
      simp [State.storeW, State.charge, ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2]
    · simp [State.storeW, State.charge, hj]
  · simp only [State.charge_va, State.storeW_va]
  · simp only [State.charge_vlen, State.storeW_vlen]
  · simp only [State.charge_v, State.storeW_v]
  · simp only [State.charge_cap, State.storeW_cap]
  · simp only [State.charge_procs, State.storeW_procs]
  · simp only [State.charge_cost, State.storeW_cost]

theorem storeSlot_spec {s : Fin G.n} (K : LReg) (kf : String) (st : State ℝ≥0) {i : ℕ}
    (hi : st.w "sl.i" = i) (hl : SlotLens st i)
    {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {b : WLab G s}
    (hb : WHolds st K kf H V b) :
    Runs realOps (storeSlot K kf) st (fun r => SlotHolds r i H V b ∧
      (∀ j, j ≠ i → r.va "sl.l" j = st.va "sl.l" j ∧ ∀ a ∈ slotW, r.wa a j = st.wa a j) ∧
      Unchanged st r slotW ["sl.l"] [] [] ∧ r.cost = st.cost + 6) := by
  rw [storeSlot_eq]
  refine runs_seq (runs_vstore (j := i) (a := st.v K.l) (by rw [evalW_var, hi])
    (by rw [evalV_var']) hl.l ?_)
  set s1 := (st.storeV "sl.l" i (st.v K.l)).charge 1 with hs1
  have hs1va : ∀ j, s1.va "sl.l" j = if j = i then st.v K.l else st.va "sl.l" j := by
    intro j
    show (if "sl.l" = "sl.l" ∧ j = i then st.v K.l else st.va "sl.l" j) = _
    by_cases hj : j = i
    · rw [if_pos ⟨rfl, hj⟩, if_pos hj]
    · rw [if_neg (fun h => hj h.2), if_neg hj]
  have hs1va' : ∀ a, a ≠ "sl.l" → s1.va a = st.va a := by
    intro a ha; funext j
    show (if a = "sl.l" ∧ j = i then st.v K.l else st.va a j) = _
    rw [if_neg (fun h => ha h.1)]
  have hs1w : s1.w = st.w := rfl
  have hs1v : s1.v = st.v := rfl
  have hs1wa : s1.wa = st.wa := rfl
  have hs1wl : s1.wlen = st.wlen := rfl
  have hs1vl : s1.vlen = st.vlen := rfl
  have hs1c : s1.cap = st.cap := rfl
  have hs1p : s1.procs = st.procs := rfl
  have hs1cost : s1.cost = st.cost + 1 := rfl
  refine (storeSlotW_spec (ops := realOps) K kf s1 (i := i) (by rw [hs1w]; exact hi)
    (by rw [hs1wl]; exact hl.h) (by rw [hs1wl]; exact hl.v) (by rw [hs1wl]; exact hl.e)
    (by rw [hs1wl]; exact hl.r) (by rw [hs1wl]; exact hl.f)).mono ?_
  rintro r ⟨e1, e2, e3, e4, e5, ef, eva, evl, ewl, ew, ev, ec, ep, ecost⟩
  rw [hs1w] at e1 e2 e3 e4 e5
  refine ⟨⟨?_, fun q hq => ?_⟩, fun j hj => ⟨?_, fun a ha => ?_⟩, ?_, ?_⟩
  · rw [e5]; exact hb.1
  · obtain ⟨x, ⟨h1, h2, h3, h4, h5⟩, hxq⟩ := hb.2 q hq
    exact ⟨x, ⟨by rw [eva, hs1va, if_pos rfl]; exact h1, by rw [e1]; exact h2,
      by rw [e2]; exact h3, by rw [e3]; exact h4, by rw [e4]; exact h5⟩, hxq⟩
  · rw [eva, hs1va, if_neg hj]
  · rw [ef a j (Or.inr hj), hs1wa]
  · refine ⟨fun a ha => ⟨?_, ?_⟩, fun a ha => ⟨?_, ?_⟩, fun z _ => ?_, fun z _ => ?_, ?_, ?_⟩
    · funext j; rw [ef a j (Or.inl ha), hs1wa]
    · rw [ewl, hs1wl]
    · simp only [List.mem_singleton] at ha
      rw [eva, hs1va' a ha]
    · rw [evl, hs1vl]
    · rw [ew, hs1w]
    · rw [ev, hs1v]
    · rw [ec, hs1c]
    · rw [ep, hs1p]
  · rw [ecost, hs1cost]

end Frontier.RAM.LabRAM
