import Frontier.CHD.SpineIter
import Frontier.CHD.SpineA
import Frontier.CHD.BaseHeap
import Frontier.CHD.SpineLoopW

/-!
# SpineFirst — the first half of an iteration (agent-08, B-L4, NON-GATE)

`childReset; pull; loadBi; expand; copyChild; lvlDn; call P_bmssp; lvlUp` from `LoopRep` to
`PostCall`.  This file: the frame lemmas.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamSpine

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.RamLevel
  Frontier.CHD.BM Frontier.CHD.RamBaseCase Frontier.CHD.LabTab WExpr Stmt

variable {G : Graph} {s : Fin G.n}


/-! ## Every run keeps the capacity and the procedure table -/

section capProcs

variable {V : Type} {ops : VOps V}

theorem exec_cap_procs : ∀ (f : ℕ) (c : Stmt) (s r : State V), exec ops f c s = some r →
    r.cap = s.cap ∧ r.procs = s.procs
  | 0, _, _, _, h => by simp [exec] at h
  | f + 1, c, s, r, h => by
    cases c with
    | skip => simp [exec] at h; subst h; simp [State.charge]
    | wset x e =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨a, _, h⟩ := h; simp at h; subst h; simp [State.charge, State.setW]
    | vset x e =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨a, _, h⟩ := h; simp at h; subst h; simp [State.charge, State.setV]
    | vle x a b =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨p, _, q, _, bit, _, h⟩ := h; simp at h; subst h; simp [State.charge, State.setW]
    | wstore arr i e =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨j, _, a, _, h⟩ := h
      split_ifs at h; simp at h; subst h; simp [State.charge, State.storeW]
    | vstore arr i e =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨j, _, a, _, h⟩ := h
      split_ifs at h; simp at h; subst h; simp [State.charge, State.storeV]
    | walloc arr e =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨k, _, h⟩ := h; simp at h; subst h; simp [State.charge, State.allocW]
    | valloc arr e =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨k, _, h⟩ := h; simp at h; subst h; simp [State.charge, State.allocV]
    | seq a b =>
      rw [exec_seq, Option.bind_eq_some_iff] at h
      obtain ⟨s', h1, h2⟩ := h
      obtain ⟨e1, e2⟩ := exec_cap_procs f a s s' h1
      obtain ⟨e3, e4⟩ := exec_cap_procs f b s' r h2
      exact ⟨e3.trans e1, e4.trans e2⟩
    | ite c a b =>
      rw [exec_ite, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, h2⟩ := h
      split_ifs at h2
      · obtain ⟨e1, e2⟩ := exec_cap_procs f a _ r h2; exact ⟨e1, e2⟩
      · obtain ⟨e1, e2⟩ := exec_cap_procs f b _ r h2; exact ⟨e1, e2⟩
    | «while» c b =>
      rw [exec_while, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, h2⟩ := h
      split_ifs at h2
      · rw [Option.bind_eq_some_iff] at h2
        obtain ⟨s', h3, h4⟩ := h2
        obtain ⟨e1, e2⟩ := exec_cap_procs f b _ s' h3
        obtain ⟨e3, e4⟩ := exec_cap_procs f (.while c b) s' r h4
        exact ⟨e3.trans e1, e4.trans e2⟩
      · simp at h2; subst h2; simp [State.charge]
    | call p =>
      rw [exec_call] at h
      cases hp : s.procs[p]? with
      | none => rw [hp] at h; exact absurd h (by simp)
      | some body =>
        rw [hp] at h
        obtain ⟨e1, e2⟩ := exec_cap_procs f body _ r h; exact ⟨e1, e2⟩

/-- Every `Runs` postcondition may be strengthened by the capacity and the procedure table. -/
theorem Runs.cap_procs {c : Stmt} {st : State V} {Q : State V → Prop} (h : Runs ops c st Q) :
    Runs ops c st (fun r => Q r ∧ r.cap = st.cap ∧ r.procs = st.procs) := by
  obtain ⟨f, r, h1, hQ⟩ := h
  exact ⟨f, r, h1, hQ, exec_cap_procs f c st r h1⟩

end capProcs

/-! ## The empty heap -/

theorem hrl_of_heapEmpty {st : State ℝ≥0} (h : HeapEmpty st G.n) (key : Labels G s) :
    RamBaseCase.HRL st ∅ key := by
  obtain ⟨h0, hA, hP, hz⟩ := h
  exact ⟨0, h0, Nat.zero_le _, hA, hP, ⟨fun i hi => absurd hi (Nat.not_lt_zero _),
    fun v hv hne => absurd (hz v hv) hne⟩, fun i _ hi => absurd hi (Nat.not_lt_zero _),
    by simp [IHeap.T]⟩

/-! ## Row-local preservation -/

section rowFrames

variable {V : Type}

/-- The group table of row `l` only depends on row `l` of the group arrays. -/
theorem grpRep_of_rows {st r : State V} {l n p : ℕ} {P : ℕ → Finset ℕ} {piv : ℕ → ℕ}
    (h : GrpRep st l n p P piv)
    (hrow : ∀ a ∈ grpArrs, ∀ i, l * n ≤ i → i < (l + 1) * n → r.wa a i = st.wa a i)
    (hwl : ∀ a ∈ grpArrs, r.wlen a = st.wlen a) : GrpRep r l n p P piv := by
  have hln : (l + 1) * n = l * n + n := Nat.succ_mul l n
  have hp := h.p_le
  have row : ∀ a ∈ grpArrs, ∀ x < n, r.wa a (l * n + x) = st.wa a (l * n + x) :=
    fun a ha x hx => hrow a ha _ (Nat.le_add_right _ _) (by omega)
  have e2 : ∀ j < p, gs r l n j = gs st l n j := fun j hj => row "sp.gs" (by simp [grpArrs]) j (by omega)
  have e3 : ∀ j < p, gl r l n j = gl st l n j := fun j hj => row "sp.gl" (by simp [grpArrs]) j (by omega)
  have e1 : ∀ q < n, gmem r l n q = gmem st l n q := fun q hq => row "sp.gm" (by simp [grpArrs]) q hq
  have hseg := h.seg
  refine ⟨by rw [hwl _ (by simp [grpArrs])]; exact h.len_gm, by rw [hwl _ (by simp [grpArrs])]; exact h.len_gs,
    by rw [hwl _ (by simp [grpArrs])]; exact h.len_gl, by rw [hwl _ (by simp [grpArrs])]; exact h.len_gp,
    by rw [hwl _ (by simp [grpArrs])]; exact h.len_gpos, by rw [hwl _ (by simp [grpArrs])]; exact h.len_g,
    h.p_le, fun j hj => by rw [e2 j hj, e3 j hj]; exact h.seg j hj, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj q hq
    rw [e3 j hj] at hq
    have := hseg j hj
    rw [e2 j hj, e1 _ (by omega)]; exact h.mem_lt j hj q hq
  · intro j hj q hq
    rw [e3 j hj] at hq
    have := hseg j hj
    have hm := h.mem_lt j hj q hq
    rw [e2 j hj, e1 _ (by omega), row "sp.gpos" (by simp [grpArrs]) _ hm]; exact h.pos j hj q hq
  · intro j hj q hq
    rw [e3 j hj] at hq
    have := hseg j hj
    have hm := h.mem_lt j hj q hq
    rw [e2 j hj, e1 _ (by omega), row "sp.g" (by simp [grpArrs]) _ hm]; exact h.memb j hj q hq
  · intro j hj
    rw [h.img j hj, e3 j hj]
    apply Finset.image_congr
    intro q hq
    have := hseg j hj
    rw [Finset.mem_coe, Finset.mem_range] at hq
    simp only [e2 j hj, e1 _ (show gs st l n j + q < n by omega)]
  · intro x hx
    rw [row "sp.g" (by simp [grpArrs]) x hx]; exact h.nomemb x hx
  · intro j hj
    rw [row "sp.gp" (by simp [grpArrs]) j (by omega)]; exact h.pivs j hj
  · intro j hj j' hj' hne
    rw [e2 j hj, e3 j hj, e2 j' hj', e3 j' hj']; exact h.disj j hj j' hj' hne

/-- A row list only depends on its row and its length entry. -/
theorem rowRep_of_rows {st r : State V} {arr len : String} {n l : ℕ} {xs : List ℕ}
    (h : RowRep st arr len n l xs)
    (hrow : ∀ i, l * n ≤ i → i < (l + 1) * n → r.wa arr i = st.wa arr i)
    (hlen : r.wa len l = st.wa len l) (hwl : r.wlen arr = st.wlen arr)
    (hwl' : r.wlen len = st.wlen len) : RowRep r arr len n l xs :=
  h.of_eq hwl hwl' hlen (fun i hi => hrow _ (Nat.le_add_right _ _) (by rw [Nat.succ_mul]; omega))

theorem setRow_of_rows {st r : State ℝ≥0} {arr len : String} {l : ℕ} {X : Finset (Fin G.n)}
    (h : SetRow st arr len l X)
    (hrow : ∀ i, l * G.n ≤ i → i < (l + 1) * G.n → r.wa arr i = st.wa arr i)
    (hlen : r.wa len l = st.wa len l) (hwl : r.wlen arr = st.wlen arr)
    (hwl' : r.wlen len = st.wlen len) : SetRow r arr len l X := by
  obtain ⟨xs, hR, hnd, hm⟩ := h
  exact ⟨xs, rowRep_of_rows hR hrow hlen hwl hwl', hnd, hm⟩

end rowFrames

/-! ## The static facts -/

/-- `Static` only depends on a few registers, the CSR / graph / table / heap arrays, the array
lengths, the procedure table and the capacity. -/
theorem Static.of_frame {st r : State ℝ≥0} {LF : ℕ} {body : Stmt} {τf Mf : ℕ → ℕ}
    (h : Static st G LF body τf Mf) (hwl : r.wlen = st.wlen) (hvl : r.vlen = st.vlen)
    (harr : ∀ a ∈ ["gSt", "gHead", "cp.tau", "cp.M", "hp_P"], r.wa a = st.wa a)
    (hgw : r.va "gW" = st.va "gW")
    (hreg : ∀ z ∈ ["n", "gN", "hp_n"], r.w z = st.w z) (hpr : r.procs = st.procs)
    (hcap : r.cap = st.cap) : Static r G LF body τf Mf := by
  have e1 := harr "gSt" (by simp); have e2 := harr "gHead" (by simp)
  have e3 := harr "cp.tau" (by simp); have e4 := harr "cp.M" (by simp)
  have e5 := harr "hp_P" (by simp)
  obtain ⟨hn, hgN, hgr, hcsr, hpro, hrows, hlens, hslots, hxm, hptr, htau, hMl, htauv, hMv, hheap,
    hcp, hτc, hMc⟩ := h
  obtain ⟨hh, hw⟩ := hgr
  refine ⟨by rw [hreg _ (by simp)]; exact hn, by rw [hreg _ (by simp)]; exact hgN, ⟨?_, ?_⟩, ?_,
    by rw [hpr]; exact hpro, fun a ha => by rw [hwl]; exact hrows a ha,
    fun a ha => by rw [hwl]; exact hlens a ha, fun i hi => ?_, by rw [hwl]; exact hxm,
    by rw [hwl]; exact hptr, by rw [hwl]; exact htau, by rw [hwl]; exact hMl,
    fun l hl => by rw [e3]; exact htauv l hl, fun l hl => by rw [e4]; exact hMv l hl, ?_,
    by rw [hcap]; exact hcp, fun l hl => by rw [hcap]; exact hτc l hl,
    fun l hl => by rw [hcap]; exact hMc l hl⟩
  · obtain ⟨hh1, hh2⟩ := hh
    exact ⟨by rw [hwl]; exact hh1, fun i hi => by rw [e2]; exact hh2 i hi⟩
  · obtain ⟨hw1, hw2⟩ := hw
    exact ⟨by rw [hvl]; exact hw1, fun i hi => by rw [hgw]; exact hw2 i hi⟩
  · obtain ⟨c1, c2, c3, c4⟩ := hcsr
    exact ⟨by rw [hwl]; exact c1, fun u => by rw [e1]; exact c2 u, fun u => by rw [e1]; exact c3 u,
      fun e u => by rw [e1]; exact c4 e u⟩
  · have := hslots i hi
    exact ⟨by rw [hvl]; exact this.l, by rw [hwl]; exact this.h, by rw [hwl]; exact this.v,
      by rw [hwl]; exact this.e, by rw [hwl]; exact this.r, by rw [hwl]; exact this.f⟩
  · obtain ⟨z1, z2, z3, z4⟩ := hheap
    exact ⟨by rw [hreg _ (by simp)]; exact z1, by rw [hwl]; exact z2, by rw [hwl]; exact z3,
      fun v hv => by rw [e5]; exact z4 v hv⟩

/-! ## Program text of the first half -/

/-- BM.10–BM.13 up to the call: child row reset, pull, `B_i` into `KBi`, expansion, child slots,
`lvl := lvl - 1`. -/
def preCall (pull ltBi : Stmt) : Stmt :=
  seq childReset (seq pull (seq loadBi (seq (expand ltBi) (seq copyChild lvlDn))))

/-- The first half of an iteration (BM.10–BM.13). -/
def firstHalf (pull ltBi : Stmt) : Stmt := seq (preCall pull ltBi) (seq (call P_bmssp) lvlUp)

/-! ## Before the call -/

section preCall

variable {T : ℕ → ℕ} {Φ : Type}

/-- The spine's own registers written before the call. -/
def pcBase : List String :=
  ["lvl", "sl.i"] ++ KBi.ws ++ ["sp.bif"] ++ KC.ws ++ ["sp.cf"] ++ expRegs

/-- The registers written before the call. -/
def pcRegs (LW dWR : List String) : List String := pcBase ++ LW ++ dWR

theorem pcBase_sp : ∀ a ∈ pcBase, a ∈ spRegs := by decide

theorem mem_pcRegs {LW dWR : List String} {a : String} :
    a ∈ pcRegs LW dWR ↔ (a ∈ pcBase ∨ a ∈ LW) ∨ a ∈ dWR := by
  simp only [pcRegs, List.mem_append]

theorem spArrs_mem {a : String} (h : a ∈ rowArrs ++ lenArrs ++ slotW ++ ["sp.xm", "sp.ptr", "cp.tau",
    "cp.M", "gSt", "gHead", "gKeep", "gRep", "hp_A", "hp_P"] ++ labW) : a ∈ spArrs := h

/-- **Up to the call** (BM.10–BM.12 + child slots): from the loop representation, the machine
reaches the call entry of the child (level `l`) on the pulled and expanded frontier. -/
theorem preCall_spec (DL : DLayer G s T) (PI : PhiI Φ) {LF : ℕ} {body : Stmt} {τf Mf : ℕ → ℕ}
    {ltBi : Stmt} {CL : ℕ} {LW LV : List String}
    (hLt : ∀ (d : Labels G s) (H : Hist G) (c0 : ℕ) (Bi : WLab G s),
      LtI realOps ltBi (fun st => LabAt st d H c0 ∧ WHolds st KBi "sp.bif" H (vc st) Bi ∧
          1 < st.cap ∧ st.w "n" = G.n)
        (fun v => ∃ h : v < G.n, d ⟨v, h⟩ < Bi) CL LW LV)
    (hLWd : ∀ a ∈ LW, a ∉ DL.dWR) (hLWp : ∀ a ∈ LW, a ∉ PI.pWR)
    (hLWs : ∀ a ∈ LW, a ∉ ["gN", "hp_n", "core.n", "core.s", "core.m"])
    (hDP : ∀ a ∈ DL.dWA, a ∉ PI.pWA) (hDPr : ∀ a ∈ DL.dWR, a ∉ PI.pWR)
    {st : State ℝ≥0} {l : ℕ} {B : WLab G s} {τl : ℕ} {Ds : ℕ → DStrM G s} {H : Hist G} {c0 : ℕ}
    {p : ℕ} {c : LoopCfgD G s Φ p}
    (hrep : LoopRep DL PI LF body τf Mf st (l + 1) B τl Ds H c0 c)
    {ks : List (Fin G.n)} {Bi : WLab G s} {g1 : DGl G s} {Dc1 : DStrM G s} {cp : ℕ}
    (hp : pullC (dlOps G s) (T (l + 1)) c.cs.g c.cs.Dc = (ks, Bi, g1, Dc1, cp)) (hksnd : ks.Nodup)
    (hub : DL.use st + (cp + 1) ≤ DL.ucap) :
    Runs realOps (preCall DL.pull ltBi) st (fun r =>
      CallIn DL PI.PhiR LF body τf Mf r l c.cs.B' Bi (BM.expand c.cs.lit ks.toFinset Bi) c.cs.d c.φ g1
        (Function.update Ds (l + 1) Dc1) H c0 ∧
      SlotHolds r (slotBi (l + 1)) H (vc r) Bi ∧
      Unchanged st r (["S", "S.len", "sp.xm"] ++ slotW ++ DL.dWA) ("sl.l" :: DL.dVA)
        (pcRegs LW DL.dWR) ([KBi.l, KC.l] ++ LV ++ DL.dVR) ∧
      (∀ i, (l + 1) * G.n ≤ i → r.wa "S" i = st.wa "S" i) ∧
      (∀ j, j ≠ l → r.wa "S.len" j = st.wa "S.len" j) ∧
      (∀ i, i ≠ slotBi (l + 1) → i ≠ slotB l → i ≠ slotBlow l →
        r.va "sl.l" i = st.va "sl.l" i ∧ ∀ a ∈ slotW, r.wa a i = st.wa a i) ∧
      r.wa "sp.xm" = st.wa "sp.xm" ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + (DL.K + CL + 70) *
        (1 + cp + ks.length + ((ks.map Fin.val).map (scanW st (l + 1) G.n)).sum) ∧
      DL.use r ≤ DL.use st + (cp + 1)) := by
  classical
  obtain ⟨hlvl, -, hlvle, hstat, hlab, hD, hphi, hgrp, hnp, hU, hinU, hsB, hsBp, htau, hclr,
    hptrU⟩ := hrep
  have hn : st.w "n" = G.n := hstat.n
  have hcapS := hstat.cap
  have hLF1 : l + 1 ≤ LF := hlvle
  have hcS1 : (LF + 3) * G.n + (LF + 3) * G.m + 8 * (LF + 3) < st.cap := by
    have e : (LF + 3) * (G.n + G.m + 8) = (LF + 3) * G.n + (LF + 3) * G.m + 8 * (LF + 3) := by ring
    omega
  have hcN : (l + 1 + 1) * G.n ≤ (LF + 3) * G.n := Nat.mul_le_mul_right _ (by omega)
  have hcN' : (l + 1) * G.n ≤ (l + 1 + 1) * G.n := Nat.mul_le_mul_right _ (by omega)
  have hslL : ∀ i ≤ slotBi (l + 1), SlotLens st i := fun i hi =>
    hstat.slots i (by unfold slotBi at hi; unfold slotB; omega)
  have hSlen : l + 1 - 1 < st.wlen "S.len" := by
    have := hstat.lens "S.len" (by simp [lenArrs]); omega
  have hSl : (l + 1) * G.n ≤ st.wlen "S" := by
    have := hstat.rows "S" (by simp [rowArrs])
    have : (l + 1) * G.n ≤ (LF + 2) * G.n := Nat.mul_le_mul_right _ (by omega)
    omega
  -- 1. the child row reset
  refine runs_seq ((childReset_spec (ops := realOps) st (l := l + 1) (n := G.n) hlvl (by omega) hSlen
    hSl (by omega)).mono ?_)
  rintro r1 ⟨hR1, hU1, hl1, hSL1, hwl1, hc1⟩
  simp only [Nat.add_sub_cancel] at hR1 hSL1
  have hvl1 : r1.vlen = st.vlen := funext fun a => (hU1.varr a (by simp)).2
  have hvc1 : vc (G := G) r1 = vc st := funext fun v => by
    simp only [vc]; rw [(hU1.warr "vcnt" (by simp)).1]
  have hn1 : r1.w "n" = G.n := by rw [hU1.wreg _ (by simp)]; exact hn
  have hD1 : DL.DR r1 H c.cs.g (Function.update Ds (l + 1) c.cs.Dc) (l + 1) :=
    DL.frame st r1 H H _ _ _ ["S.len"] [] ["lvl"] [] hD hU1
      (fun a ha h => DL.dWA_ok a ha (by simp only [List.mem_singleton] at h; subst h; simp [spArrs, lenArrs]))
      (fun _ _ h => absurd h List.not_mem_nil)
      (fun a ha h => DL.dWR_ok a ha (by simp only [List.mem_singleton] at h; subst h; simp [spRegs]))
      (by rw [hvc1]; exact HExt.refl _ _)
  have hsl1 : SlotLens r1 (slotBi (l + 1)) := by
    have h := hslL _ le_rfl
    exact ⟨by rw [hvl1]; exact h.l, by rw [hwl1]; exact h.h, by rw [hwl1]; exact h.v,
      by rw [hwl1]; exact h.e, by rw [hwl1]; exact h.r, by rw [hwl1]; exact h.f⟩
  -- 2. the pull
  have hLab1 : LabAt r1 c.cs.d H c0 := LabAt.of_unchanged hlab hU1 (by decide) (by simp)
    (by rw [hc1]; omega)
  have hu1 : DL.use r1 = DL.use st := DL.use_frame st r1 ["S.len"] [] ["lvl"] [] hU1
    (fun a ha h => DL.dWR_ok a ha (by simp only [List.mem_singleton] at h; subst h; simp [spRegs]))
  refine runs_seq ((DL.pull_spec r1 H c.cs.g (Function.update Ds (l + 1) c.cs.Dc) (l + 1) (by omega)
    hD1 hl1 hn1 (by simpa using hR1) hsl1 hLab1.rep.hist
    (by simp only [Function.update_self, hp]; rw [hu1]; exact hub)).mono ?_)
  rintro r2 ⟨hD2, hR2, hB2, hU2, hS2, hSL2, hsl2, hwl2, hvl2, hc2l, hc2, hu2⟩
  simp only [Function.update_self, hp, Function.update_idem, Nat.add_sub_cancel] at hD2 hR2 hB2 hS2 hSL2 hc2 hu2
  have nD : ∀ z ∈ spRegs, z ∉ DL.dWR := fun z hz h => DL.dWR_ok z h hz
  have nDA : ∀ a ∈ spArrs, a ∉ DL.dWA := fun a ha h => DL.dWA_ok a h ha
  have nDV : ∀ a ∈ "sl.l" :: "gW" :: labV, a ∉ DL.dVA := fun a ha h => DL.dVA_ok a h ha
  have hl2 : r2.w "lvl" = l + 1 := by rw [hU2.wreg _ (nD _ (by simp [spRegs]))]; exact hl1
  have hn2 : r2.w "n" = G.n := by rw [hU2.wreg _ (nD _ (by simp [spRegs]))]; exact hn1
  have hcap2 : r2.cap = st.cap := by rw [hU2.cap, hU1.cap]
  have hsl2' : SlotLens r2 (slotBi (l + 1)) :=
    ⟨by rw [hvl2]; exact hsl1.l, by rw [hwl2]; exact hsl1.h, by rw [hwl2]; exact hsl1.v,
      by rw [hwl2]; exact hsl1.e, by rw [hwl2]; exact hsl1.r, by rw [hwl2]; exact hsl1.f⟩
  -- the arrays not written by the pull (outside D, S, S.len and the slots)
  have hA2 : ∀ a, a ∉ DL.dWA → a ∉ ["S", "S.len"] → a ∉ slotW → r2.wa a = r1.wa a := by
    intro a h1 h2 h3
    refine (hU2.warr a ?_).1
    simp only [List.mem_append, not_or]; exact ⟨⟨h1, h2⟩, h3⟩
  -- 3. `KBi := slot B_i[l+1]`
  refine runs_seq ((loadBi_spec r2 (l := l + 1) hl2 hsl2' hB2 (by rw [hcap2]; omega)).mono ?_)
  rintro r3 ⟨hW3, hU3, hc3⟩
  have hvc3 : vc (G := G) r3 = vc r2 := funext fun v => by
    simp only [vc]; rw [(hU3.warr "vcnt" (by simp)).1]
  have hwl3 : r3.wlen = r2.wlen := funext fun a => (hU3.warr a (by simp)).2
  have hvl3 : r3.vlen = r2.vlen := funext fun a => (hU3.varr a (by simp)).2
  have hl3 : r3.w "lvl" = l + 1 := by rw [hU3.wreg _ (by simp [KBi, LReg.ws])]; exact hl2
  have hn3 : r3.w "n" = G.n := by rw [hU3.wreg _ (by simp [KBi, LReg.ws])]; exact hn2
  have hcap3 : r3.cap = st.cap := by rw [hU3.cap, hcap2]
  -- the group table of level `l + 1` at `r3`
  have hgA : ∀ a ∈ grpArrs, r3.wa a = st.wa a := by
    intro a ha
    have hs : a ∈ spArrs := by
      simp only [grpArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [spArrs, rowArrs]
    rw [(hU3.warr a (by simp)).1, hA2 a (nDA a hs) (by
      simp only [grpArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
      simp only [grpArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      (hU1.warr a (by
        simp only [grpArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)).1]
  have hG3 : GrpRep r3 (l + 1) G.n p (liftP c.cs.P) (liftPiv c.cs.piv) :=
    GrpRep.of_eq hgrp hgA (fun a _ => by rw [hwl3, hwl2, hwl1])
  have hLab2 : LabAt r2 c.cs.d H c0 := LabAt.of_unchanged hLab1 hU2 (by
      intro a ha h
      simp only [List.mem_append] at h
      rcases h with (h | h) | h
      · exact nDA a (by simp [spArrs, ha]) h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> simp [labW] at ha
      · simp [slotW] at h; rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [labW] at ha)
    (by
      intro h
      simp only [List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · exact nDV "dlen" (by simp [labV]) h
      · exact absurd h (by decide)) hc2l
  have hLab3 : LabAt r3 c.cs.d H c0 := LabAt.of_unchanged hLab2 hU3 (by simp) (by simp)
    (by rw [hc3]; omega)
  -- 4. the expansion
  have hks : ∀ x ∈ ks.map Fin.val, x < G.n := by
    intro x hx; obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx; exact w.2
  have hndv : (ks.map Fin.val).Nodup := hksnd.map Fin.val_injective
  have hR3 : RowRep r3 "S" "S.len" G.n (l + 1 - 1) (ks.map Fin.val) := by
    simpa using rowRep_of_unch hR2 hU3 (by simp) (by simp)
  have hxmA : r3.wa "sp.xm" = st.wa "sp.xm" := by
    rw [(hU3.warr "sp.xm" (by simp)).1, hA2 "sp.xm" (nDA _ (by simp [spArrs])) (by decide)
      (by decide), (hU1.warr "sp.xm" (by decide)).1]
  have hxm3 : ∀ x < G.n, r3.wa "sp.xm" x = 0 := fun x hx => by rw [hxmA]; exact hclr.xm x hx
  have hxml3 : G.n ≤ r3.wlen "sp.xm" := by rw [hwl3, hwl2, hwl1]; exact hstat.xm
  have hK3 : LabAt r3 c.cs.d H c0 ∧ WHolds r3 KBi "sp.bif" H (vc r3) Bi ∧ 1 < r3.cap ∧
      r3.w "n" = G.n :=
    ⟨hLab3, by rw [hvc3]; exact hW3, by rw [hcap3]; omega, hn3⟩
  refine runs_seq ((expand_spec (hLt c.cs.d H c0 Bi) r3 hG3 hl3 (by omega) hn3 hR3 hks
    (expList_room hG3 hks hndv) hxm3 hxml3 hK3 (by rw [hcap3]; omega) (by rw [hcap3]; omega)
    (by rw [hcap3]; omega)).mono ?_)
  rintro r4 ⟨hR4, hK4, hl4, hn4, hxm4, hU4, hwl4, hS4, hSL4, hc4l, hc4⟩
  simp only [Nat.add_sub_cancel] at hR4 hS4 hSL4
  have hvl4 : r4.vlen = r3.vlen := funext fun a => (hU4.varr a (by simp)).2
  have hvc4 : vc (G := G) r4 = vc r3 := funext fun v => by
    simp only [vc]; rw [(hU4.warr "vcnt" (by simp)).1]
  have hcap4 : r4.cap = st.cap := by rw [hU4.cap, hcap3]
  have hwl4' : r4.wlen = st.wlen := by rw [hwl4, hwl3, hwl2, hwl1]
  have hvl4' : r4.vlen = st.vlen := by rw [hvl4, hvl3, hvl2, hvl1]
  -- 5. the child slots
  have hbi4 : SlotHolds r4 (slotBi (l + 1)) H (vc r4) Bi := by
    rw [hvc4, hvc3]
    exact (hB2.of_unchanged hU3 (by simp) (by simp)).of_unchanged hU4 (by decide) (by simp)
  have hbp4 : SlotHolds r4 (slotBp (l + 1)) H (vc r4) c.cs.B' := by
    have hne : slotBp (l + 1) ≠ slotBi (l + 1) := by unfold slotBp slotBi; omega
    have h1 := hsBp.of_unchanged hU1 (by decide) (by simp)
    have h2 : SlotHolds r2 (slotBp (l + 1)) H (vc st) c.cs.B' :=
      SlotHolds.of_slot_eq h1 (hsl2 _ hne).1 (hsl2 _ hne).2
    rw [hvc4, hvc3, show vc (G := G) r2 = vc st from ?_]
    · exact (h2.of_unchanged hU3 (by simp) (by simp)).of_unchanged hU4 (by decide) (by simp)
    · funext v; simp only [vc]
      rw [hA2 "vcnt" (nDA _ (by simp [spArrs, labW])) (by decide) (by decide),
        (hU1.warr "vcnt" (by decide)).1]
  refine runs_seq ((copyChild_spec r4 (l := l + 1) hl4 (by omega) (fun i hi => by
      have h := hslL i hi
      exact ⟨by rw [hvl4']; exact h.l, by rw [hwl4']; exact h.h, by rw [hwl4']; exact h.v,
        by rw [hwl4']; exact h.e, by rw [hwl4']; exact h.r, by rw [hwl4']; exact h.f⟩)
    hbi4 hbp4 (by rw [hcap4]; omega)).mono ?_)
  rintro r5 ⟨hsB5, hsBl5, hsl5, hU5, hwl5, hvl5, hc5⟩
  simp only [Nat.add_sub_cancel] at hsB5 hsBl5 hsl5
  have hl5 : r5.w "lvl" = l + 1 := by rw [hU5.wreg _ (by simp [KC, LReg.ws])]; exact hl4
  have hcap5 : r5.cap = st.cap := by rw [hU5.cap, hcap4]
  -- 6. `lvl := l`
  refine runs_wset (a := l) (by
    simp only [lvlDn, evalW_sub', evalW_var, evalW_lit', hl5, Option.bind_some,
      fit_of_lt (show 1 < r5.cap by rw [hcap5]; omega), Nat.add_sub_cancel]) ?_
  set r6 := (r5.setW "lvl" l).charge 1 with hr6
  have hU6 : Unchanged r5 r6 [] [] ["lvl"] [] := unch_setW r5 _ (by simp)
  have hLt0 := hLt c.cs.d H c0 Bi
  -- the combined footprint
  have sWR : ∀ a ∈ pcBase, a ∈ pcRegs LW DL.dWR := fun a ha => mem_pcRegs.2 (Or.inl (Or.inl ha))
  have sLW : ∀ a ∈ LW, a ∈ pcRegs LW DL.dWR := fun a ha => mem_pcRegs.2 (Or.inl (Or.inr ha))
  have sDW : ∀ a ∈ DL.dWR, a ∈ pcRegs LW DL.dWR := fun a ha => mem_pcRegs.2 (Or.inr ha)
  have hUall : Unchanged st r6 (["S", "S.len", "sp.xm"] ++ slotW ++ DL.dWA) ("sl.l" :: DL.dVA)
      (pcRegs LW DL.dWR) ([KBi.l, KC.l] ++ LV ++ DL.dVR) :=
    (((((hU1.mono (by simp) (by simp) (fun a ha => sWR a (by simp at ha; subst ha; simp [pcBase])) (by simp)).trans
      (hU2.mono (fun a ha => by
          simp only [List.mem_append] at ha ⊢
          rcases ha with (h | h) | h
          · exact Or.inr h
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with rfl | rfl <;> simp
          · exact Or.inl (Or.inr h))
        (fun a ha => by
          simp only [List.mem_append, List.mem_singleton] at ha ⊢
          rcases ha with h | rfl
          · exact List.mem_cons_of_mem _ h
          · exact List.mem_cons_self)
        sDW (fun a ha => by simp only [List.mem_append]; exact Or.inr ha))).trans
      (hU3.mono (by simp) (by simp) (fun a ha => sWR a (by
          simp only [KBi, LReg.ws, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [pcBase, KBi, LReg.ws]))
        (fun a ha => by simp at ha; subst ha; simp))).trans
      (hU4.mono (fun a ha => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl <;> simp) (by simp)
        (fun a ha => by
          rcases List.mem_append.1 ha with h | h
          · exact sWR a (by simp only [pcBase, List.mem_append]; exact Or.inr h)
          · exact sLW a h) (fun a ha => by simp only [List.mem_append]; exact Or.inl (Or.inr ha)))).trans
      (hU5.mono (fun a ha => by simp only [List.mem_append]; exact Or.inl (Or.inr ha))
        (fun a ha => by simp at ha; subst ha; simp)
        (fun a ha => sWR a (by
          simp only [KC, LReg.ws, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [pcBase, KC, LReg.ws]))
        (fun a ha => by simp at ha; subst ha; simp [KC]))).trans
      (hU6.mono (by simp) (by simp) (fun a ha => sWR a (by simp at ha; subst ha; simp [pcBase])) (by simp))
  have nWA : ∀ a ∈ spArrs, a ∉ ["S", "S.len", "sp.xm"] → a ∉ slotW →
      a ∉ ["S", "S.len", "sp.xm"] ++ slotW ++ DL.dWA := fun a ha h1 h2 h => by
    simp only [List.mem_append] at h
    rcases h with (h | h) | h
    exacts [h1 h, h2 h, nDA a ha h]
  have hwl6 : r6.wlen = st.wlen := by
    rw [show r6.wlen = r5.wlen from rfl, hwl5, hwl4']
  have hvl6 : r6.vlen = st.vlen := by
    rw [show r6.vlen = r5.vlen from rfl, hvl5, hvl4']
  have hvc6 : vc (G := G) r6 = vc st := funext fun v => by
    simp only [vc]
    rw [(hUall.warr "vcnt" (nWA _ (by simp [spArrs, labW]) (by decide) (by decide))).1]
  have hvc62 : vc (G := G) r6 = vc r2 := by
    rw [hvc6]; funext v; simp only [vc]
    rw [hA2 "vcnt" (nDA _ (by simp [spArrs, labW])) (by decide) (by decide),
      (hU1.warr "vcnt" (by decide)).1]
  have nWR : ∀ z, z ∉ pcBase → z ∉ LW → z ∈ spRegs → z ∉ pcRegs LW DL.dWR := fun z h1 h2 h3 h => by
    rcases mem_pcRegs.1 h with (h | h) | h
    · exact h1 h
    · exact h2 h
    · exact nD z h3 h
  have hc6 : r6.cost = r5.cost + 1 := by simp only [hr6, State.charge_cost, State.setW_cost]
  have hvc64 : vc (G := G) r6 = vc r4 := by
    rw [hvc6]; funext v; simp only [vc]
    rw [(hU4.warr "vcnt" (by simp)).1, (hU3.warr "vcnt" (by simp)).1,
      hA2 "vcnt" (nDA _ (by simp [spArrs, labW])) (by decide) (by decide),
      (hU1.warr "vcnt" (by decide)).1]
  have labNot : ∀ a ∈ labW, a ∉ ["S", "S.len", "sp.xm"] ∧ a ∉ slotW := by decide
  have labSp : ∀ a ∈ labW, a ∈ spArrs := fun a ha => by simp [spArrs, ha]
  -- the footprint from `r2` (after the pull)
  have hU26 : Unchanged r2 r6 (["S", "S.len", "sp.xm"] ++ slotW) ["sl.l"] (pcRegs LW [])
      ([KBi.l, KC.l] ++ LV) := by
    have sWR' : ∀ a ∈ pcBase, a ∈ pcRegs LW [] := fun a ha => mem_pcRegs.2 (Or.inl (Or.inl ha))
    exact (((hU3.mono (by simp) (by simp) (fun a ha => sWR' a (by
          simp only [KBi, LReg.ws, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [pcBase, KBi, LReg.ws]))
        (fun a ha => by simp at ha; subst ha; simp)).trans
      (hU4.mono (fun a ha => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl <;> simp) (by simp)
        (fun a ha => by
          rcases List.mem_append.1 ha with h | h
          · exact sWR' a (by simp only [pcBase, List.mem_append]; exact Or.inr h)
          · exact mem_pcRegs.2 (Or.inl (Or.inr h))) (fun a ha => by simp only [List.mem_append]; exact Or.inr ha))).trans
      (hU5.mono (fun a ha => by simp only [List.mem_append]; exact Or.inr ha)
        (by simp)
        (fun a ha => sWR' a (by
          simp only [KC, LReg.ws, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [pcBase, KC, LReg.ws]))
        (fun a ha => by simp at ha; subst ha; simp [KC]))).trans
      (hU6.mono (by simp) (by simp) (fun a ha => sWR' a (by simp at ha; subst ha; simp [pcBase])) (by simp))
  have hu26 : DL.use r6 = DL.use r2 := DL.use_frame r2 r6 _ _ _ _ hU26 (fun a ha h => by
    rcases mem_pcRegs.1 h with (h | h) | h
    · exact nD a (pcBase_sp a h) ha
    · exact hLWd a h ha
    · exact absurd h List.not_mem_nil)
  -- the call entry of the child
  have hCI : CallIn DL PI.PhiR LF body τf Mf r6 l c.cs.B' Bi (BM.expand c.cs.lit ks.toFinset Bi)
      c.cs.d c.φ g1 (Function.update Ds (l + 1) Dc1) H c0 := by
    have hstatNot : ∀ a ∈ ["gSt", "gHead", "cp.tau", "cp.M", "hp_P"],
        a ∉ ["S", "S.len", "sp.xm"] ∧ a ∉ slotW := by decide
    refine ⟨by simp [hr6, State.setW, State.charge], by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Static.of_frame hstat hwl6 hvl6
        (fun a ha => (hUall.warr a (nWA a (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp [spArrs])
          (hstatNot a ha).1 (hstatNot a ha).2)).1)
        (hUall.varr "gW" (by
          intro h; simp only [List.mem_cons] at h
          rcases h with h | h
          · exact absurd h (by decide)
          · exact nDV "gW" (by simp) h)).1
        (fun z hz => hUall.wreg z (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl | rfl
          · exact nWR _ (by decide) (fun h => hLt0.regs _ h (by simp)) (by simp [spRegs])
          · exact nWR _ (by decide) (fun h => hLWs _ h (by simp)) (by simp [spRegs])
          · exact nWR _ (by decide) (fun h => hLWs _ h (by simp)) (by simp [spRegs])))
        hUall.procs hUall.cap
    · exact LabAt.of_unchanged hlab hUall
        (fun a ha => nWA a (labSp a ha) (labNot a ha).1 (labNot a ha).2)
        (by
          intro h; simp only [List.mem_cons] at h
          rcases h with h | h
          · exact absurd h (by decide)
          · exact nDV "dlen" (by simp [labV]) h)
        (by omega)
    · exact DL.frame r2 r6 H H g1 _ (l + 1) _ _ _ _ hD2 hU26
        (fun a ha h => by
          simp only [List.mem_append] at h
          rcases h with h | h
          · exact nDA a (by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h
              rcases h with rfl | rfl | rfl <;> simp [spArrs, rowArrs, lenArrs]) ha
          · exact nDA a (by simp [spArrs, h]) ha)
        (fun a ha h => by
          simp only [List.mem_singleton] at h; subst h
          exact nDV "sl.l" (by simp) ha)
        (fun a ha h => by
          rcases mem_pcRegs.1 h with (h | h) | h
          · exact nD a (pcBase_sp a h) ha
          · exact hLWd a h ha
          · exact absurd h List.not_mem_nil)
        (by rw [hvc62]; exact HExt.refl _ _)
    · exact PI.frame st r6 c.φ _ _ _ _ hphi hUall
        (fun a ha h => by
          simp only [List.mem_append] at h
          rcases h with (h | h) | h
          · exact PI.pWA_ok a ha (by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h
              rcases h with rfl | rfl | rfl <;> simp [spArrs, rowArrs, lenArrs])
          · exact PI.pWA_ok a ha (by simp [spArrs, h])
          · exact hDP a h ha)
        (fun a ha h => by
          rcases mem_pcRegs.1 h with (h | h) | h
          · exact PI.pWR_ok a ha (pcBase_sp a h)
          · exact hLWp a h ha
          · exact hDPr a h ha)
    · refine ⟨ks.map Fin.val ++ (ks.map Fin.val).flatMap
        (extOf r3 (l + 1) G.n (fun v => ∃ h : v < G.n, c.cs.d ⟨v, h⟩ < Bi)
          (fun x => x ∈ ks.map Fin.val)), ?_, expList_nodup hG3 hks hndv, fun x =>
        expand_link c.cs.lit hG3 ks Bi (fun v => ⟨fun ⟨_, hv⟩ => hv, fun hv => ⟨v.2, hv⟩⟩) x⟩
      exact rowRep_of_unch (rowRep_of_unch hR4 hU5 (by simp [slotW]) (by simp [slotW])) hU6
        (by simp) (by simp)
    · rw [hvc64]; exact hsB5.of_unchanged hU6 (by simp) (by simp)
    · rw [hvc64]; exact hsBl5.of_unchanged hU6 (by simp) (by simp)
    · refine ⟨fun l' hl' x hx => ?_, fun l' hl' x hx => ?_, fun x hx => ?_⟩
      · rw [(hUall.warr "sp.g" (nWA _ (by simp [spArrs, rowArrs]) (by decide) (by decide))).1]
        exact hclr.g l' (by omega) x hx
      · rw [(hUall.warr "sp.inU" (nWA _ (by simp [spArrs, rowArrs]) (by decide) (by decide))).1]
        exact hclr.inU l' (by omega) x hx
      · rw [show r6.wa = r5.wa from rfl, (hU5.warr "sp.xm" (by decide)).1, hxm4, hxmA]
        exact hclr.xm x hx
  have hne1 : slotBi (l + 1) ≠ slotB l := by unfold slotBi slotB; omega
  have hne2 : slotBi (l + 1) ≠ slotBlow l := by unfold slotBi slotBlow; omega
  have hsx : ((ks.map Fin.val).map (scanW r3 (l + 1) G.n)).sum =
      ((ks.map Fin.val).map (scanW st (l + 1) G.n)).sum := by rw [scanW_of_eq hgA]
  have slotNot : ∀ a ∈ slotW, a ∉ ["S", "S.len", "sp.xm"] ∧ a ∉ ["S.len"] := by decide
  refine ⟨hCI, ?_, hUall, ?_, ?_, ?_, ?_, hwl6, hvl6, ?_, ?_, by rw [hu26, ← hu1]; exact hu2⟩
  · rw [hvc64]
    exact (SlotHolds.of_slot_eq hbi4 (hsl5 _ hne1 hne2).1 (hsl5 _ hne1 hne2).2).of_unchanged hU6
      (by simp) (by simp)
  · intro i hi
    rw [show r6.wa = r5.wa from rfl, (hU5.warr "S" (by decide)).1, hS4 i (Or.inr hi),
      (hU3.warr "S" (by simp)).1, hS2 i (Or.inr hi), (hU1.warr "S" (by decide)).1]
  · intro j hj
    rw [show r6.wa = r5.wa from rfl, (hU5.warr "S.len" (by decide)).1, hSL4 j hj,
      (hU3.warr "S.len" (by simp)).1, hSL2 j hj, hSL1 j hj]
  · intro i h1 h2 h3
    obtain ⟨e1, e2⟩ := hsl5 i h2 h3
    obtain ⟨f1, f2⟩ := hsl2 i h1
    refine ⟨?_, fun a ha => ?_⟩
    · rw [show r6.va = r5.va from rfl, e1, (hU4.varr "sl.l" (by simp)).1,
        (hU3.varr "sl.l" (by simp [KBi])).1, f1, (hU1.varr "sl.l" (by simp)).1]
    · rw [show r6.wa = r5.wa from rfl, e2 a ha, (hU4.warr a (slotNot a ha).1).1,
        (hU3.warr a (by simp)).1, f2 a ha, (hU1.warr a (slotNot a ha).2).1]
  · rw [show r6.wa = r5.wa from rfl, (hU5.warr "sp.xm" (by decide)).1, hxm4, hxmA]
  · omega
  · rw [hsx] at hc4
    simp only [List.length_map] at hc4
    have i1 : DL.K * cp ≤ (DL.K + CL + 70) * cp := Nat.mul_le_mul_right _ (by omega)
    have i2 : ks.length * 18 ≤ (DL.K + CL + 70) * ks.length := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (by omega)
    have i3 : ((ks.map Fin.val).map (scanW st (l + 1) G.n)).sum * (CL + 10) ≤
        (DL.K + CL + 70) * ((ks.map Fin.val).map (scanW st (l + 1) G.n)).sum := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (by omega)
    have e1 : (DL.K + CL + 70) * (1 + cp + ks.length + ((ks.map Fin.val).map (scanW st (l + 1) G.n)).sum) =
        (DL.K + CL + 70) + (DL.K + CL + 70) * cp + (DL.K + CL + 70) * ks.length +
          (DL.K + CL + 70) * ((ks.map Fin.val).map (scanW st (l + 1) G.n)).sum := by ring
    have e2 : DL.K * (cp + 1) = DL.K * cp + DL.K := by ring
    omega

end preCall


/-! ## Weighted continuation totality -/

section iterW

variable {Φ Ω : Type} {ops : DOps G s} {T : ℕ} {DC : DCost} {B : WLab G s}
  {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {p : ℕ} {P0 : Fin p → Finset (Fin G.n)}
  {Q W : Finset (Fin G.n)} {B'0 : WLab G s}

/-- **Weighted continuation totality**: once the pull and the sub-call's outcome are fixed, the
iteration has a weighted outcome covering `Ko` per unit of the pull/expansion work and `K` per
unit of the sub-call's log; the returned set is disjoint from `U`. -/
theorem iterW_of_sub (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W)
    {τ : ℕ → ℕ} {Inv : Φ → Prop} {Mf : ℕ → ℕ} (hMf : ∀ l, ops.mergeM (Mf (l + 1)) (Mf l))
    {subD : SubRelD G s Φ Ω} {subC : SubRelC G s Φ Ω} {l : ℕ}
    (hsimsub : SimSub G s ops τ Inv Mf l subD subC) (hsubC : GoodSub G s τ Inv l subC)
    (hDC : DC.M (l + 1) = Mf (l + 1)) (Ko K : ℕ)
    {f0 : ℕ} {L0 : LiveM G s} {τl : ℕ} (c : LoopCfgD G s Φ p)
    (hA : ALoop ops Inv Mf l B S d0 d1 P0 B'0 f0 L0 c) (hnd : ¬ LoopDoneD τl c)
    {ks : List (Fin G.n)} {Bi : WLab G s} {g1 : DGl G s} {Dc1 : DStrM G s} {cp : ℕ}
    (hp : pullC ops T c.cs.g c.cs.Dc = (ks, Bi, g1, Dc1, cp))
    {B'i : WLab G s} {Ui : Finset (Fin G.n)} {Dci : DStrM G s} {d1' : Labels G s} {φ1 : Φ}
    {g2 : DGl G s} {lg : Log G s Ω}
    (hsubD : subD c.cs.B' Bi (BM.expand c.cs.lit ks.toFinset Bi) c.cs.d c.φ g1 (B'i, Ui, Dci, d1') φ1
      g2 lg) :
    ∃ c' kw, IterRelW (Ω := Ω) ops T subD B τl Ko K c c' kw ∧
      Ko * (1 + cp + (ks.toFinset.card + ∑ j ∈ pulledGroups c.cs.lit ks.toFinset, (c.cs.P j).card)) +
        K * lg.cost ≤ kw ∧ Disjoint Ui c.cs.U := by
  classical
  obtain ⟨hcard', hne⟩ := not_or.mp hnd
  have hcard : c.cs.U.card ≤ τl := not_lt.mp hcard'
  obtain ⟨lUi, hlUnd, hlU⟩ : ∃ lU : List (Fin G.n), lU.Nodup ∧ lU.toFinset = Ui :=
    ⟨Ui.toList, Finset.nodup_toList _, Finset.toList_toFinset _⟩
  obtain ⟨L', hnd', hmem⟩ : ∃ L : List (Fin G.m), L.Nodup ∧ ∀ e, e ∈ L ↔
      G.src e ∈ Ui ∧ Bi ≤ ext (d1' (G.src e)) e ∧ ext (d1' (G.src e)) e < B :=
    ⟨(Finset.univ.filter fun e => G.src e ∈ Ui ∧ Bi ≤ ext (d1' (G.src e)) e ∧
        ext (d1' (G.src e)) e < B).toList, Finset.nodup_toList _, by intro e; simp⟩
  obtain ⟨piv', hres⟩ := exists_reselect c.cs.lit Ui (L'.foldl (relaxInsCc ops T B (some Bi))
    ⟨d1', (delC g2 lUi).1, (ops.merge T Dc1 Dci).1, 0⟩).d
  obtain ⟨lres, hlresnd, hlres⟩ : ∃ lr : List (Fin G.n), lr.Nodup ∧
      lr.toFinset = reselected c.cs.lit Ui piv' :=
    ⟨_, Finset.nodup_toList _, Finset.toList_toFinset _⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hUi_disj, -, -⟩ :=
    stepD_inv (T := T) (DC := DC) (g0 := ⟨L0, f0⟩) hpre hfp hMf hsimsub hsubC hDC hA.linv hA.inv
      hA.sinv hA.M hA.kinj hA.chg hA.touch hne hp hsubD hlU hnd' hmem hres hlres
  refine ⟨_, _, ⟨ks, Bi, g1, Dc1, cp, B'i, Ui, Dci, d1', g2, lUi, L', piv', lres, lg, φ1, hcard, hne,
    hp, hsubD, hlUnd, hlU, hnd', hmem, hres, hlresnd, hlres, rfl, rfl⟩, ?_, hUi_disj⟩
  have h1 : 1 + cp + (ks.toFinset.card + ∑ j ∈ pulledGroups c.cs.lit ks.toFinset, (c.cs.P j).card) ≤
      iterCostD ops T B c.cs ks.toFinset cp Bi Ui Dc1 Dci d1' g2 lUi L' lres +
        (ops.merge T Dc1 Dci).2 := by
    simp only [iterCostD]; omega
  have := Nat.mul_le_mul_left Ko h1
  omega

end iterW

/-! ## The whole first half -/

section firstHalf

variable {T : ℕ → ℕ} {Φ Ω : Type} {B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s}
  {p : ℕ} {P0 : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {B'0 : WLab G s}

theorem PtrOK.of_eq {st r : State ℝ≥0} {d : Labels G s} {B : WLab G s} {u : Fin G.n}
    (h : PtrOK st d B u) (h1 : r.wa "gSt" = st.wa "gSt") (h2 : r.wa "sp.ptr" u = st.wa "sp.ptr" u) :
    PtrOK r d B u := by
  unfold PtrOK at h ⊢; rw [h1, h2]; exact h

/-- **The first half of an iteration** (BM.10–BM.13): from the loop representation, the pull, the
expansion and the recursive call on the expanded frontier lead to `PostCall`. -/
theorem firstHalf_spec (DL : DLayer G s T) (PI : PhiI Φ) {LF : ℕ} {body : Stmt} {τf Mf : ℕ → ℕ}
    {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} {DCb : DCost} {K Sl : ℕ} {Sb : ℕ → ℕ} {l : ℕ}
    (hIH : CallSpec DL PI.PhiR Inv FPC DCb Mf τf LF body K Sl Sb l)
    {ltBi : Stmt} {CL : ℕ} {LW LV : List String}
    (hLt : ∀ (d : Labels G s) (H : Hist G) (c0 : ℕ) (Bi : WLab G s),
      LtI realOps ltBi (fun st => LabAt st d H c0 ∧ WHolds st KBi "sp.bif" H (vc st) Bi ∧
          1 < st.cap ∧ st.w "n" = G.n)
        (fun v => ∃ h : v < G.n, d ⟨v, h⟩ < Bi) CL LW LV)
    (hLWd : ∀ a ∈ LW, a ∉ DL.dWR) (hLWp : ∀ a ∈ LW, a ∉ PI.pWR)
    (hLWs : ∀ a ∈ LW, a ∉ ["gN", "hp_n", "core.n", "core.s", "core.m"])
    (hDP : ∀ a ∈ DL.dWA, a ∉ PI.pWA) (hDPr : ∀ a ∈ DL.dWR, a ∉ PI.pWR)
    -- the Layer-A context of the loop
    (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W)
    (hMf : ∀ l, (dlOps G s).mergeM (Mf (l + 1)) (Mf l)) {DC : DCost}
    {subC : SubRelC G s Φ Ω}
    (hsimsub : SimSub G s (dlOps G s) τf Inv Mf l (BMSSPD G s (dlOps G s) FPC DCb T Mf τf l) subC)
    (hsubC : GoodSub G s τf Inv l subC) (hDC : DC.M (l + 1) = Mf (l + 1))
    {f0 : ℕ} {L0 : LiveM G s}
    {st0 st : State ℝ≥0} {τl : ℕ} {Ds : ℕ → DStrM G s} {H : Hist G} {c0 : ℕ}
    {c : LoopCfgD G s Φ p}
    (hrep : LoopRep DL PI LF body τf Mf st (l + 1) B τl Ds H c0 c)
    (hA : ALoop (dlOps G s) Inv Mf l B S d0 d1 P0 B'0 f0 L0 c) (hnd : ¬ LoopDoneD τl c)
    (hfr : LFrame st0 st G.n l)
    (hptr0 : ∀ x : Fin G.n, x ∉ c.cs.U → st.wa "sp.ptr" x = st0.wa "sp.ptr" x)
    (hSb : ∀ ks Bi g1 Dc1 cp, pullC (dlOps G s) (T (l + 1)) c.cs.g c.cs.Dc = (ks, Bi, g1, Dc1, cp) →
      (BM.expand c.cs.lit ks.toFinset Bi).card ≤ Sb l)
    {Ko : ℕ} (hKo : DL.K + CL + 71 ≤ Ko)
    (hbud : ∀ c' kw, IterRelW (Ω := Ω) (dlOps G s) (T (l + 1))
      (BMSSPD G s (dlOps G s) FPC DCb T Mf τf l) B τl Ko K c c' kw → st.cost + kw + Sl ≤ c0 + st.cap)
    (hsubT : TotalSub G s Inv (BMSSPD G s (dlOps G s) FPC DCb T Mf τf l))
    (hubud : ∀ c' ku, IterRelW (Ω := Ω) (dlOps G s) (T (l + 1))
      (BMSSPD G s (dlOps G s) FPC DCb T Mf τf l) B τl 2 2 c c' ku → DL.use st + ku ≤ DL.ucap) :
    Runs realOps (firstHalf DL.pull ltBi) st (fun r => ∃ (ks : List (Fin G.n)) (Bi : WLab G s)
      (g1 : DGl G s) (Dc1 : DStrM G s) (cp : ℕ) (B'i : WLab G s) (Ui : Finset (Fin G.n))
      (Dci : DStrM G s) (d1' : Labels G s) (φ1 : Φ) (g2 : DGl G s) (lg : Log G s Ω) (H' : Hist G),
      pullC (dlOps G s) (T (l + 1)) c.cs.g c.cs.Dc = (ks, Bi, g1, Dc1, cp) ∧
      BMSSPD G s (dlOps G s) FPC DCb T Mf τf l c.cs.B' Bi (BM.expand c.cs.lit ks.toFinset Bi) c.cs.d
        c.φ g1 (B'i, Ui, Dci, d1') φ1 g2 lg ∧
      HExt H (vc st) H' (vc r) ∧
      PostCall DL PI LF body τf Mf st0 l B τl Ds c0 c Bi Dc1 B'i Ui Dci d1' φ1 g2 H' r ∧
      st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + (DL.K + CL + 71) *
        (1 + cp + ks.toFinset.card + ∑ j ∈ pulledGroups c.cs.lit ks.toFinset, (c.cs.P j).card) +
        K * lg.cost ∧
      DL.use r ≤ DL.use st + (cp + 1) + 2 * lg.cost) := by
  classical
  obtain ⟨hcard', hne⟩ := not_or.mp hnd
  rcases hp : pullC (dlOps G s) (T (l + 1)) c.cs.g c.cs.Dc with ⟨ks, Bi, g1, Dc1, cp⟩
  obtain ⟨hsp, hlowdis, hBle, hK1, habove, hksnd⟩ :=
    childPre (T := T (l + 1)) hpre hfp hA.linv hA.sinv hA.kinj hne hp
  have hsw : ((ks.map Fin.val).map (scanW st (l + 1) G.n)).sum =
      ∑ j ∈ pulledGroups c.cs.lit ks.toFinset, (c.cs.P j).card := scanW_sum c.cs.lit hrep.grp ks hksnd
  have hkl : ks.length = ks.toFinset.card := (List.toFinset_card_of_nodup hksnd).symm
  -- the pull's room, from some outcome of the iteration
  have hub : DL.use st + (cp + 1) ≤ DL.ucap := by
    obtain ⟨⟨B'i, Ui, Dci, d1'⟩, φ1, g2, lg, hsubD⟩ :=
      hsubT c.cs.B' Bi (BM.expand c.cs.lit ks.toFinset Bi) c.cs.d c.φ g1 hsp hA.inv hlowdis hBle hK1
        habove
    obtain ⟨c', ku, hR, hk, -⟩ := iterW_of_sub (T := T (l + 1)) (DC := DC) hpre hfp hMf hsimsub
      hsubC hDC 2 2 c hA hnd hp hsubD
    have := hubud c' ku hR
    omega
  refine runs_seq ((preCall_spec DL PI hLt hLWd hLWp hLWs hDP hDPr hrep hp hksnd hub).mono ?_)
  rintro r6 ⟨hCI, hBi6, hU06, hS6, hSL6, hsl6, hxm6, hwl6, hvl6, hc6l, hc6, hu6⟩
  rw [hsw, hkl] at hc6
  have hcap6 : r6.cap = st.cap := hU06.cap
  -- the call
  refine runs_seq ((Runs.cap_procs (hIH r6 c.cs.B' Bi (BM.expand c.cs.lit ks.toFinset Bi) c.cs.d c.φ g1
    (Function.update Ds (l + 1) Dc1) H c0 hsp hA.inv hlowdis hBle hK1 habove (hSb _ _ _ _ _ hp) hCI
    ?_ ?_)).mono ?_)
  · -- the child's budget, from the loop's
    rintro ⟨B'i, Ui, Dci, d1'⟩ φ' g' lg hsub
    obtain ⟨c', kw, hR, hk, -⟩ := iterW_of_sub (T := T (l + 1)) (DC := DC) hpre hfp hMf hsimsub
      hsubC hDC Ko K c hA hnd hp hsub
    have hb := hbud c' kw hR
    have i1 : (DL.K + CL + 70) * (1 + cp + ks.toFinset.card +
        ∑ j ∈ pulledGroups c.cs.lit ks.toFinset, (c.cs.P j).card) ≤
        Ko * (1 + cp + (ks.toFinset.card +
          ∑ j ∈ pulledGroups c.cs.lit ks.toFinset, (c.cs.P j).card)) := by
      rw [show 1 + cp + ks.toFinset.card + ∑ j ∈ pulledGroups c.cs.lit ks.toFinset, (c.cs.P j).card =
        1 + cp + (ks.toFinset.card + ∑ j ∈ pulledGroups c.cs.lit ks.toFinset, (c.cs.P j).card) by ring]
      exact Nat.mul_le_mul_right _ (by omega)
    rw [hcap6]; omega
  · -- the child's room, from the iteration's
    rintro ⟨B'i, Ui, Dci, d1'⟩ φ' g' lg hsub
    obtain ⟨c', ku, hR, hk, -⟩ := iterW_of_sub (T := T (l + 1)) (DC := DC) hpre hfp hMf hsimsub
      hsubC hDC 2 2 c hA hnd hp hsub
    have := hubud c' ku hR
    omega
  · rintro r7 ⟨⟨⟨B'i, Ui, Dci, d1'⟩, φ1, g2, lg, H', hsubD, hHE, hCO, hc7l, hc7, hu7⟩, hcap7, hpr7⟩
    obtain ⟨-, -, -, -, hdisj⟩ := iterW_of_sub (T := T (l + 1)) (DC := DC) hpre hfp hMf hsimsub hsubC
      hDC Ko K c hA hnd hp hsubD
    have nD : ∀ z ∈ spRegs, z ∉ DL.dWR := fun z hz h => DL.dWR_ok z h hz
    have nDA : ∀ a ∈ spArrs, a ∉ DL.dWA := fun a ha h => DL.dWA_ok a h ha
    have nWA : ∀ a ∈ spArrs, a ∉ ["S", "S.len", "sp.xm"] → a ∉ slotW →
        a ∉ ["S", "S.len", "sp.xm"] ++ slotW ++ DL.dWA := fun a ha h1 h2 h => by
      simp only [List.mem_append] at h
      rcases h with (h | h) | h
      exacts [h1 h, h2 h, nDA a ha h]
    have hA6 : ∀ a ∈ spArrs, a ∉ ["S", "S.len", "sp.xm"] → a ∉ slotW → r6.wa a = st.wa a :=
      fun a ha h1 h2 => (hU06.warr a (nWA a ha h1 h2)).1
    have hvc6 : vc (G := G) r6 = vc st := funext fun v => by
      simp only [vc]; rw [hA6 "vcnt" (by simp [spArrs, labW]) (by decide) (by decide)]
    have hl7 : r7.w "lvl" = l := hCO.lvl
    -- `lvl := l + 1`
    have hcapL : l + 2 < st.cap := by
      have h1 := hrep.stat.cap
      have h2 : LF + 3 ≤ (LF + 3) * (G.n + G.m + 8) := Nat.le_mul_of_pos_right _ (by omega)
      have h3 := hrep.lvl_le
      omega
    refine runs_wset (a := l + 1) (by
      rw [evalW_add_of (x := l) (y := 1) (by rw [evalW_var, hl7])
        (evalW_lit_of (by rw [hcap7, hcap6]; omega))
        (by rw [hcap7, hcap6]; omega)]) ?_
    set r8 := (r7.setW "lvl" (l + 1)).charge 1 with hr8
    have hU78 : Unchanged r7 r8 [] [] ["lvl"] [] := unch_setW r7 _ (by simp)
    have hw87 : r8.wa = r7.wa := rfl
    have hvc87 : vc (G := G) r8 = vc r7 := rfl
    have hab := hCO.above
    have hwl7 : r7.wlen = st.wlen := by rw [hab.wlen, hwl6]
    have hvl7 : r7.vlen = st.vlen := by rw [hab.vlen, hvl6]
    have hHE' : HExt H (vc st) H' (vc r8) := by rw [← hvc6, hvc87]; exact hHE
    -- the level-(l+1) rows between `st` and `r7`
    have hrow : ∀ a ∈ rowArrs, a ≠ "S" → ∀ i, (l + 1) * G.n ≤ i → r7.wa a i = st.wa a i := by
      intro a ha haS i hi
      rw [hab.rows a ha i hi, hA6 a (by simp [spArrs, ha]) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro (h | h | h) <;> subst h <;>
          simp_all [rowArrs]) (by
        intro h; simp [slotW] at h; rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [rowArrs] at ha)]
    have hlen : ∀ a ∈ lenArrs, a ≠ "S.len" → ∀ j, l < j → r7.wa a j = st.wa a j := by
      intro a ha haS j hj
      rw [hab.lens a ha j hj, hA6 a (by simp [spArrs, ha]) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro (h | h | h) <;> subst h <;>
          simp_all [lenArrs]) (by
        intro h; simp [slotW] at h; rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [lenArrs] at ha)]
    have hslot : ∀ i, slotB (l + 1) ≤ i → i ≠ slotBi (l + 1) →
        r7.va "sl.l" i = st.va "sl.l" i ∧ ∀ a ∈ slotW, r7.wa a i = st.wa a i := by
      intro i hi hne
      have h1 : i ≠ slotB l := by simp only [slotB] at hi ⊢; omega
      have h2 : i ≠ slotBlow l := by simp only [slotB, slotBlow] at hi ⊢; omega
      obtain ⟨e1, e2⟩ := hsl6 i hne h1 h2
      exact ⟨(hab.slots i hi).1.trans e1, fun a ha => ((hab.slots i hi).2 a ha).trans (e2 a ha)⟩
    have hptr7 : ∀ x : Fin G.n, x ∉ Ui → r7.wa "sp.ptr" x = st.wa "sp.ptr" x := fun x hx => by
      rw [hCO.ptrFr x hx, hA6 "sp.ptr" (by simp [spArrs]) (by decide) (by decide)]
    have hgSt7 : r7.wa "gSt" = st.wa "gSt" := by
      rw [hCO.stArr "gSt" (by simp), hA6 "gSt" (by simp [spArrs]) (by decide) (by decide)]
    have grpRow : ∀ a ∈ grpArrs, a ∈ rowArrs ∧ a ≠ "S" := by decide
    have hwl87 : r8.wlen = st.wlen := by rw [show r8.wlen = r7.wlen from rfl, hwl7]
    have hvl87 : r8.vlen = st.vlen := by rw [show r8.vlen = r7.vlen from rfl, hvl7]
    have hc8 : r8.cost = r7.cost + 1 := by simp only [hr8, State.charge_cost, State.setW_cost]
    have hu8 : DL.use r8 = DL.use r7 := DL.use_frame r7 r8 [] [] ["lvl"] [] hU78
      (fun a ha h => nD a (by simp only [List.mem_singleton] at h; subst h; simp [spRegs]) ha)
    refine ⟨ks, Bi, g1, Dc1, cp, B'i, Ui, Dci, d1', φ1, g2, lg, H', rfl, hsubD, hHE', ?_, by omega, ?_,
      by omega⟩
    · refine ⟨by simp [hr8, State.setW, State.charge], hrep.lvl_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact Static.of_frame hCO.stat rfl rfl (fun a _ => rfl) rfl (fun z hz => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl | rfl <;> simp [hr8, State.setW, State.charge]) rfl rfl
      · exact LabAt.of_unchanged hCO.lab hU78 (by simp) (by simp) (by omega)
      · exact DL.frame r7 r8 H' H' g2 _ l [] [] ["lvl"] [] hCO.D hU78 (by simp) (by simp)
          (fun a ha h => nD a (by simp only [List.mem_singleton] at h; subst h; simp [spRegs]) ha)
          (by rw [hvc87]; exact HExt.refl _ _)
      · exact PI.frame r7 r8 φ1 [] [] ["lvl"] [] hCO.phi hU78 (by simp)
          (fun a ha h => PI.pWR_ok a ha (by simp only [List.mem_singleton] at h; subst h; simp [spRegs]))
      · exact setRow_of_rows hCO.U (fun _ _ _ => rfl) rfl rfl rfl
      · rw [hvc87]; exact hCO.sBp.of_unchanged hU78 (by simp) (by simp)
      · exact fun u hu => PtrOK.of_eq (hCO.ptr u hu) rfl rfl
      · exact ⟨fun l' h x hx => hCO.clr.g l' h x hx, fun l' h x hx => hCO.clr.inU l' h x hx,
          fun x hx => hCO.clr.xm x hx⟩
      · exact grpRep_of_rows hrep.grp (fun a ha i hi _ => by
            rw [hw87]; exact hrow a (grpRow a ha).1 (grpRow a ha).2 i hi)
          (fun a _ => by rw [hwl87])
      · exact ⟨by rw [hwl87]; exact hrep.np.1, by
          rw [hw87, hlen "sp.np" (by simp [lenArrs]) (by decide) (l + 1) (by omega)]; exact hrep.np.2⟩
      · exact setRow_of_rows hrep.U (fun i hi _ => by
            rw [hw87]; exact hrow "U" (by simp [rowArrs]) (by decide) i hi)
          (by rw [hw87]; exact hlen "U.len" (by simp [lenArrs]) (by decide) (l + 1) (by omega))
          (by rw [hwl87]) (by rw [hwl87])
      · intro v
        rw [hw87, hrow "sp.inU" (by simp [rowArrs]) (by decide) _ (Nat.le_add_right _ _)]
        exact hrep.inU v
      · have hne : slotB (l + 1) ≠ slotBi (l + 1) := by unfold slotB slotBi; omega
        exact ((SlotHolds.of_slot_eq hrep.sB (hslot _ le_rfl hne).1 (hslot _ le_rfl hne).2).ext
          hHE').of_unchanged hU78 (by simp) (by simp)
      · have hne : slotBp (l + 1) ≠ slotBi (l + 1) := by unfold slotBp slotBi; omega
        have hle : slotB (l + 1) ≤ slotBp (l + 1) := by unfold slotB slotBp; omega
        exact ((SlotHolds.of_slot_eq hrep.sBp (hslot _ hle hne).1 (hslot _ hle hne).2).ext
          hHE').of_unchanged hU78 (by simp) (by simp)
      · have hle : slotB (l + 1) ≤ slotBi (l + 1) := by unfold slotB slotBi; omega
        rw [hvc87]
        exact ((SlotHolds.of_slot_eq hBi6 (hab.slots _ hle).1 (hab.slots _ hle).2).ext
          hHE).of_unchanged hU78 (by simp) (by simp)
      · rw [hw87, hCO.stArr "cp.tau" (by simp), hA6 "cp.tau" (by simp [spArrs]) (by decide)
          (by decide)]
        exact hrep.tau
      · exact fun u hu => PtrOK.of_eq (hrep.ptr u hu) (by rw [hw87, hgSt7])
          (by rw [hw87, hptr7 u (fun h => Finset.disjoint_left.1 hdisj h hu)])
      · exact fun x hx1 hx2 => by rw [hw87, hptr7 x hx2, hptr0 x hx1]
      · refine ⟨fun i hi1 hi2 => ?_, ?_, fun i hi1 hi2 => ?_, ?_, hfr.above.trans ⟨?_, ?_, ?_, hwl87,
          hvl87⟩, fun a ha => ?_⟩
        · rw [hw87, hab.rows "S" (by simp [rowArrs]) i hi1, hS6 i hi1]; exact hfr.S i hi1 hi2
        · rw [hw87, hab.lens "S.len" (by simp [lenArrs]) (l + 1) (by omega), hSL6 (l + 1) (by omega)]
          exact hfr.Slen
        · rw [hw87, hrow "W" (by simp [rowArrs]) (by decide) i hi1]; exact hfr.W i hi1 hi2
        · rw [hw87, hlen "W.len" (by simp [lenArrs]) (by decide) (l + 1) (by omega)]; exact hfr.Wlen
        · intro a ha i hi
          have hi' : (l + 1) * G.n ≤ i :=
            le_trans (Nat.mul_le_mul_right _ (by omega)) hi
          rw [hw87]
          by_cases haS : a = "S"
          · subst haS; rw [hab.rows "S" ha i hi', hS6 i hi']
          · exact hrow a ha haS i hi'
        · intro a ha j hj
          rw [hw87]
          by_cases haS : a = "S.len"
          · subst haS; rw [hab.lens _ ha j (by omega), hSL6 j (by omega)]
          · exact hlen a ha haS j (by omega)
        · intro i hi
          have h1 : slotB (l + 1) ≤ i := le_trans (by unfold slotB; omega) hi
          have h2 : i ≠ slotBi (l + 1) := by unfold slotB at hi; unfold slotBi; omega
          exact hslot i h1 h2
        · have hS0 : ∀ a ∈ ["gSt", "gHead", "cp.tau", "cp.M", "gKeep", "gRep"],
              a ∈ spArrs ∧ a ∉ ["S", "S.len", "sp.xm"] ∧ a ∉ slotW := by decide
          rw [hw87, hCO.stArr a ha, hA6 a (hS0 a ha).1 (hS0 a ha).2.1 (hS0 a ha).2.2]
          exact hfr.stArr a ha
    · have e : (DL.K + CL + 71) *
          (1 + cp + ks.toFinset.card + ∑ j ∈ pulledGroups c.cs.lit ks.toFinset, (c.cs.P j).card) =
          (DL.K + CL + 70) *
          (1 + cp + ks.toFinset.card + ∑ j ∈ pulledGroups c.cs.lit ks.toFinset, (c.cs.P j).card) +
          (1 + cp + ks.toFinset.card + ∑ j ∈ pulledGroups c.cs.lit ks.toFinset, (c.cs.P j).card) := by
        ring
      omega

end firstHalf

/-! ## The loop test and the charge of a test -/

section loopTest

variable {T : ℕ → ℕ} {Φ : Type}

theorem LoopRep.charge {DL : DLayer G s T} {PI : PhiI Φ} {LF : ℕ} {body : Stmt} {τf Mf : ℕ → ℕ}
    {st : State ℝ≥0} {l : ℕ} {B : WLab G s} {τl : ℕ} {Ds : ℕ → DStrM G s} {H : Hist G} {c0 : ℕ}
    {p : ℕ} {c : LoopCfgD G s Φ p} (h : LoopRep DL PI LF body τf Mf st l B τl Ds H c0 c) (k : ℕ) :
    LoopRep DL PI LF body τf Mf (st.charge k) l B τl Ds H c0 c := by
  have hU := Unchanged.charge st k [] [] [] []
  exact ⟨h.lvl, h.l1, h.lvl_le,
    Static.of_frame h.stat rfl rfl (fun _ _ => rfl) rfl (fun _ _ => rfl) rfl rfl,
    LabAt.of_unchanged h.lab hU (by simp) (by simp) (by simp [State.charge]),
    DL.frame st _ H H _ _ _ [] [] [] [] h.D hU (by simp) (by simp) (by simp) (HExt.refl _ _),
    PI.frame st _ _ [] [] [] [] h.phi hU (by simp) (by simp),
    GrpRep.of_eq h.grp (fun _ _ => rfl) (fun _ _ => rfl), h.np,
    setRow_of_rows h.U (fun _ _ _ => rfl) rfl rfl rfl, h.inU,
    SlotHolds.of_unchanged h.sB hU (by simp) (by simp),
    SlotHolds.of_unchanged h.sBp hU (by simp) (by simp), h.tau,
    ⟨fun l' h' x hx => h.clr.g l' h' x hx, fun l' h' x hx => h.clr.inU l' h' x hx,
      fun x hx => h.clr.xm x hx⟩,
    fun u hu => PtrOK.of_eq (h.ptr u hu) rfl rfl⟩

/-- **BM.9's test** evaluates to a nonzero word exactly on non-final configurations. -/
theorem loopTest_eval {DL : DLayer G s T} {PI : PhiI Φ} {LF : ℕ} {body : Stmt} {τf Mf : ℕ → ℕ}
    {st : State ℝ≥0} {l : ℕ} {B : WLab G s} {τl : ℕ} {Ds : ℕ → DStrM G s} {H : Hist G} {c0 : ℕ}
    {p : ℕ} {c : LoopCfgD G s Φ p} (h : LoopRep DL PI LF body τf Mf st l B τl Ds H c0 c)
    (hem : st.w "sp.em" = 0 ↔ ¬ (c.cs.g.view c.cs.Dc).IsEmpty) :
    ∃ x, evalW st loopTest = some x ∧ (x ≠ 0 ↔ ¬ LoopDoneD τl c) := by
  obtain ⟨xs, hR, hnd, hmem⟩ := h.U
  have hcard : xs.length = c.cs.U.card := by
    rw [← List.toFinset_card_of_nodup hnd]
    have e : xs.toFinset = c.cs.U.map Fin.valEmbedding := by
      ext x
      rw [List.mem_toFinset, hmem, Finset.mem_map]
      simp [Fin.valEmbedding]
    rw [e, Finset.card_map]
  have hl := h.lvl
  have hc1 : 1 < st.cap := by
    have h1 := h.stat.cap
    have h2 : 3 * 8 ≤ (LF + 3) * (G.n + G.m + 8) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have e1 : evalW st (load "cp.tau" (var "lvl")) = some τl := by
    rw [evalW_load_of (j := l) (by rw [evalW_var, hl]) (by have := h.stat.tau; have := h.lvl_le; omega),
      h.tau]
  have e2 : evalW st (load "U.len" (var "lvl")) = some c.cs.U.card := by
    rw [evalW_load_of (j := l) (by rw [evalW_var, hl]) hR.2.2.1, hR.2.2.2.1, hcard]
  have e3 := evalW_lt_of e1 e2 hc1
  have e4 : evalW st (sub (lit 1) (lt (load "cp.tau" (var "lvl")) (load "U.len" (var "lvl")))) =
      some (1 - if τl < c.cs.U.card then 1 else 0) := by
    rw [evalW_sub', evalW_lit', fit_of_lt hc1, e3]; rfl
  have e5 : evalW st (eq (var "sp.em") (lit 0)) = some (if st.w "sp.em" = 0 then 1 else 0) :=
    evalW_eq_of (by rw [evalW_var]) (evalW_lit_of (by omega)) hc1
  refine ⟨(1 - if τl < c.cs.U.card then 1 else 0) * (if st.w "sp.em" = 0 then 1 else 0), ?_, ?_⟩
  · rw [loopTest, evalW_mul', e4, e5]
    simp only [Option.bind_some]
    exact fit_of_lt (a := (1 - if τl < c.cs.U.card then 1 else 0) *
      (if st.w "sp.em" = 0 then 1 else 0)) (by split_ifs <;> omega)
  · unfold LoopDoneD
    rw [not_or, ← hem, not_lt]
    split_ifs with h1 h2 h2 <;> omega

end loopTest

end Frontier.CHD.RamSpine
