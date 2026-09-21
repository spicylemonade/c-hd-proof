import Frontier.CHD.PtrLoop
import Frontier.CHD.BaseUtil
import Frontier.CHD.SpineLevels
import Frontier.CHD.BaseConvDL
import Frontier.CHD.BaseCostDeg
import Frontier.CHD.IHeapLab

/-!
# Frontier.CHD.BaseCall0 — the level-0 call of the spine (owner agent-03)

**NON-GATE** (B-L4, the base of agent-08's level induction).  The base case program
`baseProg = baseBody heapI ; ptrLoop ; convDL DL.new DL.ins ; clearS`:
* `baseBody` (agent-08, RamBaseCase) with agent-06's IHeap `heapI` refines `BMCost.BaseC`;
* `ptrLoop` (agent-03, PtrLoop) sets the pointers of the returned vertices (agent-02's `ptrSet`);
* `convDL` (agent-03, BaseConvDL) inserts the leftover heap keys into a fresh level-0 structure;
* `clearS` (agent-06, IHeap) empties the heap again (`Static.heap`).

`baseProg_spec`: from `CallIn … st 0 …` and the call budget, one outcome of `BMSSPD … 0`
(= `BaseDH`, via `baseDH_of_baseC`) with `CallOut … st r 0 …`, at cost `≤ K · lg.cost`.
`callSpec_zero`: agent-08's `CallSpec … 0` for the procedure `bmsspProc (baseProg Kh DL) rec`
(SpineLevels; any `rec`): the base of `callSpec_all`.
-/

open scoped ENNReal NNReal


namespace Frontier.CHD.RamSpine

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.RamLevel Frontier.CHD.BM
  Frontier.CHD.RamBaseCase Frontier.CHD.LabTab Frontier.CHD.WinScan WExpr Stmt

variable {G : Graph} {s : Fin G.n}

/-- The CSR range of `u` has length `outdeg u`. -/
theorem CSRAt.deg_eq {st : State ℝ≥0} (h : CSRAt st G) (u : Fin G.n) :
    st.wa "gSt" ((u : ℕ) + 1) - st.wa "gSt" u = BM.outdeg u := by
  classical
  unfold BM.outdeg
  have hm := h.le_m u
  rw [← Finset.card_map Fin.valEmbedding]
  have e : (Finset.univ.filter (fun e : Fin G.m => G.src e = u)).map Fin.valEmbedding =
      Finset.Ico (st.wa "gSt" u) (st.wa "gSt" ((u : ℕ) + 1)) := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ico]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact (h.src e u).mp he
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, by omega⟩, (h.src _ u).mpr ⟨h1, h2⟩, rfl⟩
  rw [e, Nat.card_Ico]

/-- The returned vertices of a base call have finite labels (they are complete and `< B`). -/
theorem baseC_fin {Φ Ω : Type} {DC : DCost} {Blow B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s}
    {φ0 : Φ} {τ : ℕ} {res : Result G s} {lg : Log G s Ω} (hpre : CallPre B S d0)
    (h : BaseC G s DC Blow B S d0 φ0 τ res φ0 lg) : ∀ u ∈ res.2.1, res.2.2.2 u ≠ ⊤ := by
  obtain ⟨st, c, hloop, hU, -, hd, -⟩ := h
  obtain ⟨hB, -⟩ := baseLoop_inv hpre _ _ (baseLoopC_erase hloop) (bInv_init hpre)
  intro u hu
  rw [hU] at hu
  rw [hd, hB.complete u hu]
  exact _root_.ne_top_of_lt (hB.UUK u hu).1

/-- The leftover heap keys of a base call are below the call bound (they are stored keys). -/
theorem baseC_heap_lt {Φ Ω : Type} {DC : DCost} {Blow B : WLab G s} {S : Finset (Fin G.n)}
    {d0 : Labels G s} {φ0 : Φ} {τ : ℕ} {res : Result G s} {lg : Log G s Ω} (hpre : CallPre B S d0)
    (h : BaseC G s DC Blow B S d0 φ0 τ res φ0 lg) {T' : Finset (Fin G.n)}
    (hT' : res.2.2.1 = Dof T' res.2.2.2) : ∀ v ∈ T', res.2.2.2 v < B := by
  obtain ⟨st, c, hloop, -, hD, hd, -⟩ := h
  obtain ⟨hB, -⟩ := baseLoop_inv hpre _ _ (baseLoopC_erase hloop) (bInv_init hpre)
  intro v hv
  have hsv : st.2.1 v = some (res.2.2.2 v) := by rw [← hD, hT', Dof_apply]; simp [hv]
  exact (hB.stored v _ hsv).2

/-- An empty base heap represents `∅` for every key. -/
theorem HeapEmpty.hrl {st : State ℝ≥0} (h : HeapEmpty st G.n) (hcap : 2 * G.n + 3 < st.cap)
    (key : Fin G.n → WLab G s) : IHeapLab.HRL st ∅ key :=
  ⟨by simpa using h.1, h.2.1, h.2.2.1, hcap,
    ⟨fun i hi => absurd hi (by simp), fun v hv hP => absurd (h.2.2.2 v hv) hP⟩,
    fun i hi hin => by simp at hin, by simp [IHeap.T]⟩


section base

variable {T : ℕ → ℕ} {Φ Ω : Type}

/-- **The base case program** (level 0): heap base case, pointers of the returned vertices, the
leftover keys into a fresh level-0 structure, and the heap cleared again. -/
noncomputable def baseProg (Kh : ℕ) (DL : DLayer G s T) : Stmt :=
  seq (baseBody (IHeapLab.heapI G s Kh)) (seq ptrLoop (seq (convDL DL.new DL.ins) IHeap.clearS))

/-- Arrays that the base program never writes (static data, other rows, marks). -/
def baseKeepA : List String :=
  ["gSt", "gHead", "cp.tau", "cp.M", "gKeep", "gRep", "sp.g", "sp.inU", "sp.xm", "S", "W", "sp.gm",
    "sp.gs", "sp.gl", "sp.gp", "sp.gpos", "sp.mk", "S.len", "W.len", "sp.np", "sp.mk.len", "Wp", "Wp.len"]

theorem baseKeepA_ok (Kh : ℕ) : ∀ a ∈ baseKeepA, a ∉ baseWA (IHeapLab.heapI G s Kh) ++ ["sp.ptr"] ∧
    a ∈ spArrs ∧ a ≠ "hp_P" := by
  simp only [baseKeepA, baseWA, IHeapLab.heapI, eWA]; decide

theorem baseWA_sp (Kh : ℕ) : ∀ a ∈ baseWA (IHeapLab.heapI G s Kh) ++ ["sp.ptr"], a ∈ spArrs := by
  simp only [baseWA, IHeapLab.heapI, eWA]; decide

theorem baseVA_sp (Kh : ℕ) : ∀ a ∈ baseVA (IHeapLab.heapI G s Kh) ++ [], a ∈ "sl.l" :: labV := by
  simp only [baseVA, IHeapLab.heapI, eVA]; decide

theorem baseRegs_ok (Kh : ℕ) : ∀ a ∈ ["lvl", "n", "gN"], a ∉ baseWR (IHeapLab.heapI G s Kh) ++ ptrLoopWR := by
  simp only [baseWR, IHeapLab.heapI, eWR]; decide

theorem baseSp_ok (Kh : ℕ) : "sp.ptr" ∉ baseWA (IHeapLab.heapI G s Kh) ∧ "vcnt" ∉ ["sp.ptr"] ∧
    "gW" ∉ baseVA (IHeapLab.heapI G s Kh) ++ [] := by
  simp only [baseWA, baseVA, IHeapLab.heapI, eWA, eVA]; decide

/-- **The level-0 call** (base of the level induction, agent-08's `CallSpec` at `l = 0` up to the
dispatch): from a call entry at level 0 and the call budget, `baseProg` realizes one outcome of
`BMSSPD … 0` (= `BaseDH`) and ends in `CallOut … 0 …`, with `E` units of cost to spare. -/
theorem baseProg_spec (DL : DLayer G s T) (PI : PhiI Φ) {FPC : FPRelC G s Φ Ω} {DCb : DCost}
    {Mf τf : ℕ → ℕ} {LF : ℕ} {body : Stmt} {Kc Sl Kh δ E : ℕ} {Sb : ℕ → ℕ}
    (hM1 : ∀ l, 1 ≤ Mf l) (hM0 : Mf 0 = 1)
    (hbext : (IHeapLab.heapI G s Kh).Cop + 7 ≤ DCb.bext)
    (hbins : 2 * (IHeapLab.heapI G s Kh).Cop + 76 ≤ DCb.bins)
    (hdeg : ∀ u : Fin G.n, BM.outdeg u ≤ δ) (hKh : Sb 0 + δ * τf 0 ≤ Kh)
    (hSl : baseBud (IHeapLab.heapI G s Kh) G (Sb 0) (τf 0) + 110 ≤ Sl)
    (hK : 2 * DL.K + 80 + E ≤ Kc)
    (hDW : ∀ a ∈ baseWR (IHeapLab.heapI G s Kh) ++ ptrLoopWR, a ∉ DL.dWR)
    (hPW : ∀ a ∈ PI.pWR, a ∉ baseWR (IHeapLab.heapI G s Kh) ++ ptrLoopWR ++ DL.dWR)
    (hPA : ∀ a ∈ PI.pWA, a ∉ DL.dWA)
    (st : State ℝ≥0) (Blow B : WLab G s) (S : Finset (Fin G.n)) (d : Labels G s) (φ : Φ)
    (g : DGl G s) (Ds : ℕ → DStrM G s) (H : Hist G) (c0 : ℕ)
    (hpre : CallPre B S d) (hKI : DB.KeyInj g.L (kof G s))
    (hab : ∀ v i a, g.L v = some (i, a) → B ≤ a) (hSb : S.card ≤ Sb 0)
    (hin : CallIn DL PI.PhiR LF body τf Mf st 0 Blow B S d φ g Ds H c0)
    (hbud : ∀ res φ' g' lg, BMSSPD G s (dlOps G s) FPC DCb T Mf τf 0 Blow B S d φ g res φ' g' lg →
      st.cost + Kc * lg.cost + Sl ≤ c0 + st.cap)
    (hbudU : ∀ res φ' g' lg, BMSSPD G s (dlOps G s) FPC DCb T Mf τf 0 Blow B S d φ g res φ' g' lg →
      DL.use st + 2 * lg.cost ≤ DL.ucap) :
    Runs realOps (baseProg Kh DL) st (fun r => ∃ (res : ResultD G s) (φ' : Φ) (g' : DGl G s)
      (lg : Log G s Ω) (H' : Hist G),
      BMSSPD G s (dlOps G s) FPC DCb T Mf τf 0 Blow B S d φ g res φ' g' lg ∧
      HExt H (vc st) H' (vc r) ∧ CallOut DL PI.PhiR LF body τf Mf st r 0 B res φ' g' Ds H' c0 ∧
      st.cost ≤ r.cost ∧ r.cost + E ≤ st.cost + Kc * lg.cost ∧ DL.use r ≤ DL.use st + 2 * lg.cost) := by
  classical
  have hgW : "gW" ∉ DL.dVA := fun h => DL.dVA_ok _ h (by simp)
  obtain ⟨hlvl, -, hstat, hlab, hD, hphi, hS, hsB, -, hclr⟩ := hin
  have hcapS := hstat.cap
  have h3 : 3 * (G.n + G.m + 8) ≤ (LF + 3) * (G.n + G.m + 8) := Nat.mul_le_mul_right _ (by omega)
  have hcapN : 2 * G.n + 3 < st.cap := by omega
  have hm : G.m + 2 ≤ st.cap := by omega
  have hncap : G.n + 2 ≤ st.cap := by omega
  have hτcap : τf 0 + 2 ≤ st.cap := by have := hstat.tauCap 0 (Nat.zero_le _); omega
  -- the static budget: pay it from any Layer-A outcome (totality of the base case)
  obtain ⟨res0, φ0', g0', lg0, hBD0⟩ := baseDH_total (G := G) (s := s) (ops := dlOps G s) (T := T 0)
    (DCb := DCb) (τ := τf) (Mf := Mf) (Φ := Φ) (Ω := Ω) hM1 (Blow := Blow) (φ0 := φ) hpre hKI hab
  have hb0 := hbud res0 φ0' g0' lg0 hBD0
  have hSl' : st.cost + baseBud (IHeapLab.heapI G s Kh) G S.card (τf 0) + 110 ≤ c0 + st.cap := by
    have : baseBud (IHeapLab.heapI G s Kh) G S.card (τf 0) ≤ baseBud (IHeapLab.heapI G s Kh) G (Sb 0) (τf 0) := by
      unfold baseBud
      have := Nat.mul_le_mul_right ((IHeapLab.heapI G s Kh).Cop + 3) (show S.card + 1 ≤ Sb 0 + 1 by omega)
      omega
    omega
  -- 1. the heap base case
  have hHR0 : (IHeapLab.heapI G s Kh).HR st ∅ d := HeapEmpty.hrl hstat.heap hcapN d
  have hsl0 : SlotLens st (slotB 0) := hstat.slots 0 (by simp [slotB])
  have hsl2 : SlotLens st (slotBp 0) := hstat.slots (slotBp 0) (by simp [slotB, slotBp]; omega)
  have hUl : G.n ≤ st.wlen "U" :=
    le_trans (Nat.le_mul_of_pos_left _ (by omega)) (hstat.rows "U" (by simp [rowArrs]))
  have hUll : 0 < st.wlen "U.len" := by have := hstat.lens "U.len" (by simp [lenArrs]); omega
  have htl : 0 < st.wlen "cp.tau" := by have := hstat.tau; omega
  have htau : st.wa "cp.tau" 0 = τf 0 := hstat.tauv 0 (Nat.zero_le _)
  have hdegC : ∀ u : Fin G.n, st.wa "gSt" ((u : ℕ) + 1) - st.wa "gSt" u ≤ δ := fun u => by
    rw [CSRAt.deg_eq hstat.csr u]; exact hdeg u
  have hsz : S.card + δ * τf 0 ≤ (IHeapLab.heapI G s Kh).hsz := by
    show S.card + δ * τf 0 ≤ Kh; omega
  refine runs_seq ((Runs.noAl (by rfl) (baseBody_spec (IHeapLab.heapI G s Kh) (IHeapLab.heapI_ok Kh) DCb
    hbext hbins (Ω := Ω) φ st Blow B S d hpre (τf 0) δ H c0 hlab hstat.graph hstat.csr hHR0 hS hsB hsl0
    hsl2 hlvl hstat.n htl htau hUl hUll hdegC hsz (by omega) hm hcapN hτcap)).mono ?_)
  rintro r1 ⟨⟨res1, lg1, T', H1, hBC, hT', hL1, hext1, hHR1, hUR1, hSBp1, hg1, hcsr1, hU1, hc1l, hc1,
    hFU1, hFL1, hFS1⟩, hwl1, hvl1⟩
  have hcap1 : r1.cap = st.cap := hU1.cap
  -- Layer A: the base record, its cost and the returned vertices' degrees
  obtain ⟨stF, cF, hloop, hUF, -, -, -, -, -, hlg1⟩ := id hBC
  have hlgc : lg1.cost = S.card * (1 + DCb.bins) + cF + 1 := by rw [hlg1]; simp [Log.cost]
  have hdegsum : (∑ u ∈ res1.2.1, (BM.outdeg u + 1)) ≤ cF := by
    have := baseLoopC_deg_le hloop; simpa [hUF] using this
  -- the returned row and its (finite) labels
  obtain ⟨xs, hrow, hxnd, hxmem⟩ := hUR1
  have hxN : ∀ x ∈ xs, x < G.n := fun x hx => by
    obtain ⟨u, -, rfl⟩ := (hxmem x).mp hx; exact u.isLt
  have hxU : ∀ x (hx : x ∈ xs), (⟨x, hxN x hx⟩ : Fin G.n) ∈ res1.2.1 := fun x hx => by
    obtain ⟨u, hu, rfl⟩ := (hxmem x).mp hx; exact hu
  have hfin := baseC_fin hpre hBC
  have hsB1 : SlotHolds r1 (slotB 0) H1 (vc r1) B :=
    (SlotHolds.of_idx hsB (hFS1 _ (by simp [slotB, slotBp])).1 (hFS1 _ (by simp [slotB, slotBp])).2).ext hext1
  have hHR1' : IHeapLab.HRL r1 T' res1.2.2.2 := hHR1
  -- the budget of the pointer pass: from the outcome with the heap's slot order
  obtain ⟨lK0, hnd0, hset0, -, -⟩ := IHeapLab.HRL.slots hHR1'
  obtain ⟨lgD0, hBD1, hcostD0⟩ := baseDH_of_baseC (dlOps G s) (T := T 0) (M0 := Mf 0) (g0 := g) hBC hT'
    hnd0 hset0
  have hb1 := hbud _ _ _ lgD0 hBD1
  have hsumxs : (xs.map (ptrCostOf r1)).sum ≤ 33 * cF := by
    have e1 : (xs.map (ptrCostOf r1)).sum = ∑ u ∈ res1.2.1, (25 * BM.outdeg u + 33) := by
      rw [← List.sum_toFinset _ hxnd]
      have e2 : xs.toFinset = res1.2.1.map Fin.valEmbedding := by
        ext x; simp only [List.mem_toFinset, Finset.mem_map, Fin.valEmbedding_apply]; exact hxmem x
      rw [e2, Finset.sum_map]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      simp only [Fin.valEmbedding_apply, ptrCostOf]
      rw [CSRAt.deg_eq hcsr1 u]
    rw [e1]
    calc ∑ u ∈ res1.2.1, (25 * BM.outdeg u + 33) ≤ ∑ u ∈ res1.2.1, 33 * (BM.outdeg u + 1) :=
          Finset.sum_le_sum (fun u _ => by omega)
      _ = 33 * ∑ u ∈ res1.2.1, (BM.outdeg u + 1) := by rw [Finset.mul_sum]
      _ ≤ 33 * cF := Nat.mul_le_mul_left _ hdegsum
  have hK80 : 80 * lgD0.cost ≤ Kc * lgD0.cost := Nat.mul_le_mul_right _ (by omega)
  -- 2. the pointers of the returned vertices
  refine runs_seq ((Runs.noAl (by rfl) (ptrLoop_spec r1 res1.2.2.2 H1 B hrow hxnd hxN
    (fun x hx => hfin _ (hxU x hx)) hL1 hg1 hcsr1 hsB1 (SlotLens.of_len hsl0 hwl1 hvl1)
    (by rw [hwl1]; exact hstat.ptr) (by rw [hcap1]; exact hncap) (by rw [hcap1]; exact hm)
    (by rw [hcap1]; omega))).mono ?_)
  rintro r2 ⟨⟨hP2, hfr2, hL2, hU2, -, hc2l, hc2⟩, hwl2, hvl2⟩
  have hU12 := hU1.comp hU2
  have hvc2 : vc (G := G) r2 = vc r1 := vc_of_unchanged hU2 (baseSp_ok (G := G) (s := s) Kh).2.1
  have hD1 : DL.DR r2 H1 g Ds 1 := DL.frame st r2 H H1 g Ds 1 _ _ _ _ hD hU12
    (fun a ha h => DL.dWA_ok a ha (baseWA_sp Kh a h))
    (fun a ha h => DL.dVA_ok a ha (by have h' := baseVA_sp Kh a h; simp only [List.mem_cons] at h' ⊢; tauto))
    (fun a ha h => hDW a h ha) (by rw [hvc2]; exact hext1)
  have hlvl2 : r2.w "lvl" = 0 := by rw [hU12.wreg "lvl" (baseRegs_ok Kh "lvl" (by simp))]; exact hlvl
  have hn2 : r2.w "n" = G.n := by rw [hU12.wreg "n" (baseRegs_ok Kh "n" (by simp))]; exact hstat.n
  have hKA := baseKeepA_ok (G := G) (s := s) Kh
  have hM2 : r2.wa "cp.M" 0 = Mf 0 := by
    rw [(hU12.warr "cp.M" (hKA "cp.M" (by simp [baseKeepA])).1).1]; exact hstat.Mv 0 (by omega)
  have hB2 : SlotHolds r2 (slotB 0) H1 (vc r2) B := by
    rw [hvc2]; exact hsB1.of_unchanged hU2 (by simp [slotW]) (by simp)
  have hHR2 : IHeapLab.HRL r2 T' res1.2.2.2 := IHeapLab.HRL.frame hHR1' hU2 (by simp) (by decide)
  have hA : "hp_A" ∉ DL.dWA := fun h => DL.dWA_ok _ h (by decide)
  -- 3. the leftover keys into a fresh level-0 structure
  have hdWR1 : ∀ a ∈ DL.dWR, a ∉ baseWR (IHeapLab.heapI G s Kh) := fun a ha h =>
    hDW a (List.mem_append_left _ h) ha
  have hdWR2 : ∀ a ∈ DL.dWR, a ∉ ptrLoopWR := fun a ha h => hDW a (List.mem_append_right _ h) ha
  have hus2 : DL.use r2 = DL.use st :=
    (DL.use_frame r1 r2 _ _ _ _ hU2 hdWR2).trans (DL.use_frame st r1 _ _ _ _ hU1 hdWR1)
  have hlt : ∀ v ∈ T', res1.2.2.2 v < B := baseC_heap_lt hpre hBC hT'
  have hMl2 : 0 < r2.wlen "cp.M" := by rw [hwl2, hwl1]; have := hstat.Ml; omega
  have hBl2 : SlotLens r2 (slotB 0) := SlotLens.of_len hsl0 (by rw [hwl2, hwl1]) (by rw [hvl2, hvl1])
  have hMc2 : 2 * Mf 0 + 2 < r2.cap := by rw [hU2.cap, hcap1, hM0]; omega
  refine runs_seq ((convDL_spec DL (dframe_of DL) r2 H1 g Ds res1.2.2.2 c0 (Mf 0) B hD1 hL2 hlvl2 hn2 hM2
    hMl2 hMc2 hB2 hBl2 hHR2 hA hlt (fun lK hnd hset => by
      obtain ⟨lgD, hBD, hcD⟩ := baseDH_of_baseC (dlOps G s) (T := T 0) (M0 := Mf 0) (g0 := g) hBC hT'
        hnd hset
      have h1 := hbudU _ _ _ lgD hBD
      have h2 := insManyC_len_le (T 0) res1.2.2.2 lK g (newC (Mf 0) B)
      have hC1 : 1 ≤ lg1.cost := by rw [hlgc]; omega
      rw [hcD] at h1
      rw [hus2]; omega)).mono ?_)
  rintro r3 ⟨lK, hnd, hset, hD3, hL3, hlvl3, hU3, hwl3, hvl3, hc3l, hc3, hus3⟩
  have hHR3 : IHeapLab.HRL r3 T' res1.2.2.2 := IHeapLab.HRL.frame hHR2 hU3
    (fun a ha h => DL.dWA_ok a h (by simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
                                     rcases ha with rfl | rfl <;> decide))
    (fun a ha h => by
      simp only [List.mem_singleton] at ha; subst ha
      rcases List.mem_append.mp h with h | h
      · exact absurd h (by decide)
      · exact DL.dWR_ok _ h (by decide))
  -- 4. the heap is emptied again
  refine (Runs.noAl (by rfl) (IHeap.Runs.cost_lt (IHeapLab.heapI_clear hHR3 res1.2.2.2))).mono ?_
  rintro r ⟨⟨⟨hHR4, hP4, hU4, hc4⟩, hc4l⟩, hwl4, hvl4⟩
  -- the outcome
  obtain ⟨lgD, hBD, hcostD⟩ := baseDH_of_baseC (dlOps G s) (T := T 0) (M0 := Mf 0) (g0 := g) hBC hT'
    hnd hset
  have hU24 := (hU2.comp hU3).comp hU4
  have hU34 := hU3.comp hU4
  have hUall := (hU12.comp hU3).comp hU4
  have hwlA : r.wlen = st.wlen := hwl4.trans (hwl3.trans (hwl2.trans hwl1))
  have hvlA : r.vlen = st.vlen := hvl4.trans (hvl3.trans (hvl2.trans hvl1))
  have hcapA : r.cap = st.cap := hUall.cap
  have hnAw : ∀ a ∈ baseKeepA, a ∉ baseWA (IHeapLab.heapI G s Kh) ++ ["sp.ptr"] ++ DL.dWA ++ ["hp_P"] := by
    intro a ha h
    obtain ⟨h1, h2, h3⟩ := hKA a ha
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact h1 h
      · exact DL.dWA_ok a h h2
    · exact h3 (List.mem_singleton.mp h)
  have hnA : ∀ a ∈ baseKeepA, r.wa a = st.wa a := fun a ha => (hUall.warr a (hnAw a ha)).1
  have hnot34 : ∀ a, a ∈ spArrs → a ≠ "hp_P" → a ∉ DL.dWA ++ ["hp_P"] := by
    intro a ha hP h
    rcases List.mem_append.mp h with h | h
    · exact DL.dWA_ok a h ha
    · exact hP (List.mem_singleton.mp h)
  have hnot24 : ∀ a, a ∈ spArrs → a ≠ "sp.ptr" → a ≠ "hp_P" → a ∉ ["sp.ptr"] ++ DL.dWA ++ ["hp_P"] := by
    intro a ha hp hP h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact hp (List.mem_singleton.mp h)
      · exact DL.dWA_ok a h ha
    · exact hP (List.mem_singleton.mp h)
  have hvcr : vc (G := G) r = vc r1 := by
    rw [vc_of_unchanged hU4 (by decide), vc_of_unchanged hU3 (fun h => DL.dWA_ok _ h (by decide)), hvc2]
  have hnR : ∀ a ∈ ["lvl", "n", "gN"], r.w a = st.w a := fun a ha => by
    refine hUall.wreg a (fun h => ?_)
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact baseRegs_ok Kh a ha h
      · rcases List.mem_append.mp h with h | h
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl <;> exact absurd h (by decide)
        · exact DL.dWR_ok a h (by simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
                                  rcases ha with rfl | rfl | rfl <;> decide)
    · rw [List.mem_singleton] at h; subst h; revert ha; decide
  have hTl : T'.card = lK.length := by rw [← hset, List.toFinset_card_of_nodup hnd]
  have hLI := insManyC_len_le (T 0) res1.2.2.2 lK g (newC (Mf 0) B)
  refine ⟨(res1.1, res1.2.1, (BM.insManyC (dlOps G s) (T 0) res1.2.2.2 lK g (newC (Mf 0) B)).2.1,
    res1.2.2.2), φ, (BM.insManyC (dlOps G s) (T 0) res1.2.2.2 lK g (newC (Mf 0) B)).1, lgD, H1,
    hBD, by rw [hvcr]; exact hext1, ?_, by omega, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- lvl
    · rw [hU4.wreg "lvl" (by decide)]; exact hlvl3
    -- stat
    · exact {
        n := by rw [hnR "n" (by simp)]; exact hstat.n
        gN := by rw [hnR "gN" (by simp)]; exact hstat.gN
        graph := graphAt_of_unchanged hUall (hnAw "gHead" (by simp [baseKeepA])) (by
          intro h
          rcases List.mem_append.mp h with h | h
          · rcases List.mem_append.mp h with h | h
            · exact (baseSp_ok (G := G) (s := s) Kh).2.2 h
            · exact hgW h
          · simp at h) hstat.graph
        csr := hstat.csr.of_unchanged hUall (hnAw "gSt" (by simp [baseKeepA]))
        proc := by rw [hUall.procs]; exact hstat.proc
        rows := fun a ha => by rw [hwlA]; exact hstat.rows a ha
        lens := fun a ha => by rw [hwlA]; exact hstat.lens a ha
        slots := fun i hi => SlotLens.of_len (hstat.slots i hi) hwlA hvlA
        xm := by rw [hwlA]; exact hstat.xm
        ptr := by rw [hwlA]; exact hstat.ptr
        tau := by rw [hwlA]; exact hstat.tau
        Ml := by rw [hwlA]; exact hstat.Ml
        tauv := fun l hl => by rw [hnA "cp.tau" (by simp [baseKeepA])]; exact hstat.tauv l hl
        Mv := fun l hl => by rw [hnA "cp.M" (by simp [baseKeepA])]; exact hstat.Mv l hl
        heap := ⟨by simpa using hHR4.1, hHR4.2.1, hHR4.2.2.1, hP4⟩
        cap := by rw [hcapA]; exact hstat.cap
        tauCap := fun l hl => by rw [hcapA]; exact hstat.tauCap l hl
        MCap := fun l hl => by rw [hcapA]; exact hstat.MCap l hl }
    -- lab
    · exact hL3.of_unchanged hU4 (by decide) (by simp) (by omega)
    -- D
    · exact DL.frame r3 r H1 H1 _ _ 0 _ _ _ _ hD3 hU4
        (fun a ha h => DL.dWA_ok a ha (by rw [List.mem_singleton] at h; subst h; decide))
        (fun a _ h => by simp at h)
        (fun a ha h => DL.dWR_ok a ha (by rw [List.mem_singleton] at h; subst h; decide))
        (by rw [vc_of_unchanged hU4 (by decide)]; exact HExt.refl _ _)
    -- phi
    · refine PI.frame st r φ _ _ _ _ hphi hUall (fun a ha h => ?_) (fun a ha h => ?_)
      · have hsp : a ∉ spArrs := PI.pWA_ok a ha
        rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with h | h
          · exact hsp (baseWA_sp Kh a h)
          · exact hPA a ha h
        · rw [List.mem_singleton] at h; subst h; exact hsp (by decide)
      · have hsp : a ∉ spRegs := PI.pWR_ok a ha
        rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with h | h
          · exact hPW a ha (List.mem_append_left _ h)
          · rcases List.mem_append.mp h with h | h
            · exact hsp (by simp only [convRegs, List.mem_cons, List.not_mem_nil, or_false] at h
                            rcases h with rfl | rfl | rfl <;> decide)
            · exact hPW a ha (List.mem_append_right _ h)
        · rw [List.mem_singleton] at h; subst h; exact hsp (by decide)
    -- U
    · have hUR : URow r1 res1.2.1 := ⟨xs, hrow, hxnd, hxmem⟩
      exact hUR.of_unchanged hU24 (hnot24 "U" (by decide) (by decide) (by decide))
        (hnot24 "U.len" (by decide) (by decide) (by decide))
    -- sBp
    · rw [hvcr]
      exact hSBp1.of_unchanged hU24 (fun a ha => hnot24 a (by
          simp only [slotW, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide)
          (by simp only [slotW, List.mem_cons, List.not_mem_nil, or_false] at ha
              rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide)
          (by simp only [slotW, List.mem_cons, List.not_mem_nil, or_false] at ha
              rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide))
        (by
          intro h
          rcases List.mem_append.mp h with h | h
          · rcases List.mem_append.mp h with h | h
            · simp at h
            · exact DL.dVA_ok _ h (by simp)
          · simp at h)
    -- ptr
    · intro u hu
      have hx : (u : ℕ) ∈ xs := (hxmem u).mpr ⟨u, hu, rfl⟩
      have h := hP2 u hx
      have e1 := (hU34.warr "gSt" (hnot34 "gSt" (by decide) (by decide))).1
      have e2 := (hU34.warr "sp.ptr" (hnot34 "sp.ptr" (by decide) (by decide))).1
      have := PtrAt.of_eq h e1 (by rw [e2])
      exact this
    -- ptrFr
    · intro x hx
      have hx' : (x : ℕ) ∉ xs := fun h => by
        obtain ⟨u, hu, e⟩ := (hxmem x).mp h
        exact hx (by rw [show x = u from Fin.ext e.symm]; exact hu)
      rw [(hU34.warr "sp.ptr" (hnot34 "sp.ptr" (by decide) (by decide))).1, hfr2 x hx',
        (hU1.warr "sp.ptr" (baseSp_ok (G := G) (s := s) Kh).1).1]
    -- clr
    · exact ⟨fun l' hl' x hx => by rw [hnA "sp.g" (by simp [baseKeepA])]; exact hclr.g l' hl' x hx,
        fun l' hl' x hx => by rw [hnA "sp.inU" (by simp [baseKeepA])]; exact hclr.inU l' hl' x hx,
        fun x hx => by rw [hnA "sp.xm" (by simp [baseKeepA])]; exact hclr.xm x hx⟩
    -- above
    · refine ⟨fun a ha i hi => ?_, fun a ha j hj => ?_, fun i hi => ?_, hwlA, hvlA⟩
      · by_cases hU : a = "U"
        · subst hU
          rw [(hU24.warr "U" (hnot24 "U" (by decide) (by decide) (by decide))).1]
          exact hFU1 i (by omega)
        · rw [hnA a ?_]
          simp only [rowArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
            first | exact absurd rfl hU | simp [baseKeepA]
      · by_cases hU : a = "U.len"
        · subst hU
          rw [(hU24.warr "U.len" (hnot24 "U.len" (by decide) (by decide) (by decide))).1]
          exact hFL1 j (by omega)
        · rw [hnA a ?_]
          simp only [lenArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with h | h | h | h | h | h <;> subst h <;>
            first | exact absurd rfl hU | simp [baseKeepA]
      · have hi2 : i ≠ slotBp 0 := by simp [slotB, slotBp] at hi ⊢; omega
        obtain ⟨e1, e2⟩ := hFS1 i hi2
        refine ⟨?_, fun a ha => ?_⟩
        · rw [(hU24.varr "sl.l" (by
            intro h
            rcases List.mem_append.mp h with h | h
            · rcases List.mem_append.mp h with h | h
              · simp at h
              · exact DL.dVA_ok _ h (by simp)
            · simp at h)).1, e1]
        · have hsw : a ∈ spArrs ∧ a ≠ "sp.ptr" ∧ a ≠ "hp_P" := by
            simp only [slotW, List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide
          rw [(hU24.warr a (hnot24 a hsw.1 hsw.2.1 hsw.2.2)).1, e2 a ha]
    -- stArr
    · intro a ha
      refine hnA a ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with h | h | h | h | h | h <;> subst h <;> simp [baseKeepA]
  · -- cost
    rw [hcostD]
    have hC1 : 0 < lg1.cost := by rw [hlgc]; omega
    have hA1 : (2 * DL.K + 80 + E) * (lg1.cost + (BM.insManyC (dlOps G s) (T 0) res1.2.2.2 lK g
        (newC (Mf 0) B)).2.2) ≤ Kc * (lg1.cost + (BM.insManyC (dlOps G s) (T 0) res1.2.2.2 lK g
        (newC (Mf 0) B)).2.2) := Nat.mul_le_mul_right _ hK
    have hKC : DL.K ≤ DL.K * lg1.cost := Nat.le_mul_of_pos_right _ hC1
    have hEC : E ≤ E * lg1.cost := Nat.le_mul_of_pos_right _ hC1
    have hLK : lK.length * (DL.K + 3) ≤ (BM.insManyC (dlOps G s) (T 0) res1.2.2.2 lK g
        (newC (Mf 0) B)).2.2 * (DL.K + 3) := Nat.mul_le_mul_right _ hLI
    set I := (BM.insManyC (dlOps G s) (T 0) res1.2.2.2 lK g (newC (Mf 0) B)).2.2 with hI
    set C := lg1.cost with hC
    have e1 : (2 * DL.K + 80 + E) * (C + I) = 2 * (DL.K * C) + 80 * C + E * C + 2 * (DL.K * I) +
        80 * I + E * I := by ring
    have e2 : lK.length * (DL.K + 3) = lK.length * DL.K + 3 * lK.length := by ring
    have e3 : I * (DL.K + 3) = DL.K * I + 3 * I := by ring
    have e4 : DL.K * I = DL.K * I := rfl
    rw [hTl] at hc4
    omega
  · -- use
    have hus4 : DL.use r = DL.use r3 := DL.use_frame r3 r _ _ _ _ hU4 (fun a ha h => by
      rw [List.mem_singleton] at h; subst h; exact DL.dWR_ok _ ha (by decide))
    have h2 := insManyC_len_le (T 0) res1.2.2.2 lK g (newC (Mf 0) B)
    have hC1 : 1 ≤ lg1.cost := by rw [hlgc]; omega
    rw [hcostD, hus4]; rw [hus2] at hus3; omega

/-- A base outcome costs at least `1` (its record's cost has the leading `+ 1`). -/
theorem baseDH_cost_pos {ops : DOps G s} {DCb : DCost} {T0 M0 : ℕ} {Blow B : WLab G s}
    {S : Finset (Fin G.n)} {d0 : Labels G s} {φ0 : Φ} {g0 : DGl G s} {τ : ℕ} {res : ResultD G s}
    {φ1 : Φ} {gE : DGl G s} {lg : Log G s Ω}
    (h : BaseDH G s ops DCb T0 M0 Blow B S d0 φ0 g0 τ res φ1 gE lg) : 1 ≤ lg.cost := by
  obtain ⟨st, c, lK, -, -, -, -, -, -, -, -, -, -, hlg⟩ := h
  rw [hlg]; simp only [Log.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega

/-- **`CallSpec` at level 0** (the base of agent-08's level induction `callSpec_all`) for the
procedure `bmsspProc (baseProg Kh DL) rec`, any `rec`: the call's entry and the level test are paid
by `K ≥ 2·DL.K + 82` and the slack. -/
theorem callSpec_zero (DL : DLayer G s T) (PI : PhiI Φ) {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω}
    {DCb : DCost} {Mf τf : ℕ → ℕ} {LF : ℕ} {rec : Stmt} {K Sl Kh δ : ℕ} {Sb : ℕ → ℕ}
    (hM1 : ∀ l, 1 ≤ Mf l) (hM0 : Mf 0 = 1)
    (hbext : (IHeapLab.heapI G s Kh).Cop + 7 ≤ DCb.bext)
    (hbins : 2 * (IHeapLab.heapI G s Kh).Cop + 76 ≤ DCb.bins)
    (hdeg : ∀ u : Fin G.n, BM.outdeg u ≤ δ) (hKh : Sb 0 + δ * τf 0 ≤ Kh)
    (hSl : baseBud (IHeapLab.heapI G s Kh) G (Sb 0) (τf 0) + 112 ≤ Sl)
    (hK : 2 * DL.K + 82 ≤ K)
    (hDW : ∀ a ∈ baseWR (IHeapLab.heapI G s Kh) ++ ptrLoopWR, a ∉ DL.dWR)
    (hPW : ∀ a ∈ PI.pWR, a ∉ baseWR (IHeapLab.heapI G s Kh) ++ ptrLoopWR ++ DL.dWR)
    (hPA : ∀ a ∈ PI.pWA, a ∉ DL.dWA) :
    CallSpec DL PI.PhiR Inv FPC DCb Mf τf LF (bmsspProc (baseProg Kh DL) rec) K Sl Sb 0 := by
  intro st Blow B S d φ g Ds H c0 hpre _ _ _ hKI hab hSb hin hbud hbudU
  refine runs_call_base hin.stat.proc hin.lvl ?_
  set st' := st.enter.charge 1 with hst'
  have hU : Unchanged st st' [] [] [] [] :=
    ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
  have hc' : st'.cost = st.cost + 2 := by simp [hst', State.enter, State.charge]
  have hus' : DL.use st' = DL.use st := DL.use_frame st st' [] [] [] [] hU (by simp)
  have hcap' : st'.cap = st.cap := rfl
  have hstat := hin.stat
  have hin' : CallIn DL PI.PhiR LF (bmsspProc (baseProg Kh DL) rec) τf Mf st' 0 Blow B S d φ g Ds H c0 :=
    ⟨hin.lvl, hin.lvl_le,
      ⟨hstat.n, hstat.gN, graphAt_of_unchanged hU (by simp) (by simp) hstat.graph,
        hstat.csr.of_unchanged hU (by simp), hstat.proc, hstat.rows, hstat.lens,
        fun i hi => SlotLens.of_len (hstat.slots i hi) rfl rfl, hstat.xm, hstat.ptr, hstat.tau, hstat.Ml,
        hstat.tauv, hstat.Mv, hstat.heap, hstat.cap, hstat.tauCap, hstat.MCap⟩,
      hin.lab.of_unchanged hU (by simp) (by simp) (by omega),
      DL.frame st st' H H g Ds _ _ _ _ _ hin.D hU (by simp) (by simp) (by simp) (HExt.refl _ _),
      PI.frame st st' φ _ _ _ _ hin.phi hU (by simp) (by simp), hin.S, hin.sB, hin.sBlow,
      ⟨hin.clr.g, hin.clr.inU, hin.clr.xm⟩⟩
  refine (baseProg_spec DL PI (FPC := FPC) (Kc := K) (Sl := Sl - 2) (E := 2) hM1 hM0 hbext hbins hdeg hKh
    (by omega) (by omega) hDW hPW hPA st' Blow B S d φ g Ds H c0 hpre hKI hab hSb hin'
    (fun res φ' g' lg h => by have := hbud res φ' g' lg h; rw [hc', hcap']; omega)
    (fun res φ' g' lg h => by rw [hus']; exact hbudU res φ' g' lg h)).mono ?_
  rintro r ⟨res, φ', g', lg, H', hB, hE, hO, hc1, hc2, hu⟩
  refine ⟨res, φ', g', lg, H', hB, hE, ⟨hO.lvl, hO.stat, hO.lab, hO.D, hO.phi, hO.U, hO.sBp, hO.ptr,
    hO.ptrFr, hO.clr, ⟨hO.above.rows, hO.above.lens, hO.above.slots, hO.above.wlen, hO.above.vlen⟩,
    hO.stArr⟩, by omega, by omega, by rw [← hus']; exact hu⟩

/-! ## The closed (computable) program text of the base case (agent-10's O30) -/

section closed

/-- agent-06's heap statements (`heapI`'s `push` / `pop` / `top`), closed. -/
def hPushC : Stmt := IHeap.pushOrDecX IHeapLab.lessL
def hPopC : Stmt := IHeap.popS IHeapLab.lessL
def hTopC : Stmt := IHeap.topS

/-- `edgeBody heapI`, closed. -/
def edgeBodyC : Stmt :=
  seq (wset "re" (var "bc.p"))
  (seq (relaxBM KB "bc.bf")
  (seq (ite (var "ok") (seq (wset "hp_x" (load "gHead" (var "bc.p"))) hPushC) skip)
       (wset "bc.p" (add (var "bc.p") (lit 1)))))

/-- `extractBody heapI`, closed. -/
def extractBodyC : Stmt :=
  seq hPopC
  (seq (RamLevel.rowAppend "U" "U.len" (var "hp_v"))
  (seq (wset "ru" (var "hp_v"))
  (seq (wset "bc.p" (load "gSt" (var "hp_v")))
  (seq (wset "bc.pe" (load "gSt" (add (var "hp_v") (lit 1))))
       (.while (lt (var "bc.p") (var "bc.pe")) edgeBodyC)))))

/-- `pushS heapI`, closed. -/
def pushSC : Stmt :=
  seq (wset "bc.k" (lit 0))
  (.while (lt (var "bc.k") (load "S.len" (lit 0)))
     (seq (wset "hp_x" (load "S" (var "bc.k")))
     (seq hPushC (wset "bc.k" (add (var "bc.k") (lit 1))))))

/-- `setBp heapI`, closed. -/
def setBpC : Stmt :=
  seq (wset "sl.i" (lit (slotBp 0)))
  (ite (var "hp_n")
     (seq hTopC (seq (loadLab "hp_v" KM "bc.mf") (storeSlot KM "bc.mf")))
     (storeSlot KB "bc.bf"))

/-- `baseBody heapI`, closed (the heap size `Kh` is not part of the text). -/
def baseBodyC : Stmt :=
  seq (wset "sl.i" (lit (slotB 0)))
  (seq (loadSlot KB "bc.bf")
  (seq (wset "bc.tau" (load "cp.tau" (lit 0)))
  (seq (RamLevel.rowReset "U.len")
  (seq pushSC
  (seq (.while (mul (lt (lit 0) (var "hp_n")) (lt (load "U.len" (lit 0)) (var "bc.tau"))) extractBodyC)
       setBpC)))))

/-- **The closed base program**: `baseProg Kh DL = baseProgC DL.new DL.ins` (`baseProg_closed`). -/
def baseProgC (newS insS : Stmt) : Stmt :=
  seq baseBodyC (seq ptrLoop (seq (convDL newS insS) IHeap.clearS))

theorem baseBody_closed (K : ℕ) : baseBody (IHeapLab.heapI G s K) = baseBodyC := rfl

theorem baseProg_closed (Kh : ℕ) (DL : DLayer G s T) : baseProg Kh DL = baseProgC DL.new DL.ins := rfl

end closed

end base

end Frontier.CHD.RamSpine
