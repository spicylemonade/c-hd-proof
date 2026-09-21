import Frontier.CHD.IHeap
import Frontier.CHD.LabRAM
import Frontier.CHD.RamBaseCase
import Frontier.CHD.LabI

/-!
# Frontier.CHD.IHeapLab — the label-compare instance of `IHeap.LessOK` (agent-06; Layer B, NON-GATE)

`lessL` loads the labels of `hp_x`, `hp_y` from the label table (agent-02's `loadLab`), handles `⊤` via the
`dfin` flags (`⊤` is the maximum), and compares finite labels with agent-02's `cmp`.  With the key
representation `LabAt st d H c0` and the key `keyN d` (`d` extended by `⊤` beyond `G.n`), `lessL` satisfies
`IHeap.LessOK`, so every IHeap operation is available for the C-HD base case on the current labels.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.IHeapLab

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD.LabTab Frontier.CHD.MLab Frontier.CHD.IHeap

/-- label blocks of the comparison -/
def HX : LReg := ⟨"hq_xl", "hq_xh", "hq_xv", "hq_xe", "hq_xr"⟩
def HY : LReg := ⟨"hq_yl", "hq_yh", "hq_yv", "hq_ye", "hq_yr"⟩

/-- `out := [d ra < d rb]` for the vertices in registers `ra`, `rb` (labels from the table; `⊤` is the
maximum); scratch: blocks `HX`, `HY`, flags `hq_xf`, `hq_yf`, compare scratch `hq_c1`, `hq_c2`. -/
def cmpLab (ra rb out : String) : Stmt :=
  .seq (loadLab ra HX "hq_xf")
    (.seq (loadLab rb HY "hq_yf")
      (.ite (.var "hq_xf")
        (.ite (.var "hq_yf") (cmp HX HY "hq_c1" "hq_c2" out) (.wset out (.lit 1)))
        (.wset out (.lit 0))))

/-- the heap's comparison: `hp_lt := [d hp_x < d hp_y]` -/
def lessL : Stmt := cmpLab "hp_x" "hp_y" "hp_lt"

/-- scratch word registers of `cmpLab` -/
def cmpScratchW : List String :=
  ["hq_xf", "hq_yf", "hq_c1", "hq_c2", "hq_xh", "hq_xv", "hq_xe", "hq_xr", "hq_yh", "hq_yv", "hq_ye", "hq_yr"]

/-- Register hygiene for `cmpLab ra rb out`. -/
structure CmpRegs (ra rb out : String) : Prop where
  ra : ra ∉ cmpScratchW
  rb : rb ∉ cmpScratchW
  out : out ∉ cmpScratchW

/-- word registers written by `lessL` -/
def lessW : List String := "hp_lt" :: cmpScratchW

/-- value registers written by `lessL` -/
def lessV : List String := ["hq_xl", "hq_yl"]

variable {G : Graph} {s : Fin G.n}

/-- the key: the label, `⊤` outside `Fin G.n` -/
noncomputable def keyN (d : Labels G s) (v : ℕ) : WLab G s := if h : v < G.n then d ⟨v, h⟩ else ⊤


theorem loadFresh_x : LoadFresh "hp_x" HX "hq_xf" := ⟨by decide, by decide⟩
theorem loadFresh_y : LoadFresh "hp_y" HY "hq_yf" := ⟨by decide, by decide⟩
theorem cmpFresh_XY : CmpFresh HX HY "hq_c1" "hq_c2" := ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem keyN_of_lt (d : Labels G s) {v : ℕ} (hv : v < G.n) : keyN d v = d ⟨v, hv⟩ := by
  simp [keyN, hv]

set_option maxHeartbeats 1000000 in
/-- **Spec of the table-vs-table label compare** (any registers): `out := [d a < d b]`, `⊤` handled. -/
theorem cmpLab_spec {ra rb out : String} (hR : CmpRegs ra rb out) (d : Labels G s)
    (Hh : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ) {st : State ℝ≥0} (hL : LabAt st d Hh c0)
    (hcap0 : 1 < st.cap) (a b : Fin G.n) (ha : st.w ra = a) (hb : st.w rb = b) :
    Runs realOps (cmpLab ra rb out) st (fun r => r.w out = (if d a < d b then 1 else 0) ∧
      Unchanged st r [] [] (out :: cmpScratchW) lessV ∧ st.cost + 1 ≤ r.cost ∧ r.cost ≤ st.cost + 27 ∧
      LabAt r d Hh c0) := by
  have hra := hR.ra
  have hrb := hR.rb
  have hout := hR.out
  simp only [cmpScratchW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hra hrb hout
  have hLF1 : LoadFresh ra HX "hq_xf" := ⟨by decide, by simp [HX]; tauto⟩
  have hLF2 : LoadFresh rb HY "hq_yf" := ⟨by decide, by simp [HY]; tauto⟩
  have hRp : Represents (s := s) (tabOf (G := G) st) d Hh := hL.rep
  unfold cmpLab
  apply runs_seq
  refine (wp_sound _ _ _ (loadLab_wp ra HX "hq_xf" hLF1 st a hL.lens ha)).mono ?_
  rintro r1 ⟨hld1, hu1, hc1⟩
  have htab1 := tabOf_of_unchanged (G := G) hu1 (by simp [labW]) (by simp)
  have hy1 : r1.w rb = b := by
    rw [hu1.wreg rb (by simp [HX, LReg.ws]; tauto)]; exact hb
  apply runs_seq
  refine (wp_sound _ _ _ (loadLab_wp rb HY "hq_yf" hLF2 r1 b (htab1.2 hL.lens) hy1)).mono ?_
  rintro r2 ⟨hld2, hu2, hc2⟩
  rw [htab1.1] at hld2
  have hld1' : Loaded r2 (tabOf (G := G) st) HX "hq_xf" a := by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hld1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hu2.vreg _ (by simp [HX, HY])]; exact a1
    · rw [hu2.wreg _ (by simp [HX, HY, LReg.ws])]; exact a2
    · rw [hu2.wreg _ (by simp [HX, HY, LReg.ws])]; exact a3
    · rw [hu2.wreg _ (by simp [HX, HY, LReg.ws])]; exact a4
    · rw [hu2.wreg _ (by simp [HX, HY, LReg.ws])]; exact a5
    · rw [hu2.wreg _ (by simp [HX, HY, LReg.ws])]; exact a6
  have hu12 : Unchanged st r2 [] [] (out :: cmpScratchW) lessV :=
    Unchanged.chain (hu1.mono (by simp) (by simp)
        (by intro x hx; simp [HX, LReg.ws] at hx; simp [cmpScratchW]; tauto)
        (by intro x hx; simp [HX] at hx; simp [lessV, hx])) hu2 (by simp) (by simp)
      (by intro x hx; simp [HY, LReg.ws] at hx; simp [cmpScratchW]; tauto)
      (by intro x hx; simp [HY] at hx; simp [lessV, hx])
  have hcap : 1 < r2.cap := by rw [hu12.cap]; exact hcap0
  have hcost12 : r2.cost = st.cost + 12 := by omega
  have hW : out ∈ out :: cmpScratchW := List.mem_cons_self
  by_cases hxt : d a = ⊤
  · -- `a` is `⊤`: not smaller than anything
    have hxf : r2.w "hq_xf" = 0 := by rw [hld1'.2.2.2.2.2]; exact (hRp.fin_iff a).mpr hxt
    refine runs_ite_false (by rw [evalW_var, hxf]) ?_
    refine runs_wset (evalW_lit_of (by simp; omega)) ?_
    have hu : Unchanged st (((r2.charge 1).setW out 0).charge 1) [] [] (out :: cmpScratchW) lessV :=
      unch_charge' (unch_setW' (unch_charge' hu12 1) hW _) 1
    refine ⟨by simp [hxt], hu, by simp; omega, by simp; omega, ?_⟩
    exact LabAt.of_unchanged hL hu (by simp [labW]) (by simp) (by simp; omega)
  · have hxf : r2.w "hq_xf" ≠ 0 := by
      rw [hld1'.2.2.2.2.2]; exact fun h => hxt ((hRp.fin_iff a).mp h)
    refine runs_ite_true (show evalW r2 (.var "hq_xf") = some (r2.w "hq_xf") from rfl) hxf ?_
    by_cases hyt : d b = ⊤
    · -- `b` is `⊤`, `a` is finite
      have hyf : (r2.charge 1).w "hq_yf" = 0 := by
        simp only [State.charge_w]; rw [hld2.2.2.2.2.2]; exact (hRp.fin_iff b).mpr hyt
      refine runs_ite_false (by rw [evalW_var, hyf]) ?_
      refine runs_wset (evalW_lit_of (by simpa using hcap)) ?_
      have hu : Unchanged st ((((r2.charge 1).charge 1).setW out 1).charge 1) [] [] (out :: cmpScratchW) lessV :=
        unch_charge' (unch_setW' (unch_charge' (unch_charge' hu12 1) 1) hW _) 1
      refine ⟨by simp [hyt, lt_top_iff_ne_top.mpr hxt], hu, by simp; omega, by simp; omega, ?_⟩
      exact LabAt.of_unchanged hL hu (by simp [labW]) (by simp) (by simp; omega)
    · -- both finite: the machine comparison
      have hyf : (r2.charge 1).w "hq_yf" ≠ 0 := by
        simp only [State.charge_w]; rw [hld2.2.2.2.2.2]; exact fun h => hyt ((hRp.fin_iff b).mp h)
      refine runs_ite_true (show evalW (r2.charge 1) (.var "hq_yf") = some ((r2.charge 1).w "hq_yf") from rfl)
        hyf ?_
      refine (wp_sound _ _ _ (cmp_wp (ops := realOps) (fun a b => rfl) out cmpFresh_XY
        ((r2.charge 1).charge 1) (by simpa using hcap))).mono ?_
      rintro r3 ⟨hbit, hu3, hc3a, hc3⟩
      have hX : Holds ((r2.charge 1).charge 1) HX ((tabOf (G := G) st).lab a) :=
        (hld1'.holds hRp hxt).charge 1 |>.charge 1
      have hY : Holds ((r2.charge 1).charge 1) HY ((tabOf (G := G) st).lab b) :=
        (hld2.holds hRp hyt).charge 1 |>.charge 1
      rw [cbit_eq hX hY] at hbit
      obtain ⟨p, hp⟩ := WithTop.ne_top_iff_exists.mp hxt
      obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hyt
      have hlt : ((tabOf (G := G) st).lab a).lt ((tabOf (G := G) st).lab b) ↔ d a < d b := by
        rw [← hp, ← hq, WithTop.coe_lt_coe]
        exact lt_iff hRp.hist (hRp.rep a p hp.symm) (hRp.rep b q hq.symm)
      have hu : Unchanged st r3 [] [] (out :: cmpScratchW) lessV :=
        Unchanged.chain (unch_charge' (unch_charge' hu12 1) 1) hu3 (by simp) (by simp)
          (by intro x hx; simp at hx; simp [cmpScratchW]; tauto) (by simp)
      refine ⟨?_, hu, by simp at hc3a; omega, by simp at hc3; omega,
        LabAt.of_unchanged hL hu (by simp [labW]) (by simp) (by simp at hc3a; omega)⟩
      rw [hbit]
      by_cases h : d a < d b
      · rw [if_pos (hlt.mpr h), if_pos h]
      · rw [if_neg (fun h' => h (hlt.mp h')), if_neg h]

theorem cmpRegs_heap : CmpRegs "hp_x" "hp_y" "hp_lt" := ⟨by decide, by decide, by decide⟩

/-- **The label compare meets the heap's comparison interface.** -/
theorem lessL_ok (d : Labels G s) (Hh : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ) :
    LessOK realOps lessL (fun st => LabAt st d Hh c0 ∧ 1 < st.cap) (keyN d) G.n 27 lessW lessV where
  run := by
    rintro st ⟨hL, hcap0⟩ hx hy
    refine (cmpLab_spec cmpRegs_heap d Hh c0 hL hcap0 ⟨st.w "hp_x", hx⟩ ⟨st.w "hp_y", hy⟩ rfl rfl).mono ?_
    rintro r ⟨hbit, hu, _, hc, hLr⟩
    refine ⟨by rw [hbit, keyN_of_lt d hx, keyN_of_lt d hy], hu, hc, hLr, by rw [hu.cap]; exact hcap0⟩
  frame := fun st r hL hu hc => ⟨LabAt.of_unchanged hL.1 hu (by simp [labW]) (by simp) hc, by rw [hu.cap]; exact hL.2⟩
  regs := by decide
  lt_mem := by simp [lessW]

/-! ## The base-case heap `RamBaseCase.HeapI` from IHeap -/

/-- The heap represents `T` (as vertices of `G`), heap-ordered by `key`. -/
def HRL (st : State ℝ≥0) (T : Finset (Fin G.n)) (key : Fin G.n → WLab G s) : Prop :=
  st.w "hp_n" = T.card ∧ st.wlen "hp_A" = G.n ∧ st.wlen "hp_P" = G.n ∧ 2 * G.n + 3 < st.cap ∧
    PosOK G.n (st.wa "hp_A") (st.wa "hp_P") T.card ∧ IHeap.HeapOK (keyN key) (st.wa "hp_A") T.card ∧
    IHeap.T (st.wa "hp_A") T.card = T.map Fin.valEmbedding

theorem card_le_n (T : Finset (Fin G.n)) : T.card ≤ G.n := by
  simpa using Finset.card_le_univ T

theorem keyN_agree {d key : Labels G s} {v : Fin G.n} (hk : ∀ y, y ≠ v → d y = key y) :
    ∀ u : ℕ, u ≠ (v : ℕ) → keyN d u = keyN key u := by
  intro u hu
  by_cases h : u < G.n
  · rw [keyN_of_lt d h, keyN_of_lt key h]
    exact hk _ (fun e => hu (by rw [← e]))
  · simp [keyN, h]

theorem mem_T_iff {A : ℕ → ℕ} {n : ℕ} {T : Finset (Fin G.n)} (hT : IHeap.T A n = T.map Fin.valEmbedding)
    (u : Fin G.n) : (u : ℕ) ∈ IHeap.T A n ↔ u ∈ T := by
  rw [hT]
  simp only [Finset.mem_map, Fin.valEmbedding_apply]
  exact ⟨fun ⟨a, ha, e⟩ => (Fin.ext e) ▸ ha, fun h => ⟨u, h, rfl⟩⟩

theorem HRL.frame {st st' : State ℝ≥0} {T : Finset (Fin G.n)} {key : Fin G.n → WLab G s}
    {wa' va' wr' vr' : List String} (h : HRL st T key) (hu : Unchanged st st' wa' va' wr' vr')
    (hwa : ∀ a ∈ ["hp_A", "hp_P"], a ∉ wa') (hwr : ∀ a ∈ ["hp_n"], a ∉ wr') : HRL st' T key := by
  obtain ⟨hn, hlA, hlP, hcap, hpos, hheap, hT⟩ := h
  have eA := hu.warr "hp_A" (hwa _ (by simp))
  have eP := hu.warr "hp_P" (hwa _ (by simp))
  refine ⟨by rw [hu.wreg _ (hwr _ (by simp))]; exact hn, by rw [eA.2]; exact hlA, by rw [eP.2]; exact hlP,
    by rw [hu.cap]; exact hcap, by rw [eA.1, eP.1]; exact hpos, by rw [eA.1]; exact hheap, by rw [eA.1]; exact hT⟩

/-- **IHeap as the base case's heap**, for heaps of size `≤ K` (`hsz = K`): the per-operation constant is
`O(log K)` — with `K = O(|S| + δ τ₀)` in a base call this is the `hbase` shape. -/
noncomputable def heapI (G : Graph) (s : Fin G.n) (K : ℕ) : RamBaseCase.HeapI G s where
  HR := HRL
  push := pushOrDecX lessL
  pop := popS lessL
  top := topS
  wa := ["hp_A", "hp_P"]
  va := []
  wr := hpRegs ++ lessW
  vr := lessV
  wa_lab := by decide
  va_lab := by simp
  hsz := K
  Cop := 74 * (Nat.log 2 (K + 1) + 1) + 12
  fwa := ["hp_A", "hp_P"]
  fwr := ["hp_n"]
  HR_frame := fun h hu hwa hwr => h.frame hu hwa hwr
  size := fun h => h.1
  push_spec := by
    intro st T key d Hh c0 v hHR hLab hk hkv _ _ hx _ _ hK
    obtain ⟨hn, hlA, hlP, hcap, hpos, hheap, hT⟩ := hHR
    refine (IHeap.Runs.cost_lt (runs_pushOrDecX (lessL_ok d Hh c0) (n := T.card) (v := v) (key0 := keyN key)
      ⟨hLab, by omega⟩ hn (card_le_n T) hlA hlP hpos hheap hx v.isLt (keyN_agree hk)
      (fun _ => by rw [keyN_of_lt d v.isLt, keyN_of_lt key v.isLt]; exact hkv) hcap)).mono ?_
    rintro r ⟨⟨n', hR, hT', hrv, hunch, hcost⟩, hlow⟩
    have hT'' : IHeap.T (r.wa "hp_A") n' = (insert v T).map Fin.valEmbedding := by
      rw [hT', hT, Finset.map_insert]; rfl
    have hn' : n' = (insert v T).card := by
      have := hR.pos.card_T
      rw [hT'', Finset.card_map] at this
      exact this.symm
    subst hn'
    refine ⟨⟨hR.rn, hR.lenA, hR.lenP, by rw [hunch.cap]; exact hcap, hR.pos, hR.heap, hT''⟩, hunch, by omega, ?_⟩
    have h1 : Nat.log 2 (T.card + 1) ≤ Nat.log 2 (K + 1) := Nat.log_mono_right (by omega)
    have h2 := Nat.mul_le_mul_left (27 + 12) (Nat.add_le_add_right h1 1)
    omega
  pop_spec := by
    intro st T d Hh c0 hHR hLab hne _ _ _ hK
    obtain ⟨hn, hlA, hlP, hcap, hpos, hheap, hT⟩ := hHR
    obtain ⟨m, hm⟩ : ∃ m, T.card = m + 1 := ⟨T.card - 1, by have := hne.card_pos; omega⟩
    rw [hm] at hn hpos hheap hT
    have hmN : m + 1 ≤ G.n := hm ▸ card_le_n T
    refine (IHeap.Runs.cost_lt (runs_pop (lessL_ok d Hh c0) (n := m) ⟨⟨hLab, by omega⟩, hn, hmN, hlA, hlP, hpos,
      hheap⟩ hcap)).mono ?_
    rintro r ⟨⟨hR, hrv, hmin, hT', hunch, hcost⟩, hlow⟩
    have hA0 : st.wa "hp_A" 0 < G.n := (hpos.slots 0 (by omega)).1
    set u : Fin G.n := ⟨st.wa "hp_A" 0, hA0⟩ with hudef
    have hu0 : (u : ℕ) ∈ IHeap.T (st.wa "hp_A") (m + 1) := by
      simp only [IHeap.T, Finset.mem_image, Finset.mem_range]; exact ⟨0, by omega, rfl⟩
    have huT : u ∈ T := (mem_T_iff hT u).mp hu0
    refine ⟨u, huT, fun y hy => ?_, hrv, ⟨?_, hR.lenA, hR.lenP, by rw [hunch.cap]; exact hcap, ?_, ?_, ?_⟩, hunch,
      by omega, ?_⟩
    · have := hmin y ((mem_T_iff hT y).mpr hy)
      rwa [keyN_of_lt d hA0, keyN_of_lt d y.isLt] at this
    · rw [hR.rn, Finset.card_erase_of_mem huT, hm]; rfl
    · rw [Finset.card_erase_of_mem huT, hm]; exact hR.pos
    · rw [Finset.card_erase_of_mem huT, hm]; exact hR.heap
    · rw [Finset.card_erase_of_mem huT, hm, Nat.add_sub_cancel, hT', hT, Finset.map_erase]; rfl
    · have h1 : Nat.log 2 m ≤ Nat.log 2 (K + 1) := Nat.log_mono_right (by omega)
      have h2 := Nat.mul_le_mul_left (2 * 27 + 20) (Nat.add_le_add_right h1 1)
      omega
  top_spec := by
    intro st T d Hh c0 hHR hLab hne _ _ _ _
    obtain ⟨hn, hlA, hlP, hcap, hpos, hheap, hT⟩ := hHR
    obtain ⟨m, hm⟩ : ∃ m, T.card = m + 1 := ⟨T.card - 1, by have := hne.card_pos; omega⟩
    have hHR' : HRL st T d := ⟨hn, hlA, hlP, hcap, hpos, hheap, hT⟩
    rw [hm] at hn hpos hheap hT
    have hmN : m + 1 ≤ G.n := hm ▸ card_le_n T
    refine (IHeap.Runs.cost_lt (runs_top (ops := realOps) (KeyRep := fun st => LabAt st d Hh c0 ∧ 1 < st.cap)
      ⟨⟨hLab, by omega⟩, hn, hmN, hlA, hlP, hpos, hheap⟩ hcap)).mono ?_
    rintro r ⟨⟨hrv, hmin, hreg, hcost⟩, hlow⟩
    have hA0 : st.wa "hp_A" 0 < G.n := (hpos.slots 0 (by omega)).1
    set u : Fin G.n := ⟨st.wa "hp_A" 0, hA0⟩ with hudef
    have hu0 : (u : ℕ) ∈ IHeap.T (st.wa "hp_A") (m + 1) := by
      simp only [IHeap.T, Finset.mem_image, Finset.mem_range]; exact ⟨0, by omega, rfl⟩
    have huT : u ∈ T := (mem_T_iff hT u).mp hu0
    have hunch0 : Unchanged st r [] [] ["hp_v"] [] := by
      obtain ⟨hwa, hva, hwlen, hvlen, hcap', hprocs, hv, hw⟩ := hreg
      exact ⟨fun a _ => ⟨by rw [hwa], by rw [hwlen]⟩, fun a _ => ⟨by rw [hva], by rw [hvlen]⟩,
        fun y hy => hw y hy, fun y _ => by rw [hv], hcap', hprocs⟩
    have hunch : Unchanged st r ["hp_A", "hp_P"] [] (hpRegs ++ lessW) lessV :=
      hunch0.mono (by simp) (by simp) (by intro a ha; simp at ha; subst ha; simp [hpRegs]) (by simp)
    refine ⟨u, huT, fun y hy => ?_, hrv, hHR'.frame hunch0 (by simp) (by simp), hunch, by omega, by omega⟩
    have := hmin y ((mem_T_iff hT y).mpr hy)
    rwa [keyN_of_lt d hA0, keyN_of_lt d y.isLt] at this


/-- `heapI` meets the base case's disjointness side conditions. -/
theorem heapI_ok (K : ℕ) : RamBaseCase.HeapOK (heapI G s K) where
  wr := by simp only [heapI, hpRegs, lessW]; decide
  vr := by simp only [heapI, lessV]; decide
  wa := by simp only [heapI]; decide
  va := by simp only [heapI]; decide
  fwa := by simp only [heapI, labW]; decide
  fwr := by simp only [heapI]; decide


/-! ### Initialization and clearing in `HeapI` terms -/

/-- a trivial comparison (constant key), used to transport `init` / `clear` to any key -/
def trivLess : Stmt := .wset "hp_lt" (.lit 0)

theorem trivLess_ok (N : ℕ) :
    LessOK realOps trivLess (fun st => 1 < st.cap) (fun _ => (0 : ℕ)) N 1 ["hp_lt"] [] where
  run := by
    intro st hc _ _
    refine runs_wset (evalW_lit_of (by omega)) ?_
    refine ⟨by simp, unch_charge' (unch_setW' (Unchanged.refl st _ _ _ _) (by simp) _) 1, by simp, by simpa using hc⟩
  frame := fun st r hc hu _ => by rw [hu.cap]; exact hc
  regs := by decide
  lt_mem := by simp

/-- **Init**: an empty heap for the vertices of `G` (register `x` holds `G.n`). -/
theorem heapI_init {st : State ℝ≥0} {x : String} (hx : st.w x = G.n) (hcap : 2 * G.n + 3 < st.cap)
    (key : Fin G.n → WLab G s) :
    Runs realOps (initS x) st (fun r => HRL r ∅ key ∧ Unchanged st r ["hp_A", "hp_P"] [] ["hp_n"] [] ∧
      r.cost = st.cost + 2 * G.n + 3) := by
  refine (runs_init (trivLess_ok G.n) (by omega) hx hcap).mono ?_
  rintro r ⟨hR, hu, hc⟩
  refine ⟨⟨by simpa using hR.rn, hR.lenA, hR.lenP, by rw [hu.cap]; exact hcap, by simpa using hR.pos,
    fun i hi hin => by simp at hin, by simp [IHeap.T]⟩, hu, hc⟩

/-- **Clear**: empty the heap (resets `hp_P`), for any key. -/
theorem heapI_clear {st : State ℝ≥0} {T : Finset (Fin G.n)} {key : Fin G.n → WLab G s}
    (hH : HRL st T key) (key' : Fin G.n → WLab G s) :
    Runs realOps clearS st (fun r => HRL r ∅ key' ∧ (∀ v < G.n, r.wa "hp_P" v = 0) ∧
      Unchanged st r ["hp_P"] [] ["hp_n"] [] ∧ r.cost ≤ st.cost + 3 * T.card + 1) := by
  obtain ⟨hn, hlA, hlP, hcap, hpos, _, _⟩ := hH
  refine (runs_clear (trivLess_ok G.n) (by omega) hn (card_le_n T) hlA hlP hpos hcap).mono ?_
  rintro r ⟨hR, hP0, hA, hu, hc⟩
  refine ⟨⟨by simpa using hR.rn, hR.lenA, hR.lenP, by rw [hu.cap]; exact hcap, by simpa using hR.pos,
    fun i hi hin => by simp at hin, by simp [IHeap.T]⟩, hP0, hu, hc⟩


/-! ### The table-vs-table compare for B-L2 (agent-09's `LabX.cmpTT`), over agent-02's `labI` -/

/-- registers for B-L2's `cmpTT` -/
def ttRa : String := "tt.ra"
def ttRb : String := "tt.rb"

theorem cmpRegs_tt : CmpRegs ttRa ttRb "lab.bit" := ⟨by decide, by decide, by decide⟩

/-- **`cmpTT` for `labI c0`**, in the exact shape of agent-09's `LabX.cmpTT_spec`:
`lab.bit := [d a < d b]` for the vertices in `tt.ra`, `tt.rb`. -/
theorem cmpTT_spec (c0 : ℕ) {st : State ℝ≥0} {d : Labels G s} {g : LabIInst.Gh G} {a b : Fin G.n}
    (hLT : LabIInst.LTp (s := s) c0 st d g) (_ : d a ≠ ⊤) (_ : d b ≠ ⊤) (ha : st.w ttRa = a)
    (hb : st.w ttRb = b) (_ : st.cost + 27 ≤ c0 + st.cap) :
    Runs realOps (cmpLab ttRa ttRb "lab.bit") st (fun st' => st'.w "lab.bit" = (if d a < d b then 1 else 0) ∧
      Unchanged st st' [] [] ("lab.bit" :: cmpScratchW) lessV ∧ st.cost ≤ st'.cost ∧ st'.cost ≤ st.cost + 27) := by
  have hcap : 1 < st.cap := by have := hLT.2.2.2; omega
  refine (cmpLab_spec cmpRegs_tt d g.1 c0 hLT.1 hcap a b ha hb).mono ?_
  rintro r ⟨hbit, hu, hc1, hc2, _⟩
  exact ⟨hbit, hu, by omega, hc2⟩

end Frontier.CHD.IHeapLab
