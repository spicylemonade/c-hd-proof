import Frontier.CHD.IHeap
import Frontier.CHD.RamBaseCase

/-!
# Frontier.CHD.BaseHeap — agent-06's IHeap keyed by the CURRENT labels (base case, B-L4)

Owner: agent-08.  NON-GATE.

`lessL` decides `key hp_x < key hp_y` for `key = keyOf d` (the current label, `⊤` outside
`[0, n)`), reading agent-02's label table: both labels are loaded, `⊤` is handled through the
`dfin` flags, finite labels are compared by B-LAB's `cmp` (exact for the walk order,
`MLabel.lt_iff`).  `lessL_ok` is IHeap's `LessOK` for the cost-free key representation
`KeyRepL d H` (table lengths + `Represents`).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamBaseCase

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD.LabTab Frontier.CHD.MLab WExpr Stmt

variable {G : Graph} {s : Fin G.n}

/-- The key of a vertex id: its current label (`⊤` outside `[0, n)`). -/
def keyOf (d : Labels G s) (v : ℕ) : WLab G s := if h : v < G.n then d ⟨v, h⟩ else ⊤

theorem keyOf_fin (d : Labels G s) (v : Fin G.n) : keyOf d v = d v := by
  simp [keyOf, v.isLt]

/-- Cost-free key representation: the label table represents `d`. -/
def KeyRepL (d : Labels G s) (H : Fin G.n → ℕ → List (Fin G.m)) (st : State ℝ≥0) : Prop :=
  LabLens st G.n ∧ Represents (s := s) (tabOf (G := G) st) d H ∧ 1 < st.cap

def X1 : LReg := ⟨"hk.xl", "hk.xh", "hk.xv", "hk.xe", "hk.xr"⟩
def Y1 : LReg := ⟨"hk.yl", "hk.yh", "hk.yv", "hk.ye", "hk.yr"⟩

/-- `hp_lt := [d[hp_x] < d[hp_y]]` (walk order, `⊤` largest). -/
def lessL : Stmt :=
  seq (loadLab "hp_x" X1 "hk.xf")
  (seq (loadLab "hp_y" Y1 "hk.yf")
  (ite (var "hk.xf")
     (ite (var "hk.yf") (cmp X1 Y1 "hk.c1" "hk.c2" "hp_lt") (wset "hp_lt" (lit 1)))
     (wset "hp_lt" (lit 0))))

/-- Word registers written by `lessL`. -/
def lessW : List String :=
  ["hk.xh", "hk.xv", "hk.xe", "hk.xr", "hk.xf", "hk.yh", "hk.yv", "hk.ye", "hk.yr", "hk.yf",
   "hk.c1", "hk.c2", "hp_lt"]
/-- Value registers written by `lessL`. -/
def lessV : List String := ["hk.xl", "hk.yl"]

theorem keyRepL_frame {d : Labels G s} {H : Fin G.n → ℕ → List (Fin G.m)} {st r : State ℝ≥0}
    {wa va wr vr : List String} (h : KeyRepL d H st) (hu : Unchanged st r wa va wr vr)
    (hw : ∀ a ∈ labW, a ∉ wa) (hv : "dlen" ∉ va) : KeyRepL d H r := by
  obtain ⟨htab, hlens⟩ := tabOf_of_unchanged (G := G) hu hw hv
  exact ⟨hlens h.1, htab ▸ h.2.1, by rw [hu.cap]; exact h.2.2⟩

open Classical in
theorem lessL_run (d : Labels G s) (H : Fin G.n → ℕ → List (Fin G.m)) (st : State ℝ≥0)
    (hK : KeyRepL d H st) (hx : st.w "hp_x" < G.n) (hy : st.w "hp_y" < G.n) :
    Runs realOps lessL st (fun r =>
      r.w "hp_lt" = (if keyOf d (st.w "hp_x") < keyOf d (st.w "hp_y") then 1 else 0) ∧
      Unchanged st r [] [] lessW lessV ∧ r.cost ≤ st.cost + 30 ∧ KeyRepL d H r) := by
  have hcap : 1 < st.cap := hK.2.2
  set x : Fin G.n := ⟨st.w "hp_x", hx⟩ with hxdef
  set y : Fin G.n := ⟨st.w "hp_y", hy⟩ with hydef
  have hkx : keyOf d (st.w "hp_x") = d x := keyOf_fin d x
  have hky : keyOf d (st.w "hp_y") = d y := keyOf_fin d y
  rw [hkx, hky]
  apply wp_sound
  rw [lessL, wp_seq]
  refine wp_mono _ ?_ _ (loadLab_wp "hp_x" X1 "hk.xf" ⟨by decide, by decide⟩ st x hK.1 rfl)
  rintro r1 ⟨hX1, hU1, hc1⟩
  rw [wp_seq]
  have hK1 : KeyRepL d H r1 := keyRepL_frame hK hU1 (by decide) (by decide)
  have hy1 : r1.w "hp_y" = y := by rw [hU1.wreg "hp_y" (by decide)]
  refine wp_mono _ ?_ _ (loadLab_wp "hp_y" Y1 "hk.yf" ⟨by decide, by decide⟩ r1 y hK1.1 hy1)
  rintro r2 ⟨hY2, hU2, hc2⟩
  have hK2 : KeyRepL d H r2 := keyRepL_frame hK1 hU2 (by decide) (by decide)
  have htab12 : tabOf (G := G) r1 = tabOf st := (tabOf_of_unchanged (G := G) hU1 (by decide) (by decide)).1
  -- X1's registers survive the second load
  have hX2 : Loaded r2 (tabOf (G := G) st) X1 "hk.xf" x := by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hX1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hU2.vreg _ (by decide)]; exact a1
    · rw [hU2.wreg _ (by decide)]; exact a2
    · rw [hU2.wreg _ (by decide)]; exact a3
    · rw [hU2.wreg _ (by decide)]; exact a4
    · rw [hU2.wreg _ (by decide)]; exact a5
    · rw [hU2.wreg _ (by decide)]; exact a6
  rw [htab12] at hY2
  have hcap2 : 1 < r2.cap := by rw [hU2.cap, hU1.cap]; exact hcap
  have hU12 : Unchanged st r2 [] [] lessW lessV :=
    (hU1.comp hU2).mono (by simp) (by simp) (by decide) (by decide)
  have hR := hK.2.1
  rw [wp_ite_var]
  refine ⟨fun hxf => ?_, fun hxf => ?_⟩
  · -- `d x` finite
    have hdx : d x ≠ ⊤ := by
      intro h; apply hxf; rw [hX2.2.2.2.2.2]; exact (hR.fin_iff x).mpr h
    rw [wp_ite_var]
    refine ⟨fun hyf => ?_, fun hyf => ?_⟩
    · have hdy : d y ≠ ⊤ := by
        intro h; apply hyf; rw [show (r2.charge 1).w "hk.yf" = r2.w "hk.yf" from rfl, hY2.2.2.2.2.2]
        exact (hR.fin_iff y).mpr h
      refine wp_mono _ ?_ _ (cmp_wp (ops := realOps) (fun a b => rfl) "hp_lt"
        ⟨by decide, by decide, by decide, by decide, by decide⟩ ((r2.charge 1).charge 1)
        (by simpa using hcap2))
      rintro r ⟨hlt, hU3, -, hc3⟩
      obtain ⟨p, hp⟩ := WithTop.ne_top_iff_exists.mp hdx
      obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hdy
      have hxh : Holds ((r2.charge 1).charge 1) X1 ((tabOf (G := G) st).lab x) :=
        (Loaded.holds hX2 hR hdx).charge 1 |>.charge 1
      have hyh : Holds ((r2.charge 1).charge 1) Y1 ((tabOf (G := G) st).lab y) :=
        (Loaded.holds hY2 hR hdy).charge 1 |>.charge 1
      have hrx := hR.rep x (p : List (Fin G.m)) (by rw [← hp]; rfl)
      have hry := hR.rep y (q : List (Fin G.m)) (by rw [← hq]; rfl)
      have hiff := MLab.lt_iff hR.hist hrx hry
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hlt, cbit_eq hxh hyh, ← hp, ← hq]
        by_cases h : ((tabOf (G := G) st).lab x).lt ((tabOf (G := G) st).lab y)
        · rw [if_pos h, if_pos (WithTop.coe_lt_coe.mpr (by exact hiff.mp h))]
        · rw [if_neg h, if_neg (fun h' => h (hiff.mpr (by exact WithTop.coe_lt_coe.mp h')))]
      · refine ((hU12.comp ((Unchanged.charge r2 1 [] [] [] []).comp
          ((Unchanged.charge _ 1 [] [] [] []).comp hU3)))).mono (by simp) (by simp) ?_ (by simp)
        decide
      · simp only [State.charge_cost] at hc3; omega
      · exact keyRepL_frame hK2 ((Unchanged.charge r2 1 [] [] [] []).comp
          ((Unchanged.charge _ 1 [] [] [] []).comp hU3)) (by simp) (by simp)
    · -- `d y = ⊤`: `d x < ⊤`
      have hdy : d y = ⊤ := by
        have : r2.w "hk.yf" = 0 := by simpa using hyf
        rw [hY2.2.2.2.2.2] at this; exact (hR.fin_iff y).mp this
      refine wp_mono _ ?_ _ (wset_lit_wp (ops := realOps) "hp_lt" 1 ((r2.charge 1).charge 1)
        (by simpa using hcap2))
      rintro r ⟨h1, h2, h3⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [h1, hdy, if_pos (lt_top_iff_ne_top.mpr hdx)]
      · refine ((hU12.comp ((Unchanged.charge r2 1 [] [] [] []).comp
          ((Unchanged.charge _ 1 [] [] [] []).comp h2)))).mono (by simp) (by simp) ?_ (by simp)
        decide
      · simp only [State.charge_cost] at h3; omega
      · exact keyRepL_frame hK2 ((Unchanged.charge r2 1 [] [] [] []).comp
          ((Unchanged.charge _ 1 [] [] [] []).comp h2)) (by simp) (by simp)
  · -- `d x = ⊤`: never smaller
    have hdx : d x = ⊤ := by
      have : r2.w "hk.xf" = 0 := hxf
      rw [hX2.2.2.2.2.2] at this; exact (hR.fin_iff x).mp this
    refine wp_mono _ ?_ _ (wset_lit_wp (ops := realOps) "hp_lt" 0 (r2.charge 1)
      (by simp only [State.charge_cap]; omega))
    rintro r ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h1, hdx, if_neg (not_lt.mpr le_top)]
    · refine ((hU12.comp ((Unchanged.charge r2 1 [] [] [] []).comp h2))).mono (by simp) (by simp)
        ?_ (by simp)
      decide
    · simp only [State.charge_cost] at h3; omega
    · exact keyRepL_frame hK2 ((Unchanged.charge r2 1 [] [] [] []).comp h2) (by simp) (by simp)

/-- **IHeap's comparison interface** for the current labels. -/
theorem lessL_ok (d : Labels G s) (H : Fin G.n → ℕ → List (Fin G.m)) :
    IHeap.LessOK realOps lessL (KeyRepL d H) (keyOf d) G.n 30 lessW lessV where
  run st hK hx hy := lessL_run d H st hK hx hy
  frame st r hK hu _ := keyRepL_frame hK hu (by decide) (by simp)
  regs := by decide
  lt_mem := by decide

/-! ## The heap interface of the base case, instantiated by IHeap -/

/-- IHeap's arrays hold the vertex set `T`, heap-ordered by the labels `key`. -/
def HRL (st : State ℝ≥0) (T : Finset (Fin G.n)) (key : Labels G s) : Prop :=
  ∃ n, st.w "hp_n" = n ∧ n ≤ G.n ∧ st.wlen "hp_A" = G.n ∧ st.wlen "hp_P" = G.n ∧
    IHeap.PosOK G.n (st.wa "hp_A") (st.wa "hp_P") n ∧ IHeap.HeapOK (keyOf key) (st.wa "hp_A") n ∧
    IHeap.T (st.wa "hp_A") n = T.map Fin.valEmbedding

theorem HRL.card {st : State ℝ≥0} {T : Finset (Fin G.n)} {key : Labels G s}
    (h : HRL st T key) : st.w "hp_n" = T.card := by
  obtain ⟨n, hn, -, -, -, hpos, -, hT⟩ := h
  rw [hn, ← hpos.card_T, hT, Finset.card_map]

theorem log_le_log_succ {n N : ℕ} (h : n ≤ N) : Nat.log 2 (n + 1) ≤ Nat.log 2 (N + 1) :=
  Nat.log_mono_right (by omega)

/-- Cost bound of one heap operation on a heap of size `≤ hs`. -/
def copL (hs : ℕ) : ℕ := 80 * (Nat.log 2 (hs + 1) + 1) + 12

open Classical in
/-- **The base case's heap**: agent-06's IHeap with the label comparison `lessL`, for heaps of
size `≤ hs` (cost `O(log hs)` per operation). -/
def heapL (hs : ℕ) : HeapI G s where
  HR := HRL
  push := IHeap.pushOrDecX lessL
  pop := IHeap.popS lessL
  top := IHeap.topS
  wa := ["hp_A", "hp_P"]
  va := []
  wr := IHeap.hpRegs ++ lessW
  vr := lessV
  wa_lab := by decide
  va_lab := by simp
  hsz := hs
  Cop := copL hs
  fwa := ["hp_A", "hp_P"]
  fwr := ["hp_n"]
  HR_frame := by
    intro st st' T key wa' va' wr' vr' h hu hfa hfr
    obtain ⟨n, hn, hnN, hlA, hlP, hpos, hheap, hT⟩ := h
    have eA := hu.warr "hp_A" (hfa "hp_A" (by simp))
    have eP := hu.warr "hp_P" (hfa "hp_P" (by simp))
    refine ⟨n, by rw [hu.wreg "hp_n" (hfr "hp_n" (by simp)), hn], hnN, by rw [eA.2, hlA],
      by rw [eP.2, hlP], by rw [eA.1, eP.1]; exact hpos, by rw [eA.1]; exact hheap,
      by rw [eA.1]; exact hT⟩
  size := fun h => HRL.card h
  push_spec := by
    intro st T key d Hh c0 v hHR hL hkey hdv hTfin hvfin hx hbud hcapN hszc
    have hcard0 := HRL.card hHR
    obtain ⟨n, hn, hnN, hlA, hlP, hpos, hheap, hT⟩ := hHR
    have hK : KeyRepL d Hh st := ⟨hL.lens, hL.rep, by omega⟩
    refine ((IHeap.runs_pushOrDecX (lessL_ok d Hh) (n := n) (v := v) (key0 := keyOf key) hK hn hnN
      hlA hlP hpos hheap hx v.isLt (fun u hu => ?_) (fun _ => ?_) hcapN).cost_mono).mono ?_
    · unfold keyOf
      split_ifs with h
      · exact hkey ⟨u, h⟩ (fun e => hu (by rw [← e]))
      · rfl
    · rw [keyOf_fin, keyOf_fin]; exact hdv
    · rintro r ⟨⟨n', hH', hT', -, hU', hc'⟩, hcl⟩
      refine ⟨⟨n', hH'.rn, hH'.nN, hH'.lenA, hH'.lenP, hH'.pos, hH'.heap, ?_⟩, hU', hcl, ?_⟩
      · rw [hT', hT, Finset.map_insert]; rfl
      · have := log_le_log_succ (show n ≤ hs by omega)
        unfold copL
        nlinarith
  pop_spec := by
    intro st T d Hh c0 hHR hL hTne hTfin hbud hcapN hszc
    obtain ⟨n, hn, hnN, hlA, hlP, hpos, hheap, hT⟩ := hHR
    have hcard : n = T.card := by rw [← hpos.card_T, hT, Finset.card_map]
    have hn1 : 0 < n := by rw [hcard]; exact Finset.card_pos.mpr hTne
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hK : KeyRepL d Hh st := ⟨hL.lens, hL.rep, by omega⟩
    have hH : IHeap.HeapRep (KeyRepL d Hh) (keyOf d) G.n st (m + 1) :=
      ⟨hK, hn, hnN, hlA, hlP, hpos, hheap⟩
    refine ((IHeap.runs_pop (lessL_ok d Hh) hH hcapN).cost_mono).mono ?_
    rintro r ⟨⟨hH', hv, hmin, hT', hU', hc'⟩, hcl⟩
    have hA0 : st.wa "hp_A" 0 < G.n := (hpos.slots 0 (by omega)).1
    set u : Fin G.n := ⟨st.wa "hp_A" 0, hA0⟩ with hu
    have hmemA : ∀ y : Fin G.n, y ∈ T ↔ (y : ℕ) ∈ IHeap.T (st.wa "hp_A") (m + 1) := by
      intro y
      rw [hT, Finset.mem_map]
      constructor
      · intro h; exact ⟨y, h, rfl⟩
      · rintro ⟨z, hz, hzy⟩
        have : z = y := Fin.ext hzy
        rw [← this]; exact hz
    have huT : u ∈ T := by
      rw [hmemA]; simp only [IHeap.T, Finset.mem_image, Finset.mem_range]
      exact ⟨0, by omega, rfl⟩
    refine ⟨u, huT, fun y hy => ?_, by rw [hv], ⟨m, hH'.rn, hH'.nN, hH'.lenA, hH'.lenP, hH'.pos,
      hH'.heap, ?_⟩, hU', hcl, ?_⟩
    · have := hmin y ((hmemA y).mp hy)
      rwa [show st.wa "hp_A" 0 = (u : ℕ) from rfl, keyOf_fin, keyOf_fin] at this
    · rw [hT', hT, Finset.map_erase]; rfl
    · have := log_le_log_succ (show m ≤ hs by omega)
      have h2 : Nat.log 2 m ≤ Nat.log 2 (m + 1) := Nat.log_mono_right (by omega)
      unfold copL
      nlinarith
  top_spec := by
    intro st T d Hh c0 hHR hL hTne hTfin hbud hcapN hszc
    obtain ⟨n, hn, hnN, hlA, hlP, hpos, hheap, hT⟩ := hHR
    have hcard : n = T.card := by rw [← hpos.card_T, hT, Finset.card_map]
    have hn1 : 0 < n := by rw [hcard]; exact Finset.card_pos.mpr hTne
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hK : KeyRepL d Hh st := ⟨hL.lens, hL.rep, by omega⟩
    have hH : IHeap.HeapRep (KeyRepL d Hh) (keyOf d) G.n st (m + 1) :=
      ⟨hK, hn, hnN, hlA, hlP, hpos, hheap⟩
    refine ((IHeap.runs_top (ops := realOps) hH hcapN).cost_mono).mono ?_
    rintro r ⟨⟨hv, hmin, ⟨hwa, hva, hwl, hvl, hcp, hpr, hvv, hw⟩, hc'⟩, hcl⟩
    have hA0 : st.wa "hp_A" 0 < G.n := (hpos.slots 0 (by omega)).1
    set u : Fin G.n := ⟨st.wa "hp_A" 0, hA0⟩ with hu
    have hmemA : ∀ y : Fin G.n, y ∈ T ↔ (y : ℕ) ∈ IHeap.T (st.wa "hp_A") (m + 1) := by
      intro y
      rw [hT, Finset.mem_map]
      constructor
      · intro h; exact ⟨y, h, rfl⟩
      · rintro ⟨z, hz, hzy⟩
        have : z = y := Fin.ext hzy
        rw [← this]; exact hz
    refine ⟨u, ?_, fun y hy => ?_, by rw [hv], ?_, ?_, hcl, ?_⟩
    · rw [hmemA]; simp only [IHeap.T, Finset.mem_image, Finset.mem_range]
      exact ⟨0, by omega, rfl⟩
    · have := hmin y ((hmemA y).mp hy)
      rwa [show st.wa "hp_A" 0 = (u : ℕ) from rfl, keyOf_fin, keyOf_fin] at this
    · refine ⟨m + 1, by rw [hw "hp_n" (by simp), hn], hnN, by rw [hwl, hlA], by rw [hwl, hlP],
        by rw [hwa]; exact hpos, by rw [hwa]; exact hheap, by rw [hwa]; exact hT⟩
    · refine ⟨fun a _ => ⟨by rw [hwa], by rw [hwl]⟩, fun a _ => ⟨by rw [hva], by rw [hvl]⟩,
        fun z hz => hw z (fun h => hz (by
          rw [List.mem_singleton] at h; subst h; simp [IHeap.hpRegs])), fun z _ => by rw [hvv],
        hcp, hpr⟩
    · unfold copL; omega

/-- IHeap stays out of the base case's arrays and registers. -/
theorem heapOK_heapL (hs : ℕ) : HeapOK (heapL (G := G) (s := s) hs) where
  wr := by simp only [heapL]; decide
  vr := by simp only [heapL]; decide
  wa := by simp only [heapL]; decide
  va := by simp only [heapL]; decide
  fwa := by simp only [heapL]; decide
  fwr := by simp only [heapL]; decide

end Frontier.CHD.RamBaseCase
