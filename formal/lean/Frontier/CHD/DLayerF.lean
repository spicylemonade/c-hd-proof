import Frontier.CHD.DMergeI
import Frontier.CHD.PullWrap
import Frontier.CHD.DProInst

/-!
# DLayerF — the D layer of the spine, assembled (B-L3, agent-04, NON-GATE)

`DLf T cn cm : RamSpine.DLayer G s T` is `DLayerInst.mkDL` with
* the representation `DRI (dParC cn cm)` (agent-09's parameters: top `LF + 1`, pool/block capacity
  `ucap + 2`, the selection routine `selBody entLess 1` at procedure index `1`);
* the four operations of `DLayerInst` (`dsIns`, `dsNew`, `dsDelB`, `dsEmpty`);
* agent-02's merge `dsMerge` (`DMergeI.dsMerge_ok`);
* agent-05's pull `pullW 1` (`PullWrap.pullOK_of`) inside `pullD`, which saves and restores the
  three spine registers `sp.go`, `sp.t`, `sl.i` the core pull uses as scratch (they are spine
  registers, so they may not belong to the D layer's register set).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.DLI

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.DB Frontier.CHD.DIns
  Frontier.CHD.DList Frontier.CHD.DGlob Frontier.CHD.MLab Frontier.CHD.LabTab Frontier.CHD.BM
  Frontier.CHD.RamLevel Frontier.CHD.RamBaseCase Frontier.CHD.PullWrap Frontier.RAM.SelectRAM
open Frontier.RAM.WExpr Frontier.RAM.Stmt

variable {G : Graph} {s : Fin G.n}

/-- the spine registers the core pull uses as scratch -/
def spSaved : List String := ["sp.go", "sp.t", "sl.i"]

/-- **the D-layer pull**: agent-05's `pullW 1`, with `sp.go`, `sp.t`, `sl.i` restored -/
def pullD : Stmt :=
  seq (wset "dp.go" (var "sp.go"))
  (seq (wset "dp.t" (var "sp.t"))
  (seq (wset "dp.si" (var "sl.i"))
  (seq (pullW 1)
  (seq (wset "sp.go" (var "dp.go"))
  (seq (wset "sp.t" (var "dp.t"))
       (wset "sl.i" (var "dp.si")))))))

/-- the word registers of `pullD` -/
def pdWR : List String := (pwWR.filter (· ∉ spSaved)) ++ ["dp.go", "dp.t", "dp.si"]

theorem unch_drop {st r : State ℝ≥0} {wa va wr vr xs : List String}
    (h : Unchanged st r wa va (wr ++ xs) vr) (hx : ∀ x ∈ xs, r.w x = st.w x) :
    Unchanged st r wa va wr vr :=
  ⟨h.warr, h.varr, fun x hx' => by
    by_cases hxs : x ∈ xs
    · exact hx x hxs
    · exact h.wreg x (by simp [hx', hxs]), h.vreg, h.cap, h.procs⟩

/-- **PullOK for `pullD`** from agent-05's `pullOK_of` -/
theorem pullD_ok (P : DPar) (T : ℕ → ℕ) (hsel : P.sel = selBody entLess P.psel) (hps : P.psel = 1)
    (wa va wr vr : List String) (K : ℕ) (hK : Kpw + 6 ≤ K)
    (hwa : ∀ a ∈ pwWA, a ∈ wa ++ ["S", "S.len"] ++ slotW) (hva : ∀ a ∈ pwVA, a ∈ va ++ ["sl.l"])
    (hwr : ∀ a ∈ pdWR, a ∈ wr) (hvr : ∀ a ∈ pwVR, a ∈ vr)
    (hdp : ∀ a ∈ ["dp.go", "dp.t", "dp.si"], a ∉ pwWR)
    (hdr : ∀ a ∈ drWR, a ∉ spSaved) :
    PullOK (G := G) (s := s) P T pullD wa va wr vr K := by
  have hPO := pullOK_of (G := G) (s := s) P T hsel wa va pwWR vr Kpw le_rfl hwa hva
    (fun a ha => ha) hvr
  rw [hps] at hPO
  intro st H g Ds l h1 hD hl hn hS hSL hH hu
  have hc := hD.lens.cap
  -- save the three registers
  refine runs_seq (runs_wset (a := st.w "sp.go") (by simp [evalW]) ?_)
  set q1 := (st.setW "dp.go" (st.w "sp.go")).charge 1 with hq1
  refine runs_seq (runs_wset (a := st.w "sp.t") (by simp [evalW, hq1]) ?_)
  set q2 := (q1.setW "dp.t" (st.w "sp.t")).charge 1 with hq2
  refine runs_seq (runs_wset (a := st.w "sl.i") (by simp [evalW, hq2, hq1]) ?_)
  set q3 := (q2.setW "dp.si" (st.w "sl.i")).charge 1 with hq3
  have hU3 : Unchanged st q3 [] [] ["dp.go", "dp.t", "dp.si"] [] := by
    rw [hq3, unch_charge, unch_setW (by simp), hq2, unch_charge, unch_setW (by simp), hq1, unch_charge,
      unch_setW (by simp)]
    exact Unchanged.refl _ _ _ _ _
  have hdrs : ∀ a ∈ drWR, a ∉ ["dp.go", "dp.t", "dp.si"] := by decide
  have hD3 : DRI P q3 H g Ds l := hD.frame_same hU3 (by simp) (by simp) hdrs (by simp)
  have hw3 : ∀ x, x ∉ ["dp.go", "dp.t", "dp.si"] → q3.w x = st.w x := hU3.wreg
  have hq3wa : q3.wa = st.wa := by simp [hq3, hq2, hq1]
  have hq3va : q3.va = st.va := by simp [hq3, hq2, hq1]
  have hq3wl : q3.wlen = st.wlen := by simp [hq3, hq2, hq1]
  have hq3vl : q3.vlen = st.vlen := by simp [hq3, hq2, hq1]
  have hvc3 : vc (G := G) q3 = vc st := vc_of hU3 (by simp)
  have hS3 : RowRep q3 "S" "S.len" G.n (l - 1) [] := by
    obtain ⟨a1, a2, a3, a4, a5⟩ := hS
    exact ⟨a1, by rw [hq3wl]; exact a2, by rw [hq3wl]; exact a3, by rw [hq3wa]; exact a4,
      fun i hi => absurd hi (by simp)⟩
  have hSL3 : SlotLens q3 (slotBi l) := by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hSL
    exact ⟨by rw [hq3vl]; exact a1, by rw [hq3wl]; exact a2, by rw [hq3wl]; exact a3,
      by rw [hq3wl]; exact a4, by rw [hq3wl]; exact a5, by rw [hq3wl]; exact a6⟩
  have hfr3 : q3.w "ds.fresh" = st.w "ds.fresh" := hw3 _ (by decide)
  have hbf3 : q3.w "blk.fresh" = st.w "blk.fresh" := hw3 _ (by decide)
  refine runs_seq ((hPO q3 H g Ds l h1 hD3 (by rw [hw3 _ (by decide)]; exact hl)
    (by rw [hw3 _ (by decide)]; exact hn) hS3 hSL3 (by rw [hvc3]; exact hH)
    (by rw [hfr3, hbf3]; exact hu)).mono (fun r4 hr4 => ?_))
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := hr4
  have hr4dp : ∀ a ∈ ["dp.go", "dp.t", "dp.si"], r4.w a = q3.w a := fun a ha => b4.wreg a (hdp a ha)
  -- restore
  refine runs_seq (runs_wset (a := st.w "sp.go") (by
    simp only [evalW]; rw [hr4dp _ (by simp)]; simp [hq3, hq2, hq1]) ?_)
  set r5 := (r4.setW "sp.go" (st.w "sp.go")).charge 1 with hr5
  refine runs_seq (runs_wset (a := st.w "sp.t") (by
    simp only [evalW, hr5, State.charge_w, State.setW_w]; rw [if_neg (by decide), hr4dp _ (by simp)]
    simp [hq3, hq2, hq1]) ?_)
  set r6 := (r5.setW "sp.t" (st.w "sp.t")).charge 1 with hr6
  refine runs_wset (a := st.w "sl.i") (by
    simp only [evalW, hr6, hr5, State.charge_w, State.setW_w]
    rw [if_neg (by decide), if_neg (by decide), hr4dp _ (by simp)]; simp [hq3]) ?_
  set r := (r6.setW "sl.i" (st.w "sl.i")).charge 1 with hr
  have hUr : Unchanged r4 r [] [] spSaved [] := by
    rw [hr, unch_charge, unch_setW (by simp [spSaved]), hr6, unch_charge, unch_setW (by simp [spSaved]),
      hr5, unch_charge, unch_setW (by simp [spSaved])]
    exact Unchanged.refl _ _ _ _ _
  have hrwa : r.wa = r4.wa := by simp [hr, hr6, hr5]
  have hrva : r.va = r4.va := by simp [hr, hr6, hr5]
  have hrwl : r.wlen = r4.wlen := by simp [hr, hr6, hr5]
  have hrvl : r.vlen = r4.vlen := by simp [hr, hr6, hr5]
  have hrs : ∀ a ∈ spSaved, r.w a = st.w a := by
    intro a ha
    simp only [spSaved, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> simp [hr, hr6, hr5]
  have hro : ∀ x, x ∉ spSaved → r.w x = r4.w x := hUr.wreg
  have hvcr : vc (G := G) r = vc r4 := by funext v; unfold vc; rw [hrwa]
  refine ⟨b1.frame_same hUr (by simp) (by simp) hdr (by simp), ?_, ?_, ?_, ?_, ?_,
    ?_, by rw [hrwl, b8, hq3wl], by rw [hrvl, b9, hq3vl], ?_, ?_, ?_⟩
  · obtain ⟨a1, a2, a3, a4, a5⟩ := b2
    exact ⟨a1, by rw [hrwl]; exact a2, by rw [hrwl]; exact a3, by rw [hrwa]; exact a4,
      fun i hi => by rw [hrwa]; exact a5 i hi⟩
  · rw [hvcr]
    obtain ⟨a1, a2⟩ := b3
    refine ⟨by rw [hrwa]; exact a1, fun q hq => ?_⟩
    obtain ⟨x, ⟨x1, x2, x3, x4, x5⟩, hxq⟩ := a2 q hq
    exact ⟨x, ⟨by rw [hrva]; exact x1, by rw [hrwa]; exact x2, by rw [hrwa]; exact x3,
      by rw [hrwa]; exact x4, by rw [hrwa]; exact x5⟩, hxq⟩
  · refine ⟨fun a ha => ?_, fun a ha => ?_, fun x hx => ?_, fun x hx => ?_, ?_, ?_⟩
    · rw [hrwa, hrwl, (b4.warr a ha).1, (b4.warr a ha).2, hq3wa, hq3wl]; exact ⟨rfl, rfl⟩
    · rw [hrva, hrvl, (b4.varr a ha).1, (b4.varr a ha).2, hq3va, hq3vl]; exact ⟨rfl, rfl⟩
    · by_cases hxs : x ∈ spSaved
      · exact hrs x hxs
      · have hxp : x ∉ pwWR := fun h' => hx (hwr x (List.mem_append_left _
          (List.mem_filter.mpr ⟨h', by simpa using hxs⟩)))
        have hxd : x ∉ ["dp.go", "dp.t", "dp.si"] := fun h' => hx (hwr x (List.mem_append_right _ h'))
        rw [hro x hxs, b4.wreg x hxp, hw3 x hxd]
    · rw [show r.v x = r4.v x by simp [hr, hr6, hr5], b4.vreg x hx]; simp [hq3, hq2, hq1]
    · rw [show r.cap = r4.cap by simp [hr, hr6, hr5], b4.cap]; simp [hq3, hq2, hq1]
    · rw [show r.procs = r4.procs by simp [hr, hr6, hr5], b4.procs]; simp [hq3, hq2, hq1]
  · intro i hi; rw [hrwa, b5 i hi, hq3wa]
  · intro j hj; rw [hrwa, b6 j hj, hq3wa]
  · intro i hi
    obtain ⟨c1, c2⟩ := b7 i hi
    exact ⟨by rw [hrva, c1, hq3va], fun a ha => by rw [hrwa, c2 a ha, hq3wa]⟩
  · have : q3.cost = st.cost + 3 := by simp [hq3, hq2, hq1]
    have : r.cost = r4.cost + 3 := by simp [hr, hr6, hr5]
    omega
  · have e1 : q3.cost = st.cost + 3 := by simp [hq3, hq2, hq1]
    have e2 : r.cost = r4.cost + 3 := by simp [hr, hr6, hr5]
    have hKc := Nat.mul_le_mul_right ((BM.pullC (dlOps G s) (T l) g (Ds l)).2.2.2.2 + 1) hK
    rw [Nat.add_mul] at hKc
    have : 6 ≤ 6 * ((BM.pullC (dlOps G s) (T l) g (Ds l)).2.2.2.2 + 1) := by omega
    omega
  · rw [hro _ (hdr _ (by simp [drWR])), hro _ (hdr _ (by simp [drWR]))]
    rw [hfr3, hbf3] at b12
    exact b12

/-! ## The name lists and the layer -/

/-- extra word arrays of the merge and the pull (beyond the representation's; expected empty) -/
def xWA : List String :=
  ((sWA dsMerge ++ pwWA).filter (fun a => a ∉ drWA ∧ a ∉ ["S", "S.len"] ++ slotW)).eraseDups
/-- extra value arrays of the merge and the pull (expected empty) -/
def xVA : List String := ((sVA dsMerge ++ pwVA).filter (fun a => a ∉ drVA ∧ a ≠ "sl.l")).eraseDups
/-- extra word registers of the merge and the pull -/
def xWR : List String := ((sWR dsMerge ++ pdWR).filter (fun a => a ∉ wrD)).eraseDups
/-- extra value registers of the merge and the pull -/
def xVR : List String := ((sVR dsMerge ++ pwVR).filter (fun a => a ∉ vrD)).eraseDups

set_option maxRecDepth 200000 in
theorem DLf_names : DNames (drWA ++ xWA) (drVA ++ xVA) (wrD ++ xWR) (vrD ++ xVR) :=
  dnames_of xWA xVA xWR xVR (by decide) (by decide) (by decide) (by decide)

theorem Kpw_ge : 40 ≤ Kpw + 6 := by unfold Kpw DPull.Kpull; omega

set_option maxRecDepth 200000 in
/-- **the D layer of the spine**: agent-09's parameters, the representation `DRI`, the four
operations of `DLayerInst`, agent-02's merge and agent-05's pull -/
def DLf (T : ℕ → ℕ) (cn cm : ℕ) : RamSpine.DLayer G s T :=
  mkDL (DPro.dParC cn cm) T (drWA ++ xWA) (drVA ++ xVA) (wrD ++ xWR) (vrD ++ xVR) DLf_names
    (Kpw + 6) Kpw_ge dsMerge pullD
    (dsMerge_ok _ (by decide) (by decide) (by decide) (by decide) (by unfold Kpw DPull.Kpull; omega))
    (pullD_ok _ T rfl rfl _ _ _ _ _ le_rfl (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide))

theorem DLf_DR (T : ℕ → ℕ) (cn cm : ℕ) : (DLf (G := G) (s := s) T cn cm).DR = DRI (DPro.dParC cn cm) :=
  rfl
theorem DLf_use (T : ℕ → ℕ) (cn cm : ℕ) (st : State ℝ≥0) :
    (DLf (G := G) (s := s) T cn cm).use st = st.w "ds.fresh" + st.w "blk.fresh" := rfl
theorem DLf_ucap (T : ℕ → ℕ) (cn cm : ℕ) :
    (DLf (G := G) (s := s) T cn cm).ucap = (DPro.dParC cn cm).ucap := rfl

end Frontier.CHD.DLI
