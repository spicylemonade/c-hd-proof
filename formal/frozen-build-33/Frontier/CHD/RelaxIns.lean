import Frontier.CHD.DRepExt
import Frontier.CHD.DInsertB
import Frontier.CHD.DInsertL
import Frontier.CHD.BMLazy
import Frontier.CHD.LabI

/-!
# RelaxIns — the per-edge relaxation with insertion into the lazy D (agent-02, B-L4 support,
NON-GATE)

`relaxInsRAM` implements BMLazy's `relaxInsCc dlOps T B lo st e`, the step shared by BM.19–21,
BM.27–28 and BC.7:

1. `relaxBM K kf` — `ok := [ValidRelax d B e]`, the label table becomes the label part of
   `relaxIns`, the candidate `d (src e) ⊕ e` stays in `X0`;
2. if `ok`: the `lo` test `lab.ge := [lo ≤ cand]` (bound block `Lo`/`lof`; `lo = none` is encoded
   by the caller setting `lab.uselo := 0`);
3. if both: copy the candidate into the insertion key block `KB`, `ds.v := dst e`, `insRAM`.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RelaxIns

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.MLab
  Frontier.CHD.LabTab Frontier.CHD.DIns WExpr Stmt

variable {G : Graph} {s : Fin G.n}

/-- `KB := X0` and `ds.v := X0.v` (6 moves). -/
def copyCand : Stmt :=
  seq (vset KB.l (.var X0.l)) (seq (wset KB.h (var X0.h)) (seq (wset KB.v (var X0.v))
  (seq (wset KB.e (var X0.e)) (seq (wset KB.r (var X0.r)) (wset "ds.v" (var X0.v))))))

/-- The `lo` test: `lab.ge := 1` if `lab.uselo = 0`, else `lab.ge := [¬ (X0 < Lo)]`. -/
def loTest (Lo : LReg) (lof : String) : Stmt :=
  ite (var "lab.uselo")
    (seq (ltB X0 Lo lof "lab.c1" "lab.c2" "lab.lolt") (wset "lab.ge" (eq (var "lab.lolt") (lit 0))))
    (wset "lab.ge" (lit 1))

/-- **One relaxation with insertion** (BMLazy `relaxInsCc` for `dlOps`). -/
def relaxInsRAM (K : LReg) (kf : String) (Lo : LReg) (lof : String) : Stmt :=
  seq (relaxBM K kf)
  (ite (var "ok")
    (seq (loTest Lo lof) (ite (var "lab.ge") (seq copyCand insRAM) skip))
    skip)

/-- Registers `relaxInsRAM` may write. -/
def riW : List String :=
  relaxW ++ ["lab.c1", "lab.c2", "lab.lolt", "lab.ge"] ++ KB.ws ++ ["ds.v"] ++ insWR
/-- Value registers `relaxInsRAM` may write. -/
def riV : List String := relaxV ++ [KB.l, YB.l]

open Classical in
/-- The state `relaxInsCc dlOps T B lo st e` (BMLazy) in closed form for a valid relaxation. -/
theorem relaxInsCc_valid (T : ℕ) (B : WLab G s) (lo : Option (WLab G s)) (st : BM.RSt G s)
    (e : Fin G.m) (hv : BM.ValidRelax G s st.d B e) :
    BM.relaxInsCc (BM.dlOps G s) T B lo st e =
      if (match lo with | none => True | some b => b ≤ ext (st.d (G.src e)) e) then
        ⟨Function.update st.d (G.dst e) (ext (st.d (G.src e)) e),
          (BM.insC (BM.dlOps G s) T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).1,
          (BM.insC (BM.dlOps G s) T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).2.1,
          st.c + 1 + (BM.insC (BM.dlOps G s) T st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)).2.2⟩
      else ⟨Function.update st.d (G.dst e) (ext (st.d (G.src e)) e), st.g, st.Dc, st.c + 1⟩ := by
  unfold BM.relaxInsCc
  rw [if_pos hv]
  cases lo with
  | none => simp
  | some b => by_cases hb : b ≤ ext (st.d (G.src e)) e <;> simp [hb]

theorem PoolRep.of_unchanged {st r : State ℝ≥0} {fresh ecap : ℕ} {wa va wr vr : List String}
    (h : PoolRep st fresh ecap) (hu : Unchanged st r wa va wr vr) (hw : ∀ a ∈ wa, a ∉ dW)
    (hv : ∀ a ∈ va, a ∉ dV) (hf : "ds.fresh" ∉ wr) : PoolRep r fresh ecap := by
  obtain ⟨h1, h2, e1, e2, e3, e4, e5, e6, e7⟩ := h
  refine ⟨by rw [hu.wreg _ hf]; exact h1, h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [(wa_eq hu hw (by simp [dW, entA])).2]; assumption)
    | (rw [(va_eq hu hv (by simp [dV, entA])).2]; assumption)

theorem insC_dl (T : ℕ) (g : BM.DGl G s) (Dc : BM.DStrM G s) (v : Fin G.n) (lam : WLab G s) :
    (BM.insC (BM.dlOps G s) T g Dc v lam).1.L = (insertNS g.L g.fresh Dc v lam).1 ∧
    (BM.insC (BM.dlOps G s) T g Dc v lam).1.fresh = (insertNS g.L g.fresh Dc v lam).2.1 ∧
    (BM.insC (BM.dlOps G s) T g Dc v lam).2.1 = (insertNS g.L g.fresh Dc v lam).2.2 := by
  have h := insertL_eq_insertNS g.L g.fresh Dc v lam
  simp only [Prod.ext_iff] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- The Layer-A cost of one `dlOps` insertion (DLazy `insertL`). -/
theorem insC_dl_cost (T : ℕ) (g : BM.DGl G s) (Dc : BM.DStrM G s) (v : Fin G.n) (lam : WLab G s) :
    (BM.insC (BM.dlOps G s) T g Dc v lam).2.2 =
      if DB.skipIns g.L v lam = true then 2 else DL.bsCost Dc.blocks.length + 3 := rfl

theorem copyCand_wp (st : State ℝ≥0) (x : MLabel G) (hX : Holds st X0 x) :
    wp realOps copyCand (fun r => Holds r KB x ∧ Holds r X0 x ∧ r.w "ds.v" = x.v ∧
      Unchanged st r [] [] (KB.ws ++ ["ds.v"]) [KB.l] ∧ r.cost = st.cost + 6) st := by
  obtain ⟨x1, x2, x3, x4, x5⟩ := hX
  simp only [copyCand, wp, evalV_var', evalW_var, State.charge_w, State.charge_v, State.setV_w,
    State.setW_v, State.setV_v, State.setW_w]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals first
    | (simp [State.setW, State.setV, State.charge, KB, X0] at *; assumption)
    | (simp [State.setW, State.setV, State.charge, KB, X0, x1, x2, x3, x4, x5]; done)
    | skip
  · simp only [unch_charge]
    rw [unch_setW (by simp [LReg.ws]), unch_charge, unch_setW (by simp [KB, LReg.ws]), unch_charge,
      unch_setW (by simp [KB, LReg.ws]), unch_charge, unch_setW (by simp [KB, LReg.ws]), unch_charge,
      unch_setW (by simp [KB, LReg.ws]), unch_charge, unch_setV (by simp)]
    simp

open Classical in
/-- Postcondition of `relaxInsRAM` relative to the entry state `st`. -/
def RIPost (T : ℕ) (st : State ℝ≥0) (d : Labels G s) (H : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ)
    (B : WLab G s) (lo : Option (WLab G s)) (g : BM.DGl G s) (Dc : BM.DStrM G s) (c : ℕ)
    (bcap ecap lv bse : ℕ) (e : Fin G.m) (r : State ℝ≥0) : Prop :=
  ∃ H', HExt H (vc st) H' (vc r) ∧
    LabAt r (BM.relaxInsCc (BM.dlOps G s) T B lo ⟨d, g, Dc, c⟩ e).d H' c0 ∧
    DRep r H' (vc r) bcap lv bse (BM.relaxInsCc (BM.dlOps G s) T B lo ⟨d, g, Dc, c⟩ e).Dc ∧
    BlkArrs r bcap ∧
    LiveRep r H' (vc r) (BM.relaxInsCc (BM.dlOps G s) T B lo ⟨d, g, Dc, c⟩ e).g.L ∧
    PoolRep r (BM.relaxInsCc (BM.dlOps G s) T B lo ⟨d, g, Dc, c⟩ e).g.fresh ecap ∧
    GraphAt r G ∧ Unchanged st r (labW ++ insWA) (labV ++ [entA.l]) riW riV ∧
    st.cost ≤ r.cost ∧ r.cost ≤ st.cost + 190 + 35 * (Nat.log 2 (Dc.blocks.length - 1) + 1) ∧
    r.cost + 100 * c ≤ st.cost + 100 * (BM.relaxInsCc (BM.dlOps G s) T B lo ⟨d, g, Dc, c⟩ e).c

set_option maxHeartbeats 1000000 in
open Classical in
/-- **Spec of `relaxInsRAM`**: refines `relaxInsCc dlOps T B lo ⟨d, g, Dc, c⟩ e` on the label
table, the level-`lv` structure `Dc`, the live map and the pool (ghost history extended). -/
theorem relaxInsRAM_spec (T : ℕ) (st : State ℝ≥0) (d : Labels G s)
    (H : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ) (hL : LabAt st d H c0) (hg : GraphAt st G)
    (e : Fin G.m) (hru : st.w "ru" = G.src e) (hre : st.w "re" = e) (hu : d (G.src e) ≠ ⊤)
    (K : LReg) (kf : String) (hKr : BoundRegs K kf) (B : WLab G s)
    (hK : WHolds st K kf H (vc st) B) (Lo : LReg) (lof : String) (hLor : BoundRegs Lo lof)
    (lo : Option (WLab G s))
    (hlo : (lo = none ∧ st.w "lab.uselo" = 0) ∨
      (∃ b, lo = some b ∧ st.w "lab.uselo" ≠ 0 ∧ WHolds st Lo lof H (vc st) b))
    (hLod : ∀ a ∈ Lo.ws, a ∉ ["lab.lolt", "lab.ge"]) (hlofd : lof ∉ ["lab.lolt", "lab.ge"])
    (hLoKB : "lab.uselo" ∉ riW)
    (g : BM.DGl G s) (Dc : BM.DStrM G s) (bcap ecap lv bse : ℕ)
    (hD : DRep st H (vc st) bcap lv bse Dc) (hBA : BlkArrs st bcap)
    (hLv : LiveRep st H (vc st) g.L) (hP : PoolRep st g.fresh ecap) (hwf : DB.WF g.L Dc)
    (hfr : DB.FreshOK g.fresh Dc) (hid : DB.IdsNodup Dc)
    (hLf : ∀ u i a, g.L u = some (i, a) → i < g.fresh) (hlv : st.w "ds.lv" = lv)
    (hb : st.w "ds.b" = bse) (hfr1 : g.fresh + 1 < ecap)
    (hcapD : 2 * Dc.blocks.length + ecap + bse + 4 < st.cap)
    (hB : st.cost + 64 ≤ c0 + st.cap) (hm : G.m + 2 ≤ st.cap) (c : ℕ) :
    Runs realOps (relaxInsRAM K kf Lo lof) st
      (RIPost T st d H c0 B lo g Dc c bcap ecap lv bse e) := by
  obtain ⟨p0, hp⟩ : ∃ p : List (Fin G.m), d (G.src e) = ((toW p : WalkOrd G s) : WLab G s) := by
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hu
    exact ⟨q, hq.symm⟩
  have hext : ext (d (G.src e)) e = ((toW (p0 ++ [e]) : WalkOrd G s) : WLab G s) := cand_ext e hp
  have hcap1 : 1 < st.cap := by omega
  apply runs_seq
  refine (Frontier.CHD.LabIInst.Runs.cost_ge
    (relaxBM_spec st d H c0 hL hg e hru hre hu K kf hKr B hK hB hm)).mono ?_
  rintro r1 ⟨⟨H1, hL1, hE1, hok1, hX1, hrep1, hg1, hU1, hc1⟩, hc1lo⟩
  -- transport the D side to r1 and the extended history
  have hw1 : ∀ a ∈ labW, a ∉ dW := labW_disj_dW
  have hv1 : ∀ a ∈ labV, a ∉ dV := labV_disj_dV
  have hD1 : DRep r1 H1 (vc r1) bcap lv bse Dc := (hD.ext hE1).of_unchanged hU1 hw1 hv1
  have hBA1 : BlkArrs r1 bcap := hBA.of_unchanged hU1 hw1 hv1
  have hLv1 : LiveRep r1 H1 (vc r1) g.L := (hLv.ext hE1).of_unchanged hU1 hw1 hv1
  have hP1 : PoolRep r1 g.fresh ecap := PoolRep.of_unchanged hP hU1 hw1 hv1 (by decide)
  have hcap1' : r1.cap = st.cap := hU1.cap
  have hw0 : ∀ a ∈ ([] : List String), a ∉ dW := by simp
  have hv0 : ∀ a ∈ ([] : List String), a ∉ dV := by simp
  by_cases hvr : BM.ValidRelax G s d B e
  · -- valid: the lo test and the insertion
    have hok : r1.w "ok" = 1 := by rw [hok1, if_pos hvr]
    rw [if_pos hvr] at hL1
    apply runs_ite_true (by simp [hok] : evalW r1 (WExpr.var "ok") = some 1) one_ne_zero
    set r1c := r1.charge 1 with hr1c
    have hUc : Unchanged r1 r1c [] [] [] [] := Unchanged.charge r1 1 [] [] [] []
    have hcand : Rep (s := s) H1 (vc r1) (cand (tabOf (G := G) st) e) (p0 ++ [e]) := hrep1 p0 hp
    have hXc : Holds r1c X0 (cand (tabOf (G := G) st) e) := hX1.charge 1
    -- the lo test: afterwards `lab.ge = [lo admits the candidate]`
    have hlo_ok : ∀ q : State ℝ≥0, Unchanged r1c q [] [] ["lab.c1", "lab.c2", "lab.lolt", "lab.ge"] [] →
        q.cost ≤ r1c.cost + 16 → r1c.cost + 1 ≤ q.cost →
        q.w "lab.ge" = (if (match lo with | none => True | some b => b ≤ ext (d (G.src e)) e)
          then 1 else 0) → Runs realOps (ite (var "lab.ge") (seq copyCand insRAM) skip) q
          (RIPost T st d H c0 B lo g Dc c bcap ecap lv bse e) := by
      intro q hUq hcq hcq' hge
      have hUq' : Unchanged st q labW labV (relaxW ++ ["lab.c1", "lab.c2", "lab.lolt", "lab.ge"]) relaxV :=
        ((hU1.comp hUc).comp hUq).mono (by simp) (by simp) (by decide) (by simp)
      have hres := relaxInsCc_valid T B lo ⟨d, g, Dc, c⟩ e hvr
      simp only at hres
      have hwq : ∀ a ∈ ([] : List String), a ∉ dW := by simp
      have hL2 : LabAt q (Function.update d (G.dst e) (ext (d (G.src e)) e)) H1 c0 :=
        hL1.of_unchanged (hUc.comp hUq) (by simp) (by simp) (by simp only [hr1c, State.charge_cost] at hcq'; omega)
      have hvcq : vc (G := G) q = vc r1 := vc_of_unchanged (hUc.comp hUq) (by simp)
      have hD2 := hD1.of_unchanged (hUc.comp hUq) (by simp) (by simp)
      have hBA2 := hBA1.of_unchanged (hUc.comp hUq) (by simp) (by simp)
      have hLv2 := hLv1.of_unchanged (hUc.comp hUq) (by simp) (by simp)
      have hP2 := PoolRep.of_unchanged hP1 (hUc.comp hUq) (by simp) (by simp) (by decide)
      have hg2 := graphAt_of_unchanged (hUc.comp hUq) (by simp) (by simp) hg1
      rw [← hvcq] at hD2 hLv2
      by_cases hadm : (match lo with | none => True | some b => b ≤ ext (d (G.src e)) e)
      · -- insert the candidate
        rw [if_pos hadm] at hres
        have hge1 : q.w "lab.ge" = 1 := by rw [hge, if_pos hadm]
        apply runs_ite_true (by simp [hge1] : evalW q (WExpr.var "lab.ge") = some 1) one_ne_zero
        apply runs_seq
        apply wp_sound
        have hX2 : Holds (q.charge 1) X0 (cand (tabOf (G := G) st) e) :=
          (hXc.of_unchanged hUq (by decide) (by decide)).charge 1
        refine wp_mono _ ?_ _ (copyCand_wp (q.charge 1) _ hX2)
        rintro q4 ⟨hK4, -, hv4, hU4, hc4⟩
        have hUq4 : Unchanged q q4 [] [] (KB.ws ++ ["ds.v"]) [KB.l] :=
          ((Unchanged.charge q 1 [] [] [] []).comp hU4).mono (by simp) (by simp) (by simp) (by simp)
        have hw4 : ∀ a ∈ ([] : List String), a ∉ dW := by simp
        have hD4 := hD2.of_unchanged hUq4 hw4 hv0
        have hBA4 := hBA2.of_unchanged hUq4 hw4 hv0
        have hLv4 := hLv2.of_unchanged hUq4 hw4 hv0
        have hP4 := PoolRep.of_unchanged hP2 hUq4 hw4 hv0 (by decide)
        have hvc4 : vc (G := G) q4 = vc q := vc_of_unchanged hUq4 (by simp)
        have hL4 : LabAt q4 (Function.update d (G.dst e) (ext (d (G.src e)) e)) H1 c0 :=
          hL2.of_unchanged hUq4 (by simp) (by simp) (by simp only [State.charge_cost] at hc4; omega)
        have hcap4 : q4.cap = st.cap := by rw [hUq4.cap, hUq.cap, hUc.cap, hU1.cap]
        have hlv4 : q4.w "ds.lv" = lv := by
          rw [hUq4.wreg _ (by decide), hUq.wreg _ (by decide), hUc.wreg _ (by simp),
            hU1.wreg _ (by decide)]; exact hlv
        have hb4 : q4.w "ds.b" = bse := by
          rw [hUq4.wreg _ (by decide), hUq.wreg _ (by decide), hUc.wreg _ (by simp),
            hU1.wreg _ (by decide)]; exact hb
        rw [← hvc4] at hD4 hLv4
        have hH4 : GoodHist (s := s) H1 (vc (G := G) q4) := by rw [hvc4, hvcq]; exact hL1.rep.hist
        have hrep4 : Rep (s := s) H1 (vc (G := G) q4) (cand (tabOf (G := G) st) e) (p0 ++ [e]) := by
          rw [hvc4, hvcq]; exact hcand
        have hins := insRAM_spec H1 (vc q4) hH4 bcap ecap lv bse g.fresh Dc g.L q4 hD4 hBA4 hLv4
          hP4 hwf hfr hid hLf (G.dst e) (by rw [hv4]; rfl) hlv4 hb4 _ (p0 ++ [e]) hK4 hrep4 hfr1
          (by rw [hcap4]; exact hcapD)
        refine hins.mono ?_
        rintro r ⟨hDr, hBAr, hLvr, hPr, hUr, -, hcr1, hcr2⟩
        obtain ⟨cL, cF, cD⟩ := insC_dl (G := G) (s := s) T g Dc (G.dst e) (ext (d (G.src e)) e)
        rw [RIPost, hres]
        simp only
        rw [cL, cF, cD, hext]
        have hvcr : vc (G := G) r = vc q4 := vc_of_unchanged hUr (by decide)
        refine ⟨H1, by rw [hvcr, hvc4, hvcq]; exact hE1, ?_, by rw [hvcr]; exact hDr, hBAr,
          by rw [hvcr]; exact hLvr, hPr, ?_, ?_, ?_, ?_, ?_⟩
        · rw [← hext]
          exact hL4.of_unchanged hUr (by decide) (by decide) hcr1
        · exact graphAt_of_unchanged (hUq4.comp hUr) (by decide) (by decide) hg2
        · exact (((hUq'.comp hUq4).comp hUr)).mono
            (by decide) (by decide) (by decide) (by decide)
        · simp only [hr1c, State.charge_cost] at hcq' hc4; omega
        · simp only [hr1c, State.charge_cost] at hcq hc4
          split_ifs at hcr2 <;> omega
        · rw [insC_dl_cost]
          have hlog : Nat.log 2 (Dc.blocks.length - 1) ≤ Nat.log 2 Dc.blocks.length :=
            Nat.log_mono_right (Nat.sub_le _ _)
          simp only [hr1c, State.charge_cost] at hcq hc4
          unfold DL.bsCost
          split_ifs at hcr2 ⊢ <;> omega
      · -- the lo bound rejects: only the label changed
        rw [if_neg hadm] at hres
        have hge0 : q.w "lab.ge" = 0 := by rw [hge, if_neg hadm]
        apply runs_ite_false (by simp [hge0])
        apply wp_sound
        rw [wp_skip]
        have hUz : Unchanged q ((q.charge 1).charge 1) [] [] [] [] := by simp
        rw [RIPost, hres]
        refine ⟨H1, by rw [show vc (G := G) ((q.charge 1).charge 1) = vc r1 from hvcq]; exact hE1,
          hL2.of_unchanged hUz (by simp) (by simp) (by simp only [State.charge_cost]; omega),
          hD2.of_unchanged hUz hw0 hv0, hBA2.of_unchanged hUz hw0 hv0,
          hLv2.of_unchanged hUz hw0 hv0, PoolRep.of_unchanged hP2 hUz hw0 hv0 (by simp),
          graphAt_of_unchanged hUz (by simp) (by simp) hg2,
          ((hUq'.comp hUz).mono (by decide) (by decide) (by decide) (by decide)), ?_, ?_, ?_⟩
        · simp only [hr1c, State.charge_cost] at hcq' ⊢; omega
        · simp only [State.charge_cost, hr1c] at hcq ⊢; omega
        · simp only [State.charge_cost, hr1c] at hcq ⊢; omega
    -- run the lo test from r1c, then hand over to `hlo_ok`
    apply runs_seq
    have hcapc : 1 < r1c.cap := by rw [hr1c]; simp [hcap1']; exact hcap1
    rw [loTest]
    rcases hlo with ⟨hlo0, hul⟩ | ⟨b, hlob, hul, hLo⟩
    · -- lo = none
      subst hlo0
      have hul' : r1c.w "lab.uselo" = 0 := by
        rw [hr1c]; simp only [State.charge_w]
        rw [hU1.wreg "lab.uselo" (fun h => hLoKB (by simp only [riW, List.mem_append]; tauto))]
        exact hul
      apply runs_ite_false (by simp [hul'])
      apply wp_sound
      refine wp_mono _ ?_ _ (wset_lit_wp (ops := realOps) "lab.ge" 1 (r1c.charge 1) (by simpa using hcapc))
      rintro q ⟨h1, h2, h3⟩
      exact hlo_ok q (((Unchanged.charge r1c 1 [] [] [] []).comp h2).mono (by simp) (by simp)
        (by decide) (by simp)) (by simp at h3 ⊢; omega) (by simp at h3 ⊢; omega) (by rw [h1]; simp)
    · -- lo = some b
      subst hlob
      have hul' : r1c.w "lab.uselo" ≠ 0 := by
        rw [hr1c]; simp only [State.charge_w]
        rw [hU1.wreg "lab.uselo" (fun h => hLoKB (by simp only [riW, List.mem_append]; tauto))]
        exact hul
      apply runs_ite_true (by simp : evalW r1c (WExpr.var "lab.uselo") = some (r1c.w "lab.uselo")) hul'
      have hLoc : WHolds (r1c.charge 1) Lo lof H1 (vc r1) b :=
        WHolds.of_unchanged (WHolds.of_unchanged (hLo.ext hE1) hU1 (fun a ha h => hLor.ws a ha h)
          (fun h => hLor.l h) (fun h => hLor.f h))
          ((hUc.comp (Unchanged.charge r1c 1 [] [] [] []))) (by simp) (by simp) (by simp)
      have hc1' : "lab.c1" ∉ Lo.ws := fun h => hLor.ws _ h (by decide)
      have hc2' : "lab.c2" ∉ Lo.ws := fun h => hLor.ws _ h (by decide)
      apply runs_seq
      apply wp_sound
      refine wp_mono _ ?_ _ (ltB_wp X0 Lo lof "lab.c1" "lab.c2" "lab.lolt"
        ⟨by decide, by decide, by decide, hc1', hc2'⟩ (r1c.charge 1) (by simpa using hcapc))
      rintro q1 ⟨hlt1, hUl, hcl1, hcl2⟩
      have hbit := ltB_bit (V := vc r1) hL1.rep.hist (hXc.charge 1) hcand hLoc
      rw [hbit, ← hext] at hlt1
      apply wp_sound
      refine wp_mono _ ?_ _ (wset_eqz_wp (ops := realOps) "lab.ge" "lab.lolt" q1
        (by rw [hUl.cap]; simpa using hcapc))
      rintro q ⟨h1, h2, h3⟩
      refine hlo_ok q ((((Unchanged.charge r1c 1 [] [] [] []).comp hUl).comp h2).mono (by simp)
        (by simp) (by decide) (by simp)) (by simp at hcl2 h3 ⊢; omega) (by simp at hcl1 h3 ⊢; omega) ?_
      rw [h1, hlt1]
      simp only
      by_cases hle : b ≤ ext (d (G.src e)) e
      · rw [if_neg (not_lt.mpr hle), if_pos rfl, if_pos hle]
      · rw [if_pos (lt_of_not_ge hle), if_neg one_ne_zero, if_neg hle]
  · -- invalid: nothing else happens
    have hok : r1.w "ok" = 0 := by rw [hok1, if_neg hvr]
    apply runs_ite_false (by simp [hok])
    apply wp_sound
    rw [wp_skip]
    have hres : BM.relaxInsCc (BM.dlOps G s) T B lo ⟨d, g, Dc, c⟩ e = ⟨d, g, Dc, c + 1⟩ := by
      unfold BM.relaxInsCc; rw [if_neg hvr]
    rw [if_neg hvr] at hL1
    have hUc : Unchanged r1 ((r1.charge 1).charge 1) [] [] [] [] := by simp
    rw [RIPost, hres]
    refine ⟨H1, hE1, hL1.of_unchanged hUc (by simp) (by simp) (by simp only [State.charge_cost]; omega), hD1.of_unchanged hUc hw0 hv0,
      hBA1.of_unchanged hUc hw0 hv0, hLv1.of_unchanged hUc hw0 hv0,
      PoolRep.of_unchanged hP1 hUc hw0 hv0 (by simp), graphAt_of_unchanged hUc (by simp) (by simp) hg1,
      ((hU1.comp hUc).mono (by decide) (by decide) (by decide) (by decide)), ?_, ?_, ?_⟩
    · simp; omega
    · simp; omega
    · simp; omega

end Frontier.CHD.RelaxIns
