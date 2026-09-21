import Frontier.CHD.BL2StepE

/-!
# Frontier.CHD.BL2ScanSpec — B-L2: the RAM scan of one out-list refines Layer A's `Scan`
(agent-09, scratch, NON-GATE)

`scan_spec`: from any machine state representing a search state `σ₀` (labels, slots, heap,
members, bitmaps, live out-lists) with the extracted vertex in `fp.u`, the program `fpScan`
terminates in a state representing SOME Layer-A outcome `Scan c T u σ₀ (c.out u) σ' r n`, with
the result code in `fp.res` (and the contact edge in `fp.cu`/`fp.cv`), the history extended,
exactly the declared write sets touched, and machine cost `≤ 5 + Kit * n` where `n` is the
Layer-A cost.  Budget hypothesis in agent-08's RefinesB form: every Layer-A outcome fits.
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}
variable {LI : LabI V ops G s} {c : FPCtx G s} {T : Finset (Fin G.n)} {slB slX : String}
  {u : Fin G.n}

theorem LabRep.charge {c : FPCtx G s} {slB slX : String} {d : Labels G s} {g : LI.Gh}
    {st : State V} (h : LabRep LI c slB slX d g st) (k : ℕ) : LabRep LI c slB slX d g (st.charge k) :=
  h.frame (Unchanged.charge st k [] [] [] []) (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _)
    (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _)
    (Disj.nil_left _) (Disj.nil_left _) (by simp)

theorem OutRep.charge {c : FPCtx G s} {D : Finset (Fin G.m)} {st : State V} (h : OutRep st c D)
    (k : ℕ) : OutRep (st.charge k) c D :=
  h.frameR (Unchanged.charge st k [] [] [] []) (Disj.nil_left _)

/-- The postcondition of the scan. -/
def ScanPost (LI : LabI V ops G s) (c : FPCtx G s) (T : Finset (Fin G.n)) (slB slX : String)
    (u : Fin G.n) (σ₀ : SSt G s) (g₀ : LI.Gh) (st₀ st' : State V) : Prop :=
  ∃ σ' r n g', Scan c T u σ₀ (c.out u) σ' r n ∧ LabRep LI c slB slX σ'.d g' st' ∧
    MyRep c T σ' st' ∧ OutRep st' c σ'.D ∧ st'.w "fp.u" = u ∧ ResCode st' r σ' ∧ LI.gext g₀ g' ∧
    Unchanged st₀ st' (scanWA LI) (scanVA LI) (scanWR LI) (scanVR LI) ∧
    st₀.cost ≤ st'.cost ∧ st'.cost ≤ st₀.cost + 5 + Kit LI * n

theorem scan_spec (hown : OutOK c) (hnd : OutNodup c) (hN : Names LI slB slX)
    {σ₀ : SSt G s} {g₀ : LI.Gh} {st₀ : State V}
    (hL : LabRep LI c slB slX σ₀.d g₀ st₀) (hM : MyRep c T σ₀ st₀) (hO : OutRep st₀ c σ₀.D)
    (hu : st₀.w "fp.u" = u) (hfin : σ₀.d u ≠ ⊤) (hK : σ₀.K.length < c.k)
    (hbud : ∀ σ' r n', Scan c T u σ₀ (c.out u) σ' r n' →
      st₀.cost + 5 + Kit LI * n' + Kit LI ≤ LI.c0 + st₀.cap)
    (hcapW : c.k + 4 < st₀.cap) :
    Runs ops (fpScan LI slB slX) st₀ (ScanPost LI c T slB slX u σ₀ g₀ st₀) := by
  have huL : (u : ℕ) < st₀.wlen "gHd" := lt_of_lt_of_le u.isLt hO.1
  have hgM : st₀.w "gM" = G.m := hM.gM
  -- initialization
  unfold fpScan fpScanInit
  refine runs_seq ?_
  apply wp_sound
  simp only [wp, evalW_var, evalW_load', evalW_lit', evalW_lt', State.charge_w, State.setW_w,
    State.charge_wa, State.setW_wa, State.charge_wlen, State.setW_wlen, State.charge_cap,
    State.setW_cap, Option.bind_some, hu, huL, ite_true, hgM, fit,
    show (0 : ℕ) < st₀.cap by omega]
  simp only [show ("fp.p" = "fp.pp") = False by decide, show ("fp.p" = "fp.res") = False by decide,
    show ("gM" = "fp.p") = False by decide, show ("gM" = "fp.pp") = False by decide,
    show ("gM" = "fp.res") = False by decide, show ("fp.u" = "fp.p") = False by decide, ite_false,
    ite_true, hgM,
    show (if st₀.wa "gHd" ↑u < G.m then 1 else 0) < st₀.cap by split_ifs <;> omega]
  generalize hst1 : ((((((((st₀.setW "fp.p" (st₀.wa "gHd" ↑u)).charge 1).setW "fp.pp"
    G.m).charge 1).setW "fp.res" 0).charge 1).setW "fp.go"
    (if st₀.wa "gHd" ↑u < G.m then 1 else 0)).charge 1) = st1
  have hu1 : Unchanged st₀ st1 [] [] ["fp.p", "fp.pp", "fp.res", "fp.go"] [] := by
    rw [← hst1]
    refine ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun x hx => ?_, fun _ _ => rfl, rfl, rfl⟩
    simp only [List.mem_cons, not_or, List.not_mem_nil, or_false] at hx
    simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2]
  have hc1 : st1.cost = st₀.cost + 4 := by rw [← hst1]; simp
  have hp1 : st1.w "fp.p" = st₀.wa "gHd" u := by rw [← hst1]; simp
  have hpp1 : st1.w "fp.pp" = G.m := by rw [← hst1]; simp
  have hres1 : st1.w "fp.res" = 0 := by rw [← hst1]; simp
  have hgo1 : st1.w "fp.go" = if st1.w "fp.p" < G.m then 1 else 0 := by rw [hp1, ← hst1]; simp
  have hwa1 : st1.wa = st₀.wa := by rw [← hst1]; rfl
  have hwl1 : st1.wlen = st₀.wlen := by rw [← hst1]; rfl
  have hRd : Disj ["fp.p", "fp.pp", "fp.res", "fp.go"] myRepRegs := by decide
  have hC1 : Core LI c T slB slX u σ₀ (c.out u) g₀ st1 := by
    refine ⟨hL.frame hu1 (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _)
        (hN.myR_slB.mono_left (by simp [myRegs])) (Disj.nil_left _) (Disj.nil_left _)
        (Disj.nil_left _) (hN.myR_slX.mono_left (by simp [myRegs])) (Disj.nil_left _) (by omega),
      hM.frameR hu1 (Disj.nil_left _) hRd, ?_, ?_, hres1, hgo1⟩
    · refine ⟨by rw [hwl1]; exact hO.1, fun w _ => by
        rw [hwa1]; exact Seg.of_eq (st' := st1) (hO.2 w) (by rw [hwa1]) (by rw [hwl1]),
        [], by simp, ?_, ?_, Or.inl ⟨by simp, hpp1⟩⟩
      · rw [hp1, hwa1]; exact Seg.nil _
      · rw [hp1]; exact Seg.of_eq (st' := st1) (hO.2 u) (by rw [hwa1]) (by rw [hwl1])
    · rw [hu1.wreg "fp.u" (by decide)]; exact hu
  have hbook1 : Book LI st₀ st1 0 := ⟨hu1.mono (by simp) (by simp) (by scan_sub) (by simp),
    by omega, by omega⟩
  -- the loop
  refine runs_while_nat (LoopI LI c T slB slX u σ₀ g₀ st₀) _ ?_ ((c.out u).length + 1) st1
    (Or.inl ⟨σ₀, c.out u, 0, g₀, rfl, ⟨hC1, hfin, hK, LI.gext_refl g₀,
      fun σ' r n' h' => by simpa using h', hbook1⟩⟩)
  intro m st hI
  rcases hI with ⟨σ, Lrem, n, g, rfl, hR⟩ | ⟨rfl, σ', r, n, g, hS⟩
  · refine ⟨st.w "fp.go", by simp, fun hgo => scan_step hown hnd hN σ₀ g₀ st₀ hbud hcapW hR hgo,
      fun hgo => ?_⟩
    -- exit: the live list is exhausted
    have hC := hR.core
    have hpM : ¬ st.w "fp.p" < G.m := by
      intro h; rw [hC.go, if_pos h] at hgo; exact one_ne_zero hgo
    obtain ⟨-, -, Pre, hPre, hs1, hs2, -⟩ := hC.cur
    have hnil : sl (Lrem.filter (fun e => e ∉ σ.D)) = [] := by
      cases hL' : sl (Lrem.filter (fun e => e ∉ σ.D)) with
      | nil => rfl
      | cons q L =>
        rw [hL'] at hs2
        obtain ⟨hq, hqM, -, -⟩ := hs2.cons_inv
        exact absurd (hq ▸ hqM) hpM
    have hfilt : Lrem.filter (fun e => e ∉ σ.D) = [] := List.map_eq_nil_iff.mp hnil
    refine ⟨σ, .cont, n, g, cont_nil hR.cont (all_dels_of_filter_nil hfilt), hC.lab.charge 1,
      hC.my.charge' 1, hC.cur.toOutRep.charge 1, by simpa using hC.ureg, Or.inl ⟨rfl, Or.inl (by simpa using hC.res)⟩,
      hR.hist, hR.book.unch.trans (Unchanged.charge st 1 _ _ _ _), by simp; exact
      (hR.book.cost0.trans (Nat.le_succ _)), by simp; have := hR.book.cost; omega⟩
  · refine ⟨st.w "fp.go", by simp, fun hgo => absurd hS.go hgo, fun _ => ?_⟩
    exact ⟨σ', r, n, g, hS.scan, hS.lab.charge 1, hS.my.charge' 1, hS.out.charge 1,
      by simpa using hS.ureg,
      by simpa [ResCode] using hS.code, hS.hist,
      hS.book.unch.trans (Unchanged.charge st 1 _ _ _ _),
      by simp; exact hS.book.cost0.trans (Nat.le_succ _), by simp; have := hS.book.cost; omega⟩

end Frontier.CHD.BL2
