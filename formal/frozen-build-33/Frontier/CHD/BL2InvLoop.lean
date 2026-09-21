import Frontier.CHD.BL2InvRoot2

/-!
# Frontier.CHD.BL2InvLoop — B-L2: one root of the invocation loop, and the loop (agent-09, NON-GATE)
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}
variable {LI : LabI V ops G s} {X : LabX LI} {TI : TreeI V ops G s} {c : FPCtx G s}
  {slB slX sA : String} {SL : List (Fin G.n)} {d0 : Labels G s}

theorem root_step (hown : OutOK c) (hsort : OutSorted c) (hnd : OutNodup c)
    (hNI : NamesI LI X TI slB slX sA)
    {S : Finset (Fin G.n)} (hpre : CallPre c.B S d0) (hSLS : ∀ x ∈ SL, x ∈ S) (hSLnd : SL.Nodup)
    {ι₀ : IState G s} {g₀ : LI.Gh} {st₀ : State V}
    (hbud : ∀ ι' n', Invoke c ι₀ SL ι' n' →
      st₀.cost + TI.Cinit + 5 + KI LI X TI * n' + KI LI X TI ≤ LI.c0 + st₀.cap)
    (hcapW : c.k + 4 < st₀.cap) (hcapN : st₀.w "fp.ob" + G.n + 2 < st₀.cap)
    (hcapS : st₀.w "fp.sb" + SL.length + 1 < st₀.cap)
    (hhext : c.k ≤ c.hext) (hk1 : 1 ≤ c.k)
    (hroots : ∀ j (h : j < SL.length), st₀.wa sA (st₀.w "fp.sb" + j) = (SL[j] : ℕ))
    (hsbL : st₀.w "fp.sb" + SL.length ≤ st₀.wlen sA)
    {ι : IState G s} {j n : ℕ} {g : LI.Gh} {st : State V}
    (h : IRun LI X TI c slB slX sA SL d0 ι₀ g₀ st₀ ι j n g st) (hj : j < SL.length) :
    Runs ops (fpRoot LI X TI sA slB slX) (st.charge 1)
      (fun st' => ∃ m', m' < SL.length - j ∧ ILoopI LI X TI c slB slX sA SL d0 ι₀ g₀ st₀ m' st') := by
  obtain ⟨hR, hjr, hjle, hwalk, hle, hfinv, hQsub, hhist, hcont, hbook⟩ := h
  have hcap : st.cap = st₀.cap := hbook.unch.cap
  have hnotW : ∀ r ∈ ["fp.sb", "fp.sn", "fp.ob"], r ∉ invWR LI X TI := fun r hr h => by
    have hr' : r ∈ invRegs := (by decide : (["fp.sb", "fp.sn", "fp.ob"] : List String) ⊆ invRegs) hr
    have hrk : r ∈ invKeep := (by decide : (["fp.sb", "fp.sn", "fp.ob"] : List String) ⊆ invKeep) hr
    simp only [invWR, List.mem_append] at h
    rcases h with ((h | h) | h) | h
    · exact hNI.srch_inv r h hrk
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [invWRegs] at h
    · exact hNI.namesT.gWR_ok r h (by simp only [List.mem_append]; left; left; right; exact hr')
    · exact hNI.namesT.iWR_ok r h (by simp only [List.mem_append]; left; left; right; exact hr')
  have hsb : st.w "fp.sb" = st₀.w "fp.sb" := hbook.unch.wreg _ (hnotW "fp.sb" (by simp))
  have hsAn : sA ∉ invWA LI TI sA := fun h => by
    simp only [invWA, List.mem_append] at h
    rcases h with ((h | h) | h) | h
    · exact hNI.srch_invA sA h (by simp)
    · exact hNI.sA_my (by simp only [List.mem_append]; right; exact h)
    · exact hNI.namesT.gWA_ok sA h (by simp only [List.mem_append]; left; left; left; right; simp)
    · exact hNI.namesT.iWA_ok sA h (by simp only [List.mem_append]; left; left; left; right; simp)
  have hsA := hbook.unch.warr sA hsAn
  -- x := S[j]
  have hxe : evalW (st.charge 1) (load sA (add (var "fp.sb") (var "fp.j"))) = some (SL[j] : ℕ) := by
    have hidx : evalW (st.charge 1) (add (var "fp.sb") (var "fp.j")) = some (st₀.w "fp.sb" + j) :=
      evalW_add_of (by simp [hsb]) (by simp [hjr]) (by simp [hcap]; omega)
    rw [evalW_load_of hidx (by simp [hsA.2]; omega)]
    simp [hsA.1, hroots j hj]
  refine runs_seq (runs_wset (a := SL[j]) hxe ?_)
  generalize hs1 : ((st.charge 1).setW "fp.x" (SL[j] : ℕ)).charge 1 = st1
  have hu1 : Unchanged st st1 [] [] ["fp.x"] [] := by
    rw [← hs1]; exact ((Unchanged.charge st 1 [] [] [] []).cat ((unch_setW _ "fp.x" _).cat
      (unch_charge' _ 1))).mono (by simp) (by simp) (by simp) (by simp)
  have hc1 : st1.cost = st.cost + 2 := by rw [← hs1]; simp
  have hx1 : st1.w "fp.x" = SL[j] := by rw [← hs1]; simp
  have hj1 : st1.w "fp.j" = j := by rw [← hs1]; simp [hjr]
  have hcap1 : st1.cap = st₀.cap := by rw [hu1.cap, hcap]
  have hR1 := hR.frame_reg hNI hu1 (by simp [invRegs]) (by decide) (by decide) (by decide) (by omega)
  have hbook1 : Unchanged st₀ st1 (invWA LI TI sA) (invVA LI TI) (invWR LI X TI) (invVR LI X TI) :=
    hbook.unch.trans (hu1.mono (by simp) (by simp) (fun z hz => invWRegs_sub (by
      simp at hz; subst hz; simp [invWRegs])) (by simp))
  have hdrop : SL.drop j = SL[j] :: SL.drop (j + 1) := List.drop_eq_getElem_cons hj
  have hcb0 := hbook.cost0
  have hcb := hbook.cost
  refine runs_seq ?_
  have hfmL : (SL[j] : ℕ) < st1.wlen "fp.fm" := by rw [hR1.my.fm.1]; exact (SL[j]).isLt
  by_cases hxT : SL[j] ∈ ι.tv
  · -- FH.3: a tree vertex is skipped (Layer A `Invoke.skip`)
    have hfm1 : st1.wa "fp.fm" SL[j] = 1 := by rw [hR1.my.fm.2]; simp [hxT]
    refine runs_ite_true (x := 1) (by simp [hx1, hfmL, hfm1]) one_ne_zero (runs_skip ?_)
    have huc : Unchanged st1 ((st1.charge 1).charge 1) [] [] [] [] :=
      (Unchanged.charge st1 1 _ _ _ _).trans (Unchanged.charge _ 1 _ _ _ _)
    refine root_finish hNI (ι' := ι) (n' := n + 1)
      (hR1.frame_reg hNI (huc.mono (by simp) (by simp) (by simp) (by simp)) (r := "fp.x")
        (by simp [invRegs]) (by decide) (by decide) (by decide) (by simp only [State.charge_cost]; omega))
      (by simpa using hj1) hj hwalk hle hfinv
      (fun q hq => List.take_subset_take_left SL (by omega) (hQsub q hq)) hhist ?_
      (hbook1.trans (huc.mono (by simp) (by simp) (by simp) (by simp)))
      (by simp only [State.charge_cost]; omega) ?_ (by simp [hcap1]; omega)
    · intro ι'' n'' h''
      have := hcont _ _ (by rw [hdrop]; exact Invoke.skip ι ι'' SL[j] (SL.drop (j + 1)) n'' hxT h'')
      rwa [show n + (n'' + 1) = n + 1 + n'' by omega] at this
    · have : KI LI X TI * (n + 1) = KI LI X TI * n + KI LI X TI := by ring
      have : 60 ≤ KI LI X TI := by simp only [KI]; omega
      simp only [State.charge_cost]; omega
  · -- a non-tree root: init + search + (grow | fail) + clear
    have hfm0 : st1.wa "fp.fm" SL[j] = 0 := by rw [hR1.my.fm.2]; simp [hxT]
    refine runs_ite_false (by simp [hx1, hfmL, hfm0]) ?_
    have huc : Unchanged st1 (st1.charge 1) [] [] [] [] := Unchanged.charge st1 1 _ _ _ _
    refine (root_search hown hsort hnd hNI hpre hSLS hSLnd hbud hcapW hcapN hhext hk1 hj
      (hR1.frame_reg hNI (huc.mono (by simp) (by simp) (by simp) (by simp)) (r := "fp.x")
        (by simp [invRegs]) (by decide) (by decide) (by decide) (by simp only [State.charge_cost]; omega))
      hwalk hle hfinv hQsub hhist hcont
      (hbook1.trans (huc.mono (by simp) (by simp) (by simp) (by simp)))
      (by simp only [State.charge_cost]; omega) (by simp only [State.charge_cost]; omega)
      (by simpa using hx1) (by simpa using hj1) hxT).mono ?_
    rintro st5 ⟨ι', n', g', hR5, hj5, hw5, hle5, hf5, hQ5, hh5, hc5, hu5, hc05, hc5'⟩
    exact root_finish hNI hR5 hj5 hj hw5 hle5 hf5 hQ5 hh5 hc5 hu5 hc05 hc5'
      (by rw [hu5.cap]; omega)

theorem iWA_sub_invWA : TI.iWA ⊆ invWA LI TI sA := by
  intro x hx; simp only [invWA, List.mem_append]; tauto
theorem iVA_sub_invVA : TI.iVA ⊆ invVA LI TI := by
  intro x hx; simp only [invVA, List.mem_append]; tauto
theorem iWR_sub_invWR : TI.iWR ⊆ invWR LI X TI := by
  intro x hx; simp only [invWR, List.mem_append]; tauto
theorem iVR_sub_invVR : TI.iVR ⊆ invVR LI X TI := by
  intro x hx; simp only [invVR, List.mem_append]; tauto

/-- The empty forest satisfies agent-05's forest invariant. -/
theorem FInv.empty (d : Labels G s) (D : Finset (Fin G.m)) :
    FInv c (⟨d, D, ∅, ∅, ∅, []⟩ : IState G s) :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun v => by simp, List.Pairwise.nil⟩

/-- Postcondition of the invocation loop. -/
def InvPost (LI : LabI V ops G s) (X : LabX LI) (TI : TreeI V ops G s) (c : FPCtx G s)
    (slB slX sA : String) (SL : List (Fin G.n)) (d0 : Labels G s) (ι₀ : IState G s) (g₀ : LI.Gh)
    (st₀ st' : State V) : Prop :=
  ∃ ι' n g', Invoke c ι₀ SL ι' n ∧ IRep LI TI c slB slX ι' g' st' ∧ WalkInv ι'.d ∧
    (∀ v, ι'.d v ≤ d0 v) ∧ FInv c ι' ∧ LI.gext g₀ g' ∧
    Unchanged st₀ st' (invWA LI TI sA) (invVA LI TI) (invWR LI X TI) (invVR LI X TI) ∧
    st₀.cost ≤ st'.cost ∧ st'.cost ≤ st₀.cost + TI.Cinit + 5 + KI LI X TI * n

/-- **The RAM invocation loop (FH.2–FH.25) refines Layer A's `Invoke`** from the empty
invocation state `⟨d0, Din, ∅, ∅, ∅, []⟩` over the root list `SL` (stored at `sA[sb ..]`). -/
theorem invoke_spec (hown : OutOK c) (hsort : OutSorted c) (hnd : OutNodup c)
    (hNI : NamesI LI X TI slB slX sA)
    {S : Finset (Fin G.n)} (hpre : CallPre c.B S d0) (hSLS : ∀ x ∈ SL, x ∈ S) (hSLnd : SL.Nodup)
    {Din : Finset (Fin G.m)} {g₀ : LI.Gh} {st₀ : State V}
    (hL : LabRep LI c slB slX d0 g₀ st₀) (hM : MyRep c ∅ (emptySt d0 Din) st₀)
    (hO : OutRep st₀ c Din) (hTA : TI.TA st₀)
    (hinW : Bits (G := G) st₀ "fp.inW" ∅) (hWL : st₀.w "fp.ob" + G.n ≤ st₀.wlen "fp.W")
    (hQL : st₀.w "fp.ob" + G.n ≤ st₀.wlen "fp.Q")
    (hbud : ∀ ι' n', Invoke c ⟨d0, Din, ∅, ∅, ∅, []⟩ SL ι' n' →
      st₀.cost + TI.Cinit + 5 + KI LI X TI * n' + KI LI X TI ≤ LI.c0 + st₀.cap)
    (hcapW : c.k + 4 < st₀.cap) (hcapN : st₀.w "fp.ob" + G.n + 2 < st₀.cap)
    (hcapS : st₀.w "fp.sb" + SL.length + 1 < st₀.cap)
    (hhext : c.k ≤ c.hext) (hk1 : 1 ≤ c.k)
    (hroots : ∀ j (h : j < SL.length), st₀.wa sA (st₀.w "fp.sb" + j) = (SL[j] : ℕ))
    (hsbL : st₀.w "fp.sb" + SL.length ≤ st₀.wlen sA) (hsn : st₀.w "fp.sn" = SL.length) :
    Runs ops (fpInvoke LI X TI sA slB slX) st₀
      (InvPost LI X TI c slB slX sA SL d0 ⟨d0, Din, ∅, ∅, ∅, []⟩ g₀ st₀) := by
  have hcapN2 : G.n + 2 < st₀.cap := by omega
  have hiA := hNI.namesT.iWA_ok
  have hiR := hNI.namesT.iWR_ok
  have hiV := hNI.namesT.iVA_ok
  have hiVR := hNI.namesT.iVR_ok
  unfold fpInvoke
  refine runs_seq ((TI.init_spec hTA hcapN2).mono ?_)
  rintro sta ⟨hFRa, hua, hca0, hca⟩
  have hcapa : sta.cap = st₀.cap := hua.cap
  have h0a : 0 < sta.cap := by omega
  apply wp_sound
  simp only [wp, evalW_lit', fit, State.charge_cap, State.setW_cap, h0a, if_true]
  generalize hsbg : ((((((sta.setW "fp.j" 0).charge 1).setW "fp.wl" 0).charge 1).setW "fp.ql" 0).charge
    1) = stb
  have hub : Unchanged sta stb [] [] ["fp.j", "fp.wl", "fp.ql"] [] := by
    rw [← hsbg]
    refine ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun x hx => ?_, fun _ _ => rfl, rfl, rfl⟩
    simp only [List.mem_cons, not_or, List.not_mem_nil, or_false] at hx
    simp [hx.1, hx.2.1, hx.2.2]
  have hcb : stb.cost = sta.cost + 3 := by rw [← hsbg]; simp
  have hjb : stb.w "fp.j" = 0 := by rw [← hsbg]; simp
  have hwlb : stb.w "fp.wl" = 0 := by rw [← hsbg]; simp
  have hqlb : stb.w "fp.ql" = 0 := by rw [← hsbg]; simp
  -- the invocation registers that are never written
  have hiRo : ∀ r ∈ invRegs, r ∉ TI.iWR := fun r hr h => hiR r h (by
    simp only [List.mem_append]; left; left; right; exact hr)
  have hob : stb.w "fp.ob" = st₀.w "fp.ob" := by
    rw [hub.wreg "fp.ob" (by decide), hua.wreg "fp.ob" (hiRo _ (by simp [invRegs]))]
  -- representation of the empty invocation state
  have hLa : LabRep LI c slB slX d0 g₀ sta :=
    hL.frame hua (hiA.mono_right (fun z hz => by simp only [List.mem_append]; left; left; right; exact hz))
      (hiV.mono_right (fun z hz => by simp only [List.mem_append]; left; left; exact hz))
      (hiA.mono_right (fun z hz => by simp only [List.mem_append]; left; right; exact hz))
      (hiV.mono_right (fun z hz => by simp only [List.mem_append]; left; right; exact hz))
      (hiR.mono_right (fun z hz => by simp only [List.mem_append]; left; right; exact hz))
      (hiVR.mono_right (fun z hz => by simp only [List.mem_append]; left; exact hz))
      (hiA.mono_right (fun z hz => by simp only [List.mem_append]; right; exact hz))
      (hiV.mono_right (fun z hz => by simp only [List.mem_append]; right; exact hz))
      (hiR.mono_right (fun z hz => by simp only [List.mem_append]; right; exact hz))
      (hiVR.mono_right (fun z hz => by simp only [List.mem_append]; right; exact hz)) hca0
  have hiAm : Disj TI.iWA myRepArrs := hiA.mono_right (fun z hz => by
    simp only [List.mem_append]; left; left; left; left; left
    exact (by decide : myRepArrs ⊆ myArrs) hz)
  have hiRm : Disj TI.iWR myRepRegs := hiR.mono_right (fun z hz => by
    simp only [List.mem_append]; left; left; left; left; left
    exact (by decide : myRepRegs ⊆ myRegs) hz)
  have hiAO : Disj TI.iWA ["gHd", "gNxt"] := hiA.mono_right (fun z hz => by
    simp only [List.mem_append]; left; left; left; left; left
    exact (by decide : (["gHd", "gNxt"] : List String) ⊆ myArrs) hz)
  have hiAW : Disj TI.iWA ["fp.W", "fp.inW"] := hiA.mono_right (fun z hz => by
    simp only [List.mem_append]; left; left; left; left; right
    exact (by decide : (["fp.W", "fp.inW"] : List String) ⊆ invArrs) hz)
  have hiAQ : Disj TI.iWA ["fp.Q"] := hiA.mono_right (fun z hz => by
    simp only [List.mem_append]; left; left; left; left; right
    exact (by decide : (["fp.Q"] : List String) ⊆ invArrs) hz)
  have hRb : IRep LI TI c slB slX ⟨d0, Din, ∅, ∅, ∅, []⟩ g₀ stb := by
    refine ⟨hLa.frame_inv hNI hub (by simp) (by decide) (by omega),
      (hM.frameR hua hiAm hiRm).frameR hub (Disj.nil_left _) (by decide),
      (hO.frameR hua hiAO).frameR hub (Disj.nil_left _),
      FR.frame_inv hNI hFRa hub (by simp) (by decide), ?_, ?_⟩
    · refine ⟨[], List.nodup_nil, by simp, by simpa using hwlb, fun i hi => absurd hi (by simp),
        ?_, by rw [hob, (hub.warr "fp.W" (by decide)).2, (hua.warr "fp.W" (fun h =>
          hiAW _ h (by simp))).2]; exact hWL⟩
      have hbits := hinW
      refine ⟨by rw [(hub.warr "fp.inW" (by decide)).2, (hua.warr "fp.inW" (fun h =>
          hiAW _ h (by simp))).2]; exact hbits.1, fun v => ?_⟩
      rw [(hub.warr "fp.inW" (by decide)).1, (hua.warr "fp.inW" (fun h => hiAW _ h (by simp))).1]
      exact hbits.2 v
    · refine ⟨[], List.nodup_nil, by simp, by simpa using hqlb, fun i hi => absurd hi (by simp), ?_⟩
      rw [hob, (hub.warr "fp.Q" (by decide)).2, (hua.warr "fp.Q" (fun h => hiAQ _ h (by simp))).2]
      exact hQL
  have hbookb : IBook LI X TI sA st₀ stb 0 := by
    refine ⟨(hua.cat hub).mono ?_ ?_ ?_ ?_, by omega, by omega⟩
    · exact List.append_subset.mpr ⟨iWA_sub_invWA, fun _ h => absurd h List.not_mem_nil⟩
    · exact List.append_subset.mpr ⟨iVA_sub_invVA, fun _ h => absurd h List.not_mem_nil⟩
    · exact List.append_subset.mpr ⟨iWR_sub_invWR, List.Subset.trans (by decide) invWRegs_sub⟩
    · exact List.append_subset.mpr ⟨iVR_sub_invVR, fun _ h => absurd h List.not_mem_nil⟩
  -- the loop over the roots
  refine runs_while_nat (ILoopI LI X TI c slB slX sA SL d0 ⟨d0, Din, ∅, ∅, ∅, []⟩ g₀ st₀) _ ?_
    (SL.length - 0) stb ⟨⟨d0, Din, ∅, ∅, ∅, []⟩, 0, 0, g₀, rfl, ⟨hRb, hjb, by omega, hpre.walk,
      fun _ => le_rfl, FInv.empty d0 Din, fun q hq => absurd hq (by simp), LI.gext_refl g₀,
      fun ι'' n' h => by simpa using h, hbookb⟩⟩
  intro m st ⟨ι, j, n, g, hm, hIR⟩
  have hsn' : st.w "fp.sn" = SL.length := by
    rw [hIR.book.unch.wreg "fp.sn" (fun h => by
      simp only [invWR, List.mem_append] at h
      rcases h with ((h | h) | h) | h
      · exact hNI.srch_inv _ h (by simp [invKeep])
      · simp [invWRegs] at h
      · exact hNI.namesT.gWR_ok _ h (by
          simp only [List.mem_append]; left; left; right; exact (by decide : "fp.sn" ∈ invRegs))
      · exact hiRo _ (by simp [invRegs]) h)]
    exact hsn
  have hcapst : st.cap = st₀.cap := hIR.book.unch.cap
  refine ⟨if j < SL.length then 1 else 0, ?_, fun hne => ?_, fun h0 => ?_⟩
  · rw [evalW_lt_of (x := j) (y := SL.length) (by simp [hIR.jreg]) (by simp [hsn'])
      (by rw [hcapst]; omega)]
  · have hj : j < SL.length := by by_contra h; simp [h] at hne
    refine (root_step hown hsort hnd hNI hpre hSLS hSLnd hbud hcapW hcapN hcapS hhext hk1 hroots
      hsbL hIR hj).mono ?_
    rintro st' ⟨m', hm', hL'⟩
    exact ⟨m', by omega, hL'⟩
  · have hjeq : j = SL.length := by
      have := hIR.jle
      by_contra h; simp [show j < SL.length by omega] at h0
    subst hjeq
    have hch : Unchanged st (st.charge 1) [] [] [] [] := Unchanged.charge st 1 _ _ _ _
    refine ⟨ι, n, g, ?_, ⟨hIR.rep.lab.charge 1, hIR.rep.my.charge' 1, hIR.rep.out.charge 1,
      TI.FR_frame hIR.rep.fr hch (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _)
        (Disj.nil_left _), hIR.rep.W.frame hch (Disj.nil_left _) (Disj.nil_left _),
      hIR.rep.Q.frame hch (Disj.nil_left _) (Disj.nil_left _)⟩, hIR.walk, hIR.le, hIR.finv,
      hIR.hist, hIR.book.unch.trans (hch.mono (by simp) (by simp) (by simp) (by simp)),
      by simp; have := hIR.book.cost0; omega, by simp; have := hIR.book.cost; omega⟩
    have := hIR.cont ι 0 (by simpa using Invoke.nil ι)
    simpa using this

end Frontier.CHD.BL2
