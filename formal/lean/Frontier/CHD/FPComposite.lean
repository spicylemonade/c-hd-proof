import Frontier.CHD.TreeRAM10
import Frontier.CHD.BL2InvLoop
import Frontier.CHD.FPTailCost

/-!
# Frontier.CHD.FPComposite — the FindPivots-HD body: invocation loop, then tail (owner agent-03, with agent-09)

**NON-GATE** (Layer B).  `fpInvoke … ; fpTail sA` with agent-03's tree layer `treeImpl`:
`fpInvTail_spec` chains agent-09's `invoke_spec` (the RAM invocation loop refines Layer A's `Invoke`) with
`fpTail_spec` (compaction, PT, cleanup).  At the end:
* Layer A: `Invoke c ⟨d0, Din, ∅, ∅, ∅, []⟩ SL ι' n` (the relation of `FindPivotsCL`), with `WalkInv`, labels `≤ d0`,
  `FInv`;
* the groups `forestGroups S ι'.Q k ι'.trees` in `GrpOut` (relabelled by `Fin.val`);
* the representation for the NEXT invocation: labels (`LabRep`), clean FindPivots marks with `fp.fm = ∅`
  (`MyRep c ∅ …`), the live out-lists `Dout` (`OutRep`), `W` and `Q` lists, and the allocations `TA0`, `PTA`;
* `Unchanged` outside the invocation's and the tail's write sets;
* cost `≤ 36 + (KI + 188)·n` over the start, `n` the invocation's Layer-A cost index (`FPTailCost.tail_le_invoke`).
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM Frontier.CHD.PartitionRAM Frontier.CHD.Partition

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}
variable {LI : LabI V ops G s} {X : LabX LI} {c : FPCtx G s}
  {slB slX sA : String} {SL : List (Fin G.n)} {d0 : Labels G s}

/-- The arrays of `PTA`. -/
def ptaArrs : List String :=
  ["pt.an", "pt.af", "pt.al", "pt.nx", "fp.inS", "fp.inQ", "pt.as", "pt.PT", "pt.PF", "pt.PL", "pt.PN",
   "pt.GV", "pt.GO", "pt.GL", "fp.TV", "fp.toff", "fp.tlen"]

theorem _root_.Frontier.CHD.PartitionRAM.PTA.frame {N : ℕ} {st st' : State V} (h : PTA N st)
    (hA : ∀ a ∈ ptaArrs, st'.wa a = st.wa a ∧ st'.wlen a = st.wlen a) : PTA N st' := by
  have e : ∀ a ∈ ptaArrs, st'.wa a = st.wa a := fun a ha => (hA a ha).1
  have l : ∀ a ∈ ptaArrs, st'.wlen a = st.wlen a := fun a ha => (hA a ha).2
  obtain ⟨⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17⟩, hS, hQ, hAs⟩ := h
  refine ⟨?_, fun x hx => by rw [e "fp.inS" (by decide)]; exact hS x hx,
    fun x hx => by rw [e "fp.inQ" (by decide)]; exact hQ x hx,
    fun x hx => by rw [e "pt.as" (by decide)]; exact hAs x hx⟩
  rw [l "pt.an" (by decide), l "pt.af" (by decide), l "pt.al" (by decide), l "pt.nx" (by decide),
    l "fp.inS" (by decide), l "fp.inQ" (by decide), l "pt.as" (by decide), l "pt.PT" (by decide),
    l "pt.PF" (by decide), l "pt.PL" (by decide), l "pt.PN" (by decide), l "pt.GV" (by decide),
    l "pt.GO" (by decide), l "pt.GL" (by decide), l "fp.TV" (by decide), l "fp.toff" (by decide),
    l "fp.tlen" (by decide)]
  exact ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17⟩

/-- Name hygiene of the tail against the label layer and the invocation (all `decide` for concrete names). -/
structure NamesTail (LI : LabI V ops G s) (slB slX sA : String) : Prop where
  tab : Disj tailWA LI.tabWA
  wB : Disj tailWA (LI.slWA slB)
  wX : Disj tailWA (LI.slWA slX)
  rB : Disj tailWR (LI.slWR slB)
  rX : Disj tailWR (LI.slWR slX)
  sA_tail : sA ∉ tailWA
  sA_tr : sA ∉ trArrs
  srch_pta : Disj (srchWA LI) ptaArrs

/-- **The FindPivots-HD body at RAM level**: agent-09's invocation loop with agent-03's tree layer, then the tail. -/
theorem fpInvTail_spec (hown : OutOK c) (hsort : OutSorted c) (hnd : OutNodup c)
    (hNI : NamesI LI X (treeImpl V ops G s) slB slX sA) (hNT : NamesTail LI slB slX sA)
    {S : Finset (Fin G.n)} (hpre : CallPre c.B S d0) (hSL : ∀ x, x ∈ SL ↔ x ∈ S) (hSLnd : SL.Nodup)
    {Din : Finset (Fin G.m)} {g₀ : LI.Gh} {st₀ : State V}
    (hL : LabRep LI c slB slX d0 g₀ st₀) (hM : MyRep c ∅ (emptySt d0 Din) st₀)
    (hO : OutRep st₀ c Din) (hTA : TA0 G.n st₀) (hPTA : PTA G.n st₀)
    (hinW : Bits (G := G) st₀ "fp.inW" ∅) (hWL : st₀.w "fp.ob" + G.n ≤ st₀.wlen "fp.W")
    (hQL : st₀.w "fp.ob" + G.n ≤ st₀.wlen "fp.Q")
    (hbud : ∀ ι' n', Invoke c ⟨d0, Din, ∅, ∅, ∅, []⟩ SL ι' n' →
      st₀.cost + (treeImpl V ops G s).Cinit + 5 + KI LI X (treeImpl V ops G s) * n' +
        KI LI X (treeImpl V ops G s) ≤ LI.c0 + st₀.cap)
    (hcapW : c.k + 4 < st₀.cap) (hcapN : st₀.w "fp.ob" + G.n + 2 < st₀.cap)
    (hcapS : st₀.w "fp.sb" + SL.length + 1 < st₀.cap)
    (hcapT : 3 * G.n + st₀.w "fp.sb" + SL.length + st₀.w "fp.ob" + 2 * c.k + 4 < st₀.cap)
    (hhext : c.k ≤ c.hext) (hk2 : 2 ≤ c.k)
    (hroots : ∀ j (h : j < SL.length), st₀.wa sA (st₀.w "fp.sb" + j) = (SL[j] : ℕ))
    (hsbL : st₀.w "fp.sb" + SL.length ≤ st₀.wlen sA) (hsn : st₀.w "fp.sn" = SL.length) :
    Runs ops (.seq (fpInvoke LI X (treeImpl V ops G s) sA slB slX) (fpTail sA)) st₀ (fun st' =>
      ∃ ι' n g', Invoke c ⟨d0, Din, ∅, ∅, ∅, []⟩ SL ι' n ∧ WalkInv ι'.d ∧ (∀ v, ι'.d v ≤ d0 v) ∧
        FInv c ι' ∧ LI.gext g₀ g' ∧
        LabRep LI c slB slX ι'.d g' st' ∧ MyRep c ∅ (emptySt ι'.d ι'.D) st' ∧ OutRep st' c ι'.D ∧
        WRep st' ι'.W ∧ QRep st' ι'.Q ∧
        GrpOut st' ((forestGroups S ι'.Q c.k ι'.trees).map (List.map Fin.val)) ∧
        PTA G.n st' ∧ TA0 G.n st' ∧
        Unchanged st₀ st' (invWA LI (treeImpl V ops G s) sA ++ tailWA) (invVA LI (treeImpl V ops G s) ++ [])
          (invWR LI X (treeImpl V ops G s) ++ tailWR) (invVR LI X (treeImpl V ops G s) ++ []) ∧
        st₀.cost ≤ st'.cost ∧ st'.cost ≤ st₀.cost + 36 + (KI LI X (treeImpl V ops G s) + 188) * n) := by
  apply runs_seq
  refine Runs.mono (invoke_spec (TI := treeImpl V ops G s) hown hsort hnd hNI hpre (fun x hx => (hSL x).mp hx)
    hSLnd hL hM hO hTA hinW hWL hQL hbud hcapW hcapN hcapS hhext (by omega) hroots hsbL hsn) ?_
  rintro s1 ⟨ι', n, g', hInv, hIR, hwalk, hle, hFI, hgext, hU1, hc1a, hc1b⟩
  -- facts at `s1`
  have hsAinv : sA ∉ invWA LI (treeImpl V ops G s) sA := by
    intro h
    simp only [invWA, List.mem_append] at h
    rcases h with ((h | h) | h) | h
    · exact hNI.srch_invA sA h (List.mem_append_right _ (List.mem_singleton_self _))
    · exact hNI.sA_my (List.mem_append_right _ h)
    · exact hNT.sA_tr h
    · simp [treeImpl] at h
  have hsA1 : s1.wa sA = st₀.wa sA := (hU1.warr sA hsAinv).1
  have hsAl1 : s1.wlen sA = st₀.wlen sA := (hU1.warr sA hsAinv).2
  have hkeep : ∀ r, r ∈ invKeep → r ∉ invWRegs → r ∉ trRegs → r ∉ ["tr.nt"] →
      r ∉ invWR LI X (treeImpl V ops G s) := by
    intro r hr h1 h2 h3 h
    simp only [invWR, List.mem_append] at h
    rcases h with ((h | h) | h) | h
    · exact hNI.srch_inv r h hr
    · exact h1 h
    · exact h2 h
    · exact h3 h
  have hsb1 : s1.w "fp.sb" = st₀.w "fp.sb" :=
    hU1.wreg _ (hkeep _ (by decide) (by decide) (by decide) (by decide))
  have hsn1 : s1.w "fp.sn" = st₀.w "fp.sn" :=
    hU1.wreg _ (hkeep _ (by decide) (by decide) (by decide) (by decide))
  have hob1 : s1.w "fp.ob" = st₀.w "fp.ob" :=
    hU1.wreg _ (hkeep _ (by decide) (by decide) (by decide) (by decide))
  have hptaN : ∀ a ∈ ptaArrs, a ∉ invArrs ∧ a ∉ trArrs := by decide
  have hpta1 : ∀ a ∈ ptaArrs, s1.wa a = st₀.wa a ∧ s1.wlen a = st₀.wlen a := by
    intro a ha
    refine hU1.warr a (fun h => ?_)
    simp only [invWA, List.mem_append] at h
    rcases h with ((h | h) | h) | h
    · exact hNT.srch_pta a h ha
    · exact (hptaN a ha).1 h
    · exact (hptaN a ha).2 h
    · exact absurd h List.not_mem_nil
  have hPTA1 : PTA G.n s1 := hPTA.frame hpta1
  have hcap1 : s1.cap = st₀.cap := hU1.cap
  obtain ⟨ql, hqnd, hqset, hqlen, hqarr, hqL⟩ := hIR.Q
  have hqlN : ql.length ≤ G.n := by simpa using hqnd.length_le_card
  have hQc : ι'.Q.card = ql.length := by rw [← hqset, List.toFinset_card_of_nodup hqnd]
  have hFR1 : FR0 s1 G.n ι'.trees := hIR.fr
  -- the tail
  refine Runs.mono (Runs.cost_mono' (fpTail_spec (ops := ops) (st0 := s1) (trees := ι'.trees) (tv := ι'.tv) (S := S) (Q := ι'.Q)
    (SL := SL) (ql := ql) (k := c.k) (sA := sA) hk2 hFR1 (fun T hT => hFI.pf T hT) hFI.tv hIR.my.fm hSL
    (fun j h => by rw [hsA1, hsb1]; exact hroots j h) (by rw [hsb1, hsAl1]; exact hsbL) (by rw [hsn1]; exact hsn)
    (fun x => by rw [← List.mem_toFinset, hqset]) hqarr hqlen (by rw [hob1] at hqL ⊢; omega) hIR.my.kreg hPTA1
    hNT.sA_tail (by rw [hsb1, hob1, hcap1]; omega))) ?_
  rintro st' ⟨⟨hG, hB, hPTA', hU2, hc2⟩, hmono⟩
  have hc2' := tail_le_invoke hInv hFI
  rw [hQc] at hc2'
  refine ⟨ι', n, g', hInv, hwalk, hle, hFI, hgext, ?_, ?_, ?_, ?_, ?_, hG, hPTA', ?_, hU1.cat hU2, by omega, ?_⟩
  · exact hIR.lab.frame hU2 hNT.tab (Disj.nil_left _) hNT.wB (Disj.nil_left _) hNT.rB (Disj.nil_left _)
      hNT.wX (Disj.nil_left _) hNT.rX (Disj.nil_left _) hmono
  · exact hIR.my.setFm hB hU2 (by decide) (by decide)
  · have hF := hU2.warr "gHd" (by decide)
    have hN := hU2.warr "gNxt" (by decide)
    obtain ⟨o1, o2⟩ := hIR.out
    exact ⟨by rw [hF.2]; exact o1, fun w => by rw [hF.1]; exact (o2 w).of_eq hN.1 hN.2⟩
  · exact hIR.W.frame hU2 (by decide) (by decide)
  · exact ⟨ql, hqnd, hqset, by rw [hU2.wreg _ (by decide)]; exact hqlen,
      fun i hi => by rw [(hU2.warr _ (by decide)).1, hU2.wreg _ (by decide)]; exact hqarr i hi,
      by rw [hU2.wreg _ (by decide), (hU2.warr _ (by decide)).2]; exact hqL⟩
  · have hfrN : ∀ a ∈ frWA0, a ∉ tailWA := by decide
    exact TA0.frame (FR0.toTA hFR1) (fun a ha => hU2.warr a (hfrN a ha))
  · have hCi : (treeImpl V ops G s).Cinit = 1 := rfl
    rw [hCi] at hc1b
    rw [Nat.add_mul]
    omega

end Frontier.CHD.BL2
