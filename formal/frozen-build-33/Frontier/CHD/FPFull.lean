import Frontier.CHD.FPComposite
import Frontier.CHD.BL2Find

/-!
# Frontier.CHD.FPFull — the complete FindPivots-HD program: FH.1, invocation loop, tail (owner agent-03, with agent-09)

**NON-GATE** (Layer B).  `fpFull = fpFind ; fpTail sA` (agent-09's driver `fpFind` = FH.1 `L_X` + the invocation loop, with
agent-03's tree layer `treeImpl`; then agent-03's tail).  `fpFull_spec`:
* Layer A: agent-05's pinned `FindPivotsC out k hins hext B S d0 Din d1 Dout Q W trees cost` (exactly `fpC`'s relation);
* the pivot groups `forestGroups S Q k trees` in `GrpOut` (relabelled by `Fin.val`);
* the representation for the NEXT call: labels, clean marks with `fp.fm = ∅` (`MyRep c ∅ …`), live lists `Dout`, the `W`
  and `Q` lists, and the allocations `TA0`, `PTA`;
* `Unchanged` outside the driver's and the tail's write sets;
* cost `≤ CFD + CLX·|S| + (KI + 188)·cost + 30` (the tail is paid by the invocation's cost index, `FPTailCost`).
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM Frontier.CHD.PartitionRAM Frontier.CHD.Partition

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}
variable {LI : LabI V ops G s} {X : LabX LI}

/-- Name hygiene of the complete program beyond `NamesD`. -/
structure NamesFull (LI : LabI V ops G s) (slB slX sA : String) : Prop where
  tail : NamesTail LI slB slX sA
  x_pta : Disj (LI.slWA slX) ptaArrs

/-- **The complete FindPivots-HD program.** -/
def fpFull (LI : LabI V ops G s) (X : LabX LI) (sA slB slX : String) : Stmt :=
  .seq (fpFind LI X (treeImpl V ops G s) sA slB slX) (fpTail sA)

/-- **The complete FindPivots-HD program refines agent-05's pinned `FindPivotsC` together with its pivot groups.** -/
theorem fpFull_spec {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}
    (hout : ∀ u e, e ∈ out u ↔ G.src e = u) (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (hnd : ∀ u, (out u).Nodup) {slB slX sA : String} (hND : NamesD LI X (treeImpl V ops G s) slB slX sA)
    (hNF : NamesFull LI slB slX sA)
    {B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} (hpre : CallPre B S d0)
    {SL : List (Fin G.n)} (hSLnd : SL.Nodup) (hSL : ∀ x, x ∈ SL ↔ x ∈ S)
    {Din : Finset (Fin G.m)} {g₀ : LI.Gh} {st₀ : State V}
    (hLT : LI.LT st₀ d0 g₀) (hB : LI.LS st₀ slB B g₀)
    (hM : MyRep (pinCtx out k hins hext B (lxOf B S d0)) ∅ (emptySt d0 Din) st₀)
    (hO : OutRep st₀ (pinCtx out k hins hext B (lxOf B S d0)) Din) (hTA : TA0 G.n st₀) (hPTA : PTA G.n st₀)
    (hinW : Bits (G := G) st₀ "fp.inW" ∅) (hWL : st₀.w "fp.ob" + G.n ≤ st₀.wlen "fp.W")
    (hQL : st₀.w "fp.ob" + G.n ≤ st₀.wlen "fp.Q")
    (hbud : ∀ d1 Dout Q W trees cost,
      FindPivotsC out k hins hext B S d0 Din d1 Dout Q W trees cost →
      st₀.cost + CFD LI (treeImpl V ops G s) + CLX LI * S.card + KI LI X (treeImpl V ops G s) * cost +
        KI LI X (treeImpl V ops G s) ≤ LI.c0 + st₀.cap)
    (hcapW : k + 4 < st₀.cap) (hcapN : st₀.w "fp.ob" + G.n + 2 < st₀.cap)
    (hcapS : st₀.w "fp.sb" + SL.length + 1 < st₀.cap)
    (hcapT : 3 * G.n + st₀.w "fp.sb" + SL.length + st₀.w "fp.ob" + 2 * k + 4 < st₀.cap)
    (hk2 : 2 ≤ k) (hhext : k ≤ hext)
    (hroots : ∀ j (h : j < SL.length), st₀.wa sA (st₀.w "fp.sb" + j) = (SL[j] : ℕ))
    (hsbL : st₀.w "fp.sb" + SL.length ≤ st₀.wlen sA) (hsn : st₀.w "fp.sn" = SL.length) :
    Runs ops (fpFull LI X sA slB slX) st₀ (fun st' =>
      ∃ (ι' : IState G s) (cost : ℕ) (g' : LI.Gh),
        FindPivotsC out k hins hext B S d0 Din ι'.d ι'.D ι'.Q ι'.W ι'.trees cost ∧
        GrpOut st' ((forestGroups S ι'.Q k ι'.trees).map (List.map Fin.val)) ∧
        LabRep LI (pinCtx out k hins hext B (lxOf B S d0)) slB slX ι'.d g' st' ∧
        MyRep (pinCtx out k hins hext B (lxOf B S d0)) ∅ (emptySt ι'.d ι'.D) st' ∧
        OutRep st' (pinCtx out k hins hext B (lxOf B S d0)) ι'.D ∧ WRep st' ι'.W ∧ QRep st' ι'.Q ∧
        PTA G.n st' ∧ TA0 G.n st' ∧
        WalkInv ι'.d ∧ (∀ v, ι'.d v ≤ d0 v) ∧ FInv (pinCtx out k hins hext B (lxOf B S d0)) ι' ∧
        LI.gext g₀ g' ∧
        Unchanged st₀ st' (fdWA LI (treeImpl V ops G s) sA slX ++ tailWA) (fdVA LI (treeImpl V ops G s) slX ++ [])
          (fdWR LI X (treeImpl V ops G s) slX ++ tailWR) (fdVR LI X (treeImpl V ops G s) slX ++ []) ∧
        st₀.cost ≤ st'.cost ∧
        st'.cost ≤ st₀.cost + CFD LI (treeImpl V ops G s) + CLX LI * S.card +
          (KI LI X (treeImpl V ops G s) + 188) * cost + 30) := by
  set c := pinCtx out k hins hext B (lxOf B S d0) with hc
  have hown : OutOK c := hout
  have hsort' : OutSorted c := hsort
  have hNI := hND.inv
  have hNT := hNF.tail
  apply runs_seq
  refine Runs.mono (fpFind_spec (TI := treeImpl V ops G s) hout hsort hnd hND hpre hSLnd hSL hLT hB hM hO hTA hinW
    hWL hQL hbud hcapW hcapN hcapS (by omega) hhext hroots hsbL hsn) ?_
  rintro s1 ⟨ι', cost, g', hFPC, hIR, hwalk, hle, hFI, hgext, hU1, hc1a, hc1b⟩
  -- the invocation behind `FindPivotsC`
  obtain ⟨SL', ι'', hSL'nd, hSL', hInv, hd, hD, hQ, hW, htr, hcard⟩ := hFPC
  have hFI'' : FInv c ι'' := Invoke.forest hown hsort' hpre hInv (fun x hx => (hSL' x).mp hx) hpre.walk
    (fun _ => le_rfl) (FInv.empty d0 Din)
  have htl := tail_le_invoke hInv hFI''
  rw [← htr, ← hQ] at htl
  have hSLl : SL'.length = SL.length := by
    rw [← hcard]
    have hSLf : SL.toFinset = S := by ext x; simp [hSL]
    rw [← hSLf, List.toFinset_card_of_nodup hSLnd]
  rw [hSLl] at htl
  -- facts at `s1`
  have hsAinv : sA ∉ invWA LI (treeImpl V ops G s) sA := by
    intro h
    simp only [invWA, List.mem_append] at h
    rcases h with ((h | h) | h) | h
    · exact hNI.srch_invA sA h (List.mem_append_right _ (List.mem_singleton_self _))
    · exact hNI.sA_my (List.mem_append_right _ h)
    · exact hNT.sA_tr h
    · simp [treeImpl] at h
  have hsAfd : sA ∉ fdWA LI (treeImpl V ops G s) sA slX := by
    intro h
    simp only [fdWA, List.mem_append] at h
    rcases h with h | h
    · exact hND.lx.x_sA h
    · exact hsAinv h
  have hsA1 : s1.wa sA = st₀.wa sA := (hU1.warr sA hsAfd).1
  have hsAl1 : s1.wlen sA = st₀.wlen sA := (hU1.warr sA hsAfd).2
  have hkeep : ∀ r, r ∈ invKeep → r ∉ invWRegs → r ∉ trRegs → r ∉ ["tr.nt"] →
      r ∉ invWR LI X (treeImpl V ops G s) := by
    intro r hr h1 h2 h3 h
    simp only [invWR, List.mem_append] at h
    rcases h with ((h | h) | h) | h
    · exact hNI.srch_inv r h hr
    · exact h1 h
    · exact h2 h
    · exact h3 h
  have hlx : ∀ r, r ∈ ["fp.sb", "fp.sn"] → r ∉ lxWR LI slX := by
    intro r hr h
    simp only [lxWR, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with ((h | h) | (h | h)) | h
    · exact hND.lx.x_regs r (List.mem_append_left _ h) (by simp at hr ⊢; tauto)
    · exact hND.lx.x_regs r (List.mem_append_right _ h) (by simp at hr ⊢; tauto)
    · subst h; simp at hr
    · subst h; exact hND.lx.rv_regs (by simp at hr ⊢; tauto)
    · exact hND.lx.cmp_regs r h (by simp at hr ⊢; tauto)
  have hsbfd : "fp.sb" ∉ fdWR LI X (treeImpl V ops G s) slX := by
    intro h
    simp only [fdWR, List.mem_append] at h
    rcases h with h | h
    · exact hlx _ (by decide) h
    · exact hkeep _ (by decide) (by decide) (by decide) (by decide) h
  have hsnfd : "fp.sn" ∉ fdWR LI X (treeImpl V ops G s) slX := by
    intro h
    simp only [fdWR, List.mem_append] at h
    rcases h with h | h
    · exact hlx _ (by decide) h
    · exact hkeep _ (by decide) (by decide) (by decide) (by decide) h
  have hobfd : "fp.ob" ∉ fdWR LI X (treeImpl V ops G s) slX := by
    intro h
    simp only [fdWR, List.mem_append] at h
    rcases h with h | h
    · exact hND.lxR "fp.ob" h (by simp)
    · exact hkeep _ (by decide) (by decide) (by decide) (by decide) h
  have hsb1 : s1.w "fp.sb" = st₀.w "fp.sb" := hU1.wreg _ hsbfd
  have hsn1 : s1.w "fp.sn" = st₀.w "fp.sn" := hU1.wreg _ hsnfd
  have hob1 : s1.w "fp.ob" = st₀.w "fp.ob" := hU1.wreg _ hobfd
  have hptaN : ∀ a ∈ ptaArrs, a ∉ invArrs ∧ a ∉ trArrs := by decide
  have hpta1 : ∀ a ∈ ptaArrs, s1.wa a = st₀.wa a ∧ s1.wlen a = st₀.wlen a := by
    intro a ha
    refine hU1.warr a (fun h => ?_)
    simp only [fdWA, invWA, List.mem_append] at h
    rcases h with h | ((h | h) | h) | h
    · exact hNF.x_pta a h ha
    · exact hNT.srch_pta a h ha
    · exact (hptaN a ha).1 h
    · exact (hptaN a ha).2 h
    · exact absurd h List.not_mem_nil
  have hPTA1 : PTA G.n s1 := hPTA.frame hpta1
  have hcap1 : s1.cap = st₀.cap := hU1.cap
  obtain ⟨ql, hqnd, hqset, hqlen, hqarr, hqL⟩ := hIR.Q
  have hqlN : ql.length ≤ G.n := by simpa using hqnd.length_le_card
  have hQc : ι'.Q.card = ql.length := by rw [← hqset, List.toFinset_card_of_nodup hqnd]
  rw [hQc] at htl
  have hFR1 : FR0 s1 G.n ι'.trees := hIR.fr
  -- the tail
  apply Runs.mono (Runs.cost_mono' (fpTail_spec (ops := ops) (st0 := s1) (trees := ι'.trees) (tv := ι'.tv)
    (S := S) (Q := ι'.Q) (SL := SL) (ql := ql) (k := k) (sA := sA) hk2 hFR1 (fun T hT => hFI.pf T hT) hFI.tv
    hIR.my.fm hSL (fun j h => by rw [hsA1, hsb1]; exact hroots j h) (by rw [hsb1, hsAl1]; exact hsbL)
    (by rw [hsn1]; exact hsn) (fun x => by rw [← List.mem_toFinset, hqset]) hqarr hqlen
    (by rw [hob1] at hqL ⊢; omega) hIR.my.kreg hPTA1 hNT.sA_tail (by rw [hsb1, hob1, hcap1]; omega)))
  rintro st' ⟨⟨hG, hBm, hPTA', hU2, hc2⟩, hmono⟩
  refine ⟨ι', cost, g', ⟨SL', ι'', hSL'nd, hSL', hInv, hd, hD, hQ, hW, htr, hcard⟩, hG, ?_, ?_, ?_, ?_, ?_,
    hPTA', ?_, hwalk, hle, hFI, hgext, hU1.cat hU2, by omega, ?_⟩
  · exact hIR.lab.frame hU2 hNT.tab (Disj.nil_left _) hNT.wB (Disj.nil_left _) hNT.rB (Disj.nil_left _)
      hNT.wX (Disj.nil_left _) hNT.rX (Disj.nil_left _) hmono
  · exact hIR.my.setFm hBm hU2 (by decide) (by decide)
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
  · rw [Nat.add_mul]
    omega

end Frontier.CHD.BL2
