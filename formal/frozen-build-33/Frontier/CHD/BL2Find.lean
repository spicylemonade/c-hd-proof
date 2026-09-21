import Frontier.CHD.BL2LX

/-!
# Frontier.CHD.BL2Find — B-L2: FindPivots-HD at RAM level refines Layer A's pinned `FindPivotsC`
(owner agent-09, NON-GATE)

`fpFind` = FH.1 (`fpLX`: the slot `slX` receives `L_X = d_B[S]`) followed by the invocation loop
(`fpInvoke`, FH.2–FH.25).  `fpFind_spec`: from the call's labels `d0` (label layer), `B` (slot
`slB`), the roots `SL` (a duplicate-free enumeration of `S` at `sA[fp.sb ..]`) and the deleted
edges `Din` (live out-lists), the program ends in a state representing the Layer-A outcome
`(ι'.d, ι'.D, ι'.Q, ι'.W, ι'.trees)` of a run of agent-05's pinned relation `FindPivotsC` with
cost `cost`, and its RAM cost is at most `CFD + CLX·|S| + KI·cost`.  The tree partition (FP-TAIL)
is separate (agent-03).
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}

variable (LI : LabI V ops G s) (X : LabX LI) (TI : TreeI V ops G s)

/-- **FindPivots-HD** without the tree partition: FH.1, then the invocation loop over the roots
`sA[fp.sb .. fp.sb + fp.sn)`. -/
def fpFind (sA slB slX : String) : Stmt :=
  seq (fpLX LI sA slB slX) (fpInvoke LI X TI sA slB slX)

/-- Name hygiene of the driver (discharged by `decide` at instantiation). -/
structure NamesD (slB slX sA : String) : Prop where
  lx : NamesL LI sA slB slX
  inv : NamesI LI X TI slB slX sA
  /-- FH.1 writes only the slot `slX`, scratch registers and the comparison bit -/
  lxA : Disj (LI.slWA slX) (myArrs ++ invArrs ++ TI.frWA)
  lxV : Disj (LI.slVA slX) TI.frVA
  lxR : Disj (lxWR LI slX) (myRegs ++ ["fp.ob"] ++ TI.frWR)
  lxVR : Disj (lxVR LI slX) TI.frVR

/-- Write sets of the driver. -/
def fdWA (sA slX : String) : List String := LI.slWA slX ++ invWA LI TI sA
def fdVA (slX : String) : List String := LI.slVA slX ++ invVA LI TI
def fdWR (slX : String) : List String := lxWR LI slX ++ invWR LI X TI
def fdVR (slX : String) : List String := lxVR LI slX ++ invVR LI X TI

/-- Constant part of the driver's cost. -/
def CFD : ℕ := LI.Ccopy + TI.Cinit + 8

variable {LI X TI}

theorem NamesL.sb_sn {sA slB slX : String} (hNL : NamesL LI sA slB slX) :
    ∀ r ∈ ["fp.sb", "fp.sn"], r ∉ lxWR LI slX := fun r hr h => by
  simp only [lxWR, List.mem_append] at h
  rcases h with ((h | h) | h) | h
  · exact hNL.x_regs r (List.mem_append_left _ h) (by simp at hr ⊢; tauto)
  · exact hNL.x_regs r (List.mem_append_right _ h) (by simp at hr ⊢; tauto)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h hr
    rcases h with rfl | rfl
    · rcases hr with h' | h' <;> exact absurd h' (by decide)
    · exact hNL.rv_regs (by simp at hr ⊢; tauto)
  · exact hNL.cmp_regs r h (by simp at hr ⊢; tauto)

/-- **FindPivots-HD at RAM level (FH.1–FH.25) refines the pinned Layer-A relation
`FindPivotsC`** (agent-05, O21): the final state represents the outcome of a `FindPivotsC` run
(labels in the label layer, deletions in the live out-lists, `W`, `Q`, the forest), with RAM cost
`≤ CFD + CLX·|S| + KI·cost`. -/
theorem fpFind_spec {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}
    (hout : ∀ u e, e ∈ out u ↔ G.src e = u) (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (hnd : ∀ u, (out u).Nodup) {slB slX sA : String} (hND : NamesD LI X TI slB slX sA)
    {B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} (hpre : CallPre B S d0)
    {SL : List (Fin G.n)} (hSLnd : SL.Nodup) (hSL : ∀ x, x ∈ SL ↔ x ∈ S)
    {Din : Finset (Fin G.m)} {g₀ : LI.Gh} {st₀ : State V}
    (hLT : LI.LT st₀ d0 g₀) (hB : LI.LS st₀ slB B g₀)
    (hM : MyRep (pinCtx out k hins hext B (lxOf B S d0)) ∅ (emptySt d0 Din) st₀)
    (hO : OutRep st₀ (pinCtx out k hins hext B (lxOf B S d0)) Din) (hTA : TI.TA st₀)
    (hinW : Bits (G := G) st₀ "fp.inW" ∅) (hWL : st₀.w "fp.ob" + G.n ≤ st₀.wlen "fp.W")
    (hQL : st₀.w "fp.ob" + G.n ≤ st₀.wlen "fp.Q")
    (hbud : ∀ d1 Dout Q W trees cost,
      FindPivotsC out k hins hext B S d0 Din d1 Dout Q W trees cost →
      st₀.cost + CFD LI TI + CLX LI * S.card + KI LI X TI * cost + KI LI X TI ≤ LI.c0 + st₀.cap)
    (hcapW : k + 4 < st₀.cap) (hcapN : st₀.w "fp.ob" + G.n + 2 < st₀.cap)
    (hcapS : st₀.w "fp.sb" + SL.length + 1 < st₀.cap) (hk1 : 1 ≤ k) (hhext : k ≤ hext)
    (hroots : ∀ j (h : j < SL.length), st₀.wa sA (st₀.w "fp.sb" + j) = (SL[j] : ℕ))
    (hsbL : st₀.w "fp.sb" + SL.length ≤ st₀.wlen sA) (hsn : st₀.w "fp.sn" = SL.length) :
    Runs ops (fpFind LI X TI sA slB slX) st₀ (fun st' =>
      ∃ (ι' : IState G s) (cost : ℕ) (g' : LI.Gh),
        FindPivotsC out k hins hext B S d0 Din ι'.d ι'.D ι'.Q ι'.W ι'.trees cost ∧
        IRep LI TI (pinCtx out k hins hext B (lxOf B S d0)) slB slX ι' g' st' ∧
        WalkInv ι'.d ∧ (∀ v, ι'.d v ≤ d0 v) ∧
        FInv (pinCtx out k hins hext B (lxOf B S d0)) ι' ∧ LI.gext g₀ g' ∧
        Unchanged st₀ st' (fdWA LI TI sA slX) (fdVA LI TI slX) (fdWR LI X TI slX)
          (fdVR LI X TI slX) ∧
        st₀.cost ≤ st'.cost ∧ st'.cost ≤ st₀.cost + CFD LI TI + CLX LI * S.card + KI LI X TI * cost) := by
  classical
  set c := pinCtx out k hins hext B (lxOf B S d0) with hc
  have hown : OutOK c := hout
  have hsort' : OutSorted c := hsort
  have hnd' : OutNodup c := hnd
  have hpre' : CallPre c.B S d0 := hpre
  have hSLS : ∀ x ∈ SL, x ∈ S := fun x hx => (hSL x).mp hx
  have hSLf : SL.toFinset = S := by ext x; simp [hSL]
  have hcard : S.card = SL.length := by rw [← hSLf, List.toFinset_card_of_nodup hSLnd]
  have hFP : ∀ ι' n', Invoke c ⟨d0, Din, ∅, ∅, ∅, []⟩ SL ι' n' →
      FindPivotsC out k hins hext B S d0 Din ι'.d ι'.D ι'.Q ι'.W ι'.trees n' :=
    fun ι' n' h => ⟨SL, ι', hSLnd, hSL, h, rfl, rfl, rfl, rfl, rfl, hcard⟩
  -- totality: some Layer-A run exists, so the budget of FH.1 is available
  obtain ⟨ι1, n1, hrun1⟩ := Invoke.exists_run hown hsort' hpre' SL ⟨d0, Din, ∅, ∅, ∅, []⟩ hSLS
    hpre.walk (fun _ => le_rfl)
  have hb1 := hbud _ _ _ _ _ _ (hFP _ _ hrun1)
  rw [hcard] at hb1 hbud ⊢
  have hCFD : CFD LI TI = LI.Ccopy + TI.Cinit + 8 := rfl
  unfold fpFind
  refine runs_seq ((lx_spec hND.lx hLT hB hroots hsbL hsn hcapS (by omega)).mono ?_)
  rintro st1 ⟨hX1, hLT1, hB1, hu1, hc01, hc1⟩
  have hcap1 : st1.cap = st₀.cap := hu1.cap
  have hA_my : Disj (LI.slWA slX) myArrs :=
    hND.lxA.mono_right (fun x hx => List.mem_append_left _ (List.mem_append_left _ hx))
  have hA_inv : Disj (LI.slWA slX) invArrs :=
    hND.lxA.mono_right (fun x hx => List.mem_append_left _ (List.mem_append_right _ hx))
  have hA_fr : Disj (LI.slWA slX) TI.frWA :=
    hND.lxA.mono_right (fun x hx => List.mem_append_right _ hx)
  have hR_my : Disj (lxWR LI slX) myRegs :=
    hND.lxR.mono_right (fun x hx => List.mem_append_left _ (List.mem_append_left _ hx))
  have hR_ob : "fp.ob" ∉ lxWR LI slX := fun h =>
    hND.lxR _ h (List.mem_append_left _ (List.mem_append_right _ (by simp)))
  have hR_fr : Disj (lxWR LI slX) TI.frWR :=
    hND.lxR.mono_right (fun x hx => List.mem_append_right _ hx)
  have hsb1 : st1.w "fp.sb" = st₀.w "fp.sb" := hu1.wreg _ (hND.lx.sb_sn "fp.sb" (by simp))
  have hsn1 : st1.w "fp.sn" = st₀.w "fp.sn" := hu1.wreg _ (hND.lx.sb_sn "fp.sn" (by simp))
  have hob1 : st1.w "fp.ob" = st₀.w "fp.ob" := hu1.wreg _ hR_ob
  have hsA1 := hu1.warr sA hND.lx.x_sA
  have hW1 := hu1.warr "fp.W" (fun h => hA_inv _ h (by simp [invArrs]))
  have hQ1 := hu1.warr "fp.Q" (fun h => hA_inv _ h (by simp [invArrs]))
  have hI1 := hu1.warr "fp.inW" (fun h => hA_inv _ h (by simp [invArrs]))
  have hL1 : LabRep LI c slB slX d0 g₀ st1 := ⟨hLT1, hB1, by rw [hSLf] at hX1; exact hX1⟩
  have hM1 : MyRep c ∅ (emptySt d0 Din) st1 := hM.frame hu1 hA_my hR_my
  have hO1 : OutRep st1 c Din := hO.frame hu1 hA_my
  have hTA1 : TI.TA st1 := TI.TA_frame hTA hu1 hA_fr hND.lxV hR_fr hND.lxVR
  have hinW1 : Bits (G := G) st1 "fp.inW" ∅ :=
    ⟨by rw [hI1.2]; exact hinW.1, fun v => by rw [hI1.1]; exact hinW.2 v⟩
  refine (invoke_spec hown hsort' hnd' hND.inv hpre' hSLS hSLnd hL1 hM1 hO1 hTA1 hinW1
    (by rw [hob1, hW1.2]; exact hWL) (by rw [hob1, hQ1.2]; exact hQL) ?_
    (by rw [hcap1]; exact hcapW) (by rw [hob1, hcap1]; exact hcapN)
    (by rw [hsb1, hcap1]; exact hcapS) hhext hk1
    (fun j hj => by rw [hsA1.1, hsb1]; exact hroots j hj) (by rw [hsb1, hsA1.2]; exact hsbL)
    (by rw [hsn1]; exact hsn)).mono ?_
  · intro ι' n' h
    have := hbud _ _ _ _ _ _ (hFP _ _ h)
    rw [hcap1]; omega
  · rintro st' ⟨ι', n, g', hrun, hIR, hwalk, hle, hF, hg, hu2, hc02, hc2⟩
    exact ⟨ι', n, g', hFP _ _ hrun, hIR, hwalk, hle, hF, hg, hu1.cat hu2, by omega, by omega⟩

end Frontier.CHD.BL2
