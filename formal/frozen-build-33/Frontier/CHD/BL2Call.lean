import Frontier.CHD.FPComposite
import Frontier.CHD.BL2LX
import Frontier.CHD.BL2Export
import Frontier.CHD.FPBind

/-!
# Frontier.CHD.BL2Call — B-L2: the COMPLETE FindPivots-HD call refines agent-05's `fpC`
(owner agent-09; composes agent-03's fpInvTail_spec; NON-GATE)

`fpCall = fpLX ; (fpInvoke ; fpTail) ; fpExport`:
* FH.1 (`lx_spec`, agent-09): slot `slX` := `L_X = d_B[S]`;
* the invocation loop and FP-TAIL (`fpInvTail_spec`, agent-03 over agent-09's `invoke_spec`);
* the export of `W` to the spine's row (`export_spec`, agent-09).

`fpCall_spec`: from the clean between-calls state `FPClean` (plus the call's labels, bound slot and
roots), the program ends in a state representing an outcome of agent-05's FULL FindPivots relation
`fpC` (labels, deletions, `Q`, `W`, groups `forestGroups`, data `ω`), with the groups in `GrpOut`,
`W` in row `lvl` of `W` / `W.len`, `FPClean` again (for the next call), a frame, and RAM cost
`≤ CFC + KC · cost` where `cost` is the Layer-A cost index of the call.
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt Frontier.CHD.PartitionRAM Frontier.CHD.Partition
  Frontier.CHD.RamLevel

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}

/-! ## Layer A: the invocation's cost index pays for `W` -/

theorem Invoke.W_card_le {c : FPCtx G s} (hout : OutOK c) (hsort : OutSorted c)
    {S : Finset (Fin G.n)} {d0 : Labels G s} (hpre : CallPre c.B S d0)
    {ι ι' : IState G s} {L : List (Fin G.n)} {n : ℕ} (h : Invoke c ι L ι' n)
    (hLS : ∀ x ∈ L, x ∈ S) (hw : WalkInv ι.d) (hle : ∀ v, ι.d v ≤ d0 v) :
    ι'.W.card ≤ ι.W.card + n := by
  classical
  induction h with
  | nil ι => simp
  | skip ι ι' x L n _ _ ih =>
    have := ih (fun y hy => hLS y (List.mem_cons_of_mem _ hy)) hw hle
    omega
  | fail ι ι' x L σ' n n' hx hs _ ih =>
    have hxS : x ∈ S := hLS x List.mem_cons_self
    have hxtop : ι.d x ≠ ⊤ := ne_top_of_lt (lt_of_le_of_lt (hle x) (hpre.inRange x hxS))
    have hS0 : SInv c (initSt ι.d ι.D x) := initSt_inv hw hxtop
    obtain ⟨hIs, hle', -, -, -⟩ :=
      Search.inv hout hsort hs hS0 (fun w hw => absurd hw (Finset.notMem_empty w))
    have ih' := ih (fun y hy => hLS y (List.mem_cons_of_mem _ hy)) hIs.walk
      (fun v => (hle' v).trans (hle v))
    dsimp only at ih'
    have h1 := Finset.card_union_le ι.W σ'.val
    have h2 : σ'.val.card ≤ σ'.K.length :=
      (Finset.card_le_card (fun v hv => List.mem_toFinset.mpr (hIs.valK v hv))).trans
        (List.toFinset_card_le _)
    omega
  | grow ι ι' x L σ' res n n' hx hres hs _ ih =>
    have hxS : x ∈ S := hLS x List.mem_cons_self
    have hxtop : ι.d x ≠ ⊤ := ne_top_of_lt (lt_of_le_of_lt (hle x) (hpre.inRange x hxS))
    have hS0 : SInv c (initSt ι.d ι.D x) := initSt_inv hw hxtop
    obtain ⟨hIs, hle', -, -, -⟩ :=
      Search.inv hout hsort hs hS0 (fun w hw => absurd hw (Finset.notMem_empty w))
    have ih' := ih (fun y hy => hLS y (List.mem_cons_of_mem _ hy)) hIs.walk
      (fun v => (hle' v).trans (hle v))
    dsimp only at ih'
    omega

/-! ## The clean FindPivots state between two calls -/

/-- **The FindPivots scratch state between two calls**: empty heap / member list / marks,
`fp.fm = ∅`, `fp.inW = ∅`, the live out-lists represent the deleted edges `D`, the tree and tail
arrays are allocated and clean, and `W` / `Q` have room. -/
structure FPClean (c : FPCtx G s) (d : Labels G s) (D : Finset (Fin G.m)) (st : State V) :
    Prop where
  my : MyRep c ∅ (emptySt d D) st
  out : OutRep st c D
  ta : TA0 G.n st
  pta : PTA G.n st
  inW : Bits (G := G) st "fp.inW" ∅
  wlen : st.w "fp.ob" + G.n ≤ st.wlen "fp.W"
  qlen : st.w "fp.ob" + G.n ≤ st.wlen "fp.Q"
  /-- `W` / `Q` start at offset `0` -/
  ob0 : st.w "fp.ob" = 0

/-- `MyRep` only depends on the cap `k` of the context (and not on the labels of the empty
search state). -/
theorem MyRep.congr_ctx {c c' : FPCtx G s} {T : Finset (Fin G.n)} {d d' : Labels G s}
    {D D' : Finset (Fin G.m)} {st : State V} (h : MyRep c T (emptySt d D) st) (hk : c.k = c'.k) :
    MyRep c' T (emptySt d' D') st :=
  ⟨h.gM, h.headL, h.head, hk ▸ h.heap, h.kl, hk ▸ h.kcap, h.karr, h.inK, h.val, h.fm, h.kpL,
    h.kp, hk ▸ h.kreg, h.Knd, h.HK⟩

/-- `OutRep` only depends on the out-lists of the context. -/
theorem OutRep.congr_ctx {c c' : FPCtx G s} {D : Finset (Fin G.m)} {st : State V}
    (h : OutRep st c D) (ho : c.out = c'.out) : OutRep st c' D := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun w => ?_⟩
  have : live c D w = live c' D w := by unfold live; rw [ho]
  rw [← this]; exact h2 w

/-- **The clean state is independent of the call** (only `k` and the out-lists matter). -/
theorem FPClean.congr {c c' : FPCtx G s} {d d' : Labels G s} {D : Finset (Fin G.m)}
    {st : State V} (h : FPClean c d D st) (hk : c.k = c'.k) (ho : c.out = c'.out) :
    FPClean c' d' D st :=
  ⟨h.my.congr_ctx hk, h.out.congr_ctx ho, h.ta, h.pta, h.inW, h.wlen, h.qlen, h.ob0⟩

/-- `GrpOut` survives writes outside its cells. -/
theorem GrpOut.of_unchanged {st st' : State V} {Gs : List (List ℕ)} {wa va wr vr : List String}
    (h : GrpOut st Gs) (hu : Unchanged st st' wa va wr vr)
    (hA : Disj wa ["pt.GO", "pt.GL", "pt.GV"]) (hR : Disj wr ["pt.ng", "pt.gv"]) :
    GrpOut st' Gs := by
  obtain ⟨h1, h2, h3⟩ := h
  have aO := hu.warr "pt.GO" (fun h' => hA _ h' (by simp))
  have aL := hu.warr "pt.GL" (fun h' => hA _ h' (by simp))
  have aV := hu.warr "pt.GV" (fun h' => hA _ h' (by simp))
  refine ⟨by rw [hu.wreg _ (fun h' => hR _ h' (by simp))]; exact h1,
    by rw [hu.wreg _ (fun h' => hR _ h' (by simp))]; exact h2, fun j hj => ?_⟩
  obtain ⟨e1, e2, e3⟩ := h3 j hj
  exact ⟨by rw [aO.1]; exact e1, by rw [aL.1]; exact e2, fun i hi => by rw [aV.1]; exact e3 i hi⟩

/-! ## The complete call -/

section

variable (LI : LabI V ops G s) (X : LabX LI)

/-- **FindPivots-HD, complete**: FH.1, the invocation loop, FP-TAIL, export of `W`. -/
def fpCall (sA slB slX : String) : Stmt :=
  seq (fpLX LI sA slB slX)
    (seq (seq (fpInvoke LI X (treeImpl V ops G s) sA slB slX) (fpTail sA)) fpExport)

/-- Write sets of the complete call. -/
def fcWA (sA slX : String) : List String :=
  (LI.slWA slX ++ (invWA LI (treeImpl V ops G s) sA ++ tailWA)) ++ ["W", "W.len", "fp.inW"]
def fcVA (slX : String) : List String :=
  (LI.slVA slX ++ (invVA LI (treeImpl V ops G s) ++ [])) ++ []
def fcWR (slX : String) : List String :=
  (lxWR LI slX ++ (invWR LI X (treeImpl V ops G s) ++ tailWR)) ++ ["fp.i", "fp.y"]
def fcVR (slX : String) : List String :=
  (lxVR LI slX ++ (invVR LI X (treeImpl V ops G s) ++ [])) ++ []

/-- Constant and per-unit cost of the complete call. -/
def CFC : ℕ := LI.Ccopy + KI LI X (treeImpl V ops G s) + 42
def KC : ℕ := CLX LI + KI LI X (treeImpl V ops G s) + 194

/-- Name hygiene of the complete call beyond `NamesL` / `NamesI` / `NamesTail` (decided at
instantiation). -/
structure NamesCall (slB slX sA : String) : Prop where
  lxA : Disj (LI.slWA slX) (myArrs ++ invArrs ++ frWA0 ++ ptaArrs ++ ["W", "W.len"])
  lxV : Disj (LI.slVA slX) []
  lxR : Disj (lxWR LI slX) (myRegs ++ ["fp.ob", "lvl", "n", "tr.nt"])
  lxVR : Disj (lxVR LI slX) []
  invW : Disj (invWA LI (treeImpl V ops G s) sA ++ tailWA) ["W", "W.len"]
  invR : Disj (invWR LI X (treeImpl V ops G s) ++ tailWR) ["lvl", "n"]
  exA_tab : Disj ["W", "W.len", "fp.inW"] LI.tabWA
  exA_slB : Disj ["W", "W.len", "fp.inW"] (LI.slWA slB)
  exA_slX : Disj ["W", "W.len", "fp.inW"] (LI.slWA slX)
  exR_slB : Disj ["fp.i", "fp.y"] (LI.slWR slB)
  exR_slX : Disj ["fp.i", "fp.y"] (LI.slWR slX)

end

variable {LI : LabI V ops G s} {X : LabX LI}

/-- **The complete FindPivots-HD call at RAM level refines agent-05's FindPivots relation `fpC`**
(the FindPivots parameter of the cost-indexed BMSSP): the final state represents the labels,
deletions, groups (`GrpOut`), and `W` (spine row `lvl`) of an `fpC` outcome with Layer-A cost
index `cost`, the scratch state is clean again for the next call, and the RAM cost is
`≤ CFC + KC · cost`. -/
theorem fpCall_spec {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}
    (hout : ∀ u e, e ∈ out u ↔ G.src e = u) (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (hnd : ∀ u, (out u).Nodup) {slB slX sA : String}
    (hNL : NamesL LI sA slB slX) (hNI : NamesI LI X (treeImpl V ops G s) slB slX sA)
    (hNT : NamesTail LI slB slX sA) (hNC : NamesCall LI X slB slX sA)
    (hk2 : 2 ≤ k) (hhext : k ≤ hext)
    {B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} (hpre : CallPre B S d0)
    {SL : List (Fin G.n)} (hSLnd : SL.Nodup) (hSL : ∀ x, x ∈ SL ↔ x ∈ S)
    {Din : Finset (Fin G.m)} {g₀ : LI.Gh} {st₀ : State V} {l : ℕ}
    (hLT : LI.LT st₀ d0 g₀) (hB : LI.LS st₀ slB B g₀)
    (hC : FPClean (pinCtx out k hins hext B (lxOf B S d0)) d0 Din st₀)
    (hroots : ∀ j (h : j < SL.length), st₀.wa sA (st₀.w "fp.sb" + j) = (SL[j] : ℕ))
    (hsbL : st₀.w "fp.sb" + SL.length ≤ st₀.wlen sA) (hsn : st₀.w "fp.sn" = SL.length)
    (hl : st₀.w "lvl" = l) (hn : st₀.w "n" = G.n) (hWlen : l < st₀.wlen "W.len")
    (hrow : (l + 1) * G.n ≤ st₀.wlen "W")
    (hbud : ∀ d1 Dout Q W trees cost,
      FindPivotsC out k hins hext B S d0 Din d1 Dout Q W trees cost →
      st₀.cost + CFC LI X + KC LI X * cost ≤ LI.c0 + st₀.cap)
    (hcap : (l + 1) * G.n + 3 * G.n + st₀.w "fp.sb" + SL.length + st₀.w "fp.ob" + 2 * k + 4 <
      st₀.cap) :
    Runs ops (fpCall LI X sA slB slX) st₀ (fun st' =>
      ∃ (ι' : IState G s) (cost : ℕ) (g' : LI.Gh) (wl : List (Fin G.n)),
        (∀ l' Blow, fpC G s out k hins hext l' Blow B S d0 Din ι'.d
          (forestGroups S ι'.Q k ι'.trees).length
          (fun j => ((forestGroups S ι'.Q k ι'.trees).get j).toFinset) ι'.Q ι'.W ι'.D
          ⟨lxOf B S d0, ι'.trees, Din, ι'.D⟩ cost) ∧
        LabRep LI (pinCtx out k hins hext B (lxOf B S d0)) slB slX ι'.d g' st' ∧ LI.gext g₀ g' ∧
        WalkInv ι'.d ∧ (∀ v, ι'.d v ≤ d0 v) ∧
        FPClean (pinCtx out k hins hext B (lxOf B S d0)) ι'.d ι'.D st' ∧
        GrpOut st' ((forestGroups S ι'.Q k ι'.trees).map (List.map Fin.val)) ∧
        wl.Nodup ∧ wl.toFinset = ι'.W ∧ RowRep st' "W" "W.len" G.n l (wl.map Fin.val) ∧
        (∀ j, j ≠ l → st'.wa "W.len" j = st₀.wa "W.len" j) ∧
        (∀ j, (j < l * G.n ∨ (l + 1) * G.n ≤ j) → st'.wa "W" j = st₀.wa "W" j) ∧
        Unchanged st₀ st' (fcWA LI sA slX) (fcVA LI slX) (fcWR LI X slX) (fcVR LI X slX) ∧
        st₀.cost ≤ st'.cost ∧ st'.cost ≤ st₀.cost + CFC LI X + KC LI X * cost) := by
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
  have hlen_le : ∀ ι' n', Invoke c ⟨d0, Din, ∅, ∅, ∅, []⟩ SL ι' n' → SL.length ≤ n' :=
    fun ι' n' h => by have := h.tv_len_le; simp only [Finset.card_empty] at this; omega
  have hCFC : CFC LI X = LI.Ccopy + KI LI X (treeImpl V ops G s) + 42 := rfl
  have hKC : ∀ n, KC LI X * n = CLX LI * n + KI LI X (treeImpl V ops G s) * n + 194 * n :=
    fun n => by simp only [KC]; ring
  have hCi : (treeImpl V ops G s).Cinit = 1 := rfl
  -- totality: some Layer-A run exists, so the budget of FH.1 is available
  obtain ⟨ι1, n1, hrun1⟩ := Invoke.exists_run hown hsort' hpre' SL ⟨d0, Din, ∅, ∅, ∅, []⟩ hSLS
    hpre.walk (fun _ => le_rfl)
  have hb1 := hbud _ _ _ _ _ _ (hFP _ _ hrun1)
  have hl1 := hlen_le _ _ hrun1
  have hm1 : CLX LI * SL.length ≤ CLX LI * n1 := Nat.mul_le_mul_left _ hl1
  rw [hKC, hCFC] at hb1
  unfold fpCall
  -- FH.1
  refine runs_seq ((lx_spec hNL hLT hB hroots hsbL hsn (by omega) (by omega)).mono ?_)
  rintro st1 ⟨hX1, hLT1, hB1, hu1, hc01, hc1⟩
  have hcap1 : st1.cap = st₀.cap := hu1.cap
  have hA1 : ∀ a ∈ myArrs ++ invArrs ++ frWA0 ++ ptaArrs ++ ["W", "W.len"],
      st1.wa a = st₀.wa a ∧ st1.wlen a = st₀.wlen a :=
    fun a ha => hu1.warr a (fun h => hNC.lxA a h ha)
  have hR1 : ∀ r ∈ myRegs ++ ["fp.ob", "lvl", "n", "tr.nt"], st1.w r = st₀.w r :=
    fun r hr => hu1.wreg r (fun h => hNC.lxR r h hr)
  have hsb1 : st1.w "fp.sb" = st₀.w "fp.sb" := hu1.wreg _ (hNL.sb_sn "fp.sb" (by simp))
  have hsn1 : st1.w "fp.sn" = st₀.w "fp.sn" := hu1.wreg _ (hNL.sb_sn "fp.sn" (by simp))
  have hob1 : st1.w "fp.ob" = st₀.w "fp.ob" := hR1 _ (by simp)
  have hsA1 := hu1.warr sA hNL.x_sA
  have hL1 : LabRep LI c slB slX d0 g₀ st1 := ⟨hLT1, hB1, by rw [hSLf] at hX1; exact hX1⟩
  have hM1 : MyRep c ∅ (emptySt d0 Din) st1 :=
    hC.my.frame hu1 (hNC.lxA.mono_right (fun x hx => by simp [hx]))
      (hNC.lxR.mono_right (fun x hx => by simp [hx]))
  have hO1 : OutRep st1 c Din := hC.out.frame hu1 (hNC.lxA.mono_right (fun x hx => by simp [hx]))
  have hTA1 : TA0 G.n st1 := TA0.frame hC.ta (fun a ha => hA1 a (by simp [ha]))
  have hPTA1 : PTA G.n st1 := hC.pta.frame (fun a ha => hA1 a (by simp [ha]))
  have hI1 := hA1 "fp.inW" (by simp [invArrs])
  have hW1 := hA1 "fp.W" (by simp [invArrs])
  have hQ1 := hA1 "fp.Q" (by simp [invArrs])
  have hinW1 : Bits (G := G) st1 "fp.inW" ∅ :=
    ⟨by rw [hI1.2]; exact hC.inW.1, fun v => by rw [hI1.1]; exact hC.inW.2 v⟩
  -- the invocation loop and the tail (agent-03's composite)
  refine runs_seq ((fpInvTail_spec (c := c) (X := X) hown hsort' hnd' hNI hNT hpre' hSL hSLnd hL1
    hM1 hO1 hTA1 hPTA1 hinW1 (by rw [hob1, hW1.2]; exact hC.wlen) (by rw [hob1, hQ1.2]; exact hC.qlen)
    ?_ (by rw [hcap1]; show k + 4 < st₀.cap; omega) (by rw [hob1, hcap1]; omega)
    (by rw [hsb1, hcap1]; omega) (by rw [hsb1, hob1, hcap1]; show _ + 2 * k + 4 < _; omega)
    hhext hk2 (fun j hj => by rw [hsA1.1, hsb1]; exact hroots j hj)
    (by rw [hsb1, hsA1.2]; exact hsbL) (by rw [hsn1]; exact hsn)).mono ?_)
  · intro ι' n' h
    have hb := hbud _ _ _ _ _ _ (hFP _ _ h)
    have hl' := hlen_le _ _ h
    have hm' : CLX LI * SL.length ≤ CLX LI * n' := Nat.mul_le_mul_left _ hl'
    rw [hKC, hCFC] at hb
    rw [hCi, hcap1]; omega
  rintro st2 ⟨ι', n, g', hInv, hwalk, hle, hFI, hgext, hLab2, hM2, hO2, hW2, hQ2, hG2, hPTA2, hTA2,
    hU2, hc02, hc2⟩
  have hcap2 : st2.cap = st₀.cap := by rw [hU2.cap, hcap1]
  have hRn : ∀ r ∈ ["lvl", "n"], st2.w r = st₀.w r := fun r hr => by
    rw [hU2.wreg r (fun h => hNC.invR r h hr), hR1 r (by simp at hr ⊢; tauto)]
  have hAW : ∀ a ∈ ["W", "W.len"], st2.wa a = st₀.wa a ∧ st2.wlen a = st₀.wlen a := fun a ha => by
    have e2 := hU2.warr a (fun h => hNC.invW a h ha)
    have e1 := hA1 a (by simp at ha ⊢; tauto)
    exact ⟨e2.1.trans e1.1, e2.2.trans e1.2⟩
  have hob2 : st2.w "fp.ob" = st₀.w "fp.ob" := by
    rw [hU2.wreg _ (fun h => ?_), hob1]
    simp only [invWR, List.mem_append] at h
    rcases h with (((h | h) | h) | h) | h
    · exact hNI.srch_inv _ h (by decide)
    · exact absurd h (by decide)
    · exact (by decide : "fp.ob" ∉ trRegs) h
    · exact (by decide : "fp.ob" ∉ ["tr.nt"]) h
    · exact absurd h (by decide)
  -- export of `W`
  have hWc : ι'.W.card ≤ n := by
    have := Invoke.W_card_le hown hsort' hpre' hInv hSLS hpre.walk (fun _ => le_rfl)
    simpa using this
  have hD0 : ∀ a ∈ frWA0, a ∉ ["W", "W.len", "fp.inW"] := by decide
  have hDP : ∀ a ∈ ptaArrs, a ∉ ["W", "W.len", "fp.inW"] := by decide
  refine (export_spec (ops := ops) (l := l) hW2 (by rw [hRn "lvl" (by simp)]; exact hl)
    (by rw [hRn "n" (by simp)]; exact hn) (by rw [(hAW "W.len" (by simp)).2]; exact hWlen)
    (by rw [(hAW "W" (by simp)).2]; exact hrow) (by rw [hob2, hcap2]; omega)).mono ?_
  rintro st3 ⟨wl, hwnd, hwset, hR3, hinW3, hu3, hWl3, hWLl3, hoL3, hoW3, hc03, hc3⟩
  have hl2 := hlen_le _ _ hInv
  have hm2 : CLX LI * SL.length ≤ CLX LI * n := Nat.mul_le_mul_left _ hl2
  refine ⟨ι', n, g', wl, fun l' Blow => ⟨hFP _ _ hInv, rfl, ⟨rfl, fun j => rfl⟩, rfl, rfl⟩,
    hLab2.frame hu3 hNC.exA_tab (Disj.nil_left _) hNC.exA_slB (Disj.nil_left _) hNC.exR_slB
      (Disj.nil_left _) hNC.exA_slX (Disj.nil_left _) hNC.exR_slX (Disj.nil_left _) hc03,
    hgext, hwalk, hle, ⟨hM2.frame hu3 (by decide) (by decide), hO2.frame hu3 (by decide),
      TA0.frame hTA2 (fun a ha => hu3.warr a (hD0 a ha)),
      hPTA2.frame (fun a ha => hu3.warr a (hDP a ha)),
      hinW3, ?_, ?_, by rw [hu3.wreg _ (by decide), hob2]; exact hC.ob0⟩,
    GrpOut.of_unchanged hG2 hu3 (by decide) (by decide), hwnd, hwset, hR3,
    fun j hj => by rw [hoL3 j hj, (hAW "W.len" (by simp)).1],
    fun j hj => by rw [hoW3 j hj, (hAW "W" (by simp)).1],
    (hu1.cat hU2).cat hu3, by omega, ?_⟩
  · obtain ⟨_, _, _, _, _, _, hWL2⟩ := hW2
    rw [hu3.wreg _ (by decide), (hu3.warr "fp.W" (by decide)).2]; exact hWL2
  · obtain ⟨_, _, _, _, _, hQL2⟩ := hQ2
    rw [hu3.wreg _ (by decide), (hu3.warr "fp.Q" (by decide)).2]; exact hQL2
  · rw [hKC, hCFC]
    have e1 : (KI LI X (treeImpl V ops G s) + 188) * n = KI LI X (treeImpl V ops G s) * n + 188 * n := by
      ring
    have : 6 * ι'.W.card ≤ 6 * n := by omega
    omega

end Frontier.CHD.BL2
