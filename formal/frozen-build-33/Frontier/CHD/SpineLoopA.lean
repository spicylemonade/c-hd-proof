import Frontier.CHD.SpineFirst
import Frontier.CHD.SpineRule

/-!
# SpineLoopA — the main loop of a recursive call (agent-08, B-L4, NON-GATE)

The loop `mainLoop DL.empty (seq (firstHalf DL.pull ltBi) postI)` refines agent-01's concrete
`LoopD` with two constants: `Ko` per unit of the loop's own work (`cc + cm`), `K` per unit of the
sub-calls (`lg.cost`).  The first half of an iteration is `firstHalf_spec`; the second half is an
interface `PostHalf` (agent-06's `postSpec` with its `postCost`); the loop is `loopTight` at factor
`1` over the weighted iterations `IterRelW`.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamSpine

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.RamLevel
  Frontier.CHD.BM Frontier.CHD.RamBaseCase Frontier.CHD.LabTab WExpr Stmt

variable {G : Graph} {s : Fin G.n}

/-! ## The cost of the second half -/

/-- The fold of the window scan (BM.19–21) from the merged, FIX-STALE-deleted structure. -/
noncomputable abbrev foldA (T : ℕ) (B Bi : WLab G s) (Dc1 Dci : DStrM G s) (d1 : Labels G s)
    (g2 : DGl G s) (lUi : List (Fin G.n)) (L' : List (Fin G.m)) : RSt G s :=
  L'.foldl (relaxInsCc (dlOps G s) T B (some Bi)) ⟨d1, (delC g2 lUi).1, ((dlOps G s).merge T Dc1 Dci).1, 0⟩

/-- The Layer-A cost of the second half of an iteration (after the sub-call): merge, deletion, the
two `|U_i|` scans, the window scan, the re-selection scan and insertions (= agent-06's
`postCost`). -/
noncomputable def restCostA (T : ℕ) (B : WLab G s) {p : ℕ} (cs : CSt G s p) (Bi : WLab G s)
    (Ui : Finset (Fin G.n)) (Dc1 Dci : DStrM G s) (d1 : Labels G s) (g2 : DGl G s)
    (lUi : List (Fin G.n)) (L' : List (Fin G.m)) (lres : List (Fin G.n)) : ℕ :=
  ((dlOps G s).merge T Dc1 Dci).2 + (delC g2 lUi).2 + 2 * Ui.card +
    (foldA T B Bi Dc1 Dci d1 g2 lUi L').c +
    (∑ j ∈ markedGroups cs.lit Ui, ((cs.P j \ Ui).card + 1)) +
    (insManyC (dlOps G s) T (foldA T B Bi Dc1 Dci d1 g2 lUi L').d lres
      (foldA T B Bi Dc1 Dci d1 g2 lUi L').g (foldA T B Bi Dc1 Dci d1 g2 lUi L').Dc).2.2

/-- The own cost of an iteration splits into the first half's and the second half's. -/
theorem iterCost_split (T : ℕ) (B : WLab G s) {p : ℕ} (cs : CSt G s p) (ks : List (Fin G.n))
    (cp : ℕ) (Bi : WLab G s) (Ui : Finset (Fin G.n)) (Dc1 Dci : DStrM G s) (d1 : Labels G s)
    (g2 : DGl G s) (lUi : List (Fin G.n)) (L' : List (Fin G.m)) (lres : List (Fin G.n)) :
    iterCostD (dlOps G s) T B cs ks.toFinset cp Bi Ui Dc1 Dci d1 g2 lUi L' lres +
        ((dlOps G s).merge T Dc1 Dci).2 =
      (1 + cp + (ks.toFinset.card + ∑ j ∈ pulledGroups cs.lit ks.toFinset, (cs.P j).card)) +
        restCostA T B cs Bi Ui Dc1 Dci d1 g2 lUi L' lres := by
  simp only [iterCostD, restCostA, foldA]; ring

/-! ## The second half as an interface -/

section postHalf

variable {T : ℕ → ℕ} {Φ Ω : Type}

/-- **The second half of an iteration** (`merge; removeU; scan; resel; appU; dsEmpty`, agent-06's
`postSpec`): from `PostCall` and the Layer-A context of the iteration, `post` completes one
`IterRelD` step and ends in `LoopRep` of `⟨c.i + 1, nextD …, φ1⟩` with the emptiness bit of the new
view, at cost `≤ Kp · (restCostA + 1)` and use `≤ 2 · restCostA`, given the budget and the room of
every completion. -/
def PostHalf (DL : DLayer G s T) (PI : PhiI Φ) (LF : ℕ) (body : Stmt) (τf Mf : ℕ → ℕ)
    (Inv : Φ → Prop) (FPC : FPRelC G s Φ Ω) (DCb : DCost) (l : ℕ) (post : Stmt) (Kp Sl : ℕ) :
    Prop :=
  ∀ (B : WLab G s) (S : Finset (Fin G.n)) (d0 d1 : Labels G s) (p : ℕ)
    (P0 : Fin p → Finset (Fin G.n)) (Q W : Finset (Fin G.n)) (B'0 : WLab G s) (f0 : ℕ)
    (L0 : LiveM G s) (c : LoopCfgD G s Φ p) (ks : List (Fin G.n)) (Bi : WLab G s) (g1 : DGl G s)
    (Dc1 : DStrM G s) (cp : ℕ) (B'i : WLab G s) (Ui : Finset (Fin G.n)) (Dci : DStrM G s)
    (d1' : Labels G s) (φ1 : Φ) (g2 : DGl G s) (lg : Log G s Ω) (st0 st : State ℝ≥0) (τl : ℕ)
    (Ds : ℕ → DStrM G s) (H : Hist G) (c0 : ℕ),
    CallPre B S d0 → FPContract B S d0 d1 p P0 Q W →
    ALoop (dlOps G s) Inv Mf l B S d0 d1 P0 B'0 f0 L0 c → ¬ (c.cs.g.view c.cs.Dc).IsEmpty →
    pullC (dlOps G s) (T (l + 1)) c.cs.g c.cs.Dc = (ks, Bi, g1, Dc1, cp) →
    BMSSPD G s (dlOps G s) FPC DCb T Mf τf l c.cs.B' Bi (BM.expand c.cs.lit ks.toFinset Bi) c.cs.d
      c.φ g1 (B'i, Ui, Dci, d1') φ1 g2 lg →
    PostCall DL PI LF body τf Mf st0 l B τl Ds c0 c Bi Dc1 B'i Ui Dci d1' φ1 g2 H st →
    (∀ (lUi : List (Fin G.n)) (L' : List (Fin G.m)) (piv' : Fin p → Fin G.n)
      (lres : List (Fin G.n)), lUi.Nodup → lUi.toFinset = Ui → L'.Nodup →
      (∀ e, e ∈ L' ↔ G.src e ∈ Ui ∧ Bi ≤ ext (d1' (G.src e)) e ∧ ext (d1' (G.src e)) e < B) →
      Reselect c.cs.lit Ui (foldA (T (l + 1)) B Bi Dc1 Dci d1' g2 lUi L').d piv' →
      lres.Nodup → lres.toFinset = reselected c.cs.lit Ui piv' →
      st.cost + Kp * (restCostA (T (l + 1)) B c.cs Bi Ui Dc1 Dci d1' g2 lUi L' lres + 1) + Sl ≤
        c0 + st.cap) →
    (∀ (lUi : List (Fin G.n)) (L' : List (Fin G.m)) (piv' : Fin p → Fin G.n)
      (lres : List (Fin G.n)), lUi.Nodup → lUi.toFinset = Ui → L'.Nodup →
      (∀ e, e ∈ L' ↔ G.src e ∈ Ui ∧ Bi ≤ ext (d1' (G.src e)) e ∧ ext (d1' (G.src e)) e < B) →
      Reselect c.cs.lit Ui (foldA (T (l + 1)) B Bi Dc1 Dci d1' g2 lUi L').d piv' →
      lres.Nodup → lres.toFinset = reselected c.cs.lit Ui piv' →
      DL.use st + 2 * restCostA (T (l + 1)) B c.cs Bi Ui Dc1 Dci d1' g2 lUi L' lres ≤ DL.ucap) →
    Runs realOps post st (fun r => ∃ (lUi : List (Fin G.n)) (L' : List (Fin G.m))
      (piv' : Fin p → Fin G.n) (lres : List (Fin G.n)) (H' : Hist G),
      lUi.Nodup ∧ lUi.toFinset = Ui ∧ L'.Nodup ∧
      (∀ e, e ∈ L' ↔ G.src e ∈ Ui ∧ Bi ≤ ext (d1' (G.src e)) e ∧ ext (d1' (G.src e)) e < B) ∧
      Reselect c.cs.lit Ui (foldA (T (l + 1)) B Bi Dc1 Dci d1' g2 lUi L').d piv' ∧
      lres.Nodup ∧ lres.toFinset = reselected c.cs.lit Ui piv' ∧
      LoopRep DL PI LF body τf Mf r (l + 1) B τl Ds H' c0
        ⟨c.i + 1, nextD (dlOps G s) (T (l + 1)) B c.cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres, φ1⟩ ∧
      (r.w "sp.em" = 0 ↔ ¬ ((nextD (dlOps G s) (T (l + 1)) B c.cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv'
        lres).g.view (nextD (dlOps G s) (T (l + 1)) B c.cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv'
        lres).Dc).IsEmpty) ∧
      HExt H (vc st) H' (vc r) ∧ LFrame st0 r G.n l ∧
      (∀ x : Fin G.n, x ∉ c.cs.U ∪ Ui → r.wa "sp.ptr" x = st0.wa "sp.ptr" x) ∧
      st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + Kp * (restCostA (T (l + 1)) B c.cs Bi Ui Dc1 Dci d1' g2 lUi L' lres + 1) ∧
      DL.use r ≤ DL.use st + 2 * restCostA (T (l + 1)) B c.cs Bi Ui Dc1 Dci d1' g2 lUi L' lres)

end postHalf

/-! ## Framing the loop representation -/

section repFrame

variable {T : ℕ → ℕ} {Φ : Type}

/-- **`LoopRep` survives any fragment whose footprint avoids the spine's and B-L2's names** (the
`D` field is re-established by the caller). -/
theorem LoopRep.of_frame {DL : DLayer G s T} {PI : PhiI Φ} {LF : ℕ} {body : Stmt} {τf Mf : ℕ → ℕ}
    {st r : State ℝ≥0} {l : ℕ} {B : WLab G s} {τl : ℕ} {Ds : ℕ → DStrM G s} {H : Hist G} {c0 : ℕ}
    {p : ℕ} {c : LoopCfgD G s Φ p} (h : LoopRep DL PI LF body τf Mf st l B τl Ds H c0 c)
    {wa va wr vr : List String} (hU : Unchanged st r wa va wr vr)
    (hwa : ∀ a ∈ wa, a ∉ spArrs ∧ a ∉ PI.pWA) (hva : ∀ a ∈ va, a ∉ "sl.l" :: "gW" :: labV)
    (hwr : ∀ a ∈ wr, a ∉ ["lvl", "n", "gN", "hp_n"] ∧ a ∉ PI.pWR)
    (hD : DL.DR r H c.cs.g (Function.update Ds l c.cs.Dc) l)
    (hwl : r.wlen = st.wlen) (hvl : r.vlen = st.vlen) (hc : st.cost ≤ r.cost) :
    LoopRep DL PI LF body τf Mf r l B τl Ds H c0 c := by
  have nw : ∀ a ∈ spArrs, a ∉ wa := fun a ha h' => (hwa a h').1 ha
  have nv : ∀ a ∈ "sl.l" :: "gW" :: labV, a ∉ va := fun a ha h' => hva a h' ha
  have nr : ∀ a ∈ ["lvl", "n", "gN", "hp_n"], a ∉ wr := fun a ha h' => (hwr a h').1 ha
  have A : ∀ a ∈ spArrs, r.wa a = st.wa a := fun a ha => (hU.warr a (nw a ha)).1
  have hvc : vc (G := G) r = vc st := funext fun v => by
    simp only [vc]; rw [A "vcnt" (by simp [spArrs, labW])]
  refine ⟨by rw [hU.wreg _ (nr _ (by simp))]; exact h.lvl, h.l1, h.lvl_le, ?_, ?_, hD, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Static.of_frame h.stat hwl hvl
      (fun a ha => A a (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp [spArrs]))
      (hU.varr "gW" (nv _ (by simp))).1
      (fun z hz => hU.wreg z (nr z (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl <;> simp)))
      hU.procs hU.cap
  · exact LabAt.of_unchanged h.lab hU (fun a ha => nw a (by simp [spArrs, ha]))
      (nv _ (by simp [labV])) hc
  · exact PI.frame st r c.φ wa va wr vr h.phi hU (fun a ha h' => (hwa a h').2 ha)
      (fun a ha h' => (hwr a h').2 ha)
  · exact GrpRep.of_eq h.grp (fun a ha => A a (by
      simp only [grpArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [spArrs, rowArrs]))
      (fun a _ => by rw [hwl])
  · exact ⟨by rw [hwl]; exact h.np.1, by rw [A "sp.np" (by simp [spArrs, lenArrs])]; exact h.np.2⟩
  · exact setRow_of_rows h.U (fun i _ _ => by rw [A "U" (by simp [spArrs, rowArrs])])
      (by rw [A "U.len" (by simp [spArrs, lenArrs])]) (by rw [hwl]) (by rw [hwl])
  · intro v; rw [A "sp.inU" (by simp [spArrs, rowArrs])]; exact h.inU v
  · rw [hvc]
    exact h.sB.of_unchanged hU (fun a ha => nw a (by simp [spArrs, ha])) (nv _ (by simp))
  · rw [hvc]
    exact h.sBp.of_unchanged hU (fun a ha => nw a (by simp [spArrs, ha])) (nv _ (by simp))
  · rw [A "cp.tau" (by simp [spArrs])]; exact h.tau
  · exact ⟨fun l' h' x hx => by rw [A "sp.g" (by simp [spArrs, rowArrs])]; exact h.clr.g l' h' x hx,
      fun l' h' x hx => by rw [A "sp.inU" (by simp [spArrs, rowArrs])]; exact h.clr.inU l' h' x hx,
      fun x hx => by rw [A "sp.xm" (by simp [spArrs])]; exact h.clr.xm x hx⟩
  · exact fun u hu => PtrOK.of_eq (h.ptr u hu) (A "gSt" (by simp [spArrs]))
      (by rw [A "sp.ptr" (by simp [spArrs])])

end repFrame

/-! ## Small transports -/

section transports

variable {T : ℕ → ℕ} {Φ : Type}

theorem LoopRep.congr_i {DL : DLayer G s T} {PI : PhiI Φ} {LF : ℕ} {body : Stmt} {τf Mf : ℕ → ℕ}
    {st : State ℝ≥0} {l : ℕ} {B : WLab G s} {τl : ℕ} {Ds : ℕ → DStrM G s} {H : Hist G} {c0 : ℕ}
    {p : ℕ} {c : LoopCfgD G s Φ p} (h : LoopRep DL PI LF body τf Mf st l B τl Ds H c0 c) (i : ℕ) :
    LoopRep DL PI LF body τf Mf st l B τl Ds H c0 ⟨i, c.cs, c.φ⟩ :=
  ⟨h.lvl, h.l1, h.lvl_le, h.stat, h.lab, h.D, h.phi, h.grp, h.np, h.U, h.inU, h.sB, h.sBp, h.tau,
    h.clr, h.ptr⟩

theorem ALoop.congr_i {ops : DOps G s} {Inv : Φ → Prop} {Mf : ℕ → ℕ} {l : ℕ} {B : WLab G s}
    {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {p : ℕ} {P0 : Fin p → Finset (Fin G.n)}
    {B'0 : WLab G s} {f0 : ℕ} {L0 : LiveM G s} {c : LoopCfgD G s Φ p}
    (h : ALoop ops Inv Mf l B S d0 d1 P0 B'0 f0 L0 c) (i : ℕ) :
    ALoop ops Inv Mf l B S d0 d1 P0 B'0 f0 L0 ⟨i, c.cs, c.φ⟩ :=
  ⟨h.linv, h.inv, h.sinv, h.M, h.kinj, h.chg, h.touch⟩

theorem RelLoop.inv {σ : Type} {R : σ → σ → ℕ → Prop} {done : σ → Prop} {Inv : σ → Prop}
    (hs : ∀ a a' k, Inv a → ¬ done a → R a a' k → Inv a') :
    ∀ {a a' : σ} {k : ℕ}, RelLoop R done a a' k → Inv a → Inv a' := by
  intro a a' k h
  induction h with
  | stop => exact id
  | step a b c k k' hnd hR _ ih => exact fun hI => ih (hs a b k hI hnd hR)

end transports

/-! ## The main loop -/

section loop

variable {T : ℕ → ℕ} {Φ Ω : Type}

/-- **The main loop of a call at level `l + 1`** (BM.9–BM.24): from `LoopRep ∧ ALoop`, the budget
and the room of every Layer-A run, `mainLoop DL.empty (seq (firstHalf DL.pull ltBi) postI)` realizes
one `LoopD` run of the concrete loop, at RAM cost `≤ Ko · (cc + cm) + K · lg.cost` (own work at
`Ko`, the sub-calls at the level IH's `K`) and use `≤ 2 · (cc + cm + lg.cost)`, and ends in
`LoopRep ∧ ALoop` of the final configuration. -/
theorem loop2_spec (DL : DLayer G s T) (PI : PhiI Φ) {LF : ℕ} {body : Stmt} {τf Mf : ℕ → ℕ}
    {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} {DCb : DCost} {K Ko Sl : ℕ} {Sb : ℕ → ℕ} {l : ℕ}
    (hIH : CallSpec DL PI.PhiR Inv FPC DCb Mf τf LF body K Sl Sb l)
    {ltBi : Stmt} {CL : ℕ} {LW LV : List String}
    (hLt : ∀ (d : Labels G s) (H : Hist G) (c0 : ℕ) (Bi : WLab G s),
      LtI realOps ltBi (fun st => LabAt st d H c0 ∧ WHolds st KBi "sp.bif" H (vc st) Bi ∧
          1 < st.cap ∧ st.w "n" = G.n)
        (fun v => ∃ h : v < G.n, d ⟨v, h⟩ < Bi) CL LW LV)
    (hLWd : ∀ a ∈ LW, a ∉ DL.dWR) (hLWp : ∀ a ∈ LW, a ∉ PI.pWR)
    (hLWs : ∀ a ∈ LW, a ∉ ["gN", "hp_n", "core.n", "core.s", "core.m"])
    (hDP : ∀ a ∈ DL.dWA, a ∉ PI.pWA) (hDPr : ∀ a ∈ DL.dWR, a ∉ PI.pWR)
    {postI : Stmt} {Kp : ℕ}
    (hpost : PostHalf DL PI LF body τf Mf Inv FPC DCb l (seq postI DL.empty) Kp Sl)
    (hMf : ∀ l, (dlOps G s).mergeM (Mf (l + 1)) (Mf l)) {DC : DCost} {subC : SubRelC G s Φ Ω}
    (hsimsub : SimSub G s (dlOps G s) τf Inv Mf l (BMSSPD G s (dlOps G s) FPC DCb T Mf τf l) subC)
    (hsubC : GoodSub G s τf Inv l subC) (hDC : DC.M (l + 1) = Mf (l + 1)) (hτ1 : 1 ≤ τf l)
    (hsubT : TotalSub G s Inv (BMSSPD G s (dlOps G s) FPC DCb T Mf τf l))
    (hKo : DL.K + CL + 71 + Kp + 1 ≤ Ko) (hKoD : DL.K + 1 ≤ Ko)
    (st : State ℝ≥0) (B : WLab G s) (S : Finset (Fin G.n)) (d0 d1 : Labels G s) (p : ℕ)
    (P0 : Fin p → Finset (Fin G.n)) (Q W : Finset (Fin G.n)) (B'0 : WLab G s) (f0 : ℕ)
    (L0 : LiveM G s) (c : LoopCfgD G s Φ p) (Ds : ℕ → DStrM G s) (H : Hist G) (c0 : ℕ)
    (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W)
    (hrep : LoopRep DL PI LF body τf Mf st (l + 1) B (τf (l + 1)) Ds H c0 c)
    (hA : ALoop (dlOps G s) Inv Mf l B S d0 d1 P0 B'0 f0 L0 c)
    (hSb : ∀ c', ALoop (dlOps G s) Inv Mf l B S d0 d1 P0 B'0 f0 L0 c' →
      ¬ LoopDoneD (τf (l + 1)) c' → ∀ ks Bi g1 Dc1 cp,
      pullC (dlOps G s) (T (l + 1)) c'.cs.g c'.cs.Dc = (ks, Bi, g1, Dc1, cp) →
      (BM.expand c'.cs.lit ks.toFinset Bi).card ≤ Sb l)
    (hbud : ∀ cs' φ' lg J cm cc, LoopD G s (dlOps G s) (T (l + 1))
      (BMSSPD G s (dlOps G s) FPC DCb T Mf τf l) B (τf (l + 1)) c.i c.cs c.φ cs' φ' lg J cm cc →
      st.cost + Ko * (cc + cm) + K * lg.cost + Sl ≤ c0 + st.cap)
    (hubud : ∀ cs' φ' lg J cm cc, LoopD G s (dlOps G s) (T (l + 1))
      (BMSSPD G s (dlOps G s) FPC DCb T Mf τf l) B (τf (l + 1)) c.i c.cs c.φ cs' φ' lg J cm cc →
      DL.use st + 2 * (cc + cm + lg.cost) ≤ DL.ucap) :
    Runs realOps (mainLoop DL.empty (seq (firstHalf DL.pull ltBi) postI)) st (fun r =>
      ∃ (cs' : CSt G s p) (φ' : Φ) (lg : Log G s Ω) (J : Finset (Fin G.m)) (cm cc : ℕ) (H' : Hist G),
      LoopD G s (dlOps G s) (T (l + 1)) (BMSSPD G s (dlOps G s) FPC DCb T Mf τf l)
        B (τf (l + 1)) c.i c.cs c.φ cs' φ' lg J cm cc ∧
      LoopRep DL PI LF body τf Mf r (l + 1) B (τf (l + 1)) Ds H' c0 ⟨c.i, cs', φ'⟩ ∧
      ALoop (dlOps G s) Inv Mf l B S d0 d1 P0 B'0 f0 L0 ⟨c.i, cs', φ'⟩ ∧
      HExt H (vc st) H' (vc r) ∧ LFrame st r G.n l ∧
      (∀ x : Fin G.n, x ∉ cs'.U → r.wa "sp.ptr" x = st.wa "sp.ptr" x) ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost + Ko * (cc + cm) + K * lg.cost ∧
      DL.use r ≤ DL.use st + 2 * (cc + cm + lg.cost)) := by
  classical
  -- 0. the initial emptiness bit
  refine runs_seq ((DL.empty_spec st H c.cs.g (Function.update Ds (l + 1) c.cs.Dc) (l + 1) hrep.D
    hrep.lvl hrep.stat.n).mono ?_)
  rintro r0 ⟨hD0, hem0, hU0, hwl0, hvl0, hc0l, hc0, hu0⟩
  simp only [Function.update_self] at hem0
  have hdA : ∀ a ∈ DL.dWA, a ∉ spArrs ∧ a ∉ PI.pWA := fun a ha => ⟨DL.dWA_ok a ha, hDP a ha⟩
  have hdR : ∀ a ∈ DL.dWR ++ ["sp.em"], a ∉ ["lvl", "n", "gN", "hp_n"] ∧ a ∉ PI.pWR := by
    intro a ha
    rcases List.mem_append.1 ha with h | h
    · exact ⟨fun h' => DL.dWR_ok a h (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
          rcases h' with rfl | rfl | rfl | rfl <;> simp [spRegs]), hDPr a h⟩
    · simp only [List.mem_singleton] at h; subst h
      exact ⟨by decide, fun h' => PI.pWR_ok _ h' (by simp [spRegs])⟩
  have hrep0 : LoopRep DL PI LF body τf Mf r0 (l + 1) B (τf (l + 1)) Ds H c0 c :=
    LoopRep.of_frame hrep hU0 hdA (fun a ha => DL.dVA_ok a ha) hdR hD0 hwl0 hvl0 hc0l
  have hcap0 : r0.cap = st.cap := hU0.cap
  have hvc0 : vc (G := G) r0 = vc st := funext fun v => by
    simp only [vc]; rw [(hU0.warr "vcnt" (fun h => DL.dWA_ok _ h (by simp [spArrs, labW]))).1]
  have hfr0 : LFrame st r0 G.n l := by
    have A : ∀ a ∈ spArrs, r0.wa a = st.wa a := fun a ha =>
      (hU0.warr a (fun h => DL.dWA_ok _ h ha)).1
    exact ⟨fun i _ _ => by rw [A "S" (by simp [spArrs, rowArrs])], by
        rw [A "S.len" (by simp [spArrs, lenArrs])],
      fun i _ _ => by rw [A "W" (by simp [spArrs, rowArrs])], by
        rw [A "W.len" (by simp [spArrs, lenArrs])],
      Above.of_unchanged hU0 (fun a ha h => DL.dWA_ok a h (by
        simp only [List.mem_append] at ha
        rcases ha with (h1 | h1) | h1 <;> simp [spArrs, h1])) (fun h => DL.dVA_ok _ h (by simp))
        hwl0 hvl0,
      fun a ha => A a (by revert a; decide)⟩
  -- the loop invariant
  set τl := τf (l + 1) with hτl
  let Rep : LoopCfgD G s Φ p → State ℝ≥0 → Prop := fun a r => ∃ H' : Hist G,
    HExt H (vc st) H' (vc r) ∧ LoopRep DL PI LF body τf Mf r (l + 1) B τl Ds H' c0 a ∧
    LFrame st r G.n l ∧ (∀ x : Fin G.n, x ∉ a.cs.U → r.wa "sp.ptr" x = st.wa "sp.ptr" x) ∧
    (r.w "sp.em" = 0 ↔ ¬ (a.cs.g.view a.cs.Dc).IsEmpty) ∧ st.cost ≤ r.cost ∧ r.cap = st.cap
  have hRep0 : Rep c r0 := ⟨H, by rw [hvc0]; exact HExt.refl _ _, hrep0, hfr0,
    fun x _ => by rw [(hU0.warr "sp.ptr" (fun h => DL.dWA_ok _ h (by simp [spArrs]))).1], hem0,
    hc0l, hcap0⟩
  have hstepI : ∀ a a' kw, ALoop (dlOps G s) Inv Mf l B S d0 d1 P0 B'0 f0 L0 a → ¬ LoopDoneD τl a →
      IterRelW (Ω := Ω) (dlOps G s) (T (l + 1)) (BMSSPD G s (dlOps G s) FPC DCb T Mf τf l) B τl Ko K
        a a' kw →
      ALoop (dlOps G s) Inv Mf l B S d0 d1 P0 B'0 f0 L0 a' ∧
        τl + 1 - a'.cs.U.card < τl + 1 - a.cs.U.card := by
    intro a a' kw hI hnd hW
    obtain ⟨k, hD⟩ := hW.toD
    obtain ⟨hI', hlt, -, -⟩ := iterD_step (T := T (l + 1)) (DC := DC) hpre hfp hMf hsimsub hsubC hDC
      hτ1 a a' k hI hD
    have hcard : a.cs.U.card ≤ τl := not_lt.mp (not_or.mp hnd).1
    exact ⟨hI', by omega⟩
  -- the abstract loop: configurations with the use spent so far
  let RU : LoopCfgD G s Φ p × ℕ → LoopCfgD G s Φ p × ℕ → ℕ → Prop :=
    IterRelU (Ω := Ω) (dlOps G s) (T (l + 1)) (BMSSPD G s (dlOps G s) FPC DCb T Mf τf l) B τl Ko K
  let doneU : LoopCfgD G s Φ p × ℕ → Prop := fun a => LoopDoneD τl a.1
  let AI : LoopCfgD G s Φ p × ℕ → Prop := fun a => ALoop (dlOps G s) Inv Mf l B S d0 d1 P0 B'0 f0 L0 a.1
  have hstepA : ∀ a a' kw, AI a → ¬ doneU a → RU a a' kw →
      AI a' ∧ τl + 1 - a'.1.cs.U.card < τl + 1 - a.1.cs.U.card :=
    fun a a' kw hI hnd hR => hstepI a.1 a'.1 kw hI hnd hR.toW
  have htotU : ∀ a, AI a → ¬ doneU a → ∃ a' kw, RU a a' kw := by
    intro a hI hnd
    obtain ⟨c', k, hD⟩ := iterD_total (T := T (l + 1)) (τ := τf) (Mf := Mf) hpre hfp hsubT a.1 hI hnd
    obtain ⟨u', kw, hU⟩ := hD.toU (Ko := Ko) (K := K) a.2
    exact ⟨(c', u'), kw, hU⟩
  have hLtot : Total AI (RelLoop RU doneU) :=
    RelLoop.total AI (fun a => τl + 1 - a.1.cs.U.card) hstepA htotU
  let IU : LoopCfgD G s Φ p × ℕ → Prop := fun a => AI a ∧
    ∀ a'' kw, RelLoop RU doneU a a'' kw → DL.use st + a''.2 ≤ DL.ucap
  let RepU : LoopCfgD G s Φ p × ℕ → State ℝ≥0 → Prop := fun a r =>
    Rep a.1 r ∧ DL.use r ≤ DL.use st + a.2
  -- the room of one more iteration
  have hroom : ∀ a a' kw, IU a → ¬ doneU a → RU a a' kw → DL.use st + a'.2 ≤ DL.ucap := by
    intro a a' kw hI hnd hR
    obtain ⟨hA', -⟩ := hstepA a a' kw hI.1 hnd hR
    obtain ⟨a'', k'', hL⟩ := hLtot a' hA'
    exact le_trans (Nat.add_le_add_left (RelLoop.le_snd_U hL) _)
      (hI.2 a'' (kw + k'') (.step a a' a'' kw k'' hnd hR hL))
  have huc : ∀ r : State ℝ≥0, DL.use (r.charge 1) = DL.use r := fun r =>
    DL.use_frame r (r.charge 1) [] [] [] [] (Unchanged.charge r 1 [] [] [] []) (by simp)
  refine (loopTight (ops := realOps) (Rep := RepU) (Inv := IU) (e := loopTest)
    (c := seq (seq (firstHalf DL.pull ltBi) postI) DL.empty) (R := RU) (K := 1)
    (Lim := c0 + st.cap - Sl) doneU (fun a => τl + 1 - a.1.cs.U.card) le_rfl
    ?_ ?_ ?_ ?_ (fun a hI hnd => htotU a hI.1 hnd) (c, 0) r0 ⟨hA, ?_⟩
    ⟨hRep0, by rw [hu0]; exact Nat.le_add_right _ _⟩ ?_).mono ?_
  · -- the test
    rintro a r - ⟨⟨H', -, hrepr, -, -, hemr, -, -⟩, -⟩
    exact loopTest_eval hrepr hemr
  · -- the charge of the test
    rintro a r ⟨⟨H', hHE, hrepr, hfrr, hptrr, hemr, hcr, hcapr⟩, hur⟩
    exact ⟨⟨H', hHE, hrepr.charge 1, ⟨hfrr.S, hfrr.Slen, hfrr.W, hfrr.Wlen,
      ⟨hfrr.above.rows, hfrr.above.lens, hfrr.above.slots, hfrr.above.wlen, hfrr.above.vlen⟩,
      hfrr.stArr⟩,
      hptrr, hemr, by simp only [State.charge_cost]; omega, hcapr⟩, by rw [huc]; exact hur⟩
  · -- one iteration
    rintro a r hI hnd ⟨⟨H1, hHE1, hrep1, hfr1, hptr1, hem1, hcr1, hcap1⟩, hur⟩ hbudI
    have hne : ¬ (a.1.cs.g.view a.1.cs.Dc).IsEmpty := (not_or.mp hnd).2
    have hcard : a.1.cs.U.card ≤ τl := not_lt.mp (not_or.mp hnd).1
    have hfr1' : LFrame st (r.charge 1) G.n l := ⟨hfr1.S, hfr1.Slen, hfr1.W, hfr1.Wlen,
      ⟨hfr1.above.rows, hfr1.above.lens, hfr1.above.slots, hfr1.above.wlen, hfr1.above.vlen⟩,
      hfr1.stArr⟩
    refine Runs.seq_assoc ?_
    refine runs_seq ((Runs.cap_procs (firstHalf_spec DL PI hIH hLt hLWd hLWp hLWs hDP hDPr hpre hfp
      hMf hsimsub hsubC hDC (hrep1.charge 1) hI.1 hnd hfr1' hptr1 (hSb a.1 hI.1 hnd) (Ko := Ko)
      (by omega) ?_ hsubT ?_)).mono ?_)
    · intro c' kw hW
      obtain ⟨u', hU⟩ := hW.toU_cost a.2
      have := hbudI (c', u') kw hU
      simp only [State.charge_cost, State.charge_cap]
      rw [hcap1]; omega
    · intro c' ku hW
      obtain ⟨kw, hU⟩ := hW.toU_use (Ko := Ko) (K := K) a.2
      have := hroom a (c', a.2 + ku) kw hI hnd hU
      rw [huc]; omega
    rintro r8 ⟨⟨ks, Bi, g1, Dc1, cp, B'i, Ui, Dci, d1', φ1, g2, lg, H', hpull, hsubD, hHE8, hPC, hc8l,
      hc8, hu8⟩, hcap8, -⟩
    simp only [State.charge_cost, State.charge_cap] at hc8 hc8l hcap8
    rw [huc] at hu8
    have hsplit := iterCost_split (T (l + 1)) B a.1.cs ks cp Bi Ui Dc1 Dci d1' g2
    -- the arithmetic of one iteration
    have arith : ∀ rest : ℕ, (DL.K + CL + 71) * (1 + cp + ks.toFinset.card +
        ∑ j ∈ pulledGroups a.1.cs.lit ks.toFinset, (a.1.cs.P j).card) + Kp * (rest + 1) + 1 ≤
        Ko * (1 + cp + (ks.toFinset.card + ∑ j ∈ pulledGroups a.1.cs.lit ks.toFinset,
          (a.1.cs.P j).card) + rest) := by
      intro rest
      set pre := 1 + cp + (ks.toFinset.card + ∑ j ∈ pulledGroups a.1.cs.lit ks.toFinset,
        (a.1.cs.P j).card) with hpre'
      have e1 : (DL.K + CL + 71) * (1 + cp + ks.toFinset.card +
          ∑ j ∈ pulledGroups a.1.cs.lit ks.toFinset, (a.1.cs.P j).card) = (DL.K + CL + 71) * pre := by
        rw [hpre']; ring
      have hp1 : 1 ≤ pre := by rw [hpre']; omega
      have i1 : (DL.K + CL + 71 + Kp + 1) * pre ≤ Ko * pre := Nat.mul_le_mul_right _ hKo
      have e2 : (DL.K + CL + 71 + Kp + 1) * pre = (DL.K + CL + 71) * pre + Kp * pre + pre := by ring
      have i2 : Kp ≤ Kp * pre := Nat.le_mul_of_pos_right _ hp1
      have i3 : Kp * rest ≤ Ko * rest := Nat.mul_le_mul_right _ (by omega)
      have e3 : Ko * (pre + rest) = Ko * pre + Ko * rest := by ring
      have e4 : Kp * (rest + 1) = Kp * rest + Kp := by ring
      rw [e1, e3, e4]; omega
    -- the iteration with its use, for every completion of the second half
    have hWU : ∀ lUi L' piv' lres, lUi.Nodup → lUi.toFinset = Ui → L'.Nodup →
        (∀ e, e ∈ L' ↔ G.src e ∈ Ui ∧ Bi ≤ ext (d1' (G.src e)) e ∧ ext (d1' (G.src e)) e < B) →
        Reselect a.1.cs.lit Ui (foldA (T (l + 1)) B Bi Dc1 Dci d1' g2 lUi L').d piv' →
        lres.Nodup → lres.toFinset = reselected a.1.cs.lit Ui piv' →
        RU a (⟨a.1.i + 1, nextD (dlOps G s) (T (l + 1)) B a.1.cs Bi B'i Ui Dc1 Dci d1' g2 lUi L'
            piv' lres, φ1⟩, a.2 + (2 * (iterCostD (dlOps G s) (T (l + 1)) B a.1.cs ks.toFinset cp Bi
            Ui Dc1 Dci d1' g2 lUi L' lres + ((dlOps G s).merge (T (l + 1)) Dc1 Dci).2) + 2 * lg.cost))
          (Ko * (iterCostD (dlOps G s) (T (l + 1)) B a.1.cs ks.toFinset cp Bi Ui Dc1 Dci d1' g2 lUi L'
            lres + ((dlOps G s).merge (T (l + 1)) Dc1 Dci).2) + K * lg.cost) :=
      fun lUi L' piv' lres h1 h2 h3 h4 h5 h6 h7 =>
        ⟨ks, Bi, g1, Dc1, cp, B'i, Ui, Dci, d1', g2, lUi, L', piv', lres, lg, φ1, hcard, hne, hpull,
          hsubD, h1, h2, h3, h4, h5, h6, h7, rfl, rfl, rfl⟩
    refine ((Runs.cap_procs (hpost B S d0 d1 p P0 Q W B'0 f0 L0 a.1 ks Bi g1 Dc1 cp B'i Ui Dci d1'
      φ1 g2 lg st r8 τl Ds H' c0 hpre hfp hI.1 hne hpull hsubD hPC ?_ ?_)).mono ?_)
    · intro lUi L' piv' lres h1 h2 h3 h4 h5 h6 h7
      have hb := hbudI _ _ (hWU lUi L' piv' lres h1 h2 h3 h4 h5 h6 h7)
      have hs := hsplit lUi L' lres
      have ha := arith (restCostA (T (l + 1)) B a.1.cs Bi Ui Dc1 Dci d1' g2 lUi L' lres)
      rw [hcap8, hcap1]
      rw [hs] at hb
      omega
    · intro lUi L' piv' lres h1 h2 h3 h4 h5 h6 h7
      have hb := hroom a _ _ hI hnd (hWU lUi L' piv' lres h1 h2 h3 h4 h5 h6 h7)
      have hs := hsplit lUi L' lres
      rw [hs] at hb
      omega
    rintro r9 ⟨⟨lUi, L', piv', lres, H'', h1, h2, h3, h4, h5, h6, h7, hrep9, hem9, hHE9, hfr9, hptr9,
      hc9l, hc9, hu9⟩, hcap9, -⟩
    have hs := hsplit lUi L' lres
    have ha := arith (restCostA (T (l + 1)) B a.1.cs Bi Ui Dc1 Dci d1' g2 lUi L' lres)
    refine ⟨_, _, hWU lUi L' piv' lres h1 h2 h3 h4 h5 h6 h7,
      ⟨⟨H'', (hHE1.trans hHE8).trans hHE9, hrep9, hfr9, fun x hx => hptr9 x hx, hem9, by omega,
        by rw [hcap9, hcap8, hcap1]⟩, ?_⟩, ?_⟩
    · show DL.use r9 ≤ DL.use st + (a.2 + (2 * (iterCostD (dlOps G s) (T (l + 1)) B a.1.cs
        ks.toFinset cp Bi Ui Dc1 Dci d1' g2 lUi L' lres + ((dlOps G s).merge (T (l + 1)) Dc1 Dci).2)
        + 2 * lg.cost))
      rw [hs]; omega
    · rw [hs]; omega
  · -- the invariant is kept
    intro a a' kw hI hnd hR
    obtain ⟨hA', hμ⟩ := hstepA a a' kw hI.1 hnd hR
    exact ⟨⟨hA', fun a'' k'' hL => hI.2 a'' (kw + k'') (.step a a' a'' kw k'' hnd hR hL)⟩, hμ⟩
  · -- the room of every loop run
    intro a'' kw hRL
    obtain ⟨lg, J, cm, cc, hLD, -, hu⟩ := loopDU_of_relLoop hRL
    have := hubud a''.1.cs a''.1.φ lg J cm cc hLD
    simp only at hu
    omega
  · -- the budget of every loop run
    intro a'' kw hRL
    obtain ⟨lg, J, cm, cc, hLD, hkw, -⟩ := loopDU_of_relLoop hRL
    have := hbud a''.1.cs a''.1.φ lg J cm cc hLD
    omega
  · -- after the loop
    rintro r ⟨a', kw, hRL, ⟨⟨H', hHE, hrepr, hfrr, hptrr, -, hcr, -⟩, hur⟩, hcost⟩
    obtain ⟨lg, J, cm, cc, hLD, hkw, hu⟩ := loopDU_of_relLoop hRL
    have hIa' := RelLoop.inv (Inv := AI) (fun a a' kw hI hnd hR => (hstepA a a' kw hI hnd hR).1)
      hRL hA
    simp only at hu
    exact ⟨a'.1.cs, a'.1.φ, lg, J, cm, cc, H', hLD, hrepr.congr_i c.i, hIa'.congr_i c.i, hHE, hfrr,
      hptrr, hcr, by omega, by omega⟩

end loop

end Frontier.CHD.RamSpine
