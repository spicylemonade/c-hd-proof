import Frontier.CHD.SpineLoop

/-!
# SpineA — Layer-A facts on one iteration of the concrete loop (agent-08, B-L4, NON-GATE)

For `RefinesB.loopVar` over `SpineBridgeD.IterRelD`: from the Layer-A loop invariant `ALoop`
(agent-01's `stepD_inv` hypotheses) every non-final configuration has a successor (`iterD_total`),
and every successor satisfies `ALoop` again, with a strictly larger `U` and a positive cost
(`iterD_step`).  Both are agent-01's `loopD_total` argument, one step at a time.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamSpine

open Frontier Frontier.CHD Frontier.CHD.BM

variable {G : Graph} {s : Fin G.n} {ops : DOps G s} {T : ℕ} {DC : DCost} {Φ Ω : Type}
  {B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {p : ℕ}
  {P0 : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {B'0 : WLab G s}

/-- **One iteration exists** from every non-final configuration satisfying `ALoop`. -/
theorem iterD_total (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W)
    {τ : ℕ → ℕ} {Inv : Φ → Prop} {Mf : ℕ → ℕ}
    {subD : SubRelD G s Φ Ω} {l : ℕ} (hsubT : TotalSub G s Inv subD)
    {f0 : ℕ} {L0 : LiveM G s} {τl : ℕ} (c : LoopCfgD G s Φ p)
    (hA : ALoop ops Inv Mf l B S d0 d1 P0 B'0 f0 L0 c) (hnd : ¬ LoopDoneD τl c) :
    ∃ c' k, IterRelD (Ω := Ω) ops T subD B τl c c' k := by
  classical
  obtain ⟨hcard', hne⟩ := not_or.mp hnd
  have hcard : c.cs.U.card ≤ τl := not_lt.mp hcard'
  rcases hp : pullC ops T c.cs.g c.cs.Dc with ⟨ks, Bi, g1, Dc1, cp⟩
  obtain ⟨hsp, hlowdis, hBle, hK1, habove, -⟩ :=
    childPre (T := T) hpre hfp hA.linv hA.sinv hA.kinj hne hp
  obtain ⟨⟨B'i, Ui, Dci, d1'⟩, φ1, g2, lg, hsubD⟩ :=
    hsubT c.cs.B' Bi (BM.expand c.cs.lit ks.toFinset Bi) c.cs.d c.φ g1 hsp hA.inv hlowdis hBle hK1 habove
  obtain ⟨lUi, hlUnd, hlU⟩ : ∃ lU : List (Fin G.n), lU.Nodup ∧ lU.toFinset = Ui :=
    ⟨Ui.toList, Finset.nodup_toList _, Finset.toList_toFinset _⟩
  obtain ⟨L', hnd', hmem⟩ : ∃ L : List (Fin G.m), L.Nodup ∧ ∀ e, e ∈ L ↔
      G.src e ∈ Ui ∧ Bi ≤ ext (d1' (G.src e)) e ∧ ext (d1' (G.src e)) e < B :=
    ⟨(Finset.univ.filter fun e => G.src e ∈ Ui ∧ Bi ≤ ext (d1' (G.src e)) e ∧
        ext (d1' (G.src e)) e < B).toList, Finset.nodup_toList _, by intro e; simp⟩
  obtain ⟨piv', hres⟩ := exists_reselect c.cs.lit Ui (L'.foldl (relaxInsCc ops T B (some Bi))
    ⟨d1', (delC g2 lUi).1, (ops.merge T Dc1 Dci).1, 0⟩).d
  obtain ⟨lres, hlresnd, hlres⟩ : ∃ lr : List (Fin G.n), lr.Nodup ∧
      lr.toFinset = reselected c.cs.lit Ui piv' :=
    ⟨_, Finset.nodup_toList _, Finset.toList_toFinset _⟩
  exact ⟨_, _, ks, Bi, g1, Dc1, cp, B'i, Ui, Dci, d1', g2, lUi, L', piv', lres, lg, φ1, hcard, hne,
    hp, hsubD, hlUnd, hlU, hnd', hmem, hres, hlresnd, hlres, rfl, rfl⟩

/-- **One iteration keeps the Layer-A invariant**, strictly grows `U` and costs at least `1`. -/
theorem iterD_step (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W)
    {τ : ℕ → ℕ} {Inv : Φ → Prop} {Mf : ℕ → ℕ} (hMf : ∀ l, ops.mergeM (Mf (l + 1)) (Mf l))
    {subD : SubRelD G s Φ Ω} {subC : SubRelC G s Φ Ω} {l : ℕ}
    (hsimsub : SimSub G s ops τ Inv Mf l subD subC) (hsubC : GoodSub G s τ Inv l subC)
    (hDC : DC.M (l + 1) = Mf (l + 1)) (hτ1 : 1 ≤ τ l)
    {f0 : ℕ} {L0 : LiveM G s} {τl : ℕ} (c c' : LoopCfgD G s Φ p) (k : ℕ)
    (hA : ALoop ops Inv Mf l B S d0 d1 P0 B'0 f0 L0 c) (hR : IterRelD (Ω := Ω) ops T subD B τl c c' k) :
    ALoop ops Inv Mf l B S d0 d1 P0 B'0 f0 L0 c' ∧ c.cs.U.card < c'.cs.U.card ∧ 1 ≤ k ∧
      c.cs.U ⊆ c'.cs.U := by
  obtain ⟨ks, Bi, g1, Dc1, cp, B'i, Ui, Dci, d1', g2, lUi, L', piv', lres, lg, φ1, hcard, hne, hp,
    hsubD, hlUnd, hlU, hnd', hmem, hres, hlresnd, hlres, rfl, rfl⟩ := hR
  obtain ⟨-, -, -, -, -, -, -, hnext', hI1, hSn', hMn', hKn', hCCn', hTn', hUine, hUi_disj, -, -⟩ :=
    stepD_inv (T := T) (DC := DC) (g0 := ⟨L0, f0⟩) hpre hfp hMf hsimsub hsubC hDC hA.linv hA.inv
      hA.sinv hA.M hA.kinj hA.chg hA.touch hne hp hsubD hlU hnd' hmem hres hlres
  refine ⟨⟨hnext', hI1, hSn', hMn', hKn', hCCn', hTn'⟩, ?_, ?_, ?_⟩
  · show c.cs.U.card < (c.cs.U ∪ Ui).card
    rw [Finset.card_union_of_disjoint (disjoint_comm.mp hUi_disj)]
    have := (hUine hτ1).card_pos
    omega
  · simp only [iterCostD]; omega
  · exact Finset.subset_union_left

/-- **Continuation totality**: once the pull and the sub-call's outcome are fixed, the iteration
has an outcome; its cost covers the pull, the expansion term and the sub-call, and the returned
set is disjoint from `U`. -/
theorem iterD_of_sub (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W)
    {τ : ℕ → ℕ} {Inv : Φ → Prop} {Mf : ℕ → ℕ} (hMf : ∀ l, ops.mergeM (Mf (l + 1)) (Mf l))
    {subD : SubRelD G s Φ Ω} {subC : SubRelC G s Φ Ω} {l : ℕ}
    (hsimsub : SimSub G s ops τ Inv Mf l subD subC) (hsubC : GoodSub G s τ Inv l subC)
    (hDC : DC.M (l + 1) = Mf (l + 1))
    {f0 : ℕ} {L0 : LiveM G s} {τl : ℕ} (c : LoopCfgD G s Φ p)
    (hA : ALoop ops Inv Mf l B S d0 d1 P0 B'0 f0 L0 c) (hnd : ¬ LoopDoneD τl c)
    {ks : List (Fin G.n)} {Bi : WLab G s} {g1 : DGl G s} {Dc1 : DStrM G s} {cp : ℕ}
    (hp : pullC ops T c.cs.g c.cs.Dc = (ks, Bi, g1, Dc1, cp))
    {B'i : WLab G s} {Ui : Finset (Fin G.n)} {Dci : DStrM G s} {d1' : Labels G s} {φ1 : Φ}
    {g2 : DGl G s} {lg : Log G s Ω}
    (hsubD : subD c.cs.B' Bi (BM.expand c.cs.lit ks.toFinset Bi) c.cs.d c.φ g1 (B'i, Ui, Dci, d1') φ1
      g2 lg) :
    ∃ c' k, IterRelD (Ω := Ω) ops T subD B τl c c' k ∧
      1 + cp + (ks.toFinset.card + ∑ j ∈ pulledGroups c.cs.lit ks.toFinset, (c.cs.P j).card) +
        lg.cost ≤ k ∧ Disjoint Ui c.cs.U := by
  classical
  obtain ⟨hcard', hne⟩ := not_or.mp hnd
  have hcard : c.cs.U.card ≤ τl := not_lt.mp hcard'
  obtain ⟨lUi, hlUnd, hlU⟩ : ∃ lU : List (Fin G.n), lU.Nodup ∧ lU.toFinset = Ui :=
    ⟨Ui.toList, Finset.nodup_toList _, Finset.toList_toFinset _⟩
  obtain ⟨L', hnd', hmem⟩ : ∃ L : List (Fin G.m), L.Nodup ∧ ∀ e, e ∈ L ↔
      G.src e ∈ Ui ∧ Bi ≤ ext (d1' (G.src e)) e ∧ ext (d1' (G.src e)) e < B :=
    ⟨(Finset.univ.filter fun e => G.src e ∈ Ui ∧ Bi ≤ ext (d1' (G.src e)) e ∧
        ext (d1' (G.src e)) e < B).toList, Finset.nodup_toList _, by intro e; simp⟩
  obtain ⟨piv', hres⟩ := exists_reselect c.cs.lit Ui (L'.foldl (relaxInsCc ops T B (some Bi))
    ⟨d1', (delC g2 lUi).1, (ops.merge T Dc1 Dci).1, 0⟩).d
  obtain ⟨lres, hlresnd, hlres⟩ : ∃ lr : List (Fin G.n), lr.Nodup ∧
      lr.toFinset = reselected c.cs.lit Ui piv' :=
    ⟨_, Finset.nodup_toList _, Finset.toList_toFinset _⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hUi_disj, -, -⟩ :=
    stepD_inv (T := T) (DC := DC) (g0 := ⟨L0, f0⟩) hpre hfp hMf hsimsub hsubC hDC hA.linv hA.inv
      hA.sinv hA.M hA.kinj hA.chg hA.touch hne hp hsubD hlU hnd' hmem hres hlres
  refine ⟨_, _, ⟨ks, Bi, g1, Dc1, cp, B'i, Ui, Dci, d1', g2, lUi, L', piv', lres, lg, φ1, hcard, hne,
    hp, hsubD, hlUnd, hlU, hnd', hmem, hres, hlresnd, hlres, rfl, rfl⟩, ?_, hUi_disj⟩
  simp only [iterCostD]; omega

end Frontier.CHD.RamSpine
