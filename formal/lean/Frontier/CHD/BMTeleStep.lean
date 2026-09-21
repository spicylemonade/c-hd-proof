import Frontier.CHD.BMTele

/-!
# Frontier.CHD.BMTeleStep — one loop iteration over `DLazy`, telescoped (owner: agent-01; NON-GATE)

`stepD_tele`: the facts of `BMLazy.stepD_inv` for `dlOps`, plus
* the block-count potential of the next state: `psi' ≤ max(psi, 2M) + 2·(E(child) + |L'| + |lres|)`;
* the iteration's actual cost (pull, expansion scan, merge, FIX-STALE deletion, window scan,
  re-selection insertions, and the sub-call's log) plus the family potential at the next state is at
  most the literal amortized cost `iterCost DC + DC.merge + (literal sub-log cost)` plus the family
  potential now, for every family of other structures `os`.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

section stepT

variable {Φ Ω : Type} {T : ℕ}
variable {B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {p : ℕ}
  {P0 : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {B'0 : WLab G s}

/-- **One concrete iteration, telescoped**: the facts of `stepD_inv` (for `DLazy`), the block-count
potential of the next state, and the iteration's actual cost (including the sub-call and the merge)
plus the family potential at the next state is at most the literal amortized cost plus the family
potential at the current state. -/
theorem stepD_tele (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W)
    {τ : ℕ → ℕ} {Inv : Φ → Prop} {Mf Emax : ℕ → ℕ} (hMpos : ∀ l, 1 ≤ Mf l)
    (h3M : ∀ l, 3 * Mf l ≤ Mf (l + 1))
    {subD : SubRelD G s Φ Ω} {subC : SubRelC G s Φ Ω} {l : ℕ}
    (hsimsubT : SimSubT G s τ Inv Mf Emax l subD subC) (hsubC : GoodSub G s τ Inv l subC)
    {DC : DCost} (hDC : DC.M (l + 1) = Mf (l + 1)) {P : ℕ}
    (hIns : ∀ D : DStrM G s, D.M = Mf (l + 1) → DL.psi D ≤ P → insCharge D ≤ DC.ins (l + 1))
    (hpullC : ∀ k, 735 * k + 950 ≤ DC.pull (l + 1) k) (hdelC : ∀ k, 5 * k + 1 ≤ DC.del (l + 1) k)
    (hmergeC : ∀ k, 14 ≤ DC.merge (l + 1) k)
    {g0 : DGl G s} {cs : CSt G s p} {φ φ1 : Φ} {ks : List (Fin G.n)} {Bi : WLab G s} {g1 : DGl G s}
    {Dc1 : DStrM G s} {cp : ℕ} {B'i : WLab G s} {Ui : Finset (Fin G.n)} {Dci : DStrM G s}
    {d1' : Labels G s} {g2 : DGl G s} {lUi : List (Fin G.n)} {L' : List (Fin G.m)}
    {piv' : Fin p → Fin G.n} {lres : List (Fin G.n)} {lg : Log G s Ω}
    (h : LInv G s B S d0 d1 P0 B'0 cs.lit) (hI : Inv φ)
    (hS : SInv G s (dlOps G s) B g0.fresh cs.g cs.Dc)
    (hMc : cs.Dc.M = Mf (l + 1)) (hK : DB.KeyInj cs.g.L (kof G s))
    (hCC : CallChange g0.fresh B g0.L cs.g.L)
    (hT : ∀ y, cs.g.L y ≠ g0.L y → y ∈ cs.U ∨ ∃ a, cs.g.view cs.Dc y = some a ∧ a ≤ d0 y)
    (hne : ¬ (cs.g.view cs.Dc).IsEmpty)
    (hpull : pullC (dlOps G s) T cs.g cs.Dc = (ks, Bi, g1, Dc1, cp))
    (hsubD : subD cs.B' Bi (expand cs.lit ks.toFinset Bi) cs.d φ g1 (B'i, Ui, Dci, d1') φ1 g2 lg)
    (hlUnd : lUi.Nodup) (hlU : lUi.toFinset = Ui) (hnd : L'.Nodup)
    (hmem : ∀ e, e ∈ L' ↔ G.src e ∈ Ui ∧ Bi ≤ ext (d1' (G.src e)) e ∧ ext (d1' (G.src e)) e < B)
    (hres : Reselect cs.lit Ui (L'.foldl (relaxInsCc (dlOps G s) T B (some Bi))
      ⟨d1', (delC g2 lUi).1, ((dlOps G s).merge T Dc1 Dci).1, 0⟩).d piv')
    (hlresnd : lres.Nodup) (hlres : lres.toFinset = reselected cs.lit Ui piv')
    (hFc : Fits Emax lg)
    (hP1 : DL.psi cs.Dc + 2 * (entCount Dci + L'.length + lres.length) ≤ P)
    (hP2 : 2 * Mf (l + 1) + 2 * (entCount Dci + L'.length + lres.length) ≤ P) :
    ∃ lgi, subC cs.lit.B' Bi (expand cs.lit ks.toFinset Bi) cs.lit.d φ
        (B'i, Ui, g2.view Dci, d1') φ1 lgi ∧ Log.strip lgi = Log.strip lg ∧
      PullSpec cs.lit.D B ks.toFinset Bi (g1.view Dc1) ∧ ks.toFinset.card ≤ DC.M (l + 1) ∧
      Reselect cs.lit Ui (L'.foldl (relaxIns G s B (some Bi))
        (d1', ((g1.view Dc1).merge (g2.view Dci)).deleteSet Ui)).1 piv' ∧
      (nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).lit = nextState B cs.lit Bi B'i Ui (g1.view Dc1) (g2.view Dci) d1' L' piv' ∧
      LInv G s B S d0 d1 P0 B'0 (nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).lit ∧ Inv φ1 ∧
      SInv G s (dlOps G s) B g0.fresh (nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).g (nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).Dc ∧ (nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).Dc.M = Mf (l + 1) ∧
      DB.KeyInj (nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).g.L (kof G s) ∧ CallChange g0.fresh B g0.L (nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).g.L ∧
      (∀ y, (nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).g.L y ≠ g0.L y → y ∈ (nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).U ∨ ∃ a, (nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).g.view (nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).Dc y = some a ∧ a ≤ d0 y) ∧
      (1 ≤ τ l → Ui.Nonempty) ∧ Disjoint Ui cs.U ∧
      (ks.toFinset.card < DC.M (l + 1) → (g1.view Dc1).IsEmpty ∧ Bi = B) ∧
      (DL.psi (nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).Dc ≤ DL.psi cs.Dc + 2 * (entCount Dci + L'.length + lres.length) ∨
        DL.psi (nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).Dc ≤ 2 * Mf (l + 1) + 2 * (entCount Dci + L'.length + lres.length)) ∧
      (∀ os : List (DB.Block (Fin G.n) (WLab G s)), (∀ x ∈ DB.allEnts os, x.id < g0.fresh) →
        ((DB.allEnts os).map (·.id)).Nodup →
        iterCostD (dlOps G s) T B cs ks.toFinset cp Bi Ui Dc1 Dci d1' g2 lUi L' lres
            + ((dlOps G s).merge T Dc1 Dci).2 + lg.cost + potG (nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).g (nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).Dc + othP (nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).g.L os ≤
          iterCost DC (l + 1) cs.lit ks.toFinset Ui L'.length
            + DC.merge (l + 1) (keyCount G s (g2.view Dci)) + lgi.cost + potG cs.g cs.Dc
            + othP cs.g.L os) := by
    -- (1) pull
    obtain ⟨hPS, hS0M, hS1, hK1, hfr1, hL1, hlive1, hsep1, habove, hM1⟩ := pull_sim hS hK hpull
    have hPS' : PullSpec cs.lit.D B ks.toFinset Bi (g1.view Dc1) := hPS
    -- (2) the literal sub-call precondition
    have hsp : CallPre Bi (expand cs.lit ks.toFinset Bi) cs.lit.d := step_pre hpre hfp h hPS'
    have hlowdis : ∀ x ∈ expand cs.lit ks.toFinset Bi, cs.lit.B' ≤ dis (s := s) x :=
      fun x hx => (Si_facts h hPS' hx).1.2.2
    have hSne : ks.toFinset.Nonempty := by
      apply hPS'.nonempty
      have hne' : ¬ cs.lit.D.IsEmpty := hne
      simp only [DS.IsEmpty, not_forall] at hne'
      exact hne'
    obtain ⟨x0, hx0⟩ := hSne
    have hx0S : x0 ∈ expand cs.lit ks.toFinset Bi := mem_expand.mpr (Or.inl hx0)
    have hBlt : cs.lit.B' < Bi := by
      obtain ⟨⟨-, -, hB⟩, hlt⟩ := Si_facts h hPS' hx0S
      exact lt_of_le_of_lt (hB.trans (h.walk.sound x0)) hlt
    -- (3) the concrete sub-call simulates a literal one
    obtain ⟨lgi, hsubCi, hstripi, hDP, hcostI⟩ := hsimsubT cs.B' Bi (expand cs.lit ks.toFinset Bi)
      cs.d φ g1 (B'i, Ui, Dci, d1') φ1 g2 lg hsp hI hlowdis hBlt.le hK1 habove ⟨x0, hx0S⟩ hsubD
    have hsubCi' : subC cs.lit.B' Bi (expand cs.lit ks.toFinset Bi) cs.lit.d φ
        (B'i, Ui, g2.view Dci, d1') φ1 lgi := hsubCi
    obtain ⟨hpost, hI1, -⟩ := hsubC _ _ _ _ _ _ _ _ hsp hI hlowdis hBlt.le hsubCi'
    -- (4) merge + FIX-STALE
    have hUiU : ∀ y, y ∈ lUi ↔ y ∈ Ui := by
      intro y; rw [← hlU, List.mem_toFinset]
    have htouch : ∀ y, g2.L y ≠ g1.L y → y ∉ lUi →
        ∃ a, g2.view Dci y = some a ∧ ∀ b, g1.view Dc1 y = some b → a ≤ b := by
      intro y hy hyU
      have hyUi : y ∉ Ui := fun h' => hyU ((hUiU y).mpr h')
      rcases hDP.touch y hy with h' | ⟨a, ha, hale⟩
      · exact absurd h' hyUi
      · refine ⟨a, ha, fun b hb => hale.trans ?_⟩
        obtain ⟨hb', -⟩ := pull_rest_some hPS' hb
        exact h.storedGe y b hb'
    have hMM : (dlOps G s).mergeM Dc1.M Dci.M := trivial
    obtain ⟨hvm, hSm, hKm, hfrm, hLm⟩ := merge_sim (T := T) hS1 hlive1 hsep1 hPS.bound hDP.sinv
      hDP.kinj hDP.chg hMM lUi htouch
    rw [hlU] at hvm
    -- (5) the window scan
    have hw1 : WalkInv d1' := hpost.walk
    obtain ⟨fd, fv, hSf, hKf, hmf, hCCf, hTf⟩ := fold_sim (T := T) (some Bi) L'
      ⟨d1', (delC g2 lUi).1, ((dlOps G s).merge T Dc1 Dci).1, 0⟩ hSm hKm hw1
    have hlit0 : ((⟨d1', (delC g2 lUi).1, ((dlOps G s).merge T Dc1 Dci).1, 0⟩ : RSt G s).d,
        (⟨d1', (delC g2 lUi).1, ((dlOps G s).merge T Dc1 Dci).1, 0⟩ : RSt G s).g.view
          (⟨d1', (delC g2 lUi).1, ((dlOps G s).merge T Dc1 Dci).1, 0⟩ : RSt G s).Dc) =
        (d1', ((g1.view Dc1).merge (g2.view Dci)).deleteSet Ui) := by
      show (d1', (delC g2 lUi).1.view ((dlOps G s).merge T Dc1 Dci).1) = _
      rw [hvm]
    rw [hlit0] at fd fv
    set fst := L'.foldl (relaxInsCc (dlOps G s) T B (some Bi)) ⟨d1', (delC g2 lUi).1, ((dlOps G s).merge T Dc1 Dci).1, 0⟩
      with hfst
    set D0 := ((g1.view Dc1).merge (g2.view Dci)).deleteSet Ui with hD0
    have hres' : Reselect cs.lit Ui (L'.foldl (relaxIns G s B (some Bi)) (d1', D0)).1 piv' := by
      rw [← fd]; exact hres
    -- (6) the literal loop invariant for the next state
    have hmem' : ∀ e, e ∈ L' ↔ G.src e ∈ Ui ∧ Bi ≤ ext (dis (s := s) (G.src e)) e ∧
        ext (dis (s := s) (G.src e)) e < B := by
      intro e
      rw [hmem e]
      constructor
      · rintro ⟨hu, h1, h2⟩
        have hc : d1' (G.src e) = dis (s := s) (G.src e) := hpost.U_complete _ hu
        rw [hc] at h1 h2
        exact ⟨hu, h1, h2⟩
      · rintro ⟨hu, h1, h2⟩
        have hc : d1' (G.src e) = dis (s := s) (G.src e) := hpost.U_complete _ hu
        rw [← hc] at h1 h2
        exact ⟨hu, h1, h2⟩
    obtain ⟨Lall, hLall, hfold⟩ := window_scan_step hPS.bound hpost D0 hnd hmem'
    have hres'' : Reselect cs.lit Ui (Lall.foldl (relaxIns G s B (some Bi)) (d1', D0)).1 piv' := by
      rw [hfold]; exact hres'
    have hne' : ¬ cs.lit.D.IsEmpty := hne
    have hnext := step_post hpre hfp h hne' hPS' hpost hLall hres''
    rw [hfold] at hnext
    -- (7) the re-selection insertions
    have hdle : ∀ z, d1' z ≤ d0 z := fun z => (hpost.mono z).trans ((h.mono z).trans (hfp.le z))
    have hfle : ∀ z, fst.d z ≤ d0 z := by
      intro z; rw [fd]; exact (foldl_relaxIns_fst_le B (some Bi) L' _ z).trans (hdle z)
    have hfw : WalkInv fst.d := by rw [fd]; exact foldl_relaxIns_walk B (some Bi) L' _ hw1
    have hlres' : ∀ y ∈ lres, fst.d y < B ∧ kof G s (fst.d y) = y := by
      intro y hy
      have hy' : y ∈ reselected cs.lit Ui piv' := by rw [← hlres]; exact List.mem_toFinset.mpr hy
      obtain ⟨j, rfl, hpj, hne''⟩ := mem_reselected.mp hy'
      have hmemP : piv' j ∈ cs.lit.P j \ Ui := (hres.resel j hpj hne'').1
      have hmemS : piv' j ∈ S := (hfp.groups j).2 (h.Psub j (Finset.mem_sdiff.mp hmemP).1)
      have hlt : fst.d (piv' j) < B := lt_of_le_of_lt (hfle _) (hpre.inRange _ hmemS)
      exact ⟨hlt, kof_of_walk hfw (ne_top_of_lt hlt)⟩
    obtain ⟨hvn, hSn, hKn, hmn, hCCn, hTn⟩ := insMany_sim (T := T) fst.d lres fst.g fst.Dc hSf hKf
      hlres'
    -- (8) the next concrete state is the literal next state
    have hlitnext : (nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).lit =
        nextState B cs.lit Bi B'i Ui (g1.view Dc1) (g2.view Dci) d1' L' piv' := by
      show ({ d := fst.d, D := (insManyC (dlOps G s) T fst.d lres fst.g fst.Dc).1.view
                (insManyC (dlOps G s) T fst.d lres fst.g fst.Dc).2.1,
              P := fun j => cs.P j \ Ui, piv := piv', U := cs.U ∪ Ui, B' := B'i } : LState G s p) =
        nextState B cs.lit Bi B'i Ui (g1.view Dc1) (g2.view Dci) d1' L' piv'
      rw [hvn, fv, fd, hlres]
      rfl
    set csn := nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres with hcsn
    have hSn' : SInv G s (dlOps G s) B g0.fresh csn.g csn.Dc := hSn
    have hMn' : csn.Dc.M = Mf (l + 1) := by
      show (insManyC (dlOps G s) T fst.d lres fst.g fst.Dc).2.1.M = Mf (l + 1)
      rw [insManyC_M, hfst, fold_M]
      show ((dlOps G s).merge T Dc1 Dci).1.M = Mf (l + 1)
      rw [merge_M, hM1, hMc]
    have hKn' : DB.KeyInj csn.g.L (kof G s) := hKn
    have hCCn' : CallChange g0.fresh B g0.L csn.g.L := by
      have c1 : CallChange g0.fresh B cs.g.L g1.L := by
        rw [hL1]; exact callChange_clearKeys _ _ _ _
      have c2 : CallChange g0.fresh B g1.L g2.L := hDP.chg.mono hS1.f0_le hPS.bound
      have c3 : CallChange g0.fresh B g2.L (delC g2 lUi).1.L := by
        rw [hLm]; exact callChange_clearKeys _ _ _ _
      have c4 : CallChange g0.fresh B (delC g2 lUi).1.L fst.g.L := hCCf.mono hSm.f0_le le_rfl
      have c5 : CallChange g0.fresh B fst.g.L csn.g.L := hCCn.mono hSf.f0_le le_rfl
      exact hCC.trans (c1.trans (c2.trans (c3.trans (c4.trans c5))))
    have hDn : csn.g.view csn.Dc =
        (nextState B cs.lit Bi B'i Ui (g1.view Dc1) (g2.view Dci) d1' L' piv').D := by
      rw [← hlitnext]; rfl
    have hTn' : ∀ y, csn.g.L y ≠ g0.L y →
        y ∈ csn.U ∨ ∃ a, csn.g.view csn.Dc y = some a ∧ a ≤ d0 y := by
      intro y hy
      rw [hDn]
      by_cases hU : y ∈ Ui
      · exact Or.inl (Finset.mem_union_right _ hU)
      have hyl : y ∉ lUi := fun h' => hU ((hUiU y).mp h')
      by_cases hn : csn.g.L y = fst.g.L y
      · by_cases hf : fst.g.L y = (delC g2 lUi).1.L y
        · have h32 : (delC g2 lUi).1.L y = g2.L y := by
            rw [hLm]; unfold DB.clearKeys; rw [if_neg hyl]
          by_cases h21 : g2.L y = g1.L y
          · by_cases h1c : g1.L y = cs.g.L y
            · have hc0 : cs.g.L y ≠ g0.L y := by
                intro h'; apply hy; rw [hn, hf, h32, h21, h1c, h']
              rcases hT y hc0 with hcU | ⟨a, ha, hale⟩
              · exact Or.inl (Finset.mem_union_left _ hcU)
              · have hyks : y ∉ ks := by
                  intro hyk
                  have hnone : g1.L y = none := by
                    rw [hL1]; unfold DB.clearKeys; rw [if_pos hyk]
                  obtain ⟨e, he, hek⟩ := hasKey_of_view ha
                  have hl := (DB.mem_liveVals.mp he).2
                  unfold DB.Entry.IsLive at hl
                  rw [hek] at hl
                  rw [h1c, hl] at hnone
                  exact absurd hnone (Option.some_ne_none _)
                have hD1 : (g1.view Dc1) y = some a := by
                  rw [hPS.rest y, if_neg (fun h' => hyks (List.mem_toFinset.mp h'))]
                  exact ha
                obtain ⟨a', ha', hle⟩ := nextState_D_le_left B cs.lit Bi B'i Ui _ _ d1' L' piv' hU hD1
                exact Or.inr ⟨a', ha', hle.trans hale⟩
            · have hyks : y ∈ ks := by
                by_contra hyk; apply h1c; rw [hL1]; unfold DB.clearKeys; rw [if_neg hyk]
              have hyS : y ∈ expand cs.lit ks.toFinset Bi :=
                mem_expand.mpr (Or.inl (List.mem_toFinset.mpr hyks))
              obtain ⟨k, hk, hkle⟩ := hpost.S_keys y hyS hU
              obtain ⟨a', ha', hle⟩ := nextState_D_le_right B cs.lit Bi B'i Ui _ _ d1' L' piv' hU hk
              exact Or.inr ⟨a', ha', hle.trans (hkle.trans ((h.mono y).trans (hfp.le y)))⟩
          · rcases hDP.touch y h21 with hyU' | ⟨a, ha, hale⟩
            · exact absurd hyU' hU
            · obtain ⟨a', ha', hle⟩ := nextState_D_le_right B cs.lit Bi B'i Ui _ _ d1' L' piv' hU ha
              exact Or.inr ⟨a', ha', hle.trans (hale.trans ((h.mono y).trans (hfp.le y)))⟩
        · obtain ⟨a, ha, hale⟩ := hTf y hf
          rw [fv] at ha
          obtain ⟨a', ha', hle⟩ := insertMany_le (reselected cs.lit Ui piv')
            (L'.foldl (relaxIns G s B (some Bi)) (d1', D0)).1 ha
          exact Or.inr ⟨a', ha', hle.trans (hale.trans (hdle y))⟩
      · have hyl' := hTn y hn
        have hyr : y ∈ reselected cs.lit Ui piv' := by
          rw [← hlres]; exact List.mem_toFinset.mpr hyl'
        obtain ⟨k, hk, hkle⟩ := DSx.mergeVal_le_right
          (a := (L'.foldl (relaxIns G s B (some Bi)) (d1', D0)).2 y)
          (b := some ((L'.foldl (relaxIns G s B (some Bi)) (d1', D0)).1 y)) rfl
        refine Or.inr ⟨k, ?_, hkle.trans ?_⟩
        · show insertMany G s _ _ _ y = some k
          rw [insertMany_apply, if_pos hyr]; exact hk
        · rw [← fd]; exact hfle y
    have hUi_disj : Disjoint Ui cs.U := by
      rw [Finset.disjoint_left]
      intro v hv hvU
      have hv' : v ∈ Utilde Bi (expand cs.lit ks.toFinset Bi : Set (Fin G.n)) :=
        utilde_mono_bound hpost.B'_le ((hpost.U_eq v).mp hv)
      exact (UKi_sub h hPS' hv').2.1 hvU
    have hUine : 1 ≤ τ l → Ui.Nonempty := by
      intro hτ1
      by_cases hfull : B'i = Bi
      · refine ⟨x0, (hpost.U_eq x0).mpr ?_⟩
        obtain ⟨-, hlt⟩ := Si_facts h hPS' hx0S
        have hdis : dis (s := s) x0 < Bi := lt_of_le_of_lt (h.walk.sound x0) hlt
        have hreach : G.Reachable s x0 := by
          by_contra hc
          rw [dis_of_not_reachable hc] at hdis
          exact absurd hdis (not_lt.mpr le_top)
        refine ⟨?_, x0, Finset.mem_coe.mpr hx0S, onPath_self hreach⟩
        show dis (s := s) x0 < B'i
        rw [hfull]; exact hdis
      · have hlt : B'i < Bi := lt_of_le_of_ne hpost.B'_le hfull
        have hcard := hpost.partial_card hlt
        exact Finset.card_pos.mp (lt_of_lt_of_le hτ1 hcard)
    have hstrong : ks.toFinset.card < DC.M (l + 1) → (g1.view Dc1).IsEmpty ∧ Bi = B := by
      intro hlt
      simp only [pullC, Prod.mk.injEq] at hpull
      obtain ⟨hks, hBi, hg1, hDc1, -⟩ := hpull
      have hnd' : ks.Nodup := hks ▸ (dlOps G s).pull_nodup T hS.ids
      rw [List.toFinset_card_of_nodup hnd', hDC, ← hMc] at hlt
      obtain ⟨-, hor, -, -, -⟩ := (dlOps G s).pull_post T hS.wf hK hS.ids hS.M1
      have hBiB : Bi = B := by
        rcases hor with h' | h'
        · rw [← hBi, h', hS.Bd]
        · rw [hks] at h'; omega
      refine ⟨?_, hBiB⟩
      intro y
      rw [hPS.rest y]
      split_ifs with hy
      · rfl
      · rcases hv : cs.g.view cs.Dc y with _ | a
        · rfl
        · exfalso
          apply hy
          have hlt' : a < Bi := by
            rw [hBiB, ← hS.Bd]; exact view_lt_Bd hS.wf hv
          exact (hPS.pulled y).mpr ⟨a, hv, hlt'⟩
    -- (9) the block-count potential
    have hMc1 : Dc1.M = Mf (l + 1) := by rw [hM1, hMc]
    have hM3 : 3 ≤ Dc1.M := by
      have := h3M l; have := hMpos l; omega
    have hpsi1 : DL.psi Dc1 + cs.Dc.M ≤ DL.psi cs.Dc ∨ DL.psi Dc1 = cs.Dc.M := by
      have := pull_psi (T := T) hS hK
      rw [hpull] at this
      exact this
    have hpsim : DL.psi ((dlOps G s).merge T Dc1 Dci).1 ≤ DL.psi Dc1 + Dc1.M + 2 * entCount Dci :=
      merge_psi (T := T) hM3
    have hpsif : DL.psi fst.Dc ≤ DL.psi ((dlOps G s).merge T Dc1 Dci).1 + 2 * L'.length :=
      fold_psi (T := T) (some Bi) L' ⟨d1', (delC g2 lUi).1, ((dlOps G s).merge T Dc1 Dci).1, 0⟩ hSm hKm hw1
    have hpsin : DL.psi (insManyC (dlOps G s) T fst.d lres fst.g fst.Dc).2.1 ≤
        DL.psi fst.Dc + 2 * lres.length :=
      insMany_psi (T := T) fst.d lres fst.g fst.Dc hSf hKf hlres'
    have hPm : DL.psi ((dlOps G s).merge T Dc1 Dci).1 + 2 * (L'.length + lres.length) ≤ P := by
      rcases hpsi1 with h' | h'
      · omega
      · omega
    have hpsiN : DL.psi (nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).Dc ≤ DL.psi cs.Dc + 2 * (entCount Dci + L'.length + lres.length) ∨
        DL.psi (nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).Dc ≤ 2 * Mf (l + 1) + 2 * (entCount Dci + L'.length + lres.length) := by
      show DL.psi (insManyC (dlOps G s) T fst.d lres fst.g fst.Dc).2.1 ≤ _ ∨
        DL.psi (insManyC (dlOps G s) T fst.d lres fst.g fst.Dc).2.1 ≤ _
      rcases hpsi1 with h' | h'
      · left; omega
      · right; omega
    -- (10) the cost of the iteration, telescoped
    have hks_len : ks.length = ks.toFinset.card := by
      have hnd' : ks.Nodup := by
        have := (dlOps G s).pull_nodup T (L := cs.g.L) hS.ids
        simp only [pullC, Prod.mk.injEq] at hpull
        rw [← hpull.1]; exact this
      exact (List.toFinset_card_of_nodup hnd').symm
    have hlUi_len : lUi.length = Ui.card := by rw [← hlU, List.toFinset_card_of_nodup hlUnd]
    have hlres_len : lres.length ≤ (markedGroups cs.lit Ui).card := by
      rw [← List.toFinset_card_of_nodup hlresnd, hlres]
      have hsub : reselected cs.lit Ui piv' ⊆ (markedGroups cs.lit Ui).image piv' := by
        intro x hx
        obtain ⟨j, rfl, hj1, hj2⟩ := mem_reselected.mp hx
        exact Finset.mem_image.mpr ⟨j, by simp [markedGroups, hj1, hj2], rfl⟩
      exact (Finset.card_le_card hsub).trans Finset.card_image_le
    have hcost : ∀ os : List (DB.Block (Fin G.n) (WLab G s)), (∀ x ∈ DB.allEnts os, x.id < g0.fresh) →
        ((DB.allEnts os).map (·.id)).Nodup →
        iterCostD (dlOps G s) T B cs ks.toFinset cp Bi Ui Dc1 Dci d1' g2 lUi L' lres
            + ((dlOps G s).merge T Dc1 Dci).2 + lg.cost + potG (nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).g (nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).Dc + othP (nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).g.L os ≤
          iterCost DC (l + 1) cs.lit ks.toFinset Ui L'.length
            + DC.merge (l + 1) (keyCount G s (g2.view Dci)) + lgi.cost + potG cs.g cs.Dc
            + othP cs.g.L os := by
      intro os hos hosnd
      -- (a) pull
      have hdisj0 : ∀ x ∈ DB.allEnts cs.Dc.blocks, ∀ z ∈ DB.allEnts os, x.id ≠ z.id := by
        intro x hx z hz
        have h1' := hS.own x hx
        have h2' := hos z hz
        omega
      have ta : cp + potG g1 Dc1 + othP g1.L os ≤
          potG cs.g cs.Dc + othP cs.g.L os + (735 * ks.length + 950) := by
        have := pull_tele (T := T) hS hK hdisj0
        rw [hpull] at this
        exact this
      -- (b) the child, with the parent's structure among its others
      have hae : DB.allEnts (Dc1.blocks ++ os) = DB.allEnts Dc1.blocks ++ DB.allEnts os := by
        simp [DB.allEnts]
      have hosc : ∀ x ∈ DB.allEnts (Dc1.blocks ++ os), x.id < g1.fresh := by
        intro x hx
        rw [hae, List.mem_append] at hx
        rcases hx with hx | hx
        · exact hS1.fr x hx
        · exact lt_of_lt_of_le (hos x hx) hS1.f0_le
      have hoscnd : ((DB.allEnts (Dc1.blocks ++ os)).map (·.id)).Nodup := by
        rw [hae, List.map_append, List.nodup_append]
        refine ⟨hS1.ids, hosnd, ?_⟩
        intro a ha b hb hab
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hb
        have h1' := hS1.own x hx
        have h2' := hos z hz
        omega
      have tb : lg.cost + potG g2 Dci + othP g2.L (Dc1.blocks ++ os) ≤
          lgi.cost + othP g1.L (Dc1.blocks ++ os) := hcostI hFc (Dc1.blocks ++ os) hosc hoscnd
      have tsplit1 : potG g1 Dc1 + othP g1.L os =
          (DL.spot Dc1.M Dc1.blocks + DL.epot Dc1) + othP g1.L (Dc1.blocks ++ os) := potM_split g1.L Dc1 os
      have tsplit2 : potG g2 Dc1 + othP g2.L os =
          (DL.spot Dc1.M Dc1.blocks + DL.epot Dc1) + othP g2.L (Dc1.blocks ++ os) := potM_split g2.L Dc1 os
      -- (c) merge
      have hDci1 : 1 ≤ Dci.M := hDP.sinv.M1
      have h3' : 3 * Dci.M ≤ Dc1.M := by
        have hMi : Dci.M = Mf l := hDP.M
        rw [hMc1, hMi]; exact h3M l
      have tc : ((dlOps G s).merge T Dc1 Dci).2 + potG g2 ((dlOps G s).merge T Dc1 Dci).1 ≤
          potG g2 Dc1 + potG g2 Dci + 14 := merge_tele (T := T) (L := g2.L) hS1.wf.1 hDci1 h3'
      -- (d) delete
      have td := del_tele (g := g2) (Dc := ((dlOps G s).merge T Dc1 Dci).1) hSm.ids lUi hosnd
      rw [hlUi_len] at td
      -- (e) the window scan
      have hos3 : ∀ x ∈ DB.allEnts os, x.id < (delC g2 lUi).1.fresh := by
        intro x hx; exact lt_of_lt_of_le (hos x hx) hSm.f0_le
      have hMm : ((dlOps G s).merge T Dc1 Dci).1.M = Mf (l + 1) := by
        rw [((dlOps G s).merge_M T Dc1 Dci).1, hMc1]
      have te : fst.c + potG fst.g fst.Dc + othP fst.g.L os ≤
          0 + potG (delC g2 lUi).1 ((dlOps G s).merge T Dc1 Dci).1 + othP (delC g2 lUi).1.L os
            + L'.length * (1 + DC.ins (l + 1)) :=
        fold_tele (T := T) (some Bi) (Mlv := Mf (l + 1)) (P := P) hIns hosnd L'
          ⟨d1', (delC g2 lUi).1, ((dlOps G s).merge T Dc1 Dci).1, 0⟩ hSm hKm hw1 hMm
          (by show DL.psi ((dlOps G s).merge T Dc1 Dci).1 + 2 * L'.length ≤ P; omega) hos3
      -- (f) the re-selection insertions
      have hosf : ∀ x ∈ DB.allEnts os, x.id < fst.g.fresh := by
        intro x hx; exact lt_of_lt_of_le (hos x hx) hSf.f0_le
      have hMf' : fst.Dc.M = Mf (l + 1) := by
        rw [hfst, fold_M]; exact hMm
      have tf := insMany_tele (T := T) fst.d (Mlv := Mf (l + 1)) (P := P) hIns hosnd lres fst.g fst.Dc
        hSf hKf hlres' hMf' (by omega) hosf
      have hmk : ∑ j ∈ markedGroups cs.lit Ui, ((cs.lit.P j \ Ui).card + 1 + DC.ins (l + 1)) =
          ∑ j ∈ markedGroups cs.lit Ui, ((cs.lit.P j \ Ui).card + 1)
            + (markedGroups cs.lit Ui).card * DC.ins (l + 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
      have hmul : lres.length * DC.ins (l + 1) ≤ (markedGroups cs.lit Ui).card * DC.ins (l + 1) :=
        Nat.mul_le_mul_right _ hlres_len
      have hp := hpullC ks.toFinset.card
      have hd := hdelC Ui.card
      have hm := hmergeC (keyCount G s (g2.view Dci))
      have e1 : iterCost DC (l + 1) cs.lit ks.toFinset Ui L'.length =
          1 + DC.pull (l + 1) ks.toFinset.card
            + (ks.toFinset.card + ∑ j ∈ pulledGroups cs.lit ks.toFinset, (cs.lit.P j).card)
            + (DC.del (l + 1) Ui.card + Ui.card)
            + (Ui.card + L'.length * (1 + DC.ins (l + 1)))
            + ∑ j ∈ markedGroups cs.lit Ui, ((cs.lit.P j \ Ui).card + 1 + DC.ins (l + 1)) := rfl
      have e2 : iterCostD (dlOps G s) T B cs ks.toFinset cp Bi Ui Dc1 Dci d1' g2 lUi L' lres =
          1 + cp + (ks.toFinset.card + ∑ j ∈ pulledGroups cs.lit ks.toFinset, (cs.lit.P j).card)
            + ((delC g2 lUi).2 + Ui.card) + Ui.card + fst.c
            + ∑ j ∈ markedGroups cs.lit Ui, ((cs.lit.P j \ Ui).card + 1)
            + (insManyC (dlOps G s) T fst.d lres fst.g fst.Dc).2.2 := rfl
      have e3a : potG (nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).g (nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).Dc = potG (insManyC (dlOps G s) T fst.d lres fst.g fst.Dc).1
          (insManyC (dlOps G s) T fst.d lres fst.g fst.Dc).2.1 := rfl
      have e3b : othP (nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).g.L os = othP (insManyC (dlOps G s) T fst.d lres fst.g fst.Dc).1.L os := rfl
      rw [e1, e2, hmk, e3a, e3b]
      rw [hks_len] at ta
      omega
    exact ⟨lgi, hsubCi', hstripi, hPS', by rw [hDC, ← hMc]; exact hS0M, hres', hlitnext,
      by rw [hlitnext]; exact hnext, hI1, hSn', hMn', hKn', hCCn', hTn', hUine, hUi_disj, hstrong,
      hpsiN, hcost⟩

end stepT

end BM
end CHD
end Frontier
