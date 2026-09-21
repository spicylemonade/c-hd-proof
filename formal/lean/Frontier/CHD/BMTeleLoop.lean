import Frontier.CHD.BMTeleStep

/-!
# Frontier.CHD.BMTeleLoop — the concrete run over `DLazy`, telescoped (tracker O23; owner agent-01)

**NON-GATE** (Layer A).  For agent-04's lazy block structure (`dlOps`), the ACTUAL cost of every
concrete run (`BMSSPD`) is at most the cost of the literal run (`BMSSPC`) with any cost parameters
`DC` dominating the amortized charges:
* pull `735k + 950`, delete `5k + 1`, merge `14`, new structure `3` (agent-04, agent-06),
* insert `DC.ins l ≥ insBound (M_l) (2M_l + 2·Emax l)` (binary search over at most
  `O(Emax/M)` blocks plus `O(log(Emax/M))`, via the block-count potential `DL.psi`),
* base case: `DC.bins ≥ DCb.bins + DC.ins 0 + 3` (each heap insertion also pays for the conversion
  of its key into the level-0 structure), `DC.bext ≥ DCb.bext`,

provided every subtree of the log fits its level's placement budget (`Fits Emax`, from agent-03's
(B4′) subtree sums).  The family potential (`potM` of the active structure plus `2·stale` of all
other structures) telescopes along the whole run.

* `loopD_tele`: the loop (block-count invariant `psi + 2·(remaining placements) ≤ 2M + 2·Emax`);
* `callD_tele`: one recursive call (initialisation, loop, finalisation);
* `baseDH_tele`: the heap base case (`baseLoopC_recostN`: the literal base loop at the larger heap
  charge costs `(Δbins)·|Eout U|` more);
* `bmsspD_tele`: all levels (`SimSubT`);
* `bmsspDL_tele_top`: the top-level run: `lg.cost ≤ lgC.cost` for a literal log `lgC` with the same
  stripped trace.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

section costs

variable {Ω : Type}

theorem Log.costT_append (l1 l2 : Log G s Ω) : Log.cost (l1 ++ l2) = Log.cost l1 + Log.cost l2 := by
  unfold Log.cost; rw [List.map_append, List.sum_append]

theorem Log.costT_shift (i : ℕ) (lg : Log G s Ω) : Log.cost (Log.shift i lg) = Log.cost lg := by
  unfold Log.cost Log.shift; rw [List.map_map]; rfl

theorem Log.costT_cons (x : List ℕ × CallRec G s Ω) (l : Log G s Ω) :
    Log.cost (x :: l) = x.2.cost + Log.cost l := by
  unfold Log.cost; rw [List.map_cons, List.sum_cons]

theorem ownB_of_rec (r : CallRec G s Ω) (h : r.base = false) :
    ownB r = r.p + r.J.card + 2 * r.S.card + r.Wr.card := by
  unfold ownB; simp [h]

theorem ownB_of_base (r : CallRec G s Ω) (h : r.base = true) :
    ownB r = r.S.card + (Finset.univ.filter fun e => G.src e ∈ r.U).card := by
  unfold ownB; simp [h]

theorem psi_newC (M : ℕ) (Bd : WLab G s) : DL.psi (newC M Bd : DStrM G s) = M := DL.psi_new M Bd

theorem othP_nil (L : LiveM G s) : othP L [] = 0 := by
  simp [othP, DB.staleCnt, DB.allEnts]


theorem ownSum_strip (lg : Log G s Ω) : Log.ownSum (Log.strip lg) = Log.ownSum lg := by
  unfold Log.ownSum Log.strip; rw [List.map_map]; rfl

theorem subLog_strip (lg : Log G s Ω) (q : List ℕ) :
    subLog (Log.strip lg) q = Log.strip (subLog lg q) := by
  unfold subLog Log.strip
  rw [List.filter_map]
  rfl

theorem Fits.strip {Emax : ℕ → ℕ} {lg : Log G s Ω} (h : Fits Emax lg) : Fits Emax (Log.strip lg) := by
  intro q r hq
  obtain ⟨⟨q', r'⟩, hq', he⟩ := List.mem_map.mp hq
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  rw [subLog_strip, ownSum_strip]
  exact h q' r' hq'

theorem Fits.of_strip {Emax : ℕ → ℕ} {lg : Log G s Ω} (h : Fits Emax (Log.strip lg)) : Fits Emax lg := by
  intro q r hq
  have hm : (q, r.strip) ∈ Log.strip lg := List.mem_map.mpr ⟨(q, r), hq, rfl⟩
  have := h q r.strip hm
  rw [subLog_strip, ownSum_strip] at this
  exact this

/-- `Fits` depends only on the stripped trace. -/
theorem Fits.of_strip_eq {Emax : ℕ → ℕ} {lg lgC : Log G s Ω} (hs : Log.strip lgC = Log.strip lg)
    (h : Fits Emax lgC) : Fits Emax lg := by
  apply Fits.of_strip
  rw [← hs]
  exact Fits.strip h

end costs

/-! ## The loop, telescoped -/

section loopT

variable {Φ Ω : Type} {T : ℕ}
variable {B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {p : ℕ}
  {P0 : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {B'0 : WLab G s}

/-- **The loop over the lazy structure, telescoped.**  Along the loop, the block-count potential
plus twice the remaining placement budget (the rest of the log's own placements, the remaining
window edges, the remaining group members, and a reserve `R` for the finalization) stays within
`2M + 2·Emax`; every insertion then costs at most `DC.ins`, and the actual cost plus the family
potential is paid by the literal amortized cost. -/
theorem loopD_tele (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W)
    {τ : ℕ → ℕ} {Inv : Φ → Prop} {Mf Emax : ℕ → ℕ} (hMpos : ∀ l, 1 ≤ Mf l)
    (h3M : ∀ l, 3 * Mf l ≤ Mf (l + 1))
    {subD : SubRelD G s Φ Ω} {subC : SubRelC G s Φ Ω} {l : ℕ}
    (hsimsub : SimSub G s (dlOps G s) τ Inv Mf l subD subC)
    (hsimsubT : SimSubT G s τ Inv Mf Emax l subD subC) (hsubC : GoodSub G s τ Inv l subC)
    (hsubE : ∀ Blow B S d φ g res φ' g' lg, CallPre B S d → Inv φ →
      (∀ x ∈ S, Blow ≤ dis (s := s) x) → Blow ≤ B → DB.KeyInj g.L (kof G s) →
      (∀ v i a, g.L v = some (i, a) → B ≤ a) → subD Blow B S d φ g res φ' g' lg →
      entCount res.2.2.1 ≤ Log.ownSum lg)
    {DC : DCost} (hDC : DC.M (l + 1) = Mf (l + 1))
    (hIns : ∀ D : DStrM G s, D.M = Mf (l + 1) → DL.psi D ≤ 2 * Mf (l + 1) + 2 * Emax (l + 1) →
      insCharge D ≤ DC.ins (l + 1))
    (hpullC : ∀ k, 735 * k + 950 ≤ DC.pull (l + 1) k) (hdelC : ∀ k, 5 * k + 1 ≤ DC.del (l + 1) k)
    (hmergeC : ∀ k, 14 ≤ DC.merge (l + 1) k)
    {g0 : DGl G s} {τl : ℕ} (R : ℕ) :
    ∀ i (cs : CSt G s p) φ cs' φ' lg J cm c,
      LoopD G s (dlOps G s) T subD B τl i cs φ cs' φ' lg J cm c →
      LInv G s B S d0 d1 P0 B'0 cs.lit → Inv φ → SInv G s (dlOps G s) B g0.fresh cs.g cs.Dc →
      cs.Dc.M = Mf (l + 1) → DB.KeyInj cs.g.L (kof G s) → CallChange g0.fresh B g0.L cs.g.L →
      (∀ y, cs.g.L y ≠ g0.L y → y ∈ cs.U ∨ ∃ a, cs.g.view cs.Dc y = some a ∧ a ≤ d0 y) →
      Fits Emax lg →
      DL.psi cs.Dc + 2 * (Log.ownSum lg + J.card + ∑ j, (cs.P j).card + R) ≤
        2 * Mf (l + 1) + 2 * Emax (l + 1) →
      Log.ownSum lg + J.card + ∑ j, (cs.P j).card + R ≤ Emax (l + 1) →
      ∃ lgC cmC cC, LoopC G s DC subC (l + 1) B τl i cs.lit φ cs'.lit φ' lgC J cmC cC ∧
        Log.strip lgC = Log.strip lg ∧
        LInv G s B S d0 d1 P0 B'0 cs'.lit ∧ (τl < cs'.U.card ∨ (cs'.g.view cs'.Dc).IsEmpty) ∧
        Inv φ' ∧ SInv G s (dlOps G s) B g0.fresh cs'.g cs'.Dc ∧ cs'.Dc.M = Mf (l + 1) ∧
        DB.KeyInj cs'.g.L (kof G s) ∧ CallChange g0.fresh B g0.L cs'.g.L ∧
        (∀ y, cs'.g.L y ≠ g0.L y → y ∈ cs'.U ∨ ∃ a, cs'.g.view cs'.Dc y = some a ∧ a ≤ d0 y) ∧
        DL.psi cs'.Dc + 2 * (∑ j, (cs'.P j).card + R) ≤ 2 * Mf (l + 1) + 2 * Emax (l + 1) ∧
        ∑ j, (cs'.P j).card + R ≤ Emax (l + 1) ∧
        (∀ os : List (DB.Block (Fin G.n) (WLab G s)), (∀ x ∈ DB.allEnts os, x.id < g0.fresh) →
          ((DB.allEnts os).map (·.id)).Nodup →
          c + cm + lg.cost + potG cs'.g cs'.Dc + othP cs'.g.L os ≤
            cC + cmC + lgC.cost + potG cs.g cs.Dc + othP cs.g.L os) := by
  intro i cs φ cs' φ' lg J cm c hloop
  induction hloop with
  | stop i cs φ hstop =>
    intro h hI hS hMc hK hCC hT _ hB1 hB2
    refine ⟨[], 0, 1, LoopC.stop i cs.lit φ hstop, rfl, h, hstop, hI, hS, hMc, hK, hCC, hT, ?_, ?_,
      fun _ _ _ => le_rfl⟩
    · simp only [Log.ownSum, List.map_nil, List.sum_nil, Finset.card_empty] at hB1; omega
    · simp only [Log.ownSum, List.map_nil, List.sum_nil, Finset.card_empty] at hB2; omega
  | step i cs cs' φ φ1 φ' ks Bi g1 Dc1 cp B'i Ui Dci d1' g2 lUi L' piv' lres lg lg' J' cm c
      hcard hne hpull hsubD hlUnd hlU hnd hmem hres hlresnd hlres hrest ih =>
    intro h hI hS hMc hK hCC hT hFits hB1 hB2
    classical
    -- the next-state invariants (without costs) and the rest of the loop's window edges
    obtain ⟨-, -, -, -, -, -, -, hnext', hI1, hSn', hMn', hKn', hCCn', hTn', -, hUi_disj, -, -⟩ :=
      stepD_inv (T := T) (DC := DC) (g0 := g0) hpre hfp (fun _ => trivial) hsimsub hsubC hDC h hI
        hS hMc hK hCC hT hne hpull hsubD hlU hnd hmem hres hlres
    obtain ⟨-, ihJ, -⟩ := loopD_place (T := T) (DC := DC) (g0 := g0) hpre hfp (fun _ => trivial)
      hsimsub hsubC hDC hsubE _ _ _ _ _ _ _ _ _ hrest hnext' hI1 hSn' hMn' hKn' hCCn' hTn'
    have hdisj : Disjoint L'.toFinset J' := by
      rw [Finset.disjoint_left]
      intro e he he'
      have hsrc : G.src e ∈ Ui := ((hmem e).mp (List.mem_toFinset.mp he)).1
      exact (ihJ e he').2 (Finset.mem_union_right _ hsrc)
    -- the child's placement
    obtain ⟨hPS, -, -, hK1, -, -, -, -, habove, -⟩ := pull_sim hS hK hpull
    have hPS' : PullSpec cs.lit.D B ks.toFinset Bi (g1.view Dc1) := hPS
    have hsp := step_pre hpre hfp h hPS'
    have hlowdis : ∀ x ∈ expand cs.lit ks.toFinset Bi, cs.lit.B' ≤ dis (s := s) x :=
      fun x hx => (Si_facts h hPS' hx).1.2.2
    have hSne : ks.toFinset.Nonempty := by
      apply hPS'.nonempty
      have hne' : ¬ cs.lit.D.IsEmpty := hne
      simp only [DS.IsEmpty, not_forall] at hne'
      exact hne'
    obtain ⟨x0, hx0⟩ := hSne
    have hBlt : cs.lit.B' < Bi := by
      obtain ⟨⟨-, -, hB⟩, hlt⟩ := Si_facts h hPS' (mem_expand.mpr (Or.inl hx0))
      exact lt_of_le_of_lt (hB.trans (h.walk.sound x0)) hlt
    have hEi : entCount Dci ≤ Log.ownSum lg :=
      hsubE _ _ _ _ _ _ (B'i, Ui, Dci, d1') _ _ lg hsp hI hlowdis hBlt.le hK1 habove hsubD
    -- the budget of this iteration
    have hres_card := reselected_card_le h Ui piv'
    have hlres_len : lres.length = (reselected cs.lit Ui piv').card := by
      rw [← hlres, List.toFinset_card_of_nodup hlresnd]
    have hL'len : L'.length = L'.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    have hJ : (L'.toFinset ∪ J').card = L'.toFinset.card + J'.card := Finset.card_union_of_disjoint hdisj
    have hown : Log.ownSum (Log.shift i lg ++ lg') = Log.ownSum lg + Log.ownSum lg' := by
      rw [Log.ownSum_append, Log.ownSum_shift]
    have hPn : ∑ j, ((nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).P j).card =
        ∑ j, (cs.lit.P j \ Ui).card := rfl
    have hPc : ∑ j, (cs.P j).card = ∑ j, (cs.lit.P j).card := rfl
    rw [hown, hJ] at hB1 hB2
    have hP1 : DL.psi cs.Dc + 2 * (entCount Dci + L'.length + lres.length) ≤
        2 * Mf (l + 1) + 2 * Emax (l + 1) := by omega
    have hP2 : 2 * Mf (l + 1) + 2 * (entCount Dci + L'.length + lres.length) ≤
        2 * Mf (l + 1) + 2 * Emax (l + 1) := by omega
    -- the telescoped iteration
    have hFc : Fits Emax lg := (Fits.append_left hFits).shift
    have hF' : Fits Emax lg' := Fits.append_right hFits
    obtain ⟨lgi, hsubCi', hstripi, hPS'', hS0M', hres', hlitnext, hnext'', hI1', hSn'', hMn'', hKn'',
      hCCn'', hTn'', -, -, hSP', hpsiN, hcost⟩ :=
      stepD_tele (T := T) (DC := DC) (g0 := g0) hpre hfp hMpos h3M hsimsubT hsubC hDC hIns
        hpullC hdelC hmergeC h hI hS hMc hK hCC hT hne hpull hsubD hlUnd hlU hnd hmem hres
        hlresnd hlres hFc hP1 hP2
    have hne' : ¬ cs.lit.D.IsEmpty := hne
    -- the rest of the loop
    have hB1' : DL.psi (nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).Dc +
        2 * (Log.ownSum lg' + J'.card +
          ∑ j, ((nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).P j).card + R) ≤
        2 * Mf (l + 1) + 2 * Emax (l + 1) := by
      rw [hPn]
      rcases hpsiN with h' | h'
      · omega
      · omega
    have hB2' : Log.ownSum lg' + J'.card +
          ∑ j, ((nextD (dlOps G s) T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).P j).card + R ≤
        Emax (l + 1) := by
      rw [hPn]; omega
    obtain ⟨lgC', cmC', cC', hloopC', hstrip', h', hstop', hI', hS', hM', hK', hCC', hT', hB1'', hB2'',
      hcost'⟩ := ih hnext'' hI1' hSn'' hMn'' hKn'' hCCn'' hTn'' hF' hB1' hB2'
    rw [hlitnext] at hloopC'
    refine ⟨lgi.shift i ++ lgC', _, _, LoopC.step i cs.lit cs'.lit φ φ1 φ' ks.toFinset Bi
      (g1.view Dc1) B'i Ui (g2.view Dci) d1' L' piv' lgi lgC' J' cmC' cC' hcard hne' hPS''
      hS0M' hSP' hsubCi' hnd hmem hres' hloopC', ?_, h', hstop', hI', hS', hM', hK', hCC', hT',
      hB1'', hB2'', ?_⟩
    · rw [Log.strip_append, Log.strip_append, Log.strip_shift, Log.strip_shift, hstripi, hstrip']
    · intro os hos hosnd
      have k1 := hcost os hos hosnd
      have k2 := hcost' os hos hosnd
      rw [Log.costT_append, Log.costT_append, Log.costT_shift, Log.costT_shift]
      omega

end loopT


/-! ## One recursive call, telescoped -/

section callT

variable {Φ Ω : Type} {T : ℕ}

/-- **A recursive call over the lazy structure, telescoped**: it simulates the literal call, and
when its log fits the budgets, its actual cost plus the potential of the returned structure plus
the others' potential is at most the literal cost plus the others' potential at the start. -/
theorem callD_tele {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} (hFPC : FPCSound G s FPC Inv)
    {τ : ℕ → ℕ} {Mf Emax : ℕ → ℕ} (hMpos : ∀ l, 1 ≤ Mf l) (h3M : ∀ l, 3 * Mf l ≤ Mf (l + 1))
    {subD : SubRelD G s Φ Ω} {subC : SubRelC G s Φ Ω} {l : ℕ}
    (hsimsub : SimSub G s (dlOps G s) τ Inv Mf l subD subC)
    (hsimsubT : SimSubT G s τ Inv Mf Emax l subD subC) (hsubC : GoodSub G s τ Inv l subC)
    (hsubE : ∀ Blow B S d φ g res φ' g' lg, CallPre B S d → Inv φ →
      (∀ x ∈ S, Blow ≤ dis (s := s) x) → Blow ≤ B → DB.KeyInj g.L (kof G s) →
      (∀ v i a, g.L v = some (i, a) → B ≤ a) → subD Blow B S d φ g res φ' g' lg →
      entCount res.2.2.1 ≤ Log.ownSum lg)
    {DC : DCost} (hDC : DC.M (l + 1) = Mf (l + 1))
    (hIns : ∀ D : DStrM G s, D.M = Mf (l + 1) → DL.psi D ≤ 2 * Mf (l + 1) + 2 * Emax (l + 1) →
      insCharge D ≤ DC.ins (l + 1))
    (hnewC : 3 ≤ DC.new (l + 1))
    (hpullC : ∀ k, 735 * k + 950 ≤ DC.pull (l + 1) k) (hdelC : ∀ k, 5 * k + 1 ≤ DC.del (l + 1) k)
    (hmergeC : ∀ k, 14 ≤ DC.merge (l + 1) k)
    {Blow B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} {φ0 φ2 : Φ} {g0 gE : DGl G s}
    {res : ResultD G s} {lg : Log G s Ω}
    (hpre : CallPre B S d0) (hI : Inv φ0) (hlow : ∀ x ∈ S, Blow ≤ dis (s := s) x)
    (hK : DB.KeyInj g0.L (kof G s)) (hab : ∀ v i a, g0.L v = some (i, a) → B ≤ a)
    (hrel : CallD G s (dlOps G s) FPC T Mf subD (l + 1) Blow B S d0 φ0 g0 (τ (l + 1)) res φ2 gE lg) :
    ∃ lgC, CallC G s FPC DC subC (l + 1) Blow B S d0 φ0 (τ (l + 1)) (res.lit gE) φ2 lgC ∧
      Log.strip lgC = Log.strip lg ∧ DPost G s (dlOps G s) B d0 (Mf (l + 1)) g0 gE res ∧
      (Fits Emax lg → ∀ os : List (DB.Block (Fin G.n) (WLab G s)),
        (∀ x ∈ DB.allEnts os, x.id < g0.fresh) → ((DB.allEnts os).map (·.id)).Nodup →
        lg.cost + potG gE res.2.2.1 + othP gE.L os ≤ lgC.cost + othP g0.L os) := by
  classical
  have hsim := callD_sim (T := T) (DC := DC) hFPC (fun _ => trivial) hMpos hsimsub hsubC hDC hpre hI
    hlow hK hab hrel
  by_cases hF : Fits Emax lg
  swap
  · obtain ⟨lgC, h1, h2, h3⟩ := hsim
    exact ⟨lgC, h1, h2, h3, fun h => absurd h hF⟩
  obtain ⟨-, -, -, hDP⟩ := hsim
  obtain ⟨d1, p, P, Q, W, φ1, ω, cfp, piv, lpiv, cs, lgc, J, cm, cl, L, B'f, lT6, W', lW', hfprel,
    hpiv, hlpnd, hlp, hloop, hB'e, hB'n, hT6nd, hT6, hW', hL, hlWnd, hlW, hres, hgE, hlg⟩ := hrel
  have hlow' : ∀ x ∈ S, Blow ≤ d0 x := fun x hx => (hlow x hx).trans (hpre.walk.sound x)
  obtain ⟨hfp, hI1⟩ := hFPC _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpre hI hlow' hfprel
  -- the placement budget of the call
  obtain ⟨R, hR, hRlvl, hRbase, hRp, hRJ, hRS, hRWr⟩ : ∃ R : CallRec G s Ω, lg = ([], R) :: lgc ∧
      R.lvl = l + 1 ∧ R.base = false ∧ R.p = p ∧ R.J = J ∧ R.S = S ∧ R.Wr = L.toFinset :=
    ⟨_, hlg, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hF' : Fits Emax (([], R) :: lgc) := hR ▸ hF
  have hroot := Fits.root hF'
  rw [Log.ownSum_cons, ownB_of_rec R hRbase, hRp, hRJ, hRS, hRWr, hRlvl] at hroot
  have hFc : Fits Emax lgc := Fits.cons hF'
  have hLlen : L.toFinset.card = L.length := List.toFinset_card_of_nodup hL.1
  have hlpiv : lpiv.length ≤ p := by
    rw [← List.toFinset_card_of_nodup hlpnd, hlp]
    exact Finset.card_image_le.trans (by simp)
  have hPS : ∑ j, (P j).card ≤ S.card := card_groups_le hfp.groups hfp.gdisj
  have hT6len : lT6.length ≤ S.card := by
    rw [← List.toFinset_card_of_nodup hT6nd]
    exact Finset.card_le_card (fun x hx => ((hT6 x).mp (List.mem_toFinset.mp hx)).1)
  have hW'len : lW'.length = W'.card := by rw [← hlW, List.toFinset_card_of_nodup hlWnd]
  -- the initial structure with the pivots
  obtain ⟨hSnew, hvnew⟩ := new_sim (ops := dlOps G s) (g := g0) (M := Mf (l + 1)) (B := B)
    (hMpos _) hab
  have hlp' : ∀ y ∈ lpiv, d1 y < B ∧ kof G s (d1 y) = y := by
    intro y hy
    have hy' : y ∈ Finset.univ.image piv := by rw [← hlp]; exact List.mem_toFinset.mpr hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy'
    have hS : piv j ∈ S := (hfp.groups j).2 (hpiv j).1
    have hlt : d1 (piv j) < B := lt_of_le_of_lt (hfp.le _) (hpre.inRange _ hS)
    exact ⟨hlt, kof_of_walk hfp.walk (ne_top_of_lt hlt)⟩
  obtain ⟨hvi, hSi, hKi, hmi, hCCi, hTi⟩ :=
    insMany_sim (T := T) d1 lpiv g0 (newC (Mf (l + 1)) B) hSnew hK hlp'
  have hcs0 :
      ({ d := d1, P := P, piv := piv, U := ∅, B' := initB' B d1 piv,
         g := (initD (dlOps G s) T (Mf (l + 1)) B d1 lpiv g0).1,
         Dc := (initD (dlOps G s) T (Mf (l + 1)) B d1 lpiv g0).2.1 } : CSt G s p).lit =
        initState B d1 P piv := by
    show
      ({ d := d1, D := (insManyC (dlOps G s) T d1 lpiv g0 (newC (Mf (l + 1)) B)).1.view
           (insManyC (dlOps G s) T d1 lpiv g0 (newC (Mf (l + 1)) B)).2.1,
         P := P, piv := piv, U := ∅, B' := initB' B d1 piv } : LState G s p) = _
    rw [hvi, hvnew, hlp]; rfl
  have h0 := linv_init hpre hfp hpiv
  rw [← hcs0] at h0
  have hM0 : (initD (dlOps G s) T (Mf (l + 1)) B d1 lpiv g0).2.1.M = Mf (l + 1) := by
    show (insManyC (dlOps G s) T d1 lpiv g0 (newC (Mf (l + 1)) B)).2.1.M = _
    rw [insManyC_M]; rfl
  have hT0 : ∀ y, (initD (dlOps G s) T (Mf (l + 1)) B d1 lpiv g0).1.L y ≠ g0.L y →
      y ∈ (∅ : Finset (Fin G.n)) ∨ ∃ a, (initD (dlOps G s) T (Mf (l + 1)) B d1 lpiv g0).1.view
        (initD (dlOps G s) T (Mf (l + 1)) B d1 lpiv g0).2.1 y = some a ∧ a ≤ d0 y := by
    intro y hy
    have hyl := hTi y hy
    right
    refine ⟨d1 y, ?_, hfp.le y⟩
    show (insManyC (dlOps G s) T d1 lpiv g0 (newC (Mf (l + 1)) B)).1.view
      (insManyC (dlOps G s) T d1 lpiv g0 (newC (Mf (l + 1)) B)).2.1 y = some (d1 y)
    rw [hvi, hvnew, insertMany_apply, if_pos (List.mem_toFinset.mpr hyl)]
    rfl
  have hpsi0 : DL.psi (insManyC (dlOps G s) T d1 lpiv g0 (newC (Mf (l + 1)) B)).2.1 ≤
      Mf (l + 1) + 2 * lpiv.length := by
    have := insMany_psi (T := T) d1 lpiv g0 (newC (Mf (l + 1)) B) hSnew hK hlp'
    rw [psi_newC] at this
    exact this
  -- the loop
  have hB1 : DL.psi (initD (dlOps G s) T (Mf (l + 1)) B d1 lpiv g0).2.1 +
      2 * (Log.ownSum lgc + J.card + ∑ j, (P j).card + (S.card + L.length)) ≤
      2 * Mf (l + 1) + 2 * Emax (l + 1) := by
    have e : (initD (dlOps G s) T (Mf (l + 1)) B d1 lpiv g0).2.1 =
        (insManyC (dlOps G s) T d1 lpiv g0 (newC (Mf (l + 1)) B)).2.1 := rfl
    rw [e]; omega
  have hB2 : Log.ownSum lgc + J.card + ∑ j, (P j).card + (S.card + L.length) ≤ Emax (l + 1) := by
    omega
  obtain ⟨lgcC, cmC, cC, hloopC, hstripc, h, hstop, hI2, hS, hM, hKc, hCC, hT, hB1', hB2', hcostL⟩ :=
    loopD_tele (T := T) (DC := DC) (g0 := g0) hpre hfp hMpos h3M hsimsub hsimsubT hsubC hsubE hDC
      hIns hpullC hdelC hmergeC (S.card + L.length) 0 _ φ1 cs φ2 lgc J cm cl hloop h0 hI1 hSi hM0
      hKi hCCi hT0 hFc hB1 hB2
  rw [hcs0] at hloopC
  -- the finalization
  have hlT6' : ∀ y ∈ lT6, cs.d y < B ∧ kof G s (cs.d y) = y := by
    intro y hy
    have hlt := ((hT6 y).mp hy).2.2
    exact ⟨hlt, kof_of_walk h.walk (ne_top_of_lt hlt)⟩
  obtain ⟨hv6, hS6, hK6, hm6, hCC6, hTc6⟩ :=
    insMany_sim (T := T) cs.d lT6 cs.g cs.Dc hS hKc hlT6'
  obtain ⟨fd, fv, hSf, hKf, hmf, hCCf, hTf⟩ := fold_sim (T := T) (some B'f) L
    ⟨cs.d, (insManyC (dlOps G s) T cs.d lT6 cs.g cs.Dc).1,
      (insManyC (dlOps G s) T cs.d lT6 cs.g cs.Dc).2.1, 0⟩ hS6 hK6 h.walk
  have hlit6 : ((⟨cs.d, (insManyC (dlOps G s) T cs.d lT6 cs.g cs.Dc).1,
        (insManyC (dlOps G s) T cs.d lT6 cs.g cs.Dc).2.1, 0⟩ : RSt G s).d,
      (⟨cs.d, (insManyC (dlOps G s) T cs.d lT6 cs.g cs.Dc).1,
        (insManyC (dlOps G s) T cs.d lT6 cs.g cs.Dc).2.1, 0⟩ : RSt G s).g.view
        (⟨cs.d, (insManyC (dlOps G s) T cs.d lT6 cs.g cs.Dc).1,
          (insManyC (dlOps G s) T cs.d lT6 cs.g cs.Dc).2.1, 0⟩ : RSt G s).Dc) =
        (cs.d, insertMany G s cs.lit.D lT6.toFinset cs.d) := by
    show (cs.d, (insManyC (dlOps G s) T cs.d lT6 cs.g cs.Dc).1.view
      (insManyC (dlOps G s) T cs.d lT6 cs.g cs.Dc).2.1) = _
    rw [hv6]; rfl
  rw [hlit6] at fd fv
  set fw := L.foldl (relaxInsCc (dlOps G s) T B (some B'f))
    ⟨cs.d, (insManyC (dlOps G s) T cs.d lT6 cs.g cs.Dc).1,
      (insManyC (dlOps G s) T cs.d lT6 cs.g cs.Dc).2.1, 0⟩ with hfw
  obtain ⟨hvd, hSd, hKd, hfd, hLd⟩ := del_sim hSf hKf lW'
  have hres1 : res = (B'f, cs.U ∪ W', fw.Dc, fw.d) := hres
  have hgE1 : gE = (delC fw.g lW').1 := hgE
  have hlitres : res.lit gE = (B'f, cs.lit.U ∪ W',
      ((L.foldl (relaxIns G s B (some B'f)) (cs.lit.d, insertMany G s cs.lit.D lT6.toFinset
        cs.lit.d)).2).deleteSet W',
      (L.foldl (relaxIns G s B (some B'f)) (cs.lit.d, insertMany G s cs.lit.D lT6.toFinset
        cs.lit.d)).1) := by
    rw [hres1, hgE1]
    show (B'f, cs.U ∪ W', (delC fw.g lW').1.view fw.Dc, fw.d) = _
    rw [hvd, fv, fd, hlW]
    rfl
  refine ⟨([],
      { lvl := l + 1, Blow := Blow, B := B, S := S, B' := B'f, U := cs.lit.U ∪ W',
        base := false, p := p, Q := Q, W := W, W' := W', J := J, Wr := L.toFinset,
        fp := some ω, cFP := cfp, cMerge := cmC,
        cost := cfp + initCost DC (l + 1) p P + cC + cmC
          + finCost DC (l + 1) p P S W lT6.toFinset W' L.length }) :: lgcC,
    ⟨d1, p, P, Q, W, φ1, ω, cfp, piv, cs.lit, lgcC, J, cmC, cC, L, B'f, lT6.toFinset, W', hfprel,
      hpiv, hloopC, hB'e, hB'n, fun x => by rw [List.mem_toFinset]; exact hT6 x, hW', hL, hlitres,
      rfl⟩, ?_, hDP, ?_⟩
  · rw [hlg, Log.strip_cons, Log.strip_cons, hstripc]
    rfl
  · intro _ os hos hosnd
    -- (i) initialisation
    have ti : (insManyC (dlOps G s) T d1 lpiv g0 (newC (Mf (l + 1)) B)).2.2 +
        potG (insManyC (dlOps G s) T d1 lpiv g0 (newC (Mf (l + 1)) B)).1
          (insManyC (dlOps G s) T d1 lpiv g0 (newC (Mf (l + 1)) B)).2.1 +
        othP (insManyC (dlOps G s) T d1 lpiv g0 (newC (Mf (l + 1)) B)).1.L os ≤
        potG g0 (newC (Mf (l + 1)) B) + othP g0.L os + lpiv.length * DC.ins (l + 1) :=
      insMany_tele (T := T) d1 (Mlv := Mf (l + 1)) (P := 2 * Mf (l + 1) + 2 * Emax (l + 1)) hIns
        hosnd lpiv g0 (newC (Mf (l + 1)) B) hSnew hK hlp' rfl (by rw [psi_newC]; omega) hos
    rw [potG_newC] at ti
    -- (ii) the loop
    have tl : cl + cm + lgc.cost + potG cs.g cs.Dc + othP cs.g.L os ≤
        cC + cmC + lgcC.cost + potG (insManyC (dlOps G s) T d1 lpiv g0 (newC (Mf (l + 1)) B)).1
          (insManyC (dlOps G s) T d1 lpiv g0 (newC (Mf (l + 1)) B)).2.1 +
          othP (insManyC (dlOps G s) T d1 lpiv g0 (newC (Mf (l + 1)) B)).1.L os :=
      hcostL os hos hosnd
    -- (iii) the finalisation
    have hosc : ∀ x ∈ DB.allEnts os, x.id < cs.g.fresh :=
      fun x hx => lt_of_lt_of_le (hos x hx) hS.f0_le
    have t6 : (insManyC (dlOps G s) T cs.d lT6 cs.g cs.Dc).2.2 +
        potG (insManyC (dlOps G s) T cs.d lT6 cs.g cs.Dc).1
          (insManyC (dlOps G s) T cs.d lT6 cs.g cs.Dc).2.1 +
        othP (insManyC (dlOps G s) T cs.d lT6 cs.g cs.Dc).1.L os ≤
        potG cs.g cs.Dc + othP cs.g.L os + lT6.length * DC.ins (l + 1) :=
      insMany_tele (T := T) cs.d (Mlv := Mf (l + 1)) (P := 2 * Mf (l + 1) + 2 * Emax (l + 1)) hIns
        hosnd lT6 cs.g cs.Dc hS hKc hlT6' hM (by omega) hosc
    have hpsi6 := insMany_psi (T := T) cs.d lT6 cs.g cs.Dc hS hKc hlT6'
    have hos6 : ∀ x ∈ DB.allEnts os, x.id < (insManyC (dlOps G s) T cs.d lT6 cs.g cs.Dc).1.fresh :=
      fun x hx => lt_of_lt_of_le (hosc x hx) hm6
    have hM6 : (insManyC (dlOps G s) T cs.d lT6 cs.g cs.Dc).2.1.M = Mf (l + 1) := by
      rw [insManyC_M]; exact hM
    have tw : fw.c + potG fw.g fw.Dc + othP fw.g.L os ≤
        0 + potG (insManyC (dlOps G s) T cs.d lT6 cs.g cs.Dc).1
          (insManyC (dlOps G s) T cs.d lT6 cs.g cs.Dc).2.1 +
        othP (insManyC (dlOps G s) T cs.d lT6 cs.g cs.Dc).1.L os + L.length * (1 + DC.ins (l + 1)) :=
      fold_tele (T := T) (some B'f) (Mlv := Mf (l + 1)) (P := 2 * Mf (l + 1) + 2 * Emax (l + 1)) hIns
        hosnd L ⟨cs.d, (insManyC (dlOps G s) T cs.d lT6 cs.g cs.Dc).1,
          (insManyC (dlOps G s) T cs.d lT6 cs.g cs.Dc).2.1, 0⟩ hS6 hK6 h.walk hM6
        (by show DL.psi (insManyC (dlOps G s) T cs.d lT6 cs.g cs.Dc).2.1 + 2 * L.length ≤ _; omega)
        hos6
    have td := del_tele (g := fw.g) (Dc := fw.Dc) hSf.ids lW' hosnd
    rw [hW'len] at td
    -- (iv) the costs
    rw [hlg, Log.costT_cons, Log.costT_cons, hres1, hgE1]
    show cfp + ((insManyC (dlOps G s) T d1 lpiv g0 (newC (Mf (l + 1)) B)).2.2 + ∑ j, (P j).card
          + 2 * p) + cl + cm
        + (1 + S.card + W.card + W'.card + ∑ j, (P j).card
          + ((insManyC (dlOps G s) T cs.d lT6 cs.g cs.Dc).2.2 + fw.c + (delC fw.g lW').2))
        + lgc.cost + potG (delC fw.g lW').1 fw.Dc + othP (delC fw.g lW').1.L os ≤
      cfp + initCost DC (l + 1) p P + cC + cmC + finCost DC (l + 1) p P S W lT6.toFinset W' L.length
        + lgcC.cost + othP g0.L os
    unfold initCost finCost
    have hT6c : lT6.toFinset.card = lT6.length := List.toFinset_card_of_nodup hT6nd
    rw [hT6c]
    have hmul1 : lpiv.length * DC.ins (l + 1) ≤ p * DC.ins (l + 1) := Nat.mul_le_mul_right _ hlpiv
    have hmul2 : p * (2 + DC.ins (l + 1)) = 2 * p + p * DC.ins (l + 1) := by ring
    have hd := hdelC W'.card
    omega

end callT

/-! ## The heap base case, telescoped -/

section baseT

variable {Φ Ω : Type} {T : ℕ}

theorem eout_insert_le (U : Finset (Fin G.n)) (u : Fin G.n) (L : List (Fin G.m))
    (hL : Enumerates G L {u}) :
    (Finset.univ.filter fun e => G.src e ∈ insert u U).card ≤
      (Finset.univ.filter fun e => G.src e ∈ U).card + L.length := by
  classical
  have hsub : (Finset.univ.filter fun e => G.src e ∈ insert u U) ⊆
      (Finset.univ.filter fun e => G.src e ∈ U) ∪ L.toFinset := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at he
    rcases he with he | he
    · exact Finset.mem_union_right _ (List.mem_toFinset.mpr ((hL.2 e).mpr (by simp [he])))
    · exact Finset.mem_union_left _ (by simp [he])
  calc _ ≤ ((Finset.univ.filter fun e => G.src e ∈ U) ∪ L.toFinset).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter fun e => G.src e ∈ U).card + L.toFinset.card := Finset.card_union_le _ _
    _ = _ := by rw [List.toFinset_card_of_nodup hL.1]

/-- **Re-costing the literal base loop, quantitatively**: at a larger heap-insertion charge the
same run costs at most `(Δbins)·(new out-edges)` more. -/
theorem baseLoopC_recostN {DC1 DC2 : DCost} {B : WLab G s} {τ : ℕ} (hb : DC1.bins ≤ DC2.bins)
    (he : DC1.bext ≤ DC2.bext) :
    ∀ {st st' : Labels G s × DS G s × Finset (Fin G.n)} {c : ℕ},
      BaseLoopC G s DC1 B τ st st' c → ∃ c', BaseLoopC G s DC2 B τ st st' c' ∧
        c + (DC2.bins - DC1.bins) * (Finset.univ.filter fun e => G.src e ∈ st'.2.2).card ≤
          c' + (DC2.bins - DC1.bins) * (Finset.univ.filter fun e => G.src e ∈ st.2.2).card := by
  intro st st' c h
  induction h with
  | stop st hst => exact ⟨1, BaseLoopC.stop st hst, le_rfl⟩
  | step d D U u val L st' c hu hmin hcard hL _ ih =>
    obtain ⟨c', h', hc'⟩ := ih
    refine ⟨c' + 1 + DC2.bext + L.length * (1 + DC2.bins),
      BaseLoopC.step d D U u val L st' c' hu hmin hcard hL h', ?_⟩
    dsimp only at hc' ⊢
    set δ := DC2.bins - DC1.bins with hδ
    have hE := eout_insert_le U u L hL
    have k1 := Nat.mul_le_mul_left δ hE
    rw [Nat.mul_add] at k1
    have hb2 : DC2.bins = DC1.bins + δ := by omega
    have k2 : L.length * (1 + DC2.bins) = L.length * (1 + DC1.bins) + δ * L.length := by
      rw [hb2]; ring
    omega

theorem Eout_empty : (Finset.univ.filter fun e => G.src e ∈ (∅ : Finset (Fin G.n))).card = 0 := by
  simp

/-- **The heap base case, telescoped.** -/
theorem baseDH_tele {DCb DC : DCost} {τ : ℕ → ℕ} {Mf Emax : ℕ → ℕ} (hMpos : ∀ l, 1 ≤ Mf l)
    (hIns0 : ∀ D : DStrM G s, D.M = Mf 0 → DL.psi D ≤ 2 * Mf 0 + 2 * Emax 0 →
      insCharge D ≤ DC.ins 0)
    (hbins : DCb.bins + DC.ins 0 + 3 ≤ DC.bins) (hbext : DCb.bext ≤ DC.bext)
    {Blow B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} {φ0 φ1 : Φ} {g0 gE : DGl G s}
    {res : ResultD G s} {lg : Log G s Ω}
    (hpre : CallPre B S d0) (hK : DB.KeyInj g0.L (kof G s))
    (hab : ∀ v i a, g0.L v = some (i, a) → B ≤ a) (hSne : S.Nonempty)
    (hrel : BaseDH G s (dlOps G s) DCb T (Mf 0) Blow B S d0 φ0 g0 (τ 0) res φ1 gE lg) :
    ∃ lgC, BaseC G s DC Blow B S d0 φ0 (τ 0) (res.lit gE) φ1 lgC ∧ Log.strip lgC = Log.strip lg ∧
      DPost G s (dlOps G s) B d0 (Mf 0) g0 gE res ∧
      (Fits Emax lg → ∀ os : List (DB.Block (Fin G.n) (WLab G s)),
        (∀ x ∈ DB.allEnts os, x.id < g0.fresh) → ((DB.allEnts os).map (·.id)).Nodup →
        lg.cost + potG gE res.2.2.1 + othP gE.L os ≤ lgC.cost + othP g0.L os) := by
  classical
  obtain ⟨-, -, -, hDP⟩ := baseDH_sim (T := T) (DC := DC) hMpos hpre hK hab hrel
  obtain ⟨st, c, lK, hloop, hlKnd, hlK, hU, hd, hDc, hgE, hemp, hnemp, hφ, hlg⟩ := hrel
  obtain ⟨hB, -⟩ := baseLoop_inv hpre _ _ (baseLoopC_erase hloop) (bInv_init hpre)
  obtain ⟨c', hloop', hc'⟩ := baseLoopC_recostN (DC2 := DC) (by omega) hbext hloop
  dsimp only at hc'
  rw [Eout_empty, Nat.mul_zero, Nat.add_zero] at hc'
  obtain ⟨hSnew, hvnew⟩ := new_sim (ops := dlOps G s) (g := g0) (M := Mf 0) (B := B) (hMpos 0) hab
  have hlK' : ∀ y ∈ lK, st.1 y < B ∧ kof G s (st.1 y) = y := by
    intro y hy
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp ((hlK y).mp hy)
    obtain ⟨hkd, hkB⟩ := hB.stored y k hk
    rw [hkd] at hkB
    exact ⟨hkB, kof_of_walk hB.walk (ne_top_of_lt hkB)⟩
  obtain ⟨hvi, hSi, hKi, -, hCCi, hTi⟩ :=
    insMany_sim (T := T) st.1 lK g0 (newC (Mf 0) B) hSnew hK hlK'
  have hview : gE.view res.2.2.1 = st.2.1 := by
    rw [hDc, hgE, hvi, hvnew]; exact baseDH_conv hB hlK
  -- the leftover keys: frontier members or heads of out-edges of `U`
  have hkeys := baseLoopC_keys (S := S) hloop (by
    intro y hy
    left
    by_contra hyS
    apply hy
    show insertMany G s DS.empty S d0 y = none
    rw [insertMany_apply, if_neg hyS]
    rfl)
  have hlKlen : lK.length ≤ S.card + (Finset.univ.filter fun e => G.src e ∈ st.2.2).card := by
    rw [← List.toFinset_card_of_nodup hlKnd]
    calc lK.toFinset.card ≤ (S ∪ (Finset.univ.filter fun e => G.src e ∈ st.2.2).image G.dst).card := by
          apply Finset.card_le_card
          intro y hy
          rcases hkeys y ((hlK y).mp (List.mem_toFinset.mp hy)) with h1 | ⟨e, he, hey⟩
          · exact Finset.mem_union_left _ h1
          · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, by simp [he], hey⟩)
      _ ≤ S.card + ((Finset.univ.filter fun e => G.src e ∈ st.2.2).image G.dst).card :=
          Finset.card_union_le _ _
      _ ≤ S.card + (Finset.univ.filter fun e => G.src e ∈ st.2.2).card := by
          have := Finset.card_image_le (s := Finset.univ.filter fun e => G.src e ∈ st.2.2) (f := G.dst)
          omega
  refine ⟨[([],
      { lvl := 0, Blow := Blow, B := B, S := S, B' := (res.lit gE).1,
        U := (res.lit gE).2.1, base := true, p := 0, Q := ∅, W := ∅, W' := ∅, J := ∅, Wr := ∅,
        fp := none, cFP := 0, cMerge := 0, cost := S.card * (1 + DC.bins) + c' + 1 })],
    ⟨st, c', hloop', hU, hview, hd, hemp, hnemp, hφ, rfl⟩, by rw [hlg]; rfl, hDP, ?_⟩
  intro hF os hos hosnd
  -- the budget
  obtain ⟨R, hR, hRlvl, hRbase, hRS, hRU⟩ : ∃ R : CallRec G s Ω, lg = [([], R)] ∧
      R.lvl = 0 ∧ R.base = true ∧ R.S = S ∧ R.U = res.2.1 := ⟨_, hlg, rfl, rfl, rfl, rfl⟩
  have hF' : Fits Emax (([], R) :: ([] : Log G s Ω)) := hR ▸ hF
  have hroot := Fits.root hF'
  rw [Log.ownSum_cons, ownB_of_base R hRbase, hRS, hRU, hU, hRlvl] at hroot
  have hnil : Log.ownSum ([] : Log G s Ω) = 0 := rfl
  rw [hnil, Nat.add_zero] at hroot
  have ti : (insManyC (dlOps G s) T st.1 lK g0 (newC (Mf 0) B)).2.2 +
      potG (insManyC (dlOps G s) T st.1 lK g0 (newC (Mf 0) B)).1
        (insManyC (dlOps G s) T st.1 lK g0 (newC (Mf 0) B)).2.1 +
      othP (insManyC (dlOps G s) T st.1 lK g0 (newC (Mf 0) B)).1.L os ≤
      potG g0 (newC (Mf 0) B) + othP g0.L os + lK.length * DC.ins 0 :=
    insMany_tele (T := T) st.1 (Mlv := Mf 0) (P := 2 * Mf 0 + 2 * Emax 0) hIns0 hosnd lK g0
      (newC (Mf 0) B) hSnew hK hlK' rfl (by rw [psi_newC]; omega) hos
  rw [potG_newC] at ti
  rw [hlg, Log.costT_cons, Log.costT_cons, hDc, hgE]
  show S.card * (1 + DCb.bins) + c + 1 + (insManyC (dlOps G s) T st.1 lK g0 (newC (Mf 0) B)).2.2
      + Log.cost ([] : Log G s Ω) + potG (insManyC (dlOps G s) T st.1 lK g0 (newC (Mf 0) B)).1
        (insManyC (dlOps G s) T st.1 lK g0 (newC (Mf 0) B)).2.1
      + othP (insManyC (dlOps G s) T st.1 lK g0 (newC (Mf 0) B)).1.L os ≤
    S.card * (1 + DC.bins) + c' + 1 + Log.cost ([] : Log G s Ω) + othP g0.L os
  have hc0 : Log.cost ([] : Log G s Ω) = 0 := rfl
  rw [hc0]
  set EU := (Finset.univ.filter fun e => G.src e ∈ st.2.2).card with hEU
  set δ := DC.bins - DCb.bins with hδ
  have hS1 : 1 ≤ S.card := Finset.card_pos.mpr hSne
  have hb2 : DC.bins = DCb.bins + δ := by omega
  have k1 : S.card * (1 + DC.bins) = S.card * (1 + DCb.bins) + S.card * δ := by rw [hb2]; ring
  have k2 : (DC.ins 0 + 3) * (S.card + EU) ≤ δ * (S.card + EU) :=
    Nat.mul_le_mul_right _ (by omega)
  have k3 : lK.length * DC.ins 0 ≤ (S.card + EU) * DC.ins 0 := Nat.mul_le_mul_right _ hlKlen
  have k4 : δ * (S.card + EU) = S.card * δ + δ * EU := by ring
  have k5 : (DC.ins 0 + 3) * (S.card + EU) = (S.card + EU) * DC.ins 0 + 3 * S.card + 3 * EU := by ring
  omega

end baseT

/-! ## All levels -/

section levelsT

variable {Φ Ω : Type} {T : ℕ → ℕ}

/-- **Every concrete call over `DLazy`, telescoped** (all levels). -/
theorem bmsspD_tele {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} (hFPC : FPCSound G s FPC Inv)
    (τ : ℕ → ℕ) {Mf Emax : ℕ → ℕ} (hMpos : ∀ l, 1 ≤ Mf l) (h3M : ∀ l, 3 * Mf l ≤ Mf (l + 1))
    {DC DCb : DCost} (hDC : ∀ l, DC.M l = Mf l)
    (hIns : ∀ l, ∀ D : DStrM G s, D.M = Mf l → DL.psi D ≤ 2 * Mf l + 2 * Emax l →
      insCharge D ≤ DC.ins l)
    (hnewC : ∀ l, 3 ≤ DC.new (l + 1))
    (hpullC : ∀ l k, 735 * k + 950 ≤ DC.pull (l + 1) k)
    (hdelC : ∀ l k, 5 * k + 1 ≤ DC.del (l + 1) k) (hmergeC : ∀ l k, 14 ≤ DC.merge (l + 1) k)
    (hbins : DCb.bins + DC.ins 0 + 3 ≤ DC.bins) (hbext : DCb.bext ≤ DC.bext) :
    ∀ l, SimSubT G s τ Inv Mf Emax l (BMSSPD G s (dlOps G s) FPC DCb T Mf τ l)
      (BMSSPC G s FPC DC τ l)
  | 0 => by
    intro Blow B S d φ g res φ' g' lg hpre _ _ _ hK hab hSne hrel
    exact baseDH_tele (T := T 0) hMpos (hIns 0) hbins hbext hpre hK hab hSne hrel
  | l + 1 => by
    intro Blow B S d φ g res φ' g' lg hpre hI hlow _ hK hab _ hrel
    exact callD_tele (T := T (l + 1)) hFPC hMpos h3M
      (bmsspD_sim hFPC τ (fun _ => trivial) hMpos hDC l)
      (bmsspD_tele hFPC τ hMpos h3M hDC hIns hnewC hpullC hdelC hmergeC hbins hbext l)
      (bmsspC_log hFPC τ l) (bmsspD_place hFPC τ (fun _ => trivial) hMpos l) (hDC (l + 1))
      (hIns (l + 1)) (hnewC l) (hpullC l) (hdelC l) (hmergeC l) hpre hI hlow hK hab hrel

/-- **The top-level run over agent-04's DLazy costs at most the literal amortized cost.**  For any
cost parameters `DC` dominating the amortized charges (see the module header), a top-level run
from the initial labels and the empty global state whose log fits the budgets `Emax` has a
literal counterpart `lgC` (same stripped trace, a derivation of the cost-indexed literal relation)
with `lg.cost ≤ lgC.cost`. -/
theorem bmsspDL_tele_top {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} (hFPC : FPCSound G s FPC Inv)
    (τ : ℕ → ℕ) {Mf Emax : ℕ → ℕ} (hMpos : ∀ l, 1 ≤ Mf l) (h3M : ∀ l, 3 * Mf l ≤ Mf (l + 1))
    {DC DCb : DCost} (hDC : ∀ l, DC.M l = Mf l)
    (hIns : ∀ l, ∀ D : DStrM G s, D.M = Mf l → DL.psi D ≤ 2 * Mf l + 2 * Emax l →
      insCharge D ≤ DC.ins l)
    (hnewC : ∀ l, 3 ≤ DC.new (l + 1))
    (hpullC : ∀ l k, 735 * k + 950 ≤ DC.pull (l + 1) k)
    (hdelC : ∀ l k, 5 * k + 1 ≤ DC.del (l + 1) k) (hmergeC : ∀ l k, 14 ≤ DC.merge (l + 1) k)
    (hbins : DCb.bins + DC.ins 0 + 3 ≤ DC.bins) (hbext : DCb.bext ≤ DC.bext)
    (l : ℕ) {Blow : WLab G s} (hlow : Blow ≤ initLabels s s) {φ φ' : Φ} (hI : Inv φ)
    {res : ResultD G s} {gE : DGl G s} {lg : Log G s Ω}
    (hrel : BMSSPD G s (dlOps G s) FPC DCb T Mf τ l Blow ⊤ {s} (initLabels s) φ DGl.init res φ' gE lg)
    (hfits : Fits Emax lg) :
    ∃ lgC, BMSSPC G s FPC DC τ l Blow ⊤ {s} (initLabels s) φ (res.lit gE) φ' lgC ∧
      Log.strip lgC = Log.strip lg ∧ lg.cost ≤ lgC.cost := by
  have hlow' : ∀ x ∈ ({s} : Finset (Fin G.n)), Blow ≤ dis (s := s) x := by
    intro x hx
    rw [Finset.mem_singleton.mp hx, ← initLabels_source]
    exact hlow
  have hK0 : DB.KeyInj (DGl.init (G := G) (s := s)).L (kof G s) := by
    intro v i a h; simp [DGl.init] at h
  have hab0 : ∀ v i a, (DGl.init (G := G) (s := s)).L v = some (i, a) → (⊤ : WLab G s) ≤ a := by
    intro v i a h; simp [DGl.init] at h
  obtain ⟨lgC, hC, hstrip, -, hcost⟩ :=
    bmsspD_tele (T := T) hFPC τ hMpos h3M hDC hIns hnewC hpullC hdelC hmergeC hbins hbext l
      Blow ⊤ {s} (initLabels s) φ DGl.init res φ' gE lg callPre_top hI hlow' le_top hK0 hab0
      (Finset.singleton_nonempty s) hrel
  have h := hcost hfits [] (by simp [DB.allEnts]) (by simp [DB.allEnts])
  rw [othP_nil, othP_nil] at h
  exact ⟨lgC, hC, hstrip, by omega⟩


/-- **The top-level run over DLazy, with the budgets checked on the literal side**: if every literal
run of the top call fits the budgets (a statement about `BMSSPC` logs only, e.g. from agent-03's
trace-size sums), then the concrete run's actual cost is at most its literal twin's cost. -/
theorem bmsspDL_tele_top' {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} (hFPC : FPCSound G s FPC Inv)
    (τ : ℕ → ℕ) {Mf Emax : ℕ → ℕ} (hMpos : ∀ l, 1 ≤ Mf l) (h3M : ∀ l, 3 * Mf l ≤ Mf (l + 1))
    {DC DCb : DCost} (hDC : ∀ l, DC.M l = Mf l)
    (hIns : ∀ l, ∀ D : DStrM G s, D.M = Mf l → DL.psi D ≤ 2 * Mf l + 2 * Emax l →
      insCharge D ≤ DC.ins l)
    (hnewC : ∀ l, 3 ≤ DC.new (l + 1))
    (hpullC : ∀ l k, 735 * k + 950 ≤ DC.pull (l + 1) k)
    (hdelC : ∀ l k, 5 * k + 1 ≤ DC.del (l + 1) k) (hmergeC : ∀ l k, 14 ≤ DC.merge (l + 1) k)
    (hbins : DCb.bins + DC.ins 0 + 3 ≤ DC.bins) (hbext : DCb.bext ≤ DC.bext)
    (l : ℕ) {Blow : WLab G s} (hlow : Blow ≤ initLabels s s) {φ φ' : Φ} (hI : Inv φ)
    {res : ResultD G s} {gE : DGl G s} {lg : Log G s Ω}
    (hrel : BMSSPD G s (dlOps G s) FPC DCb T Mf τ l Blow ⊤ {s} (initLabels s) φ DGl.init res φ' gE lg)
    (hfitsC : ∀ lgC, BMSSPC G s FPC DC τ l Blow ⊤ {s} (initLabels s) φ (res.lit gE) φ' lgC →
      Fits Emax lgC) :
    ∃ lgC, BMSSPC G s FPC DC τ l Blow ⊤ {s} (initLabels s) φ (res.lit gE) φ' lgC ∧
      Log.strip lgC = Log.strip lg ∧ lg.cost ≤ lgC.cost := by
  have hlow' : ∀ x ∈ ({s} : Finset (Fin G.n)), Blow ≤ dis (s := s) x := by
    intro x hx
    rw [Finset.mem_singleton.mp hx, ← initLabels_source]
    exact hlow
  have hK0 : DB.KeyInj (DGl.init (G := G) (s := s)).L (kof G s) := by
    intro v i a h; simp [DGl.init] at h
  have hab0 : ∀ v i a, (DGl.init (G := G) (s := s)).L v = some (i, a) → (⊤ : WLab G s) ≤ a := by
    intro v i a h; simp [DGl.init] at h
  obtain ⟨lgC, hC, hstrip, -, hcost⟩ :=
    bmsspD_tele (T := T) hFPC τ hMpos h3M hDC hIns hnewC hpullC hdelC hmergeC hbins hbext l
      Blow ⊤ {s} (initLabels s) φ DGl.init res φ' gE lg callPre_top hI hlow' le_top hK0 hab0
      (Finset.singleton_nonempty s) hrel
  have hfits : Fits Emax lg := Fits.of_strip_eq hstrip (hfitsC lgC hC)
  have h := hcost hfits [] (by simp [DB.allEnts]) (by simp [DB.allEnts])
  rw [othP_nil, othP_nil] at h
  exact ⟨lgC, hC, hstrip, by omega⟩

end levelsT

end BM
end CHD
end Frontier
