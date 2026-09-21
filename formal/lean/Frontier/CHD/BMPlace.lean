import Frontier.CHD.BMLazy

/-!
# Frontier.CHD.BMPlace — entries placed into the lazy structures (O12 / (B4′) own-placement)

Owner: agent-01 (for agent-03's (B4′) trace-size lemma).  NON-GATE.

`E(Dc)` = number of entries (live or stale) of a structure.  Operations only ADD entries through
insertions (≤ 1 each) and merges (union); pulls and deletions never add.  For every run of the
concrete relation, the returned structure satisfies `E(Dc_X) ≤ Σ_{records of X's log} ownB`, with
`ownB r = p + |J| + 2|S| + |Wr|` (recursive) and `|S| + |Eout U|` (heap base case).
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}



/-- The own-placement bound of a call record. -/
noncomputable def ownB {Ω : Type} (r : CallRec G s Ω) : ℕ := by
  classical
  exact if r.base then r.S.card + (Finset.univ.filter fun e => G.src e ∈ r.U).card
    else r.p + r.J.card + 2 * r.S.card + r.Wr.card

/-- Sum of the own-placement bounds of a log. -/
noncomputable def Log.ownSum {Ω : Type} (lg : Log G s Ω) : ℕ := (lg.map fun x => ownB x.2).sum

theorem Log.ownSum_append {Ω : Type} (l1 l2 : Log G s Ω) :
    Log.ownSum (l1 ++ l2) = Log.ownSum l1 + Log.ownSum l2 := by
  unfold Log.ownSum; rw [List.map_append, List.sum_append]

theorem Log.ownSum_shift {Ω : Type} (i : ℕ) (lg : Log G s Ω) :
    Log.ownSum (Log.shift i lg) = Log.ownSum lg := by
  unfold Log.ownSum Log.shift; rw [List.map_map]; rfl

theorem Log.ownSum_cons {Ω : Type} (x : List ℕ × CallRec G s Ω) (lg : Log G s Ω) :
    Log.ownSum (x :: lg) = ownB x.2 + Log.ownSum lg := by
  unfold Log.ownSum; rw [List.map_cons, List.sum_cons]

theorem entCount_newC (M : ℕ) (Bd : WLab G s) : entCount (newC M Bd : DStrM G s) = 0 := by
  simp [entCount, newC, DB.allEnts]

section place

variable {ops : DOps G s} {Φ Ω : Type} {T : ℕ} {DC : DCost}
variable {B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {p : ℕ}
  {P0 : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {B'0 : WLab G s}

/-- Re-selections consume group members: the number of re-selected pivots of one iteration is at
most the decrease of `Σ_j |P_j|`. -/
theorem reselected_card_le (h : LInv G s B S d0 d1 P0 B'0 σ) (Ui : Finset (Fin G.n))
    (piv' : Fin p → Fin G.n) :
    (reselected σ Ui piv').card + ∑ j, (σ.P j \ Ui).card ≤ ∑ j, (σ.P j).card := by
  classical
  have h1 : (reselected σ Ui piv').card ≤ (markedGroups σ Ui).card := by
    have hsub : reselected σ Ui piv' ⊆ (markedGroups σ Ui).image piv' := by
      intro x hx
      obtain ⟨j, rfl, hj1, hj2⟩ := mem_reselected.mp hx
      exact Finset.mem_image.mpr ⟨j, by simp [markedGroups, hj1, hj2], rfl⟩
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  have h2 : ∀ j ∈ markedGroups σ Ui, (σ.P j \ Ui).card + 1 ≤ (σ.P j).card := by
    intro j hj
    simp only [markedGroups, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hpj : σ.piv j ∈ σ.P j := (h.pivots j (hj.2.mono Finset.sdiff_subset)).1
    have hss : σ.P j \ Ui ⊂ σ.P j := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, fun heq => ?_⟩
      have : σ.piv j ∈ σ.P j \ Ui := by rw [heq]; exact hpj
      exact (Finset.mem_sdiff.mp this).2 hj.1
    exact Finset.card_lt_card hss
  have h3 : ∀ j, (σ.P j \ Ui).card ≤ (σ.P j).card := fun j => Finset.card_le_card Finset.sdiff_subset
  have hsplit : ∑ j, (σ.P j).card =
      ∑ j ∈ markedGroups σ Ui, (σ.P j).card + ∑ j ∈ Finset.univ \ markedGroups σ Ui, (σ.P j).card := by
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  have hsplit' : ∑ j, (σ.P j \ Ui).card =
      ∑ j ∈ markedGroups σ Ui, (σ.P j \ Ui).card +
        ∑ j ∈ Finset.univ \ markedGroups σ Ui, (σ.P j \ Ui).card := by
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  have hm : (markedGroups σ Ui).card + ∑ j ∈ markedGroups σ Ui, (σ.P j \ Ui).card ≤
      ∑ j ∈ markedGroups σ Ui, (σ.P j).card := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j hj => by have := h2 j hj; omega
  have hr : ∑ j ∈ Finset.univ \ markedGroups σ Ui, (σ.P j \ Ui).card ≤
      ∑ j ∈ Finset.univ \ markedGroups σ Ui, (σ.P j).card :=
    Finset.sum_le_sum fun j _ => h3 j
  omega

/-- **Loop placement**: the entries of the loop's structure grow by at most the children's
placements, the window edges, and the consumed group members. -/
theorem loopD_place (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W)
    {τ : ℕ → ℕ} {Inv : Φ → Prop} {Mf : ℕ → ℕ}
    (hMf : ∀ l, ops.mergeM (Mf (l + 1)) (Mf l))
    {subD : SubRelD G s Φ Ω} {subC : SubRelC G s Φ Ω} {l : ℕ}
    (hsimsub : SimSub G s ops τ Inv Mf l subD subC) (hsubC : GoodSub G s τ Inv l subC)
    (hDC : DC.M (l + 1) = Mf (l + 1))
    (hsubE : ∀ Blow B S d φ g res φ' g' lg, CallPre B S d → Inv φ →
      (∀ x ∈ S, Blow ≤ dis (s := s) x) → Blow ≤ B → DB.KeyInj g.L (kof G s) →
      (∀ v i a, g.L v = some (i, a) → B ≤ a) → subD Blow B S d φ g res φ' g' lg →
      entCount res.2.2.1 ≤ Log.ownSum lg)
    {g0 : DGl G s} {τl : ℕ} :
    ∀ i (cs : CSt G s p) φ cs' φ' lg J cm c, LoopD G s ops T subD B τl i cs φ cs' φ' lg J cm c →
      LInv G s B S d0 d1 P0 B'0 cs.lit → Inv φ → SInv G s ops B g0.fresh cs.g cs.Dc →
      cs.Dc.M = Mf (l + 1) → DB.KeyInj cs.g.L (kof G s) → CallChange g0.fresh B g0.L cs.g.L →
      (∀ y, cs.g.L y ≠ g0.L y → y ∈ cs.U ∨ ∃ a, cs.g.view cs.Dc y = some a ∧ a ≤ d0 y) →
      entCount cs'.Dc + ∑ j, (cs'.P j).card ≤
          entCount cs.Dc + Log.ownSum lg + J.card + ∑ j, (cs.P j).card ∧
        (∀ e ∈ J, G.src e ∈ cs'.U ∧ G.src e ∉ cs.U) ∧ cs.U ⊆ cs'.U := by
  intro i cs φ cs' φ' lg J cm c hloop
  induction hloop with
  | stop i cs φ _ =>
    intro _ _ _ _ _ _ _
    refine ⟨by simp [Log.ownSum], by simp, subset_rfl⟩
  | step i cs cs' φ φ1 φ' ks Bi g1 Dc1 cp B'i Ui Dci d1' g2 lUi L' piv' lres lg lg' J' cm c
      hcard hne hpull hsubD hlUnd hlU hnd hmem hres hlresnd hlres _ ih =>
    intro h hI hS hMc hK hCC hT
    classical
    obtain ⟨-, -, -, -, -, -, -, hnext', hI1, hSn', hMn', hKn', hCCn', hTn', -, hUi_disj, -, hent⟩ :=
      stepD_inv (T := T) (DC := DC) (g0 := g0) hpre hfp hMf hsimsub hsubC hDC h hI hS hMc hK hCC hT
        hne hpull hsubD hlU hnd hmem hres hlres
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
    -- the rest of the loop
    obtain ⟨ihE, ihJ, ihU⟩ := ih hnext' hI1 hSn' hMn' hKn' hCCn' hTn'
    -- re-selections
    have hres_card := reselected_card_le h Ui piv'
    have hlres_len : lres.length = (reselected cs.lit Ui piv').card := by
      rw [← hlres, List.toFinset_card_of_nodup hlresnd]
    have hL'len : L'.length = L'.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    -- disjointness of the window edges
    have hdisj : Disjoint L'.toFinset J' := by
      rw [Finset.disjoint_left]
      intro e he he'
      have hsrc : G.src e ∈ Ui := ((hmem e).mp (List.mem_toFinset.mp he)).1
      have := (ihJ e he').2
      exact this (Finset.mem_union_right _ hsrc)
    have hPn : ∑ j, ((nextD ops T B cs Bi B'i Ui Dc1 Dci d1' g2 lUi L' piv' lres).P j).card =
        ∑ j, (cs.lit.P j \ Ui).card := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [Finset.card_union_of_disjoint hdisj, Log.ownSum_append, Log.ownSum_shift]
      have hsumP : ∑ j, (cs.P j).card = ∑ j, (cs.lit.P j).card := rfl
      omega
    · intro e he
      rcases Finset.mem_union.mp he with he | he
      · have hsrc : G.src e ∈ Ui := ((hmem e).mp (List.mem_toFinset.mp he)).1
        exact ⟨ihU (Finset.mem_union_right _ hsrc),
          fun hc => Finset.disjoint_left.mp hUi_disj hsrc hc⟩
      · obtain ⟨h1, h2⟩ := ihJ e he
        exact ⟨h1, fun hc => h2 (Finset.mem_union_left _ hc)⟩
    · exact Finset.subset_union_left.trans ihU

end place


section place2

variable {ops : DOps G s} {Φ Ω : Type} {T : ℕ} {DC : DCost}

theorem card_groups_le {p : ℕ} {P : Fin p → Finset (Fin G.n)} {S : Finset (Fin G.n)}
    (hg : ∀ j, (P j).Nonempty ∧ P j ⊆ S) (hd : ∀ i j, i ≠ j → Disjoint (P i) (P j)) :
    ∑ j, (P j).card ≤ S.card := by
  classical
  rw [← Finset.card_biUnion (fun i _ j _ hij => hd i j hij)]
  exact Finset.card_le_card (Finset.biUnion_subset.mpr fun j _ => (hg j).2)

/-- **Call placement.** -/
theorem callD_place {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} (hFPC : FPCSound G s FPC Inv)
    {τ : ℕ → ℕ} {Mf : ℕ → ℕ} (hMf : ∀ l, ops.mergeM (Mf (l + 1)) (Mf l)) (hM1 : ∀ l, 1 ≤ Mf l)
    {subD : SubRelD G s Φ Ω} {subC : SubRelC G s Φ Ω} {l : ℕ}
    (hsimsub : SimSub G s ops τ Inv Mf l subD subC) (hsubC : GoodSub G s τ Inv l subC)
    (hDC : DC.M (l + 1) = Mf (l + 1))
    (hsubE : ∀ Blow B S d φ g res φ' g' lg, CallPre B S d → Inv φ →
      (∀ x ∈ S, Blow ≤ dis (s := s) x) → Blow ≤ B → DB.KeyInj g.L (kof G s) →
      (∀ v i a, g.L v = some (i, a) → B ≤ a) → subD Blow B S d φ g res φ' g' lg →
      entCount res.2.2.1 ≤ Log.ownSum lg)
    {Blow B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} {φ0 φ2 : Φ} {g0 gE : DGl G s}
    {res : ResultD G s} {lg : Log G s Ω}
    (hpre : CallPre B S d0) (hI : Inv φ0) (hlow : ∀ x ∈ S, Blow ≤ dis (s := s) x)
    (hK : DB.KeyInj g0.L (kof G s)) (hab : ∀ v i a, g0.L v = some (i, a) → B ≤ a)
    (hrel : CallD G s ops FPC T Mf subD (l + 1) Blow B S d0 φ0 g0 (τ (l + 1)) res φ2 gE lg) :
    entCount res.2.2.1 ≤ Log.ownSum lg := by
  classical
  obtain ⟨d1, p, P, Q, W, φ1, ω, cfp, piv, lpiv, cs, lgc, J, cm, cl, L, B'f, lT6, W', lW', hfprel,
    hpiv, hlpnd, hlp, hloop, hB'e, hB'n, hT6nd, hT6, hW', hL, hlWnd, hlW, hres, hgE, hlg⟩ := hrel
  have hlow' : ∀ x ∈ S, Blow ≤ d0 x := fun x hx => (hlow x hx).trans (hpre.walk.sound x)
  obtain ⟨hfp, hI1⟩ := hFPC _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpre hI hlow' hfprel
  obtain ⟨hSnew, hvnew⟩ := new_sim (ops := ops) (g := g0) (M := Mf (l + 1)) (B := B) (hM1 _) hab
  have hlp' : ∀ y ∈ lpiv, d1 y < B ∧ kof G s (d1 y) = y := by
    intro y hy
    have hy' : y ∈ Finset.univ.image piv := by rw [← hlp]; exact List.mem_toFinset.mpr hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy'
    have hS : piv j ∈ S := (hfp.groups j).2 (hpiv j).1
    have hlt : d1 (piv j) < B := lt_of_le_of_lt (hfp.le _) (hpre.inRange _ hS)
    exact ⟨hlt, kof_of_walk hfp.walk (ne_top_of_lt hlt)⟩
  obtain ⟨hvi, hSi, hKi, -, hCCi, hTi⟩ :=
    insMany_sim (T := T) d1 lpiv g0 (newC (Mf (l + 1)) B) hSnew hK hlp'
  have hE0 : entCount (insManyC ops T d1 lpiv g0 (newC (Mf (l + 1)) B)).2.1 ≤ lpiv.length := by
    have := insMany_ent_le (T := T) d1 lpiv g0 (newC (Mf (l + 1)) B) hSnew hK hlp'
    rw [entCount_newC] at this; omega
  have hcs0 :
      ({ d := d1, P := P, piv := piv, U := ∅, B' := initB' B d1 piv,
         g := (initD ops T (Mf (l + 1)) B d1 lpiv g0).1,
         Dc := (initD ops T (Mf (l + 1)) B d1 lpiv g0).2.1 } : CSt G s p).lit =
        initState B d1 P piv := by
    show
      ({ d := d1, D := (insManyC ops T d1 lpiv g0 (newC (Mf (l + 1)) B)).1.view
           (insManyC ops T d1 lpiv g0 (newC (Mf (l + 1)) B)).2.1,
         P := P, piv := piv, U := ∅, B' := initB' B d1 piv } : LState G s p) = _
    rw [hvi, hvnew, hlp]; rfl
  have h0 := linv_init hpre hfp hpiv
  rw [← hcs0] at h0
  have hM0 : (initD ops T (Mf (l + 1)) B d1 lpiv g0).2.1.M = Mf (l + 1) := by
    show (insManyC ops T d1 lpiv g0 (newC (Mf (l + 1)) B)).2.1.M = _
    rw [insManyC_M]; rfl
  have hT0 : ∀ y, (initD ops T (Mf (l + 1)) B d1 lpiv g0).1.L y ≠ g0.L y →
      y ∈ (∅ : Finset (Fin G.n)) ∨ ∃ a, (initD ops T (Mf (l + 1)) B d1 lpiv g0).1.view
        (initD ops T (Mf (l + 1)) B d1 lpiv g0).2.1 y = some a ∧ a ≤ d0 y := by
    intro y hy
    have hyl := hTi y hy
    right
    refine ⟨d1 y, ?_, hfp.le y⟩
    show (insManyC ops T d1 lpiv g0 (newC (Mf (l + 1)) B)).1.view
      (insManyC ops T d1 lpiv g0 (newC (Mf (l + 1)) B)).2.1 y = some (d1 y)
    rw [hvi, hvnew, insertMany_apply, if_pos (List.mem_toFinset.mpr hyl)]
    rfl
  obtain ⟨-, -, -, -, -, h, -, -, hS, -, hKc, -, -⟩ :=
    loopD_sim (T := T) (DC := DC) (g0 := g0) hpre hfp hMf hsimsub hsubC hDC 0 _ φ1 cs φ2 lgc J cm cl
      hloop h0 hI1 hSi hM0 hKi hCCi hT0
  obtain ⟨hE, -, -⟩ := loopD_place (T := T) (DC := DC) (g0 := g0) hpre hfp hMf hsimsub hsubC hDC hsubE
    0 _ φ1 cs φ2 lgc J cm cl hloop h0 hI1 hSi hM0 hKi hCCi hT0
  -- finalization
  have hlT6' : ∀ y ∈ lT6, cs.d y < B ∧ kof G s (cs.d y) = y := by
    intro y hy
    have hlt := ((hT6 y).mp hy).2.2
    exact ⟨hlt, kof_of_walk h.walk (ne_top_of_lt hlt)⟩
  obtain ⟨-, hS6, hK6, -⟩ := insMany_sim (T := T) cs.d lT6 cs.g cs.Dc hS hKc hlT6'
  have hE6 := insMany_ent_le (T := T) cs.d lT6 cs.g cs.Dc hS hKc hlT6'
  have hEf := fold_ent_le (T := T) (some B'f) L
    ⟨cs.d, (insManyC ops T cs.d lT6 cs.g cs.Dc).1, (insManyC ops T cs.d lT6 cs.g cs.Dc).2.1, 0⟩ hS6 hK6
    h.walk
  have hres1 : res.2.2.1 = (L.foldl (relaxInsCc ops T B (some B'f))
      ⟨cs.d, (insManyC ops T cs.d lT6 cs.g cs.Dc).1, (insManyC ops T cs.d lT6 cs.g cs.Dc).2.1, 0⟩).Dc := by
    rw [hres]; rfl
  -- counting
  have hlpiv : lpiv.length ≤ p := by
    rw [← List.toFinset_card_of_nodup hlpnd, hlp]
    exact Finset.card_image_le.trans (by simp)
  have hPS : ∑ j, (P j).card ≤ S.card := card_groups_le hfp.groups hfp.gdisj
  have hT6len : lT6.length ≤ S.card := by
    rw [← List.toFinset_card_of_nodup hT6nd]
    exact Finset.card_le_card (fun x hx => ((hT6 x).mp (List.mem_toFinset.mp hx)).1)
  have hLlen : L.length = L.toFinset.card := (List.toFinset_card_of_nodup hL.1).symm
  have hownB : ownB
      ({ lvl := l + 1, Blow := Blow, B := B, S := S, B' := B'f, U := cs.U ∪ W',
         base := false, p := p, Q := Q, W := W, W' := W', J := J, Wr := L.toFinset,
         fp := some ω, cFP := cfp, cMerge := cm,
         cost := cfp + ((initD ops T (Mf (l + 1)) B d1 lpiv g0).2.2 + ∑ j, (P j).card + 2 * p)
           + cl + cm + (1 + S.card + W.card + W'.card + ∑ j, (P j).card
             + (finD ops T B B'f cs.d cs.g cs.Dc lT6 L lW').2.2.2) } : CallRec G s Ω) =
      p + J.card + 2 * S.card + L.toFinset.card := by
    simp [ownB]
  rw [hlg, Log.ownSum_cons, hownB, hres1]
  have hE' : entCount cs.Dc + ∑ j, (cs.P j).card ≤
      entCount (initD ops T (Mf (l + 1)) B d1 lpiv g0).2.1 + Log.ownSum lgc + J.card +
        ∑ j, (P j).card := hE
  have hE0' : entCount (initD ops T (Mf (l + 1)) B d1 lpiv g0).2.1 ≤ lpiv.length := hE0
  have hEf' : entCount (L.foldl (relaxInsCc ops T B (some B'f))
      ⟨cs.d, (insManyC ops T cs.d lT6 cs.g cs.Dc).1, (insManyC ops T cs.d lT6 cs.g cs.Dc).2.1, 0⟩).Dc ≤
      entCount (insManyC ops T cs.d lT6 cs.g cs.Dc).2.1 + L.length := hEf
  omega

/-- Keys of a relaxation scan: old keys or heads of scanned edges. -/
theorem foldl_relaxIns_keys_sub (B : WLab G s) (lo : Option (WLab G s)) :
    ∀ (L : List (Fin G.m)) (st : Labels G s × DS G s) (y : Fin G.n),
      (L.foldl (relaxIns G s B lo) st).2 y ≠ none → st.2 y ≠ none ∨ ∃ e ∈ L, G.dst e = y := by
  intro L
  induction L with
  | nil => intro st y h; exact Or.inl h
  | cons e L ih =>
    intro st y h
    rw [List.foldl_cons] at h
    rcases ih _ y h with h1 | ⟨e', he', he'y⟩
    · have hstep : (relaxIns G s B lo st e).2 y ≠ none → st.2 y ≠ none ∨ G.dst e = y := by
        intro hy
        unfold relaxIns at hy
        split_ifs at hy with hv
        · by_cases hye : y = G.dst e
          · exact Or.inr hye.symm
          · left
            have hins : (st.2.insert (G.dst e) (ext (st.1 (G.src e)) e)) y = st.2 y := by
              unfold DS.insert; rw [Function.update_of_ne hye]
            cases lo with
            | none => simp only at hy; rw [hins] at hy; exact hy
            | some b =>
              simp only at hy
              split_ifs at hy
              · rw [hins] at hy; exact hy
              · exact hy
        · exact Or.inl hy
      rcases hstep h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr ⟨e, List.mem_cons_self, h2⟩
    · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', he'y⟩

/-- Keys of the literal base loop: frontier vertices or heads of out-edges of extracted vertices. -/
theorem baseLoopC_keys {DCb : DCost} {B : WLab G s} {τ : ℕ} {S : Finset (Fin G.n)} :
    ∀ {st st' : Labels G s × DS G s × Finset (Fin G.n)} {c : ℕ},
      BaseLoopC G s DCb B τ st st' c →
      (∀ y, st.2.1 y ≠ none → y ∈ S ∨ ∃ e, G.src e ∈ st.2.2 ∧ G.dst e = y) →
      ∀ y, st'.2.1 y ≠ none → y ∈ S ∨ ∃ e, G.src e ∈ st'.2.2 ∧ G.dst e = y := by
  intro st st' c h
  induction h with
  | stop st _ => exact fun h => h
  | step d D U u val L st' c _ _ _ hL _ ih =>
    intro hk
    apply ih
    intro y hy
    rcases foldl_relaxIns_keys_sub B none L (d, D.deleteSet {u}) y hy with h1 | ⟨e, he, hey⟩
    · have h1' : D y ≠ none := by
        by_cases hyu : y ∈ ({u} : Finset (Fin G.n))
        · simp [DS.deleteSet, hyu] at h1
        · simpa [DS.deleteSet, hyu] using h1
      rcases hk y h1' with h2 | ⟨e, he, hey⟩
      · exact Or.inl h2
      · exact Or.inr ⟨e, Finset.mem_insert_of_mem he, hey⟩
    · have hsrc : G.src e = u := by
        have := (hL.2 e).mp he
        simpa using this
      exact Or.inr ⟨e, by rw [hsrc]; exact Finset.mem_insert_self _ _, hey⟩

/-- **Heap base-case placement.** -/
theorem baseDH_place {DCb : DCost} {τ : ℕ → ℕ} {Mf : ℕ → ℕ} (hM1 : ∀ l, 1 ≤ Mf l)
    {Blow B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} {φ0 φ1 : Φ} {g0 gE : DGl G s}
    {res : ResultD G s} {lg : Log G s Ω}
    (hpre : CallPre B S d0) (hK : DB.KeyInj g0.L (kof G s))
    (hab : ∀ v i a, g0.L v = some (i, a) → B ≤ a)
    (hrel : BaseDH G s ops DCb T (Mf 0) Blow B S d0 φ0 g0 (τ 0) res φ1 gE lg) :
    entCount res.2.2.1 ≤ Log.ownSum lg := by
  classical
  obtain ⟨st, c, lK, hloop, hlKnd, hlK, hU, hd, hDc, hgE, hemp, hnemp, hφ, hlg⟩ := hrel
  obtain ⟨hB, -⟩ := baseLoop_inv hpre _ _ (baseLoopC_erase hloop) (bInv_init hpre)
  obtain ⟨hSnew, -⟩ := new_sim (ops := ops) (g := g0) (M := Mf 0) (B := B) (hM1 0) hab
  have hlK' : ∀ y ∈ lK, st.1 y < B ∧ kof G s (st.1 y) = y := by
    intro y hy
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp ((hlK y).mp hy)
    obtain ⟨hkd, hkB⟩ := hB.stored y k hk
    rw [hkd] at hkB
    exact ⟨hkB, kof_of_walk hB.walk (ne_top_of_lt hkB)⟩
  have hEc := insMany_ent_le (T := T) st.1 lK g0 (newC (Mf 0) B) hSnew hK hlK'
  rw [entCount_newC] at hEc
  have hkeys := baseLoopC_keys (S := S) hloop (by
    intro y hy
    change insertMany G s DS.empty S d0 y ≠ none at hy
    rw [insertMany_empty_apply] at hy
    split_ifs at hy with hyS
    · exact Or.inl hyS
    · exact absurd rfl hy)
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
  rw [hlg, Log.ownSum_cons, hDc]
  have hownB : ownB
      ({ lvl := 0, Blow := Blow, B := B, S := S, B' := res.1, U := res.2.1,
         base := true, p := 0, Q := ∅, W := ∅, W' := ∅, J := ∅, Wr := ∅,
         fp := none, cFP := 0, cMerge := 0,
         cost := S.card * (1 + DCb.bins) + c + 1
           + (insManyC ops T st.1 lK g0 (newC (Mf 0) B)).2.2 } : CallRec G s Ω) =
      S.card + (Finset.univ.filter fun e => G.src e ∈ res.2.1).card := by
    simp [ownB]
  rw [hownB, hU]
  simp only [Log.ownSum, List.map_nil, List.sum_nil, add_zero]
  omega

end place2

section place3

variable {ops : DOps G s} {Φ Ω : Type} {T : ℕ → ℕ} {DCb : DCost}

/-- **Own-placement for every run** (O12 / (B4′) input): the returned structure's entries are
bounded by the log's own-placement sum. -/
theorem bmsspD_place {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} (hFPC : FPCSound G s FPC Inv)
    (τ : ℕ → ℕ) {Mf : ℕ → ℕ} (hMf : ∀ l, ops.mergeM (Mf (l + 1)) (Mf l)) (hM1 : ∀ l, 1 ≤ Mf l) :
    ∀ l Blow B S d φ g res φ' g' (lg : Log G s Ω), CallPre B S d → Inv φ →
      (∀ x ∈ S, Blow ≤ dis (s := s) x) → Blow ≤ B → DB.KeyInj g.L (kof G s) →
      (∀ v i a, g.L v = some (i, a) → B ≤ a) →
      BMSSPD G s ops FPC DCb T Mf τ l Blow B S d φ g res φ' g' lg → entCount res.2.2.1 ≤ Log.ownSum lg
  | 0 => by
    intro Blow B S d φ g res φ' g' lg hpre _ _ _ hK hab hrel
    exact baseDH_place (T := T 0) hM1 hpre hK hab hrel
  | l + 1 => by
    intro Blow B S d φ g res φ' g' lg hpre hI hlow _ hK hab hrel
    let DC0 : DCost := ⟨Mf, fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, 0, 0⟩
    exact callD_place (T := T (l + 1)) (DC := DC0) hFPC hMf hM1
      (bmsspD_sim (DC := DC0) (DCb := DCb) hFPC τ hMf hM1 (fun _ => rfl) l) (bmsspC_log hFPC τ l) rfl
      (bmsspD_place hFPC τ hMf hM1 l) hpre hI hlow hK hab hrel

end place3

end BM
end CHD
end Frontier
