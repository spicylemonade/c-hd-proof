import Frontier.CHD.BMTrace
import Frontier.CHD.FPBind

/-!
# Frontier.CHD.LoopCost — the per-iteration cost of the BMSSP main loop (tracker O10; owner agent-03)

**NON-GATE** (Layer A, cost side).  Combinatorial facts about one iteration of `BM.LoopC` (BM.9–BM.24) that bound
`iterCost` by the per-call budget of `CostAggregate.Valid.cost_le`:
* marked groups (BM.16–18/BM.23) are groups whose ORIGINAL pivot set meets the child's returned set `U_i`;
* pulled groups (BM.11–12) inject into the pulled keys (their pivots);
* with a FULL child, a pulled group is marked or emptied in that iteration (its pivot returns in `U_i`).
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

section Groups

variable {p : ℕ} (σ : LState G s p) (P0 : Fin p → Finset (Fin G.n))

/-- **Marked groups meet the child's set** through their original pivot set. -/
theorem marked_sub_meeting (hsub : ∀ j, σ.P j ⊆ P0 j)
    (hpiv : ∀ j, (σ.P j).Nonempty → σ.piv j ∈ σ.P j) (Ui : Finset (Fin G.n)) :
    markedGroups σ Ui ⊆ Finset.univ.filter (fun j => (P0 j ∩ Ui).Nonempty) := by
  classical
  intro j hj
  simp only [markedGroups, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  obtain ⟨hpU, hne⟩ := hj
  have hPne : (σ.P j).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, (Finset.mem_sdiff.mp hx).1⟩
  exact ⟨σ.piv j, Finset.mem_inter.mpr ⟨hsub j (hpiv j hPne), hpU⟩⟩

/-- **Pulled groups inject into the pulled keys** (groups are disjoint; a pulled group's pivot is a member). -/
theorem card_pulled_le (hdisj : ∀ i j, i ≠ j → Disjoint (σ.P i) (σ.P j)) (S0 : Finset (Fin G.n)) :
    (pulledGroups σ S0).card ≤ S0.card := by
  classical
  refine Finset.card_le_card_of_injOn (fun j => σ.piv j) ?_ ?_
  · intro j hj
    simp only [pulledGroups, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj
    exact hj.1
  · intro i hi j hj hij
    simp only [pulledGroups, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi hj
    by_contra hne
    have hij' : σ.piv i = σ.piv j := hij
    exact Finset.disjoint_left.mp (hdisj i j hne) hi.2 (by rw [hij']; exact hj.2)

/-- Groups emptied in an iteration: nonempty before, contained in the child's set. -/
noncomputable def emptiedGroups (Ui : Finset (Fin G.n)) : Finset (Fin p) := by
  classical
  exact Finset.univ.filter (fun j => (σ.P j).Nonempty ∧ σ.P j ⊆ Ui)

/-- **Full child**: every pulled group is marked or emptied (its pivot returns in `U_i`). -/
theorem pulled_sub_marked_emptied {S0 Ui : Finset (Fin G.n)} (hS0 : S0 ⊆ Ui) :
    pulledGroups σ S0 ⊆ markedGroups σ Ui ∪ emptiedGroups σ Ui := by
  classical
  intro j hj
  simp only [pulledGroups, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  obtain ⟨hpS, hpP⟩ := hj
  by_cases hne : (σ.P j \ Ui).Nonempty
  · exact Finset.mem_union_left _ (by simp [markedGroups, hS0 hpS, hne])
  · refine Finset.mem_union_right _ ?_
    simp only [emptiedGroups, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨_, hpP⟩, fun x hx => ?_⟩
    by_contra hxU
    exact hne ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxU⟩⟩

/-- Nonempty groups after the iteration (`P' j = P j \ U_i`): the emptied ones are gone. -/
theorem card_nonempty_next (Ui : Finset (Fin G.n)) :
    (Finset.univ.filter (fun j => (σ.P j \ Ui).Nonempty)).card + (emptiedGroups σ Ui).card ≤
      (Finset.univ.filter (fun j => (σ.P j).Nonempty)).card := by
  classical
  rw [← Finset.card_union_of_disjoint]
  · refine Finset.card_le_card (fun j hj => ?_)
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, emptiedGroups] at hj ⊢
    rcases hj with ⟨x, hx⟩ | ⟨h, -⟩
    · exact ⟨x, (Finset.mem_sdiff.mp hx).1⟩
    · exact h
  · rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, emptiedGroups] at h1 h2
    obtain ⟨x, hx⟩ := h1
    exact (Finset.mem_sdiff.mp hx).2 (h2.2 (Finset.mem_sdiff.mp hx).1)

end Groups

section Iter

variable {p : ℕ} {σ : LState G s p}

/-- Pulled-group expansion cost, full child (`S0 ⊆ U_i`): charged to markings and emptied groups. -/
theorem pulled_sum_full {g : ℕ} (hg : ∀ j, (σ.P j).card ≤ g) {S0 Ui : Finset (Fin G.n)} (hS0 : S0 ⊆ Ui) :
    ∑ j ∈ pulledGroups σ S0, (σ.P j).card ≤ g * ((markedGroups σ Ui).card + (emptiedGroups σ Ui).card) := by
  classical
  calc ∑ j ∈ pulledGroups σ S0, (σ.P j).card ≤ ∑ j ∈ pulledGroups σ S0, g := Finset.sum_le_sum (fun j _ => hg j)
    _ = (pulledGroups σ S0).card * g := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (markedGroups σ Ui ∪ emptiedGroups σ Ui).card * g :=
        Nat.mul_le_mul_right _ (Finset.card_le_card (pulled_sub_marked_emptied σ hS0))
    _ ≤ ((markedGroups σ Ui).card + (emptiedGroups σ Ui).card) * g :=
        Nat.mul_le_mul_right _ (Finset.card_union_le _ _)
    _ = g * ((markedGroups σ Ui).card + (emptiedGroups σ Ui).card) := Nat.mul_comm _ _

/-- Pulled-group expansion cost, any child: at most `g` per pulled key. -/
theorem pulled_sum_le {g : ℕ} (hg : ∀ j, (σ.P j).card ≤ g)
    (hdisj : ∀ i j, i ≠ j → Disjoint (σ.P i) (σ.P j)) (S0 : Finset (Fin G.n)) :
    ∑ j ∈ pulledGroups σ S0, (σ.P j).card ≤ g * S0.card := by
  classical
  calc ∑ j ∈ pulledGroups σ S0, (σ.P j).card ≤ ∑ j ∈ pulledGroups σ S0, g := Finset.sum_le_sum (fun j _ => hg j)
    _ = (pulledGroups σ S0).card * g := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ S0.card * g := Nat.mul_le_mul_right _ (card_pulled_le σ hdisj S0)
    _ = g * S0.card := Nat.mul_comm _ _

/-- **One iteration's cost** in the per-call budget's shape. -/
theorem iterCost_le {DC : DCost} {lv : ℕ} {S0 Ui : Finset (Fin G.n)} {nL : ℕ}
    {ap bp ad bd I g m : ℕ}
    (hpull : DC.pull lv S0.card ≤ ap * S0.card + bp)
    (hdel : DC.del lv Ui.card ≤ ad * Ui.card + bd)
    (hins : DC.ins lv ≤ I) (hg : ∀ j, (σ.P j).card ≤ g) (hS0 : S0.card ≤ Ui.card)
    (hpulled : ∑ j ∈ pulledGroups σ S0, (σ.P j).card ≤
      Ui.card + g * ((markedGroups σ Ui).card + (emptiedGroups σ Ui).card))
    (hmk : (markedGroups σ Ui).card ≤ m) :
    iterCost DC lv σ S0 Ui nL ≤ (1 + bp + bd) + (ap + ad + 4) * Ui.card + (1 + I) * nL +
      (2 * g + 1 + I) * m + g * (emptiedGroups σ Ui).card := by
  classical
  unfold iterCost
  have hmarked : ∑ j ∈ markedGroups σ Ui, ((σ.P j \ Ui).card + 1 + DC.ins lv) ≤
      (markedGroups σ Ui).card * (g + 1 + I) := by
    calc ∑ j ∈ markedGroups σ Ui, ((σ.P j \ Ui).card + 1 + DC.ins lv)
        ≤ ∑ j ∈ markedGroups σ Ui, (g + 1 + I) := Finset.sum_le_sum (fun j _ => by
          have := Finset.card_le_card (Finset.sdiff_subset (s := σ.P j) (t := Ui))
          have := hg j
          omega)
      _ = (markedGroups σ Ui).card * (g + 1 + I) := by rw [Finset.sum_const, smul_eq_mul]
  have h1 : ap * S0.card ≤ ap * Ui.card := Nat.mul_le_mul_left _ hS0
  have h2 : nL * (1 + DC.ins lv) ≤ (1 + I) * nL := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (by omega)
  have h3 : (markedGroups σ Ui).card * (g + 1 + I) ≤ (g + 1 + I) * m := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hmk
  have h4 : g * ((markedGroups σ Ui).card + (emptiedGroups σ Ui).card) ≤
      g * m + g * (emptiedGroups σ Ui).card := by
    rw [Nat.mul_add]; exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hmk) _
  have h5 : (2 * g + 1 + I) * m = g * m + (g + 1 + I) * m := by ring
  have h6 : (ap + ad + 4) * Ui.card = ap * Ui.card + ad * Ui.card + 4 * Ui.card := by ring
  omega

end Iter

section ChildSum

variable {Ω : Type}

/-- Sum of `f` over the records of `lg` at depth-one paths (the children of the call owning the loop). -/
def childSum (f : CallRec G s Ω → ℕ) (lg : Log G s Ω) : ℕ :=
  ((lg.filter (fun x => decide (x.1.length = 1))).map (fun x => f x.2)).sum

theorem childSum_nil (f : CallRec G s Ω → ℕ) : childSum f ([] : Log G s Ω) = 0 := rfl

theorem childSum_append (f : CallRec G s Ω → ℕ) (a b : Log G s Ω) :
    childSum f (a ++ b) = childSum f a + childSum f b := by
  simp [childSum, List.filter_append, List.map_append, List.sum_append]

/-- A shifted sub-call log contributes exactly its root record. -/
theorem childSum_shift (f : CallRec G s Ω → ℕ) (i : ℕ) {lg : Log G s Ω} (hnd : (lg.map Prod.fst).Nodup)
    {r : CallRec G s Ω} (hr : ([], r) ∈ lg) : childSum f (lg.shift i) = f r := by
  classical
  unfold childSum Log.shift
  rw [List.filter_map, List.map_map]
  have hfilt : (lg.filter ((fun x => decide (x.1.length = 1)) ∘ fun x => (i :: x.1, x.2))) =
      lg.filter (fun x => decide (x.1 = [])) := by
    congr 1; funext x; simp [List.length_eq_zero_iff]
  rw [hfilt]
  set L := lg.filter (fun x => decide (x.1 = [])) with hL
  have hsub : ∀ x ∈ L, x = ([], r) := by
    intro x hx
    obtain ⟨hxl, hx0⟩ := List.mem_filter.mp hx
    have hx0' : x.1 = [] := by simpa using hx0
    obtain ⟨q, r'⟩ := x
    simp only at hx0'
    subst hx0'
    rw [rec_unique hnd hxl hr]
  have hmem : ([], r) ∈ L := List.mem_filter.mpr ⟨hr, by simp⟩
  have hndL : L.Nodup := (List.Nodup.of_map _ hnd).sublist List.filter_sublist
  have hrep : L = List.replicate L.length ([], r) := List.eq_replicate_iff.mpr ⟨rfl, hsub⟩
  have hlen : L.length = 1 := by
    have h1 : L.length ≤ 1 := by
      have := hndL; rw [hrep] at this; exact List.nodup_replicate.mp this
    have h2 : 0 < L.length := List.length_pos_of_mem hmem
    omega
  rw [hrep, hlen]
  simp

end ChildSum

section LoopCostSec

variable {Φ Ω : Type} {DC : DCost}
variable {B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {p : ℕ}
  {P0 : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {B'0 : WLab G s}

/-- Number of nonempty groups of a loop state (the emptying potential). -/
def nonemptyCount (σ : LState G s p) : ℕ := (Finset.univ.filter (fun j => (σ.P j).Nonempty)).card

/-- The per-child charge of the main loop. -/
def childCharge (P0 : Fin p → Finset (Fin G.n)) (C0 C1 C2 : ℕ) (r : CallRec G s Ω) : ℕ :=
  C0 + C1 * r.U.card + C2 * (Finset.univ.filter (fun j => (P0 j ∩ r.U).Nonempty)).card

/-- **The main loop's own cost** (BM.9–BM.24), charged to its children, its window edges and the emptying of
groups. -/
theorem loopC_cost (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W)
    {τ : ℕ → ℕ} {Inv : Φ → Prop} {sub : SubRelC G s Φ Ω} {l : ℕ} (hsub : GoodSub G s τ Inv l sub)
    {τl : ℕ} {ap bp ad bd I g : ℕ}
    (hpull : ∀ x, DC.pull (l + 1) x ≤ ap * x + bp) (hdel : ∀ x, DC.del (l + 1) x ≤ ad * x + bd)
    (hins : DC.ins (l + 1) ≤ I) (hP0 : ∀ j, (P0 j).card ≤ g)
    (hMτ : DC.M (l + 1) ≤ τ l) (hgMτ : g * DC.M (l + 1) ≤ τ l) :
    ∀ i (σ : LState G s p) φ σ' φ' lg J cm c,
      LoopC G s DC sub (l + 1) B τl i σ φ σ' φ' lg J cm c →
      LInv G s B S d0 d1 P0 B'0 σ → Inv φ →
      c + g * nonemptyCount σ' ≤ 1 + g * nonemptyCount σ +
        childSum (childCharge P0 (1 + bp + bd) (ap + ad + 4) (2 * g + 1 + I)) lg + (1 + I) * J.card := by
  classical
  intro i σ φ σ' φ' lg J cm c hloop
  induction hloop with
  | stop i σ φ hstop =>
    intro _ _
    simp [childSum_nil]
  | step i σ σ' φ φ1 φ' S0 Bi D1 B'i Ui Di dsub L' piv' lg lg' J' cm c _ hne hpull' hSM _ hsubrel
      hnd hmem hres hrest ih =>
    intro h hI
    -- the sub-call (as in `loopC_log`)
    have hsp : CallPre Bi (expand σ S0 Bi) σ.d := step_pre hpre hfp h hpull'
    have hlowdis : ∀ x ∈ expand σ S0 Bi, σ.B' ≤ dis (s := s) x :=
      fun x hx => (Si_facts h hpull' hx).1.2.2
    have hSne : S0.Nonempty := by
      apply hpull'.nonempty
      simp only [DS.IsEmpty, not_forall] at hne
      exact hne
    obtain ⟨x0, hx0⟩ := hSne
    have hx0S : x0 ∈ expand σ S0 Bi := mem_expand.mpr (Or.inl hx0)
    have hBlt : σ.B' < Bi := by
      obtain ⟨⟨-, -, hB⟩, hlt⟩ := Si_facts h hpull' hx0S
      exact lt_of_le_of_lt (hB.trans (h.walk.sound x0)) hlt
    obtain ⟨hpost, hI1, hlog⟩ := hsub σ.B' Bi (expand σ S0 Bi) σ.d φ (B'i, Ui, Di, dsub) φ1 lg
      hsp hI hlowdis hBlt.le hsubrel
    have hmem' : ∀ e, e ∈ L' ↔ G.src e ∈ Ui ∧ Bi ≤ ext (dis (s := s) (G.src e)) e ∧
        ext (dis (s := s) (G.src e)) e < B := by
      intro e
      rw [hmem e]
      constructor
      · rintro ⟨hu, h1, h2⟩
        have hc : dsub (G.src e) = dis (s := s) (G.src e) := hpost.U_complete _ hu
        rw [hc] at h1 h2
        exact ⟨hu, h1, h2⟩
      · rintro ⟨hu, h1, h2⟩
        have hc : dsub (G.src e) = dis (s := s) (G.src e) := hpost.U_complete _ hu
        rw [← hc] at h1 h2
        exact ⟨hu, h1, h2⟩
    obtain ⟨L, hL, hfold⟩ :=
      window_scan_step hpull'.bound hpost ((D1.merge Di).deleteSet Ui) hnd hmem'
    have hres' : Reselect σ Ui
        (L.foldl (relaxIns G s B (some Bi)) (dsub, (D1.merge Di).deleteSet Ui)).1 piv' := by
      rw [hfold]; exact hres
    have hnext := step_post hpre hfp h hne hpull' hpost hL hres'
    rw [hfold] at hnext
    have ih' := ih hnext hI1
    -- the tail's log (for window disjointness)
    obtain ⟨-, -, -, hll⟩ := loopC_log hpre hfp hsub _ _ _ _ _ _ _ _ _ hrest hnext hI1
    -- the child's root record
    obtain ⟨ri, hri, -, -, -, -, hriB', hriU⟩ := hlog.root
    have hriU' : ri.U = Ui := hriU
    -- group facts from the loop invariant
    have hsubP : ∀ j, σ.P j ⊆ P0 j := h.Psub
    have hpivP : ∀ j, (σ.P j).Nonempty → σ.piv j ∈ σ.P j := fun j hj => (h.pivots j hj).1
    have hdisjP : ∀ a b, a ≠ b → Disjoint (σ.P a) (σ.P b) := fun a b hab =>
      Disjoint.mono (hsubP a) (hsubP b) (hfp.gdisj a b hab)
    have hgP : ∀ j, (σ.P j).card ≤ g := fun j => (Finset.card_le_card (hsubP j)).trans (hP0 j)
    -- full or partial child
    have hS0U : S0.card ≤ Ui.card ∧ ∑ j ∈ pulledGroups σ S0, (σ.P j).card ≤
        Ui.card + g * ((markedGroups σ Ui).card + (emptiedGroups σ Ui).card) := by
      by_cases hfull : B'i = Bi
      · have hsubU : S0 ⊆ Ui := by
          intro x hx
          have hxS : x ∈ expand σ S0 Bi := mem_expand.mpr (Or.inl hx)
          obtain ⟨-, hlt⟩ := Si_facts h hpull' hxS
          have hdis : dis (s := s) x < Bi := lt_of_le_of_lt (h.walk.sound x) hlt
          have hreach : G.Reachable s x := by
            have hne' : σ.d x ≠ ⊤ := ne_top_of_lt hlt
            obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hne'
            exact ⟨q, h.walk x q hq.symm⟩
          have hU : x ∈ Utilde Bi (expand σ S0 Bi : Set (Fin G.n)) := ⟨hdis, x, hxS, onPath_self hreach⟩
          have := (hpost.U_eq x).mpr (by rw [show (B'i, Ui, Di, dsub).1 = B'i from rfl, hfull]; exact hU)
          exact this
        refine ⟨Finset.card_le_card hsubU, ?_⟩
        have := pulled_sum_full hgP (Ui := Ui) hsubU
        omega
      · have hlt : B'i < Bi := lt_of_le_of_ne hpost.B'_le hfull
        have hcap := hpost.partial_card hlt
        have hc' : τ l ≤ Ui.card := hcap
        refine ⟨by omega, ?_⟩
        have h1 := pulled_sum_le hgP hdisjP S0
        have h2 : g * S0.card ≤ g * DC.M (l + 1) := Nat.mul_le_mul_left _ hSM
        omega
    have hit := iterCost_le (σ := σ) (DC := DC) (lv := l + 1) (S0 := S0) (Ui := Ui) (nL := L'.length)
      (hpull S0.card) (hdel Ui.card) hins hgP hS0U.1 hS0U.2
      (Finset.card_le_card (marked_sub_meeting σ P0 hsubP hpivP Ui))
    -- the emptying potential
    have hpot := card_nonempty_next σ Ui
    have hne_next : nonemptyCount (nextState B σ Bi B'i Ui D1 Di dsub L' piv') =
        (Finset.univ.filter (fun j => (σ.P j \ Ui).Nonempty)).card := by
      rfl
    have hne_now : nonemptyCount σ = (Finset.univ.filter (fun j => (σ.P j).Nonempty)).card := rfl
    -- windows are disjoint across iterations
    have hJdisj : Disjoint L'.toFinset J' := by
      rw [Finset.disjoint_left]
      intro e he he'
      obtain ⟨j, r, hjr, hsrc, -, -⟩ := hll.Jwin e he'
      have hsrcU : G.src e ∈ Ui := ((hmem' e).mp (List.mem_toFinset.mp he)).1
      obtain ⟨-, hdisj, -, -, -⟩ := hll.root j r hjr
      have : G.src e ∈ (nextState B σ Bi B'i Ui D1 Di dsub L' piv').U := by
        simp [nextState, hsrcU]
      exact Finset.disjoint_left.mp hdisj hsrc this
    have hJcard : (L'.toFinset ∪ J').card = L'.length + J'.card := by
      rw [Finset.card_union_of_disjoint hJdisj, List.toFinset_card_of_nodup hnd]
    -- the child's charge
    have hch : childSum (childCharge P0 (1 + bp + bd) (ap + ad + 4) (2 * g + 1 + I)) (lg.shift i ++ lg') =
        childCharge P0 (1 + bp + bd) (ap + ad + 4) (2 * g + 1 + I) ri +
          childSum (childCharge P0 (1 + bp + bd) (ap + ad + 4) (2 * g + 1 + I)) lg' := by
      rw [childSum_append, childSum_shift _ _ hlog.inv.nodup hri]
    have hri_charge : childCharge P0 (1 + bp + bd) (ap + ad + 4) (2 * g + 1 + I) ri =
        (1 + bp + bd) + (ap + ad + 4) * Ui.card +
          (2 * g + 1 + I) * (Finset.univ.filter (fun j => (P0 j ∩ Ui).Nonempty)).card := by
      simp [childCharge, hriU']
    rw [hch, hri_charge, hJcard]
    rw [hne_next] at ih'
    rw [hne_now]
    have e1 : (1 + I) * (L'.length + J'.card) = (1 + I) * L'.length + (1 + I) * J'.card := by ring
    have e2 : g * (Finset.univ.filter (fun j => (σ.P j).Nonempty)).card ≥
        g * (Finset.univ.filter (fun j => (σ.P j \ Ui).Nonempty)).card + g * (emptiedGroups σ Ui).card := by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hpot
    omega

end LoopCostSec

section CallCostSec

variable {DC : DCost} {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}

theorem sum_card_le_of_disjoint {p : ℕ} {P : Fin p → Finset (Fin G.n)} {S : Finset (Fin G.n)}
    (hsub : ∀ j, P j ⊆ S) (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j)) : ∑ j, (P j).card ≤ S.card := by
  classical
  rw [← Finset.card_biUnion (fun i _ j _ hij => hdisj i j hij)]
  exact Finset.card_le_card (Finset.biUnion_subset.mpr (fun j _ => hsub j))

/-- **The own cost of one recursive call**, in budget form: FindPivots (`fpC_cost_del`), BM.3–8, the main loop
(`loopC_cost`), the merges and BM.24a–31. -/
theorem callC_cost (hout : ∀ u e, e ∈ out u ↔ G.src e = u) (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (hsimp : ∀ u, ((out u).map G.dst).Nodup) (hk : 2 ≤ k)
    {τ : ℕ → ℕ} {sub : SubRelC G s (Finset (Fin G.m)) (FPData G s)} {l : ℕ}
    (hsub : GoodSub G s τ (DelInv G s) l sub)
    {Blow B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} {φ0 φ2 : Finset (Fin G.m)}
    {τl : ℕ} {res : Result G s} {lg : Log G s (FPData G s)}
    (hpre : CallPre B S d0) (hI : DelInv G s φ0) (hlow : ∀ x ∈ S, Blow ≤ dis (s := s) x)
    (hrel : CallC G s (fpC G s out k hins hext) DC sub (l + 1) Blow B S d0 φ0 τl res φ2 lg)
    {ap bp ad bd I nw : ℕ}
    (hpull : ∀ x, DC.pull (l + 1) x ≤ ap * x + bp) (hdel : ∀ x, DC.del (l + 1) x ≤ ad * x + bd)
    (hinsI : DC.ins (l + 1) ≤ I) (hnew : DC.new (l + 1) ≤ nw)
    (hMτ : DC.M (l + 1) ≤ τ l) (hgMτ : 3 * k * DC.M (l + 1) ≤ τ l) :
    ∃ (r : CallRec G s (FPData G s)) (lgc : Log G s (FPData G s)) (ω : FPData G s) (p : ℕ)
      (P : Fin p → Finset (Fin G.n)) (T6 : Finset (Fin G.n)),
      lg = ([], r) :: lgc ∧ r.fp = some ω ∧ r.p = p ∧ (∀ j, P j ⊆ r.S) ∧
      (∃ hp : p = (forestGroups r.S r.Q k ω.trees).length,
        ∀ j, P j = ((forestGroups r.S r.Q k ω.trees).get (Fin.cast hp j)).toFinset) ∧
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧ T6 ⊆ r.S ∧ (r.B' = r.B → T6 = ∅) ∧
      r.cost ≤ scanC * (ω.Dout \ ω.Din).card +
          fpA k hins hext * ((ω.trees.flatMap (fun T => T.ord)).length + k * r.Q.card) + 3 * r.S.card
        + (nw + r.S.card + p * (2 + I))
        + (1 + 3 * k * p + childSum (childCharge P (1 + bp + bd) (ap + ad + 4) (2 * (3 * k) + 1 + I)) lgc
            + (1 + I) * r.J.card)
        + r.cMerge
        + (1 + r.S.card + T6.card * I + r.W.card + r.W'.card + r.Wr.card * (1 + I) + (ad * r.W'.card + bd)
            + r.S.card) := by
  classical
  obtain ⟨d1, p, P, Q, W, φ1, ω, cfp, piv, σ, lgc, J, cm, cl, L, B'f, T6, W', hfprel, hpiv,
    hloop, hB'e, hB'n, hT6, hW', hL, rfl, rfl⟩ := hrel
  have hlow' : ∀ x ∈ S, Blow ≤ d0 x := fun x hx => (hlow x hx).trans (hpre.walk.sound x)
  obtain ⟨hfp, hI1⟩ := fpC_sound hout hsort hsimp hk _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpre hI hlow' hfprel
  obtain ⟨-, -, hsz, -, -⟩ := fpC_spec hout hsort hsimp hk hpre hI hfprel
  have hcfp := fpC_cost_del hout hsort hsimp hk hpre hI hfprel
  have h0 := linv_init hpre hfp hpiv
  have hP0 : ∀ j, (P j).card ≤ 3 * k := fun j => le_of_lt (hsz j)
  have hlc := loopC_cost (DC := DC) hpre hfp hsub (τl := τl) hpull hdel hinsI hP0 hMτ hgMτ
    _ _ _ _ _ _ _ _ _ hloop h0 hI1
  have hne0 : nonemptyCount (initState B d1 P piv) ≤ p := by
    unfold nonemptyCount
    exact (Finset.card_le_univ _).trans (by simp)
  have hsumP : ∑ j, (P j).card ≤ S.card := sum_card_le_of_disjoint (fun j => (hfp.groups j).2) hfp.gdisj
  have hLlen : L.length = L.toFinset.card := (List.toFinset_card_of_nodup hL.1).symm
  have hpin := hfprel.2.2.1
  refine ⟨_, lgc, ω, p, P, T6, rfl, rfl, rfl, fun j => (hfp.groups j).2, hpin, hfp.gdisj,
    fun x hx => ((hT6 x).mp hx).1, fun hB => ?_, ?_⟩
  · ext x
    simp only [Finset.notMem_empty, iff_false]
    intro hx
    obtain ⟨-, h1, h2⟩ := (hT6 x).mp hx
    have : B'f = B := hB
    rw [this] at h1
    exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)
  · simp only
    unfold initCost finCost
    have e1 : DC.del (l + 1) W'.card ≤ ad * W'.card + bd := hdel _
    have e2 : T6.card * DC.ins (l + 1) ≤ T6.card * I := Nat.mul_le_mul_left _ hinsI
    have e3 : L.length * (1 + DC.ins (l + 1)) ≤ L.toFinset.card * (1 + I) := by
      rw [hLlen]; exact Nat.mul_le_mul_left _ (by omega)
    have e4 : p * (2 + DC.ins (l + 1)) ≤ p * (2 + I) := Nat.mul_le_mul_left _ (by omega)
    have e5 : 3 * k * nonemptyCount (initState B d1 P piv) ≤ 3 * k * p := Nat.mul_le_mul_left _ hne0
    omega

end CallCostSec

end BM
end CHD
end Frontier
