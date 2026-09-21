import Frontier.CHD.FPForeign
import Frontier.Homes
import Frontier.CHD.Reselect

/-!
# Frontier.CHD.CrBe — crossing and kind-(β) tree edges of the traced run (PAPER_CHD §5.3; owner agent-03)

**NON-GATE** (Layer A, cost side, tracker O10).  For a FULL call `X` with FindPivots forest `ω`, a tree edge whose
ends have different HOMES (`Density.Ranges.home` over `Log.ranges`, value = canonical label) is
* a CROSSING edge (`crOf`) if both ends are returned by `X` — no child contains both (`Valid.cr_cross`), or
* a kind-(β) edge (`beOf`) if its head is a foreign leaf — its tail SPLITS the head's fixed value at `X`, so every
  such edge is charged at one call only (`Valid.be_total`, via `Density.Ranges.beta_sum_le`).
Every tree edge is represented by a graph edge whose source lies in `U X` (`treeEdge`; for full calls the extracted
end is in `Ũ = U`).
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD

open Frontier Graph Frontier.CHD.Partition

variable {G : Graph} {s : Fin G.n}

/-- A graph edge between `T.par x` and `x` whose source lies in `U`, if one exists. -/
noncomputable def treeEdge (U : Finset (Fin G.n)) (T : TreeRec (Fin G.n)) (x : Fin G.n) : Option (Fin G.m) := by
  classical
  exact if h : ∃ e, ((G.src e = T.par x ∧ G.dst e = x) ∨ (G.src e = x ∧ G.dst e = T.par x)) ∧ G.src e ∈ U
    then some h.choose else none

/-- The tree edges of a FindPivots forest (non-root members, represented with a source in `U`). -/
noncomputable def treeEdges (U : Finset (Fin G.n)) (ω : FPData G s) : Finset (Fin G.m) :=
  (ω.trees.flatMap (fun T => T.ord.tail.filterMap (treeEdge U T))).toFinset

theorem treeEdge_spec {U : Finset (Fin G.n)} {T : TreeRec (Fin G.n)} {x : Fin G.n} {e : Fin G.m}
    (h : treeEdge U T x = some e) :
    ((G.src e = T.par x ∧ G.dst e = x) ∨ (G.src e = x ∧ G.dst e = T.par x)) ∧ G.src e ∈ U := by
  classical
  unfold treeEdge at h
  split at h
  · next hex =>
    obtain rfl := Option.some.inj h
    exact hex.choose_spec
  · cases h

/-- Forest facts of a record's FindPivots output (agent-05's `FInv` plus the extracted-source tree edges). -/
structure RecForest (r : BM.CallRec G s (FPData G s)) : Prop where
  pf : ∀ ω, r.fp = some ω → ∀ T ∈ ω.trees, ParentFirst T.par T.root T.ord
  disj : ∀ ω, r.fp = some ω → ω.trees.Pairwise (fun a b => ∀ w ∈ a.ord, w ∉ b.ord)
  edge : ∀ ω, r.fp = some ω → ∀ T ∈ ω.trees, ∀ x ∈ T.ord.tail, ∃ e,
    ((G.src e = T.par x ∧ G.dst e = x) ∨ (G.src e = x ∧ G.dst e = T.par x)) ∧
      G.src e ∈ Utilde r.B (r.S : Set (Fin G.n))

theorem parentFirst_par_mem {par : Fin G.n → Fin G.n} {root : Fin G.n} {ord : List (Fin G.n)}
    (h : ParentFirst par root ord) {x : Fin G.n} (hx : x ∈ ord.tail) : par x ∈ ord := by
  obtain ⟨-, hhead, hpar⟩ := h
  cases ord with
  | nil => simp at hx
  | cons a t =>
    simp only [List.tail_cons] at hx
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hx
    have := hpar (a :: pre) post x (by rw [hsplit]; rfl) (List.cons_ne_nil _ _)
    rcases List.mem_cons.mp this with h | h
    · exact h ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hsplit ▸ List.mem_append_left _ h)

variable {τ : ℕ → ℕ} {L0 : ℕ} {lg : BM.Log G s (FPData G s)} (hL : BM.LogInv τ L0 lg)

/-- The home colouring of the traced run at the call `X`. -/
noncomputable def homeX (X : lg.Call) : Fin G.n → Option lg.Call :=
  (BM.Log.ranges hL).home (fun v => dis (s := s) v) X

/-- The FindPivots tree edges of a FULL call, as graph edges with source in `U`. -/
noncomputable def fullEdges (X : lg.Call) : Finset (Fin G.m) := by
  classical
  exact if (lg.recOf X).B' = (lg.recOf X).B then
    match (lg.recOf X).fp with
    | none => ∅
    | some ω => treeEdges (lg.recOf X).U ω
  else ∅

/-- Crossing tree edges (both ends returned, different homes). -/
noncomputable def crOf (X : lg.Call) : Finset (Fin G.m) := by
  classical
  exact (fullEdges X).filter (fun e => G.dst e ∈ (lg.recOf X).U ∧
    homeX hL X (G.src e) ≠ homeX hL X (G.dst e))

/-- Kind-(β) tree edges (head a foreign leaf, different homes). -/
noncomputable def beOf (X : lg.Call) : Finset (Fin G.m) := by
  classical
  exact (fullEdges X).filter (fun e => G.dst e ∉ (lg.recOf X).U ∧
    homeX hL X (G.src e) ≠ homeX hL X (G.dst e))

theorem mem_fullEdges (hF : ∀ q r, (q, r) ∈ lg → RecForest r) {X : lg.Call} {e : Fin G.m}
    (he : e ∈ fullEdges X) :
    (lg.recOf X).B' = (lg.recOf X).B ∧ ∃ ω, (lg.recOf X).fp = some ω ∧ G.src e ∈ (lg.recOf X).U ∧
      G.src e ∈ ω.tvs ∧ G.dst e ∈ ω.tvs := by
  classical
  unfold fullEdges at he
  split_ifs at he with hfull
  · refine ⟨hfull, ?_⟩
    split at he
    · exact absurd he (Finset.notMem_empty e)
    · next ω hω =>
      refine ⟨ω, hω, ?_⟩
      unfold treeEdges at he
      obtain ⟨T, hT, hx⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp he)
      obtain ⟨x, hxT, hxe⟩ := List.mem_filterMap.mp hx
      obtain ⟨hends, hsrc⟩ := treeEdge_spec hxe
      have hpf := (hF _ _ (BM.recOf_mem X)).pf ω hω T hT
      have hxo : x ∈ T.ord := List.mem_of_mem_tail hxT
      have hpo : T.par x ∈ T.ord := parentFirst_par_mem hpf hxT
      have hmem : ∀ y ∈ T.ord, y ∈ ω.tvs := fun y hy =>
        List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨T, hT, hy⟩)
      refine ⟨hsrc, ?_, ?_⟩
      · rcases hends with ⟨h1, -⟩ | ⟨h1, -⟩
        · rw [h1]; exact hmem _ hpo
        · rw [h1]; exact hmem _ hxo
      · rcases hends with ⟨-, h2⟩ | ⟨-, h2⟩
        · rw [h2]; exact hmem _ hxo
        · rw [h2]; exact hmem _ hpo
  · exact absurd he (Finset.notMem_empty e)

/-- **`Valid.cr_cross`** for `crOf`. -/
theorem crOf_cross (hF : ∀ q r, (q, r) ∈ lg → RecForest r) :
    ∀ X, ∀ e ∈ crOf hL X, G.src e ∈ (BM.Log.forest hL).U X ∧ G.dst e ∈ (BM.Log.forest hL).U X ∧
      ∀ Y, (BM.Log.forest hL).parent Y = some X →
        ¬ (G.src e ∈ (BM.Log.forest hL).U Y ∧ G.dst e ∈ (BM.Log.forest hL).U Y) := by
  classical
  intro X e he
  unfold crOf at he
  obtain ⟨he1, hdst, hne⟩ := Finset.mem_filter.mp he
  obtain ⟨-, ω, -, hsrc, -, -⟩ := mem_fullEdges hF he1
  exact ⟨hsrc, hdst, Density.Ranges.cross_of_home_ne hne⟩

section Beta

variable {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}

/-- **Kind-(β) edges split their head's value at their call.** -/
theorem beOf_split (hout : ∀ u e, e ∈ out u ↔ G.src e = u) (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (hrec : ∀ q r, (q, r) ∈ lg → RecFP out k hins hext r) (hF : ∀ q r, (q, r) ∈ lg → RecForest r) :
    ∀ X, ∀ e ∈ beOf hL X, (BM.Log.ranges hL).Split (G.src e) (dis (s := s) (G.dst e)) X := by
  classical
  intro X e he
  unfold beOf at he
  obtain ⟨he1, hdst, hne⟩ := Finset.mem_filter.mp he
  obtain ⟨hfull, ω, hω, hsrc, -, hdtv⟩ := mem_fullEdges hF he1
  have hfo : G.dst e ∈ foOf (lg.recOf X) := by
    unfold foOf; rw [hω]; exact Finset.mem_sdiff.mpr ⟨hdtv, hdst⟩
  obtain ⟨h1, h2⟩ := foOf_range hout hsort (hrec _ _ (BM.recOf_mem X)) hfull _ hfo
  exact Density.Ranges.split_of_home_ne hsrc hdst ⟨h1, h2⟩ hne

/-- **`Valid.be_total`**: every kind-(β) edge is charged at one call only. -/
theorem beOf_total (hout : ∀ u e, e ∈ out u ↔ G.src e = u) (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (hrec : ∀ q r, (q, r) ∈ lg → RecFP out k hins hext r) (hF : ∀ q r, (q, r) ∈ lg → RecForest r) :
    ∑ X, (beOf hL X).card ≤ Fintype.card (Fin G.m) := by
  classical
  exact (BM.Log.ranges hL).beta_sum_le G.src G.dst (fun v => dis (s := s) v) (beOf hL)
    (beOf_split hL hout hsort hrec hF)

end Beta


section Count

/-- `filterMap` with every value present keeps the length. -/
theorem length_filterMap_of_isSome {α' β' : Type*} (f : α' → Option β') :
    ∀ L : List α', (∀ x ∈ L, (f x).isSome) → (L.filterMap f).length = L.length
  | [], _ => rfl
  | x :: L, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h x List.mem_cons_self)
    rw [List.filterMap_cons_some hb, List.length_cons, List.length_cons,
      length_filterMap_of_isSome f L (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- Tree edges of one tree are injective in the non-root member (no 2-cycles in a parent-first tree). -/
theorem treeEdge_inj {U : Finset (Fin G.n)} {T : TreeRec (Fin G.n)} (hpf : ParentFirst T.par T.root T.ord)
    {x y : Fin G.n} (hx : x ∈ T.ord.tail) (hy : y ∈ T.ord.tail) {e : Fin G.m}
    (hex : treeEdge U T x = some e) (hey : treeEdge U T y = some e) : x = y := by
  have hnd : T.ord.Nodup := hpf.1
  have hne : ∀ z ∈ T.ord.tail, z ≠ T.root := by
    intro z hz hzr
    obtain ⟨-, hhead, -⟩ := hpf
    cases hord : T.ord with
    | nil => rw [hord] at hz; simp at hz
    | cons a t =>
      rw [hord] at hz hhead hnd
      simp only [List.head?_cons, Option.some.injEq] at hhead
      simp only [List.tail_cons] at hz
      exact (List.nodup_cons.mp hnd).1 (hhead ▸ hzr ▸ hz)
  obtain ⟨hpx, hlx⟩ := idx_par_lt hpf (List.mem_of_mem_tail hx) (hne x hx)
  obtain ⟨hpy, hly⟩ := idx_par_lt hpf (List.mem_of_mem_tail hy) (hne y hy)
  obtain ⟨ex, -⟩ := treeEdge_spec hex
  obtain ⟨ey, -⟩ := treeEdge_spec hey
  rcases ex with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases ey with ⟨b1, b2⟩ | ⟨b1, b2⟩
  · exact a2.symm.trans b2
  · -- x = par y and par x = y: a 2-cycle
    have h1 : x = T.par y := a2.symm.trans b2
    have h2 : T.par x = y := a1.symm.trans b1
    rw [← h1] at hly; rw [h2] at hlx; omega
  · have h1 : T.par x = y := a2.symm.trans b2
    have h2 : x = T.par y := a1.symm.trans b1
    rw [← h2] at hly; rw [h1] at hlx; omega
  · exact a1.symm.trans b1

end Count


section Count2

theorem mem_foldr_union {γ δ : Type*} [DecidableEq δ] {L : List γ} {E : γ → Finset δ} {x : δ} :
    x ∈ L.foldr (fun T acc => E T ∪ acc) ∅ ↔ ∃ T ∈ L, x ∈ E T := by
  induction L with
  | nil => simp
  | cons T L ih => simp [ih]

theorem card_foldr_union {γ δ : Type*} [DecidableEq δ] (L : List γ) (E : γ → Finset δ)
    (hdisj : L.Pairwise (fun a b => Disjoint (E a) (E b))) :
    (L.foldr (fun T acc => E T ∪ acc) ∅).card = (L.map (fun T => (E T).card)).sum := by
  induction L with
  | nil => simp
  | cons T L ih =>
    obtain ⟨h1, h2⟩ := List.pairwise_cons.mp hdisj
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    rw [Finset.card_union_of_disjoint, ih h2]
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨T', hT', hxT'⟩ := mem_foldr_union.mp hx'
    exact Finset.disjoint_left.mp (h1 T' hT') hx hxT'

theorem nodup_filterMap_of_injOn {α' β' : Type*} {f : α' → Option β'} :
    ∀ {L : List α'}, L.Nodup → (∀ a ∈ L, ∀ a' ∈ L, ∀ b, f a = some b → f a' = some b → a = a') →
      (L.filterMap f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: L, hnd, hinj => by
    have hnd' := (List.nodup_cons.mp hnd)
    have ih := nodup_filterMap_of_injOn hnd'.2
      (fun x hx y hy b h1 h2 => hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) b h1 h2)
    cases hfa : f a with
    | none => rw [List.filterMap_cons_none hfa]; exact ih
    | some b =>
      rw [List.filterMap_cons_some hfa]
      refine List.nodup_cons.mpr ⟨fun hb => ?_, ih⟩
      obtain ⟨a', ha', hfa'⟩ := List.mem_filterMap.mp hb
      have := hinj a List.mem_cons_self a' (List.mem_cons_of_mem _ ha') b hfa hfa'
      exact hnd'.1 (this ▸ ha')

/-- **Bichromatic tree edges of a full call are crossing or kind-(β) edges** (injectively). -/
theorem bich_le_crbe (hF : ∀ q r, (q, r) ∈ lg → RecForest r) {X : lg.Call}
    (hfull : (lg.recOf X).B' = (lg.recOf X).B)
    (hUt : ∀ v ∈ Utilde (lg.recOf X).B ((lg.recOf X).S : Set (Fin G.n)), v ∈ (lg.recOf X).U)
    {ω : FPData G s} (hω : (lg.recOf X).fp = some ω) :
    (ω.trees.map (Reselect.bich (homeX hL X))).sum ≤ (crOf hL X).card + (beOf hL X).card := by
  classical
  have hFX := hF _ _ (BM.recOf_mem X)
  set U := (lg.recOf X).U with hUdef
  set h := homeX hL X with hdef
  set LT : TreeRec (Fin G.n) → List (Fin G.n) :=
    fun T => T.ord.tail.filter (fun x => decide (h x ≠ h (T.par x))) with hLT
  set ET : TreeRec (Fin G.n) → Finset (Fin G.m) := fun T => ((LT T).filterMap (treeEdge U T)).toFinset with hET
  -- every non-root member has a tree edge with source in `U`
  have hsome : ∀ T ∈ ω.trees, ∀ x ∈ T.ord.tail, (treeEdge U T x).isSome := by
    intro T hT x hx
    obtain ⟨e, hends, hsrc⟩ := hFX.edge ω hω T hT x hx
    unfold treeEdge
    rw [dif_pos ⟨e, hends, hUt _ hsrc⟩]
    rfl
  -- per tree: `bich = |ET|`
  have hper : ∀ T ∈ ω.trees, Reselect.bich h T = (ET T).card := by
    intro T hT
    have hpf := hFX.pf ω hω T hT
    have hLTsub : ∀ x ∈ LT T, x ∈ T.ord.tail := fun x hx => (List.mem_filter.mp hx).1
    have hlen := length_filterMap_of_isSome (treeEdge U T) (LT T) (fun x hx => hsome T hT x (hLTsub x hx))
    have hnd : ((LT T).filterMap (treeEdge U T)).Nodup := by
      refine nodup_filterMap_of_injOn ((hpf.1.sublist (List.tail_sublist _)).filter _) ?_
      intro a ha a' ha' b h1 h2
      exact treeEdge_inj hpf (hLTsub a ha) (hLTsub a' ha') h1 h2
    rw [hET]; simp only
    rw [List.toFinset_card_of_nodup hnd, hlen]
    rfl
  -- each `ET T` consists of crossing or kind-(β) edges
  have hsubC : ∀ T ∈ ω.trees, ET T ⊆ crOf hL X ∪ beOf hL X := by
    intro T hT e he
    obtain ⟨x, hxL, hxe⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp he)
    obtain ⟨hxT, hbx⟩ := List.mem_filter.mp hxL
    have hbx' : h x ≠ h (T.par x) := by simpa using hbx
    have hfe : e ∈ fullEdges X := by
      unfold fullEdges
      rw [if_pos hfull]
      simp only [hω]
      unfold treeEdges
      exact List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨T, hT, List.mem_filterMap.mpr ⟨x, hxT, hxe⟩⟩)
    obtain ⟨hends, -⟩ := treeEdge_spec hxe
    have hhome : h (G.src e) ≠ h (G.dst e) := by
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact fun hh => hbx' hh.symm
      · rw [h1, h2]; exact hbx'
    by_cases hd : G.dst e ∈ U
    · exact Finset.mem_union_left _ (by unfold crOf; exact Finset.mem_filter.mpr ⟨hfe, hd, hhome⟩)
    · exact Finset.mem_union_right _ (by unfold beOf; exact Finset.mem_filter.mpr ⟨hfe, hd, hhome⟩)
  -- the `ET T` are pairwise disjoint (trees are vertex-disjoint)
  have hsrcT : ∀ T ∈ ω.trees, ∀ e ∈ ET T, G.src e ∈ T.ord := by
    intro T hT e he
    obtain ⟨x, hxL, hxe⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp he)
    have hxT := (List.mem_filter.mp hxL).1
    obtain ⟨hends, -⟩ := treeEdge_spec hxe
    rcases hends with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1]; exact parentFirst_par_mem (hFX.pf ω hω T hT) hxT
    · rw [h1]; exact List.mem_of_mem_tail hxT
  have hdisj : ω.trees.Pairwise (fun a b => Disjoint (ET a) (ET b)) := by
    refine List.Pairwise.imp_of_mem ?_ (hFX.disj ω hω)
    intro a b ha hb hab
    rw [Finset.disjoint_left]
    intro e hea heb
    exact hab _ (hsrcT a ha e hea) (hsrcT b hb e heb)
  calc (ω.trees.map (Reselect.bich h)).sum = (ω.trees.map (fun T => (ET T).card)).sum := by
        congr 1; exact List.map_congr_left hper
    _ = (ω.trees.foldr (fun T acc => ET T ∪ acc) ∅).card := (card_foldr_union _ _ hdisj).symm
    _ ≤ (crOf hL X ∪ beOf hL X).card := by
        refine Finset.card_le_card (fun e he => ?_)
        obtain ⟨T, hT, heT⟩ := mem_foldr_union.mp he
        exact hsubC T hT heT
    _ ≤ (crOf hL X).card + (beOf hL X).card := Finset.card_union_le _ _

end Count2


section Mk

variable (k : ℕ)

/-- The pivot groups of a record (the tree-partition MakePivots output pinned by `fpC`). -/
noncomputable def groupsOf (r : BM.CallRec G s (FPData G s)) : List (List (Fin G.n)) :=
  match r.fp with
  | none => []
  | some ω => forestGroups r.S r.Q k ω.trees

/-- The marking budget of a call: summed over its groups, the number of children whose returned set meets the
group (each re-selection of a group happens in a distinct such child). -/
noncomputable def mkOf (X : lg.Call) : ℕ := by
  classical
  exact ((groupsOf k (lg.recOf X)).map (fun g =>
    (Finset.univ.filter (fun Y => (BM.Log.forest hL).parent Y = some X ∧
      (g.toFinset ∩ (BM.Log.forest hL).U Y).Nonempty)).card)).sum

/-- **Markings of a full call** (PAPER 5.3(i)): at most `p + |Cr X| + |Be X|`. -/
theorem mkOf_full_le (hk : 2 ≤ k) (hF : ∀ q r, (q, r) ∈ lg → RecForest r) {X : lg.Call}
    (hfull : (lg.recOf X).B' = (lg.recOf X).B)
    (hUt : ∀ v ∈ Utilde (lg.recOf X).B ((lg.recOf X).S : Set (Fin G.n)), v ∈ (lg.recOf X).U) :
    mkOf hL k X ≤ (groupsOf k (lg.recOf X)).length + (crOf hL X).card + (beOf hL X).card := by
  classical
  unfold mkOf groupsOf
  cases hω : (lg.recOf X).fp with
  | none => simp
  | some ω =>
    simp only
    have hFX := hF _ _ (BM.recOf_mem X)
    have h1 : ((forestGroups (lg.recOf X).S (lg.recOf X).Q k ω.trees).map (fun g =>
        (Finset.univ.filter (fun Y => (BM.Log.forest hL).parent Y = some X ∧
          (g.toFinset ∩ (BM.Log.forest hL).U Y).Nonempty)).card)).sum ≤
        ((forestGroups (lg.recOf X).S (lg.recOf X).Q k ω.trees).map
          (fun g => (g.map (homeX hL X)).toFinset.card)).sum := by
      refine Reselect.map_sum_le _ _ _ (fun g _ => ?_)
      have := (BM.Log.ranges hL).card_children_meeting_le (val := fun v => dis (s := s) v) X g.toFinset
      have heq : g.toFinset.image ((BM.Log.ranges hL).home (fun v => dis (s := s) v) X) =
          (g.map (homeX hL X)).toFinset := by
        ext c; simp [homeX]
      rw [heq] at this
      exact this
    have h2 := Reselect.groups_colors_le (lg.recOf X).S (lg.recOf X).Q hk (homeX hL X) ω.trees
      (hFX.pf ω hω)
    have h3 := bich_le_crbe hL hF hfull hUt hω
    unfold forestGroups at h1 ⊢
    omega

end Mk

end CHD
end Frontier
