import Frontier.CHD.Partition

/-!
# Frontier.CHD.PartitionMap — the tree partition commutes with injective relabelling (owner agent-03)

**NON-GATE** (Layer A).  For an injective `f : α → β` and parent functions with `par' (f a) = f (par a)`:
Algorithm 5 (`run`, `pieces`), `forestPieces`, MakePivots (`mpStep`, `makePivots`) and `ParentFirst` commute with
`f` (`makePivots (S.image f) (Q.image f) (forestPieces k (trees.map (relabel f P))) =
(makePivots S Q (forestPieces k trees)).map (map f)`).  Used with `f = Fin.val` to transfer the RAM PT program's
output (over `ℕ`) to Layer A's `forestGroups` (over `Fin n`).
-/

namespace Frontier.CHD.Partition

open List

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

section Map

variable (f : α → β) (hf : Function.Injective f)

/-- Algorithm-5 states related by `f`. -/
def PRel (st : PState α) (st' : PState β) : Prop :=
  (∀ a, st'.acc (f a) = (st.acc a).map f) ∧ st'.groups = st.groups.map (List.map f)

include hf in
theorem step_map {s : ℕ} {par : α → α} {par' : β → β} (hpar : ∀ a, par' (f a) = f (par a))
    {st : PState α} {st' : PState β} (h : PRel f st st') (v : α) :
    PRel f (step s par st v) (step s par' st' (f v)) := by
  obtain ⟨hacc, hgr⟩ := h
  have hlen : (st'.acc (par' (f v)) ++ st'.acc (f v)).length = (st.acc (par v) ++ st.acc v).length := by
    rw [hpar, hacc, hacc]; simp
  unfold step
  rw [hlen]
  split_ifs with hs
  · refine ⟨fun a => ?_, ?_⟩
    · dsimp only
      rw [hpar]
      by_cases ha : a = par v
      · subst ha; simp
      · rw [Function.update_of_ne (fun h => ha (hf h)), Function.update_of_ne ha, hacc]
    · dsimp only
      rw [hgr, hpar, hacc, hacc]; simp
  · refine ⟨fun a => ?_, ?_⟩
    · dsimp only
      rw [hpar]
      by_cases ha : a = par v
      · subst ha; simp [hacc]
      · rw [Function.update_of_ne (fun h => ha (hf h)), Function.update_of_ne ha, hacc]
    · exact hgr

include hf in
theorem run_map {s : ℕ} {par : α → α} {par' : β → β} (hpar : ∀ a, par' (f a) = f (par a)) (rest : List α) :
    PRel f (run s par rest) (run s par' (rest.map f)) := by
  unfold run
  suffices h : ∀ (l : List α) (st : PState α) (st' : PState β), PRel f st st' →
      PRel f (l.foldl (step s par) st) ((l.map f).foldl (step s par') st') from
    h rest init init ⟨fun a => by simp [init], by simp [init]⟩
  intro l
  induction l with
  | nil => intro st st' h; exact h
  | cons a l ih =>
    intro st st' h
    simp only [List.map_cons, List.foldl_cons]
    exact ih _ _ (step_map f hf hpar h a)

include hf in
theorem pieces_map {s : ℕ} {par : α → α} {par' : β → β} (hpar : ∀ a, par' (f a) = f (par a))
    (rest : List α) (root : α) :
    pieces s par' (rest.map f) (f root) = (pieces s par rest root).map (List.map f) := by
  obtain ⟨hacc, hgr⟩ := run_map f hf hpar (s := s) rest
  unfold pieces
  rw [hgr, List.getLast?_map]
  cases h : (run s par rest).groups.getLast? with
  | none => simp [hacc]
  | some G => simp [hacc, List.map_dropLast]

/-- Relabel a tree by `f`, with a parent function `P` on `β`. -/
def relabel (P : TreeRec α → β → β) (T : TreeRec α) : TreeRec β := ⟨f T.root, T.ord.map f, P T⟩

include hf in
theorem forestPieces_map (k : ℕ) (P : TreeRec α → β → β) :
    ∀ (trees : List (TreeRec α)), (∀ T ∈ trees, ∀ a, P T (f a) = f (T.par a)) →
      forestPieces k (trees.map (relabel f P)) = (forestPieces k trees).map (List.map f)
  | [], _ => by simp [forestPieces]
  | T :: ts, hP => by
    have ih := forestPieces_map k P ts (fun U hU => hP U (List.mem_cons_of_mem _ hU))
    unfold forestPieces at ih ⊢
    simp only [List.map_cons, List.flatMap_cons, List.map_append, ih]
    congr 1
    simp only [relabel]
    rw [← List.map_tail, ← List.map_reverse]
    exact pieces_map f hf (hP T List.mem_cons_self) _ _

include hf in
theorem dedup_map_inj : ∀ l : List α, (l.map f).dedup = l.dedup.map f
  | [] => by simp
  | a :: l => by
    have ih := dedup_map_inj l
    by_cases ha : a ∈ l
    · rw [List.map_cons, List.dedup_cons_of_mem (List.mem_map_of_mem ha), List.dedup_cons_of_mem ha, ih]
    · have hfa : f a ∉ l.map f := fun h => by
        obtain ⟨b, hb, hba⟩ := List.mem_map.mp h
        exact ha (hf hba ▸ hb)
      rw [List.map_cons, List.dedup_cons_of_notMem hfa, List.dedup_cons_of_notMem ha, ih, List.map_cons]

theorem toFinset_map' (l : List α) : (l.map f).toFinset = l.toFinset.image f := by
  ext y; simp

include hf in
theorem mpStep_map (S Q : Finset α) (acc : List (List α) × Finset α) (F : List α) :
    mpStep (S.image f) (Q.image f) (acc.1.map (List.map f), acc.2.image f) (F.map f) =
      ((mpStep S Q acc F).1.map (List.map f), (mpStep S Q acc F).2.image f) := by
  have hfilt : (F.map f).filter (fun y => decide (y ∈ S.image f ∧ y ∉ Q.image f ∧ y ∉ acc.2.image f)) =
      (F.filter (fun x => decide (x ∈ S ∧ x ∉ Q ∧ x ∉ acc.2))).map f := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro x _
    simp only [Function.comp, hf.mem_finset_image]
  unfold mpStep
  simp only []
  rw [hfilt, dedup_map_inj f hf]
  by_cases h0 : (F.filter (fun x => decide (x ∈ S ∧ x ∉ Q ∧ x ∉ acc.2))).dedup = []
  · rw [if_pos (by rw [h0]; rfl), if_pos h0]
  · rw [if_neg (fun h => h0 (List.map_eq_nil_iff.mp h)), if_neg h0]
    simp only [List.map_append, List.map_cons, List.map_nil, Finset.image_union, toFinset_map']

include hf in
theorem makePivots_map (S Q : Finset α) (pcs : List (List α)) :
    makePivots (S.image f) (Q.image f) (pcs.map (List.map f)) = (makePivots S Q pcs).map (List.map f) := by
  unfold makePivots
  suffices h : ∀ (l : List (List α)) (acc : List (List α) × Finset α),
      (l.map (List.map f)).foldl (mpStep (S.image f) (Q.image f)) (acc.1.map (List.map f), acc.2.image f) =
        ((l.foldl (mpStep S Q) acc).1.map (List.map f), (l.foldl (mpStep S Q) acc).2.image f) by
    have := h pcs ([], ∅)
    simp only [List.map_nil, Finset.image_empty] at this
    rw [this]
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons F l ih =>
    intro acc
    simp only [List.map_cons, List.foldl_cons]
    rw [mpStep_map f hf S Q acc F]
    exact ih _

include hf in
theorem parentFirst_map {par : α → α} {par' : β → β} (hpar : ∀ a, par' (f a) = f (par a)) {root : α}
    {ord : List α} (h : ParentFirst par root ord) : ParentFirst par' (f root) (ord.map f) := by
  obtain ⟨hnd, hhd, hp⟩ := h
  refine ⟨hnd.map hf, by rw [List.head?_map, hhd]; rfl, fun pre post b heq hpre => ?_⟩
  obtain ⟨l1, l2, rfl, h1, h2⟩ := List.map_eq_append_iff.mp heq
  obtain ⟨a, l3, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.mp h2
  have hl1 : l1 ≠ [] := by rintro rfl; exact hpre (by rw [← h1]; rfl)
  have := hp l1 l3 a rfl hl1
  rw [← h1, hpar]
  exact List.mem_map_of_mem this

end Map

end Frontier.CHD.Partition
