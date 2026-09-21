import Frontier.CHD.Partition

/-!
# Frontier.CHD.Reselect — re-selection charging (PAPER_CHD §5.3(i)); owner agent-03

**NON-GATE** (Layer A, cost side, tracker O10).  The combinatorial core of the re-selection bound
`g_j ≤ 1 + c_j`: in a parent-first list, the number of distinct colours is at most one plus the number
of members whose parent has a different colour.  Applied to a PT piece (a subtree of a FindPivots tree)
with the HOME colouring (the child of the full call whose range contains the vertex), this bounds the
number of children that can return a pivot of the piece's group.
-/

namespace Frontier.CHD.Reselect

open Frontier.CHD.Partition

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Every member after the first has its parent strictly earlier. -/
def PFirst (par : α → α) (L : List α) : Prop :=
  ∀ (pre post : List α) (v : α), L = pre ++ v :: post → pre ≠ [] → par v ∈ pre

theorem PFirst.of_append {par : α → α} {L : List α} {v : α} (h : PFirst par (L ++ [v])) :
    PFirst par L := by
  intro pre post w hL hpre
  exact h pre (post ++ [v]) w (by rw [hL]; simp) hpre

/-- **Colours along a parent-first list**: at most one colour plus one per bichromatic parent edge. -/
theorem colors_le (par : α → α) (h : α → β) :
    ∀ L : List α, PFirst par L →
      (L.map h).toFinset.card ≤ 1 + (L.tail.filter (fun x => decide (h x ≠ h (par x)))).length := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro _; simp
  | append_singleton L v ih =>
    intro hpf
    have ih' := ih hpf.of_append
    by_cases hL : L = []
    · subst hL; simp
    · have hpv : par v ∈ L := hpf L [] v rfl hL
      have htail : (L ++ [v]).tail = L.tail ++ [v] := List.tail_append_of_ne_nil hL
      rw [htail, List.filter_append, List.length_append, List.map_append, List.toFinset_append]
      simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil, insert_empty_eq]
      by_cases hc : h v = h (par v)
      · have hmem : h v ∈ (L.map h).toFinset := by
          rw [List.mem_toFinset, hc]; exact List.mem_map_of_mem hpv
        rw [Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr hmem)]
        omega
      · have h1 := Finset.card_union_le (L.map h).toFinset {h v}
        rw [Finset.card_singleton] at h1
        have h2 : ([v].filter (fun x => decide (h x ≠ h (par x)))).length = 1 := by simp [hc]
        omega

/-- **Colours on a rooted list with a strictly increasing parent measure**: at most one colour (the top's) plus one per
member whose parent has a different colour.  (Map each other colour to its member of maximal measure.) -/
theorem colors_le_measure (par : α → α) (h : α → β) (μ : α → ℕ) (top : α) (T : List α)
    (hnd : (top :: T).Nodup) (hroot : ∀ x ∈ T, par x ∈ top :: T ∧ μ x < μ (par x)) :
    ((top :: T).map h).toFinset.card ≤ 1 + (T.filter (fun x => decide (h x ≠ h (par x)))).length := by
  classical
  set C := ((top :: T).map h).toFinset with hC
  set Bi := T.filter (fun x => decide (h x ≠ h (par x))) with hBi
  -- the representative of a colour: a member of that colour with maximal measure
  have hrep : ∀ c ∈ C.erase (h top), ∃ x ∈ Bi, h x = c := by
    intro c hc
    obtain ⟨hct, hcC⟩ := Finset.mem_erase.mp hc
    have hne : ((top :: T).toFinset.filter (fun x => h x = c)).Nonempty := by
      obtain ⟨x, hx, hxc⟩ := List.mem_map.mp (List.mem_toFinset.mp hcC)
      exact ⟨x, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hx, hxc⟩⟩
    obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image _ μ hne
    obtain ⟨hxF, hxc⟩ := Finset.mem_filter.mp hx
    have hxT : x ∈ T := by
      rcases List.mem_cons.mp (List.mem_toFinset.mp hxF) with rfl | hxT
      · exact absurd hxc.symm hct
      · exact hxT
    obtain ⟨hpF, hμ⟩ := hroot x hxT
    have hpc : h (par x) ≠ c := by
      intro hpc
      have := hmax (par x) (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hpF, hpc⟩)
      omega
    refine ⟨x, List.mem_filter.mpr ⟨hxT, ?_⟩, hxc⟩
    simp only [decide_eq_true_eq, hxc]; exact fun h' => hpc h'.symm
  haveI : Nonempty α := ⟨top⟩
  choose! f hfB hfc using hrep
  have hinj : Set.InjOn f (C.erase (h top) : Set β) := by
    intro c1 hc1 c2 hc2 heq
    rw [← hfc c1 hc1, ← hfc c2 hc2, heq]
  have h1 : (C.erase (h top)).card ≤ Bi.toFinset.card :=
    Finset.card_le_card_of_injOn f (fun c hc => List.mem_toFinset.mpr (hfB c hc)) hinj
  have h2 : Bi.toFinset.card ≤ Bi.length := List.toFinset_card_le _
  have hmem : h top ∈ C := by rw [hC]; simp
  have h3 : (C.erase (h top)).card + 1 = C.card := Finset.card_erase_add_one hmem
  omega

/-- **Colours on a PT piece.**  A piece of a tree in children-first order `rest` (root `root`) has at most one colour
plus one per non-top member whose parent has a different colour. -/
theorem pieces_colors_le {s : ℕ} (hs : 2 ≤ s) {par : α → α} {rest : List α} {root : α}
    (ht : TreeOrder par rest root) (h : α → β) :
    ∀ F ∈ pieces s par rest root,
      (F.map h).toFinset.card ≤ 1 + (F.tail.filter (fun x => decide (h x ≠ h (par x)))).length := by
  intro F hF
  obtain ⟨hne, hrt⟩ := pieces_rooted hs ht F hF
  have hnd := pieces_nodup hs ht F hF
  have htails := pieces_tails_perm hs ht
  have hrnd : rest.Nodup := ht.nodup
  obtain ⟨top, T, rfl⟩ : ∃ top T, F = top :: T := by
    cases F with
    | nil => exact absurd rfl hne
    | cons a t => exact ⟨a, t, rfl⟩
  classical
  let μ : α → ℕ := fun x => if x ∈ rest then rest.idxOf x else rest.length
  refine colors_le_measure par h μ top T hnd (fun x hx => ⟨hrt x hx, ?_⟩)
  have hxr : x ∈ rest := htails.subset (List.mem_flatMap.mpr ⟨_, hF, hx⟩)
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hxr
  have hxpre : x ∉ pre := by
    rw [hsplit] at hrnd
    exact fun hm => (List.nodup_append.mp hrnd).2.2 x hm x List.mem_cons_self rfl
  have hidx : rest.idxOf x = pre.length := by
    rw [hsplit, List.idxOf_append_of_notMem hxpre, List.idxOf_cons_self]; simp
  have hμx : μ x = pre.length := by simp only [μ, if_pos hxr, hidx]
  rw [hμx]
  rcases ht.childFirst pre post x hsplit with hp | hp
  · have hpr : par x ∈ rest := by rw [hsplit]; simp [hp]
    have hppre : par x ∉ pre := by
      rw [hsplit] at hrnd
      exact fun hm => (List.nodup_append.mp hrnd).2.2 _ hm _ (List.mem_cons_of_mem _ hp) rfl
    have hpx : par x ≠ x := by
      intro heq
      rw [hsplit] at hrnd
      have := (List.nodup_cons.mp (List.nodup_append.mp hrnd).2.1).1
      exact this (heq ▸ hp)
    have : rest.idxOf (par x) = pre.length + (1 + post.idxOf (par x)) := by
      rw [hsplit, List.idxOf_append_of_notMem hppre, List.idxOf_cons_ne _ (Ne.symm hpx)]
      omega
    simp only [μ, if_pos hpr, this]
    omega
  · have hnr : root ∉ rest := ht.root_nmem
    have hlt : pre.length < rest.length := by rw [hsplit]; simp
    simp only [μ, hp, if_neg hnr]
    exact hlt

/-- **Groups come from distinct pieces, in order**: the MakePivots groups are pointwise contained in a sublist of the
pieces. -/
theorem makePivots_sublist (S Q : Finset α) (pcs : List (List α)) :
    ∃ sub : List (List α), sub.Sublist pcs ∧
      List.Forall₂ (fun g F => ∀ x ∈ g, x ∈ F) (makePivots S Q pcs) sub := by
  unfold makePivots
  induction pcs using List.reverseRecOn with
  | nil => exact ⟨[], List.Sublist.slnil, List.Forall₂.nil⟩
  | append_singleton pcs F ih =>
    obtain ⟨sub, hsub, hfa⟩ := ih
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    set acc := pcs.foldl (mpStep S Q) ([], ∅) with hacc
    have hdef : mpStep S Q acc F =
        if (F.filter (fun x => decide (x ∈ S ∧ x ∉ Q ∧ x ∉ acc.2))).dedup = [] then acc
        else (acc.1 ++ [(F.filter (fun x => decide (x ∈ S ∧ x ∉ Q ∧ x ∉ acc.2))).dedup],
          acc.2 ∪ ((F.filter (fun x => decide (x ∈ S ∧ x ∉ Q ∧ x ∉ acc.2))).dedup).toFinset) := rfl
    rw [hdef]
    split_ifs with hcur
    · exact ⟨sub, hsub.trans (List.sublist_append_left _ _), hfa⟩
    · refine ⟨sub ++ [F], hsub.append (List.Sublist.refl _), ?_⟩
      refine List.rel_append hfa (List.Forall₂.cons ?_ List.Forall₂.nil)
      intro x hx
      exact (List.mem_filter.mp (List.mem_dedup.mp hx)).1

/-- Bichromatic parent edges of a tree under a colouring. -/
def bich (h : α → β) (T : TreeRec α) : ℕ := (T.ord.tail.filter (fun x => decide (h x ≠ h (T.par x)))).length

theorem map_sum_le {γ : Type*} (L : List γ) (f g : γ → ℕ) (hfg : ∀ x ∈ L, f x ≤ g x) :
    (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (hfg x List.mem_cons_self) (ih (fun y hy => hfg y (List.mem_cons_of_mem _ hy)))

theorem sum_le_len_add {γ : Type*} (L : List γ) (f g : γ → ℕ) (hfg : ∀ x ∈ L, f x ≤ 1 + g x) :
    (L.map f).sum ≤ L.length + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := hfg x List.mem_cons_self
    have h2 := ih (fun y hy => hfg y (List.mem_cons_of_mem _ hy))
    omega

/-- The pieces of one tree carry exactly the tree's bichromatic parent edges. -/
theorem pieces_bich_sum {s : ℕ} (hs : 2 ≤ s) (h : α → β) {T : TreeRec α}
    (hpf : ParentFirst T.par T.root T.ord) :
    ((pieces s T.par T.ord.tail.reverse T.root).map
      (fun F => (F.tail.filter (fun x => decide (h x ≠ h (T.par x)))).length)).sum = bich h T := by
  have ht := treeOrder_of_parentFirst hpf
  have hperm := pieces_tails_perm hs ht
  have h1 : ((pieces s T.par T.ord.tail.reverse T.root).map
      (fun F => (F.tail.filter (fun x => decide (h x ≠ h (T.par x)))).length)).sum =
      (((pieces s T.par T.ord.tail.reverse T.root).flatMap List.tail).filter
        (fun x => decide (h x ≠ h (T.par x)))).length := by
    rw [List.filter_flatMap, List.length_flatMap]
  rw [h1, (hperm.filter _).length_eq, List.filter_reverse, List.length_reverse]
  rfl

theorem forall2_colors_le (h : α → β) {gs sub : List (List α)}
    (hfa : List.Forall₂ (fun g F => ∀ x ∈ g, x ∈ F) gs sub) :
    (gs.map (fun g => (g.map h).toFinset.card)).sum ≤ (sub.map (fun F => (F.map h).toFinset.card)).sum := by
  induction hfa with
  | nil => simp
  | cons hgF _ ih =>
    simp only [List.map_cons, List.sum_cons]
    refine Nat.add_le_add ?_ ih
    refine Finset.card_le_card (fun c hc => ?_)
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hc)
    exact List.mem_toFinset.mpr (List.mem_map_of_mem (hgF x hx))

/-- **Colours of the pivot groups of a forest**: summed over the MakePivots groups, the number of distinct colours is
at most the number of groups plus the forest's bichromatic parent edges. -/
theorem groups_colors_le (S Q : Finset α) {k : ℕ} (hk : 2 ≤ k) (h : α → β) (trees : List (TreeRec α))
    (hok : ∀ T ∈ trees, ParentFirst T.par T.root T.ord) :
    ((makePivots S Q (forestPieces k trees)).map (fun g => (g.map h).toFinset.card)).sum ≤
      (makePivots S Q (forestPieces k trees)).length + (trees.map (bich h)).sum := by
  classical
  obtain ⟨sub, hsub, hfa⟩ := makePivots_sublist S Q (forestPieces k trees)
  set cF : List α → ℕ := fun F => (F.map h).toFinset.card with hcF
  have hpt : ((makePivots S Q (forestPieces k trees)).map (fun g => (g.map h).toFinset.card)).sum ≤
      (sub.map cF).sum := forall2_colors_le h hfa
  have hlen : sub.length = (makePivots S Q (forestPieces k trees)).length := hfa.length_eq.symm
  -- colours minus one, summed over any list of pieces
  set w : List α → ℕ := fun F => cF F - 1 with hw
  have h1 : (sub.map cF).sum ≤ sub.length + (sub.map w).sum :=
    sum_le_len_add sub cF w (fun F _ => by simp only [hw]; omega)
  have h2 : (sub.map w).sum ≤ ((forestPieces k trees).map w).sum :=
    (hsub.map w).sum_le_sum (fun _ _ => Nat.zero_le _)
  have h3 : ((forestPieces k trees).map w).sum ≤ (trees.map (bich h)).sum := by
    unfold forestPieces
    clear hpt h1 h2 hlen hfa hsub sub
    induction trees with
    | nil => simp
    | cons T ts ih =>
      have hT := hok T List.mem_cons_self
      have ih' := ih (fun U hU => hok U (List.mem_cons_of_mem _ hU))
      have hpc : ((pieces k T.par T.ord.tail.reverse T.root).map w).sum ≤ bich h T := by
        rw [← pieces_bich_sum hk h hT]
        refine map_sum_le _ w _ (fun F hF => ?_)
        have := pieces_colors_le hk (treeOrder_of_parentFirst hT) h F hF
        simp only [hw, hcF]
        omega
      rw [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      exact Nat.add_le_add hpc ih'
  calc ((makePivots S Q (forestPieces k trees)).map (fun g => (g.map h).toFinset.card)).sum
      ≤ (sub.map cF).sum := hpt
    _ ≤ sub.length + (sub.map w).sum := h1
    _ ≤ (makePivots S Q (forestPieces k trees)).length + (trees.map (bich h)).sum := by
      rw [hlen]; exact Nat.add_le_add_left (h2.trans h3) _

end Frontier.CHD.Reselect
