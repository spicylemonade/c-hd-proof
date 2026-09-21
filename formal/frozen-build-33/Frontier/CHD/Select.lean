import Mathlib.Data.List.Sort
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Frontier.CHD.Select — deterministic linear-time selection with a comparison counter

Owner: agent-04 (work package L3 of COORD G2-2).  NON-GATE supporting lemma.

Mathematical (list-level) model of the Blum–Floyd–Pratt–Rivest–Tarjan selection algorithm
(median of medians, groups of five).  Every comparison between two elements of the linear
order `α` is counted explicitly in the second component of the result.  Main results:

* `selectC_isKth` : the returned element is a `k`-th smallest element (0-indexed) of the list;
* `selectC_cost`  : the number of comparisons is at most `100 * l.length`.

This file is architecture independent: the RAM-level implementation (work package L3,
after the formal-architecture decision) must refine `selectC`.
-/

namespace Frontier.CHD

variable {α : Type*} [LinearOrder α]

/-! ## Insertion sort with a comparison counter -/

/-- Ordered insertion with a comparison counter. -/
def insC (a : α) : List α → List α × ℕ
  | [] => ([a], 0)
  | b :: l => if a ≤ b then (a :: b :: l, 1) else (b :: (insC a l).1, (insC a l).2 + 1)

theorem insC_fst (a : α) (l : List α) : (insC a l).1 = l.orderedInsert (· ≤ ·) a := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [insC, List.orderedInsert]
    split_ifs <;> simp [ih]

theorem insC_snd_le (a : α) (l : List α) : (insC a l).2 ≤ l.length := by
  induction l with
  | nil => simp [insC]
  | cons b l ih =>
    simp only [insC]
    split_ifs <;> simp <;> omega

/-- Insertion sort with a comparison counter. -/
def sortC : List α → List α × ℕ
  | [] => ([], 0)
  | a :: l => ((insC a (sortC l).1).1, (sortC l).2 + (insC a (sortC l).1).2)

theorem sortC_fst (l : List α) : (sortC l).1 = l.insertionSort (· ≤ ·) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [sortC, insC_fst, ih]
    rfl

theorem length_sortC (l : List α) : (sortC l).1.length = l.length := by
  rw [sortC_fst, List.length_insertionSort]

theorem sortC_snd_le (l : List α) : 2 * (sortC l).2 ≤ l.length * l.length := by
  induction l with
  | nil => simp [sortC]
  | cons a l ih =>
    simp only [sortC, List.length_cons]
    have h1 := insC_snd_le a (sortC l).1
    rw [length_sortC] at h1
    have h2 : (l.length + 1) * (l.length + 1) = l.length * l.length + 2 * l.length + 1 := by ring
    omega

theorem perm_sortC (l : List α) : (sortC l).1.Perm l := by
  rw [sortC_fst]; exact List.perm_insertionSort _ l

theorem pairwise_sortC (l : List α) : (sortC l).1.Pairwise (· ≤ ·) := by
  rw [sortC_fst]; exact List.pairwise_insertionSort _ l

/-! ## Rank counting and the specification -/

/-- number of elements `< x` -/
def cntLt (l : List α) (x : α) : ℕ := l.countP (fun y => decide (y < x))
/-- number of elements `≤ x` -/
def cntLe (l : List α) (x : α) : ℕ := l.countP (fun y => decide (y ≤ x))
/-- number of elements `≥ x` -/
def cntGe (l : List α) (x : α) : ℕ := l.countP (fun y => decide (x ≤ y))

/-- `x` is a `k`-th smallest element (0-indexed) of `l`. -/
def IsKth (l : List α) (k : ℕ) (x : α) : Prop := x ∈ l ∧ cntLt l x ≤ k ∧ k < cntLe l x

/-- The `k`-th smallest value is unique. -/
theorem IsKth.unique {l : List α} {k : ℕ} {x y : α} (hx : IsKth l k x) (hy : IsKth l k y) :
    x = y := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have : cntLe l x ≤ cntLt l y :=
      List.countP_mono_left (fun z _ hz => by simp at hz ⊢; exact lt_of_le_of_lt hz h)
    have := hx.2.2; have := hy.2.1; omega
  · have : cntLe l y ≤ cntLt l x :=
      List.countP_mono_left (fun z _ hz => by simp at hz ⊢; exact lt_of_le_of_lt hz h)
    have := hy.2.2; have := hx.2.1; omega

theorem cntLt_add_cntGe (l : List α) (x : α) : cntLt l x + cntGe l x = l.length := by
  unfold cntLt cntGe
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons, List.length_cons]
    by_cases h : a < x
    · have : ¬ x ≤ a := not_le.mpr h
      simp [h, this]; omega
    · have : x ≤ a := not_lt.mp h
      simp [h, this]; omega

theorem length_filter_gt_add_cntLe (l : List α) (x : α) :
    (l.filter (fun y => decide (x < y))).length + cntLe l x = l.length := by
  unfold cntLe
  rw [← List.countP_eq_length_filter]
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons, List.length_cons]
    by_cases h : x < a
    · have : ¬ a ≤ x := not_le.mpr h
      simp [h, this]; omega
    · have : a ≤ x := not_lt.mp h
      simp [h, this]; omega

/-! ## Counting lemmas for sorted lists -/

theorem countP_lt_getElem_le {s : List α} (hs : s.Pairwise (· ≤ ·)) {i : ℕ} (hi : i < s.length) :
    s.countP (fun x => decide (x < s[i])) ≤ i := by
  induction s generalizing i with
  | nil => simp at hi
  | cons a s ih =>
    rw [List.pairwise_cons] at hs
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero, List.countP_cons]
      have : s.countP (fun x => decide (x < a)) = 0 := by
        rw [List.countP_eq_zero]; intro x hx; simp [not_lt.mpr (hs.1 x hx)]
      simp [this]
    | succ i =>
      simp only [List.getElem_cons_succ, List.countP_cons]
      have := ih hs.2 (i := i) (by simpa using hi)
      split_ifs <;> omega

theorem le_countP_le_getElem {s : List α} (hs : s.Pairwise (· ≤ ·)) {i : ℕ} (hi : i < s.length) :
    i + 1 ≤ s.countP (fun x => decide (x ≤ s[i])) := by
  induction s generalizing i with
  | nil => simp at hi
  | cons a s ih =>
    rw [List.pairwise_cons] at hs
    cases i with
    | zero => simp
    | succ i =>
      have hi' : i < s.length := by simpa using hi
      simp only [List.getElem_cons_succ, List.countP_cons]
      have h1 := ih hs.2 hi'
      have h2 : a ≤ s[i] := hs.1 _ (List.getElem_mem hi')
      simp [h2]; omega

theorem le_countP_ge_getElem {s : List α} (hs : s.Pairwise (· ≤ ·)) {i : ℕ} (hi : i < s.length) :
    s.length - i ≤ s.countP (fun x => decide (s[i] ≤ x)) := by
  induction s generalizing i with
  | nil => simp at hi
  | cons a s ih =>
    rw [List.pairwise_cons] at hs
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero, List.countP_cons, List.length_cons]
      have : s.countP (fun x => decide (a ≤ x)) = s.length := by
        rw [List.countP_eq_length]; intro x hx; simp [hs.1 x hx]
      simp [this]
    | succ i =>
      simp only [List.getElem_cons_succ, List.countP_cons, List.length_cons]
      have := ih hs.2 (i := i) (by simpa using hi)
      split_ifs <;> omega

/-- the `k`-th element of the sorted list is a `k`-th smallest element -/
theorem isKth_sortC (l : List α) {k : ℕ} (hk : k < l.length) :
    IsKth l k ((sortC l).1[k]'(by rw [length_sortC]; exact hk)) := by
  have hp := perm_sortC l
  have hs := pairwise_sortC l
  have hk' : k < (sortC l).1.length := by rw [length_sortC]; exact hk
  refine ⟨hp.subset (List.getElem_mem hk'), ?_, ?_⟩
  · unfold cntLt; rw [← hp.countP_eq]; exact countP_lt_getElem_le hs hk'
  · unfold cntLe; rw [← hp.countP_eq]; have := le_countP_le_getElem hs hk'; omega

/-! ## Groups of five -/

/-- Split a list into consecutive groups of five (the last one may be shorter). -/
def chunk5 : List α → List (List α)
  | [] => []
  | a :: l => (a :: l).take 5 :: chunk5 ((a :: l).drop 5)
termination_by l => l.length
decreasing_by simp; omega

theorem flatten_chunk5 : ∀ l : List α, (chunk5 l).flatten = l
  | [] => by simp [chunk5]
  | a :: l => by
      rw [chunk5, List.flatten_cons, flatten_chunk5 ((a :: l).drop 5)]
      exact List.take_append_drop 5 (a :: l)
termination_by l => l.length
decreasing_by simp; omega

theorem mem_chunk5 : ∀ {l : List α} {g : List α}, g ∈ chunk5 l → g ≠ [] ∧ g.length ≤ 5
  | [], g, h => by simp [chunk5] at h
  | a :: l, g, h => by
      rw [chunk5, List.mem_cons] at h
      rcases h with h | h
      · subst h; refine ⟨by simp, by simp⟩
      · exact mem_chunk5 h
termination_by l => l.length
decreasing_by simp; omega

theorem length_chunk5 : ∀ l : List α, (chunk5 l).length = (l.length + 4) / 5
  | [] => by simp [chunk5]
  | a :: l => by
      rw [chunk5, List.length_cons, length_chunk5 ((a :: l).drop 5), List.length_drop,
        List.length_cons]
      omega
termination_by l => l.length
decreasing_by simp; omega

theorem countP_short_chunk5 : ∀ l : List α, (chunk5 l).countP (fun g => decide (g.length < 5)) ≤ 1
  | [] => by simp [chunk5]
  | a :: l => by
      rw [chunk5, List.countP_cons]
      by_cases h : 5 ≤ (a :: l).length
      · have h1 : ¬ ((a :: l).take 5).length < 5 := by rw [List.length_take]; omega
        have := countP_short_chunk5 ((a :: l).drop 5)
        simp only [h1, decide_false]; simpa using this
      · have h2 : (a :: l).drop 5 = [] := List.drop_eq_nil_of_le (by omega)
        rw [h2]; simp only [chunk5, List.countP_cons, List.countP_nil]; split <;> omega
termination_by l => l.length
decreasing_by simp; omega

/-! ## Medians of groups -/

variable [Inhabited α]

/-- median of a group: its element of rank `(|g|-1)/2` -/
def med (g : List α) : α := (sortC g).1.getD ((g.length - 1) / 2) default

theorem med_eq {g : List α} (hg : g ≠ []) :
    med g = (sortC g).1[(g.length - 1) / 2]'(by
      rw [length_sortC]; have := List.length_pos_of_ne_nil hg; omega) := by
  unfold med; rw [List.getD_eq_getElem]

theorem med_mem {g : List α} (hg : g ≠ []) : med g ∈ g := by
  rw [med_eq hg]; exact (perm_sortC g).subset (List.getElem_mem _)

theorem three_le_cntLe_med {g : List α} (h5 : g.length = 5) : 3 ≤ cntLe g (med g) := by
  have hg : g ≠ [] := by intro h; simp [h] at h5
  rw [med_eq hg]
  unfold cntLe
  rw [← (perm_sortC g).countP_eq]
  have := le_countP_le_getElem (pairwise_sortC g)
    (i := (g.length - 1) / 2) (by rw [length_sortC]; omega)
  simp only [h5] at this ⊢
  omega

theorem three_le_cntGe_med {g : List α} (h5 : g.length = 5) : 3 ≤ cntGe g (med g) := by
  have hg : g ≠ [] := by intro h; simp [h] at h5
  rw [med_eq hg]
  unfold cntGe
  rw [← (perm_sortC g).countP_eq]
  have hi : (g.length - 1) / 2 < (sortC g).1.length := by rw [length_sortC]; omega
  have := le_countP_ge_getElem (pairwise_sortC g) hi
  have hl : (sortC g).1.length = g.length := length_sortC g
  calc 3 ≤ (sortC g).1.length - (g.length - 1) / 2 := by rw [hl, h5]
    _ ≤ _ := this

/-! ## Summation helpers -/

theorem mul_countP_le_sum {β : Type*} (gs : List β) (P : β → Bool) (f : β → ℕ) (c : ℕ)
    (h : ∀ g ∈ gs, P g = true → c ≤ f g) : c * gs.countP P ≤ (gs.map f).sum := by
  induction gs with
  | nil => simp
  | cons a gs ih =>
    simp only [List.countP_cons, List.map_cons, List.sum_cons]
    have ih' := ih (fun g hg hP => h g (List.mem_cons_of_mem _ hg) hP)
    by_cases hP : P a = true
    · have := h a (List.mem_cons_self) hP
      simp [hP]; rw [Nat.mul_add, Nat.mul_one]; omega
    · simp [hP]; omega

theorem countP_le_countP_and_add {β : Type*} (gs : List β) (P Q : β → Bool) :
    gs.countP P ≤ gs.countP (fun g => P g && Q g) + gs.countP (fun g => !Q g) := by
  induction gs with
  | nil => simp
  | cons a gs ih =>
    simp only [List.countP_cons]
    cases hP : P a <;> cases hQ : Q a <;> simp <;> omega

theorem cnt_flatten_chunk5 (l : List α) (q : α → Bool) :
    l.countP q = ((chunk5 l).map (fun g => g.countP q)).sum := by
  conv_lhs => rw [← flatten_chunk5 l]
  rw [List.countP_flatten]

theorem sum_length_chunk5 (l : List α) : ((chunk5 l).map List.length).sum = l.length := by
  conv_rhs => rw [← flatten_chunk5 l]
  rw [List.length_flatten]

theorem sum_map_le_mul_sum {β : Type*} (gs : List β) (f g : β → ℕ) (c : ℕ)
    (h : ∀ x ∈ gs, f x ≤ c * g x) : (gs.map f).sum ≤ c * (gs.map g).sum := by
  induction gs with
  | nil => simp
  | cons a gs ih =>
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    have := h a List.mem_cons_self
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    omega

theorem sum_cost_chunk5 (l : List α) :
    ((chunk5 l).map (fun g => (sortC g).2)).sum ≤ 5 * l.length := by
  rw [← sum_length_chunk5 l]
  apply sum_map_le_mul_sum
  intro g hg
  have h1 := sortC_snd_le g
  have h2 := (mem_chunk5 hg).2
  have : g.length * g.length ≤ 5 * g.length := Nat.mul_le_mul_right _ h2
  omega

/-! ## The median-of-medians bound -/

theorem mom_bound (l : List α) (p : α)
    (hp : IsKth ((chunk5 l).map med) ((((chunk5 l).map med).length - 1) / 2) p) :
    10 * cntLt l p ≤ 7 * l.length + 30 ∧
    10 * (l.filter (fun x => decide (p < x))).length ≤ 7 * l.length + 30 := by
  set gs := chunk5 l with hgs
  set G := gs.length with hG
  have hGn : G = (l.length + 4) / 5 := length_chunk5 l
  have hms : ((gs.map med).length) = G := by simp [hG]
  rw [hms] at hp
  set j := (G - 1) / 2 with hj
  have hshort := countP_short_chunk5 l
  rw [← hgs] at hshort
  have hlen5 : ∀ g ∈ gs, (!decide (g.length = 5)) = decide (g.length < 5) := by
    intro g hg
    have := (mem_chunk5 hg).2
    by_cases h : g.length = 5 <;> simp [h] <;> omega
  have hshort' : gs.countP (fun g => !decide (g.length = 5)) ≤ 1 := by
    rw [List.countP_congr (q := fun g => decide (g.length < 5))
      (fun g hg => by rw [hlen5 g hg])]
    exact hshort
  constructor
  · -- lower part: elements `≥ p` are many
    have hGe : cntGe l p = (gs.map (fun g => cntGe g p)).sum := by
      unfold cntGe; exact cnt_flatten_chunk5 l _
    have h1 : 3 * gs.countP (fun g => decide (p ≤ med g) && decide (g.length = 5)) ≤
        (gs.map (fun g => cntGe g p)).sum := by
      apply mul_countP_le_sum
      intro g _ hP
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
      have h3 := three_le_cntGe_med hP.2
      have : cntGe g (med g) ≤ cntGe g p :=
        List.countP_mono_left (fun z _ hz => by simp at hz ⊢; exact le_trans hP.1 hz)
      omega
    have h2 := countP_le_countP_and_add gs (fun g => decide (p ≤ med g))
      (fun g => decide (g.length = 5))
    have h4 : gs.countP (fun g => decide (p ≤ med g)) = cntGe (gs.map med) p := by
      unfold cntGe; rw [List.countP_map]; rfl
    have h5 := cntLt_add_cntGe (gs.map med) p
    rw [hms] at h5
    have h6 := hp.2.1
    have h7 := cntLt_add_cntGe l p
    omega
  · -- upper part: elements `≤ p` are many
    have hLe : cntLe l p = (gs.map (fun g => cntLe g p)).sum := by
      unfold cntLe; exact cnt_flatten_chunk5 l _
    have h1 : 3 * gs.countP (fun g => decide (med g ≤ p) && decide (g.length = 5)) ≤
        (gs.map (fun g => cntLe g p)).sum := by
      apply mul_countP_le_sum
      intro g _ hP
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
      have h3 := three_le_cntLe_med hP.2
      have : cntLe g (med g) ≤ cntLe g p :=
        List.countP_mono_left (fun z _ hz => by simp at hz ⊢; exact le_trans hz hP.1)
      omega
    have h2 := countP_le_countP_and_add gs (fun g => decide (med g ≤ p))
      (fun g => decide (g.length = 5))
    have h4 : gs.countP (fun g => decide (med g ≤ p)) = cntLe (gs.map med) p := by
      unfold cntLe; rw [List.countP_map]; rfl
    have h6 := hp.2.2
    have h7 := length_filter_gt_add_cntLe l p
    omega

/-! ## The selection algorithm -/

/-- BFPRT selection with a comparison counter.  Returns a `k`-th smallest element of `l`
(0-indexed) and the number of comparisons between elements that the algorithm performs.
Lists of length `≤ 200` are sorted by insertion sort; otherwise groups of five, the median of
medians as pivot, a three-way partition (`2|l|` comparisons) and one recursive call.  The two
`if … < l.length` guards only make termination syntactic; `selectC_spec` shows they always hold. -/
def selectC (l : List α) (k : ℕ) : α × ℕ :=
  if hsmall : l.length ≤ 200 then ((sortC l).1.getD k default, (sortC l).2)
  else
    let pr := selectC ((chunk5 l).map med) ((((chunk5 l).map med).length - 1) / 2)
    let p := pr.1
    let lo := l.filter (fun x => decide (x < p))
    let hi := l.filter (fun x => decide (p < x))
    let c0 := ((chunk5 l).map (fun g => (sortC g).2)).sum + pr.2 + 2 * l.length
    if k < lo.length then
      if hlo : lo.length < l.length then
        let r := selectC lo k
        (r.1, c0 + r.2)
      else (p, c0)
    else if k < l.length - hi.length then (p, c0)
    else if hhi : hi.length < l.length then
      let r := selectC hi (k - (l.length - hi.length))
      (r.1, c0 + r.2)
    else (p, c0)
termination_by l.length
decreasing_by
  · simp only [List.length_map, length_chunk5]; omega
  · exact hlo
  · exact hhi

theorem isKth_of_filter_lt {l : List α} {p x : α} {k : ℕ}
    (h : IsKth (l.filter (fun y => decide (y < p))) k x) : IsKth l k x := by
  obtain ⟨hx, h1, h2⟩ := h
  rw [List.mem_filter] at hx
  have hxp : x < p := by simpa using hx.2
  refine ⟨hx.1, ?_, ?_⟩
  · unfold cntLt at h1 ⊢
    rw [List.countP_filter] at h1
    have e : l.countP (fun y => decide (y < x)) =
        l.countP (fun y => decide (y < x) && decide (y < p)) := by
      apply List.countP_congr
      intro y _
      constructor
      · intro hy; simp only [decide_eq_true_eq, Bool.and_eq_true] at hy ⊢
        exact ⟨hy, lt_trans hy hxp⟩
      · intro hy; simp only [decide_eq_true_eq, Bool.and_eq_true] at hy ⊢; exact hy.1
    rw [e]; exact h1
  · unfold cntLe at h2 ⊢
    rw [List.countP_filter] at h2
    have e : l.countP (fun y => decide (y ≤ x)) =
        l.countP (fun y => decide (y ≤ x) && decide (y < p)) := by
      apply List.countP_congr
      intro y _
      constructor
      · intro hy; simp only [decide_eq_true_eq, Bool.and_eq_true] at hy ⊢
        exact ⟨hy, lt_of_le_of_lt hy hxp⟩
      · intro hy; simp only [decide_eq_true_eq, Bool.and_eq_true] at hy ⊢; exact hy.1
    rw [e]; exact h2

theorem isKth_of_filter_gt {l : List α} {p x : α} {k : ℕ}
    (h : IsKth (l.filter (fun y => decide (p < y))) k x) :
    IsKth l (k + cntLe l p) x := by
  obtain ⟨hx, h1, h2⟩ := h
  rw [List.mem_filter] at hx
  have hpx : p < x := by simpa using hx.2
  have split_lt : cntLt l x = cntLt (l.filter (fun y => decide (p < y))) x + cntLe l p := by
    unfold cntLt cntLe
    rw [List.countP_eq_countP_filter_add l (fun y => decide (y < x)) (fun y => decide (p < y))]
    simp only [List.countP_filter]
    congr 1
    apply List.countP_congr
    intro y _
    by_cases hy : y ≤ p
    · have : y < x := lt_of_le_of_lt hy hpx
      simp [hy, this, not_lt.mpr hy]
    · simp [hy]
  have split_le : cntLe l x = cntLe (l.filter (fun y => decide (p < y))) x + cntLe l p := by
    unfold cntLe
    rw [List.countP_eq_countP_filter_add l (fun y => decide (y ≤ x)) (fun y => decide (p < y))]
    simp only [List.countP_filter]
    congr 1
    apply List.countP_congr
    intro y _
    by_cases hy : y ≤ p
    · have : y ≤ x := le_trans hy hpx.le
      simp [hy, this, not_lt.mpr hy]
    · simp [hy]
  refine ⟨hx.1, ?_, ?_⟩
  · rw [split_lt]; omega
  · rw [split_le]; omega

/-- Correctness and cost of `selectC`: for `k < |l|` the result is a `k`-th smallest element
of `l`, and at most `100 * |l|` comparisons are performed. -/
theorem selectC_spec : ∀ (n : ℕ) (l : List α) (k : ℕ), l.length = n → k < n →
    IsKth l k (selectC l k).1 ∧ (selectC l k).2 ≤ 100 * n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l k hn hk
  rw [selectC]
  by_cases hsmall : l.length ≤ 200
  · rw [dite_eq_left_of_eq_true (eq_true hsmall)]
    have hk' : k < (sortC l).1.length := by rw [length_sortC]; omega
    refine ⟨?_, ?_⟩
    · simp only
      rw [List.getD_eq_getElem _ _ hk']
      exact isKth_sortC l (by omega)
    · have := sortC_snd_le l
      have : l.length * l.length ≤ 200 * l.length := Nat.mul_le_mul_right _ hsmall
      omega
  · rw [dite_eq_right_of_eq_false (eq_false hsmall)]
    simp only
    -- the median of medians
    set gs := chunk5 l with hgs
    set ms := gs.map med with hms
    have hG : ms.length = (l.length + 4) / 5 := by simp [hms, hgs, length_chunk5]
    have hGpos : 0 < ms.length := by omega
    have hGlt : ms.length < n := by omega
    obtain ⟨hp, hpc⟩ := ih ms.length hGlt ms ((ms.length - 1) / 2) rfl (by omega)
    set p := (selectC ms ((ms.length - 1) / 2)).1 with hpdef
    have hpl : p ∈ l := by
      have hpm := hp.1
      rw [hms, List.mem_map] at hpm
      obtain ⟨g, hg, hgp⟩ := hpm
      rw [← hgp, ← flatten_chunk5 l, List.mem_flatten]
      exact ⟨g, hg, med_mem (mem_chunk5 hg).1⟩
    obtain ⟨hlo10, hhi10⟩ := mom_bound l p hp
    set lo := l.filter (fun x => decide (x < p)) with hlodef
    set hi := l.filter (fun x => decide (p < x)) with hhidef
    have hlo_eq : lo.length = cntLt l p := by
      rw [hlodef, ← List.countP_eq_length_filter]; rfl
    have hhi_eq : hi.length + cntLe l p = l.length := length_filter_gt_add_cntLe l p
    have hlolt : lo.length < l.length := by
      rw [hlodef, List.length_filter_lt_length_iff_exists]
      exact ⟨p, hpl, by simp⟩
    have hhilt : hi.length < l.length := by
      rw [hhidef, List.length_filter_lt_length_iff_exists]
      exact ⟨p, hpl, by simp⟩
    have hcm := sum_cost_chunk5 l
    rw [← hgs] at hcm
    have hc0 : (gs.map (fun g => (sortC g).2)).sum + (selectC ms ((ms.length - 1) / 2)).2
        + 2 * l.length ≤ 27 * n + 80 := by omega
    by_cases hklo : k < lo.length
    · rw [ite_eq_left hklo, dite_eq_left_of_eq_true (eq_true hlolt)]
      obtain ⟨hr, hrc⟩ := ih lo.length (by omega) lo k rfl hklo
      refine ⟨isKth_of_filter_lt hr, ?_⟩
      simp only
      omega
    · rw [ite_eq_right hklo]
      by_cases hkmid : k < l.length - hi.length
      · rw [ite_eq_left hkmid]
        refine ⟨⟨hpl, ?_, ?_⟩, ?_⟩
        · show cntLt l p ≤ k
          rw [← hlo_eq]; omega
        · show k < cntLe l p
          omega
        · simp only
          omega
      · rw [ite_eq_right hkmid, dite_eq_left_of_eq_true (eq_true hhilt)]
        have hk2 : k - (l.length - hi.length) < hi.length := by omega
        obtain ⟨hr, hrc⟩ := ih hi.length (by omega) hi _ rfl hk2
        have hr' := isKth_of_filter_gt hr
        have : k - (l.length - hi.length) + cntLe l p = k := by omega
        rw [this] at hr'
        refine ⟨hr', ?_⟩
        simp only
        omega

theorem selectC_isKth (l : List α) {k : ℕ} (hk : k < l.length) : IsKth l k (selectC l k).1 :=
  (selectC_spec l.length l k rfl hk).1

theorem selectC_cost (l : List α) {k : ℕ} (hk : k < l.length) :
    (selectC l k).2 ≤ 100 * l.length :=
  (selectC_spec l.length l k rfl hk).2

end Frontier.CHD
