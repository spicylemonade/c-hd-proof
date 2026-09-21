import Mathlib.Data.List.Basic
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Frontier.CostCharging

/-!
# Frontier.CHD.Partition — DMSY26 Lemma A.1 (tree partition), post-order formulation (owner: agent-03)

**NON-GATE.** A rooted tree is given by a parent function `par` and a list `rest` of its NON-root vertices in an
order where every vertex precedes its parent (children first). The root is processed last. `run` is DMSY26
Algorithm 5, unrolled into a left fold over `rest`:
* every vertex `w` owns an accumulator list `acc w`, initially `[w]` (head = its top);
* processing `v` appends `acc v` to `acc (par v)`;
* if the result has at least `s` elements, it is reported as a group and `acc (par v)` is reset to `[par v]`.

Main invariant (`Inv`): the TAILS of the active containers — the accumulators of unprocessed vertices, plus the reported
groups — are, as a multiset, exactly the processed vertices. Consequences:
* sizes (groups in `[s, 2s)`);
* the edge budget `Σ_groups (|G| - 1) ≤ |rest|`, which gives the pivot bound `#groups · (s-1) ≤ |T| - 1`;
* every vertex is a non-top member of at most one piece (the parent edges of the pieces are disjoint);
* each container is a rooted subtree at its head.
-/

set_option linter.unusedSectionVars false

namespace Frontier.CHD.Partition

open List

variable {α : Type*} [DecidableEq α]

/-- Partition state: accumulators and reported groups (in report order). -/
structure PState (α : Type*) where
  acc : α → List α
  groups : List (List α)

/-- One step of Algorithm 5: absorb the finished vertex `v` into its parent's accumulator. -/
def step (s : ℕ) (par : α → α) (st : PState α) (v : α) : PState α :=
  if s ≤ (st.acc (par v) ++ st.acc v).length then
    { acc := Function.update st.acc (par v) [par v], groups := st.groups ++ [st.acc (par v) ++ st.acc v] }
  else
    { acc := Function.update st.acc (par v) (st.acc (par v) ++ st.acc v), groups := st.groups }

/-- Initial state: every vertex owns the singleton `[w]`. -/
def init : PState α := ⟨fun w => [w], []⟩

/-- Run Algorithm 5 over the children-first list `rest`. -/
def run (s : ℕ) (par : α → α) (rest : List α) : PState α := rest.foldl (step s par) init



theorem flatMap_update_perm {β : Type*} {l : List α} {p : α} (hp : p ∈ l) (hnd : l.Nodup)
    (f : α → List β) (b : List β) :
    (l.flatMap (Function.update f p b)) ++ f p ~ l.flatMap f ++ b := by
  induction l with
  | nil => simp at hp
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    by_cases hx : x = p
    · subst hx
      have hnot : ∀ y ∈ xs, Function.update f x b y = f y := by
        intro y hy
        have : y ≠ x := fun h => hnd.1 (h ▸ hy)
        simp [Function.update_of_ne this]
      have hfm : xs.flatMap (Function.update f x b) = xs.flatMap f :=
        List.flatMap_congr hnot
      simp only [List.flatMap_cons, Function.update_self, hfm, List.append_assoc]
      calc b ++ (xs.flatMap f ++ f x) ~ (xs.flatMap f ++ f x) ++ b := List.perm_append_comm
        _ ~ (f x ++ xs.flatMap f) ++ b := List.perm_append_comm.append_right b
        _ = f x ++ (xs.flatMap f ++ b) := by rw [List.append_assoc]
    · have hp' : p ∈ xs := by
        rcases List.mem_cons.mp hp with h | h
        · exact absurd h.symm hx
        · exact h
      have := ih hp' hnd.2
      simp only [List.flatMap_cons, Function.update_of_ne hx, List.append_assoc]
      exact this.append_left (f x)

/-- The tree hypotheses: `rest` lists the non-root vertices without repetition, children before parents. -/
structure TreeOrder (par : α → α) (rest : List α) (root : α) : Prop where
  nodup : rest.Nodup
  root_nmem : root ∉ rest
  childFirst : ∀ (pre post : List α) (v : α), rest = pre ++ v :: post → par v ∈ post ∨ par v = root

/-- The invariant after processing the prefix `pre` of `rest = pre ++ post`. Active containers are the accumulators of
`post ++ [root]` and the reported groups. -/
structure Inv (s : ℕ) (par : α → α) (root : α) (pre post : List α) (st : PState α) : Prop where
  head : ∀ w ∈ post ++ [root], ∃ t, st.acc w = w :: t
  gne : ∀ G ∈ st.groups, G ≠ []
  tails : ((post ++ [root]).flatMap (fun w => (st.acc w).tail)) ++ st.groups.flatMap List.tail ~ pre
  small : ∀ w ∈ post ++ [root], (st.acc w).length < s
  gsize : ∀ G ∈ st.groups, s ≤ G.length ∧ G.length < 2 * s
  rooted : ∀ w ∈ post ++ [root], ∀ x ∈ (st.acc w).tail, par x ∈ st.acc w
  grooted : ∀ G ∈ st.groups, ∀ x ∈ G.tail, par x ∈ G
  lastTop : ∀ G g, st.groups.getLast? = some G → G.head? = some g → ∃ w ∈ post ++ [root], g ∈ st.acc w

theorem inv_init {s : ℕ} (hs : 2 ≤ s) (par : α → α) (rest : List α) (root : α) :
    Inv s par root [] rest (init : PState α) where
  head w _ := ⟨[], rfl⟩
  gne G h := by simp [init] at h
  tails := by
    have : ((rest ++ [root]).flatMap (fun w => ((init : PState α).acc w).tail)) = [] := by
      simp [init]
    simp [this, init]
  small w _ := by simp [init]; omega
  gsize G h := by simp [init] at h
  rooted w _ x hx := by simp [init] at hx
  grooted G h := by simp [init] at h
  lastTop G g h := by simp [init] at h


theorem inv_step {s : ℕ} (hs : 2 ≤ s) {par : α → α} {rest : List α} {root : α}
    (ht : TreeOrder par rest root) {pre post : List α} {v : α} (hrest : rest = pre ++ v :: post)
    {st : PState α} (hI : Inv s par root pre (v :: post) st) :
    Inv s par root (pre ++ [v]) post (step s par st v) := by
  classical
  -- basic facts
  have hnd : rest.Nodup := ht.nodup
  have hvpost : v ∉ post := by
    rw [hrest] at hnd
    have := (List.nodup_append.mp hnd).2.1
    exact (List.nodup_cons.mp this).1
  have hvroot : v ≠ root := by
    intro h; apply ht.root_nmem; rw [hrest, ← h]; simp
  have hrootpost : root ∉ post := by
    intro h; apply ht.root_nmem; rw [hrest]; simp [h]
  have hpostnd : post.Nodup := by
    rw [hrest] at hnd
    exact (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).2
  have hAnd : (post ++ [root]).Nodup := by
    rw [List.nodup_append]
    refine ⟨hpostnd, List.nodup_singleton _, ?_⟩
    intro a ha b hb hab
    simp at hb; subst hb; subst hab; exact hrootpost ha
  have hp : par v ∈ post ++ [root] := by
    rcases ht.childFirst pre post v hrest with h | h
    · exact List.mem_append_left _ h
    · rw [h]; simp
  have hvA : v ∉ post ++ [root] := by
    simp only [List.mem_append, List.mem_singleton, not_or]; exact ⟨hvpost, hvroot⟩
  have hpv : par v ≠ v := fun h => hvA (h ▸ hp)
  have hpA0 : par v ∈ (v :: post) ++ [root] := by simp only [List.cons_append]; exact List.mem_cons_of_mem _ hp
  have hvA0 : v ∈ (v :: post) ++ [root] := by simp
  obtain ⟨tp, htp⟩ := hI.head (par v) hpA0
  obtain ⟨tv, htv⟩ := hI.head v hvA0
  have hmemA0 : ∀ w ∈ post ++ [root], w ∈ (v :: post) ++ [root] := by
    intro w hw; simp only [List.cons_append]; exact List.mem_cons_of_mem _ hw
  -- the tails of the old active containers split as `tv ++ (flatMap over post ++ [root])`
  have hT0 : ((v :: post) ++ [root]).flatMap (fun w => (st.acc w).tail)
      = tv ++ (post ++ [root]).flatMap (fun w => (st.acc w).tail) := by
    simp [htv]
  have hlen_p := hI.small (par v) hpA0
  have hlen_v := hI.small v hvA0
  unfold step
  by_cases hc : s ≤ (st.acc (par v) ++ st.acc v).length
  · -- REPORT case
    rw [if_pos hc]
    have hupd : ∀ w, (Function.update st.acc (par v) [par v] w).tail
        = Function.update (fun w => (st.acc w).tail) (par v) [] w := by
      intro w; by_cases hw : w = par v
      · subst hw; simp
      · simp [Function.update_of_ne hw]
    refine
      { head := ?_, gne := ?_, tails := ?_, small := ?_, gsize := ?_, rooted := ?_, grooted := ?_,
        lastTop := ?_ }
    all_goals try dsimp only
    · intro w hw
      by_cases hwp : w = par v
      · subst hwp; exact ⟨[], by simp⟩
      · rw [Function.update_of_ne hwp]; exact hI.head w (hmemA0 w hw)
    · intro G hG
      simp only [List.mem_append, List.mem_singleton] at hG
      rcases hG with hG | hG
      · exact hI.gne G hG
      · subst hG; simp [htp]
    · have hL := flatMap_update_perm hp hAnd (fun w => (st.acc w).tail) []
      have hfun : (fun w => (Function.update st.acc (par v) [par v] w).tail)
          = Function.update (fun w => (st.acc w).tail) (par v) [] := funext hupd
      rw [hfun]
      have hold := hI.tails
      rw [hT0] at hold
      rw [List.perm_iff_count]
      intro a
      have h1 := hL.count_eq a
      have h2 := hold.count_eq a
      simp only [List.count_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil] at h1 h2 ⊢
      simp only [htp, htv, List.cons_append, List.tail_cons, List.count_append, List.count_cons,
        List.count_nil] at h1 h2 ⊢
      split_ifs at h1 h2 ⊢ <;> omega
    · intro w hw
      by_cases hwp : w = par v
      · subst hwp; simp; omega
      · rw [Function.update_of_ne hwp]; exact hI.small w (hmemA0 w hw)
    · intro G hG
      simp only [List.mem_append, List.mem_singleton] at hG
      rcases hG with hG | hG
      · exact hI.gsize G hG
      · subst hG; refine ⟨hc, ?_⟩; rw [List.length_append]; omega
    · intro w hw x hx
      by_cases hwp : w = par v
      · subst hwp; simp at hx
      · rw [Function.update_of_ne hwp] at hx ⊢; exact hI.rooted w (hmemA0 w hw) x hx
    · intro G hG x hx
      simp only [List.mem_append, List.mem_singleton] at hG
      rcases hG with hG | hG
      · exact hI.grooted G hG x hx
      · subst hG
        rw [htp, htv] at hx ⊢
        simp only [List.cons_append, List.tail_cons, List.mem_append, List.mem_cons] at hx
        rcases hx with hx | hx | hx
        · have := hI.rooted (par v) hpA0 x (by rw [htp]; simpa using hx)
          rw [htp] at this
          simp only [List.cons_append, List.mem_cons, List.mem_append] at this ⊢
          tauto
        · subst hx; simp
        · have := hI.rooted v hvA0 x (by rw [htv]; simpa using hx)
          rw [htv] at this
          simp only [List.cons_append, List.mem_cons, List.mem_append] at this ⊢
          tauto
    · intro G g hG hg
      rw [List.getLast?_append] at hG
      simp at hG
      subst hG
      rw [htp] at hg
      simp at hg
      subst hg
      exact ⟨par v, hp, by simp⟩
  · -- NO-REPORT case
    rw [if_neg hc]
    have hupd : ∀ w, (Function.update st.acc (par v) (st.acc (par v) ++ st.acc v) w).tail
        = Function.update (fun w => (st.acc w).tail) (par v) (tp ++ st.acc v) w := by
      intro w; by_cases hw : w = par v
      · subst hw; simp [htp]
      · simp [Function.update_of_ne hw]
    refine
      { head := ?_, gne := hI.gne, tails := ?_, small := ?_, gsize := hI.gsize, rooted := ?_,
        grooted := hI.grooted, lastTop := ?_ }
    all_goals try dsimp only
    · intro w hw
      by_cases hwp : w = par v
      · subst hwp; exact ⟨tp ++ st.acc v, by simp [htp]⟩
      · rw [Function.update_of_ne hwp]; exact hI.head w (hmemA0 w hw)
    · have hL := flatMap_update_perm hp hAnd (fun w => (st.acc w).tail) (tp ++ st.acc v)
      have hfun : (fun w => (Function.update st.acc (par v) (st.acc (par v) ++ st.acc v) w).tail)
          = Function.update (fun w => (st.acc w).tail) (par v) (tp ++ st.acc v) := funext hupd
      rw [hfun]
      have hold := hI.tails
      rw [hT0] at hold
      rw [List.perm_iff_count]
      intro a
      have h1 := hL.count_eq a
      have h2 := hold.count_eq a
      simp only [List.count_append] at h1 h2 ⊢
      simp only [htp, htv, List.tail_cons, List.count_cons, List.count_append, List.count_nil] at h1 h2 ⊢
      split_ifs at h1 h2 ⊢ <;> omega
    · intro w hw
      by_cases hwp : w = par v
      · subst hwp; simp only [Function.update_self]; omega
      · rw [Function.update_of_ne hwp]; exact hI.small w (hmemA0 w hw)
    · intro w hw x hx
      by_cases hwp : w = par v
      · subst hwp
        simp only [Function.update_self] at hx ⊢
        rw [htp, htv] at hx ⊢
        simp only [List.cons_append, List.tail_cons, List.mem_append, List.mem_cons] at hx
        rcases hx with hx | hx | hx
        · have := hI.rooted (par v) hpA0 x (by rw [htp]; simpa using hx)
          rw [htp] at this
          simp only [List.cons_append, List.mem_cons, List.mem_append] at this ⊢
          tauto
        · subst hx; simp
        · have := hI.rooted v hvA0 x (by rw [htv]; simpa using hx)
          rw [htv] at this
          simp only [List.cons_append, List.mem_cons, List.mem_append] at this ⊢
          tauto
      · rw [Function.update_of_ne hwp] at hx ⊢; exact hI.rooted w (hmemA0 w hw) x hx
    · intro G g hG hg
      obtain ⟨w, hw, hgw⟩ := hI.lastTop G g hG hg
      simp only [List.cons_append, List.mem_cons] at hw
      rcases hw with hw | hw
      · rw [hw] at hgw
        exact ⟨par v, hp, by simp only [Function.update_self]; exact List.mem_append_right _ hgw⟩
      · by_cases hwp : w = par v
        · rw [hwp] at hgw
          exact ⟨par v, hp, by simp only [Function.update_self]; exact List.mem_append_left _ hgw⟩
        · exact ⟨w, hw, by rw [Function.update_of_ne hwp]; exact hgw⟩


/-- The invariant holds after every prefix. -/
theorem inv_prefix {s : ℕ} (hs : 2 ≤ s) {par : α → α} {rest : List α} {root : α}
    (ht : TreeOrder par rest root) :
    ∀ n, n ≤ rest.length →
      Inv s par root (rest.take n) (rest.drop n) ((rest.take n).foldl (step s par) init) := by
  intro n
  induction n with
  | zero => intro _; simpa using inv_init hs par rest root
  | succ n ih =>
    intro hn
    have hlt : n < rest.length := by omega
    have hI := ih (by omega)
    have hdrop : rest.drop n = rest[n] :: rest.drop (n + 1) := List.drop_eq_getElem_cons hlt
    have htake : rest.take (n + 1) = rest.take n ++ [rest[n]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hlt]; rfl
    have hrest : rest = rest.take n ++ rest[n] :: rest.drop (n + 1) := by
      rw [← hdrop, List.take_append_drop]
    rw [hdrop] at hI
    have := inv_step hs ht hrest hI
    rw [htake, List.foldl_append]
    simpa using this

/-- The invariant at the end of the run: only the root's accumulator is active. -/
theorem inv_run {s : ℕ} (hs : 2 ≤ s) {par : α → α} {rest : List α} {root : α}
    (ht : TreeOrder par rest root) : Inv s par root rest [] (run s par rest) := by
  have := inv_prefix hs ht rest.length le_rfl
  simpa [run] using this

/-- The final pieces: the reported groups, the last one merged with the root's accumulator (its head, the top of
the last group, already lies in the root's accumulator, so only its tail is appended). -/
def pieces (s : ℕ) (par : α → α) (rest : List α) (root : α) : List (List α) :=
  match (run s par rest).groups.getLast? with
  | none => [(run s par rest).acc root]
  | some G => (run s par rest).groups.dropLast ++ [(run s par rest).acc root ++ G.tail]

/-- If every list in `l` has a tail of length at least `c`, then `|l| · c ≤ Σ |tail|`. -/
theorem len_mul_le_sum {β : Type*} (l : List (List β)) (c : ℕ) (h : ∀ F ∈ l, c ≤ (List.tail F).length) :
    l.length * c ≤ (l.map (fun F => (List.tail F).length)).sum := by
  induction l with
  | nil => simp
  | cons F l ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have h1 := h F List.mem_cons_self
    have h2 := ih (fun G hG => h G (List.mem_cons_of_mem _ hG))
    rw [Nat.succ_mul]; omega

section Pieces

variable {s : ℕ} {par : α → α} {rest : List α} {root : α}

/-- **Parent edges are partitioned**: the tails of the pieces are, as a multiset, exactly the non-root vertices.
Hence every non-root vertex is a non-top member of exactly one piece. -/
theorem pieces_tails_perm (hs : 2 ≤ s) (ht : TreeOrder par rest root) :
    (pieces s par rest root).flatMap List.tail ~ rest := by
  have hI := inv_run hs ht
  obtain ⟨t, ht0⟩ := hI.head root (by simp)
  have htails := hI.tails
  simp only [List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, ht0,
    List.tail_cons] at htails
  unfold pieces
  cases hG : (run s par rest).groups.getLast? with
  | none =>
    have hnil : (run s par rest).groups = [] := List.getLast?_eq_none_iff.mp hG
    rw [hnil] at htails
    simpa [ht0] using htails
  | some G =>
    have hsplit : (run s par rest).groups = (run s par rest).groups.dropLast ++ [G] := by
      have := List.dropLast_append_getLast? (l := (run s par rest).groups) G (by rw [hG]; rfl)
      exact this.symm
    rw [hsplit] at htails
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, ht0,
      List.cons_append, List.tail_cons]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil] at htails
    refine List.Perm.trans ?_ htails
    calc (run s par rest).groups.dropLast.flatMap List.tail ++ (t ++ G.tail)
        ~ t ++ ((run s par rest).groups.dropLast.flatMap List.tail ++ G.tail) := by
          rw [← List.append_assoc, ← List.append_assoc]
          exact List.perm_append_comm.append_right _
      _ = t ++ ((run s par rest).groups.dropLast.flatMap List.tail ++ G.tail) := rfl

/-- **Pieces are rooted subtrees**: every piece is nonempty and every non-head member has its parent in the
piece. -/
theorem pieces_rooted (hs : 2 ≤ s) (ht : TreeOrder par rest root) :
    ∀ F ∈ pieces s par rest root, F ≠ [] ∧ ∀ x ∈ F.tail, par x ∈ F := by
  have hI := inv_run hs ht
  obtain ⟨t, ht0⟩ := hI.head root (by simp)
  have hrootR := hI.rooted root (by simp)
  unfold pieces
  cases hG : (run s par rest).groups.getLast? with
  | none =>
    intro F hF
    simp only [List.mem_singleton] at hF
    subst hF
    exact ⟨by simp [ht0], fun x hx => hrootR x hx⟩
  | some G =>
    have hGmem : G ∈ (run s par rest).groups := List.mem_of_getLast? hG
    intro F hF
    simp only [List.mem_append, List.mem_singleton] at hF
    rcases hF with hF | hF
    · have hFg : F ∈ (run s par rest).groups := List.dropLast_subset _ hF
      exact ⟨hI.gne F hFg, hI.grooted F hFg⟩
    · subst hF
      refine ⟨by simp [ht0], ?_⟩
      intro x hx
      rw [ht0] at hx ⊢
      simp only [List.cons_append, List.tail_cons, List.mem_append] at hx
      rcases hx with hx | hx
      · have := hrootR x (by rw [ht0]; exact hx)
        rw [ht0] at this
        simp only [List.cons_append, List.mem_cons, List.mem_append] at this ⊢
        tauto
      · -- `x ∈ G.tail`: its parent is in `G`, i.e. the top of `G` (in the root accumulator) or in `G.tail`
        have hpx := hI.grooted G hGmem x hx
        obtain ⟨g, gt, hGg⟩ : ∃ g gt, G = g :: gt := by
          cases G with
          | nil => exact absurd rfl (hI.gne [] hGmem)
          | cons g gt => exact ⟨g, gt, rfl⟩
        rw [hGg] at hpx hx
        simp only [List.mem_cons] at hpx
        rcases hpx with hpx | hpx
        · -- the top `g` of the last group lies in the root's accumulator
          obtain ⟨w, hw, hgw⟩ := hI.lastTop G g hG (by rw [hGg]; rfl)
          simp only [List.nil_append, List.mem_singleton] at hw
          subst hw
          rw [ht0] at hgw
          rw [hpx]
          simp only [List.cons_append, List.mem_cons, List.mem_append] at hgw ⊢
          tauto
        · simp only [List.cons_append, List.mem_cons, List.mem_append]
          rw [hGg]; simp only [List.tail_cons]
          tauto

/-- **Piece sizes**: every piece has fewer than `3s` vertices. -/
theorem pieces_size_lt (hs : 2 ≤ s) (ht : TreeOrder par rest root) :
    ∀ F ∈ pieces s par rest root, F.length < 3 * s := by
  have hI := inv_run hs ht
  have hsmall := hI.small root (by simp)
  unfold pieces
  cases hG : (run s par rest).groups.getLast? with
  | none =>
    intro F hF; simp only [List.mem_singleton] at hF; subst hF; omega
  | some G =>
    have hGmem : G ∈ (run s par rest).groups := List.mem_of_getLast? hG
    intro F hF
    simp only [List.mem_append, List.mem_singleton] at hF
    rcases hF with hF | hF
    · have := (hI.gsize F (List.dropLast_subset _ hF)).2; omega
    · subst hF
      have := (hI.gsize G hGmem).2
      rw [List.length_append, List.length_tail]; omega

/-- **Piece sizes, lower bound**: if the tree has at least `s` vertices, every piece has at least `s` vertices. -/
theorem pieces_size_ge (hs : 2 ≤ s) (ht : TreeOrder par rest root) (hT : s ≤ rest.length + 1) :
    ∀ F ∈ pieces s par rest root, s ≤ F.length := by
  have hI := inv_run hs ht
  have hsmall := hI.small root (by simp)
  obtain ⟨t, ht0⟩ := hI.head root (by simp)
  unfold pieces
  cases hG : (run s par rest).groups.getLast? with
  | none =>
    exfalso
    have hnil : (run s par rest).groups = [] := List.getLast?_eq_none_iff.mp hG
    have htails := hI.tails
    simp only [List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, ht0,
      List.tail_cons, hnil] at htails
    have hlen := htails.length_eq
    rw [ht0] at hsmall
    simp at hsmall hlen
    omega
  | some G =>
    have hGmem : G ∈ (run s par rest).groups := List.mem_of_getLast? hG
    intro F hF
    simp only [List.mem_append, List.mem_singleton] at hF
    rcases hF with hF | hF
    · exact (hI.gsize F (List.dropLast_subset _ hF)).1
    · subst hF
      have h1 := (hI.gsize G hGmem).1
      rw [List.length_append, List.length_tail, ht0]
      simp only [List.length_cons]
      omega

/-- **Pivot bound**: at most `|rest| / (s-1)` pieces when the tree has at least `s` vertices. -/
theorem pieces_count (hs : 2 ≤ s) (ht : TreeOrder par rest root) (hT : s ≤ rest.length + 1) :
    (pieces s par rest root).length * (s - 1) ≤ rest.length := by
  have hperm := pieces_tails_perm hs ht
  have hge := pieces_size_ge hs ht hT
  have hlen : ((pieces s par rest root).flatMap List.tail).length = rest.length := hperm.length_eq
  rw [List.length_flatMap] at hlen
  rw [← hlen]
  have : ∀ F ∈ pieces s par rest root, s - 1 ≤ (List.tail F).length := by
    intro F hF; rw [List.length_tail]; have := hge F hF; omega
  exact len_mul_le_sum _ (s - 1) this

/-- **Cover**: every tree vertex lies in some piece. -/
theorem pieces_cover (hs : 2 ≤ s) (ht : TreeOrder par rest root) :
    ∀ x ∈ rest ++ [root], ∃ F ∈ pieces s par rest root, x ∈ F := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · have hperm := pieces_tails_perm hs ht
    obtain ⟨F, hF, hxF⟩ := List.mem_flatMap.mp (hperm.symm.subset hx)
    exact ⟨F, hF, List.mem_of_mem_tail hxF⟩
  · simp only [List.mem_singleton] at hx
    subst hx
    have hI := inv_run hs ht
    obtain ⟨t, ht0⟩ := hI.head x (by simp)
    unfold pieces
    cases hG : (run s par rest).groups.getLast? with
    | none => exact ⟨_, List.mem_singleton_self _, by rw [ht0]; simp⟩
    | some G => exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by rw [ht0]; simp⟩

end Pieces


/-- A member's image is a sublist of the `flatMap`. -/
theorem sublist_flatMap_of_mem' {β γ : Type*} (f : β → List γ) {l : List β} {a : β} (h : a ∈ l) :
    (f a).Sublist (l.flatMap f) := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rw [List.flatMap_cons]
    rcases List.mem_cons.mp h with h | h
    · subst h; exact List.sublist_append_left _ _
    · exact (ih h).trans (List.sublist_append_right _ _)

/-! ### Pieces are duplicate-free (needed for exact list-level Layer-B refinement of MakePivots) -/

/-- Group tops do not occur in their own tails. -/
def GTop (st : PState α) : Prop := ∀ G ∈ st.groups, ∀ g t, G = g :: t → g ∉ t

theorem gtop_step {s : ℕ} {par : α → α} {rest : List α} {root : α} (ht : TreeOrder par rest root)
    {pre post : List α} {v : α} (hrest : rest = pre ++ v :: post) {st : PState α}
    (hI : Inv s par root pre (v :: post) st) (hG : GTop st) : GTop (step s par st v) := by
  have hnd : rest.Nodup := ht.nodup
  have hp : par v ∈ post ∨ par v = root := ht.childFirst pre post v hrest
  have hppre : par v ∉ pre := by
    intro h
    rcases hp with h' | h'
    · rw [hrest] at hnd
      exact (List.nodup_append.mp hnd).2.2 (par v) h (par v) (List.mem_cons_of_mem _ h') rfl
    · exact ht.root_nmem (by rw [hrest, ← h']; exact List.mem_append_left _ h)
  have hpv : par v ≠ v := by
    intro h
    rcases hp with h' | h'
    · rw [hrest] at hnd
      have := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
      exact this (h ▸ h')
    · exact ht.root_nmem (by rw [hrest, ← h, h']; simp)
  have hpA0 : par v ∈ (v :: post) ++ [root] := by
    rcases hp with h' | h'
    · simp [h']
    · simp [h']
  have hvA0 : v ∈ (v :: post) ++ [root] := by simp
  obtain ⟨tp, htp⟩ := hI.head (par v) hpA0
  obtain ⟨tv, htv⟩ := hI.head v hvA0
  -- tails of active containers lie in `pre`
  have hsub : ∀ w ∈ (v :: post) ++ [root], ∀ x ∈ (st.acc w).tail, x ∈ pre := by
    intro w hw x hx
    exact hI.tails.subset (List.mem_append_left _ (List.mem_flatMap.mpr ⟨w, hw, hx⟩))
  unfold step
  split_ifs with hc
  · intro G hG' g t hGt
    simp only [List.mem_append, List.mem_singleton] at hG'
    rcases hG' with hG' | hG'
    · exact hG G hG' g t hGt
    · subst hG'
      rw [htp, htv] at hGt
      simp only [List.cons_append, List.cons.injEq] at hGt
      obtain ⟨rfl, rfl⟩ := hGt
      simp only [List.mem_append, List.mem_cons, not_or]
      refine ⟨fun h => hppre (hsub _ hpA0 _ (by rw [htp]; exact h)), fun h => hpv h, fun h => hppre
        (hsub _ hvA0 _ (by rw [htv]; exact h))⟩
  · exact hG

theorem gtop_prefix {s : ℕ} (hs : 2 ≤ s) {par : α → α} {rest : List α} {root : α}
    (ht : TreeOrder par rest root) :
    ∀ n, n ≤ rest.length → GTop ((rest.take n).foldl (step s par) init) := by
  intro n
  induction n with
  | zero => intro _ G hG; simp [init] at hG
  | succ n ih =>
    intro hn
    have hlt : n < rest.length := by omega
    have hdrop : rest.drop n = rest[n] :: rest.drop (n + 1) := List.drop_eq_getElem_cons hlt
    have htake : rest.take (n + 1) = rest.take n ++ [rest[n]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hlt]; rfl
    have hrest : rest = rest.take n ++ rest[n] :: rest.drop (n + 1) := by
      rw [← hdrop, List.take_append_drop]
    have hI := inv_prefix hs ht n (by omega)
    rw [hdrop] at hI
    rw [htake, List.foldl_append]
    exact gtop_step ht hrest hI (ih (by omega))

/-- **Pieces are duplicate-free.** -/
theorem pieces_nodup {s : ℕ} (hs : 2 ≤ s) {par : α → α} {rest : List α} {root : α}
    (ht : TreeOrder par rest root) : ∀ F ∈ pieces s par rest root, F.Nodup := by
  have hI := inv_run hs ht
  have hG : GTop (run s par rest) := by
    have := gtop_prefix hs ht rest.length le_rfl
    simpa [run] using this
  obtain ⟨t, ht0⟩ := hI.head root (by simp)
  have htails := hI.tails
  simp only [List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, ht0,
    List.tail_cons] at htails
  have hall : (t ++ (run s par rest).groups.flatMap List.tail).Nodup := htails.nodup_iff.mpr ht.nodup
  have hroot_nmem : ∀ x ∈ t ++ (run s par rest).groups.flatMap List.tail, x ≠ root := by
    intro x hx hxr; exact ht.root_nmem (hxr ▸ htails.subset hx)
  unfold pieces
  cases hGl : (run s par rest).groups.getLast? with
  | none =>
    have hnil : (run s par rest).groups = [] := List.getLast?_eq_none_iff.mp hGl
    intro F hF
    simp only [List.mem_singleton] at hF
    subst hF
    rw [ht0, List.nodup_cons]
    refine ⟨fun h => hroot_nmem root (List.mem_append_left _ h) rfl, ?_⟩
    exact (List.nodup_append.mp hall).1
  | some G =>
    have hGmem : G ∈ (run s par rest).groups := List.mem_of_getLast? hGl
    intro F hF
    simp only [List.mem_append, List.mem_singleton] at hF
    -- tails of groups are duplicate-free sublists of the concatenation
    have htailnd : ∀ H ∈ (run s par rest).groups, H.tail.Nodup := by
      intro H hH
      exact ((List.nodup_append.mp hall).2.1).sublist (sublist_flatMap_of_mem' List.tail hH)
    rcases hF with hF | hF
    · have hFg : F ∈ (run s par rest).groups := List.dropLast_subset _ hF
      obtain ⟨g, gt, hFe⟩ : ∃ g gt, F = g :: gt := by
        cases F with
        | nil => exact absurd rfl (hI.gne [] hFg)
        | cons g gt => exact ⟨g, gt, rfl⟩
      rw [hFe, List.nodup_cons]
      refine ⟨hG F hFg g gt hFe, ?_⟩
      have := htailnd F hFg; rwa [hFe] at this
    · subst hF
      rw [ht0]
      simp only [List.cons_append, List.nodup_cons, List.mem_append, not_or]
      refine ⟨⟨fun h => hroot_nmem root (List.mem_append_left _ h) rfl,
        fun h => hroot_nmem root (List.mem_append_right _ (List.mem_flatMap.mpr ⟨G, hGmem, h⟩)) rfl⟩, ?_⟩
      rw [List.nodup_append]
      refine ⟨(List.nodup_append.mp hall).1, htailnd G hGmem, ?_⟩
      intro a ha b hb hab
      subst hab
      exact (List.nodup_append.mp hall).2.2 a ha a (List.mem_flatMap.mpr ⟨G, hGmem, hb⟩) rfl

/-! ### Pieces as rooted trees (for the re-selection charge `CostCharging.bichromatic_ge`) -/

/-- A children-first order gives a depth function: position from the END of `rest ++ [root]`. -/
def depthOf (rest : List α) (root : α) (x : α) : ℕ := (rest ++ [root]).length - (rest ++ [root]).idxOf x

/-- A piece `F` (nonempty, parents of non-head members inside `F`) is a rooted tree over its members, given any
depth function that strictly decreases along parent edges of the piece. -/
def pieceTree (par : α → α) (F : List α) (hF : F ≠ []) (hroot : ∀ x ∈ F.tail, par x ∈ F)
    (dep : α → ℕ) (hdep : ∀ x ∈ F.tail, dep (par x) < dep x) :
    Frontier.CostCharging.RootedTree {x // x ∈ F} where
  par x := if h : x.1 = F.head hF then none else
    some ⟨par x.1, hroot x.1 (by
      obtain ⟨y, hy⟩ := x
      cases F with
      | nil => exact absurd rfl hF
      | cons a t =>
        simp only [List.head_cons] at h
        simp only [List.tail_cons]
        rcases List.mem_cons.mp hy with hy' | hy'
        · exact absurd hy' h
        · exact hy')⟩
  root := ⟨F.head hF, List.head_mem hF⟩
  dep x := dep x.1
  root_par := by simp
  par_some x hx := by
    have : x.1 ≠ F.head hF := fun h => hx (Subtype.ext h)
    simp [this]
  dep_par x p hp := by
    by_cases h : x.1 = F.head hF
    · simp [h] at hp
    · simp only [h, dite_false, Option.some.injEq] at hp
      subst hp
      obtain ⟨y, hy⟩ := x
      cases F with
      | nil => exact absurd rfl hF
      | cons a t =>
        simp only [List.head_cons] at h
        rcases List.mem_cons.mp hy with hy' | hy'
        · exact absurd hy' h
        · exact hdep y (by simpa using hy')


/-- The depth function strictly decreases along parent edges of non-root vertices. -/
theorem depthOf_par {par : α → α} {rest : List α} {root : α} (ht : TreeOrder par rest root) :
    ∀ x ∈ rest, depthOf rest root (par x) < depthOf rest root x := by
  intro x hx
  obtain ⟨pre, post, hrest⟩ := List.append_of_mem hx
  have hnd := ht.nodup
  rw [hrest] at hnd
  have hxpre : x ∉ pre := fun h => (List.nodup_append.mp hnd).2.2 x h x (List.mem_cons_self) rfl
  have hL : rest ++ [root] = pre ++ x :: (post ++ [root]) := by rw [hrest]; simp
  have hcf := ht.childFirst pre post x hrest
  have hpA : par x ∈ post ++ [root] := by
    rcases hcf with h | h
    · exact List.mem_append_left _ h
    · rw [h]; simp
  have hvroot : x ≠ root := fun h => ht.root_nmem (h ▸ hx)
  have hxpost : x ∉ post := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
  have hpx : par x ≠ x := by
    intro h; rw [h] at hpA
    simp only [List.mem_append, List.mem_singleton] at hpA
    rcases hpA with h' | h'
    · exact hxpost h'
    · exact hvroot h'
  have hppre : par x ∉ pre := by
    intro h
    rcases hcf with h' | h'
    · exact (List.nodup_append.mp hnd).2.2 (par x) h (par x) (List.mem_cons_of_mem _ h') rfl
    · exact ht.root_nmem (by rw [hrest, ← h']; exact List.mem_append_left _ h)
  have hix : (rest ++ [root]).idxOf x = pre.length := by
    rw [hL, List.idxOf_append_of_notMem hxpre, List.idxOf_cons_self]; simp
  have hip : pre.length < (rest ++ [root]).idxOf (par x) := by
    rw [hL, List.idxOf_append_of_notMem hppre, List.idxOf_cons_ne _ (fun h => hpx h.symm)]
    omega
  have hlt : (rest ++ [root]).idxOf (par x) < (rest ++ [root]).length := by
    rw [List.idxOf_lt_length_iff]
    rcases hcf with h | h
    · rw [hrest]; simp [h]
    · rw [h]; simp
  unfold depthOf
  omega

/-! ### MakePivots over the pieces (B1 MP.1–MP.10) -/

section MakePivots

variable (S Q : Finset α)

/-- One piece: collect its unassigned `S \ Q` members as a new group (if nonempty). -/
def mpStep (acc : List (List α) × Finset α) (F : List α) : List (List α) × Finset α :=
  let cur := (F.filter (fun x => decide (x ∈ S ∧ x ∉ Q ∧ x ∉ acc.2))).dedup
  if cur = [] then acc else (acc.1 ++ [cur], acc.2 ∪ cur.toFinset)

/-- MakePivots: groups from the pieces, in piece order; every `S \ Q` vertex goes to the first piece containing it. -/
def makePivots (pcs : List (List α)) : List (List α) := (pcs.foldl (mpStep S Q) ([], ∅)).1

/-- Invariant of the MakePivots fold. -/
structure MPInv (seen : List (List α)) (acc : List (List α) × Finset α) : Prop where
  ne : ∀ g ∈ acc.1, g ≠ []
  sub : ∀ g ∈ acc.1, ∀ x ∈ g, x ∈ S ∧ x ∉ Q
  nodup : ∀ g ∈ acc.1, g.Nodup
  assigned : ∀ x, x ∈ acc.2 ↔ ∃ g ∈ acc.1, x ∈ g
  disj : acc.1.Pairwise (fun g g' => ∀ x ∈ g, x ∉ g')
  cover : ∀ F ∈ seen, ∀ x ∈ F, x ∈ S → x ∉ Q → x ∈ acc.2
  small : ∀ g ∈ acc.1, ∃ F ∈ seen, ∀ x ∈ g, x ∈ F
  count : acc.1.length ≤ seen.length

theorem mpInv_nil : MPInv S Q [] ([], ∅) where
  ne g h := by simp at h
  sub g h := by simp at h
  nodup g h := by simp at h
  assigned x := by simp
  disj := List.Pairwise.nil
  cover F h := by simp at h
  small g h := by simp at h
  count := le_rfl

theorem mpInv_step {seen : List (List α)} {acc : List (List α) × Finset α} (h : MPInv S Q seen acc)
    (F : List α) : MPInv S Q (seen ++ [F]) (mpStep S Q acc F) := by
  have hdef : mpStep S Q acc F =
      if (F.filter (fun x => decide (x ∈ S ∧ x ∉ Q ∧ x ∉ acc.2))).dedup = [] then acc
      else (acc.1 ++ [(F.filter (fun x => decide (x ∈ S ∧ x ∉ Q ∧ x ∉ acc.2))).dedup],
        acc.2 ∪ ((F.filter (fun x => decide (x ∈ S ∧ x ∉ Q ∧ x ∉ acc.2))).dedup).toFinset) := rfl
  rw [hdef]
  generalize hcur : (F.filter (fun x => decide (x ∈ S ∧ x ∉ Q ∧ x ∉ acc.2))).dedup = cur
  have hmem : ∀ x, x ∈ cur ↔ x ∈ F ∧ x ∈ S ∧ x ∉ Q ∧ x ∉ acc.2 := by
    intro x; rw [← hcur, List.mem_dedup, List.mem_filter]; simp
  have hnd : cur.Nodup := by rw [← hcur]; exact List.nodup_dedup _
  by_cases hc : cur = []
  · rw [if_pos hc]
    constructor
    · exact h.ne
    · exact h.sub
    · exact h.nodup
    · exact h.assigned
    · exact h.disj
    · intro G hG x hx hxS hxQ
      rcases List.mem_append.mp hG with hG | hG
      · exact h.cover G hG x hx hxS hxQ
      · simp only [List.mem_singleton] at hG; subst hG
        by_contra hna
        have : x ∈ cur := (hmem x).mpr ⟨hx, hxS, hxQ, hna⟩
        rw [hc] at this; simp at this
    · intro g hg
      obtain ⟨G, hG, hgG⟩ := h.small g hg
      exact ⟨G, List.mem_append_left _ hG, hgG⟩
    · have := h.count; simp; omega
  · rw [if_neg hc]
    constructor
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact h.ne g hg
      · simp only [List.mem_singleton] at hg; subst hg; exact hc
    · intro g hg x hx
      rcases List.mem_append.mp hg with hg | hg
      · exact h.sub g hg x hx
      · simp only [List.mem_singleton] at hg; subst hg
        have := (hmem x).mp hx; exact ⟨this.2.1, this.2.2.1⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact h.nodup g hg
      · simp only [List.mem_singleton] at hg; subst hg; exact hnd
    · intro x
      simp only [Finset.mem_union, List.mem_toFinset, h.assigned x, List.mem_append, List.mem_singleton]
      constructor
      · rintro (⟨g, hg, hxg⟩ | hx)
        · exact ⟨g, Or.inl hg, hxg⟩
        · exact ⟨cur, Or.inr rfl, hx⟩
      · rintro ⟨g, hg | hg, hxg⟩
        · exact Or.inl ⟨g, hg, hxg⟩
        · subst hg; exact Or.inr hxg
    · rw [List.pairwise_append]
      refine ⟨h.disj, List.pairwise_singleton _ _, ?_⟩
      intro g hg g' hg' x hxg hxg'
      simp only [List.mem_singleton] at hg'; subst hg'
      have := (hmem x).mp hxg'
      exact this.2.2.2 ((h.assigned x).mpr ⟨g, hg, hxg⟩)
    · intro G hG x hx hxS hxQ
      simp only [Finset.mem_union, List.mem_toFinset]
      rcases List.mem_append.mp hG with hG | hG
      · exact Or.inl (h.cover G hG x hx hxS hxQ)
      · simp only [List.mem_singleton] at hG; subst hG
        by_cases hna : x ∈ acc.2
        · exact Or.inl hna
        · exact Or.inr ((hmem x).mpr ⟨hx, hxS, hxQ, hna⟩)
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨G, hG, hgG⟩ := h.small g hg
        exact ⟨G, List.mem_append_left _ hG, hgG⟩
      · simp only [List.mem_singleton] at hg; subst hg
        exact ⟨F, List.mem_append_right _ (List.mem_singleton_self _), fun x hx => ((hmem x).mp hx).1⟩
    · have := h.count; simp; omega

theorem mpInv_fold (pcs : List (List α)) :
    MPInv S Q pcs (pcs.foldl (mpStep S Q) ([], ∅)) := by
  have key : ∀ (l : List (List α)) (seen : List (List α)) acc, MPInv S Q seen acc →
      MPInv S Q (seen ++ l) (l.foldl (mpStep S Q) acc) := by
    intro l
    induction l with
    | nil => intro seen acc h; simpa using h
    | cons F l ih =>
      intro seen acc h
      have := ih (seen ++ [F]) _ (mpInv_step S Q h F)
      simpa [List.append_assoc] using this
  simpa using key pcs [] ([], ∅) (mpInv_nil S Q)



/-- **MakePivots contract** (B1 MP.1–MP.10 with the cost facts). -/
theorem makePivots_spec (pcs : List (List α)) :
    (∀ g ∈ makePivots S Q pcs, g ≠ [] ∧ g.Nodup ∧ ∀ x ∈ g, x ∈ S ∧ x ∉ Q) ∧
    (makePivots S Q pcs).Pairwise (fun g g' => ∀ x ∈ g, x ∉ g') ∧
    (∀ F ∈ pcs, ∀ x ∈ F, x ∈ S → x ∉ Q → ∃ g ∈ makePivots S Q pcs, x ∈ g) ∧
    (∀ g ∈ makePivots S Q pcs, ∃ F ∈ pcs, ∀ x ∈ g, x ∈ F) ∧
    (makePivots S Q pcs).length ≤ pcs.length := by
  have h := mpInv_fold S Q pcs
  refine ⟨fun g hg => ⟨h.ne g hg, h.nodup g hg, h.sub g hg⟩, h.disj, ?_, h.small, h.count⟩
  intro F hF x hx hxS hxQ
  exact (h.assigned x).mp (h.cover F hF x hx hxS hxQ)

/-- Groups are no larger than their pieces (dedup'd sub-multisets of a piece). -/
theorem group_length_le {g F : List α} (hnd : g.Nodup) (hsub : ∀ x ∈ g, x ∈ F) : g.length ≤ F.length := by
  calc g.length = g.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ F.toFinset.card := Finset.card_le_card (fun x hx => by
        rw [List.mem_toFinset] at hx ⊢; exact hsub x hx)
    _ ≤ F.length := List.toFinset_card_le F

end MakePivots

/-! ### Cost of the partition (linked-list implementation)

In the RAM implementation each accumulator is a linked list with head, tail and length fields, so `step` costs
`O(1)`: one parent read, one splice, one comparison of lengths, one pointer reset, one append of a group pointer.
`run` therefore costs `O(|rest|)`. `pieces` costs `O(1)`: one splice of the root's list onto the last group's tail.
MakePivots scans every piece once with O(1) bitmap tests per member, for a total of `O(Σ_F |F| + #pieces)`.
The next lemma bounds `Σ_F |F|` by `|rest| + #pieces ≤ 2|T|`, so the whole partition-plus-grouping is `O(|T|)` per
tree. -/

/-- For nonempty lists, total length = total tail length + number of lists. -/
theorem sum_length_eq {β : Type*} (l : List (List β)) (hne : ∀ F ∈ l, F ≠ []) :
    (l.map List.length).sum = (l.flatMap List.tail).length + l.length := by
  induction l with
  | nil => simp
  | cons F l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, List.flatMap_cons, List.length_append]
    have hF := hne F List.mem_cons_self
    have := ih (fun G hG => hne G (List.mem_cons_of_mem _ hG))
    have hFl : F.length = F.tail.length + 1 := by
      cases F with
      | nil => exact absurd rfl hF
      | cons a t => simp
    omega

theorem pieces_total_length {s : ℕ} (hs : 2 ≤ s) {par : α → α} {rest : List α} {root : α}
    (ht : TreeOrder par rest root) :
    ((pieces s par rest root).map List.length).sum = rest.length + (pieces s par rest root).length := by
  have hperm := pieces_tails_perm hs ht
  rw [sum_length_eq _ (fun F hF => (pieces_rooted hs ht F hF).1), hperm.length_eq]


/-! ### Tree records produced by FindPivots, and their re-rooting on contact

A tree record lists its vertices in PARENT-BEFORE-CHILD order (`ord`, head = root) with a parent function. A
FindPivots search yields such an order for its `K`: extracted vertices in extraction order (each `kpar` tail was
extracted earlier), then the unextracted members, whose `kpar` tails are extracted. A contact merge attaches `K`
to an existing tree through the scanned edge `(u, v)` (`u ∈ K`, `v ∈ T`) after re-rooting `K` at `u`: the `K`-path
from `u` up to its root is listed first (reversed pointers), followed by the other `K` members in their old order. -/

/-- Parent-before-child order: `ord` is duplicate-free with head `root`, and every later member's parent occurs
strictly earlier in `ord`. -/
def ParentFirst (par : α → α) (root : α) (ord : List α) : Prop :=
  ord.Nodup ∧ ord.head? = some root ∧
    ∀ (pre post : List α) (v : α), ord = pre ++ v :: post → pre ≠ [] → par v ∈ pre

/-- A parent-first order gives the children-first `TreeOrder` of Algorithm 5 on the reversed tail. -/
theorem treeOrder_of_parentFirst {par : α → α} {root : α} {ord : List α} (h : ParentFirst par root ord) :
    TreeOrder par ord.tail.reverse root := by
  obtain ⟨hnd, hhead, hpar⟩ := h
  obtain ⟨t, rfl⟩ : ∃ t, ord = root :: t := by
    cases ord with
    | nil => simp at hhead
    | cons a t => simp only [List.head?_cons, Option.some.injEq] at hhead; exact ⟨t, by rw [hhead]⟩
  simp only [List.tail_cons]
  rw [List.nodup_cons] at hnd
  refine ⟨List.nodup_reverse.mpr hnd.2, by simpa using hnd.1, ?_⟩
  intro pre post v hrev
  -- `t = post.reverse ++ v :: pre.reverse`
  have ht : t = post.reverse ++ v :: pre.reverse := by
    have := congrArg List.reverse hrev
    simpa using this
  have hp := hpar (root :: post.reverse) pre.reverse v (by rw [ht]; simp) (by simp)
  simp only [List.mem_cons, List.mem_reverse] at hp
  rcases hp with hp | hp
  · exact Or.inr hp
  · exact Or.inl hp


/-- Re-rooting along a path `[w₀, w₁, …]`: `w₀ ↦ prev`, `w_{i+1} ↦ w_i`, everything else unchanged. -/
def reroot : List α → α → (α → α) → (α → α)
  | [], _, f => f
  | w :: ws, prev, f => reroot ws w (Function.update f w prev)

theorem reroot_not_mem {path : List α} {prev : α} {f : α → α} {y : α} (hy : y ∉ path) :
    reroot path prev f y = f y := by
  induction path generalizing prev f with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.mem_cons, not_or] at hy
    simp only [reroot]
    rw [ih hy.2, Function.update_of_ne hy.1]

/-- On a duplicate-free path, `reroot` maps the head to `prev` and each later member to its predecessor. -/
theorem reroot_head {w : α} {ws : List α} {prev : α} {f : α → α} (hnd : (w :: ws).Nodup) :
    reroot (w :: ws) prev f w = prev := by
  simp only [reroot]
  rw [List.nodup_cons] at hnd
  rw [reroot_not_mem hnd.1]; simp

theorem reroot_succ : ∀ {path : List α} {prev : α} {f : α → α} (_ : path.Nodup) (pre post : List α) (a b : α),
    path = pre ++ a :: b :: post → reroot path prev f b = a
  | [], _, _, _, pre, post, a, b, h => by simp at h
  | w :: ws, prev, f, hnd, pre, post, a, b, h => by
    simp only [reroot]
    rw [List.nodup_cons] at hnd
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact reroot_head hnd.2
    | cons c pre =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, hws⟩ := h
      exact reroot_succ hnd.2 pre post a b hws


/-- In a duplicate-free list, the prefix before a given element is unique. -/
theorem prefix_unique_of_nodup {l f g b post : List α} {w : α} (hnd : l.Nodup)
    (h1 : l = b ++ w :: post) (h2 : l = f ++ w :: g) : b = f := by
  have hwb : w ∉ b := by
    rw [h1] at hnd; exact fun hm => (List.nodup_append.mp hnd).2.2 w hm w List.mem_cons_self rfl
  have hwf : w ∉ f := by
    rw [h2] at hnd; exact fun hm => (List.nodup_append.mp hnd).2.2 w hm w List.mem_cons_self rfl
  have i1 : l.idxOf w = b.length := by
    rw [h1, List.idxOf_append_of_notMem hwb, List.idxOf_cons_self]; simp
  have i2 : l.idxOf w = f.length := by
    rw [h2, List.idxOf_append_of_notMem hwf, List.idxOf_cons_self]; simp
  have hb : b = l.take b.length := by rw [h1]; simp
  have hf : f = l.take f.length := by rw [h2]; simp
  rw [hb, hf, ← i1, ← i2]

/-- **Contact merge.** Attaching a search tree `K` (parent-first order `kord` rooted at `x`, parents `kpar`) to a
tree `T` (parent-first `ord` rooted at `r`, parents `par`) through the edge `(u, v)` with `v ∈ T`, after re-rooting
`K` at `u` along the `kpar`-path `path` from `u` to `x`, gives a parent-first order of the merged tree. -/
theorem mergeAt_parentFirst {par kpar : α → α} {r x u v : α} {ord kord path : List α}
    (hT : ParentFirst par r ord) (hK : ParentFirst kpar x kord)
    (hdisj : ∀ y ∈ ord, y ∉ kord) (hv : v ∈ ord)
    (hpath : path.Nodup) (hpk : ∀ y ∈ path, y ∈ kord) (hx : x ∈ path) (hhead : path.head? = some u)
    (hstep : ∀ pre post a b, path = pre ++ a :: b :: post → b = kpar a) :
    ParentFirst (reroot path v (fun w => if w ∈ kord then kpar w else par w)) r
      (ord ++ path ++ kord.filter (fun y => y ∉ path)) := by
  classical
  obtain ⟨hnd, hhd, hpar⟩ := hT
  obtain ⟨hknd, hkhd, hkpar⟩ := hK
  set oth := kord.filter (fun y => y ∉ path) with hoth
  have hothnd : oth.Nodup := hknd.filter _
  have hmem_oth : ∀ y, y ∈ oth ↔ y ∈ kord ∧ y ∉ path := by
    intro y; rw [hoth, List.mem_filter]; simp
  refine ⟨?_, ?_, ?_⟩
  · -- nodup
    rw [List.append_assoc, List.nodup_append, List.nodup_append]
    refine ⟨hnd, ⟨hpath, hothnd, ?_⟩, ?_⟩
    · intro a ha b hb hab; subst hab; exact ((hmem_oth a).mp hb).2 ha
    · intro a ha b hb hab; subst hab
      rcases List.mem_append.mp hb with hb | hb
      · exact hdisj a ha (hpk a hb)
      · exact hdisj a ha ((hmem_oth a).mp hb).1
  · -- head
    cases ord with
    | nil => simp at hhd
    | cons a t => simpa using hhd
  · intro pre post w hdec hpre
    have hdec' : ord ++ (path ++ oth) = pre ++ w :: post := by rw [← hdec, List.append_assoc]
    rcases List.append_eq_append_iff.mp hdec' with ⟨a', hpre', hrest⟩ | ⟨c', hord', hwpost⟩
    · -- `w` lies in `path ++ oth`, `pre = ord ++ a'`
      rcases List.append_eq_append_iff.mp hrest with ⟨b', ha', hoth'⟩ | ⟨c', hpath', hw⟩
      · -- `w ∈ oth`, `a' = path ++ b'`, `oth = b' ++ w :: post`
        have hwo : w ∈ oth := by rw [hoth']; simp
        obtain ⟨hwk, hwp⟩ := (hmem_oth w).mp hwo
        have hwx : w ≠ x := fun h => hwp (h ▸ hx)
        rw [reroot_not_mem hwp]
        simp only [hwk, if_true]
        obtain ⟨preK, postK, hk⟩ := List.append_of_mem hwk
        have hpreK : preK ≠ [] := by
          rintro rfl
          simp only [List.nil_append] at hk
          rw [hk] at hkhd; simp at hkhd; exact hwx hkhd
        have hkp := hkpar preK postK w hk hpreK
        rw [hpre', ha']
        by_cases hkpath : kpar w ∈ path
        · simp [hkpath]
        · -- `kpar w ∈ oth`, before `w`: it lies in `b'`
          have hfilt : oth = preK.filter (fun y => y ∉ path) ++ w :: postK.filter (fun y => y ∉ path) := by
            rw [hoth, hk, List.filter_append, List.filter_cons]; simp [hwp]
          have hb' : b' = preK.filter (fun y => y ∉ path) := prefix_unique_of_nodup hothnd hoth' hfilt
          have : kpar w ∈ b' := by rw [hb', List.mem_filter]; simp [hkp, hkpath]
          simp [this]
      · -- `w ∈ path`
        cases c' with
        | nil =>
          -- `w` is the first element of `oth`
          simp only [List.nil_append] at hw
          simp only [List.append_nil] at hpath'
          have hwo : w ∈ oth := by rw [← hw]; simp
          obtain ⟨hwk, hwp⟩ := (hmem_oth w).mp hwo
          have hwx : w ≠ x := fun h => hwp (h ▸ hx)
          rw [reroot_not_mem hwp]
          simp only [hwk, if_true]
          obtain ⟨preK, postK, hk⟩ := List.append_of_mem hwk
          have hpreK : preK ≠ [] := by
            rintro rfl
            simp only [List.nil_append] at hk
            rw [hk] at hkhd; simp at hkhd; exact hwx hkhd
          have hkp := hkpar preK postK w hk hpreK
          rw [hpre', ← hpath']
          by_cases hkpath : kpar w ∈ path
          · simp [hkpath]
          · exfalso
            -- `kpar w ∈ oth` before `w`, but `w` is the first element of `oth`
            have hfilt : oth = preK.filter (fun y => y ∉ path) ++ w :: postK.filter (fun y => y ∉ path) := by
              rw [hoth, hk, List.filter_append, List.filter_cons]; simp [hwp]
            have hb' : ([] : List α) = preK.filter (fun y => y ∉ path) :=
              prefix_unique_of_nodup hothnd (by rw [← hw]; rfl) hfilt
            have : kpar w ∈ preK.filter (fun y => y ∉ path) := by rw [List.mem_filter]; simp [hkp, hkpath]
            rw [← hb'] at this; simp at this
        | cons w' c'' =>
          simp only [List.cons_append, List.cons.injEq] at hw
          obtain ⟨rfl, -⟩ := hw
          -- `path = a' ++ w :: c''`
          rw [hpre']
          rcases List.eq_nil_or_concat a' with ha | ⟨a'', z, ha⟩
          · subst ha
            -- `w` is the head `u` of the path: re-rooted parent `v ∈ ord`
            simp only [List.nil_append] at hpath'
            rw [hpath', reroot_head (hpath' ▸ hpath)]
            exact List.mem_append_left _ hv
          · subst ha
            have hpz : path = a'' ++ z :: w :: c'' := by rw [hpath']; simp
            rw [reroot_succ hpath a'' c'' z w hpz]
            simp
    · -- `w ∈ ord`, `ord = pre ++ c'`
      cases c' with
      | nil =>
        simp only [List.append_nil] at hord'
        simp only [List.nil_append] at hwpost
        -- `w` is the first element of `path ++ oth`, i.e. the head `u` of the (nonempty) path; `pre = ord`
        cases path with
        | nil => simp at hx
        | cons p0 ps =>
          simp only [List.cons_append, List.cons.injEq] at hwpost
          obtain ⟨rfl, -⟩ := hwpost
          rw [reroot_head hpath]
          rw [hord'] at hv; simpa using hv
      | cons w' c'' =>
        simp only [List.cons_append, List.cons.injEq] at hwpost
        obtain ⟨rfl, -⟩ := hwpost
        have hwo : w ∈ ord := by rw [hord']; simp
        have hwk : w ∉ kord := hdisj w hwo
        have hwp : w ∉ path := fun h => hwk (hpk w h)
        rw [reroot_not_mem hwp]
        simp only [hwk, if_false]
        exact hpar pre c'' w (by rw [← hord']) hpre


/-! ### From the FindPivots forest to the pivot groups -/

/-- A tree of a FindPivots invocation: root, parent-first vertex order, parent function. -/
structure TreeRec (α : Type*) where
  root : α
  ord : List α
  par : α → α

/-- All pieces of all trees (DMSY26 Lemma A.1 applied per tree, with `s = k`). -/
def forestPieces (k : ℕ) (trees : List (TreeRec α)) : List (List α) :=
  trees.flatMap (fun T => pieces k T.par T.ord.tail.reverse T.root)

theorem length_ord_of_parentFirst {par : α → α} {root : α} {ord : List α} (h : ParentFirst par root ord) :
    ord.length = ord.tail.reverse.length + 1 := by
  obtain ⟨-, hhead, -⟩ := h
  cases ord with
  | nil => simp at hhead
  | cons a t => simp

theorem mem_ord_iff_of_parentFirst {par : α → α} {root : α} {ord : List α} (h : ParentFirst par root ord)
    (x : α) : x ∈ ord ↔ x ∈ ord.tail.reverse ++ [root] := by
  obtain ⟨-, hhead, -⟩ := h
  cases ord with
  | nil => simp at hhead
  | cons a t =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    simp [or_comm]

/-- **Pivot groups of a FindPivots invocation** (the MakePivots cost contract over the whole forest). -/
theorem forest_groups_spec (S Q : Finset α) {k : ℕ} (hk : 2 ≤ k) (trees : List (TreeRec α))
    (hok : ∀ T ∈ trees, ParentFirst T.par T.root T.ord) (hsize : ∀ T ∈ trees, k ≤ T.ord.length) :
    (∀ g ∈ makePivots S Q (forestPieces k trees), g ≠ [] ∧ g.Nodup ∧ ∀ x ∈ g, x ∈ S ∧ x ∉ Q) ∧
    (makePivots S Q (forestPieces k trees)).Pairwise (fun g g' => ∀ x ∈ g, x ∉ g') ∧
    (∀ T ∈ trees, ∀ x ∈ T.ord, x ∈ S → x ∉ Q → ∃ g ∈ makePivots S Q (forestPieces k trees), x ∈ g) ∧
    (∀ g ∈ makePivots S Q (forestPieces k trees), g.length < 3 * k) ∧
    (makePivots S Q (forestPieces k trees)).length * (k - 1) ≤ (trees.map (fun T => T.ord.length - 1)).sum := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := makePivots_spec S Q (forestPieces k trees)
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · intro T hT x hx hxS hxQ
    have hto := treeOrder_of_parentFirst (hok T hT)
    obtain ⟨F, hF, hxF⟩ := pieces_cover hk hto x ((mem_ord_iff_of_parentFirst (hok T hT) x).mp hx)
    exact h3 F (List.mem_flatMap.mpr ⟨T, hT, hF⟩) x hxF hxS hxQ
  · intro g hg
    obtain ⟨F, hF, hgF⟩ := h4 g hg
    obtain ⟨T, hT, hFT⟩ := List.mem_flatMap.mp hF
    have hto := treeOrder_of_parentFirst (hok T hT)
    have hlt := pieces_size_lt hk hto F hFT
    have := group_length_le (h1 g hg).2.1 hgF
    omega
  · calc (makePivots S Q (forestPieces k trees)).length * (k - 1)
        ≤ (forestPieces k trees).length * (k - 1) := Nat.mul_le_mul_right _ h5
      _ ≤ (trees.map (fun T => T.ord.length - 1)).sum := by
        unfold forestPieces
        clear h1 h2 h3 h4 h5
        induction trees with
        | nil => simp
        | cons T ts ih =>
          simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons, Nat.add_mul]
          have hT := hok T List.mem_cons_self
          have hto := treeOrder_of_parentFirst hT
          have hlen := length_ord_of_parentFirst hT
          have hcnt := pieces_count hk hto (by have := hsize T List.mem_cons_self; omega)
          have := ih (fun U hU => hok U (List.mem_cons_of_mem _ hU)) (fun U hU => hsize U (List.mem_cons_of_mem _ hU))
          omega

end Frontier.CHD.Partition
