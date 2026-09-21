import Frontier.CostCharging
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Frontier.CostAggregate — C-HD cost composition skeleton, part 3: summing the per-call costs (owner: agent-06)

**NON-GATE.**  Abstract aggregation of the DMSY26 Lemma 3.9 accounting, in the C-HD form (degree `δ = Θ(m/n)`,
FindPivots with leaves, foreign leaves, lazy-linked `D`).  The per-call quantities below are exactly the counters
the Layer-A call relation (L2–L4) must expose; the hypotheses in `CallCounters.Valid` are the structural facts
L4/L2 prove about them.  The conclusion `total_cost_le` bounds the total cost by

  `c · [ (2(k+1) + 2t/(k-1) + 5) · |V| · (Lmax+1) + 4 t |E| + M0 ]`,

which the term menu of `Frontier.CostSkeleton` turns into `O(Tchd n m)` (with `|V| = O(n)`, `|E| = O(m)` after
degree reduction, `k = kpar`, `t = tpar`, `Lmax + 1 ≤ 2 Lpar`).

Per call `X` (`V` = vertices after degree reduction, `E` = edges):
* `U X` returned set, `S X` input frontier, `Q X` failed-search roots, `Fo X` foreign leaves;
* `J X` edges inserted by Line 24 at `X` (jumps), `Wr X` edges relaxed from `W'` at Lines 34–37,
  `Cr X` tree edges charged by re-selections (crossing edges);
* `p X` pivot count, `mergeCost X` the `D`-merge cost (bounded globally by `M0`, the DS' lemma of L3),
  `cost X` the cost of `X` excluding its children.
-/

namespace Frontier.CostAggregate

open Finset Frontier.CostCharging

set_option linter.unusedSectionVars false

variable {ι V E α : Type*} [Fintype ι] [Fintype V] [Fintype E] [DecidableEq ι] [DecidableEq V]
  [DecidableEq E] [LinearOrder α]

/-- The counters of one execution of the C-HD recursion. -/
structure CallCounters (ι V E α : Type*) [LinearOrder α] where
  F : CallForest ι V α
  src : E → V
  dst : E → V
  val : E → α
  full : ι → Bool
  S : ι → Finset V
  Q : ι → Finset V
  Fo : ι → Finset V
  J : ι → Finset E
  Wr : ι → Finset E
  Cr : ι → Finset E
  /-- re-selection edges of kind (β): tail in `U X`, head a foreign leaf (agent-03, PAPER_CHD §5.3 (ii)) -/
  Be : ι → Finset E
  /-- edges deleted by X's FindPivots (FH.9; each edge at most once globally, Lemma L) -/
  Del : ι → Finset E
  p : ι → ℕ
  mergeCost : ι → ℕ
  cost : ι → ℕ
  /-- base-case calls (level 0: bounded Dijkstra with a BST) -/
  base : ι → Bool

namespace CallCounters

variable (C : CallCounters ι V E α)

/-- `v` belongs to `U X` but to no child of `X` (its deepest call is `X`). -/
def Own (X : ι) (v : V) : Prop := v ∈ C.F.U X ∧ ∀ Y, C.F.parent Y = some X → v ∉ C.F.U Y

/-- The structural facts and the per-call cost inequality.  `t, k` are the C-HD parameters, `c` the
per-operation constant, `Lmax` the maximal depth, `wit` the witness in-edge of a full-call `Q`-appearance
(DMSY26 Lemma 3.9: the edge of the latest INSERTING relaxation into `v` before `X` starts), `inE v` the in-edges
of `v`, `src` the source (the only vertex that may lie in `Q` of a full call without any inserting relaxation;
reviewer #1, O22(C)). -/
structure Valid (t k c Lmax M0 : ℕ) (inE : V → Finset E) (wit : ι → V → E) (src : V) : Prop where
  two_le_k : 2 ≤ k
  k_le_t : k ≤ t
  depth_le : ∀ X, C.F.depth X ≤ Lmax
  /-- jumps lie in the window of `X` (Line 24: `B_child ≤ d[u]+w < B_X`, `u` returned by the child) -/
  jump_window : ∀ X, ∀ e ∈ C.J X, ∃ Y, C.F.parent Y = some X ∧ C.src e ∈ C.F.U Y ∧
      C.F.B Y ≤ C.val e ∧ C.val e < C.F.B X
  /-- `W'` relaxations start at vertices whose deepest call is `X` -/
  wr_own : ∀ X, ∀ e ∈ C.Wr X, C.Own X (C.src e)
  /-- crossing edges: both ends in `U X`, no child contains both (with foreign ends replaced by homes, F3) -/
  cr_cross : ∀ X, ∀ e ∈ C.Cr X, C.src e ∈ C.F.U X ∧ C.dst e ∈ C.F.U X ∧
      ∀ Y, C.F.parent Y = some X → ¬ (C.src e ∈ C.F.U Y ∧ C.dst e ∈ C.F.U Y)
  /-- partial calls have small frontiers, pivots and foreign mass -/
  partial_S : ∀ X, C.full X = false → t * (C.S X).card ≤ (C.F.U X).card
  partial_Fo : ∀ X, C.full X = false → (C.Fo X).card ≤ (C.F.U X).card
  partial_p : ∀ X, C.full X = false → C.p X ≤ (C.S X).card
  /-- full calls: `S ⊆ U`, pivots `≤ (|U| + |Fo|)/(k-1)` -/
  full_S : ∀ X, C.full X = true → C.S X ⊆ C.F.U X
  full_p : ∀ X, C.full X = true → C.p X * (k - 1) ≤ (C.F.U X).card + (C.Fo X).card
  Q_sub : ∀ X, C.Q X ⊆ C.S X
  /-- `Q`-witnesses of full calls: in-edges (for `v ≠ src`), injective per vertex -/
  wit_mem : ∀ X, C.full X = true → ∀ v ∈ C.Q X, v ≠ src → wit X v ∈ inE v
  wit_inj : ∀ v X X', C.full X = true → C.full X' = true → v ∈ C.Q X → v ∈ C.Q X' →
      wit X v = wit X' v → X = X'
  /-- the source lies in `Q` of at most one full call -/
  src_once : ∀ X X', C.full X = true → C.full X' = true → src ∈ C.Q X → src ∈ C.Q X' → X = X'
  inE_card : ∑ v, (inE v).card ≤ Fintype.card E
  /-- foreign leaves of full calls on one level: total at most `|V|` (disjoint full ranges) -/
  foreign_level : ∀ j, ∑ X ∈ univ.filter (fun X => C.F.depth X = j ∧ C.full X = true), (C.Fo X).card
      ≤ Fintype.card V
  merge_total : ∑ X, C.mergeCost X ≤ M0
  /-- kind-(β) edges are charged once in total (discharge: `Frontier.Density.Ranges.beta_sum_le`) -/
  be_total : ∑ X, (C.Be X).card ≤ Fintype.card E
  /-- deletions of different calls are disjoint (a deleted edge leaves `Out(u)` forever) -/
  del_disj : ∀ X X', X ≠ X' → Disjoint (C.Del X) (C.Del X')
  /-- the per-call cost inequality (excluding children) for recursive calls -/
  cost_le : ∀ X, C.base X = false → C.cost X ≤ c * ((k + 1) * ((C.F.U X).card + (C.Fo X).card) + (C.S X).card
      + t * (C.Q X).card + t * ((C.J X).card + (C.Wr X).card + (C.Cr X).card + (C.Be X).card) + t * C.p X
      + (if C.full X then 0 else t * (C.S X).card) + C.mergeCost X + (C.Del X).card)
  /-- base calls have no sub-calls -/
  base_leaf : ∀ X Y, C.base X = true → C.F.parent Y ≠ some X

variable {C}

/-! ### Global counts -/

/-- Jumps: each edge is a jump of at most one call. -/
theorem sum_J_le {t k c Lmax M0 : ℕ} {inE : V → Finset E} {wit : ι → V → E} {src : V}
    (h : C.Valid t k c Lmax M0 inE wit src) : ∑ X, (C.J X).card ≤ Fintype.card E := by
  classical
  rw [← Finset.card_biUnion]
  · exact Finset.card_le_univ _
  · intro X _ X' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    obtain ⟨Y, hY, hu, hw1, hw2⟩ := h.jump_window X e he
    obtain ⟨Y', hY', hu', hw1', hw2'⟩ := h.jump_window X' e he'
    exact C.F.window_unique hY hY' hu hu' hne ⟨hw1, hw2⟩ ⟨hw1', hw2'⟩

/-- `Own` determines the call. -/
theorem own_unique {X X' : ι} {v : V} (h : C.Own X v) (h' : C.Own X' v) : X = X' := by
  rcases C.F.chain_of_mem h.1 h'.1 with ha | ha
  · -- `X'` is an ancestor of `X`; if proper, the child of `X'` on the path contains `v`
    by_contra hne
    have : ∃ Y, C.F.parent Y = some X' ∧ C.F.Anc X Y := by
      cases ha with
      | refl => exact absurd rfl hne
      | tail hh hp => exact ⟨_, hp, hh⟩
    obtain ⟨Y, hY, hXY⟩ := this
    exact h'.2 Y hY (C.F.U_mono_anc hXY h.1)
  · by_contra hne
    have : ∃ Y, C.F.parent Y = some X ∧ C.F.Anc X' Y := by
      cases ha with
      | refl => exact absurd rfl (fun h => hne h.symm)
      | tail hh hp => exact ⟨_, hp, hh⟩
    obtain ⟨Y, hY, hXY⟩ := this
    exact h.2 Y hY (C.F.U_mono_anc hXY h'.1)

/-- `W'` relaxations: each edge at most once. -/
theorem sum_Wr_le {t k c Lmax M0 : ℕ} {inE : V → Finset E} {wit : ι → V → E} {src : V}
    (h : C.Valid t k c Lmax M0 inE wit src) : ∑ X, (C.Wr X).card ≤ Fintype.card E := by
  classical
  rw [← Finset.card_biUnion]
  · exact Finset.card_le_univ _
  · intro X _ X' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    exact hne (own_unique (h.wr_own X e he) (h.wr_own X' e he'))

/-- Crossing edges: each edge at most once. -/
theorem sum_Cr_le {t k c Lmax M0 : ℕ} {inE : V → Finset E} {wit : ι → V → E} {src : V}
    (h : C.Valid t k c Lmax M0 inE wit src) : ∑ X, (C.Cr X).card ≤ Fintype.card E := by
  classical
  rw [← Finset.card_biUnion]
  · exact Finset.card_le_univ _
  · intro X _ X' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    obtain ⟨ha, hb, hc⟩ := h.cr_cross X e he
    obtain ⟨ha', hb', hc'⟩ := h.cr_cross X' e he'
    exact hne (C.F.cross_unique ha hb ha' hb' hc hc')

/-- Deletions: each edge at most once. -/
theorem sum_Del_le {t k c Lmax M0 : ℕ} {inE : V → Finset E} {wit : ι → V → E} {src : V}
    (h : C.Valid t k c Lmax M0 inE wit src) : ∑ X, (C.Del X).card ≤ Fintype.card E := by
  classical
  rw [← Finset.card_biUnion]
  · exact Finset.card_le_univ _
  · intro X _ X' _ hne
    exact h.del_disj X X' hne

/-- Summing a per-call quantity bounded levelwise by `A` over depths `0..Lmax`. -/
theorem sum_le_levels {t k c Lmax M0 : ℕ} {inE : V → Finset E} {wit : ι → V → E} {src : V}
    (h : C.Valid t k c Lmax M0 inE wit src) (g : ι → ℕ) (A : ℕ)
    (hlev : ∀ j, ∑ X ∈ univ.filter (fun X => C.F.depth X = j), g X ≤ A) :
    ∑ X, g X ≤ (Lmax + 1) * A := by
  classical
  have hmaps : ∀ X ∈ (univ : Finset ι), C.F.depth X ∈ Finset.range (Lmax + 1) := by
    intro X _; simp only [Finset.mem_range]; have := h.depth_le X; omega
  have hsplit : ∑ X, g X = ∑ j ∈ Finset.range (Lmax + 1), ∑ X ∈ univ.filter (fun X => C.F.depth X = j), g X :=
    (Finset.sum_fiberwise_of_maps_to hmaps g).symm
  rw [hsplit]
  calc ∑ j ∈ Finset.range (Lmax + 1), ∑ X ∈ univ.filter (fun X => C.F.depth X = j), g X
      ≤ ∑ _j ∈ Finset.range (Lmax + 1), A := Finset.sum_le_sum fun j _ => hlev j
    _ = (Lmax + 1) * A := by simp

/-- `Σ |U X| ≤ (Lmax+1) |V|`. -/
theorem sum_U_le {t k c Lmax M0 : ℕ} {inE : V → Finset E} {wit : ι → V → E} {src : V}
    (h : C.Valid t k c Lmax M0 inE wit src) : ∑ X, (C.F.U X).card ≤ (Lmax + 1) * Fintype.card V :=
  sum_le_levels h _ _ fun j => C.F.level_card_sum_le j

/-- Split a sum over calls into full and partial calls. -/
theorem sum_split (g : ι → ℕ) :
    ∑ X, g X = ∑ X ∈ univ.filter (fun X => C.full X = true), g X
      + ∑ X ∈ univ.filter (fun X => ¬ C.full X = true), g X :=
  (Finset.sum_filter_add_sum_filter_not univ (fun X => C.full X = true) g).symm

/-- Foreign mass: `Σ |Fo X| ≤ 2 (Lmax+1) |V|`. -/
theorem sum_Fo_le {t k c Lmax M0 : ℕ} {inE : V → Finset E} {wit : ι → V → E} {src : V}
    (h : C.Valid t k c Lmax M0 inE wit src) :
    ∑ X, (C.Fo X).card ≤ 2 * ((Lmax + 1) * Fintype.card V) := by
  classical
  rw [sum_split (C := C)]
  have hfull : ∑ X ∈ univ.filter (fun X => C.full X = true), (C.Fo X).card ≤ (Lmax + 1) * Fintype.card V := by
    have := sum_le_levels h (fun X => if C.full X = true then (C.Fo X).card else 0) (Fintype.card V)
      (fun j => by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.filter_filter]
        exact h.foreign_level j)
    rw [← Finset.sum_filter] at this
    exact this
  have hpart : ∑ X ∈ univ.filter (fun X => ¬ C.full X = true), (C.Fo X).card ≤ (Lmax + 1) * Fintype.card V := by
    calc ∑ X ∈ univ.filter (fun X => ¬ C.full X = true), (C.Fo X).card
        ≤ ∑ X ∈ univ.filter (fun X => ¬ C.full X = true), (C.F.U X).card := by
          refine Finset.sum_le_sum fun X hX => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at hX
          exact h.partial_Fo X hX
      _ ≤ ∑ X, (C.F.U X).card := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ ≤ (Lmax + 1) * Fintype.card V := sum_U_le h
  linarith

/-- `|S X| ≤ |U X|` for every call. -/
theorem S_le_U {t k c Lmax M0 : ℕ} {inE : V → Finset E} {wit : ι → V → E} {src : V}
    (h : C.Valid t k c Lmax M0 inE wit src) (X : ι) : (C.S X).card ≤ (C.F.U X).card := by
  cases hX : C.full X
  · have h1 := h.partial_S X hX
    have ht : 1 ≤ t := le_trans (by norm_num) (le_trans h.two_le_k h.k_le_t)
    calc (C.S X).card = 1 * (C.S X).card := by ring
      _ ≤ t * (C.S X).card := Nat.mul_le_mul_right _ ht
      _ ≤ (C.F.U X).card := h1
  · exact Finset.card_le_card (h.full_S X hX)

/-- `t · Σ |Q X| ≤ t (|E| + 1) + (Lmax+1) |V|` (the `+1`: the source, O22(C)). -/
theorem sum_tQ_le {t k c Lmax M0 : ℕ} {inE : V → Finset E} {wit : ι → V → E} {src : V}
    (h : C.Valid t k c Lmax M0 inE wit src) :
    ∑ X, t * (C.Q X).card ≤ t * (Fintype.card E + 1) + (Lmax + 1) * Fintype.card V := by
  classical
  rw [sum_split (C := C)]
  have hfull : ∑ X ∈ univ.filter (fun X => C.full X = true), (C.Q X).card ≤ Fintype.card E + 1 := by
    set F := univ.filter (fun X => C.full X = true) with hF
    have h1 : ∑ X ∈ F, ((C.Q X).erase src).card ≤ Fintype.card E := by
      refine le_trans ?_ h.inE_card
      refine sum_card_le_of_witness F (fun X => (C.Q X).erase src) inE wit ?_ ?_
      · intro X hX v hv
        simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hX
        rw [Finset.mem_erase] at hv
        exact h.wit_mem X hX v hv.2 hv.1
      · intro v X hX X' hX' hv hv' hw
        simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hX hX'
        exact h.wit_inj v X X' hX hX' (Finset.mem_of_mem_erase hv) (Finset.mem_of_mem_erase hv') hw
    have h2 : (F.filter (fun X => src ∈ C.Q X)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro X hX X' hX'
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hX hX'
      exact h.src_once X X' hX.1 hX'.1 hX.2 hX'.2
    have h3 : ∀ X, (C.Q X).card ≤ ((C.Q X).erase src).card + (if src ∈ C.Q X then 1 else 0) := by
      intro X
      by_cases hs : src ∈ C.Q X
      · rw [if_pos hs, Finset.card_erase_add_one hs]
      · rw [if_neg hs, Finset.erase_eq_of_notMem hs]; simp
    calc ∑ X ∈ F, (C.Q X).card
        ≤ ∑ X ∈ F, (((C.Q X).erase src).card + (if src ∈ C.Q X then 1 else 0)) :=
          Finset.sum_le_sum fun X _ => h3 X
      _ = ∑ X ∈ F, ((C.Q X).erase src).card + (F.filter (fun X => src ∈ C.Q X)).card := by
          rw [Finset.sum_add_distrib, Finset.sum_boole]; simp
      _ ≤ Fintype.card E + 1 := by omega
  have hpart : ∑ X ∈ univ.filter (fun X => ¬ C.full X = true), t * (C.Q X).card
      ≤ (Lmax + 1) * Fintype.card V := by
    calc ∑ X ∈ univ.filter (fun X => ¬ C.full X = true), t * (C.Q X).card
        ≤ ∑ X ∈ univ.filter (fun X => ¬ C.full X = true), (C.F.U X).card := by
          refine Finset.sum_le_sum fun X hX => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at hX
          calc t * (C.Q X).card ≤ t * (C.S X).card :=
                Nat.mul_le_mul_left _ (Finset.card_le_card (h.Q_sub X))
            _ ≤ (C.F.U X).card := h.partial_S X hX
      _ ≤ ∑ X, (C.F.U X).card := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ ≤ (Lmax + 1) * Fintype.card V := sum_U_le h
  rw [← Finset.mul_sum]
  have := Nat.mul_le_mul_left t hfull
  linarith

/-- `(k-1) · Σ t · p X ≤ 3 t (Lmax+1) |V| + (k-1)(Lmax+1)|V|`. -/
theorem sum_tp_le {t k c Lmax M0 : ℕ} {inE : V → Finset E} {wit : ι → V → E} {src : V}
    (h : C.Valid t k c Lmax M0 inE wit src) :
    (k - 1) * ∑ X, t * C.p X ≤ 3 * t * ((Lmax + 1) * Fintype.card V) + (k - 1) * ((Lmax + 1) * Fintype.card V) := by
  classical
  rw [sum_split (C := C), Nat.mul_add]
  have hU := sum_U_le h
  have hFo := sum_Fo_le h
  have hfull : (k - 1) * ∑ X ∈ univ.filter (fun X => C.full X = true), t * C.p X
      ≤ 3 * t * ((Lmax + 1) * Fintype.card V) := by
    rw [Finset.mul_sum]
    calc ∑ X ∈ univ.filter (fun X => C.full X = true), (k - 1) * (t * C.p X)
        ≤ ∑ X ∈ univ.filter (fun X => C.full X = true), t * ((C.F.U X).card + (C.Fo X).card) := by
          refine Finset.sum_le_sum fun X hX => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX
          have := h.full_p X hX
          calc (k - 1) * (t * C.p X) = t * (C.p X * (k - 1)) := by ring
            _ ≤ t * ((C.F.U X).card + (C.Fo X).card) := Nat.mul_le_mul_left _ this
      _ ≤ ∑ X, t * ((C.F.U X).card + (C.Fo X).card) := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = t * (∑ X, (C.F.U X).card + ∑ X, (C.Fo X).card) := by rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ t * ((Lmax + 1) * Fintype.card V + 2 * ((Lmax + 1) * Fintype.card V)) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add hU hFo)
      _ = 3 * t * ((Lmax + 1) * Fintype.card V) := by ring
  have hpart : (k - 1) * ∑ X ∈ univ.filter (fun X => ¬ C.full X = true), t * C.p X
      ≤ (k - 1) * ((Lmax + 1) * Fintype.card V) := by
    apply Nat.mul_le_mul_left
    calc ∑ X ∈ univ.filter (fun X => ¬ C.full X = true), t * C.p X
        ≤ ∑ X ∈ univ.filter (fun X => ¬ C.full X = true), (C.F.U X).card := by
          refine Finset.sum_le_sum fun X hX => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at hX
          calc t * C.p X ≤ t * (C.S X).card := Nat.mul_le_mul_left _ (h.partial_p X hX)
            _ ≤ (C.F.U X).card := h.partial_S X hX
      _ ≤ ∑ X, (C.F.U X).card := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ ≤ (Lmax + 1) * Fintype.card V := hU
  exact Nat.add_le_add hfull hpart

/-- Partial-call re-insertions: `Σ [partial] t |S X| ≤ (Lmax+1)|V|`. -/
theorem sum_partial_tS_le {t k c Lmax M0 : ℕ} {inE : V → Finset E} {wit : ι → V → E} {src : V}
    (h : C.Valid t k c Lmax M0 inE wit src) :
    ∑ X, (if C.full X then 0 else t * (C.S X).card) ≤ (Lmax + 1) * Fintype.card V := by
  calc ∑ X, (if C.full X then 0 else t * (C.S X).card) ≤ ∑ X, (C.F.U X).card := by
        refine Finset.sum_le_sum fun X _ => ?_
        cases hX : C.full X
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact h.partial_S X hX
        · simp
    _ ≤ (Lmax + 1) * Fintype.card V := sum_U_le h

/-- **Aggregation (C-HD Lemma 3.9, summed).**  With `N = (Lmax+1)|V|`:
`(k-1) · Σ cost ≤ c · [ (k-1) · ((3k+8) N + 6 t (|E| + 1) + M0) + 3 t N ]`. -/
theorem total_cost_le {t k c Lmax M0 : ℕ} {inE : V → Finset E} {wit : ι → V → E} {src : V}
    (h : C.Valid t k c Lmax M0 inE wit src) :
    (k - 1) * ∑ X ∈ univ.filter (fun X => C.base X = false), C.cost X ≤
      c * ((k - 1) * ((3 * k + 8) * ((Lmax + 1) * Fintype.card V) + 6 * t * (Fintype.card E + 1) + M0)
        + 3 * t * ((Lmax + 1) * Fintype.card V)) := by
  classical
  set N := (Lmax + 1) * Fintype.card V with hN
  have hU := sum_U_le h
  have hFo := sum_Fo_le h
  have hS : ∑ X, (C.S X).card ≤ N := le_trans (Finset.sum_le_sum fun X _ => S_le_U h X) hU
  have hQ := sum_tQ_le h
  have hJ := sum_J_le h
  have hW := sum_Wr_le h
  have hCr := sum_Cr_le h
  have hp := sum_tp_le h
  have hpS := sum_partial_tS_le h
  have hM := h.merge_total
  have hBe := h.be_total
  -- the bracket without the pivot term
  set R : ι → ℕ := fun X => (k + 1) * ((C.F.U X).card + (C.Fo X).card) + (C.S X).card
      + t * (C.Q X).card + t * ((C.J X).card + (C.Wr X).card + (C.Cr X).card + (C.Be X).card)
      + (if C.full X then 0 else t * (C.S X).card) + C.mergeCost X + (C.Del X).card with hR
  have hDel := sum_Del_le h
  have hRsum : ∑ X, R X ≤ (3 * k + 7) * N + 5 * t * (Fintype.card E + 1) + M0 + Fintype.card E := by
    have e : ∑ X, R X = (k + 1) * (∑ X, (C.F.U X).card + ∑ X, (C.Fo X).card) + ∑ X, (C.S X).card
        + ∑ X, t * (C.Q X).card + t * (∑ X, (C.J X).card + ∑ X, (C.Wr X).card + ∑ X, (C.Cr X).card
          + ∑ X, (C.Be X).card)
        + ∑ X, (if C.full X then 0 else t * (C.S X).card) + ∑ X, C.mergeCost X + ∑ X, (C.Del X).card := by
      simp only [hR, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [e]
    have h1 : (k + 1) * (∑ X, (C.F.U X).card + ∑ X, (C.Fo X).card) ≤ (k + 1) * (3 * N) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : t * (∑ X, (C.J X).card + ∑ X, (C.Wr X).card + ∑ X, (C.Cr X).card + ∑ X, (C.Be X).card)
        ≤ t * (4 * Fintype.card E) :=
      Nat.mul_le_mul_left _ (by omega)
    nlinarith
  have hcost : ∀ X, C.base X = false → C.cost X ≤ c * (R X + t * C.p X) := by
    intro X hb
    have := h.cost_le X hb
    simp only [hR]
    calc C.cost X ≤ c * ((k + 1) * ((C.F.U X).card + (C.Fo X).card) + (C.S X).card
          + t * (C.Q X).card + t * ((C.J X).card + (C.Wr X).card + (C.Cr X).card + (C.Be X).card) + t * C.p X
          + (if C.full X then 0 else t * (C.S X).card) + C.mergeCost X + (C.Del X).card) := this
      _ = c * ((k + 1) * ((C.F.U X).card + (C.Fo X).card) + (C.S X).card
          + t * (C.Q X).card + t * ((C.J X).card + (C.Wr X).card + (C.Cr X).card + (C.Be X).card)
          + (if C.full X then 0 else t * (C.S X).card) + C.mergeCost X + (C.Del X).card + t * C.p X) := by ring
  have hsum : ∑ X ∈ univ.filter (fun X => C.base X = false), C.cost X ≤ c * (∑ X, R X + ∑ X, t * C.p X) := by
    calc ∑ X ∈ univ.filter (fun X => C.base X = false), C.cost X
        ≤ ∑ X ∈ univ.filter (fun X => C.base X = false), c * (R X + t * C.p X) := by
          refine Finset.sum_le_sum fun X hX => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX
          exact hcost X hX
      _ ≤ ∑ X, c * (R X + t * C.p X) := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = c * (∑ X, R X + ∑ X, t * C.p X) := by rw [← Finset.mul_sum, Finset.sum_add_distrib]
  calc (k - 1) * ∑ X ∈ univ.filter (fun X => C.base X = false), C.cost X
      ≤ (k - 1) * (c * (∑ X, R X + ∑ X, t * C.p X)) :=
        Nat.mul_le_mul_left _ hsum
    _ = c * ((k - 1) * ∑ X, R X + (k - 1) * ∑ X, t * C.p X) := by ring
    _ ≤ c * ((k - 1) * ((3 * k + 7) * N + 5 * t * (Fintype.card E + 1) + M0 + Fintype.card E)
          + (3 * t * N + (k - 1) * N)) := by
        apply Nat.mul_le_mul_left
        exact Nat.add_le_add (Nat.mul_le_mul_left _ hRsum) hp
    _ ≤ c * ((k - 1) * ((3 * k + 8) * N + 6 * t * (Fintype.card E + 1) + M0) + 3 * t * N) := by
        have ht1 : 1 ≤ t := le_trans (by norm_num) (le_trans h.two_le_k h.k_le_t)
        have hE1 : Fintype.card E + 1 ≤ t * (Fintype.card E + 1) := Nat.le_mul_of_pos_left _ ht1
        apply Nat.mul_le_mul_left
        have : (k - 1) * ((3 * k + 7) * N + 5 * t * (Fintype.card E + 1) + M0 + Fintype.card E)
            + (3 * t * N + (k - 1) * N)
            ≤ (k - 1) * ((3 * k + 8) * N + 6 * t * (Fintype.card E + 1) + M0) + 3 * t * N := by
          have h1 : (3 * k + 7) * N + 5 * t * (Fintype.card E + 1) + M0 + Fintype.card E + N
              ≤ (3 * k + 8) * N + 6 * t * (Fintype.card E + 1) + M0 := by nlinarith
          have h2 := Nat.mul_le_mul_left (k - 1) h1
          nlinarith
        exact this

/-- Out-edges of `U X`. -/
def Eout (X : ι) : Finset E := univ.filter (fun e => C.src e ∈ C.F.U X)

omit [DecidableEq ι] [DecidableEq V] in
/-- Two distinct base calls have disjoint `U` (base calls are leaves, and calls sharing a vertex are comparable). -/
theorem base_disjoint {t k c Lmax M0 : ℕ} {inE : V → Finset E} {wit : ι → V → E} {src : V}
    (h : C.Valid t k c Lmax M0 inE wit src) {X X' : ι} (hb : C.base X = true) (hb' : C.base X' = true)
    (hne : X ≠ X') : Disjoint (C.F.U X) (C.F.U X') := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  rcases C.F.chain_of_mem hv hv' with ha | ha
  · -- `X'` is an ancestor of `X`; a proper ancestor has a child, contradicting `base_leaf`
    cases ha with
    | refl => exact hne rfl
    | tail _ hp => exact h.base_leaf X' _ hb' hp
  · cases ha with
    | refl => exact hne rfl
    | tail _ hp => exact h.base_leaf X _ hb hp

/-- **Base cases.**  If every base call costs at most `c (lg + 1)(|U| + |Eout|)`, all base calls together cost
at most `c (lg + 1)(|V| + |E|)` (each vertex and each edge is in at most one base call). -/
theorem base_total_le {t k c Lmax M0 lg : ℕ} {inE : V → Finset E} {wit : ι → V → E} {src : V}
    (h : C.Valid t k c Lmax M0 inE wit src)
    (hbase : ∀ X, C.base X = true → C.cost X ≤ c * (lg + 1) * ((C.F.U X).card + (C.Eout X).card)) :
    ∑ X ∈ univ.filter (fun X => C.base X = true), C.cost X
      ≤ c * (lg + 1) * (Fintype.card V + Fintype.card E) := by
  classical
  set B := univ.filter (fun X => C.base X = true) with hB
  have hdisjU : (B : Set ι).PairwiseDisjoint (fun X => C.F.U X) := by
    intro X hX X' hX' hne
    simp only [hB, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hX hX'
    exact base_disjoint h hX hX' hne
  have hdisjE : (B : Set ι).PairwiseDisjoint (fun X => C.Eout X) := by
    intro X hX X' hX' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    simp only [Eout, Finset.mem_filter, Finset.mem_univ, true_and] at he he'
    exact Finset.disjoint_left.mp (hdisjU hX hX' hne) he he'
  have hU : ∑ X ∈ B, (C.F.U X).card ≤ Fintype.card V := by
    rw [← Finset.card_biUnion hdisjU]; exact Finset.card_le_univ _
  have hE : ∑ X ∈ B, (C.Eout X).card ≤ Fintype.card E := by
    rw [← Finset.card_biUnion hdisjE]; exact Finset.card_le_univ _
  calc ∑ X ∈ B, C.cost X ≤ ∑ X ∈ B, c * (lg + 1) * ((C.F.U X).card + (C.Eout X).card) := by
        refine Finset.sum_le_sum fun X hX => ?_
        simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hX
        exact hbase X hX
    _ = c * (lg + 1) * (∑ X ∈ B, (C.F.U X).card + ∑ X ∈ B, (C.Eout X).card) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ c * (lg + 1) * (Fintype.card V + Fintype.card E) := Nat.mul_le_mul_left _ (Nat.add_le_add hU hE)

end CallCounters

end Frontier.CostAggregate
