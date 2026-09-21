import Frontier.CostCharging

/-!
# Frontier.Density — handled ranges, foreign leaves, split-uniqueness (owner: agent-03)

**NON-GATE.**  Abstract combinatorics used by the C-HD time analysis (PAPER_CHD §5.1–§5.3, agent-03).
They are stated over agent-06's abstract `CostCharging.CallForest`. The algorithm-specific hypotheses are exactly the
structural facts that the correctness development proves (S2 (J5)/(R8)/(S-a), PAPER_CHD §5.1). These are:
* handled ranges `[lo X, hi X)` are nested along parent edges;
* the handled ranges of siblings (and of roots) are pairwise disjoint.

Results:
* `inR_anc`: a value in the range of `X` is in the range of every ancestor of `X`.
* `inR_same_depth`: two distinct calls of one depth never share a value of their ranges.
* `level_foreign_sum_le`: foreign sets whose members carry fixed values inside their call's range have total size
  at most `|V|` per depth. This is the per-layer foreign-leaf bound of PAPER_CHD §5.2.
* `split_unique`: for a vertex `u` and a value `c`, at most one call contains `u`, has `c` in range, and has no child
  that contains `u` and has `c` in range. This is the once-per-edge charge of the home-charging lemma (PAPER_CHD §5.3 (ii)).
-/

namespace Frontier.Density

open Finset Frontier.CostCharging

variable {ι V α : Type*} [LinearOrder α]

/-- Handled ranges on a call forest. -/
structure Ranges (F : CallForest ι V α) where
  lo : ι → α
  hi : ι → α
  lo_le : ∀ X Y, F.parent X = some Y → lo Y ≤ lo X
  hi_le : ∀ X Y, F.parent X = some Y → hi X ≤ hi Y
  sib : ∀ X X' Y, F.parent X = some Y → F.parent X' = some Y → X ≠ X' → ∀ c : α,
    lo X ≤ c → c < hi X → lo X' ≤ c → c < hi X' → False
  roots : ∀ X X', F.parent X = none → F.parent X' = none → X ≠ X' → ∀ c : α,
    lo X ≤ c → c < hi X → lo X' ≤ c → c < hi X' → False

namespace Ranges

variable {F : CallForest ι V α} (R : Ranges F)

/-- `c` lies in the handled range of `X`. -/
def inR (X : ι) (c : α) : Prop := R.lo X ≤ c ∧ c < R.hi X

/-- Ranges are nested along ancestors. -/
theorem inR_anc {X Y : ι} (h : F.Anc X Y) {c : α} (hc : R.inR X c) : R.inR Y c := by
  induction h with
  | refl => exact hc
  | tail _ hp ih => exact ⟨le_trans (R.lo_le _ _ hp) ih.1, lt_of_lt_of_le ih.2 (R.hi_le _ _ hp)⟩

/-- **Same-depth disjointness of handled ranges.** -/
theorem inR_same_depth : ∀ (j : ℕ) (X X' : ι), F.depth X = j → F.depth X' = j → X ≠ X' →
    ∀ c : α, R.inR X c → R.inR X' c → False
  | 0, X, X', hX, hX', hne, c, h1, h2 =>
    R.roots X X' ((F.depth_zero_iff X).mp hX) ((F.depth_zero_iff X').mp hX') hne c h1.1 h1.2 h2.1 h2.2
  | j + 1, X, X', hX, hX', hne, c, h1, h2 => by
    cases hp : F.parent X with
    | none => have := F.depth_root X hp; omega
    | some Y =>
      cases hp' : F.parent X' with
      | none => have := F.depth_root X' hp'; omega
      | some Y' =>
        by_cases hYY : Y = Y'
        · subst hYY
          exact R.sib X X' Y hp hp' hne c h1.1 h1.2 h2.1 h2.2
        · have hdY := F.depth_parent X Y hp
          have hdY' := F.depth_parent X' Y' hp'
          have hA : F.Anc X Y := Relation.ReflTransGen.single hp
          have hA' : F.Anc X' Y' := Relation.ReflTransGen.single hp'
          exact inR_same_depth j Y Y' (by omega) (by omega) hYY c (R.inR_anc hA h1) (R.inR_anc hA' h2)

/-- **Per-depth foreign bound.** Let `full` be a predicate on calls, `O X` a set of vertices for each call, and
`val` a FIXED value per vertex, such that every member of `O X` of a `full` call has its value in the range of `X`.
Then, on every depth, the `O`'s of full calls are pairwise disjoint, so their sizes sum to at most `|V|`. -/
theorem level_foreign_sum_le [Fintype ι] [Fintype V] [DecidableEq V] (full : ι → Prop) [DecidablePred full]
    (O : ι → Finset V) (val : V → α) (hO : ∀ X, full X → ∀ v ∈ O X, R.inR X (val v)) (j : ℕ) :
    ∑ X ∈ univ.filter (fun X => F.depth X = j ∧ full X), (O X).card ≤ Fintype.card V := by
  classical
  rw [← Finset.card_biUnion]
  · exact Finset.card_le_univ _
  · intro X hX X' hX' hne
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hX hX'
    show Disjoint (O X) (O X')
    rw [Finset.disjoint_left]
    intro v hv hv'
    exact R.inR_same_depth j X X' hX.1 hX'.1 hne (val v) (hO X hX.2 v hv) (hO X' hX'.2 v hv')

/-- The last step of a proper ancestor chain: if `X` is a proper ancestor of `Z`, some child `Y` of `X` is an
ancestor of `Z`. -/
theorem exists_child_anc {X Z : ι} (h : F.Anc Z X) (hne : Z ≠ X) :
    ∃ Y, F.parent Y = some X ∧ F.Anc Z Y := by
  cases h with
  | refl => exact absurd rfl hne
  | tail h' hp => exact ⟨_, hp, h'⟩

/-- `u` SPLITS the value `c` at `X`: `u ∈ U X`, `c` is in range of `X`, and no child of `X` contains `u` with `c`
in range. -/
def Split (u : V) (c : α) (X : ι) : Prop :=
  u ∈ F.U X ∧ R.inR X c ∧ ∀ Y, F.parent Y = some X → u ∈ F.U Y → ¬ R.inR Y c

/-- **Split uniqueness (home charging, once per edge).** For a vertex `u` and a value `c`, at most one call
splits `c` for `u`. -/
theorem split_unique {u : V} {c : α} {X₁ X₂ : ι} (h₁ : R.Split u c X₁) (h₂ : R.Split u c X₂) : X₁ = X₂ := by
  by_contra hne
  have key : ∀ {X Z : ι}, F.Anc Z X → Z ≠ X → R.Split u c X → R.Split u c Z → False := by
    intro X Z hZX hZne hX hZ
    obtain ⟨Y, hY, hZY⟩ := exists_child_anc (F := F) hZX hZne
    exact hX.2.2 Y hY (F.U_mono_anc hZY hZ.1) (R.inR_anc hZY hZ.2.1)
  rcases F.chain_of_mem h₁.1 h₂.1 with h | h
  · exact key h hne h₂ h₁
  · exact key h (fun h' => hne h'.symm) h₁ h₂


/-- **Pivot mass per depth (PAPER_CHD §5.2).** For full calls, `U X` and the foreign sets `O X` are each
disjoint across a depth, so `Σ (|U X| + |O X|) ≤ 2|V|` on every depth. -/
theorem level_pivot_mass_le [Fintype ι] [Fintype V] [DecidableEq V] (full : ι → Prop) [DecidablePred full]
    (O : ι → Finset V) (val : V → α) (hO : ∀ X, full X → ∀ v ∈ O X, R.inR X (val v)) (j : ℕ) :
    ∑ X ∈ univ.filter (fun X => F.depth X = j ∧ full X), ((F.U X).card + (O X).card) ≤
      2 * Fintype.card V := by
  classical
  rw [Finset.sum_add_distrib, two_mul]
  refine Nat.add_le_add ?_ (R.level_foreign_sum_le full O val hO j)
  calc ∑ X ∈ univ.filter (fun X => F.depth X = j ∧ full X), (F.U X).card
      ≤ ∑ X ∈ univ.filter (fun X => F.depth X = j), (F.U X).card := by
        refine Finset.sum_le_sum_of_subset ?_
        intro X hX
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX ⊢
        exact hX.1
    _ ≤ Fintype.card V := F.level_card_sum_le j

end Ranges

/-- **Once-per-element double counting.** If every element belongs to the sets `A X` of at most one index,
the sizes of the `A X` sum to at most the number of elements. -/
theorem sum_card_le_of_unique {ι E : Type*} [Fintype ι] [Fintype E] [DecidableEq E] (A : ι → Finset E)
    (h : ∀ e X X', e ∈ A X → e ∈ A X' → X = X') :
    ∑ X, (A X).card ≤ Fintype.card E := by
  classical
  rw [← Finset.card_biUnion]
  · exact Finset.card_le_univ _
  · intro X _ X' _ hne
    show Disjoint (A X) (A X')
    rw [Finset.disjoint_left]
    intro e h1 h2
    exact hne (h e X X' h1 h2)

namespace Ranges

variable {F : CallForest ι V α} (R : Ranges F)

/-- **Foreign-leaf re-selection charge (PAPER_CHD §5.3 (ii), kind (β)).** Let `Bet X` be any set of edges `e` such
that the tail of `e` splits the (fixed) value of the head of `e` at `X`. Then every edge lies in at most one `Bet X`,
so `Σ_X |Bet X| ≤ |E|`. -/
theorem beta_sum_le {E : Type*} [Fintype ι] [Fintype E] [DecidableEq E] (tail head : E → V) (val : V → α)
    (Bet : ι → Finset E) (hB : ∀ X, ∀ e ∈ Bet X, R.Split (tail e) (val (head e)) X) :
    ∑ X, (Bet X).card ≤ Fintype.card E :=
  sum_card_le_of_unique Bet fun e X X' h1 h2 => R.split_unique (hB X e h1) (hB X' e h2)

end Ranges

end Frontier.Density
