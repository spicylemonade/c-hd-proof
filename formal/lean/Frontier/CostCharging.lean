import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Basic
import Mathlib.Logic.Relation

/-!
# Frontier.CostCharging — C-HD cost composition skeleton, part 2: abstract charging lemmas (owner: agent-06)

**NON-GATE.**  Pure combinatorics over an ABSTRACT recursion forest of BMSSP calls.  These are the counting
facts that DMSY26 §3.4/§3.6 (and the C-HD card) use in the running-time analysis; the algorithm-specific
hypotheses (sibling disjointness, nested bounds, the witness map for `Q`) are exactly the structural facts that
the correctness development (L4) proves, so the assembled cost proof instantiates `CallForest` with the real
call tree.

* `CallForest`: calls `ι` with `parent`, `depth`, vertex sets `U`, bounds `B`, satisfying
  `U child ⊆ U parent`, `B child ≤ B parent`, siblings (and roots) have disjoint `U`.
* `same_depth_disjoint`, `level_card_sum_le`: the `U`'s of one level are pairwise disjoint, so their sizes sum
  to at most the number of vertices (DMSY26 §3.4 item 5).
* `chain_of_mem`: the calls containing a vertex form a chain (item 6).
* `window_unique`: a value lies in at most one window `[B child, B X)` along a vertex's chain (Obs. 3.5:
  every edge enters Line 24 at most once).
* `sum_card_le_of_witness`: double counting for the `Q`-charge (Lemma 3.9: `Σ |Q_Y| ≤ δ |U|` over full calls).
* `bichromatic_ge`: a rooted tree whose vertices meet `g` colour classes has at least `g - 1` edges joining
  different classes (the re-selection charge T5 to cross-level tree edges).
-/

namespace Frontier.CostCharging

open Finset

/-! ## Abstract call forests -/

/-- An abstract forest of recursive calls.  `parent X = some Y`: `X` is a direct sub-call of `Y`. -/
structure CallForest (ι V α : Type*) [LinearOrder α] where
  parent : ι → Option ι
  depth : ι → ℕ
  U : ι → Finset V
  B : ι → α
  depth_parent : ∀ X Y, parent X = some Y → depth X = depth Y + 1
  depth_root : ∀ X, parent X = none → depth X = 0
  U_sub : ∀ X Y, parent X = some Y → U X ⊆ U Y
  B_le : ∀ X Y, parent X = some Y → B X ≤ B Y
  siblings_disjoint : ∀ X X' Y, parent X = some Y → parent X' = some Y → X ≠ X' → Disjoint (U X) (U X')
  roots_disjoint : ∀ X X', parent X = none → parent X' = none → X ≠ X' → Disjoint (U X) (U X')

namespace CallForest

variable {ι V α : Type*} [LinearOrder α] (F : CallForest ι V α)

/-- `F.Anc X Y`: `Y` is an ancestor of `X` (reflexive). -/
def Anc (X Y : ι) : Prop := Relation.ReflTransGen (fun a b => F.parent a = some b) X Y

theorem depth_zero_iff (X : ι) : F.depth X = 0 ↔ F.parent X = none := by
  constructor
  · intro h
    cases hp : F.parent X with
    | none => rfl
    | some Y => have := F.depth_parent X Y hp; omega
  · exact F.depth_root X

/-- **Same-level disjointness.** -/
theorem same_depth_disjoint : ∀ (j : ℕ) (X X' : ι), F.depth X = j → F.depth X' = j → X ≠ X' →
    Disjoint (F.U X) (F.U X')
  | 0, X, X', hX, hX', hne =>
    F.roots_disjoint X X' ((F.depth_zero_iff X).mp hX) ((F.depth_zero_iff X').mp hX') hne
  | j + 1, X, X', hX, hX', hne => by
    cases hp : F.parent X with
    | none => have := F.depth_root X hp; omega
    | some Y =>
      cases hp' : F.parent X' with
      | none => have := F.depth_root X' hp'; omega
      | some Y' =>
        by_cases hYY : Y = Y'
        · subst hYY; exact F.siblings_disjoint X X' Y hp hp' hne
        · have hdY := F.depth_parent X Y hp
          have hdY' := F.depth_parent X' Y' hp'
          have hdis := same_depth_disjoint j Y Y' (by omega) (by omega) hYY
          exact Disjoint.mono (F.U_sub X Y hp) (F.U_sub X' Y' hp') hdis

/-- **Level sums.**  On one level the `U`'s are disjoint, so `Σ |U X| ≤ |V|`. -/
theorem level_card_sum_le [Fintype ι] [Fintype V] [DecidableEq V] (j : ℕ) :
    ∑ X ∈ univ.filter (fun X => F.depth X = j), (F.U X).card ≤ Fintype.card V := by
  classical
  rw [← Finset.card_biUnion]
  · exact Finset.card_le_univ _
  · intro X hX X' hX' hne
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hX hX'
    exact F.same_depth_disjoint j X X' hX hX' hne

/-- Ancestors have larger (or equal) `U`. -/
theorem U_mono_anc {X Y : ι} (h : F.Anc X Y) : F.U X ⊆ F.U Y := by
  induction h with
  | refl => exact le_rfl
  | tail _ hpy ih => exact ih.trans (F.U_sub _ _ hpy)

/-- Ancestors have larger (or equal) bound. -/
theorem B_mono_anc {X Y : ι} (h : F.Anc X Y) : F.B X ≤ F.B Y := by
  induction h with
  | refl => exact le_rfl
  | tail _ hpy ih => exact ih.trans (F.B_le _ _ hpy)

/-- Ancestors have smaller (or equal) depth, with equality only for the call itself. -/
theorem depth_anc {X Y : ι} (h : F.Anc X Y) : F.depth Y ≤ F.depth X ∧ (F.depth Y = F.depth X → X = Y) := by
  induction h with
  | refl => exact ⟨le_rfl, fun _ => rfl⟩
  | tail hxb hpy ih =>
    rename_i b c
    have hd := F.depth_parent b c hpy
    refine ⟨by omega, fun heq => ?_⟩
    exfalso; omega

/-- The ancestor of `X` at any smaller depth exists. -/
theorem exists_anc_at_depth : ∀ (k : ℕ) (X : ι), k ≤ F.depth X → ∃ Y, F.Anc X Y ∧ F.depth Y = k := by
  intro k X hk
  induction h : F.depth X - k generalizing X with
  | zero => exact ⟨X, Relation.ReflTransGen.refl, by omega⟩
  | succ j ih =>
    cases hp : F.parent X with
    | none => have := F.depth_root X hp; omega
    | some Y =>
      have hdY := F.depth_parent X Y hp
      obtain ⟨Z, hYZ, hZ⟩ := ih Y (by omega) (by omega)
      exact ⟨Z, Relation.ReflTransGen.head hp hYZ, hZ⟩

/-- **Chains.**  Two calls containing the same vertex are comparable in the ancestor order. -/
theorem chain_of_mem {X X' : ι} {v : V} (hX : v ∈ F.U X) (hX' : v ∈ F.U X') :
    F.Anc X X' ∨ F.Anc X' X := by
  rcases le_total (F.depth X) (F.depth X') with hle | hle
  · obtain ⟨A, hA, hAd⟩ := F.exists_anc_at_depth (F.depth X) X' hle
    have hvA : v ∈ F.U A := F.U_mono_anc hA hX'
    by_cases hAX : A = X
    · subst hAX; exact Or.inr hA
    · exact absurd (F.same_depth_disjoint _ A X hAd rfl hAX) (Finset.not_disjoint_iff.mpr ⟨v, hvA, hX⟩)
  · obtain ⟨A, hA, hAd⟩ := F.exists_anc_at_depth (F.depth X') X hle
    have hvA : v ∈ F.U A := F.U_mono_anc hA hX
    by_cases hAX : A = X'
    · subst hAX; exact Or.inl hA
    · exact absurd (F.same_depth_disjoint _ A X' hAd rfl hAX) (Finset.not_disjoint_iff.mpr ⟨v, hvA, hX'⟩)

/-- If `Z` is a proper descendant of `X` and `Y` is the child of `X` containing `v ∈ U Z`, then `Z` is a
descendant (or equal) of `Y`. -/
theorem anc_child_of_mem {X Y Z : ι} {v : V} (hY : F.parent Y = some X) (hvY : v ∈ F.U Y)
    (hZX : F.Anc Z X) (hZne : Z ≠ X) (hvZ : v ∈ F.U Z) : F.Anc Z Y := by
  rcases F.chain_of_mem hvZ hvY with h | h
  · exact h
  · -- `Y` is a descendant of `Z`, and `Z` a proper descendant of `X`: impossible unless `Z = Y`
    have h1 := F.depth_anc h
    have h2 := F.depth_anc hZX
    have hdY := F.depth_parent Y X hY
    have hdZ : F.depth Z ≠ F.depth X := fun heq => hZne (h2.2 heq.symm)
    have : F.depth Y = F.depth Z := by omega
    rw [h1.2 this.symm]; exact Relation.ReflTransGen.refl

/-- **Once per edge (DMSY26 Obs. 3.5).**  Let `X₁ ≠ X₂` be calls with children `Y₁, Y₂` that all contain
the vertex `u`.  Then the windows `[B Y₁, B X₁)` and `[B Y₂, B X₂)` are disjoint, so a relaxation value
`x = dis(u) + w_uv` enters the "jump" test of at most one call. -/
theorem window_unique {X₁ X₂ Y₁ Y₂ : ι} {u : V} (hY₁ : F.parent Y₁ = some X₁) (hY₂ : F.parent Y₂ = some X₂)
    (hu₁ : u ∈ F.U Y₁) (hu₂ : u ∈ F.U Y₂) (hne : X₁ ≠ X₂) {x : α}
    (hw₁ : F.B Y₁ ≤ x ∧ x < F.B X₁) (hw₂ : F.B Y₂ ≤ x ∧ x < F.B X₂) : False := by
  have huX₁ : u ∈ F.U X₁ := F.U_sub Y₁ X₁ hY₁ hu₁
  have huX₂ : u ∈ F.U X₂ := F.U_sub Y₂ X₂ hY₂ hu₂
  rcases F.chain_of_mem huX₁ huX₂ with h | h
  · -- `X₂` is an ancestor of `X₁`: then `X₁` is below `Y₂`, so `B X₁ ≤ B Y₂ ≤ x`
    have hne' : X₁ ≠ X₂ := hne
    have hY := F.anc_child_of_mem hY₂ hu₂ h hne' huX₁
    have := F.B_mono_anc hY
    exact absurd (lt_of_lt_of_le hw₁.2 this) (not_lt.mpr hw₂.1)
  · have hne' : X₂ ≠ X₁ := fun h' => hne h'.symm
    have hY := F.anc_child_of_mem hY₁ hu₁ h hne' huX₂
    have := F.B_mono_anc hY
    exact absurd (lt_of_lt_of_le hw₂.2 this) (not_lt.mpr hw₁.1)

/-- **Cross edges are charged once.**  Call a pair `{a, b}` *crossing at `X`* if `a, b ∈ U X` and no child of
`X` contains both.  A pair is crossing at no more than one call. -/
theorem cross_unique {X₁ X₂ : ι} {a b : V} (ha₁ : a ∈ F.U X₁) (hb₁ : b ∈ F.U X₁) (ha₂ : a ∈ F.U X₂)
    (hb₂ : b ∈ F.U X₂)
    (hc₁ : ∀ Y, F.parent Y = some X₁ → ¬ (a ∈ F.U Y ∧ b ∈ F.U Y))
    (hc₂ : ∀ Y, F.parent Y = some X₂ → ¬ (a ∈ F.U Y ∧ b ∈ F.U Y)) : X₁ = X₂ := by
  by_contra hne
  -- the deeper of the two is a proper descendant of the other; its parent chain passes through a child of
  -- the other that contains both `a` and `b`
  have key : ∀ {X Z : ι}, F.Anc Z X → Z ≠ X → a ∈ F.U Z → b ∈ F.U Z →
      (∀ Y, F.parent Y = some X → ¬ (a ∈ F.U Y ∧ b ∈ F.U Y)) → False := by
    intro X Z hZX hZne haZ hbZ hcX
    -- the child of `X` on the path from `Z` is the last step of the ancestor chain
    have : ∃ Y, F.parent Y = some X ∧ F.Anc Z Y := by
      cases hZX with
      | refl => exact absurd rfl hZne
      | tail h hp => exact ⟨_, hp, h⟩
    obtain ⟨Y, hY, hZY⟩ := this
    exact hcX Y hY ⟨F.U_mono_anc hZY haZ, F.U_mono_anc hZY hbZ⟩
  rcases F.chain_of_mem ha₁ ha₂ with h | h
  · exact key h hne ha₁ hb₁ hc₂
  · exact key h (fun h' => hne h'.symm) ha₂ hb₂ hc₁

/-- Level-wise charge for PARTIAL calls: if `t · |Q X| ≤ |U X|` on a set of calls of depth `j`, their `Q`'s have
total size at most `|V| / t` (stated multiplicatively). -/
theorem level_partial_charge [Fintype ι] [Fintype V] [DecidableEq V] (j t : ℕ) (Q : ι → Finset V)
    (hQ : ∀ X, F.depth X = j → t * (Q X).card ≤ (F.U X).card) :
    t * ∑ X ∈ univ.filter (fun X => F.depth X = j), (Q X).card ≤ Fintype.card V := by
  rw [Finset.mul_sum]
  calc ∑ X ∈ univ.filter (fun X => F.depth X = j), t * (Q X).card
      ≤ ∑ X ∈ univ.filter (fun X => F.depth X = j), (F.U X).card := by
        refine Finset.sum_le_sum fun X hX => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX
        exact hQ X hX
    _ ≤ Fintype.card V := F.level_card_sum_le j

end CallForest

/-! ## Double counting for the `Q`-charge -/

/-- If every vertex `v` injects its `Q`-appearances (over a set of calls) into its in-edges, then the total
`Q` size is at most the number of edges. -/
theorem sum_card_le_of_witness {ι V E : Type*} [Fintype ι] [Fintype V] [DecidableEq V] [DecidableEq ι]
    [DecidableEq E] (calls : Finset ι) (Q : ι → Finset V) (inE : V → Finset E) (wit : ι → V → E)
    (hwit : ∀ X ∈ calls, ∀ v ∈ Q X, wit X v ∈ inE v)
    (hinj : ∀ v, ∀ X ∈ calls, ∀ X' ∈ calls, v ∈ Q X → v ∈ Q X' → wit X v = wit X' v → X = X') :
    ∑ X ∈ calls, (Q X).card ≤ ∑ v, (inE v).card := by
  classical
  have hswap : ∑ X ∈ calls, (Q X).card = ∑ v, (calls.filter (fun X => v ∈ Q X)).card := by
    rw [show (∑ X ∈ calls, (Q X).card) = ∑ X ∈ calls, ∑ v, (if v ∈ Q X then 1 else 0) by
      refine Finset.sum_congr rfl fun X _ => ?_
      rw [Finset.sum_boole]; simp]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_boole]; simp
  rw [hswap]
  refine Finset.sum_le_sum fun v _ => ?_
  refine Finset.card_le_card_of_injOn (fun X => wit X v) ?_ ?_
  · intro X hX
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hX
    exact hwit X hX.1 v hX.2
  · intro X hX X' hX' h
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hX hX'
    exact hinj v X hX.1 X' hX'.1 hX.2 hX'.2 h

/-! ## Bichromatic edges of a rooted tree (re-selection charge) -/

/-- A rooted tree on the finite vertex set `W`: `par v = some p` is the parent edge of `v`; `root` is the unique
vertex without parent; `dep` strictly increases along parent edges (acyclicity). -/
structure RootedTree (W : Type*) where
  par : W → Option W
  root : W
  dep : W → ℕ
  root_par : par root = none
  par_some : ∀ v, v ≠ root → (par v).isSome
  dep_par : ∀ v p, par v = some p → dep p < dep v

/-- **Bichromatic edges.**  If the vertices of a rooted tree meet `g` distinct colours, then at least `g - 1`
parent edges join vertices of different colours. -/
theorem bichromatic_ge {W κ : Type*} [Fintype W] [DecidableEq W] [DecidableEq κ] (T : RootedTree W)
    (col : W → κ) :
    (univ.image col).card - 1 ≤
      (univ.filter (fun v => ∃ p, T.par v = some p ∧ col p ≠ col v)).card := by
  classical
  -- for every colour `c ≠ col root`, a vertex of colour `c` of minimum depth has a parent of another colour
  have key : ∀ c ∈ (univ.image col).erase (col T.root), ∃ v, col v = c ∧
      ∃ p, T.par v = some p ∧ col p ≠ col v := by
    intro c hc
    obtain ⟨hcr, hcim⟩ := Finset.mem_erase.mp hc
    obtain ⟨v0, -, hv0⟩ := Finset.mem_image.mp hcim
    have hne : (univ.filter (fun v => col v = c)).Nonempty := ⟨v0, by simp [hv0]⟩
    obtain ⟨v, hvmem, hvmin⟩ := Finset.exists_min_image _ T.dep hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hvmem
    have hvroot : v ≠ T.root := by
      intro h; subst h; exact hcr hvmem.symm
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (T.par_some v hvroot)
    refine ⟨v, hvmem, p, hp, fun hpc => ?_⟩
    have hdep := T.dep_par v p hp
    have := hvmin p (by simp [hpc, hvmem])
    omega
  have hW : Nonempty W := ⟨T.root⟩
  choose! f hf using key
  have hinj : Set.InjOn f ((univ.image col).erase (col T.root) : Set κ) := by
    intro c hc c' hc' h
    have h1 := (hf c hc).1
    have h2 := (hf c' hc').1
    rw [← h1, ← h2, h]
  have hmaps : ∀ c ∈ (univ.image col).erase (col T.root),
      f c ∈ univ.filter (fun v => ∃ p, T.par v = some p ∧ col p ≠ col v) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hf c hc).2
  have := Finset.card_le_card_of_injOn f hmaps hinj
  have hroot : col T.root ∈ univ.image col := Finset.mem_image_of_mem col (Finset.mem_univ _)
  rw [Finset.card_erase_of_mem hroot] at this
  exact this

end Frontier.CostCharging
