import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Frontier.SpecGen — shortest paths over a generic ordered weight monoid

Owner: agent-08.  Same semantics as `Frontier.Spec`, but edge weights live in any linearly
ordered cancellative additive commutative monoid `α` with nonnegative weights.  Purpose: the
DMSY-style algorithms compare *tuple* labels; with the lexicographic monoid `ℝ≥0 ×ₗ ℕ` and
edge weights `(w e, 1)` every edge is strictly positive, lexicographically shortest walks are
simple, and hop counts strictly increase along them (`Visits.dist_lt`).  The bridge lemmas
relating this file to `Frontier.Spec` live in `Frontier.SpecBridge`.

* `WGraph α`, `IsWalk`, `len`, `dist : WithTop α` (minimum over walks with `< n` edges);
* `dist_le_len`, `exists_shortest_path`, `dist_eq_top_iff`, triangle inequalities;
* the frontier framework of `Frontier.Spec` (Visits/Utilde/IsFrontier, Observation 2.1,
  framework step, frontier split), and for strictly positive weights the strict monotonicity
  `Visits.dist_lt` needed for tuple-keyed frontier splits.
-/

set_option linter.unusedSectionVars false

namespace Frontier
namespace Gen

universe u

/-- A finite directed multigraph with nonnegative weights in `α`. -/
structure WGraph (α : Type u) [AddCommMonoid α] [LinearOrder α] where
  n : ℕ
  m : ℕ
  src : Fin m → Fin n
  dst : Fin m → Fin n
  w : Fin m → α
  w_nonneg : ∀ e, 0 ≤ w e

variable {α : Type u} [AddCommMonoid α] [LinearOrder α] [IsOrderedCancelAddMonoid α]

namespace WGraph

variable (G : WGraph α)

inductive IsWalk : Fin G.n → Fin G.n → List (Fin G.m) → Prop
  | nil (u : Fin G.n) : IsWalk u u []
  | cons {e : Fin G.m} {v : Fin G.n} {p : List (Fin G.m)} :
      IsWalk (G.dst e) v p → IsWalk (G.src e) v (e :: p)

def len (p : List (Fin G.m)) : α := (p.map G.w).sum

def verts (u : Fin G.n) (p : List (Fin G.m)) : List (Fin G.n) := u :: p.map G.dst

def Reachable (u v : Fin G.n) : Prop := ∃ p, G.IsWalk u v p

/-- Walks from `s` to `v` with fewer than `n` edges (a finite set). -/
noncomputable def shortWalks (s v : Fin G.n) : Finset (List (Fin G.m)) :=
  ((List.finite_length_lt (Fin G.m) G.n).subset
    (t := {p : List (Fin G.m) | p.length < G.n ∧ G.IsWalk s v p}) (fun _ hp => hp.1)).toFinset

/-- The exact distance: minimum length over walks (attained on simple paths), `⊤` if
unreachable. -/
noncomputable def dist (s v : Fin G.n) : WithTop α := ((G.shortWalks s v).image G.len).min

variable {G}

theorem mem_shortWalks {s v : Fin G.n} {p : List (Fin G.m)} :
    p ∈ G.shortWalks s v ↔ p.length < G.n ∧ G.IsWalk s v p := by
  unfold shortWalks
  rw [Set.Finite.mem_toFinset]
  rfl

@[simp] theorem len_nil : G.len [] = 0 := by simp [len]
@[simp] theorem len_cons (e : Fin G.m) (p : List (Fin G.m)) :
    G.len (e :: p) = G.w e + G.len p := by simp [len]
@[simp] theorem len_append (p q : List (Fin G.m)) :
    G.len (p ++ q) = G.len p + G.len q := by simp [len]
@[simp] theorem len_singleton (e : Fin G.m) : G.len [e] = G.w e := by simp [len]

theorem len_nonneg (p : List (Fin G.m)) : 0 ≤ G.len p := by
  induction p with
  | nil => simp
  | cons e p ih => rw [len_cons]; exact add_nonneg (G.w_nonneg e) ih

theorem IsWalk.single (e : Fin G.m) : G.IsWalk (G.src e) (G.dst e) [e] :=
  IsWalk.cons (IsWalk.nil _)

theorem IsWalk.append {u v x : Fin G.n} {p q : List (Fin G.m)}
    (hp : G.IsWalk u v p) (hq : G.IsWalk v x q) : G.IsWalk u x (p ++ q) := by
  induction hp with
  | nil u => simpa using hq
  | cons _ ih => exact IsWalk.cons (ih hq)

theorem IsWalk.of_append {u x : Fin G.n} {p q : List (Fin G.m)}
    (h : G.IsWalk u x (p ++ q)) : ∃ v, G.IsWalk u v p ∧ G.IsWalk v x q := by
  induction p generalizing u with
  | nil => exact ⟨u, IsWalk.nil u, by simpa using h⟩
  | cons e p ih =>
    cases h with
    | cons h' =>
      obtain ⟨v, hp, hq⟩ := ih h'
      exact ⟨v, IsWalk.cons hp, hq⟩

theorem isWalk_nil_iff {u v : Fin G.n} : G.IsWalk u v [] ↔ u = v := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact IsWalk.nil u

theorem isWalk_cons_iff {u v : Fin G.n} {e : Fin G.m} {p : List (Fin G.m)} :
    G.IsWalk u v (e :: p) ↔ G.src e = u ∧ G.IsWalk (G.dst e) v p := by
  constructor
  · intro h; cases h with | cons h' => exact ⟨rfl, h'⟩
  · rintro ⟨rfl, h⟩; exact IsWalk.cons h

theorem IsWalk.concat_iff {u x : Fin G.n} {p : List (Fin G.m)} {e : Fin G.m} :
    G.IsWalk u x (p ++ [e]) ↔ G.IsWalk u (G.src e) p ∧ G.dst e = x := by
  constructor
  · intro h
    obtain ⟨v, hp, he⟩ := h.of_append
    rw [isWalk_cons_iff, isWalk_nil_iff] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨hp, rfl⟩
  · rintro ⟨hp, rfl⟩
    exact hp.append (IsWalk.single e)

@[simp] theorem verts_nil (u : Fin G.n) : G.verts u [] = [u] := rfl
theorem verts_cons (u : Fin G.n) (e : Fin G.m) (p : List (Fin G.m)) :
    G.verts u (e :: p) = u :: G.verts (G.dst e) p := rfl
@[simp] theorem length_verts (u : Fin G.n) (p : List (Fin G.m)) :
    (G.verts u p).length = p.length + 1 := by simp [verts]

theorem IsWalk.split_at_mem {x v : Fin G.n} {q : List (Fin G.m)} (hq : G.IsWalk x v q)
    {u : Fin G.n} (hu : u ∈ G.verts x q) :
    ∃ pre suf, q = pre ++ suf ∧ G.IsWalk x u pre ∧ G.IsWalk u v suf ∧
      G.verts u suf <:+ G.verts x q := by
  induction hq with
  | nil x =>
    simp only [verts_nil, List.mem_singleton] at hu
    subst hu
    exact ⟨[], [], rfl, IsWalk.nil _, IsWalk.nil _, List.suffix_refl _⟩
  | @cons e v p h ih =>
    rw [verts_cons, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact ⟨[], e :: p, rfl, IsWalk.nil _, IsWalk.cons h, List.suffix_refl _⟩
    · obtain ⟨pre, suf, rfl, hpre, hsuf, hsx⟩ := ih hu
      refine ⟨e :: pre, suf, rfl, IsWalk.cons hpre, hsuf, ?_⟩
      rw [verts_cons]
      exact hsx.trans (List.suffix_cons _ _)

theorem IsWalk.exists_path {u v : Fin G.n} {p : List (Fin G.m)} (hp : G.IsWalk u v p) :
    ∃ q, G.IsWalk u v q ∧ G.len q ≤ G.len p ∧ (G.verts u q).Nodup := by
  induction hp with
  | nil u => exact ⟨[], IsWalk.nil u, le_rfl, by simp⟩
  | @cons e v p h ih =>
    obtain ⟨q, hq, hlen, hnd⟩ := ih
    by_cases hmem : G.src e ∈ G.verts (G.dst e) q
    · obtain ⟨pre, suf, rfl, _, hsuf, hsx⟩ := hq.split_at_mem hmem
      refine ⟨suf, hsuf, ?_, hnd.sublist hsx.sublist⟩
      rw [len_append] at hlen
      rw [len_cons]
      calc G.len suf ≤ G.len pre + G.len suf := le_add_of_nonneg_left (len_nonneg pre)
        _ ≤ G.len p := hlen
        _ ≤ G.w e + G.len p := le_add_of_nonneg_left (G.w_nonneg e)
    · refine ⟨e :: q, IsWalk.cons hq, ?_, ?_⟩
      · rw [len_cons, len_cons]
        exact add_le_add_right hlen _
      · rw [verts_cons]
        exact List.nodup_cons.mpr ⟨hmem, hnd⟩

theorem length_lt_of_nodup {u : Fin G.n} {q : List (Fin G.m)} (h : (G.verts u q).Nodup) :
    q.length < G.n := by
  have := h.length_le_card
  simp only [length_verts, Fintype.card_fin] at this
  omega

/-! ## Distances -/

theorem dist_le_len {s v : Fin G.n} {p : List (Fin G.m)} (hp : G.IsWalk s v p) :
    G.dist s v ≤ G.len p := by
  obtain ⟨q, hq, hle, hnd⟩ := hp.exists_path
  have hmem : q ∈ G.shortWalks s v := mem_shortWalks.mpr ⟨length_lt_of_nodup hnd, hq⟩
  calc G.dist s v ≤ G.len q := Finset.min_le (Finset.mem_image_of_mem _ hmem)
    _ ≤ G.len p := WithTop.coe_le_coe.mpr hle

theorem exists_shortest_path {s v : Fin G.n} (h : G.Reachable s v) :
    ∃ p, G.IsWalk s v p ∧ (G.len p : WithTop α) = G.dist s v ∧ p.length < G.n := by
  obtain ⟨p0, hp0⟩ := h
  obtain ⟨q0, hq0, -, hnd0⟩ := hp0.exists_path
  have hne : ((G.shortWalks s v).image G.len).Nonempty :=
    ⟨_, Finset.mem_image_of_mem _ (mem_shortWalks.mpr ⟨length_lt_of_nodup hnd0, hq0⟩)⟩
  obtain ⟨a, ha⟩ := Finset.min_of_nonempty hne
  have hamem := Finset.mem_of_min ha
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hamem
  obtain ⟨hpl, hpw⟩ := mem_shortWalks.mp hp
  exact ⟨p, hpw, ha.symm, hpl⟩

theorem dist_eq_top_iff {s v : Fin G.n} : G.dist s v = ⊤ ↔ ¬ G.Reachable s v := by
  constructor
  · intro h hr
    obtain ⟨p, -, hp, -⟩ := exists_shortest_path hr
    rw [← hp] at h
    exact WithTop.coe_ne_top h
  · intro h
    unfold dist
    rw [Finset.min_eq_top, Finset.image_eq_empty]
    ext p
    simp only [Finset.notMem_empty, iff_false]
    intro hp
    exact h ⟨p, (mem_shortWalks.mp hp).2⟩

theorem dist_ne_top_iff {s v : Fin G.n} : G.dist s v ≠ ⊤ ↔ G.Reachable s v := by
  rw [Ne, dist_eq_top_iff, not_not]

theorem exists_walk_eq_dist {s v : Fin G.n} (h : G.dist s v ≠ ⊤) :
    ∃ p, G.IsWalk s v p ∧ (G.len p : WithTop α) = G.dist s v := by
  obtain ⟨p, hp, heq, -⟩ := exists_shortest_path (dist_ne_top_iff.mp h)
  exact ⟨p, hp, heq⟩

theorem dist_nonneg (s v : Fin G.n) : 0 ≤ G.dist s v := by
  by_cases h : G.dist s v = ⊤
  · rw [h]; exact le_top
  · obtain ⟨p, -, hp⟩ := exists_walk_eq_dist h
    rw [← hp]
    exact WithTop.coe_le_coe.mpr (len_nonneg p)

@[simp] theorem dist_self (s : Fin G.n) : G.dist s s = 0 :=
  le_antisymm ((dist_le_len (IsWalk.nil s)).trans (by simp)) (dist_nonneg s s)

theorem dist_le_dist_add_len {s u v : Fin G.n} {p : List (Fin G.m)} (hp : G.IsWalk u v p) :
    G.dist s v ≤ G.dist s u + G.len p := by
  by_cases hu : G.dist s u = ⊤
  · simp [hu]
  · obtain ⟨q, hq, hqe⟩ := exists_walk_eq_dist hu
    calc G.dist s v ≤ G.len (q ++ p) := dist_le_len (hq.append hp)
      _ = G.dist s u + G.len p := by rw [len_append, WithTop.coe_add, hqe]

theorem dist_edge (s : Fin G.n) (e : Fin G.m) :
    G.dist s (G.dst e) ≤ G.dist s (G.src e) + G.w e := by
  simpa using dist_le_dist_add_len (s := s) (IsWalk.single e)

/-- Uniqueness of the distance function: any function that lower-bounds every walk and is
attained (or `⊤` exactly when unreachable) equals `dist`. -/
theorem dist_eq_of_spec {s v : Fin G.n} {x : WithTop α}
    (hle : ∀ p, G.IsWalk s v p → x ≤ G.len p)
    (hatt : x ≠ ⊤ → ∃ p, G.IsWalk s v p ∧ (G.len p : WithTop α) = x)
    (htop : x = ⊤ → ¬ G.Reachable s v) : G.dist s v = x := by
  by_cases hx : x = ⊤
  · rw [hx]; exact dist_eq_top_iff.mpr (htop hx)
  · obtain ⟨p, hp, hpx⟩ := hatt hx
    refine le_antisymm (hpx ▸ dist_le_len hp) ?_
    obtain ⟨q, hq, hqe⟩ := exists_walk_eq_dist (dist_ne_top_iff.mpr ⟨p, hp⟩)
    rw [← hqe]
    exact hle q hq

/-! ## Frontier framework over `α` -/

section FrontierFramework

variable (G) (s : Fin G.n)

def Visits (y v : Fin G.n) : Prop :=
  G.dist s v ≠ ⊤ ∧ ∃ q, G.IsWalk y v q ∧ G.dist s v = G.dist s y + G.len q

def Utilde (B : WithTop α) (S : Set (Fin G.n)) : Set (Fin G.n) :=
  {v | G.dist s v < B ∧ ∃ y ∈ S, G.Visits s y v}

def Complete (d : Fin G.n → WithTop α) (v : Fin G.n) : Prop := d v = G.dist s v

def Sound (d : Fin G.n → WithTop α) : Prop := ∀ v, G.dist s v ≤ d v

def IsFrontier (d : Fin G.n → WithTop α) (U X Y : Set (Fin G.n)) : Prop :=
  ∀ v ∈ U, (v ∈ X ∧ G.Complete s d v) ∨ ∃ y ∈ Y, G.Complete s d y ∧ G.Visits s y v

def Relaxed (d : Fin G.n → WithTop α) (B : WithTop α) (Z : Set (Fin G.n)) : Set (Fin G.n) :=
  {v | v ∉ Z ∧ ∃ e, G.src e ∈ Z ∧ G.dst e = v ∧ d v = d (G.src e) + G.w e ∧ d v < B}

variable {G} {s}

theorem Visits.dist_le {y v : Fin G.n} (h : G.Visits s y v) : G.dist s y ≤ G.dist s v := by
  obtain ⟨-, q, -, hq⟩ := h
  rw [hq]
  exact le_add_of_nonneg_right (WithTop.coe_le_coe.mpr (len_nonneg q))

theorem visits_split {y x v : Fin G.n} {q₁ q₂ : List (Fin G.m)}
    (h : G.dist s v = G.dist s y + G.len (q₁ ++ q₂))
    (h₁ : G.IsWalk y x q₁) (h₂ : G.IsWalk x v q₂) :
    G.dist s x = G.dist s y + G.len q₁ ∧ G.dist s v = G.dist s x + G.len q₂ := by
  have hx : G.dist s x ≤ G.dist s y + G.len q₁ := dist_le_dist_add_len h₁
  have hv' : G.dist s v ≤ G.dist s x + G.len q₂ := dist_le_dist_add_len h₂
  have hsum : G.dist s y + (G.len (q₁ ++ q₂) : WithTop α) =
      G.dist s y + G.len q₁ + G.len q₂ := by
    rw [len_append, WithTop.coe_add, add_assoc]
  have h2 : G.dist s v = G.dist s x + G.len q₂ := by
    refine le_antisymm hv' ?_
    calc G.dist s x + G.len q₂ ≤ G.dist s y + G.len q₁ + G.len q₂ := add_le_add_left hx _
      _ = G.dist s v := by rw [h, hsum]
  refine ⟨?_, h2⟩
  have : G.dist s x + G.len q₂ = G.dist s y + G.len q₁ + G.len q₂ := by
    rw [← h2, h, hsum]
  exact WithTop.add_right_cancel WithTop.coe_ne_top this

theorem Visits.trans {x y v : Fin G.n} (h₁ : G.Visits s x y) (h₂ : G.Visits s y v) :
    G.Visits s x v := by
  obtain ⟨-, q₁, hq₁, e₁⟩ := h₁
  obtain ⟨hv, q₂, hq₂, e₂⟩ := h₂
  refine ⟨hv, q₁ ++ q₂, hq₁.append hq₂, ?_⟩
  rw [e₂, e₁, len_append, WithTop.coe_add, add_assoc]

theorem visits_self {v : Fin G.n} (hv : G.dist s v ≠ ⊤) : G.Visits s v v :=
  ⟨hv, [], IsWalk.nil v, by simp⟩

theorem IsWalk.exists_exit {y v : Fin G.n} {q : List (Fin G.m)} (hq : G.IsWalk y v q)
    (Z : Set (Fin G.n)) (hy : y ∈ Z) (hv : v ∉ Z) :
    ∃ q₁ e q₂, q = q₁ ++ e :: q₂ ∧ G.IsWalk y (G.src e) q₁ ∧ G.src e ∈ Z ∧ G.dst e ∉ Z ∧
      G.IsWalk (G.dst e) v q₂ := by
  induction hq with
  | nil u => exact absurd hy hv
  | @cons e x p h ih =>
    by_cases hd : G.dst e ∈ Z
    · obtain ⟨q₁, e', q₂, rfl, h₁, hs, hd', h₂⟩ := ih hd hv
      exact ⟨e :: q₁, e', q₂, rfl, IsWalk.cons h₁, hs, hd', h₂⟩
    · exact ⟨[], e, p, rfl, IsWalk.nil _, hy, hd, h⟩

theorem Complete.of_le {d d' : Fin G.n → WithTop α} {v : Fin G.n} (h : G.Complete s d v)
    (hsound : G.Sound s d') (hle : d' v ≤ d v) : G.Complete s d' v :=
  le_antisymm (hle.trans h.le) (hsound v)

theorem IsFrontier.of_le {d d' : Fin G.n → WithTop α} {U X Y : Set (Fin G.n)}
    (hF : G.IsFrontier s d U X Y) (hsound : G.Sound s d') (hle : ∀ v, d' v ≤ d v) :
    G.IsFrontier s d' U X Y := by
  intro v hv
  rcases hF v hv with ⟨hX, hc⟩ | ⟨y, hy, hc, hvis⟩
  · exact Or.inl ⟨hX, hc.of_le hsound (hle v)⟩
  · exact Or.inr ⟨y, hy, hc.of_le hsound (hle y), hvis⟩

theorem IsFrontier.mono {d : Fin G.n → WithTop α} {U U' X X' Y Y' : Set (Fin G.n)}
    (hF : G.IsFrontier s d U X Y) (hU : U' ⊆ U) (hX : X ⊆ X') (hY : Y ⊆ Y') :
    G.IsFrontier s d U' X' Y' := by
  intro v hv
  rcases hF v (hU hv) with ⟨hx, hc⟩ | ⟨y, hy, hc, hvis⟩
  · exact Or.inl ⟨hX hx, hc⟩
  · exact Or.inr ⟨y, hY hy, hc, hvis⟩

theorem utilde_subset {B : WithTop α} {S Y : Set (Fin G.n)} (hY : Y ⊆ G.Utilde s B S) :
    G.Utilde s B Y ⊆ G.Utilde s B S := by
  rintro v ⟨hvB, y, hy, hvis⟩
  obtain ⟨-, x, hx, hxy⟩ := hY hy
  exact ⟨hvB, x, hx, hxy.trans hvis⟩

theorem utilde_mono_bound {B B' : WithTop α} {S : Set (Fin G.n)} (h : B' ≤ B) :
    G.Utilde s B' S ⊆ G.Utilde s B S :=
  fun _ hv => ⟨lt_of_lt_of_le hv.1 h, hv.2⟩

theorem IsFrontier.restrict {d : Fin G.n → WithTop α} {B : WithTop α} {S X Y : Set (Fin G.n)}
    (hF : G.IsFrontier s d (G.Utilde s B S) X Y) (hY : Y ⊆ G.Utilde s B S) :
    G.IsFrontier s d (G.Utilde s B Y) ∅ Y := by
  rintro v ⟨-, y, hy, hvis⟩
  by_cases hc : G.Complete s d y
  · exact Or.inr ⟨y, hy, hc, hvis⟩
  · rcases hF y (hY hy) with ⟨-, hc'⟩ | ⟨y', hy', hc', hvis'⟩
    · exact absurd hc' hc
    · exact Or.inr ⟨y', hy', hc', hvis'.trans hvis⟩

theorem IsFrontier.complete_of_min {d : Fin G.n → WithTop α} {B : WithTop α}
    {S X Y : Set (Fin G.n)}
    (hF : G.IsFrontier s d (G.Utilde s B S) X Y) (hY : Y ⊆ G.Utilde s B S)
    (hsound : G.Sound s d) {y : Fin G.n} (hy : y ∈ Y) (hmin : ∀ y' ∈ Y, d y ≤ d y') :
    G.Complete s d y := by
  rcases hF y (hY hy) with ⟨-, hc⟩ | ⟨y', hy', hc', hvis⟩
  · exact hc
  · refine le_antisymm ?_ (hsound y)
    calc d y ≤ d y' := hmin y' hy'
      _ = G.dist s y' := hc'
      _ ≤ G.dist s y := hvis.dist_le

theorem IsFrontier.step {d d' : Fin G.n → WithTop α} {B : WithTop α} {U X Y Z : Set (Fin G.n)}
    (hF : G.IsFrontier s d U X Y) (hU : ∀ v ∈ U, G.dist s v < B)
    (hsound : G.Sound s d') (hle : ∀ v, d' v ≤ d v)
    (hZ : ∀ z ∈ Z, G.Complete s d' z)
    (hrelax : ∀ e, G.src e ∈ Z → d' (G.src e) + G.w e < B →
      d' (G.dst e) ≤ d' (G.src e) + G.w e) :
    G.IsFrontier s d' U (X ∪ Z) ((Y \ Z) ∪ G.Relaxed d' B Z) := by
  intro v hvU
  rcases hF v hvU with ⟨hX, hc⟩ | ⟨y, hy, hc, hvis⟩
  · exact Or.inl ⟨Or.inl hX, hc.of_le hsound (hle v)⟩
  · by_cases hyZ : y ∈ Z
    · by_cases hvZ : v ∈ Z
      · exact Or.inl ⟨Or.inr hvZ, hZ v hvZ⟩
      · obtain ⟨hvtop, q, hq, hqe⟩ := hvis
        obtain ⟨q₁, e, q₂, rfl, h₁, hsZ, hdZ, h₂⟩ := hq.exists_exit Z hyZ hvZ
        have hqe' : G.dist s v = G.dist s y + G.len ((q₁ ++ [e]) ++ q₂) := by
          simpa [List.append_assoc] using hqe
        obtain ⟨hde, hvd⟩ := visits_split hqe' (h₁.append (IsWalk.single e)) h₂
        obtain ⟨-, hde'⟩ := visits_split hde h₁ (IsWalk.single e)
        have hdle : G.dist s (G.dst e) ≤ G.dist s v := by
          rw [hvd]; exact le_add_of_nonneg_right (WithTop.coe_le_coe.mpr (len_nonneg q₂))
        have hdB : G.dist s (G.dst e) < B := lt_of_le_of_lt hdle (hU v hvU)
        have hcs : d' (G.src e) = G.dist s (G.src e) := hZ _ hsZ
        have htight : d' (G.src e) + G.w e = G.dist s (G.dst e) := by
          rw [hcs, hde', len_singleton]
        have hrel := hrelax e hsZ (by rw [htight]; exact hdB)
        have hcd : G.Complete s d' (G.dst e) :=
          le_antisymm (hrel.trans htight.le) (hsound _)
        refine Or.inr ⟨G.dst e, Or.inr ⟨hdZ, e, hsZ, rfl, ?_, ?_⟩, hcd, ?_⟩
        · rw [hcd, htight]
        · rw [hcd]; exact hdB
        · exact ⟨hvtop, q₂, h₂, hvd⟩
    · exact Or.inr ⟨y, Or.inl ⟨hy, hyZ⟩, hc.of_le hsound (hle y), hvis⟩

theorem IsFrontier.split {d : Fin G.n → WithTop α} {B Bs : WithTop α} {S X Y Ys : Set (Fin G.n)}
    (hF : G.IsFrontier s d (G.Utilde s B S) X Y)
    (hYs₁ : ∀ y ∈ Y, d y < Bs → y ∈ Ys) (hYs₂ : Ys ⊆ G.Utilde s B S) :
    G.IsFrontier s d (G.Utilde s Bs Ys) ∅ Ys := by
  rintro v ⟨hvB, y, hy, hvis⟩
  by_cases hc : G.Complete s d y
  · exact Or.inr ⟨y, hy, hc, hvis⟩
  · rcases hF y (hYs₂ hy) with ⟨-, hc'⟩ | ⟨y', hy', hc', hvis'⟩
    · exact absurd hc' hc
    · refine Or.inr ⟨y', hYs₁ y' hy' ?_, hc', hvis'.trans hvis⟩
      rw [hc']
      exact lt_of_le_of_lt (hvis'.trans hvis).dist_le hvB

theorem IsFrontier.complete_of_empty {d : Fin G.n → WithTop α} {U X : Set (Fin G.n)}
    (hF : G.IsFrontier s d U X ∅) : ∀ v ∈ U, v ∈ X ∧ G.Complete s d v := by
  intro v hv
  rcases hF v hv with h | ⟨y, hy, -⟩
  · exact h
  · exact absurd hy (Set.notMem_empty y)

theorem isFrontier_init {d : Fin G.n → WithTop α} (hs : d s = 0) :
    G.IsFrontier s d (G.Utilde s ⊤ {s}) ∅ {s} := by
  rintro v ⟨-, y, hy, hvis⟩
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact Or.inr ⟨y, rfl, by simp [Complete, hs], hvis⟩

/-! ### Strictly positive weights: strict monotonicity along shortest walks -/

/-- With strictly positive weights, a vertex strictly before `v` on a shortest walk to `v` has
strictly smaller distance.  (For the lexicographic `(length, hops)` monoid this is what makes
tuple-keyed frontier splits work.) -/
theorem visits_dist_lt (hpos : ∀ e, 0 < G.w e) {y v : Fin G.n} {q : List (Fin G.m)}
    (hv : G.dist s v ≠ ⊤) (hq : G.IsWalk y v q) (hqe : G.dist s v = G.dist s y + G.len q)
    (hne : q ≠ []) : G.dist s y < G.dist s v := by
  have hy : G.dist s y ≠ ⊤ := by
    intro h; rw [hqe, h, WithTop.top_add] at hv; exact hv rfl
  have hlen : 0 < G.len q := by
    cases q with
    | nil => exact absurd rfl hne
    | cons e p => rw [len_cons]; exact add_pos_of_pos_of_nonneg (hpos e) (len_nonneg p)
  rw [hqe]
  lift G.dist s y to α using hy with a
  rw [← WithTop.coe_add, WithTop.coe_lt_coe]
  exact lt_add_of_pos_right a hlen

end FrontierFramework

end WGraph
end Gen
end Frontier
