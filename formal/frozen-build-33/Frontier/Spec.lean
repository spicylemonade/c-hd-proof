import Mathlib.Basic.ENNReal.Operations
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Fintype.Card

/-!
# Frontier.Spec — exact semantics of directed nonnegative-real SSSP

Owner: agent-08.  This file fixes the *problem contract* used by every Frontier lane.

* `Graph`: an explicitly represented finite directed multigraph.  Vertices are `Fin G.n`,
  edges are indices `Fin G.m` with `src`, `dst : Fin G.m → Fin G.n` and nonnegative real
  weights `w : Fin G.m → ℝ≥0`.  Parallel edges, self loops, zero weights and zero-weight
  cycles are all allowed.
* `IsWalk G u v p`: `p : List (Fin G.m)` is a directed walk from `u` to `v`.
* `len G p : ℝ≥0` is the total weight of an edge list.
* `dist G s v : ℝ≥0∞` is the infimum of `len` over all walks from `s` to `v`;
  it is `⊤` exactly for unreachable vertices (`dist_eq_top_iff`), it is attained by a
  vertex-simple path with fewer than `G.n` edges (`exists_shortest_path`).
* `IsSSSP G s d`: the exact labeled output contract, `d v = dist G s v` for every vertex.
* `IsSPTree G s d pred`: exact labels plus a predecessor-edge shortest-path arborescence.
* Certificate theorems (`eq_dist_of_relaxed_of_realized`, `isSPTree_of_certificate`):
  the reusable correctness endpoint for label-setting / label-correcting algorithms.
* Frontier framework (Duan–Mao–Shu–Yin 2026, §2.5), stated *without* any unique-shortest-path
  assumption: `Visits`, `Utilde`, `IsFrontier`, the observations of their Observation 2.1,
  the framework step lemma (`IsFrontier.step`) and the frontier split (`IsFrontier.split`).

No axioms beyond Lean's standard `propext`, `Classical.choice`, `Quot.sound`.
-/

open scoped ENNReal NNReal

namespace Frontier

/-- An explicitly represented finite directed graph with nonnegative real edge weights.
Edges are identified by their index `Fin m`; multi-edges and self-loops are allowed. -/
structure Graph where
  /-- number of vertices -/
  n : ℕ
  /-- number of edges -/
  m : ℕ
  /-- tail of each edge -/
  src : Fin m → Fin n
  /-- head of each edge -/
  dst : Fin m → Fin n
  /-- nonnegative real weight of each edge -/
  w : Fin m → ℝ≥0

namespace Graph

variable (G : Graph)

/-- `G.IsWalk u v p`: the edge list `p` is a directed walk in `G` from `u` to `v`. -/
inductive IsWalk : Fin G.n → Fin G.n → List (Fin G.m) → Prop
  | nil (u : Fin G.n) : IsWalk u u []
  | cons {e : Fin G.m} {v : Fin G.n} {p : List (Fin G.m)} :
      IsWalk (G.dst e) v p → IsWalk (G.src e) v (e :: p)

/-- Total weight of an edge list. -/
def len (p : List (Fin G.m)) : ℝ≥0 := (p.map G.w).sum

/-- The vertex sequence visited by the edge list `p` when started at `u`. -/
def verts (u : Fin G.n) (p : List (Fin G.m)) : List (Fin G.n) := u :: p.map G.dst

/-- `v` is reachable from `u`. -/
def Reachable (u v : Fin G.n) : Prop := ∃ p, G.IsWalk u v p

/-- The exact shortest-path distance, `⊤` when `v` is unreachable from `s`. -/
noncomputable def dist (s v : Fin G.n) : ℝ≥0∞ :=
  ⨅ (p : List (Fin G.m)) (_ : G.IsWalk s v p), ((G.len p : ℝ≥0) : ℝ≥0∞)

variable {G}

/-! ## Walk algebra -/

@[simp] theorem len_nil : G.len [] = 0 := by simp [len]

@[simp] theorem len_cons (e : Fin G.m) (p : List (Fin G.m)) :
    G.len (e :: p) = G.w e + G.len p := by simp [len]

@[simp] theorem len_append (p q : List (Fin G.m)) :
    G.len (p ++ q) = G.len p + G.len q := by simp [len]

@[simp] theorem len_singleton (e : Fin G.m) : G.len [e] = G.w e := by simp [len]

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

theorem isWalk_cons_iff {u v : Fin G.n} {e : Fin G.m} {p : List (Fin G.m)} :
    G.IsWalk u v (e :: p) ↔ G.src e = u ∧ G.IsWalk (G.dst e) v p := by
  constructor
  · intro h
    cases h with
    | cons h' => exact ⟨rfl, h'⟩
  · rintro ⟨rfl, h⟩
    exact IsWalk.cons h

theorem isWalk_nil_iff {u v : Fin G.n} : G.IsWalk u v [] ↔ u = v := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact IsWalk.nil u

/-- The last edge of a nonempty walk ends at the walk's endpoint. -/
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

/-- The endpoint of a walk is its last visited vertex. -/
theorem IsWalk.end_mem_verts {u v : Fin G.n} {p : List (Fin G.m)} (h : G.IsWalk u v p) :
    v ∈ G.verts u p := by
  induction h with
  | nil u => simp
  | cons _ ih => rw [verts_cons]; exact List.mem_cons_of_mem _ ih

/-- A vertex visited by a walk splits it. -/
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

/-- Every walk can be shortcut to a vertex-simple path of no larger weight. -/
theorem IsWalk.exists_path {u v : Fin G.n} {p : List (Fin G.m)} (hp : G.IsWalk u v p) :
    ∃ q, G.IsWalk u v q ∧ G.len q ≤ G.len p ∧ (G.verts u q).Nodup := by
  induction hp with
  | nil u => exact ⟨[], IsWalk.nil u, le_rfl, by simp⟩
  | @cons e v p h ih =>
    obtain ⟨q, hq, hlen, hnd⟩ := ih
    by_cases hmem : G.src e ∈ G.verts (G.dst e) q
    · obtain ⟨_, suf, rfl, _, hsuf, hsx⟩ := hq.split_at_mem hmem
      refine ⟨suf, hsuf, ?_, hnd.sublist hsx.sublist⟩
      simp only [len_append, len_cons] at hlen ⊢
      calc G.len suf ≤ _ + G.len suf := le_add_self
        _ ≤ G.len p := hlen
        _ ≤ G.w e + G.len p := le_add_self
    · refine ⟨e :: q, IsWalk.cons hq, ?_, ?_⟩
      · simp only [len_cons]
        exact add_le_add_right hlen _
      · rw [verts_cons]
        exact List.nodup_cons.mpr ⟨hmem, hnd⟩

/-- A vertex-simple path has fewer than `n` edges. -/
theorem length_lt_of_nodup {u : Fin G.n} {q : List (Fin G.m)} (h : (G.verts u q).Nodup) :
    q.length < G.n := by
  have := h.length_le_card
  simp only [length_verts, Fintype.card_fin] at this
  omega

/-! ## Distances -/

theorem dist_le_len {s v : Fin G.n} {p : List (Fin G.m)} (hp : G.IsWalk s v p) :
    G.dist s v ≤ G.len p :=
  iInf₂_le p hp

/-- Shortest paths exist, are vertex-simple and have fewer than `n` edges.  This is where
zero-weight cycles are handled: they can always be cut out. -/
theorem exists_shortest_path {s v : Fin G.n} (h : G.Reachable s v) :
    ∃ p, G.IsWalk s v p ∧ ((G.len p : ℝ≥0) : ℝ≥0∞) = G.dist s v ∧
      (G.verts s p).Nodup ∧ p.length < G.n := by
  let S : Set (List (Fin G.m)) := {p | p.length < G.n ∧ G.IsWalk s v p ∧ (G.verts s p).Nodup}
  have hfin : S.Finite := (List.finite_length_lt (Fin G.m) G.n).subset fun p hp => hp.1
  obtain ⟨p0, hp0⟩ := h
  obtain ⟨q0, hq0, -, hnd0⟩ := hp0.exists_path
  have hne : S.Nonempty := ⟨q0, length_lt_of_nodup hnd0, hq0, hnd0⟩
  obtain ⟨p, ⟨hpl, hpw, hpnd⟩, hmin⟩ := Set.exists_min_image S G.len hfin hne
  refine ⟨p, hpw, le_antisymm ?_ (dist_le_len hpw), hpnd, hpl⟩
  refine le_iInf₂ fun q hq => ?_
  obtain ⟨q', hq', hle, hnd⟩ := hq.exists_path
  exact ENNReal.coe_le_coe.mpr ((hmin q' ⟨length_lt_of_nodup hnd, hq', hnd⟩).trans hle)

theorem dist_eq_top_iff {s v : Fin G.n} : G.dist s v = ⊤ ↔ ¬ G.Reachable s v := by
  constructor
  · intro h hr
    obtain ⟨p, -, hp, -, -⟩ := exists_shortest_path hr
    rw [← hp] at h
    exact ENNReal.coe_ne_top h
  · intro h
    exact top_le_iff.mp (le_iInf₂ fun p hp => (h ⟨p, hp⟩).elim)

theorem dist_ne_top_iff {s v : Fin G.n} : G.dist s v ≠ ⊤ ↔ G.Reachable s v := by
  rw [Ne, dist_eq_top_iff, not_not]

theorem dist_lt_top_iff {s v : Fin G.n} : G.dist s v < ⊤ ↔ G.Reachable s v := by
  rw [lt_top_iff_ne_top, dist_ne_top_iff]

@[simp] theorem dist_self (s : Fin G.n) : G.dist s s = 0 :=
  le_antisymm ((dist_le_len (IsWalk.nil s)).trans (by simp)) zero_le

/-- If `v` is reachable there is a walk whose length equals the distance. -/
theorem exists_walk_eq_dist {s v : Fin G.n} (h : G.dist s v ≠ ⊤) :
    ∃ p, G.IsWalk s v p ∧ ((G.len p : ℝ≥0) : ℝ≥0∞) = G.dist s v := by
  obtain ⟨p, hp, heq, -, -⟩ := exists_shortest_path (dist_ne_top_iff.mp h)
  exact ⟨p, hp, heq⟩

/-- Triangle inequality along a walk. -/
theorem dist_le_dist_add_len {s u v : Fin G.n} {p : List (Fin G.m)} (hp : G.IsWalk u v p) :
    G.dist s v ≤ G.dist s u + G.len p := by
  by_cases hu : G.dist s u = ⊤
  · simp [hu]
  · obtain ⟨q, hq, hqe⟩ := exists_walk_eq_dist hu
    calc G.dist s v ≤ G.len (q ++ p) := dist_le_len (hq.append hp)
      _ = G.dist s u + G.len p := by rw [len_append, ENNReal.coe_add, hqe]

/-- Triangle inequality for a single edge. -/
theorem dist_edge (s : Fin G.n) (e : Fin G.m) :
    G.dist s (G.dst e) ≤ G.dist s (G.src e) + G.w e := by
  simpa using dist_le_dist_add_len (s := s) (IsWalk.single e)

theorem reachable_of_isWalk {s u v : Fin G.n} {p : List (Fin G.m)}
    (hu : G.Reachable s u) (hp : G.IsWalk u v p) : G.Reachable s v := by
  obtain ⟨q, hq⟩ := hu
  exact ⟨q ++ p, hq.append hp⟩

/-! ## Output contracts -/

/-- Exact labeled single-source distances: every vertex receives its exact distance,
unreachable vertices receive `⊤`.  (No ordering of vertices is required.) -/
def IsSSSP (G : Graph) (s : Fin G.n) (d : Fin G.n → ℝ≥0∞) : Prop :=
  ∀ v, d v = G.dist s v

/-- Exact labels together with a predecessor-edge shortest-path arborescence rooted at `s`.
`pred v = some e` means edge `e` enters `v`; it is tight; unreachable vertices and the source
have no predecessor; every other reachable vertex has one; and predecessor pointers are
acyclic (witnessed by a strictly decreasing rank). -/
structure IsSPTree (G : Graph) (s : Fin G.n) (d : Fin G.n → ℝ≥0∞)
    (pred : Fin G.n → Option (Fin G.m)) : Prop where
  exact : G.IsSSSP s d
  pred_dst : ∀ v e, pred v = some e → G.dst e = v
  pred_tight : ∀ v e, pred v = some e → d v = d (G.src e) + G.w e
  pred_source : pred s = none
  pred_unreachable : ∀ v, d v = ⊤ → pred v = none
  pred_reachable : ∀ v, v ≠ s → d v ≠ ⊤ → pred v ≠ none
  acyclic : ∃ r : Fin G.n → ℕ, ∀ v e, pred v = some e → r (G.src e) < r v

/-! ## Certificates -/

/-- A labeling with `d s = 0` in which every edge is relaxed is a lower bound on distances. -/
theorem le_dist_of_relaxed {s : Fin G.n} {d : Fin G.n → ℝ≥0∞} (hs : d s = 0)
    (hrel : ∀ e, d (G.dst e) ≤ d (G.src e) + G.w e) (v : Fin G.n) : d v ≤ G.dist s v := by
  have key : ∀ u x p, G.IsWalk u x p → d x ≤ d u + G.len p := by
    intro u x p hp
    induction hp with
    | nil u => simp
    | @cons e x p _ ih =>
      calc d x ≤ d (G.dst e) + G.len p := ih
        _ ≤ d (G.src e) + G.w e + G.len p := add_le_add_left (hrel e) _
        _ = d (G.src e) + G.len (e :: p) := by
          rw [len_cons, ENNReal.coe_add, add_assoc]
  refine le_iInf₂ fun p hp => ?_
  simpa [hs] using key s v p hp

/-- A labeling whose finite values are realized by walks is an upper bound on distances. -/
theorem dist_le_of_realized {s : Fin G.n} {d : Fin G.n → ℝ≥0∞}
    (hreal : ∀ v, d v ≠ ⊤ → ∃ p, G.IsWalk s v p ∧ ((G.len p : ℝ≥0) : ℝ≥0∞) ≤ d v)
    (v : Fin G.n) : G.dist s v ≤ d v := by
  by_cases h : d v = ⊤
  · simp [h]
  · obtain ⟨p, hp, hle⟩ := hreal v h
    exact (dist_le_len hp).trans hle

/-- **Certificate theorem.**  `d s = 0`, all edges relaxed, and all finite labels realized by
walks imply that `d` is exactly the distance function (including `⊤` for unreachable vertices). -/
theorem isSSSP_of_relaxed_of_realized {s : Fin G.n} {d : Fin G.n → ℝ≥0∞} (hs : d s = 0)
    (hrel : ∀ e, d (G.dst e) ≤ d (G.src e) + G.w e)
    (hreal : ∀ v, d v ≠ ⊤ → ∃ p, G.IsWalk s v p ∧ ((G.len p : ℝ≥0) : ℝ≥0∞) ≤ d v) :
    G.IsSSSP s d := fun v =>
  le_antisymm (le_dist_of_relaxed hs hrel v) (dist_le_of_realized hreal v)

/-- The exact distance function satisfies the certificate. -/
theorem isSSSP_dist (s : Fin G.n) : G.IsSSSP s (G.dist s) := fun _ => rfl

theorem IsSSSP.unique {s : Fin G.n} {d d' : Fin G.n → ℝ≥0∞} (h : G.IsSSSP s d)
    (h' : G.IsSSSP s d') : d = d' := funext fun v => (h v).trans (h' v).symm

/-- Following tight acyclic predecessor pointers realizes every finite label by a walk. -/
theorem realized_of_pred {s : Fin G.n} {d : Fin G.n → ℝ≥0∞}
    {pred : Fin G.n → Option (Fin G.m)} (hs : d s = 0)
    (hdst : ∀ v e, pred v = some e → G.dst e = v)
    (htight : ∀ v e, pred v = some e → d v = d (G.src e) + G.w e)
    (hnone : ∀ v, v ≠ s → d v ≠ ⊤ → pred v ≠ none)
    {r : Fin G.n → ℕ} (hr : ∀ v e, pred v = some e → r (G.src e) < r v) :
    ∀ v, d v ≠ ⊤ → ∃ p, G.IsWalk s v p ∧ ((G.len p : ℝ≥0) : ℝ≥0∞) = d v := by
  intro v
  induction hk : r v using Nat.strong_induction_on generalizing v with
  | _ k ih =>
    intro hv
    by_cases hvs : v = s
    · subst hvs
      exact ⟨[], IsWalk.nil _, by simp [hs]⟩
    · obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp (hnone v hvs hv)
      have hsrc : d (G.src e) ≠ ⊤ := by
        intro h
        apply hv
        rw [htight v e he, h, top_add]
      obtain ⟨p, hp, hpe⟩ := ih (r (G.src e)) (hk ▸ hr v e he) (G.src e) rfl hsrc
      refine ⟨p ++ [e], ?_, ?_⟩
      · rw [IsWalk.concat_iff]
        exact ⟨hp, hdst v e he⟩
      · rw [len_append, len_singleton, ENNReal.coe_add, hpe, htight v e he]

/-- **Predecessor certificate.**  If `d s = 0`, every edge is relaxed, `pred` gives tight
entering edges for all finite non-source vertices and none for the source or unreachable
labels, and pred-pointers strictly decrease a rank, then `(d, pred)` is an exact shortest-path
tree output.  This is the endpoint the algorithm lanes should target. -/
theorem isSPTree_of_certificate {s : Fin G.n} {d : Fin G.n → ℝ≥0∞}
    {pred : Fin G.n → Option (Fin G.m)} (hs : d s = 0)
    (hrel : ∀ e, d (G.dst e) ≤ d (G.src e) + G.w e)
    (hdst : ∀ v e, pred v = some e → G.dst e = v)
    (htight : ∀ v e, pred v = some e → d v = d (G.src e) + G.w e)
    (hsrc : pred s = none)
    (hunr : ∀ v, d v = ⊤ → pred v = none)
    (hnone : ∀ v, v ≠ s → d v ≠ ⊤ → pred v ≠ none)
    {r : Fin G.n → ℕ} (hr : ∀ v e, pred v = some e → r (G.src e) < r v) :
    G.IsSPTree s d pred where
  exact := isSSSP_of_relaxed_of_realized hs hrel fun v hv => by
    obtain ⟨p, hp, hpe⟩ := realized_of_pred hs hdst htight hnone hr v hv
    exact ⟨p, hp, hpe.le⟩
  pred_dst := hdst
  pred_tight := htight
  pred_source := hsrc
  pred_unreachable := hunr
  pred_reachable := hnone
  acyclic := ⟨r, hr⟩

/-- An `IsSPTree` output yields, for every reachable vertex, a shortest walk. -/
theorem IsSPTree.exists_shortest_walk {s : Fin G.n} {d : Fin G.n → ℝ≥0∞}
    {pred : Fin G.n → Option (Fin G.m)} (h : G.IsSPTree s d pred) (v : Fin G.n)
    (hv : G.Reachable s v) :
    ∃ p, G.IsWalk s v p ∧ ((G.len p : ℝ≥0) : ℝ≥0∞) = G.dist s v := by
  obtain ⟨r, hr⟩ := h.acyclic
  have hs : d s = 0 := by rw [h.exact s, dist_self]
  have hdv : d v ≠ ⊤ := by rw [h.exact v]; exact dist_ne_top_iff.mpr hv
  obtain ⟨p, hp, hpe⟩ := realized_of_pred hs h.pred_dst h.pred_tight h.pred_reachable hr v hdv
  exact ⟨p, hp, hpe.trans (h.exact v)⟩


/-! ## Frontier framework (Duan–Mao–Shu–Yin 2026, §2.5) without unique shortest paths

The paper assumes a tie-breaking rule making shortest paths unique.  Here "the shortest path
of `v` visits `y`" is replaced by the existential `Visits s y v` (some shortest `s`–`v` walk
passes through `y`).  All of Observation 2.1, the framework step and Lemma 3.6 (frontier split)
remain true in this form; Observation 2.1(4) needs a slightly different argument than the
paper's (which uses uniqueness), see `IsFrontier.restrict`. -/

section FrontierFramework

variable (G) (s : Fin G.n)

/-- Some shortest `s`–`v` walk passes through `y`: `v` is reachable and some walk `q` from `y`
to `v` satisfies `dist s v = dist s y + len q`. -/
def Visits (y v : Fin G.n) : Prop :=
  G.dist s v ≠ ⊤ ∧ ∃ q, G.IsWalk y v q ∧ G.dist s v = G.dist s y + G.len q

/-- The target set `Ũ(B, S)`: vertices below the bound some shortest walk of which visits `S`. -/
def Utilde (B : ℝ≥0∞) (S : Set (Fin G.n)) : Set (Fin G.n) :=
  {v | G.dist s v < B ∧ ∃ y ∈ S, G.Visits s y v}

/-- `v` is complete for labels `d`. -/
def Complete (d : Fin G.n → ℝ≥0∞) (v : Fin G.n) : Prop := d v = G.dist s v

/-- Labels are sound: never below the true distance. -/
def Sound (d : Fin G.n → ℝ≥0∞) : Prop := ∀ v, G.dist s v ≤ d v

/-- `⟨X, Y⟩` is a frontier for `U` under labels `d`: every `v ∈ U` is in `X` and complete, or
some shortest walk to `v` visits a complete vertex of `Y`. -/
def IsFrontier (d : Fin G.n → ℝ≥0∞) (U X Y : Set (Fin G.n)) : Prop :=
  ∀ v ∈ U, (v ∈ X ∧ G.Complete s d v) ∨ ∃ y ∈ Y, G.Complete s d y ∧ G.Visits s y v

/-- The out-neighbours of a set `Z` validly relaxed from `Z` below `B` (the set `R(B, Z)`). -/
def Relaxed (d : Fin G.n → ℝ≥0∞) (B : ℝ≥0∞) (Z : Set (Fin G.n)) : Set (Fin G.n) :=
  {v | v ∉ Z ∧ ∃ e, G.src e ∈ Z ∧ G.dst e = v ∧ d v = d (G.src e) + G.w e ∧ d v < B}

/-- `d_B[Y] = min({B} ∪ {d y : y ∈ Y})`. -/
noncomputable def boundedMin (d : Fin G.n → ℝ≥0∞) (B : ℝ≥0∞) (Y : Set (Fin G.n)) : ℝ≥0∞ :=
  B ⊓ ⨅ y ∈ Y, d y

variable {G} {s}

theorem visits_self {v : Fin G.n} (hv : G.dist s v ≠ ⊤) : G.Visits s v v :=
  ⟨hv, [], IsWalk.nil v, by simp⟩

theorem Visits.dist_le {y v : Fin G.n} (h : G.Visits s y v) : G.dist s y ≤ G.dist s v := by
  obtain ⟨-, q, -, hq⟩ := h
  rw [hq]
  exact le_self_add

theorem Visits.dist_ne_top {y v : Fin G.n} (h : G.Visits s y v) : G.dist s y ≠ ⊤ :=
  ne_top_of_le_ne_top h.1 h.dist_le

/-- Optimal substructure: splitting a witness walk of `Visits` at an intermediate vertex. -/
theorem visits_split {y x v : Fin G.n} {q₁ q₂ : List (Fin G.m)}
    (h : G.dist s v = G.dist s y + G.len (q₁ ++ q₂))
    (h₁ : G.IsWalk y x q₁) (h₂ : G.IsWalk x v q₂) :
    G.dist s x = G.dist s y + G.len q₁ ∧ G.dist s v = G.dist s x + G.len q₂ := by
  have hx : G.dist s x ≤ G.dist s y + G.len q₁ := dist_le_dist_add_len h₁
  have hv' : G.dist s v ≤ G.dist s x + G.len q₂ := dist_le_dist_add_len h₂
  have hsum : G.dist s y + G.len (q₁ ++ q₂) = G.dist s y + G.len q₁ + G.len q₂ := by
    rw [len_append, ENNReal.coe_add, add_assoc]
  have h2 : G.dist s v = G.dist s x + G.len q₂ := by
    refine le_antisymm hv' ?_
    calc G.dist s x + G.len q₂ ≤ G.dist s y + G.len q₁ + G.len q₂ := add_le_add_left hx _
      _ = G.dist s v := by rw [h, hsum]
  refine ⟨?_, h2⟩
  have : G.dist s x + G.len q₂ = G.dist s y + G.len q₁ + G.len q₂ := by
    rw [← h2, h, hsum]
  exact (ENNReal.add_left_inj ENNReal.coe_ne_top).mp this

theorem Visits.trans {x y v : Fin G.n} (h₁ : G.Visits s x y) (h₂ : G.Visits s y v) :
    G.Visits s x v := by
  obtain ⟨-, q₁, hq₁, e₁⟩ := h₁
  obtain ⟨hv, q₂, hq₂, e₂⟩ := h₂
  refine ⟨hv, q₁ ++ q₂, hq₁.append hq₂, ?_⟩
  rw [e₂, e₁, len_append, ENNReal.coe_add, add_assoc]

/-- A walk leaving a set has a first exit edge. -/
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

theorem Complete.of_le {d d' : Fin G.n → ℝ≥0∞} {v : Fin G.n} (h : G.Complete s d v)
    (hsound : G.Sound s d') (hle : d' v ≤ d v) : G.Complete s d' v :=
  le_antisymm (hle.trans h.le) (hsound v)

/-- Observation 2.1(1): frontiers survive further (sound, monotone) relaxation. -/
theorem IsFrontier.of_le {d d' : Fin G.n → ℝ≥0∞} {U X Y : Set (Fin G.n)}
    (hF : G.IsFrontier s d U X Y) (hsound : G.Sound s d') (hle : ∀ v, d' v ≤ d v) :
    G.IsFrontier s d' U X Y := by
  intro v hv
  rcases hF v hv with ⟨hX, hc⟩ | ⟨y, hy, hc, hvis⟩
  · exact Or.inl ⟨hX, hc.of_le hsound (hle v)⟩
  · exact Or.inr ⟨y, hy, hc.of_le hsound (hle y), hvis⟩

theorem IsFrontier.mono {d : Fin G.n → ℝ≥0∞} {U U' X X' Y Y' : Set (Fin G.n)}
    (hF : G.IsFrontier s d U X Y) (hU : U' ⊆ U) (hX : X ⊆ X') (hY : Y ⊆ Y') :
    G.IsFrontier s d U' X' Y' := by
  intro v hv
  rcases hF v (hU hv) with ⟨hx, hc⟩ | ⟨y, hy, hc, hvis⟩
  · exact Or.inl ⟨hX hx, hc⟩
  · exact Or.inr ⟨y, hY hy, hc, hvis⟩

/-- Observation 2.1(3). -/
theorem utilde_subset {B : ℝ≥0∞} {S Y : Set (Fin G.n)} (hY : Y ⊆ G.Utilde s B S) :
    G.Utilde s B Y ⊆ G.Utilde s B S := by
  rintro v ⟨hvB, y, hy, hvis⟩
  obtain ⟨-, x, hx, hxy⟩ := hY hy
  exact ⟨hvB, x, hx, hxy.trans hvis⟩

theorem utilde_mono_bound {B B' : ℝ≥0∞} {S : Set (Fin G.n)} (h : B' ≤ B) :
    G.Utilde s B' S ⊆ G.Utilde s B S :=
  fun _ hv => ⟨lt_of_lt_of_le hv.1 h, hv.2⟩

theorem utilde_mono_set {B : ℝ≥0∞} {S S' : Set (Fin G.n)} (h : S ⊆ S') :
    G.Utilde s B S ⊆ G.Utilde s B S' := by
  rintro v ⟨hvB, y, hy, hvis⟩
  exact ⟨hvB, y, h hy, hvis⟩

/-- Observation 2.1(4), proved without unique shortest paths. -/
theorem IsFrontier.restrict {d : Fin G.n → ℝ≥0∞} {B : ℝ≥0∞} {S X Y : Set (Fin G.n)}
    (hF : G.IsFrontier s d (G.Utilde s B S) X Y) (hY : Y ⊆ G.Utilde s B S) :
    G.IsFrontier s d (G.Utilde s B Y) ∅ Y := by
  rintro v ⟨-, y, hy, hvis⟩
  by_cases hc : G.Complete s d y
  · exact Or.inr ⟨y, hy, hc, hvis⟩
  · rcases hF y (hY hy) with ⟨-, hc'⟩ | ⟨y', hy', hc', hvis'⟩
    · exact absurd hc' hc
    · exact Or.inr ⟨y', hy', hc', hvis'.trans hvis⟩

/-- Observation 2.1(2): on the frontier set, the bounded minimum label is exact. -/
theorem IsFrontier.boundedMin_eq {d : Fin G.n → ℝ≥0∞} {B : ℝ≥0∞} {S X Y : Set (Fin G.n)}
    (hF : G.IsFrontier s d (G.Utilde s B S) X Y) (hY : Y ⊆ G.Utilde s B S)
    (hsound : G.Sound s d) :
    G.boundedMin d B Y = G.boundedMin (G.dist s) B Y := by
  unfold boundedMin
  refine le_antisymm ?_ ?_
  · refine le_inf inf_le_left (le_iInf₂ fun y hy => ?_)
    by_cases hyB : B ≤ G.dist s y
    · exact inf_le_left.trans hyB
    · have hyU := hY hy
      rcases hF y hyU with ⟨-, hc⟩ | ⟨y', hy', hc', hvis⟩
      · exact inf_le_right.trans ((iInf₂_le y hy).trans hc.le)
      · exact inf_le_right.trans ((iInf₂_le y' hy').trans (hc'.le.trans hvis.dist_le))
  · exact inf_le_inf_left _ (iInf₂_mono fun y _ => hsound y)

/-- Observation 2.1(5): everything below `d_B[Y]` is already settled in `X`. -/
theorem IsFrontier.below_boundedMin {d : Fin G.n → ℝ≥0∞} {B : ℝ≥0∞} {S X Y : Set (Fin G.n)}
    (hF : G.IsFrontier s d (G.Utilde s B S) X Y) :
    ∀ v ∈ G.Utilde s (G.boundedMin d B Y) S, v ∈ X ∧ G.Complete s d v := by
  rintro v ⟨hvB, hvis⟩
  have hvU : v ∈ G.Utilde s B S := ⟨lt_of_lt_of_le hvB inf_le_left, hvis⟩
  rcases hF v hvU with h | ⟨y, hy, hc, hyv⟩
  · exact h
  · exfalso
    have h1 : G.dist s v < d y := lt_of_lt_of_le hvB (inf_le_right.trans (iInf₂_le y hy))
    rw [hc] at h1
    exact absurd hyv.dist_le (not_le.mpr h1)

/-- Dijkstra's selection rule inside the framework: a minimum-label vertex of `Y` below `B`
is complete. -/
theorem IsFrontier.complete_of_min {d : Fin G.n → ℝ≥0∞} {B : ℝ≥0∞} {S X Y : Set (Fin G.n)}
    (hF : G.IsFrontier s d (G.Utilde s B S) X Y) (hY : Y ⊆ G.Utilde s B S)
    (hsound : G.Sound s d) {y : Fin G.n} (hy : y ∈ Y) (hmin : ∀ y' ∈ Y, d y ≤ d y') :
    G.Complete s d y := by
  rcases hF y (hY hy) with ⟨-, hc⟩ | ⟨y', hy', hc', hvis⟩
  · exact hc
  · refine le_antisymm ?_ (hsound y)
    calc d y ≤ d y' := hmin y' hy'
      _ = G.dist s y' := hc'
      _ ≤ G.dist s y := hvis.dist_le

/-- **Framework step** (DMSY26 §2.5): after making `Z` complete and relaxing all edges out of
`Z` below `B`, `⟨X ∪ Z, (Y \ Z) ∪ R(B, Z)⟩` is again a frontier. -/
theorem IsFrontier.step {d d' : Fin G.n → ℝ≥0∞} {B : ℝ≥0∞} {U X Y Z : Set (Fin G.n)}
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
        have hdB : G.dist s (G.dst e) < B :=
          lt_of_le_of_lt (by rw [hvd]; exact le_self_add) (hU v hvU)
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

/-- **Frontier split** (DMSY26 Lemma 3.6). -/
theorem IsFrontier.split {d : Fin G.n → ℝ≥0∞} {B Bs : ℝ≥0∞} {S X Y Ys : Set (Fin G.n)}
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

/-- The initial frontier `⟨∅, {s}⟩` for `Ũ(⊤, {s})`, which is every reachable vertex. -/
theorem isFrontier_init {d : Fin G.n → ℝ≥0∞} (hs : d s = 0) :
    G.IsFrontier s d (G.Utilde s ⊤ {s}) ∅ {s} := by
  rintro v ⟨-, y, hy, hvis⟩
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact Or.inr ⟨y, rfl, by simp [Complete, hs], hvis⟩

theorem utilde_top_source : G.Utilde s ⊤ {s} = {v | G.Reachable s v} := by
  ext v
  simp only [Utilde, Set.mem_singleton_iff, exists_eq_left, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h, -⟩
    exact dist_lt_top_iff.mp h
  · intro h
    have hv : G.dist s v ≠ ⊤ := dist_ne_top_iff.mpr h
    refine ⟨lt_top_iff_ne_top.mpr hv, hv, ?_⟩
    obtain ⟨p, hp, hpe⟩ := exists_walk_eq_dist hv
    exact ⟨p, hp, by rw [dist_self, zero_add, hpe]⟩

/-- Termination of the framework: an empty frontier side means `U ⊆ X` is complete. -/
theorem IsFrontier.complete_of_empty {d : Fin G.n → ℝ≥0∞} {U X : Set (Fin G.n)}
    (hF : G.IsFrontier s d U X ∅) : ∀ v ∈ U, v ∈ X ∧ G.Complete s d v := by
  intro v hv
  rcases hF v hv with h | ⟨y, hy, -⟩
  · exact h
  · exact absurd hy (Set.notMem_empty y)

end FrontierFramework

end Graph

end Frontier
