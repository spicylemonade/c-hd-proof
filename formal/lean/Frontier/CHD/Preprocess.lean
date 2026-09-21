import Frontier.Spec

/-!
# Frontier.CHD.Preprocess — distance preservation of the C-HD preprocessing (owner: agent-10)

NON-GATE.  Mathematical (Spec-level) facts only.  Any concrete preprocessing routine whose output
satisfies one of the relational specifications below may be used by C-HD; the distance equality is
proved once, here.

* `Simplification G`: drop self-loops, keep (at least) one minimum-weight copy of every parallel
  class.  Distances are unchanged (`Simplification.dist_eq`).
* `DegRed G`: DMSY26 Sec. 2.1 degree reduction — every vertex becomes a strongly connected
  zero-weight gadget (a cycle), every original edge becomes one edge between the gadgets of its
  endpoints.  Distances from any gadget vertex of `s` to any gadget vertex of `v` equal
  `dist_G(s, v)` (`DegRed.dist_eq`).
-/

open scoped ENNReal NNReal

namespace Frontier

namespace Graph

variable {G : Graph}

/-- Generic transfer: an endpoint-preserving, length-nonincreasing map of walks gives a distance
inequality. -/
theorem dist_le_of_walk_transfer {H : Graph} (f : Fin H.n → Fin G.n) {x y : Fin H.n}
    (T : ∀ q : List (Fin H.m), H.IsWalk x y q →
      ∃ p : List (Fin G.m), G.IsWalk (f x) (f y) p ∧ G.len p ≤ H.len q) :
    G.dist (f x) (f y) ≤ H.dist x y := by
  refine le_iInf₂ fun q hq => ?_
  obtain ⟨p, hp, hle⟩ := T q hq
  exact (dist_le_len hp).trans (ENNReal.coe_le_coe.mpr hle)

end Graph

namespace CHD

/-! ## Simplification -/

/-- A simplification of `G`: a graph on the same vertex set whose edges are copies of edges of `G`
and which contains, for every non-loop edge of `G`, a parallel copy of no larger weight. -/
structure Simplification (G : Graph) where
  m' : ℕ
  src' : Fin m' → Fin G.n
  dst' : Fin m' → Fin G.n
  w' : Fin m' → ℝ≥0
  /-- every new edge is dominated by (is a copy of) an old edge -/
  sound : ∀ f : Fin m', ∃ e : Fin G.m, G.src e = src' f ∧ G.dst e = dst' f ∧ G.w e ≤ w' f
  /-- every old non-loop edge has a parallel new edge of no larger weight -/
  complete : ∀ e : Fin G.m, G.src e ≠ G.dst e →
    ∃ f : Fin m', src' f = G.src e ∧ dst' f = G.dst e ∧ w' f ≤ G.w e

namespace Simplification

variable {G : Graph} (S : Simplification G)

/-- The simplified graph. -/
def toGraph : Graph := ⟨G.n, S.m', S.src', S.dst', S.w'⟩

/-- Walks of the simplification map to walks of `G` of no larger length. -/
theorem walk_down {u v : Fin S.toGraph.n} {q : List (Fin S.toGraph.m)} (hq : S.toGraph.IsWalk u v q) :
    ∃ p : List (Fin G.m), G.IsWalk u v p ∧ G.len p ≤ S.toGraph.len q := by
  induction hq with
  | nil u => exact ⟨[], Graph.IsWalk.nil (G := G) u, by simp⟩
  | @cons f v q _ ih =>
    obtain ⟨p, hp, hle⟩ := ih
    obtain ⟨e, hs, hd, hw⟩ := S.sound f
    refine ⟨e :: p, ?_, ?_⟩
    · have hp' : G.IsWalk (G.dst e) v p := by
        rw [hd]; exact hp
      have := Graph.IsWalk.cons hp'
      rw [hs] at this
      exact this
    · simp only [Graph.len_cons]
      exact add_le_add hw hle

/-- Walks of `G` map to walks of the simplification of no larger length (self-loops are cut). -/
theorem walk_up {u v : Fin G.n} {p : List (Fin G.m)} (hp : G.IsWalk u v p) :
    ∃ q : List (Fin S.toGraph.m), S.toGraph.IsWalk u v q ∧ S.toGraph.len q ≤ G.len p := by
  induction hp with
  | nil u => exact ⟨[], Graph.IsWalk.nil (G := S.toGraph) u, by simp⟩
  | @cons e v p _ ih =>
    obtain ⟨q, hq, hle⟩ := ih
    by_cases hloop : G.src e = G.dst e
    · refine ⟨q, ?_, ?_⟩
      · rw [hloop]; exact hq
      · simp only [Graph.len_cons]
        exact hle.trans (le_add_self)
    · obtain ⟨f, hs, hd, hw⟩ := S.complete e hloop
      refine ⟨f :: q, ?_, ?_⟩
      · have hq' : S.toGraph.IsWalk (S.toGraph.dst f) v q := by
          show S.toGraph.IsWalk (S.dst' f) v q
          rw [hd]; exact hq
        have := Graph.IsWalk.cons hq'
        have hsrc : S.toGraph.src f = G.src e := hs
        rw [hsrc] at this
        exact this
      · simp only [Graph.len_cons]
        exact add_le_add hw hle

/-- **Simplification preserves distances.** -/
theorem dist_eq (s v : Fin G.n) : S.toGraph.dist s v = G.dist s v := by
  apply le_antisymm
  · refine le_iInf₂ fun p hp => ?_
    obtain ⟨q, hq, hle⟩ := S.walk_up hp
    exact (Graph.dist_le_len hq).trans (ENNReal.coe_le_coe.mpr hle)
  · refine le_iInf₂ fun q hq => ?_
    obtain ⟨p, hp, hle⟩ := S.walk_down hq
    exact (Graph.dist_le_len hp).trans (ENNReal.coe_le_coe.mpr hle)

end Simplification

/-! ## Degree reduction -/

/-- A degree reduction of `G` (DMSY26 Sec. 2.1): gadget vertices `Fin N` projecting onto `G`'s
vertices, each original edge realized by one gadget edge between the right gadgets, every other
gadget edge a zero-weight edge inside one gadget, and every gadget strongly connected by
zero-length walks.  (Degree bounds are separate facts used only by the cost analysis.) -/
structure DegRed (G : Graph) where
  N : ℕ
  M : ℕ
  src : Fin M → Fin N
  dst : Fin M → Fin N
  w : Fin M → ℝ≥0
  proj : Fin N → Fin G.n
  rep : Fin G.n → Fin N
  proj_rep : ∀ v, proj (rep v) = v
  orig : Fin G.m → Fin M
  orig_src : ∀ e, proj (src (orig e)) = G.src e
  orig_dst : ∀ e, proj (dst (orig e)) = G.dst e
  orig_w : ∀ e, w (orig e) = G.w e
  /-- every gadget edge is an original edge or a zero-weight intra-gadget edge -/
  classify : ∀ f : Fin M, (∃ e, orig e = f) ∨ (proj (src f) = proj (dst f) ∧ w f = 0)
  /-- gadgets are strongly connected by zero-length walks -/
  fiber_conn : ∀ x y : Fin N, proj x = proj y →
    ∃ q : List (Fin M), (Graph.IsWalk ⟨N, M, src, dst, w⟩ x y q) ∧
      Graph.len ⟨N, M, src, dst, w⟩ q = 0

namespace DegRed

variable {G : Graph} (R : DegRed G)

/-- The reduced graph. -/
def toGraph : Graph := ⟨R.N, R.M, R.src, R.dst, R.w⟩

theorem fiber_conn' (x y : Fin R.toGraph.n) (h : R.proj x = R.proj y) :
    ∃ q : List (Fin R.toGraph.m), R.toGraph.IsWalk x y q ∧ R.toGraph.len q = 0 :=
  R.fiber_conn x y h

/-- Projection of reduced walks: original edges map to themselves, gadget edges disappear. -/
theorem walk_down {x y : Fin R.toGraph.n} {q : List (Fin R.toGraph.m)} (hq : R.toGraph.IsWalk x y q) :
    ∃ p : List (Fin G.m), G.IsWalk (R.proj x) (R.proj y) p ∧ G.len p ≤ R.toGraph.len q := by
  induction hq with
  | nil x => exact ⟨[], Graph.IsWalk.nil _, by simp⟩
  | @cons f y q _ ih =>
    obtain ⟨p, hp, hle⟩ := ih
    rcases R.classify f with ⟨e, he⟩ | ⟨hfib, hw0⟩
    · refine ⟨e :: p, ?_, ?_⟩
      · have hd : G.dst e = R.proj (R.toGraph.dst f) := by
          rw [← he, ← R.orig_dst e]; rfl
        have hs : G.src e = R.proj (R.toGraph.src f) := by
          rw [← he, ← R.orig_src e]; rfl
        have hp' : G.IsWalk (G.dst e) (R.proj y) p := by rw [hd]; exact hp
        have := Graph.IsWalk.cons hp'
        rw [hs] at this
        exact this
      · simp only [Graph.len_cons]
        have hwe : G.w e = R.toGraph.w f := by rw [← he, ← R.orig_w e]; rfl
        rw [hwe]
        exact add_le_add le_rfl hle
    · refine ⟨p, ?_, ?_⟩
      · have : R.proj (R.toGraph.src f) = R.proj (R.toGraph.dst f) := hfib
        rw [this]; exact hp
      · simp only [Graph.len_cons]
        exact hle.trans le_add_self

/-- Lifting: an original walk from `u` to `v` lifts to a reduced walk of the same length between
ANY gadget vertices of `u` and `v`. -/
theorem walk_up {u v : Fin G.n} {p : List (Fin G.m)} (hp : G.IsWalk u v p) :
    ∀ a b : Fin R.toGraph.n, R.proj a = u → R.proj b = v →
      ∃ q : List (Fin R.toGraph.m), R.toGraph.IsWalk a b q ∧ R.toGraph.len q = G.len p := by
  induction hp with
  | nil u =>
    intro a b ha hb
    obtain ⟨q, hq, hl⟩ := R.fiber_conn' a b (ha.trans hb.symm)
    exact ⟨q, hq, hl⟩
  | @cons e v p _ ih =>
    intro a b ha hb
    -- a ⇝ src (orig e) inside the gadget of `src e`
    obtain ⟨q₁, hq₁, hl₁⟩ := R.fiber_conn' a (R.src (R.orig e)) (ha.trans (R.orig_src e).symm)
    -- dst (orig e) ⇝ b by induction
    obtain ⟨q₂, hq₂, hl₂⟩ := ih (R.dst (R.orig e)) b (R.orig_dst e) hb
    let f : Fin R.toGraph.m := R.orig e
    refine ⟨q₁ ++ (f :: q₂), ?_, ?_⟩
    · exact hq₁.append (Graph.IsWalk.cons hq₂)
    · have hl₁' : R.toGraph.len q₁ = 0 := hl₁
      have hw : R.toGraph.w f = G.w e := R.orig_w e
      calc R.toGraph.len (q₁ ++ (f :: q₂))
          = R.toGraph.len q₁ + (R.toGraph.w f + R.toGraph.len q₂) := by
            rw [Graph.len_append, Graph.len_cons]
        _ = G.len (e :: p) := by rw [hl₁', hw, hl₂, zero_add, Graph.len_cons]

/-- **Degree reduction preserves distances**: from any gadget vertex of `s` to any gadget vertex
`x`, the reduced distance equals the original distance to `proj x`. -/
theorem dist_eq (s : Fin G.n) (a x : Fin R.toGraph.n) (ha : R.proj a = s) :
    R.toGraph.dist a x = G.dist s (R.proj x) := by
  apply le_antisymm
  · refine le_iInf₂ fun p hp => ?_
    obtain ⟨q, hq, hl⟩ := R.walk_up hp a x ha rfl
    exact (Graph.dist_le_len hq).trans (le_of_eq (by rw [hl]))
  · have h := Graph.dist_le_of_walk_transfer (G := G) (H := R.toGraph) R.proj (x := a) (y := x)
      (fun q hq => R.walk_down hq)
    rw [ha] at h
    exact h

/-- The representative form used by the driver. -/
theorem dist_rep (s v : Fin G.n) : R.toGraph.dist (R.rep s) (R.rep v) = G.dist s v := by
  rw [R.dist_eq s (R.rep s) (R.rep v) (R.proj_rep s), R.proj_rep v]

end DegRed

/-! ## Out-degree chunking (zero-weight chains) -/

/-- An out-degree reduction of `G` by chains: every vertex `v` becomes a chain of gadget vertices
reachable from its head `rep v` by zero-length walks; every original edge `e` becomes one gadget
edge from some gadget vertex of `src e` INTO THE HEAD `rep (dst e)`; all other gadget edges are
zero-weight intra-gadget edges.  (Out-degree bounds and sortedness are separate cost facts.) -/
structure ChainRed (G : Graph) where
  N : ℕ
  M : ℕ
  src : Fin M → Fin N
  dst : Fin M → Fin N
  w : Fin M → ℝ≥0
  proj : Fin N → Fin G.n
  rep : Fin G.n → Fin N
  proj_rep : ∀ v, proj (rep v) = v
  orig : Fin G.m → Fin M
  orig_src : ∀ e, proj (src (orig e)) = G.src e
  orig_dst : ∀ e, dst (orig e) = rep (G.dst e)
  orig_w : ∀ e, w (orig e) = G.w e
  classify : ∀ f : Fin M, (∃ e, orig e = f) ∨ (proj (src f) = proj (dst f) ∧ w f = 0)
  head_conn : ∀ x : Fin N, ∃ q : List (Fin M),
    (Graph.IsWalk ⟨N, M, src, dst, w⟩ (rep (proj x)) x q) ∧ Graph.len ⟨N, M, src, dst, w⟩ q = 0

namespace ChainRed

variable {G : Graph} (R : ChainRed G)

/-- The reduced graph. -/
def toGraph : Graph := ⟨R.N, R.M, R.src, R.dst, R.w⟩

theorem head_conn' (x : Fin R.toGraph.n) :
    ∃ q : List (Fin R.toGraph.m), R.toGraph.IsWalk (R.rep (R.proj x)) x q ∧ R.toGraph.len q = 0 :=
  R.head_conn x

/-- Projection of reduced walks (as for `DegRed`). -/
theorem walk_down {x y : Fin R.toGraph.n} {q : List (Fin R.toGraph.m)} (hq : R.toGraph.IsWalk x y q) :
    ∃ p : List (Fin G.m), G.IsWalk (R.proj x) (R.proj y) p ∧ G.len p ≤ R.toGraph.len q := by
  induction hq with
  | nil x => exact ⟨[], Graph.IsWalk.nil _, by simp⟩
  | @cons f y q _ ih =>
    obtain ⟨p, hp, hle⟩ := ih
    rcases R.classify f with ⟨e, he⟩ | ⟨hfib, hw0⟩
    · refine ⟨e :: p, ?_, ?_⟩
      · have hd : G.dst e = R.proj (R.toGraph.dst f) := by
          rw [← he]
          show G.dst e = R.proj (R.dst (R.orig e))
          rw [R.orig_dst e, R.proj_rep]
        have hs : G.src e = R.proj (R.toGraph.src f) := by
          rw [← he, ← R.orig_src e]; rfl
        have hp' : G.IsWalk (G.dst e) (R.proj y) p := by rw [hd]; exact hp
        have := Graph.IsWalk.cons hp'
        rw [hs] at this
        exact this
      · simp only [Graph.len_cons]
        have hwe : G.w e = R.toGraph.w f := by rw [← he, ← R.orig_w e]; rfl
        rw [hwe]
        exact add_le_add le_rfl hle
    · refine ⟨p, ?_, ?_⟩
      · have : R.proj (R.toGraph.src f) = R.proj (R.toGraph.dst f) := hfib
        rw [this]; exact hp
      · simp only [Graph.len_cons]
        exact hle.trans le_add_self

/-- Lifting from heads: an original walk from `u` to `v` lifts to a reduced walk of the same
length from the head `rep u` to ANY gadget vertex of `v`. -/
theorem walk_up {u v : Fin G.n} {p : List (Fin G.m)} (hp : G.IsWalk u v p) :
    ∀ b : Fin R.toGraph.n, R.proj b = v →
      ∃ q : List (Fin R.toGraph.m), R.toGraph.IsWalk (R.rep u) b q ∧ R.toGraph.len q = G.len p := by
  induction hp with
  | nil u =>
    intro b hb
    obtain ⟨q, hq, hl⟩ := R.head_conn' b
    rw [hb] at hq
    exact ⟨q, hq, by simpa using hl⟩
  | @cons e v p _ ih =>
    intro b hb
    obtain ⟨q₁, hq₁, hl₁⟩ := R.head_conn' (R.src (R.orig e))
    have hsrc : R.proj (R.src (R.orig e)) = G.src e := R.orig_src e
    rw [hsrc] at hq₁
    obtain ⟨q₂, hq₂, hl₂⟩ := ih b hb
    let f : Fin R.toGraph.m := R.orig e
    refine ⟨q₁ ++ (f :: q₂), ?_, ?_⟩
    · have hd : R.toGraph.dst f = R.rep (G.dst e) := R.orig_dst e
      have hq₂' : R.toGraph.IsWalk (R.toGraph.dst f) b q₂ := by rw [hd]; exact hq₂
      exact hq₁.append (Graph.IsWalk.cons hq₂')
    · have hw : R.toGraph.w f = G.w e := R.orig_w e
      calc R.toGraph.len (q₁ ++ (f :: q₂))
          = R.toGraph.len q₁ + (R.toGraph.w f + R.toGraph.len q₂) := by
            rw [Graph.len_append, Graph.len_cons]
        _ = G.len (e :: p) := by rw [hl₁, hw, hl₂, zero_add, Graph.len_cons]

/-- **Chain reduction preserves distances from the source head.** -/
theorem dist_eq (s : Fin G.n) (x : Fin R.toGraph.n) :
    R.toGraph.dist (R.rep s) x = G.dist s (R.proj x) := by
  apply le_antisymm
  · refine le_iInf₂ fun p hp => ?_
    obtain ⟨q, hq, hl⟩ := R.walk_up hp x rfl
    exact (Graph.dist_le_len hq).trans (le_of_eq (by rw [hl]))
  · have h := Graph.dist_le_of_walk_transfer (G := G) (H := R.toGraph) R.proj
      (x := R.rep s) (y := x) (fun q hq => R.walk_down hq)
    rw [R.proj_rep] at h
    exact h

theorem dist_rep (s v : Fin G.n) : R.toGraph.dist (R.rep s) (R.rep v) = G.dist s v := by
  rw [R.dist_eq s (R.rep v), R.proj_rep v]

end ChainRed

/-! ## The combined reduction spec used by L6 (existential form) -/

/-- `H` is a reduction of `G` (dedup + out-degree chunking in one): gadget vertices `proj`/`rep`;
every non-loop edge of `G` has a copy of no larger weight from its tail's gadget into the head
gadget's HEAD `rep`; every edge of `H` is either a copy (into a head) of an edge of `G` of no smaller
weight, or an intra-gadget edge (any weight); every gadget vertex is reachable from its head by a
zero-length walk.  Self-loops and heavier parallel edges of `G` may be dropped. -/
structure Reduction (G H : Graph) where
  proj : Fin H.n → Fin G.n
  rep : Fin G.n → Fin H.n
  proj_rep : ∀ v, proj (rep v) = v
  copy_of : ∀ e : Fin G.m, G.src e ≠ G.dst e →
    ∃ f : Fin H.m, proj (H.src f) = G.src e ∧ H.dst f = rep (G.dst e) ∧ H.w f ≤ G.w e
  classify : ∀ f : Fin H.m,
    (∃ e : Fin G.m, proj (H.src f) = G.src e ∧ H.dst f = rep (G.dst e) ∧ G.w e ≤ H.w f) ∨
      proj (H.src f) = proj (H.dst f)
  head_conn : ∀ x : Fin H.n, ∃ q : List (Fin H.m), H.IsWalk (rep (proj x)) x q ∧ H.len q = 0

namespace Reduction

variable {G H : Graph} (R : Reduction G H)

theorem walk_down {x y : Fin H.n} {q : List (Fin H.m)} (hq : H.IsWalk x y q) :
    ∃ p : List (Fin G.m), G.IsWalk (R.proj x) (R.proj y) p ∧ G.len p ≤ H.len q := by
  induction hq with
  | nil x => exact ⟨[], Graph.IsWalk.nil _, by simp⟩
  | @cons f y q _ ih =>
    obtain ⟨p, hp, hle⟩ := ih
    rcases R.classify f with ⟨e, hs, hd, hw⟩ | hfib
    · refine ⟨e :: p, ?_, ?_⟩
      · have hd' : G.dst e = R.proj (H.dst f) := by rw [hd, R.proj_rep]
        have hp' : G.IsWalk (G.dst e) (R.proj y) p := by rw [hd']; exact hp
        have := Graph.IsWalk.cons hp'
        rw [← hs] at this
        exact this
      · simp only [Graph.len_cons]
        exact add_le_add hw hle
    · refine ⟨p, ?_, ?_⟩
      · rw [hfib]; exact hp
      · simp only [Graph.len_cons]
        exact hle.trans le_add_self

theorem walk_up {u v : Fin G.n} {p : List (Fin G.m)} (hp : G.IsWalk u v p) :
    ∀ b : Fin H.n, R.proj b = v →
      ∃ q : List (Fin H.m), H.IsWalk (R.rep u) b q ∧ H.len q ≤ G.len p := by
  induction hp with
  | nil u =>
    intro b hb
    obtain ⟨q, hq, hl⟩ := R.head_conn b
    rw [hb] at hq
    exact ⟨q, hq, by rw [hl]; simp⟩
  | @cons e v p _ ih =>
    intro b hb
    by_cases hloop : G.src e = G.dst e
    · obtain ⟨q, hq, hl⟩ := ih b hb
      refine ⟨q, ?_, ?_⟩
      · rw [hloop]; exact hq
      · simp only [Graph.len_cons]; exact hl.trans le_add_self
    · obtain ⟨f, hs, hd, hw⟩ := R.copy_of e hloop
      obtain ⟨q₁, hq₁, hl₁⟩ := R.head_conn (H.src f)
      rw [hs] at hq₁
      obtain ⟨q₂, hq₂, hl₂⟩ := ih b hb
      refine ⟨q₁ ++ (f :: q₂), ?_, ?_⟩
      · have hq₂' : H.IsWalk (H.dst f) b q₂ := by rw [hd]; exact hq₂
        exact hq₁.append (Graph.IsWalk.cons hq₂')
      · rw [Graph.len_append, Graph.len_cons, hl₁, zero_add, Graph.len_cons]
        exact add_le_add hw hl₂

/-- **A reduction preserves distances from the source head.** -/
theorem dist_eq (s : Fin G.n) (x : Fin H.n) : H.dist (R.rep s) x = G.dist s (R.proj x) := by
  apply le_antisymm
  · refine le_iInf₂ fun p hp => ?_
    obtain ⟨q, hq, hl⟩ := R.walk_up hp x rfl
    exact (Graph.dist_le_len hq).trans (ENNReal.coe_le_coe.mpr hl)
  · have h := Graph.dist_le_of_walk_transfer (G := G) (H := H) R.proj
      (x := R.rep s) (y := x) (fun q hq => R.walk_down hq)
    rw [R.proj_rep] at h
    exact h

theorem dist_rep (s v : Fin G.n) : H.dist (R.rep s) (R.rep v) = G.dist s v := by
  rw [R.dist_eq s (R.rep v), R.proj_rep v]

end Reduction

/-! ## Reduction with a keep set (L6 v2: vertices without non-loop in-edges are dropped) -/

/-- `H` is a keep-set reduction of `G` from source `s`: the kept vertices contain `s` and are
closed under non-loop edges (so every vertex reachable from `s` is kept); every kept vertex has a
gadget in `H` with head `rep v`; non-loop edges with kept tails have copies of no larger weight
into the head gadget's head; every `H`-edge is a copy (into a head) of a non-loop `G`-edge of no
smaller weight or an intra-gadget edge; gadgets are reachable from their heads at zero cost. -/
structure KReduction (G H : Graph) (s : Fin G.n) where
  keep : Fin G.n → Prop
  keep_s : keep s
  keep_dst : ∀ e : Fin G.m, G.src e ≠ G.dst e → keep (G.dst e)
  proj : Fin H.n → Fin G.n
  rep : Fin G.n → Fin H.n
  proj_rep : ∀ v, keep v → proj (rep v) = v
  proj_keep : ∀ x, keep (proj x)
  copy_of : ∀ e : Fin G.m, G.src e ≠ G.dst e → keep (G.src e) →
    ∃ f : Fin H.m, proj (H.src f) = G.src e ∧ H.dst f = rep (G.dst e) ∧ H.w f ≤ G.w e
  classify : ∀ f : Fin H.m,
    (∃ e : Fin G.m, G.src e ≠ G.dst e ∧ proj (H.src f) = G.src e ∧ H.dst f = rep (G.dst e) ∧
      G.w e ≤ H.w f) ∨ proj (H.src f) = proj (H.dst f)
  head_conn : ∀ x : Fin H.n, ∃ q : List (Fin H.m), H.IsWalk (rep (proj x)) x q ∧ H.len q = 0

namespace KReduction

variable {G H : Graph} {s : Fin G.n} (R : KReduction G H s)

/-- Walks from kept vertices end at kept vertices. -/
theorem walk_keep {u v : Fin G.n} {p : List (Fin G.m)} (hp : G.IsWalk u v p) (hu : R.keep u) :
    R.keep v := by
  induction hp with
  | nil u => exact hu
  | @cons e v p _ ih =>
    apply ih
    by_cases hl : G.src e = G.dst e
    · rw [← hl]; exact hu
    · exact R.keep_dst e hl

theorem walk_down {x y : Fin H.n} {q : List (Fin H.m)} (hq : H.IsWalk x y q) :
    ∃ p : List (Fin G.m), G.IsWalk (R.proj x) (R.proj y) p ∧ G.len p ≤ H.len q := by
  induction hq with
  | nil x => exact ⟨[], Graph.IsWalk.nil _, by simp⟩
  | @cons f y q _ ih =>
    obtain ⟨p, hp, hle⟩ := ih
    rcases R.classify f with ⟨e, hne, hs, hd, hw⟩ | hfib
    · refine ⟨e :: p, ?_, ?_⟩
      · have hd' : G.dst e = R.proj (H.dst f) := by rw [hd, R.proj_rep _ (R.keep_dst e hne)]
        have hp' : G.IsWalk (G.dst e) (R.proj y) p := by rw [hd']; exact hp
        have := Graph.IsWalk.cons hp'
        rw [← hs] at this
        exact this
      · simp only [Graph.len_cons]
        exact add_le_add hw hle
    · refine ⟨p, ?_, ?_⟩
      · rw [hfib]; exact hp
      · simp only [Graph.len_cons]
        exact hle.trans le_add_self

theorem walk_up {u v : Fin G.n} {p : List (Fin G.m)} (hp : G.IsWalk u v p) (hu : R.keep u) :
    ∀ b : Fin H.n, R.proj b = v →
      ∃ q : List (Fin H.m), H.IsWalk (R.rep u) b q ∧ H.len q ≤ G.len p := by
  induction hp with
  | nil u =>
    intro b hb
    obtain ⟨q, hq, hl⟩ := R.head_conn b
    rw [hb] at hq
    exact ⟨q, hq, by rw [hl]; simp⟩
  | @cons e v p hp' ih =>
    intro b hb
    by_cases hloop : G.src e = G.dst e
    · obtain ⟨q, hq, hl⟩ := ih (by rw [← hloop]; exact hu) b hb
      refine ⟨q, ?_, ?_⟩
      · rw [hloop]; exact hq
      · simp only [Graph.len_cons]; exact hl.trans le_add_self
    · obtain ⟨f, hs, hd, hw⟩ := R.copy_of e hloop hu
      obtain ⟨q₁, hq₁, hl₁⟩ := R.head_conn (H.src f)
      rw [hs] at hq₁
      obtain ⟨q₂, hq₂, hl₂⟩ := ih (R.keep_dst e hloop) b hb
      refine ⟨q₁ ++ (f :: q₂), ?_, ?_⟩
      · have hq₂' : H.IsWalk (H.dst f) b q₂ := by rw [hd]; exact hq₂
        exact hq₁.append (Graph.IsWalk.cons hq₂')
      · rw [Graph.len_append, Graph.len_cons, hl₁, zero_add, Graph.len_cons]
        exact add_le_add hw hl₂

/-- **Distances from the source head** (every `H`-vertex, projected). -/
theorem dist_eq (x : Fin H.n) : H.dist (R.rep s) x = G.dist s (R.proj x) := by
  apply le_antisymm
  · refine le_iInf₂ fun p hp => ?_
    obtain ⟨q, hq, hl⟩ := R.walk_up hp R.keep_s x rfl
    exact (Graph.dist_le_len hq).trans (ENNReal.coe_le_coe.mpr hl)
  · have h := Graph.dist_le_of_walk_transfer (G := G) (H := H) R.proj
      (x := R.rep s) (y := x) (fun q hq => R.walk_down hq)
    rw [R.proj_rep _ R.keep_s] at h
    exact h

theorem dist_rep {v : Fin G.n} (hv : R.keep v) : H.dist (R.rep s) (R.rep v) = G.dist s v := by
  rw [R.dist_eq (R.rep v), R.proj_rep v hv]

/-- Dropped vertices are unreachable. -/
theorem dist_top {v : Fin G.n} (hv : ¬ R.keep v) : G.dist s v = ⊤ := by
  rw [Graph.dist_eq_top_iff]
  rintro ⟨p, hp⟩
  exact hv (R.walk_keep hp R.keep_s)

end KReduction

end CHD

end Frontier

#print axioms Frontier.CHD.Simplification.dist_eq
#print axioms Frontier.CHD.DegRed.dist_eq
#print axioms Frontier.CHD.DegRed.dist_rep
#print axioms Frontier.CHD.ChainRed.dist_eq
#print axioms Frontier.CHD.ChainRed.dist_rep
#print axioms Frontier.CHD.Reduction.dist_rep
#print axioms Frontier.CHD.KReduction.dist_eq
#print axioms Frontier.CHD.KReduction.dist_top
