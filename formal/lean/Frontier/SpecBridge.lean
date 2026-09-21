import Frontier.Spec
import Frontier.SpecGen

/-!
# Frontier.SpecBridge — relating `Frontier.Spec` and `Frontier.SpecGen`

Owner: agent-08.

* `Graph.toW G : WGraph ℝ≥0` and `dist_toW : (G.toW).dist s v = G.dist s v`: the generic
  distance at `ℝ≥0` is the contract distance.
* `Graph.lexW G : WGraph (ℝ≥0 ×ₗ ℕ)` with weights `toLex (w e, 1)`; every lexicographic edge
  weight is strictly positive (`toLex_w_pos`), lengths are `toLex (len p, p.length)`
  (`len_toLex`), and the first component of the lexicographic distance is the true distance
  (`dist_toLex_fst`).  So an algorithm proved exact for `(length, hops)` labels on `G.lexW`
  is exact for the labeled real distances of `G`.
-/

open scoped ENNReal NNReal

namespace Frontier

open Gen

namespace Graph

variable (G : Graph)

/-- The graph as a generic `ℝ≥0`-weighted graph. -/
abbrev toW : WGraph ℝ≥0 := ⟨G.n, G.m, G.src, G.dst, G.w, fun _ => zero_le⟩

/-- The graph with lexicographic `(length, hops)` weights. -/
abbrev lexW : WGraph (ℝ≥0 ×ₗ ℕ) :=
  ⟨G.n, G.m, G.src, G.dst, fun e => toLex (G.w e, 1), fun e => by
    rw [← toLex_zero, Prod.Lex.toLex_le_toLex]
    rcases (zero_le : (0 : ℝ≥0) ≤ G.w e).lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨by simpa using h, Nat.zero_le 1⟩⟩

variable {G}

theorem isWalk_toW_iff : ∀ {u v : Fin G.n} {p : List (Fin G.m)},
    G.toW.IsWalk u v p ↔ G.IsWalk u v p
  | u, v, [] => by rw [WGraph.isWalk_nil_iff, Graph.isWalk_nil_iff]
  | u, v, e :: p => by
    rw [WGraph.isWalk_cons_iff, Graph.isWalk_cons_iff]
    exact and_congr Iff.rfl isWalk_toW_iff

theorem isWalk_toLex_iff : ∀ {u v : Fin G.n} {p : List (Fin G.m)},
    G.lexW.IsWalk u v p ↔ G.IsWalk u v p
  | u, v, [] => by rw [WGraph.isWalk_nil_iff, Graph.isWalk_nil_iff]
  | u, v, e :: p => by
    rw [WGraph.isWalk_cons_iff, Graph.isWalk_cons_iff]
    exact and_congr Iff.rfl isWalk_toLex_iff

theorem len_toW (p : List (Fin G.m)) : G.toW.len p = G.len p := rfl

theorem len_toLex (p : List (Fin G.m)) : G.lexW.len p = toLex (G.len p, p.length) := by
  induction p with
  | nil => rw [WGraph.len_nil, Graph.len_nil, List.length_nil]; rfl
  | cons e p ih =>
    rw [WGraph.len_cons, ih, Graph.len_cons, List.length_cons]
    show toLex (G.w e, 1) + toLex (G.len p, p.length) = _
    rw [← toLex_add]
    simp only [Prod.mk_add_mk]
    congr 1
    rw [Nat.add_comm]

theorem toLex_w_pos (e : Fin G.m) : 0 < G.lexW.w e := by
  show (0 : ℝ≥0 ×ₗ ℕ) < toLex (G.w e, 1)
  rw [← toLex_zero, Prod.Lex.toLex_lt_toLex]
  rcases (zero_le : (0 : ℝ≥0) ≤ G.w e).lt_or_eq with h | h
  · exact Or.inl h
  · exact Or.inr ⟨by simpa using h, Nat.zero_lt_one⟩

/-- The generic distance at `ℝ≥0` is the contract distance. -/
theorem dist_toW (s v : Fin G.n) : (G.toW.dist s v : WithTop ℝ≥0) = G.dist s v := by
  refine WGraph.dist_eq_of_spec (fun p hp => ?_) (fun h => ?_) (fun h hr => ?_)
  · exact G.dist_le_len (isWalk_toW_iff.mp hp)
  · obtain ⟨p, hp, hpe⟩ := G.exists_walk_eq_dist h
    exact ⟨p, isWalk_toW_iff.mpr hp, hpe⟩
  · obtain ⟨p, hp⟩ := hr
    exact (dist_eq_top_iff.mp h) ⟨p, isWalk_toW_iff.mp hp⟩

/-- First components of lexicographic distances are the true distances. -/
theorem dist_toLex_fst (s v : Fin G.n) :
    WithTop.map (fun x : ℝ≥0 ×ₗ ℕ => (ofLex x).1) (G.lexW.dist s v) = G.dist s v := by
  by_cases hr : G.Reachable s v
  · have hr' : G.lexW.Reachable s v := by
      obtain ⟨p, hp⟩ := hr; exact ⟨p, isWalk_toLex_iff.mpr hp⟩
    obtain ⟨p, hp, hpe, -⟩ := WGraph.exists_shortest_path hr'
    rw [← hpe, WithTop.map_coe, len_toLex]
    simp only [ofLex_toLex]
    refine le_antisymm ?_ (G.dist_le_len (isWalk_toLex_iff.mp hp))
    obtain ⟨q, hq, hqe⟩ := G.exists_walk_eq_dist (dist_ne_top_iff.mpr hr)
    rw [← hqe]
    have hle : (G.lexW.dist s v) ≤ G.lexW.len q := WGraph.dist_le_len (isWalk_toLex_iff.mpr hq)
    rw [← hpe, WithTop.coe_le_coe, len_toLex, len_toLex, Prod.Lex.toLex_le_toLex] at hle
    rcases hle with h | ⟨h, -⟩
    · exact ENNReal.coe_le_coe.mpr h.le
    · exact ENNReal.coe_le_coe.mpr h.le
  · have h1 : G.lexW.dist s v = ⊤ := WGraph.dist_eq_top_iff.mpr (fun ⟨p, hp⟩ =>
      hr ⟨p, isWalk_toLex_iff.mp hp⟩)
    rw [h1, (dist_eq_top_iff).mpr hr]
    rfl

end Graph

end Frontier
