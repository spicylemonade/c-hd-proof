import Frontier.CHD.FindPivots

/-! # (w, head)-order implies the core's `SortedRel` (agent-10, scratch) -/

open scoped NNReal ENNReal

namespace Frontier.CHD

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

theorem endV_snoc (p : List (Fin G.m)) (e : Fin G.m) : endV G s (p ++ [e]) = G.dst e := by
  unfold endV; simp

theorem key_le (q : List (Fin G.m)) {e e' : Fin G.m}
    (h : G.w e < G.w e' ∨ (G.w e = G.w e' ∧ G.dst e < G.dst e')) :
    (toW (q ++ [e]) : WalkOrd G s) ≤ toW (q ++ [e']) := by
  rw [le_iff_kap]
  unfold kap
  rw [Prod.Lex.toLex_le_toLex]
  simp only [Graph.len_append, Graph.len_cons, Graph.len_nil, add_zero]
  rcases h with hw | ⟨hw, hd⟩
  · left; exact (add_lt_add_iff_left _).mpr hw
  · right
    refine ⟨by rw [hw], ?_⟩
    rw [Prod.Lex.toLex_le_toLex]
    right
    refine ⟨by simp, ?_⟩
    rw [Prod.Lex.toLex_le_toLex]
    left
    rw [endV_snoc, endV_snoc]; exact hd

theorem sortedRel_of_key {e e' : Fin G.m}
    (h : G.w e < G.w e' ∨ (G.w e = G.w e' ∧ G.dst e < G.dst e')) : SortedRel G s e e' := by
  intro lab
  induction lab using WithTop.recTopCoe with
  | top => exact le_refl _
  | coe p => exact WithTop.coe_le_coe.mpr (key_le (s := s) p h)

end Frontier.CHD
