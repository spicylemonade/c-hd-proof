import Frontier.CHD.FindPivots

/-!
# Frontier.CHD.FPTailCost — the invocation's cost index pays for the FindPivots tail (owner agent-03)

**NON-GATE** (Layer A).  The tail (compaction, PT, bitmaps; `TreeRAM9.fpTail_spec`) costs
`188·Σ|T| + 8|S| + 8|Q| + 30`.  Layer A's invocation cost index already dominates this:
* `Invoke.tv_len_le`: `|tv'| + |L| ≤ |tv| + n` (every root costs `≥ 1`, every search `≥ |K| + 2`);
* `Invoke.Q_card_le`: `|Q'| ≤ |Q| + |L|`;
* `FInv.sum_len`: the forest has exactly `|tv|` vertices (disjoint duplicate-free orders);
* `tail_le_invoke`: from the empty invocation state, `188·Σ|T| + 8|L| + 8|Q| + 30 ≤ 188·n + 30`.
-/

namespace Frontier
namespace CHD

open Frontier Graph Frontier.CHD.Partition

variable {G : Graph} {s : Fin G.n}

theorem Invoke.tv_len_le {c : FPCtx G s} {ι ι' : IState G s} {L : List (Fin G.n)} {n : ℕ}
    (h : Invoke c ι L ι' n) : ι'.tv.card + L.length ≤ ι.tv.card + n := by
  classical
  induction h with
  | nil => simp
  | skip ι ι' x L n _ _ ih => simp only [List.length_cons]; omega
  | fail ι ι' x L σ' n n' _ _ _ ih =>
    dsimp only at ih
    simp only [List.length_cons]; omega
  | grow ι ι' x L σ' res n n' _ _ hs _ ih =>
    dsimp only at ih
    have hU : (ι.tv ∪ σ'.K.toFinset).card ≤ ι.tv.card + σ'.K.length :=
      (Finset.card_union_le _ _).trans (by have := List.toFinset_card_le σ'.K; omega)
    simp only [List.length_cons]; omega

theorem Invoke.Q_card_le {c : FPCtx G s} {ι ι' : IState G s} {L : List (Fin G.n)} {n : ℕ}
    (h : Invoke c ι L ι' n) : ι'.Q.card ≤ ι.Q.card + L.length := by
  classical
  induction h with
  | nil => simp
  | skip ι ι' x L n _ _ ih => simp only [List.length_cons]; omega
  | fail ι ι' x L σ' n n' _ _ _ ih =>
    dsimp only at ih
    have := Finset.card_insert_le x ι.Q
    simp only [List.length_cons]; omega
  | grow ι ι' x L σ' res n n' _ _ hs _ ih =>
    dsimp only at ih
    simp only [List.length_cons]; omega

/-- The forest of an invocation has exactly `|tv|` vertices. -/
theorem FInv.sum_len {c : FPCtx G s} {ι : IState G s} (hF : FInv c ι) :
    (ι.trees.map (fun T => T.ord.length)).sum = ι.tv.card := by
  classical
  have hnd : (ι.trees.flatMap (fun T => T.ord)).Nodup :=
    List.nodup_flatMap.mpr ⟨fun T hT => (hF.pf T hT).1, hF.disj.imp (fun h w hwa hwb => h w hwa hwb)⟩
  have hts : (ι.trees.flatMap (fun T => T.ord)).toFinset = ι.tv := by
    ext v
    rw [List.mem_toFinset, List.mem_flatMap, hF.tv v]
  rw [← hts, List.toFinset_card_of_nodup hnd, List.length_flatMap]

/-- **The tail is paid by the invocation's cost index.** -/
theorem tail_le_invoke {c : FPCtx G s} {d0 : Labels G s} {Din : Finset (Fin G.m)} {L : List (Fin G.n)}
    {ι' : IState G s} {n : ℕ} (h : Invoke c ⟨d0, Din, ∅, ∅, ∅, []⟩ L ι' n) (hF : FInv c ι') :
    188 * (ι'.trees.map (fun T => T.ord.length)).sum + 8 * L.length + 8 * ι'.Q.card + 30 ≤ 188 * n + 30 := by
  have h1 := h.tv_len_le
  have h2 := h.Q_card_le
  rw [hF.sum_len]
  simp only [Finset.card_empty] at h1 h2
  omega

end CHD
end Frontier
