import Frontier.CHD.BMTrace
import Frontier.CHD.FPBind

/-!
# Frontier.CHD.FPForeign — foreign leaves in the cost chain (owner agent-03)

**NON-GATE** (Layer A, L5 glue).  The foreign-leaf counter of a call record is
`Fo X := tv_X \ U_X`, the FindPivots tree vertices outside the returned set (PAPER_CHD §5.2).
From agent-05's Lemma F2 (`fpC_foreign`), agent-01's traced log (`Log.ranges`) and the Density
lemma `level_foreign_sum_le` we get the `CostAggregate.Valid` field `foreign_level`; `full_p`
follows from the pivot bound of `fpC_spec`.

The per-record FindPivots facts `RecFP` (the record's FindPivots output comes from an `fpC` run
under `CallPre` at the record's `B, S`, the record's `U` is `Ũ(B', S)`, `B_low ≤ B`, base calls
have no groups) are the interface to the traced recursion (agent-01).
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD

open Frontier Graph Frontier.CHD.Partition

variable {G : Graph} {s : Fin G.n}

/-- The tree-vertex set of a FindPivots output. -/
def FPData.tvs (ω : FPData G s) : Finset (Fin G.n) := (ω.trees.flatMap (fun T => T.ord)).toFinset

/-- Foreign leaves of a call record: FindPivots tree vertices outside `U` (none for base calls). -/
def foOf (r : BM.CallRec G s (FPData G s)) : Finset (Fin G.n) :=
  match r.fp with
  | none => ∅
  | some ω => ω.tvs \ r.U

/-- Per-record FindPivots facts, for `FPC := fpC out k hins hext`. -/
structure RecFP (out : Fin G.n → List (Fin G.m)) (k hins hext : ℕ) (r : BM.CallRec G s (FPData G s)) :
    Prop where
  Blow_le : r.Blow ≤ r.B
  U_eq : ∀ v, v ∈ r.U ↔ v ∈ Utilde r.B' (r.S : Set (Fin G.n))
  low_S : ∀ x ∈ r.S, r.Blow ≤ dis (s := s) x
  none_p : r.fp = none → r.p = 0
  fp : ∀ ω, r.fp = some ω → ∃ d0 d1 Din Dout P c, CallPre r.B r.S d0 ∧ DelInv G s Din ∧
    fpC G s out k hins hext r.lvl r.Blow r.B r.S d0 Din d1 r.p P r.Q r.W Dout ω c

section

variable {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}

/-- **Foreign leaves of a full call lie in its handled range** `[B_low, B') = [B_low, B)`. -/
theorem foOf_range (hout : ∀ u e, e ∈ out u ↔ G.src e = u)
    (hsort : ∀ u, (out u).Pairwise (SortedRel G s)) {r : BM.CallRec G s (FPData G s)}
    (hr : RecFP out k hins hext r) (hfull : r.B' = r.B) :
    ∀ v ∈ foOf r, r.Blow ≤ dis (s := s) v ∧ dis (s := s) v < r.B' := by
  intro v hv
  unfold foOf at hv
  split at hv
  · exact absurd hv (Finset.notMem_empty v)
  · next ω hω =>
    obtain ⟨hvt, hvU⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨d0, d1, Din, Dout, P, c, hpre, -, hrel⟩ := hr.fp ω hω
    have hvU' : v ∉ Utilde r.B (r.S : Set (Fin G.n)) := by
      rw [← hfull]; exact fun h => hvU ((hr.U_eq v).mpr h)
    obtain ⟨hlow, hF2⟩ := fpC_foreign hout hsort hpre hrel
    obtain ⟨T, hT, hvT⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hvt)
    obtain ⟨h1, h2, -, -⟩ := hF2 T hT v hvT hvU'
    have hS : ∀ x ∈ r.S, r.Blow ≤ d0 x := fun x hx => (hr.low_S x hx).trans (hpre.walk.sound x)
    exact ⟨(hlow hr.Blow_le hS).trans h1, hfull ▸ h2⟩

variable {τ : ℕ → ℕ} {L0 : ℕ} {lg : BM.Log G s (FPData G s)}

/-- **`Valid.foreign_level`**: on every depth, the foreign leaves of full calls number at most `|V|`. -/
theorem counters_foreign_level (hout : ∀ u e, e ∈ out u ↔ G.src e = u)
    (hsort : ∀ u, (out u).Pairwise (SortedRel G s)) (hL : BM.LogInv τ L0 lg)
    (hrec : ∀ q r, (q, r) ∈ lg → RecFP out k hins hext r) (Cr Be Del : BM.CallRec G s (FPData G s) → Finset (Fin G.m))
    (j : ℕ) :
    ∑ X ∈ Finset.univ.filter (fun X => (BM.Log.counters hL foOf Cr Be Del).F.depth X = j ∧
        (BM.Log.counters hL foOf Cr Be Del).full X = true),
      ((BM.Log.counters hL foOf Cr Be Del).Fo X).card ≤ Fintype.card (Fin G.n) := by
  classical
  have key := (BM.Log.ranges hL).level_foreign_sum_le
    (fun X => (BM.Log.counters hL foOf Cr Be Del).full X = true)
    (fun X => (BM.Log.counters hL foOf Cr Be Del).Fo X) (fun v => dis (s := s) v) ?_ j
  · convert key using 2
    rfl
  · intro X hX v hv
    have hfull : (lg.recOf X).B' = (lg.recOf X).B := of_decide_eq_true hX
    exact foOf_range hout hsort (hrec _ _ (BM.recOf_mem X)) hfull v hv

/-- **`Valid.full_p`** from the pivot bound `p (k-1) ≤ #tree vertices` and a duplicate-free forest. -/
theorem counters_full_p (hout : ∀ u e, e ∈ out u ↔ G.src e = u)
    (hsort : ∀ u, (out u).Pairwise (SortedRel G s)) (hsimp : ∀ u, ((out u).map G.dst).Nodup)
    (hk : 2 ≤ k) (hL : BM.LogInv τ L0 lg)
    (hrec : ∀ q r, (q, r) ∈ lg → RecFP out k hins hext r)
    (hnd : ∀ q r, (q, r) ∈ lg → ∀ ω, r.fp = some ω → (ω.trees.flatMap (fun T => T.ord)).Nodup)
    (Cr Be Del : BM.CallRec G s (FPData G s) → Finset (Fin G.m)) :
    ∀ X, (BM.Log.counters hL foOf Cr Be Del).full X = true →
      (BM.Log.counters hL foOf Cr Be Del).p X * (k - 1) ≤
        ((BM.Log.counters hL foOf Cr Be Del).F.U X).card + ((BM.Log.counters hL foOf Cr Be Del).Fo X).card := by
  intro X _
  have hr := hrec _ _ (BM.recOf_mem X)
  show (lg.recOf X).p * (k - 1) ≤ (lg.recOf X).U.card + (foOf (lg.recOf X)).card
  cases hω : (lg.recOf X).fp with
  | none => rw [hr.none_p hω]; simp
  | some ω =>
    obtain ⟨d0, d1, Din, Dout, P, c, hpre, hI, hrel⟩ := hr.fp ω hω
    obtain ⟨-, -, -, hpiv, -⟩ := fpC_spec hout hsort hsimp hk hpre hI hrel
    have hlen : (ω.trees.flatMap (fun T => T.ord)).length = ω.tvs.card :=
      (List.toFinset_card_of_nodup (hnd _ _ (BM.recOf_mem X) ω hω)).symm
    have hsplit : ω.tvs.card ≤ (lg.recOf X).U.card + (ω.tvs \ (lg.recOf X).U).card := by
      have := Finset.card_le_card_sdiff_add_card (s := ω.tvs) (t := (lg.recOf X).U)
      omega
    have hfo : foOf (lg.recOf X) = ω.tvs \ (lg.recOf X).U := by unfold foOf; rw [hω]
    rw [hfo]
    omega

/-- **`Valid.partial_Fo`**: a partial call has at most `|U|` foreign leaves, from `#tv ≤ k|S|`, `k ≤ t` and
`t|S| ≤ |U|` (`Valid.partial_S`). -/
theorem counters_partial_Fo (hout : ∀ u e, e ∈ out u ↔ G.src e = u)
    (hsort : ∀ u, (out u).Pairwise (SortedRel G s)) (hk : 1 ≤ k) {t : ℕ} (hkt : k ≤ t)
    (hL : BM.LogInv τ L0 lg) (hrec : ∀ q r, (q, r) ∈ lg → RecFP out k hins hext r)
    (Cr Be Del : BM.CallRec G s (FPData G s) → Finset (Fin G.m))
    (hpS : ∀ X, (BM.Log.counters hL foOf Cr Be Del).full X = false →
      t * ((BM.Log.counters hL foOf Cr Be Del).S X).card ≤ ((BM.Log.counters hL foOf Cr Be Del).F.U X).card) :
    ∀ X, (BM.Log.counters hL foOf Cr Be Del).full X = false →
      ((BM.Log.counters hL foOf Cr Be Del).Fo X).card ≤ ((BM.Log.counters hL foOf Cr Be Del).F.U X).card := by
  intro X hX
  have hS := hpS X hX
  have hr := hrec _ _ (BM.recOf_mem X)
  show (foOf (lg.recOf X)).card ≤ (lg.recOf X).U.card
  change t * (lg.recOf X).S.card ≤ (lg.recOf X).U.card at hS
  cases hω : (lg.recOf X).fp with
  | none => simp [foOf, hω]
  | some ω =>
    obtain ⟨d0, d1, Din, Dout, P, c, hpre, -, hrel⟩ := hr.fp ω hω
    have htv := fpC_tv_card hout hsort hk hpre hrel
    have hfo : foOf (lg.recOf X) = ω.tvs \ (lg.recOf X).U := by unfold foOf; rw [hω]
    rw [hfo]
    have h1 : (ω.tvs \ (lg.recOf X).U).card ≤ ω.tvs.card := Finset.card_le_card Finset.sdiff_subset
    have h2 : ω.tvs.card ≤ (ω.trees.flatMap (fun T => T.ord)).length := List.toFinset_card_le _
    have h3 : k * (lg.recOf X).S.card ≤ t * (lg.recOf X).S.card := Nat.mul_le_mul_right _ hkt
    omega

end

end CHD
end Frontier
