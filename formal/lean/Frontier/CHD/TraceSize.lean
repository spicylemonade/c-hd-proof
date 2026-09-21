import Frontier.CHD.QWit
import Frontier.CHD.CrBe

/-!
# Frontier.CHD.TraceSize — subtree sums for the trace-size lemma (B4') (tracker O12; owner agent-03)

**NON-GATE** (Layer A, combinatorial part).  For a call `X` of a `LogInv` log:
* `sub_events_le`: the inserting-capable events (`evOf`) of the records in the subtree of `X` are pairwise disjoint
  (G2) and have tails in `U_X`, so their number is at most the number of edges out of `U_X`;
* `sub_U_le`: records of one depth in the subtree have disjoint `U ⊆ U_X`, so `Σ |U_Z| ≤ (#depths) · |U_X|`.
With `|S_Z| ≤ |U_Z|` these bound `Σ_{Z ⊆ X} (2|S_Z| + #events(Z))`, the entries ever placed into the structure
of `X` once each structure's own placements are bounded by `2|S_Z| + #events(Z)` (BMLazy side).
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n} {Ω : Type}

section Pre

variable {lg : Log G s Ω}

/-- The records of the subtree of `x`. -/
def subLog (lg : Log G s Ω) (x : List ℕ) : Log G s Ω := lg.filter (fun qr => decide (x <+: qr.1))

theorem mem_subLog {x : List ℕ} {qr : List ℕ × CallRec G s Ω} : qr ∈ subLog lg x ↔ qr ∈ lg ∧ x <+: qr.1 := by
  unfold subLog
  simp

/-- Splitting a list sum by a bounded key. -/
theorem sum_split {β : Type*} (f : β → ℕ) (k : β → ℕ) (K : ℕ) :
    ∀ L : List β, (∀ a ∈ L, k a < K) →
      (L.map f).sum = ∑ j ∈ Finset.range K, ((L.filter (fun a => decide (k a = j))).map f).sum
  | [], _ => by simp
  | a :: L, hk => by
    have ih := sum_split f k K L (fun b hb => hk b (List.mem_cons_of_mem _ hb))
    have hka := hk a List.mem_cons_self
    simp only [List.map_cons, List.sum_cons, List.filter_cons]
    rw [ih]
    have e : ∀ j, ((if decide (k a = j) = true then a :: L.filter (fun a => decide (k a = j))
        else L.filter (fun a => decide (k a = j))).map f).sum =
        (if k a = j then f a else 0) + ((L.filter (fun a => decide (k a = j))).map f).sum := by
      intro j
      by_cases h : k a = j <;> simp [h]
    rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_eq (Finset.range K) (k a) (fun _ => f a)]
    simp [hka]

/-- The out-edges of a vertex set. -/
def Eout (G : Graph) (U : Finset (Fin G.n)) : Finset (Fin G.m) := Finset.univ.filter (fun e => G.src e ∈ U)

/-- The own-placement weight of a record (agent-01's `ownB` with `p ≤ |S|` applied). -/
def wB (r : CallRec G s Ω) : ℕ :=
  if r.base = true then r.S.card + (Eout G r.U).card else 3 * r.S.card + r.J.card + r.Wr.card

/-- Sums of cards of pairwise disjoint subsets of `T` are at most `|T|`. -/
theorem sum_disjoint_le {β : Type*} [DecidableEq β] (L : List (List ℕ × CallRec G s Ω))
    (E : List ℕ × CallRec G s Ω → Finset β) (T : Finset β)
    (hdisj : L.Pairwise (fun a b => Disjoint (E a) (E b))) (hsub : ∀ a ∈ L, E a ⊆ T) :
    (L.map (fun a => (E a).card)).sum ≤ T.card := by
  rw [← card_foldr_union L E hdisj]
  refine Finset.card_le_card (fun x hx => ?_)
  obtain ⟨a, ha, hxa⟩ := mem_foldr_union.mp hx
  exact hsub a ha hxa

end Pre

section Sub

variable {τ : ℕ → ℕ} {L0 : ℕ} {lg : Log G s Ω} (hL : LogInv τ L0 lg)
include hL

/-- **Events of a subtree**: at most the edges out of `U_X`. -/
theorem sub_events_le {x : List ℕ} {rx : CallRec G s Ω} (hx : (x, rx) ∈ lg) :
    ((subLog lg x).map (fun qr => (evOf qr.2).card)).sum ≤
      (Finset.univ.filter (fun e : Fin G.m => G.src e ∈ rx.U)).card := by
  classical
  have hnd : ((subLog lg x).map Prod.fst).Nodup :=
    (hL.nodup.sublist (List.Sublist.map _ List.filter_sublist))
  have hdisj : (subLog lg x).Pairwise (fun a b => Disjoint (evOf a.2) (evOf b.2)) := by
    have hpw : (subLog lg x).Pairwise (fun a b => a.1 ≠ b.1) := List.pairwise_map.mp hnd
    refine hpw.imp_of_mem (fun {a b} ha hb hne => ?_)
    rw [Finset.disjoint_left]
    intro e hea heb
    exact hne (ev_unique hL (mem_subLog.mp ha).1 (mem_subLog.mp hb).1 hea heb)
  refine sum_disjoint_le (subLog lg x) (fun qr => evOf qr.2) _ hdisj (fun qr hqr e heq => ?_)
  obtain ⟨hmem, hpre⟩ := mem_subLog.mp hqr
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases ev_kind hL hmem heq with ⟨-, -, a, r', hr', hu, -, -⟩ | ⟨hu, -, -, -⟩
  · obtain ⟨r0, hr0, hU, -⟩ := prefix_rec' hL hr' (q0 := x) (hpre.trans (List.prefix_append _ _))
    have := rec_unique hL.nodup hr0 hx
    subst this
    exact hU hu
  · obtain ⟨r0, hr0, hU, -⟩ := prefix_rec' hL hmem (q0 := x) hpre
    have := rec_unique hL.nodup hr0 hx
    subst this
    exact hU hu

/-- Records of one depth have disjoint `U`. -/
theorem same_len_disjoint {q q' : List ℕ} {r r' : CallRec G s Ω} (h : (q, r) ∈ lg) (h' : (q', r') ∈ lg)
    (hlen : q.length = q'.length) (hne : q ≠ q') : Disjoint r.U r'.U := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  rcases prefix_chain hL h h' hv hv' with hp | hp
  · exact hne (hp.eq_of_length hlen)
  · exact hne (hp.eq_of_length hlen.symm).symm

/-- **One depth of a subtree**: `Σ |U_Z| ≤ |U_X|`. -/
theorem sub_U_level_le {x : List ℕ} {rx : CallRec G s Ω} (hx : (x, rx) ∈ lg) (j : ℕ) :
    (((subLog lg x).filter (fun qr => decide (qr.1.length = j))).map (fun qr => qr.2.U.card)).sum ≤
      rx.U.card := by
  classical
  have hnd : (((subLog lg x).filter (fun qr => decide (qr.1.length = j))).map Prod.fst).Nodup :=
    hL.nodup.sublist (List.Sublist.map _ (List.filter_sublist.trans List.filter_sublist))
  have hdisj : ((subLog lg x).filter (fun qr => decide (qr.1.length = j))).Pairwise
      (fun a b => Disjoint a.2.U b.2.U) := by
    have hpw := List.pairwise_map.mp hnd
    refine hpw.imp_of_mem (fun {a b} ha hb hne => ?_)
    obtain ⟨ha1, ha2⟩ := List.mem_filter.mp ha
    obtain ⟨hb1, hb2⟩ := List.mem_filter.mp hb
    exact same_len_disjoint hL (mem_subLog.mp ha1).1 (mem_subLog.mp hb1).1
      (by simp only [decide_eq_true_eq] at ha2 hb2; rw [ha2, hb2]) hne
  refine sum_disjoint_le _ (fun qr => qr.2.U) _ hdisj (fun qr hqr v hv' => ?_)
  obtain ⟨hmem, hpre⟩ := mem_subLog.mp (List.mem_filter.mp hqr).1
  obtain ⟨r0, hr0, hU, -⟩ := prefix_rec' hL hmem (q0 := x) hpre
  have := rec_unique hL.nodup hr0 hx
  subst this
  exact hU hv'

/-- **The whole subtree**: `Σ |U_Z| ≤ (L0 + 1) · |U_X|` (depths are at most `L0`). -/
theorem sub_U_le {x : List ℕ} {rx : CallRec G s Ω} (hx : (x, rx) ∈ lg) :
    ((subLog lg x).map (fun qr => qr.2.U.card)).sum ≤ (L0 + 1) * rx.U.card := by
  have hk : ∀ qr ∈ subLog lg x, qr.1.length < L0 + 1 := by
    intro qr hqr
    have := hL.depth qr.1 qr.2 (mem_subLog.mp hqr).1
    omega
  rw [sum_split _ (fun qr => qr.1.length) (L0 + 1) _ hk]
  calc ∑ j ∈ Finset.range (L0 + 1),
        (((subLog lg x).filter (fun a => decide (a.1.length = j))).map (fun qr => qr.2.U.card)).sum
      ≤ ∑ j ∈ Finset.range (L0 + 1), rx.U.card := Finset.sum_le_sum (fun j _ => sub_U_level_le hL hx j)
    _ = (L0 + 1) * rx.U.card := by simp

/-- `W'` relaxation lists of distinct records are disjoint (their sources are owned). -/
theorem wr_disjoint {q1 q2 : List ℕ} {r1 r2 : CallRec G s Ω} (h1 : (q1, r1) ∈ lg) (h2 : (q2, r2) ∈ lg)
    (hne : q1 ≠ q2) : Disjoint r1.Wr r2.Wr := by
  rw [Finset.disjoint_left]
  intro e he1 he2
  obtain ⟨hu1, hown1⟩ := hL.wr q1 r1 h1 e he1
  obtain ⟨hu2, hown2⟩ := hL.wr q2 r2 h2 e he2
  rcases prefix_chain hL h1 h2 hu1 hu2 with hp | hp
  · exact own_not_above hL h1 h2 hown1 hu2 hp hne
  · exact own_not_above hL h2 h1 hown2 hu1 hp (fun h => hne h.symm)

/-- Base records have pairwise disjoint `U` (a base call has no sub-calls). -/
theorem base_disjoint {q1 q2 : List ℕ} {r1 r2 : CallRec G s Ω} (h1 : (q1, r1) ∈ lg) (h2 : (q2, r2) ∈ lg)
    (hb1 : r1.base = true) (hb2 : r2.base = true) (hne : q1 ≠ q2) : Disjoint r1.U r2.U := by
  rw [Finset.disjoint_left]
  intro v hv1 hv2
  have key : ∀ {qa qb : List ℕ} {ra rb : CallRec G s Ω}, (qa, ra) ∈ lg → (qb, rb) ∈ lg → ra.base = true →
      qa <+: qb → qa ≠ qb → False := by
    intro qa qb ra rb ha hb hba hp hne'
    obtain ⟨t, rfl⟩ := hp
    have ht : t ≠ [] := fun ht => hne' (by simp [ht])
    obtain ⟨a, t', rfl⟩ := List.exists_cons_of_ne_nil ht
    obtain ⟨r', hr', -, -⟩ := prefix_rec' hL hb (q0 := qa ++ [a]) ⟨t', by simp⟩
    exact hL.base qa ra ha hba a r' hr'
  rcases prefix_chain hL h1 h2 hv1 hv2 with hp | hp
  · exact key h1 h2 hb1 hp hne
  · exact key h2 h1 hb2 hp (fun h => hne h.symm)

/-- **Trace-size sum** (the combinatorial core of (B4')): for a log with root `([], r0)`, `|S| ≤ |U|` on every
record and out-degrees at most `δ`, the own-placement weights sum to at most `(3(L0+1) + 3δ)·|U_root|`. -/
theorem wB_sum_le (δ : ℕ) (hdeg : ∀ u, (Eout G {u}).card ≤ δ)
    (hSU : ∀ q r, (q, r) ∈ lg → r.S.card ≤ r.U.card) {r0 : CallRec G s Ω} (h0 : ([], r0) ∈ lg) :
    (lg.map (fun qr => wB qr.2)).sum ≤ (3 * (L0 + 1) + 3 * δ) * r0.U.card := by
  classical
  have hsubAll : subLog lg [] = lg := by
    unfold subLog; exact List.filter_eq_self.mpr (fun qr _ => by simp)
  have hnd : lg.Pairwise (fun a b => a.1 ≠ b.1) := List.pairwise_map.mp hL.nodup
  have hUsub : ∀ qr ∈ lg, qr.2.U ⊆ r0.U := by
    intro qr hqr
    obtain ⟨r1, hr1, hU, -⟩ := prefix_rec' hL hqr (q0 := []) List.nil_prefix
    have := rec_unique hL.nodup hr1 h0
    subst this
    exact hU
  -- the out-edges of `U_root`
  have hE : (Eout G r0.U).card ≤ δ * r0.U.card := by
    have : Eout G r0.U = r0.U.biUnion (fun u => Eout G {u}) := by
      ext e; simp [Eout]
    rw [this]
    calc _ ≤ ∑ u ∈ r0.U, (Eout G {u}).card := Finset.card_biUnion_le
      _ ≤ ∑ u ∈ r0.U, δ := Finset.sum_le_sum (fun u _ => hdeg u)
      _ = δ * r0.U.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  -- (1) frontiers
  have hS : (lg.map (fun qr => qr.2.S.card)).sum ≤ (L0 + 1) * r0.U.card := by
    have h1 := sub_U_le hL h0
    rw [hsubAll] at h1
    exact le_trans (Reselect.map_sum_le _ _ _ (fun qr hqr => hSU qr.1 qr.2 hqr)) h1
  -- (2) jumps of recursive records
  have hJ : (lg.map (fun qr => if qr.2.base = true then 0 else qr.2.J.card)).sum ≤ (Eout G r0.U).card := by
    have h2 := sub_events_le hL h0
    rw [hsubAll] at h2
    refine le_trans (Reselect.map_sum_le _ _ _ (fun qr hqr => ?_)) h2
    split_ifs with hb
    · exact Nat.zero_le _
    · refine Finset.card_le_card (fun e he => ?_)
      unfold evOf
      rw [if_neg hb]
      exact Finset.mem_union_left _ he
  -- (3) `W'` relaxations
  have hW : (lg.map (fun qr => qr.2.Wr.card)).sum ≤ (Eout G r0.U).card := by
    refine sum_disjoint_le lg (fun qr => qr.2.Wr) _ (hnd.imp_of_mem (fun {a b} ha hb hne => ?_))
      (fun qr hqr e he => ?_)
    · exact wr_disjoint hL ha hb hne
    · simp only [Eout, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hUsub qr hqr (hL.wr qr.1 qr.2 hqr e he).1
  -- (4) out-edges of base calls
  have hB : (lg.map (fun qr => if qr.2.base = true then (Eout G qr.2.U).card else 0)).sum ≤
      (Eout G r0.U).card := by
    have e1 : (lg.map (fun qr => if qr.2.base = true then (Eout G qr.2.U).card else 0)) =
        (lg.map (fun qr => (if qr.2.base = true then Eout G qr.2.U else ∅).card)) := by
      refine List.map_congr_left (fun qr _ => ?_)
      split_ifs <;> simp
    rw [e1]
    refine sum_disjoint_le lg (fun qr => if qr.2.base = true then Eout G qr.2.U else ∅) _
      (hnd.imp_of_mem (fun {a b} ha hb hne => ?_)) (fun qr hqr e he => ?_)
    · by_cases hba : a.2.base = true
      · by_cases hbb : b.2.base = true
        · simp only [hba, hbb, if_true]
          rw [Finset.disjoint_left]
          intro e hea heb
          simp only [Eout, Finset.mem_filter, Finset.mem_univ, true_and] at hea heb
          exact Finset.disjoint_left.mp (base_disjoint hL ha hb hba hbb hne) hea heb
        · simp [hbb]
      · simp [hba]
    · split_ifs at he with hb
      · simp only [Eout, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
        exact hUsub qr hqr he
      · simp at he
  -- assemble
  have hpt : ∀ qr ∈ lg, wB qr.2 ≤ 3 * qr.2.S.card + (if qr.2.base = true then 0 else qr.2.J.card) +
      qr.2.Wr.card + (if qr.2.base = true then (Eout G qr.2.U).card else 0) := by
    intro qr _
    unfold wB
    split_ifs <;> omega
  have hsum := Reselect.map_sum_le _ _ _ hpt
  rw [List.sum_map_add, List.sum_map_add, List.sum_map_add, List.sum_map_mul_left] at hsum
  have : (3 * (L0 + 1) + 3 * δ) * r0.U.card = 3 * ((L0 + 1) * r0.U.card) + 3 * (δ * r0.U.card) := by ring
  omega

end Sub

end BM
end CHD
end Frontier
