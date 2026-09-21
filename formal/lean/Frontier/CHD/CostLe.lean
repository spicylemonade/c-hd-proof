import Frontier.CHD.CostLog
import Frontier.CHD.RecFPLog
import Frontier.CHD.FPWQ
import Frontier.CHD.FPDel

/-!
# Frontier.CHD.CostLe — `CostAggregate.Valid.cost_le` for the traced run (tracker O10; owner agent-03)

**NON-GATE** (Layer A).  Assembles the per-call inequality from the per-record cost facts (`CostLog.RecCost`,
from `callC_cost`), the markings bound of PAPER 5.3(i) (`CrBe.mkOf_full_le`), the foreign-leaf counts
(`FPForeign`) and the parameter facts.

Child sums: `childSumAt (chgOf …) X.1 lg = Σ_{children Y} (C0 + C1 |U_Y| + C2 · #groups meeting U_Y)`;
`Σ_Y #groups meeting U_Y = mkOf X` (swap of the double sum).
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

section Swap

variable {τ : ℕ → ℕ} {L0 : ℕ} {lg : Log G s (FPData G s)} (hL : LogInv τ L0 lg)

/-- **Swapping the double sum**: groups meeting children, counted per child or per group. -/
theorem sum_children_countP (k : ℕ) (X : lg.Call) :
    ∑ Y ∈ Finset.univ.filter (fun Y => Log.parentOf hL Y = some X),
        (groupsOf k (lg.recOf X)).countP (fun g => decide (g.toFinset ∩ (lg.recOf Y).U).Nonempty) =
      mkOf hL k X := by
  classical
  unfold mkOf
  generalize groupsOf k (lg.recOf X) = L
  induction L with
  | nil => simp
  | cons g L ih =>
    simp only [List.countP_cons, List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib, ih, Nat.add_comm]
    congr 1
    rw [Finset.sum_boole, Finset.filter_filter, Nat.cast_id]
    congr 1
    ext Y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
    exact Iff.rfl

end Swap

section Arith

/-- **The per-call arithmetic** of `Valid.cost_le`: the budget of `callC_cost` is at most a constant times the
`Valid.cost_le` right-hand side `R`, from the per-term facts (all counts are plain naturals here).
`pS = [partial]·|S|`. -/
theorem budget_arith {Del A tv k Q S nw p I cs J cm W W' Wr ad bd U Fo t Cr Be mk nch C0 C1 C2 a cI cn c9 pS : ℕ}
    (htv : tv ≤ U + Fo + k * pS) (hA : A ≤ a * (k + 1))
    (hW : W ≤ k * Q) (hW' : W' ≤ U)
    (hcs : cs ≤ C0 * nch + C1 * U + C2 * mk) (hmk : mk ≤ p + Cr + Be + pS)
    (hnch : C0 * nch ≤ c9 * (U + t * (p + Q) + t * (p + Cr + Be)))
    (hS1 : 1 ≤ S) (hpQ : 1 ≤ p + Q) (hkk : k * (k + 1) ≤ 2 * t) (h3k : 3 * k ≤ t) (hk1 : 1 ≤ k)
    (hI : I ≤ cI * t) (hnw : nw ≤ cn * t) (hC2 : C2 ≤ 6 * k + 1 + I) :
    scanC * Del + A * (tv + k * Q) + 3 * S + (nw + S + p * (2 + I)) + (1 + 3 * k * p + cs + (1 + I) * J)
      + cm + (1 + S + pS * I + W + W' + Wr * (1 + I) + (ad * W' + bd) + S)
      ≤ (scanC + 5 * a + cn + 5 * c9 + C1 + 7 * cI + ad + bd + 30) *
        ((k + 1) * (U + Fo) + S + t * Q + t * (J + Wr + Cr + Be) + t * p + t * pS + cm + Del) := by
  set R := (k + 1) * (U + Fo) + S + t * Q + t * (J + Wr + Cr + Be) + t * p + t * pS + cm + Del with hR
  have ht1 : 1 ≤ t := by omega
  have eJ4 : t * (J + Wr + Cr + Be) = t * J + t * Wr + t * (Cr + Be) := by ring
  have rS : S ≤ R := by rw [hR]; omega
  have rkUF : (k + 1) * (U + Fo) ≤ R := by rw [hR]; omega
  have rU : U ≤ R := by
    have : U ≤ (k + 1) * (U + Fo) := by
      calc U ≤ U + Fo := by omega
        _ ≤ (k + 1) * (U + Fo) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have rtQ : t * Q ≤ R := by rw [hR]; omega
  have rtp : t * p ≤ R := by rw [hR]; omega
  have rtpS : t * pS ≤ R := by rw [hR]; omega
  have rtJ : t * J ≤ R := by rw [hR]; omega
  have rtWr : t * Wr ≤ R := by rw [hR]; omega
  have rtCB : t * (Cr + Be) ≤ R := by rw [hR]; omega
  have rcm : cm ≤ R := by rw [hR]; omega
  have rDel : Del ≤ R := by rw [hR]; omega
  have r1 : 1 ≤ R := le_trans hS1 rS
  have le_t : ∀ x, x ≤ t * x := fun x => Nat.le_mul_of_pos_left _ (by omega)
  have rp : p ≤ R := le_trans (le_t p) rtp
  have rJ : J ≤ R := le_trans (le_t J) rtJ
  have rWr : Wr ≤ R := le_trans (le_t Wr) rtWr
  -- (2) A·tv and A·kQ
  have hk2 : (k + 1) * k ≤ 2 * t := by rw [Nat.mul_comm]; exact hkk
  have eA1 : A * tv ≤ a * R + 2 * a * R := by
    have h1 : A * tv ≤ a * (k + 1) * (U + Fo + k * pS) := Nat.mul_le_mul hA htv
    have h2 : a * (k + 1) * (U + Fo + k * pS) = a * ((k + 1) * (U + Fo)) + a * ((k + 1) * k) * pS := by ring
    have h3 : a * ((k + 1) * (U + Fo)) ≤ a * R := Nat.mul_le_mul_left _ rkUF
    have h4 : a * ((k + 1) * k) * pS ≤ 2 * a * R := by
      calc a * ((k + 1) * k) * pS ≤ a * (2 * t) * pS := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hk2)
        _ = 2 * a * (t * pS) := by ring
        _ ≤ 2 * a * R := Nat.mul_le_mul_left _ rtpS
    omega
  have eA2 : A * (k * Q) ≤ 2 * a * R := by
    calc A * (k * Q) ≤ a * (k + 1) * (k * Q) := Nat.mul_le_mul_right _ hA
      _ = a * ((k + 1) * k) * Q := by ring
      _ ≤ a * (2 * t) * Q := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hk2)
      _ = 2 * a * (t * Q) := by ring
      _ ≤ 2 * a * R := Nat.mul_le_mul_left _ rtQ
  -- I-terms
  have eI : ∀ x, t * x ≤ R → x * I ≤ cI * R := fun x hx => by
    calc x * I ≤ x * (cI * t) := Nat.mul_le_mul_left _ hI
      _ = cI * (t * x) := by ring
      _ ≤ cI * R := Nat.mul_le_mul_left _ hx
  have enw : nw ≤ cn * R := by
    calc nw ≤ cn * t := hnw
      _ ≤ cn * R := Nat.mul_le_mul_left _ (by
          have : t ≤ t * (p + Q) := Nat.le_mul_of_pos_right _ hpQ
          have : t * (p + Q) = t * p + t * Q := by ring
          omega)
  have eW : W ≤ R := by
    have : k * Q ≤ t * Q := Nat.mul_le_mul_right _ (by omega)
    omega
  have e3kp : 3 * k * p ≤ R := by
    have : 3 * k * p ≤ t * p := Nat.mul_le_mul_right _ h3k
    omega
  -- the child sum
  have hC2t : C2 ≤ (3 + cI) * t := by
    have : (3 + cI) * t = 3 * t + cI * t := by ring
    omega
  have etm : t * (p + Cr + Be + pS) ≤ 3 * R := by
    have : t * (p + Cr + Be + pS) = t * p + t * (Cr + Be) + t * pS := by ring
    omega
  have eC2 : C2 * mk ≤ 9 * R + 3 * cI * R := by
    calc C2 * mk ≤ ((3 + cI) * t) * (p + Cr + Be + pS) := Nat.mul_le_mul hC2t hmk
      _ = (3 + cI) * (t * (p + Cr + Be + pS)) := by ring
      _ ≤ (3 + cI) * (3 * R) := Nat.mul_le_mul_left _ etm
      _ = 9 * R + 3 * cI * R := by ring
  have enc : C0 * nch ≤ 5 * c9 * R := by
    have : U + t * (p + Q) + t * (p + Cr + Be) ≤ 5 * R := by
      have e1 : t * (p + Q) = t * p + t * Q := by ring
      have e2 : t * (p + Cr + Be) = t * p + t * (Cr + Be) := by ring
      omega
    calc C0 * nch ≤ c9 * (U + t * (p + Q) + t * (p + Cr + Be)) := hnch
      _ ≤ c9 * (5 * R) := Nat.mul_le_mul_left _ this
      _ = 5 * c9 * R := by ring
  have eC1 : C1 * U ≤ C1 * R := Nat.mul_le_mul_left _ rU
  have epI : p * (2 + I) ≤ 2 * R + cI * R := by
    have := eI p rtp
    have : p * (2 + I) = 2 * p + p * I := by ring
    omega
  have eJI : (1 + I) * J ≤ R + cI * R := by
    have := eI J rtJ
    have : (1 + I) * J = J + J * I := by ring
    omega
  have eWrI : Wr * (1 + I) ≤ R + cI * R := by
    have := eI Wr rtWr
    have : Wr * (1 + I) = Wr + Wr * I := by ring
    omega
  have epSI : pS * I ≤ cI * R := eI pS rtpS
  have eadW : ad * W' ≤ ad * R := Nat.mul_le_mul_left _ (le_trans hW' rU)
  have ebd : bd ≤ bd * R := Nat.le_mul_of_pos_right _ r1
  have escan : scanC * Del ≤ scanC * R := Nat.mul_le_mul_left _ rDel
  have eA : A * (tv + k * Q) = A * tv + A * (k * Q) := by ring
  have hK : (scanC + 5 * a + cn + 5 * c9 + C1 + 7 * cI + ad + bd + 30) * R =
      scanC * R + a * R + 2 * a * R + 2 * a * R + cn * R + 5 * c9 * R + C1 * R + 3 * cI * R + cI * R +
        cI * R + cI * R + cI * R + ad * R + bd * R + 30 * R := by ring
  rw [hK]
  omega

end Arith

section Helpers

variable {Ω : Type} {τ : ℕ → ℕ} {L0 : ℕ} {lg : Log G s Ω} (hL : LogInv τ L0 lg)

/-- Children's returned sets are disjoint subsets of the parent's. -/
theorem children_U_sum_le (X : lg.Call) :
    ∑ Y ∈ Finset.univ.filter (fun Y => Log.parentOf hL Y = some X), (lg.recOf Y).U.card ≤ (lg.recOf X).U.card := by
  classical
  have hdisj : ∀ Y ∈ Finset.univ.filter (fun Y => Log.parentOf hL Y = some X),
      ∀ Y' ∈ Finset.univ.filter (fun Y => Log.parentOf hL Y = some X), Y ≠ Y' →
      Disjoint (lg.recOf Y).U (lg.recOf Y').U := by
    intro Y hY Y' hY' hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hY hY'
    exact (Log.forest hL).siblings_disjoint Y Y' X hY hY' hne
  rw [← Finset.card_biUnion hdisj]
  refine Finset.card_le_card (Finset.biUnion_subset.mpr (fun Y hY => ?_))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hY
  exact (Log.forest hL).U_sub Y X hY

include hL in
/-- Nonempty `U` for every record, from nonempty `S`, `RecFacts` and `τ ≥ 1` (as agent-05's
`MergeTotal.U_ne_of_S_ne`). -/
theorem recU_ne (hτ : ∀ l, 1 ≤ τ l) (hS : ∀ q r, (q, r) ∈ lg → r.S.Nonempty) :
    ∀ q r, (q, r) ∈ lg → r.U.Nonempty := by
  intro q r hq
  have hf := hL.facts q r hq
  rcases lt_or_eq_of_le hf.B'_le with hlt | heq
  · exact Finset.card_pos.mp (lt_of_lt_of_le (hτ r.lvl) (hf.partial_card hlt))
  · obtain ⟨x, hx⟩ := hS q r hq
    exact ⟨x, hf.full_S heq hx⟩

/-- With nonempty `U`s, the number of children is at most the sum of their `U`s. -/
theorem card_children_le (hne : ∀ q r, (q, r) ∈ lg → r.U.Nonempty) (X : lg.Call) :
    (Finset.univ.filter (fun Y => Log.parentOf hL Y = some X)).card ≤
      ∑ Y ∈ Finset.univ.filter (fun Y => Log.parentOf hL Y = some X), (lg.recOf Y).U.card := by
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum (fun Y _ => Finset.card_pos.mpr (hne _ _ (recOf_mem Y)))

end Helpers

/-- Pairwise disjoint lists inside `S` have total size at most `|S|`. -/
theorem sum_toFinset_card_le {α : Type*} [DecidableEq α] {S : Finset α} :
    ∀ L : List (List α), L.Pairwise (fun g g' => ∀ x ∈ g, x ∉ g') → (∀ g ∈ L, ∀ x ∈ g, x ∈ S) →
      (L.map (fun g => g.toFinset.card)).sum ≤ S.card := by
  intro L
  induction L generalizing S with
  | nil => intro _ _; simp
  | cons g L ih =>
    intro hpw hsub
    obtain ⟨h1, h2⟩ := List.pairwise_cons.mp hpw
    have hgS : g.toFinset ⊆ S := fun x hx => hsub g List.mem_cons_self x (List.mem_toFinset.mp hx)
    have ih' := ih (S := S \ g.toFinset) h2 (fun g' hg' x hx => by
      refine Finset.mem_sdiff.mpr ⟨hsub g' (List.mem_cons_of_mem _ hg') x hx, ?_⟩
      intro hxg
      exact h1 g' hg' x (List.mem_toFinset.mp hxg) hx)
    simp only [List.map_cons, List.sum_cons]
    have : (S \ g.toFinset).card = S.card - g.toFinset.card := Finset.card_sdiff_of_subset hgS
    have := Finset.card_le_card hgS
    omega


section Final

variable {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}
variable {τ : ℕ → ℕ} {L0 : ℕ} {lg : Log G s (FPData G s)} (hL : LogInv τ L0 lg)

/-- The FindPivots constant is linear in `k`. -/
theorem fpA_le : fpA k hins hext ≤ (2 * (scanC + hins) + hext + 2) * (k + 1) := by
  unfold fpA
  have e : (2 * (scanC + hins) + hext + 2) * (k + 1) =
      2 * ((scanC + hins) * k) + 2 * (scanC + hins) + (hext + 2) * k + hext + 2 := by ring
  have e2 : (scanC + hins) * (1 + k) = (scanC + hins) + (scanC + hins) * k := by ring
  rw [e, e2]
  have : 0 ≤ (hext + 2) * k := Nat.zero_le _
  omega

/-- **Markings of any call** are at most `|S|` (groups are disjoint subsets of `S`; each child meeting a
group owns one of its vertices). -/
theorem mkOf_le_S (X : lg.Call) : mkOf hL k X ≤ (lg.recOf X).S.card := by
  classical
  unfold mkOf groupsOf
  cases hω : (lg.recOf X).fp with
  | none => simp
  | some ω =>
    simp only
    obtain ⟨hg1, hg2, -, -, -⟩ := Partition.makePivots_spec (S := (lg.recOf X).S) (Q := (lg.recOf X).Q)
      (Partition.forestPieces k ω.trees)
    calc _ ≤ ((forestGroups (lg.recOf X).S (lg.recOf X).Q k ω.trees).map (fun g => g.toFinset.card)).sum := by
          refine Reselect.map_sum_le _ _ _ (fun g _ => ?_)
          exact ((BM.Log.ranges hL).card_children_meeting_le (val := fun v => dis (s := s) v) X
            g.toFinset).trans Finset.card_image_le
      _ ≤ (lg.recOf X).S.card :=
          sum_toFinset_card_le _ hg2 (fun g hg x hx => ((hg1 g hg).2.2 x hx).1)

/-- The call-indexed counters of a traced C-HD run: agent-01's `countersC` with agent-03's foreign leaves
(`foOf`), crossing edges (`crOf`), kind-(β) edges (`beOf`) and the FindPivots deletions (`delOf`). -/
noncomputable def tracedCounters :
    CostAggregate.CallCounters lg.Call (Fin G.n) (Fin G.m) (WLab G s) :=
  Log.countersC hL (fun X => foOf (lg.recOf X)) (crOf hL) (beOf hL)
    (fun X => delOf (fun ω : FPData G s => ω.Din) (fun ω => ω.Dout) (lg.recOf X))

/-- **`CostAggregate.Valid.cost_le`** (tracker O10) for the traced counters, from the per-record cost facts
(`RecCost`, all levels by `bmsspC_reccost`), the record facts (`RecAll`, by `bmsspC_recall`), nonempty
frontiers (`bmsspC_S_ne`) and the parameter facts.  `C0 ≤ c9` is the per-iteration constant
`1 + b_pull + b_del`; it is `O(1)` exactly when the `D`-pull bound has an `O(1)` additive part. -/
theorem tracedCounters_cost_le (hout : ∀ u e, e ∈ out u ↔ G.src e = u)
    (hsort : ∀ u, (out u).Pairwise (SortedRel G s)) (hsimp : ∀ u, ((out u).map G.dst).Nodup)
    (hk : 2 ≤ k) {C0 C1 I ad bd nw a cI cn c9 t c : ℕ}
    (hRC : RecCost (chgOf k C0 C1 (2 * (3 * k) + 1 + I)) (budOf k hins hext ad bd I nw) lg)
    (hRA : ∀ q r, (q, r) ∈ lg → RecAll out k hins hext r)
    (hS : ∀ q r, (q, r) ∈ lg → r.S.Nonempty) (hτ : ∀ l, 1 ≤ τ l)
    (hA : fpA k hins hext ≤ a * (k + 1)) (hkk : k * (k + 1) ≤ 2 * t) (h3k : 3 * k ≤ t)
    (hI : I ≤ cI * t) (hnw : nw ≤ cn * t) (hC0 : C0 ≤ c9)
    (hc : scanC + 5 * a + cn + 5 * c9 + C1 + 7 * cI + ad + bd + 30 ≤ c) :
    ∀ X, (tracedCounters hL).base X = false → (tracedCounters hL).cost X ≤
      c * ((k + 1) * (((tracedCounters hL).F.U X).card + ((tracedCounters hL).Fo X).card)
        + ((tracedCounters hL).S X).card + t * ((tracedCounters hL).Q X).card
        + t * (((tracedCounters hL).J X).card + ((tracedCounters hL).Wr X).card
          + ((tracedCounters hL).Cr X).card + ((tracedCounters hL).Be X).card)
        + t * (tracedCounters hL).p X
        + (if (tracedCounters hL).full X then 0 else t * ((tracedCounters hL).S X).card)
        + (tracedCounters hL).mergeCost X + ((tracedCounters hL).Del X).card) := by
  classical
  intro X hb
  have hmem : (X.1, lg.recOf X) ∈ lg := recOf_mem X
  set r := lg.recOf X with hr
  have hb' : r.base = false := hb
  have hcost := hRC X.1 r hmem hb'
  rw [childSumAt_eq_sum hL] at hcost
  obtain ⟨hFP, -, hnd, hfpω⟩ := hRA X.1 r hmem
  obtain ⟨ω, hω⟩ := hfpω hb'
  have hf := hL.facts X.1 r hmem
  have hF : ∀ q r, (q, r) ∈ lg → RecForest r := fun q r h => (hRA q r h).2.1
  -- the FindPivots facts of this record
  obtain ⟨d0, d1, Din, Dout, P, cfp, hpre, hDI, hfprel⟩ := hFP.fp ω hω
  have hW : r.W.card ≤ k * r.Q.card := fpC_W_card hfprel
  obtain ⟨hp, -⟩ := hfprel.2.2.1
  have hDin : ω.Din = Din := hfprel.2.2.2.1
  have hDout : ω.Dout = Dout := hfprel.2.2.2.2
  obtain ⟨hrel, -, -, -⟩ := hfprel
  obtain ⟨hcon, -⟩ := findPivotsC_spec hout hsort hsimp hk hpre hDI hrel
  -- S nonempty, p + |Q| ≥ 1
  obtain ⟨x0, hx0⟩ := hS X.1 r hmem
  have hS1 : 1 ≤ r.S.card := Finset.card_pos.mpr ⟨x0, hx0⟩
  have hpQ : 1 ≤ r.p + r.Q.card := by
    rcases hcon.cover x0 hx0 with hq | ⟨j, -⟩
    · have := Finset.card_pos.mpr ⟨x0, hq⟩; omega
    · have := j.2; rw [hp]; omega
  -- tree vertices: `#tv ≤ |U| + |Fo|`
  have htv : tvLen r ≤ r.U.card + (foOf r).card + k * (if r.B' = r.B then 0 else r.S.card) := by
    have h1 : tvLen r = ω.tvs.card := by
      simp only [tvLen, hω, FPData.tvs]; exact (List.toFinset_card_of_nodup (hnd ω hω)).symm
    have h2 : foOf r = ω.tvs \ r.U := by simp only [foOf, hω]
    have h3 : ω.tvs.card ≤ (ω.tvs \ r.U).card + r.U.card := Finset.card_le_card_sdiff_add_card
    rw [h1, h2]; omega
  have hW' : r.W'.card ≤ r.U.card := Finset.card_le_card hf.W'_sub
  have hDel : delCard r = (delOf (fun ω : FPData G s => ω.Din) (fun ω => ω.Dout) r).card := by
    simp only [delCard, delOf, hω]
  -- children
  have hUne := recU_ne hL hτ hS
  have hch1 : (Finset.univ.filter (fun Y => Log.parentOf hL Y = some X)).card ≤ r.U.card :=
    (card_children_le hL hUne X).trans (children_U_sum_le hL X)
  have hch2 : ∑ Y ∈ Finset.univ.filter (fun Y => Log.parentOf hL Y = some X), (lg.recOf Y).U.card ≤ r.U.card :=
    children_U_sum_le hL X
  have hch3 : ∑ Y ∈ Finset.univ.filter (fun Y => Log.parentOf hL Y = some X),
      (groupsOf k r).countP (fun g => decide (g.toFinset ∩ (lg.recOf Y).U).Nonempty) = mkOf hL k X :=
    sum_children_countP hL k X
  have hcs : ∑ Y ∈ Finset.univ.filter (fun Y => Log.parentOf hL Y = some X),
      chgOf k C0 C1 (2 * (3 * k) + 1 + I) r (lg.recOf Y) ≤
      C0 * (Finset.univ.filter (fun Y => Log.parentOf hL Y = some X)).card + C1 * r.U.card +
        (2 * (3 * k) + 1 + I) * mkOf hL k X := by
    unfold chgOf
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.mul_sum,
      ← Finset.mul_sum, hch3, Nat.mul_comm _ C0]
    have := Nat.mul_le_mul_left C1 hch2
    omega
  -- markings
  have hmk : mkOf hL k X ≤ r.p + (crOf hL X).card + (beOf hL X).card + (if r.B' = r.B then 0 else r.S.card) := by
    by_cases hfull : r.B' = r.B
    · have hUt : ∀ v ∈ Utilde r.B (r.S : Set (Fin G.n)), v ∈ r.U := fun v hv =>
        (hFP.U_eq v).mpr (by rw [hfull]; exact hv)
      have h1 : mkOf hL k X ≤ (groupsOf k r).length + (crOf hL X).card + (beOf hL X).card :=
        mkOf_full_le hL k hk hF hfull hUt
      have hg : (groupsOf k r).length = r.p := by simp only [groupsOf, hω]; exact hp.symm
      rw [if_pos hfull]; omega
    · rw [if_neg hfull]
      have : mkOf hL k X ≤ r.S.card := mkOf_le_S (k := k) hL X
      omega
  have hnch : C0 * (Finset.univ.filter (fun Y => Log.parentOf hL Y = some X)).card ≤
      c9 * (r.U.card + t * (r.p + r.Q.card) + t * (r.p + (crOf hL X).card + (beOf hL X).card)) :=
    (Nat.mul_le_mul hC0 hch1).trans (Nat.mul_le_mul_left _ (by omega))
  have key := budget_arith (Del := delCard r) (A := fpA k hins hext) (tv := tvLen r) (k := k) (Q := r.Q.card)
    (S := r.S.card) (nw := nw) (p := r.p) (I := I) (J := r.J.card) (cm := r.cMerge) (W := r.W.card)
    (W' := r.W'.card) (Wr := r.Wr.card) (ad := ad) (bd := bd) (U := r.U.card) (Fo := (foOf r).card) (t := t)
    (Cr := (crOf hL X).card) (Be := (beOf hL X).card) (mk := mkOf hL k X) (C0 := C0) (C1 := C1)
    (C2 := 2 * (3 * k) + 1 + I) (a := a) (cI := cI) (cn := cn) (c9 := c9)
    (pS := if r.B' = r.B then 0 else r.S.card)
    htv hA hW hW' hcs hmk hnch hS1 hpQ hkk h3k (by omega) hI hnw (by omega)
  unfold budOf at hcost
  have hfin := hcost.trans (key.trans (Nat.mul_le_mul_right _ hc))
  show r.cost ≤ c * ((k + 1) * (r.U.card + (foOf r).card) + r.S.card + t * r.Q.card
      + t * (r.J.card + r.Wr.card + (crOf hL X).card + (beOf hL X).card) + t * r.p
      + (if decide (r.B' = r.B) = true then 0 else t * r.S.card) + r.cMerge
      + (delOf (fun ω : FPData G s => ω.Din) (fun ω => ω.Dout) r).card)
  rw [← hDel]
  have ht : t * (if r.B' = r.B then 0 else r.S.card) = (if decide (r.B' = r.B) = true then 0 else t * r.S.card) := by
    by_cases hfull : r.B' = r.B <;> simp [hfull]
  rw [← ht]
  exact hfin

end Final

section Transfer

/-! ### The other agent-03 fields of `Valid` for the traced counters (transfers from the record-indexed forms) -/

variable {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}
variable {τ : ℕ → ℕ} {L0 : ℕ} {lg : Log G s (FPData G s)} (hL : LogInv τ L0 lg)

/-- `Valid.foreign_level` (O3). -/
theorem tracedCounters_foreign_level (hout : ∀ u e, e ∈ out u ↔ G.src e = u)
    (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (hrec : ∀ q r, (q, r) ∈ lg → RecFP out k hins hext r) (j : ℕ) :
    ∑ X ∈ Finset.univ.filter (fun X => (tracedCounters hL).F.depth X = j ∧ (tracedCounters hL).full X = true),
      ((tracedCounters hL).Fo X).card ≤ Fintype.card (Fin G.n) :=
  counters_foreign_level hout hsort hL hrec (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) j

/-- `Valid.full_p` (O3). -/
theorem tracedCounters_full_p (hout : ∀ u e, e ∈ out u ↔ G.src e = u)
    (hsort : ∀ u, (out u).Pairwise (SortedRel G s)) (hsimp : ∀ u, ((out u).map G.dst).Nodup) (hk : 2 ≤ k)
    (hrec : ∀ q r, (q, r) ∈ lg → RecFP out k hins hext r)
    (hnd : ∀ q r, (q, r) ∈ lg → ∀ ω, r.fp = some ω → (ω.trees.flatMap (fun T => T.ord)).Nodup) :
    ∀ X, (tracedCounters hL).full X = true →
      (tracedCounters hL).p X * (k - 1) ≤ ((tracedCounters hL).F.U X).card + ((tracedCounters hL).Fo X).card :=
  counters_full_p hout hsort hsimp hk hL hrec hnd (fun _ => ∅) (fun _ => ∅) (fun _ => ∅)

/-- `Valid.partial_Fo` (O3), from `Valid.partial_S`. -/
theorem tracedCounters_partial_Fo (hout : ∀ u e, e ∈ out u ↔ G.src e = u)
    (hsort : ∀ u, (out u).Pairwise (SortedRel G s)) (hk : 1 ≤ k) {t : ℕ} (hkt : k ≤ t)
    (hrec : ∀ q r, (q, r) ∈ lg → RecFP out k hins hext r)
    (hpS : ∀ X, (tracedCounters hL).full X = false →
      t * ((tracedCounters hL).S X).card ≤ ((tracedCounters hL).F.U X).card) :
    ∀ X, (tracedCounters hL).full X = false →
      ((tracedCounters hL).Fo X).card ≤ ((tracedCounters hL).F.U X).card :=
  counters_partial_Fo hout hsort hk hkt hL hrec (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) hpS

/-- `Valid.cr_cross`. -/
theorem tracedCounters_cr_cross (hF : ∀ q r, (q, r) ∈ lg → RecForest r) :
    ∀ X, ∀ e ∈ (tracedCounters hL).Cr X, (tracedCounters hL).src e ∈ (tracedCounters hL).F.U X ∧
      (tracedCounters hL).dst e ∈ (tracedCounters hL).F.U X ∧
      ∀ Y, (tracedCounters hL).F.parent Y = some X →
        ¬ ((tracedCounters hL).src e ∈ (tracedCounters hL).F.U Y ∧
          (tracedCounters hL).dst e ∈ (tracedCounters hL).F.U Y) :=
  crOf_cross hL hF

/-- `Valid.be_total`. -/
theorem tracedCounters_be_total (hout : ∀ u e, e ∈ out u ↔ G.src e = u)
    (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (hrec : ∀ q r, (q, r) ∈ lg → RecFP out k hins hext r) (hF : ∀ q r, (q, r) ∈ lg → RecForest r) :
    ∑ X, ((tracedCounters hL).Be X).card ≤ Fintype.card (Fin G.m) :=
  beOf_total hL hout hsort hrec hF

/-- `Valid.del_disj` (agent-05's chained deletion intervals). -/
theorem tracedCounters_del_disj {a b : Finset (Fin G.m)}
    (hc : Chain (fun ω : FPData G s => ω.Din) (fun ω => ω.Dout) a lg b) :
    ∀ X X', X ≠ X' → Disjoint ((tracedCounters hL).Del X) ((tracedCounters hL).Del X') :=
  counters_del_disj (din := fun ω : FPData G s => ω.Din) (dout := fun ω => ω.Dout) hL hc
    (fun _ => ∅) (fun _ => ∅) (fun _ => ∅)

end Transfer

end BM
end CHD
end Frontier
