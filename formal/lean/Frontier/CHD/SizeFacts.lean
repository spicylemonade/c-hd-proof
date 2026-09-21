import Frontier.CHD.CostLog
import Frontier.CHD.FPWQ

/-!
# Frontier.CHD.SizeFacts — frontier and returned-set sizes as trace facts (tracker O12 (B1), (B3); owner agent-03)

**NON-GATE** (Layer A).  For every `BMSSPC` derivation with `FPC := fpC …`:
* (B1) `bmsspC_sizes` (`ChildS`): every sub-call of a level-`lv` call has `|S| ≤ 3k · DC.M lv` (at most `M` pulled
  keys, each the pivot of at most one group of size `< 3k`);
* (B3) `bmsspC_sizes`: a call at level `l` returns `|U| ≤ ucap l |S|`, where
  `ucap 0 _ = τ 0` and `ucap (l+1) Sb = τ (l+1) + ucap l (3k · DC.M (l+1)) + k · Sb`
  (the loop stops once `|U| > τ`, the last sub-call adds at most its own cap, and `|W'| ≤ |W| ≤ k|Q| ≤ k|S|`).
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-- **Expansion of a pulled set** (BM.11–12): at most `3k` vertices per pulled key. -/
theorem expand_card_le {p : ℕ} (σ : LState G s p) (S0 : Finset (Fin G.n)) (Bi : WLab G s) {k : ℕ}
    (hk : 1 ≤ k) (hP : ∀ j, (σ.P j).card < 3 * k) (hdisj : ∀ i j, i ≠ j → Disjoint (σ.P i) (σ.P j)) :
    (expand σ S0 Bi).card ≤ 3 * k * S0.card := by
  classical
  set Jsel := Finset.univ.filter (fun j : Fin p => σ.piv j ∈ S0 ∧ σ.piv j ∈ σ.P j) with hJsel
  have hsub : expand σ S0 Bi ⊆ S0 ∪ Jsel.biUnion (fun j => σ.P j) := by
    intro v hv
    rcases mem_expand.mp hv with h | ⟨j, h1, h2, h3, -⟩
    · exact Finset.mem_union_left _ h
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, ?_, h3⟩)
      rw [hJsel, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, h1, h2⟩
  have hJ : Jsel.card ≤ S0.card := by
    refine Finset.card_le_card_of_injOn (fun j => σ.piv j) ?_ ?_
    · intro j hj
      have hj' : j ∈ Jsel := hj
      rw [hJsel, Finset.mem_filter] at hj'
      exact hj'.2.1
    · intro i hi j hj hij
      have hi' : i ∈ Jsel := hi
      have hj' : j ∈ Jsel := hj
      rw [hJsel, Finset.mem_filter] at hi' hj'
      by_contra hne
      have hij' : σ.piv i = σ.piv j := hij
      exact Finset.disjoint_left.mp (hdisj i j hne) hi'.2.2 (by rw [hij']; exact hj'.2.2)
  have hU : (Jsel.biUnion (fun j => σ.P j)).card ≤ Jsel.card * (3 * k - 1) := by
    calc _ ≤ ∑ j ∈ Jsel, (σ.P j).card := Finset.card_biUnion_le
      _ ≤ ∑ j ∈ Jsel, (3 * k - 1) := Finset.sum_le_sum (fun j _ => by have := hP j; omega)
      _ = Jsel.card * (3 * k - 1) := by rw [Finset.sum_const, smul_eq_mul]
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le S0 (Jsel.biUnion (fun j => σ.P j))
  have h3 : Jsel.card * (3 * k - 1) ≤ S0.card * (3 * k - 1) := Nat.mul_le_mul_right _ hJ
  have h4 : 3 * k * S0.card = S0.card * (3 * k - 1) + S0.card := by
    obtain ⟨m, hm⟩ : ∃ m, 3 * k = m + 1 := ⟨3 * k - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel]
    ring
  omega

/-- The returned-set cap: `ucap 0 _ = τ 0`, `ucap (l+1) Sb = τ (l+1) + ucap l (3k · M_{l+1}) + k · Sb`. -/
def ucap (DC : DCost) (k : ℕ) (τ : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => τ 0
  | l + 1, Sb => τ (l + 1) + ucap DC k τ l (3 * k * DC.M (l + 1)) + k * Sb

theorem ucap_mono {DC : DCost} {k : ℕ} {τ : ℕ → ℕ} : ∀ (l : ℕ) {Sb Sb' : ℕ}, Sb ≤ Sb' →
    ucap DC k τ l Sb ≤ ucap DC k τ l Sb'
  | 0, _, _, _ => le_rfl
  | l + 1, Sb, Sb', h => by
    simp only [ucap]
    have := Nat.mul_le_mul_left k h
    omega

/-- Size facts of a log: every sub-call record has `|S| ≤ 3k · M` of its parent's level. -/
def ChildS (DC : DCost) (k : ℕ) (lg : Log G s (FPData G s)) : Prop :=
  ∀ q a r, (q ++ [a], r) ∈ lg → ∃ r0, (q, r0) ∈ lg ∧ r.S.card ≤ 3 * k * DC.M r0.lvl

section Loop

variable {DC : DCost} {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}
variable {B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {p : ℕ}
  {P0 : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {B'0 : WLab G s}

/-- **(B1) and (B3) in the loop.** -/
theorem loopC_sizes (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W)
    {τ : ℕ → ℕ} {Inv : Finset (Fin G.m) → Prop} {sub : SubRelC G s (Finset (Fin G.m)) (FPData G s)} {l : ℕ}
    (hsub : GoodSub G s τ Inv l sub) (hk : 1 ≤ k) (hP0 : ∀ j, (P0 j).card < 3 * k) {cap : ℕ}
    (hsubS : ∀ Blow B S d φ res φ' lg, CallPre B S d → Inv φ → (∀ x ∈ S, Blow ≤ dis (s := s) x) → Blow ≤ B →
      sub Blow B S d φ res φ' lg → S.card ≤ 3 * k * DC.M (l + 1) → res.2.1.card ≤ cap ∧ ChildS DC k lg)
    {τl : ℕ} :
    ∀ i (σ : LState G s p) φ σ' φ' lg J cm c,
      LoopC G s DC sub (l + 1) B τl i σ φ σ' φ' lg J cm c →
      LInv G s B S d0 d1 P0 B'0 σ → Inv φ →
      (∀ j r, ([j], r) ∈ lg → r.S.card ≤ 3 * k * DC.M (l + 1)) ∧
      (∀ q a r, (q ++ [a], r) ∈ lg → q ≠ [] → ∃ r0, (q, r0) ∈ lg ∧ r.S.card ≤ 3 * k * DC.M r0.lvl) ∧
      (σ.U.card ≤ τl + cap → σ'.U.card ≤ τl + cap) := by
  intro i σ φ σ' φ' lg J cm c hloop
  induction hloop with
  | stop i σ φ hstop =>
    intro _ _
    exact ⟨fun j r h => absurd h List.not_mem_nil, fun q a r h => absurd h List.not_mem_nil, id⟩
  | step i σ σ' φ φ1 φ' S0 Bi D1 B'i Ui Di dsub L' piv' lg lg' J' cm c hUτ hne hpull' hSM _ hsubrel
      hnd hmem hres hrest ih =>
    intro h hI
    have hsp : CallPre Bi (expand σ S0 Bi) σ.d := step_pre hpre hfp h hpull'
    have hlowdis : ∀ x ∈ expand σ S0 Bi, σ.B' ≤ dis (s := s) x :=
      fun x hx => (Si_facts h hpull' hx).1.2.2
    have hSne : S0.Nonempty := by
      apply hpull'.nonempty
      simp only [DS.IsEmpty, not_forall] at hne
      exact hne
    obtain ⟨x0, hx0⟩ := hSne
    have hx0S : x0 ∈ expand σ S0 Bi := mem_expand.mpr (Or.inl hx0)
    have hBlt : σ.B' < Bi := by
      obtain ⟨⟨-, -, hB⟩, hlt⟩ := Si_facts h hpull' hx0S
      exact lt_of_le_of_lt (hB.trans (h.walk.sound x0)) hlt
    obtain ⟨hpost, hI1, hclog⟩ := hsub σ.B' Bi (expand σ S0 Bi) σ.d φ (B'i, Ui, Di, dsub) φ1 lg
      hsp hI hlowdis hBlt.le hsubrel
    -- (B1) for this sub-call
    have hPk : ∀ j, (σ.P j).card < 3 * k := fun j =>
      lt_of_le_of_lt (Finset.card_le_card (h.Psub j)) (hP0 j)
    have hPd : ∀ i j, i ≠ j → Disjoint (σ.P i) (σ.P j) := fun i j hij =>
      Finset.disjoint_of_subset_left (h.Psub i) (Finset.disjoint_of_subset_right (h.Psub j) (hfp.gdisj i j hij))
    have hSi : (expand σ S0 Bi).card ≤ 3 * k * DC.M (l + 1) :=
      (expand_card_le σ S0 Bi hk hPk hPd).trans (Nat.mul_le_mul_left _ hSM)
    obtain ⟨hUi0, hCS⟩ := hsubS σ.B' Bi (expand σ S0 Bi) σ.d φ (B'i, Ui, Di, dsub) φ1 lg
      hsp hI hlowdis hBlt.le hsubrel hSi
    have hUi : Ui.card ≤ cap := hUi0
    obtain ⟨ri, hri, -, -, -, hriS, -, -⟩ := hclog.root
    -- the next state
    have hmem' : ∀ e, e ∈ L' ↔ G.src e ∈ Ui ∧ Bi ≤ ext (dis (s := s) (G.src e)) e ∧
        ext (dis (s := s) (G.src e)) e < B := by
      intro e
      rw [hmem e]
      constructor
      · rintro ⟨hu, h1, h2⟩
        have hc : dsub (G.src e) = dis (s := s) (G.src e) := hpost.U_complete _ hu
        rw [hc] at h1 h2
        exact ⟨hu, h1, h2⟩
      · rintro ⟨hu, h1, h2⟩
        have hc : dsub (G.src e) = dis (s := s) (G.src e) := hpost.U_complete _ hu
        rw [← hc] at h1 h2
        exact ⟨hu, h1, h2⟩
    obtain ⟨L, hL, hfold⟩ :=
      window_scan_step hpull'.bound hpost ((D1.merge Di).deleteSet Ui) hnd hmem'
    have hres' : Reselect σ Ui
        (L.foldl (relaxIns G s B (some Bi)) (dsub, (D1.merge Di).deleteSet Ui)).1 piv' := by
      rw [hfold]; exact hres
    have hnext := step_post hpre hfp h hne hpull' hpost hL hres'
    rw [hfold] at hnext
    obtain ⟨ha, hb, hc⟩ := ih hnext hI1
    have hin1 : ∀ x, x ∈ lg.shift i → x ∈ lg.shift i ++ lg' := fun x hx => List.mem_append_left _ hx
    have hin2 : ∀ x, x ∈ lg' → x ∈ lg.shift i ++ lg' := fun x hx => List.mem_append_right _ hx
    refine ⟨fun j r hjr => ?_, fun q a r hqr hq => ?_, fun hU0 => hc ?_⟩
    · rcases List.mem_append.mp hjr with h1 | h2
      · obtain ⟨q', hq', hq'r⟩ := mem_shift.mp h1
        obtain ⟨rfl, rfl⟩ : j = i ∧ q' = [] := by
          simp only [List.cons.injEq] at hq'
          exact ⟨hq'.1, hq'.2.symm⟩
        have hrr : r = ri := rec_unique hclog.inv.nodup hq'r hri
        subst hrr
        rw [hriS]
        exact hSi
      · exact ha j r h2
    · rcases List.mem_append.mp hqr with h1 | h2
      · obtain ⟨q', hq', hq'r⟩ := mem_shift.mp h1
        obtain ⟨b, q0, rfl⟩ := List.exists_cons_of_ne_nil hq
        simp only [List.cons_append, List.cons.injEq] at hq'
        obtain ⟨rfl, rfl⟩ := hq'
        obtain ⟨r0, hr0, hS0⟩ := hCS q0 a r hq'r
        exact ⟨r0, hin1 _ (mem_shift.mpr ⟨q0, rfl, hr0⟩), hS0⟩
      · obtain ⟨r0, hr0, hS0⟩ := hb q a r h2 hq
        exact ⟨r0, hin2 _ hr0, hS0⟩
    · show (σ.U ∪ Ui).card ≤ τl + cap
      exact (Finset.card_union_le _ _).trans (by omega)

end Loop

section Levels

variable {DC : DCost} {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}

/-- The base loop never returns more than `τ` vertices. -/
theorem baseLoopC_U {B : WLab G s} {τ : ℕ} :
    ∀ {st st' : Labels G s × DS G s × Finset (Fin G.n)} {c : ℕ}, BaseLoopC G s DC B τ st st' c →
      st.2.2.card ≤ τ → st'.2.2.card ≤ τ := by
  intro st st' c h
  induction h with
  | stop st _ => exact id
  | step d D U u val L st' c hu hmin hcard hL _ ih =>
    intro _
    apply ih
    exact (Finset.card_insert_le _ _).trans (by omega)

/-- **(B1) and (B3) for every traced derivation**: a call at level `l` returns at most `ucap l |S|` vertices,
and every sub-call record of its log has `|S| ≤ 3k · M` of its parent's level. -/
theorem bmsspC_sizes (hout : ∀ u e, e ∈ out u ↔ G.src e = u) (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (hsimp : ∀ u, ((out u).map G.dst).Nodup) (hk : 2 ≤ k) (τ : ℕ → ℕ) :
    ∀ l Blow B S d φ res φ' lg, CallPre B S d → DelInv G s φ → (∀ x ∈ S, Blow ≤ dis (s := s) x) → Blow ≤ B →
      BMSSPC G s (fpC G s out k hins hext) DC τ l Blow B S d φ res φ' lg →
      res.2.1.card ≤ ucap DC k τ l S.card ∧ ChildS DC k lg
  | 0 => by
    intro Blow B S d φ res φ' lg _ _ _ _ hrel
    obtain ⟨st, c, hloop, hU, -, -, -, -, -, rfl⟩ := hrel
    refine ⟨?_, fun q a r h => ?_⟩
    · rw [hU]
      exact baseLoopC_U hloop (by simp)
    · rcases List.mem_singleton.mp h with heq
      have := congrArg Prod.fst heq
      simp at this
  | l + 1 => by
    intro Blow B S d φ res φ' lg hpre hI hlow hBB hrel
    have hsub := bmsspC_log (DC := DC) (fpC_sound (hins := hins) (hext := hext) hout hsort hsimp hk) τ l
    have hsz := bmsspC_sizes hout hsort hsimp hk τ l
    obtain ⟨d1, p, P, Q, W, φ1, ω, cfp, piv, σ, lgc, J, cm, cl, L, B'f, T6, W', hfprel, hpiv,
      hloop, hB'e, hB'n, hT6, hW', hL, hres, hlg⟩ := hrel
    obtain ⟨R, hR, hRlvl, hRS⟩ : ∃ R : CallRec G s (FPData G s), lg = ([], R) :: lgc ∧ R.lvl = l + 1 ∧
        R.S = S := ⟨_, hlg, rfl, rfl⟩
    subst hR
    subst hres
    have hlow' : ∀ x ∈ S, Blow ≤ d x := fun x hx => (hlow x hx).trans (hpre.walk.sound x)
    obtain ⟨hfp, hI1⟩ := fpC_sound hout hsort hsimp hk _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpre hI hlow' hfprel
    obtain ⟨-, -, hP0, -, -⟩ := fpC_spec hout hsort hsimp hk hpre hI hfprel
    have hWQ : W.card ≤ k * Q.card := fpC_W_card hfprel
    have h0 := linv_init hpre hfp hpiv
    have hsubS : ∀ Blow' B' S' d' φ0 res' φ0' lg', CallPre B' S' d' → DelInv G s φ0 →
        (∀ x ∈ S', Blow' ≤ dis (s := s) x) → Blow' ≤ B' →
        BMSSPC G s (fpC G s out k hins hext) DC τ l Blow' B' S' d' φ0 res' φ0' lg' →
        S'.card ≤ 3 * k * DC.M (l + 1) →
        res'.2.1.card ≤ ucap DC k τ l (3 * k * DC.M (l + 1)) ∧ ChildS DC k lg' := by
      intro Blow' B' S' d' φ0 res' φ0' lg' h1 h2 h3 h4 h5 hS'
      obtain ⟨hU', hC'⟩ := hsz Blow' B' S' d' φ0 res' φ0' lg' h1 h2 h3 h4 h5
      exact ⟨hU'.trans (ucap_mono l hS'), hC'⟩
    obtain ⟨ha, hb, hc⟩ := loopC_sizes hpre hfp hsub (by omega) hP0 hsubS _ _ _ _ _ _ _ _ _ hloop h0 hI1
    have hσU : σ.U.card ≤ τ (l + 1) + ucap DC k τ l (3 * k * DC.M (l + 1)) := hc (by simp [initState])
    have hQS : Q.card ≤ S.card := Finset.card_le_card hfp.qsub
    have hW'W : W'.card ≤ W.card := Finset.card_le_card (fun x hx => ((hW' x).mp hx).1.1)
    refine ⟨?_, fun q a r hqr => ?_⟩
    · show (σ.U ∪ W').card ≤ τ (l + 1) + ucap DC k τ l (3 * k * DC.M (l + 1)) + k * S.card
      have := Nat.mul_le_mul_left k hQS
      exact (Finset.card_union_le _ _).trans (by omega)
    · have hqr' : (q ++ [a], r) ∈ lgc := by
        rcases List.mem_cons.mp hqr with heq | h'
        · have := congrArg Prod.fst heq
          simp at this
        · exact h'
      by_cases hq : q = []
      · subst hq
        exact ⟨R, List.mem_cons_self, by rw [hRlvl]; exact ha a r hqr'⟩
      · obtain ⟨r0, hr0, hS0⟩ := hb q a r hqr' hq
        exact ⟨r0, List.mem_cons_of_mem _ hr0, hS0⟩

end Levels

end BM
end CHD
end Frontier
