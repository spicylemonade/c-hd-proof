import Frontier.CHD.BMCost
import Frontier.Density
import Frontier.CostAggregate

/-!
# Frontier.CHD.BMTrace — the call forest of a cost-indexed BMSSP run (L4-COST stage 2)

Owner: agent-01 (COORD G2-4; tracker O1, O2, and the L4-owned fields of `CostAggregate.Valid`).
NON-GATE.

For every derivation of `BMSSPC` (from a call satisfying `CallPre`), the call log satisfies
`LogInv`: record facts from Lemma S2.1, parent/child facts, ordered siblings, jump windows,
`W'`-ownership and leaf base calls.  From `LogInv` we build
* `Log.forest`: a `CostCharging.CallForest` on the call paths (tracker O1);
* `Log.ranges`: the handled ranges `[B_low X, B'_X)` as a `Density.Ranges` (tracker O2);
* the L4-owned facts of `CostAggregate.CallCounters.Valid`: `jump_window`, `wr_own`, `full_S`,
  `base_leaf`, `depth_le`, `Q_sub`, `partial_p`.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

section defs

variable (G s)

/-- The window value of an edge: the canonical label of its tail, extended by the edge. -/
noncomputable def eval (e : Fin G.m) : WLab G s := ext (dis (s := s) (G.src e)) e

variable {G s} {Ω : Type}

/-- Facts about one call record (from Lemma S2.1 and the FindPivots contract). -/
structure RecFacts (τ : ℕ → ℕ) (r : CallRec G s Ω) : Prop where
  B'_le : r.B' ≤ r.B
  low_S : ∀ x ∈ r.S, r.Blow ≤ dis (s := s) x
  U_low : ∀ v ∈ r.U, r.Blow ≤ dis (s := s) v
  U_high : ∀ v ∈ r.U, dis (s := s) v < r.B'
  full_S : r.B' = r.B → r.S ⊆ r.U
  partial_card : r.B' < r.B → τ r.lvl ≤ r.U.card
  W'_sub : r.W' ⊆ r.U
  Q_sub : r.Q ⊆ r.S
  p_le : r.p ≤ r.S.card

/-- Parent (`r0`) / child (`r`) facts. -/
structure PC (r0 r : CallRec G s Ω) : Prop where
  U_sub : r.U ⊆ r0.U
  B_le : r.B ≤ r0.B
  lo_le : r0.Blow ≤ r.Blow
  hi_le : r.B' ≤ r0.B'
  lvl : r0.lvl = r.lvl + 1
  nbase : r0.base = false

/-- The invariant of a call log whose root is at level `L0`. -/
structure LogInv (τ : ℕ → ℕ) (L0 : ℕ) (lg : Log G s Ω) : Prop where
  nodup : (lg.map Prod.fst).Nodup
  facts : ∀ q r, (q, r) ∈ lg → RecFacts τ r
  depth : ∀ q r, (q, r) ∈ lg → r.lvl + q.length = L0
  parent : ∀ q r, (q, r) ∈ lg → q ≠ [] → ∃ r0, (q.dropLast, r0) ∈ lg ∧ PC r0 r
  sib : ∀ q a b r1 r2, (q ++ [a], r1) ∈ lg → (q ++ [b], r2) ∈ lg → a < b → r1.B' ≤ r2.Blow
  jump : ∀ q r, (q, r) ∈ lg → ∀ e ∈ r.J, ∃ a r', (q ++ [a], r') ∈ lg ∧ G.src e ∈ r'.U ∧
    r'.B ≤ eval G s e ∧ eval G s e < r.B
  wr : ∀ q r, (q, r) ∈ lg → ∀ e ∈ r.Wr, G.src e ∈ r.U ∧
    ∀ a r', (q ++ [a], r') ∈ lg → G.src e ∉ r'.U
  base : ∀ q r, (q, r) ∈ lg → r.base = true → ∀ a r', (q ++ [a], r') ∉ lg

/-- The log of a call `(Blow, B, S) ↦ res` at level `L0`: the invariant plus the root record. -/
structure CallLog (τ : ℕ → ℕ) (L0 : ℕ) (Blow B : WLab G s) (S : Finset (Fin G.n))
    (res : Result G s) (lg : Log G s Ω) : Prop where
  inv : LogInv τ L0 lg
  root : ∃ r, ([], r) ∈ lg ∧ r.lvl = L0 ∧ r.Blow = Blow ∧ r.B = B ∧ r.S = S ∧ r.B' = res.1 ∧
    r.U = res.2.1

/-- The log of the sub-calls of a loop at level `lv` with bound `B`, from iteration `i` and state
`σ` to state `σ'`, with window edges `J`. -/
structure LoopLog (τ : ℕ → ℕ) (lv : ℕ) (B : WLab G s) (i : ℕ) {p : ℕ} (σ σ' : LState G s p)
    (lg : Log G s Ω) (J : Finset (Fin G.m)) : Prop where
  nodup : (lg.map Prod.fst).Nodup
  shape : ∀ q r, (q, r) ∈ lg → ∃ j q', q = j :: q' ∧ i ≤ j
  facts : ∀ q r, (q, r) ∈ lg → RecFacts τ r
  depth : ∀ q r, (q, r) ∈ lg → r.lvl + q.length = lv
  parent : ∀ q r, (q, r) ∈ lg → q.dropLast ≠ [] → ∃ r0, (q.dropLast, r0) ∈ lg ∧ PC r0 r
  root : ∀ j r, ([j], r) ∈ lg → r.U ⊆ σ'.U ∧ Disjoint r.U σ.U ∧ r.B ≤ B ∧ σ.B' ≤ r.Blow ∧
    r.B' ≤ σ'.B'
  sib : ∀ q a b r1 r2, (q ++ [a], r1) ∈ lg → (q ++ [b], r2) ∈ lg → a < b → r1.B' ≤ r2.Blow
  jump : ∀ q r, (q, r) ∈ lg → ∀ e ∈ r.J, ∃ a r', (q ++ [a], r') ∈ lg ∧ G.src e ∈ r'.U ∧
    r'.B ≤ eval G s e ∧ eval G s e < r.B
  wr : ∀ q r, (q, r) ∈ lg → ∀ e ∈ r.Wr, G.src e ∈ r.U ∧
    ∀ a r', (q ++ [a], r') ∈ lg → G.src e ∉ r'.U
  base : ∀ q r, (q, r) ∈ lg → r.base = true → ∀ a r', (q ++ [a], r') ∉ lg
  Jwin : ∀ e ∈ J, ∃ j r, ([j], r) ∈ lg ∧ G.src e ∈ r.U ∧ r.B ≤ eval G s e ∧ eval G s e < B
  U_mono : σ.U ⊆ σ'.U
  B'_mono : σ.B' ≤ σ'.B'

end defs

/-! ## Lemmas on logs -/

section loglemmas

variable {Ω : Type}

theorem mem_shift {i : ℕ} {lg : Log G s Ω} {q : List ℕ} {r : CallRec G s Ω} :
    (q, r) ∈ lg.shift i ↔ ∃ q', q = i :: q' ∧ (q', r) ∈ lg := by
  unfold Log.shift
  rw [List.mem_map]
  constructor
  · rintro ⟨⟨q', r'⟩, hmem, heq⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨q', rfl, hmem⟩
  · rintro ⟨q', rfl, hmem⟩
    exact ⟨(q', r), hmem, rfl⟩

theorem map_fst_shift (i : ℕ) (lg : Log G s Ω) :
    (lg.shift i).map Prod.fst = (lg.map Prod.fst).map (List.cons i) := by
  unfold Log.shift
  rw [List.map_map, List.map_map]
  rfl

/-- Records are determined by their path in a log with distinct paths. -/
theorem rec_unique {lg : Log G s Ω} (h : (lg.map Prod.fst).Nodup) {q : List ℕ}
    {r1 r2 : CallRec G s Ω} (h1 : (q, r1) ∈ lg) (h2 : (q, r2) ∈ lg) : r1 = r2 := by
  have := List.inj_on_of_nodup_map h h1 h2 rfl
  simp only [Prod.mk.injEq, true_and] at this
  exact this


theorem card_le_of_groups {p : ℕ} {P : Fin p → Finset (Fin G.n)} {S : Finset (Fin G.n)}
    (hg : ∀ j, (P j).Nonempty ∧ P j ⊆ S) (hd : ∀ i j, i ≠ j → Disjoint (P i) (P j)) :
    p ≤ S.card := by
  classical
  have h1 : (Finset.univ.biUnion P).card = ∑ j, (P j).card := by
    apply Finset.card_biUnion
    intro i _ j _ hij
    exact hd i j hij
  have h2 : ∑ _j : Fin p, 1 ≤ ∑ j, (P j).card := Finset.sum_le_sum fun j _ => (hg j).1.card_pos
  have h3 : (Finset.univ.biUnion P).card ≤ S.card :=
    Finset.card_le_card (Finset.biUnion_subset.mpr fun j _ => (hg j).2)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h2
  omega

theorem cons_append_singleton (i : ℕ) (q : List ℕ) (a : ℕ) : (i :: q) ++ [a] = i :: (q ++ [a]) :=
  rfl

end loglemmas


/-! ## The log invariant holds for every derivation -/

section looplog

variable {Φ Ω : Type} {DC : DCost}

variable (G s) in
/-- Sub-calls at level `l` are correct and correctly logged. -/
def GoodSub (τ : ℕ → ℕ) (Inv : Φ → Prop) (l : ℕ) (sub : SubRelC G s Φ Ω) : Prop :=
  ∀ Blow B S d φ res φ' lg, CallPre B S d → Inv φ → (∀ x ∈ S, Blow ≤ dis (s := s) x) →
    Blow ≤ B → sub Blow B S d φ res φ' lg →
    CallPost G s B S d (τ l) res ∧ Inv φ' ∧ CallLog τ l Blow B S res lg

variable {B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {p : ℕ}
  {P0 : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {B'0 : WLab G s}

theorem loopC_log (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W)
    {τ : ℕ → ℕ} {Inv : Φ → Prop} {sub : SubRelC G s Φ Ω} {l : ℕ} (hsub : GoodSub G s τ Inv l sub)
    {τl : ℕ} :
    ∀ i (σ : LState G s p) φ σ' φ' lg J cm c,
      LoopC G s DC sub (l + 1) B τl i σ φ σ' φ' lg J cm c →
      LInv G s B S d0 d1 P0 B'0 σ → Inv φ →
      LInv G s B S d0 d1 P0 B'0 σ' ∧ (τl < σ'.U.card ∨ σ'.D.IsEmpty) ∧ Inv φ' ∧
        LoopLog τ (l + 1) B i σ σ' lg J := by
  intro i σ φ σ' φ' lg J cm c hloop
  induction hloop with
  | stop i σ φ hstop =>
    intro h hI
    refine ⟨h, hstop, hI, ⟨List.nodup_nil, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, subset_rfl, le_rfl⟩⟩ <;>
      simp
  | step i σ σ' φ φ1 φ' S0 Bi D1 B'i Ui Di dsub L' piv' lg lg' J' cm c _ hne hpull _ _ hsubrel
      hnd hmem hres _ ih =>
    intro h hI
    have hsp : CallPre Bi (expand σ S0 Bi) σ.d := step_pre hpre hfp h hpull
    have hlowdis : ∀ x ∈ expand σ S0 Bi, σ.B' ≤ dis (s := s) x :=
      fun x hx => (Si_facts h hpull hx).1.2.2
    have hSne : S0.Nonempty := by
      apply hpull.nonempty
      simp only [DS.IsEmpty, not_forall] at hne
      exact hne
    obtain ⟨x0, hx0⟩ := hSne
    have hx0S : x0 ∈ expand σ S0 Bi := mem_expand.mpr (Or.inl hx0)
    have hBlt : σ.B' < Bi := by
      obtain ⟨⟨-, -, hB⟩, hlt⟩ := Si_facts h hpull hx0S
      exact lt_of_le_of_lt (hB.trans (h.walk.sound x0)) hlt
    obtain ⟨hpost, hI1, hlog⟩ := hsub σ.B' Bi (expand σ S0 Bi) σ.d φ (B'i, Ui, Di, dsub) φ1 lg
      hsp hI hlowdis hBlt.le hsubrel
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
      window_scan_step hpull.bound hpost ((D1.merge Di).deleteSet Ui) hnd hmem'
    have hres' : Reselect σ Ui
        (L.foldl (relaxIns G s B (some Bi)) (dsub, (D1.merge Di).deleteSet Ui)).1 piv' := by
      rw [hfold]; exact hres
    have hnext := step_post hpre hfp h hne hpull hpost hL hres'
    rw [hfold] at hnext
    obtain ⟨h', hstop', hI', hll⟩ := ih hnext hI1
    refine ⟨h', hstop', hI', ?_⟩
    -- the root record of the sub-call
    obtain ⟨ri, hri, -, hriBlow, hriB, -, hriB', hriU⟩ := hlog.root
    have hriB'' : ri.B' = B'i := hriB'
    have hriU' : ri.U = Ui := hriU
    have hUi_disj : Disjoint Ui σ.U := by
      rw [Finset.disjoint_left]
      intro v hv hvU
      have hv' : v ∈ Utilde Bi (expand σ S0 Bi : Set (Fin G.n)) :=
        utilde_mono_bound hpost.B'_le ((hpost.U_eq v).mp hv)
      exact (UKi_sub h hpull hv').2.1 hvU
    have hB'ge : σ.B' ≤ B'i := hpost.B'_ge σ.B' hBlt.le hlowdis
    have hUmono' : σ.U ∪ Ui ⊆ σ'.U := hll.U_mono
    have hB'mono' : B'i ≤ σ'.B' := hll.B'_mono
    have hmemc : ∀ q r, (q, r) ∈ lg.shift i ++ lg' ↔
        (∃ q', q = i :: q' ∧ (q', r) ∈ lg) ∨ (q, r) ∈ lg' := by
      intro q r; rw [List.mem_append, mem_shift]
    have hshape' : ∀ q r, (q, r) ∈ lg' → ∃ j q', q = j :: q' ∧ i + 1 ≤ j := hll.shape
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- nodup
      rw [List.map_append, map_fst_shift, List.nodup_append]
      refine ⟨hlog.inv.nodup.map (fun a b h => List.cons_injective h), hll.nodup, ?_⟩
      intro a ha b hb hab
      obtain ⟨q', -, rfl⟩ := List.mem_map.mp ha
      obtain ⟨⟨qb, rb⟩, hqb, rfl⟩ := List.mem_map.mp hb
      obtain ⟨j, q'', hq, hj⟩ := hshape' qb rb hqb
      have h1 : i :: q' = qb := hab
      rw [hq] at h1
      have := (List.cons.inj h1).1
      omega
    · -- shape
      intro q r hqr
      rcases (hmemc q r).mp hqr with ⟨q', rfl, -⟩ | h2
      · exact ⟨i, q', rfl, le_rfl⟩
      · obtain ⟨j, q', hq, hj⟩ := hshape' q r h2
        exact ⟨j, q', hq, by omega⟩
    · -- facts
      intro q r hqr
      rcases (hmemc q r).mp hqr with ⟨q', -, h1⟩ | h2
      · exact hlog.inv.facts q' r h1
      · exact hll.facts q r h2
    · -- depth
      intro q r hqr
      rcases (hmemc q r).mp hqr with ⟨q', rfl, h1⟩ | h2
      · have := hlog.inv.depth q' r h1
        simp only [List.length_cons]
        omega
      · exact hll.depth q r h2
    · -- parent
      intro q r hqr hq
      rcases (hmemc q r).mp hqr with ⟨q', rfl, h1⟩ | h2
      · have hq' : q' ≠ [] := by
          rintro rfl; exact hq rfl
        obtain ⟨r0, hr0, hpc⟩ := hlog.inv.parent q' r h1 hq'
        refine ⟨r0, ?_, hpc⟩
        rw [List.dropLast_cons_of_ne_nil hq']
        exact (hmemc _ _).mpr (Or.inl ⟨q'.dropLast, rfl, hr0⟩)
      · obtain ⟨r0, hr0, hpc⟩ := hll.parent q r h2 hq
        exact ⟨r0, List.mem_append_right _ hr0, hpc⟩
    · -- root
      intro j r hjr
      rcases (hmemc [j] r).mp hjr with ⟨q', hq, h1⟩ | h2
      · have hq' : q' = [] := (List.cons.inj hq).2.symm
        subst hq'
        have hr : r = ri := rec_unique hlog.inv.nodup h1 hri
        subst hr
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hriU']; exact Finset.subset_union_right.trans hUmono'
        · rw [hriU']; exact hUi_disj
        · rw [hriB]; exact hpull.bound
        · exact le_of_eq hriBlow.symm
        · rw [hriB'']; exact hB'mono'
      · obtain ⟨h1, h2', h3, h4, h5⟩ := hll.root j r h2
        have h2'' : Disjoint r.U (σ.U ∪ Ui) := h2'
        have h4' : B'i ≤ r.Blow := h4
        exact ⟨h1, Disjoint.mono_right Finset.subset_union_left h2'', h3, hB'ge.trans h4', h5⟩
    · -- sib
      intro q a b r1 r2 h1 h2 hab
      rcases (hmemc _ _).mp h1 with ⟨q1, hq1, h1'⟩ | h1'
      · rcases (hmemc _ _).mp h2 with ⟨q2, hq2, h2'⟩ | h2'
        · rcases q with _ | ⟨k, q0⟩
          · have ha : a = i := (List.cons.inj hq1).1
            have hb : b = i := (List.cons.inj hq2).1
            omega
          · have hk1 := List.cons.inj hq1
            have hk2 := List.cons.inj hq2
            rw [← hk1.2] at h1'
            rw [← hk2.2] at h2'
            exact hlog.inv.sib q0 a b r1 r2 h1' h2' hab
        · rcases q with _ | ⟨k, q0⟩
          · have hq1' : q1 = [] := (List.cons.inj hq1).2.symm
            subst hq1'
            have hr1 : r1 = ri := rec_unique hlog.inv.nodup h1' hri
            subst hr1
            obtain ⟨-, -, -, h4, -⟩ := hll.root b r2 h2'
            have h4' : B'i ≤ r2.Blow := h4
            rw [hriB'']; exact h4'
          · have hk1 := (List.cons.inj hq1).1
            obtain ⟨j, q'', hq, hj⟩ := hshape' _ _ h2'
            have hk2 := (List.cons.inj hq).1
            omega
      · rcases (hmemc _ _).mp h2 with ⟨q2, hq2, h2'⟩ | h2'
        · obtain ⟨j, q'', hq, hj⟩ := hshape' _ _ h1'
          rcases q with _ | ⟨k, q0⟩
          · have ha : a = j := (List.cons.inj hq).1
            have hb : b = i := (List.cons.inj hq2).1
            omega
          · have hk1 := (List.cons.inj hq).1
            have hk2 := (List.cons.inj hq2).1
            omega
        · exact hll.sib q a b r1 r2 h1' h2' hab
    · -- jump
      intro q r hqr e he
      rcases (hmemc q r).mp hqr with ⟨q', rfl, h1⟩ | h2
      · obtain ⟨a, r', h1', hsrc, hlo, hhi⟩ := hlog.inv.jump q' r h1 e he
        exact ⟨a, r', (hmemc _ _).mpr (Or.inl ⟨q' ++ [a], rfl, h1'⟩), hsrc, hlo, hhi⟩
      · obtain ⟨a, r', h1', hsrc, hlo, hhi⟩ := hll.jump q r h2 e he
        exact ⟨a, r', List.mem_append_right _ h1', hsrc, hlo, hhi⟩
    · -- wr
      intro q r hqr e he
      rcases (hmemc q r).mp hqr with ⟨q', rfl, h1⟩ | h2
      · obtain ⟨hsrc, hch⟩ := hlog.inv.wr q' r h1 e he
        refine ⟨hsrc, fun a r' h' => ?_⟩
        rcases (hmemc _ _).mp h' with ⟨q'', hq'', h''⟩ | h''
        · have : q' ++ [a] = q'' := (List.cons.inj hq'').2
          rw [← this] at h''
          exact hch a r' h''
        · obtain ⟨j, q3, hq3, hj⟩ := hshape' _ _ h''
          have := (List.cons.inj hq3).1
          omega
      · obtain ⟨hsrc, hch⟩ := hll.wr q r h2 e he
        refine ⟨hsrc, fun a r' h' => ?_⟩
        rcases (hmemc _ _).mp h' with ⟨q'', hq'', h''⟩ | h''
        · obtain ⟨j, q3, hq3, hj⟩ := hshape' q r h2
          rw [hq3] at hq''
          have := (List.cons.inj hq'').1
          omega
        · exact hch a r' h''
    · -- base
      intro q r hqr hb a r' h'
      rcases (hmemc q r).mp hqr with ⟨q', rfl, h1⟩ | h2
      · rcases (hmemc _ _).mp h' with ⟨q'', hq'', h''⟩ | h''
        · have : q' ++ [a] = q'' := (List.cons.inj hq'').2
          rw [← this] at h''
          exact hlog.inv.base q' r h1 hb a r' h''
        · obtain ⟨j, q3, hq3, hj⟩ := hshape' _ _ h''
          have := (List.cons.inj hq3).1
          omega
      · rcases (hmemc _ _).mp h' with ⟨q'', hq'', h''⟩ | h''
        · obtain ⟨j, q3, hq3, hj⟩ := hshape' q r h2
          rw [hq3] at hq''
          have := (List.cons.inj hq'').1
          omega
        · exact hll.base q r h2 hb a r' h''
    · -- Jwin
      intro e he
      rcases Finset.mem_union.mp he with h1 | h2
      · have h1' := (hmem' e).mp (List.mem_toFinset.mp h1)
        refine ⟨i, ri, (hmemc _ _).mpr (Or.inl ⟨[], rfl, hri⟩), ?_, ?_, h1'.2.2⟩
        · rw [hriU']; exact h1'.1
        · rw [hriB]; exact h1'.2.1
      · obtain ⟨j, r, h1, h2', h3, h4⟩ := hll.Jwin e h2
        exact ⟨j, r, List.mem_append_right _ h1, h2', h3, h4⟩
    · exact Finset.subset_union_left.trans hUmono'
    · exact hB'ge.trans hB'mono'

end looplog


section calllog

variable {Φ Ω : Type} {DC : DCost}
variable {B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s}

theorem mem_cons_nonempty {Ω : Type} {r0 : CallRec G s Ω} {lg : Log G s Ω} {q : List ℕ}
    {r : CallRec G s Ω} (h : (q, r) ∈ ([], r0) :: lg) (hq : q ≠ []) : (q, r) ∈ lg := by
  rcases List.mem_cons.mp h with h1 | h1
  · exact absurd (Prod.mk.inj h1).1 hq
  · exact h1

/-- **The log of a recursive call.** -/
theorem callC_log {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} (hFPC : FPCSound G s FPC Inv)
    {τ : ℕ → ℕ} {sub : SubRelC G s Φ Ω} {l : ℕ} (hsub : GoodSub G s τ Inv l sub)
    {Blow : WLab G s} {φ0 φ2 : Φ} {res : Result G s} {lg : Log G s Ω}
    (hpre : CallPre B S d0) (hI : Inv φ0) (hlow : ∀ x ∈ S, Blow ≤ dis (s := s) x)
    (hBlowB : Blow ≤ B)
    (hrel : CallC G s FPC DC sub (l + 1) Blow B S d0 φ0 (τ (l + 1)) res φ2 lg) :
    CallPost G s B S d0 (τ (l + 1)) res ∧ Inv φ2 ∧ CallLog τ (l + 1) Blow B S res lg := by
  obtain ⟨d1, p, P, Q, W, φ1, ω, cfp, piv, σ, lgc, J, cm, cl, L, B'f, T6, W', hfprel, hpiv,
    hloop, hB'e, hB'n, hT6, hW', hL, rfl, rfl⟩ := hrel
  have hlow' : ∀ x ∈ S, Blow ≤ d0 x := fun x hx => (hlow x hx).trans (hpre.walk.sound x)
  obtain ⟨hfp, hI1⟩ := hFPC _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpre hI hlow' hfprel
  have h0 := linv_init hpre hfp hpiv
  obtain ⟨h, hstop, hI2, hll⟩ := loopC_log hpre hfp hsub _ _ _ _ _ _ _ _ _ hloop h0 hI1
  have hpost1 := final_post hpre hfp hpiv h hstop hB'e hB'n hT6 hW' hL
  have hpost := hpost1.of_cap_le (Nat.le_succ _)
  refine ⟨hpost, hI2, ?_⟩
  have hB'fle : B'f ≤ B := hpost.B'_le
  have hσB'f : σ.B' ≤ B'f := by
    by_cases he : σ.D.IsEmpty
    · rw [hB'e he]; exact h.B'_le
    · rw [hB'n he]
  have hBlow0 : Blow ≤ initB' B d1 piv :=
    le_min hBlowB (Finset.le_inf fun j _ =>
      (hlow (piv j) ((hfp.groups j).2 (hpiv j).1)).trans (hfp.walk.sound (piv j)))
  set rr : CallRec G s Ω :=
    { lvl := l + 1, Blow := Blow, B := B, S := S, B' := B'f,
      U := σ.U ∪ W', base := false, p := p, Q := Q, W := W, W' := W', J := J,
      Wr := L.toFinset, fp := some ω, cFP := cfp, cMerge := cm,
      cost := cfp + initCost DC (l + 1) p P + cl + cm
        + finCost DC (l + 1) p P S W T6 W' L.length } with hrr
  have hfacts : RecFacts τ rr := by
    refine ⟨hB'fle, hlow, ?_, ?_, ?_, ?_, Finset.subset_union_right, hfp.qsub,
      card_le_of_groups hfp.groups hfp.gdisj⟩
    · intro v hv
      obtain ⟨-, y, hy, hyv⟩ := (hpost.U_eq v).mp hv
      exact (hlow y hy).trans hyv.dis_le
    · intro v hv
      exact ((hpost.U_eq v).mp hv).1
    · intro heq x hx
      have heq' : B'f = B := heq
      have hx' := S_sub_of_pre hpre x hx
      show x ∈ σ.U ∪ W'
      have : x ∈ Utilde B'f (S : Set (Fin G.n)) := by rw [heq']; exact hx'
      exact (hpost.U_eq x).mpr this
    · intro hlt
      exact hpost.partial_card hlt
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨rr, List.mem_cons_self .., rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  · -- nodup
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, hll.nodup⟩
    intro hmem
    obtain ⟨⟨q, r⟩, hqr, hq⟩ := List.mem_map.mp hmem
    obtain ⟨j, q', hq', -⟩ := hll.shape q r hqr
    have : q = [] := hq
    rw [hq'] at this
    exact List.cons_ne_nil _ _ this
  · -- facts
    intro q r hqr
    rcases List.mem_cons.mp hqr with h1 | h1
    · rw [(Prod.mk.inj h1).2]; exact hfacts
    · exact hll.facts q r h1
  · -- depth
    intro q r hqr
    rcases List.mem_cons.mp hqr with h1 | h1
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
      rfl
    · exact hll.depth q r h1
  · -- parent
    intro q r hqr hq
    have h1 := mem_cons_nonempty hqr hq
    by_cases hdl : q.dropLast = []
    · obtain ⟨j, q', rfl, -⟩ := hll.shape q r h1
      have hq' : q' = [] := by
        by_contra hne
        rw [List.dropLast_cons_of_ne_nil hne] at hdl
        exact List.cons_ne_nil _ _ hdl
      subst hq'
      refine ⟨rr, ?_, ?_⟩
      · rw [hdl]; exact List.mem_cons_self ..
      obtain ⟨hU, -, hB, hlo, hhi⟩ := hll.root j r h1
      have hd := hll.depth [j] r h1
      simp only [List.length_cons, List.length_nil] at hd
      exact ⟨hU.trans Finset.subset_union_left, hB, hBlow0.trans hlo, hhi.trans hσB'f,
        by show l + 1 = r.lvl + 1; omega, rfl⟩
    · obtain ⟨r0, hr0, hpc⟩ := hll.parent q r h1 hdl
      exact ⟨r0, List.mem_cons_of_mem _ hr0, hpc⟩
  · -- sib
    intro q a b r1 r2 h1 h2 hab
    exact hll.sib q a b r1 r2 (mem_cons_nonempty h1 (by simp)) (mem_cons_nonempty h2 (by simp)) hab
  · -- jump
    intro q r hqr e he
    rcases List.mem_cons.mp hqr with h1 | h1
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
      obtain ⟨j, r', h1', hsrc, hlo, hhi⟩ := hll.Jwin e he
      exact ⟨j, r', List.mem_cons_of_mem _ h1', hsrc, hlo, hhi⟩
    · obtain ⟨a, r', h1', hsrc, hlo, hhi⟩ := hll.jump q r h1 e he
      exact ⟨a, r', List.mem_cons_of_mem _ h1', hsrc, hlo, hhi⟩
  · -- wr
    intro q r hqr e he
    rcases List.mem_cons.mp hqr with h1 | h1
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
      have hsW : G.src e ∈ W' := (hL.2 e).mp (List.mem_toFinset.mp he)
      refine ⟨Finset.mem_union_right _ hsW, fun a r' h' => ?_⟩
      have h'' := mem_cons_nonempty h' (by simp)
      obtain ⟨hU, -⟩ := hll.root a r' h''
      intro hsrc
      exact ((hW' _).mp hsW).1.2 (hU hsrc)
    · obtain ⟨hsrc, hch⟩ := hll.wr q r h1 e he
      exact ⟨hsrc, fun a r' h' => hch a r' (mem_cons_nonempty h' (by simp))⟩
  · -- base
    intro q r hqr hb a r' h'
    rcases List.mem_cons.mp hqr with h1 | h1
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
      exact absurd hb (by simp [hrr])
    · exact hll.base q r h1 hb a r' (mem_cons_nonempty h' (by simp))

/-- **The log of a base call.** -/
theorem baseC_log {τ : ℕ → ℕ} {Blow : WLab G s} {φ0 φ1 : Φ} {res : Result G s}
    {lg : Log G s Ω} (hpre : CallPre B S d0) (hlow : ∀ x ∈ S, Blow ≤ dis (s := s) x)
    (hrel : BaseC G s DC Blow B S d0 φ0 (τ 0) res φ1 lg) :
    CallPost G s B S d0 (τ 0) res ∧ φ1 = φ0 ∧ CallLog τ 0 Blow B S res lg := by
  obtain ⟨hb, hφ⟩ := baseC_erase hrel
  have hpost := baseRel_post hpre hb
  refine ⟨hpost, hφ, ?_⟩
  obtain ⟨st, c, -, -, -, -, -, -, -, rfl⟩ := hrel
  set rr : CallRec G s Ω :=
    { lvl := 0, Blow := Blow, B := B, S := S, B' := res.1,
      U := res.2.1, base := true, p := 0, Q := ∅, W := ∅, W' := ∅, J := ∅, Wr := ∅,
      fp := none, cFP := 0, cMerge := 0, cost := S.card * (1 + DC.bins) + c + 1 } with hrr
  have hfacts : RecFacts τ rr := by
    refine ⟨hpost.B'_le, hlow, ?_, ?_, ?_, hpost.partial_card, by simp [hrr], by simp [hrr],
      by simp [hrr]⟩
    · intro v hv
      obtain ⟨-, y, hy, hyv⟩ := (hpost.U_eq v).mp hv
      exact (hlow y hy).trans hyv.dis_le
    · intro v hv
      exact ((hpost.U_eq v).mp hv).1
    · intro heq x hx
      have hx' := S_sub_of_pre hpre x hx
      have : x ∈ Utilde res.1 (S : Set (Fin G.n)) := by
        show x ∈ Utilde rr.B' (S : Set (Fin G.n)); rw [heq]; exact hx'
      exact (hpost.U_eq x).mpr this
  have hsingle : ∀ (q : List ℕ) (r : CallRec G s Ω), (q, r) ∈ [([], rr)] → q = [] ∧ r = rr := by
    intro q r h
    rw [List.mem_singleton] at h
    exact ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2⟩
  refine ⟨⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨rr, List.mem_singleton_self _, rfl, rfl, rfl, rfl,
    rfl, rfl⟩⟩
  · intro q r h; rw [(hsingle q r h).2]; exact hfacts
  · intro q r h; obtain ⟨rfl, rfl⟩ := hsingle q r h; rfl
  · intro q r h hq; exact absurd (hsingle q r h).1 hq
  · intro q a b r1 r2 h1 _ _
    exact absurd (hsingle _ _ h1).1 (by simp)
  · intro q r h e he
    rw [(hsingle q r h).2] at he
    simp [hrr] at he
  · intro q r h e he
    rw [(hsingle q r h).2] at he
    simp [hrr] at he
  · intro q r h _ a r' h'
    exact absurd (hsingle _ _ h').1 (by simp)

/-- **Every derivation of the cost-indexed relation is correct and correctly logged.** -/
theorem bmsspC_log {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} (hFPC : FPCSound G s FPC Inv)
    (τ : ℕ → ℕ) : ∀ l, GoodSub G s τ Inv l (BMSSPC G s FPC DC τ l)
  | 0 => by
    intro Blow B S d φ res φ' lg hpre hI hlow _ hrel
    obtain ⟨hpost, rfl, hlog⟩ := baseC_log hpre hlow hrel
    exact ⟨hpost, hI, hlog⟩
  | l + 1 => by
    intro Blow B S d φ res φ' lg hpre hI hlow hBB hrel
    exact callC_log hFPC (bmsspC_log hFPC τ l) hpre hI hlow hBB hrel

end calllog


/-! ## The call forest, the handled ranges and the L4-owned counters -/

section forest

variable {Ω : Type} {τ : ℕ → ℕ} {L0 : ℕ} {lg : Log G s Ω}

/-- The call paths of a log. -/
def Log.paths (lg : Log G s Ω) : Finset (List ℕ) := (lg.map Prod.fst).toFinset

theorem mem_paths {q : List ℕ} : q ∈ lg.paths ↔ ∃ r, (q, r) ∈ lg := by
  unfold Log.paths
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨⟨q', r⟩, h, rfl⟩; exact ⟨r, h⟩
  · rintro ⟨r, h⟩; exact ⟨(q, r), h, rfl⟩

/-- The calls of a log (its paths). -/
abbrev Log.Call (lg : Log G s Ω) := {q : List ℕ // q ∈ lg.paths}

/-- The record of a call. -/
noncomputable def Log.recOf (lg : Log G s Ω) (X : lg.Call) : CallRec G s Ω :=
  Classical.choose (mem_paths.mp X.2)

theorem recOf_mem (X : lg.Call) : (X.1, lg.recOf X) ∈ lg :=
  Classical.choose_spec (mem_paths.mp X.2)

theorem recOf_eq (h : (lg.map Prod.fst).Nodup) {X : lg.Call} {r : CallRec G s Ω}
    (hr : (X.1, r) ∈ lg) : lg.recOf X = r :=
  rec_unique h (recOf_mem X) hr

theorem exists_concat_of_ne_nil {q : List ℕ} (h : q ≠ []) : ∃ q' a, q = q' ++ [a] := by
  rcases List.eq_nil_or_concat q with h' | ⟨q', a, h'⟩
  · exact absurd h' h
  · exact ⟨q', a, by rw [h', List.concat_eq_append]⟩

/-- The parent of a call: the path without its last index. -/
noncomputable def Log.parentOf (hL : LogInv τ L0 lg) (X : lg.Call) : Option lg.Call :=
  if h : X.1 = [] then none else
    some ⟨X.1.dropLast,
      mem_paths.mpr ⟨_, (hL.parent X.1 (lg.recOf X) (recOf_mem X) h).choose_spec.1⟩⟩

theorem parentOf_some (hL : LogInv τ L0 lg) {X Y : lg.Call} :
    Log.parentOf hL X = some Y ↔ X.1 ≠ [] ∧ Y.1 = X.1.dropLast := by
  unfold Log.parentOf
  split_ifs with h
  · simp [h]
  · simp only [Option.some.injEq]
    constructor
    · rintro rfl; exact ⟨h, rfl⟩
    · rintro ⟨-, hY⟩; exact Subtype.ext hY.symm

theorem parentOf_none (hL : LogInv τ L0 lg) {X : lg.Call} :
    Log.parentOf hL X = none ↔ X.1 = [] := by
  unfold Log.parentOf
  split_ifs with h
  · simp [h]
  · simp [h]

/-- The parent's record is the parent of the record. -/
theorem parent_pc (hL : LogInv τ L0 lg) {X Y : lg.Call} (h : Log.parentOf hL X = some Y) :
    PC (lg.recOf Y) (lg.recOf X) := by
  obtain ⟨hne, hY⟩ := (parentOf_some hL).mp h
  obtain ⟨r0, hr0, hpc⟩ := hL.parent X.1 (lg.recOf X) (recOf_mem X) hne
  have : lg.recOf Y = r0 := recOf_eq hL.nodup (by rw [hY]; exact hr0)
  rw [this]; exact hpc

/-- Children are the one-index extensions. -/
theorem parentOf_child (hL : LogInv τ L0 lg) {X Y : lg.Call} (h : Log.parentOf hL Y = some X) :
    ∃ a, Y.1 = X.1 ++ [a] := by
  obtain ⟨hne, hX⟩ := (parentOf_some hL).mp h
  obtain ⟨q', a, hq⟩ := exists_concat_of_ne_nil hne
  refine ⟨a, ?_⟩
  rw [hX, hq, List.dropLast_concat]

theorem child_parentOf (hL : LogInv τ L0 lg) {X : lg.Call} {a : ℕ} {r : CallRec G s Ω}
    (h : (X.1 ++ [a], r) ∈ lg) :
    Log.parentOf hL ⟨X.1 ++ [a], mem_paths.mpr ⟨r, h⟩⟩ = some X :=
  (parentOf_some hL).mpr ⟨by simp, by rw [List.dropLast_concat]⟩

/-- Siblings have disjoint returned sets. -/
theorem sib_disjoint (hL : LogInv τ L0 lg) {q : List ℕ} {a b : ℕ} {r1 r2 : CallRec G s Ω}
    (h1 : (q ++ [a], r1) ∈ lg) (h2 : (q ++ [b], r2) ∈ lg) (hab : a ≠ b) : Disjoint r1.U r2.U := by
  rw [Finset.disjoint_left]
  intro v hv1 hv2
  rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
  · have hs := hL.sib q a b r1 r2 h1 h2 hlt
    have e1 := (hL.facts _ _ h1).U_high v hv1
    have e2 := (hL.facts _ _ h2).U_low v hv2
    exact absurd (lt_of_lt_of_le e1 (hs.trans e2)) (lt_irrefl _)
  · have hs := hL.sib q b a r2 r1 h2 h1 hlt
    have e1 := (hL.facts _ _ h2).U_high v hv2
    have e2 := (hL.facts _ _ h1).U_low v hv1
    exact absurd (lt_of_lt_of_le e1 (hs.trans e2)) (lt_irrefl _)

/-- Sibling calls with a common parent are one-index extensions of the same path. -/
theorem siblings_split (hL : LogInv τ L0 lg) {X X' Y : lg.Call}
    (h : Log.parentOf hL X = some Y) (h' : Log.parentOf hL X' = some Y) (hne : X ≠ X') :
    ∃ a b, X.1 = Y.1 ++ [a] ∧ X'.1 = Y.1 ++ [b] ∧ a ≠ b := by
  obtain ⟨a, ha⟩ := parentOf_child hL h
  obtain ⟨b, hb⟩ := parentOf_child hL h'
  refine ⟨a, b, ha, hb, fun hab => hne (Subtype.ext ?_)⟩
  rw [ha, hb, hab]

/-- **Tracker O1**: the call forest of a logged run. -/
noncomputable def Log.forest (hL : LogInv τ L0 lg) :
    CostCharging.CallForest lg.Call (Fin G.n) (WLab G s) where
  parent := Log.parentOf hL
  depth X := X.1.length
  U X := (lg.recOf X).U
  B X := (lg.recOf X).B
  depth_parent X Y h := by
    obtain ⟨hne, hY⟩ := (parentOf_some hL).mp h
    show X.1.length = Y.1.length + 1
    rw [hY, List.length_dropLast]
    have : X.1.length ≠ 0 := fun h0 => hne (List.length_eq_zero_iff.mp h0)
    omega
  depth_root X h := by
    show X.1.length = 0
    rw [(parentOf_none hL).mp h]; rfl
  U_sub X Y h := (parent_pc hL h).U_sub
  B_le X Y h := (parent_pc hL h).B_le
  siblings_disjoint X X' Y h h' hne := by
    obtain ⟨a, b, ha, hb, hab⟩ := siblings_split hL h h' hne
    have h1 : (Y.1 ++ [a], lg.recOf X) ∈ lg := ha ▸ recOf_mem X
    have h2 : (Y.1 ++ [b], lg.recOf X') ∈ lg := hb ▸ recOf_mem X'
    exact sib_disjoint hL h1 h2 hab
  roots_disjoint X X' h h' hne := by
    exfalso; apply hne
    exact Subtype.ext (((parentOf_none hL).mp h).trans ((parentOf_none hL).mp h').symm)

/-- **Tracker O2**: the handled ranges `[B_low X, B'_X)` of a logged run. -/
noncomputable def Log.ranges (hL : LogInv τ L0 lg) : Density.Ranges (Log.forest hL) where
  lo X := (lg.recOf X).Blow
  hi X := (lg.recOf X).B'
  lo_le X Y h := (parent_pc hL h).lo_le
  hi_le X Y h := (parent_pc hL h).hi_le
  sib X X' Y h h' hne c h1 h2 h3 h4 := by
    obtain ⟨a, b, ha, hb, hab⟩ := siblings_split hL h h' hne
    have m1 : (Y.1 ++ [a], lg.recOf X) ∈ lg := ha ▸ recOf_mem X
    have m2 : (Y.1 ++ [b], lg.recOf X') ∈ lg := hb ▸ recOf_mem X'
    rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
    · have hs := hL.sib _ a b _ _ m1 m2 hlt
      exact absurd (lt_of_lt_of_le h2 (hs.trans h3)) (lt_irrefl _)
    · have hs := hL.sib _ b a _ _ m2 m1 hlt
      exact absurd (lt_of_lt_of_le h4 (hs.trans h1)) (lt_irrefl _)
  roots X X' h h' hne := by
    exfalso; apply hne
    exact Subtype.ext (((parentOf_none hL).mp h).trans ((parentOf_none hL).mp h').symm)

/-- The counters of a logged run (`CostAggregate.CallCounters`).  The FindPivots/partition
counters `Fo, Cr, Be, Del` are read off the records by the given functions (packages L2/PT). -/
noncomputable def Log.counters (hL : LogInv τ L0 lg)
    (Fo : CallRec G s Ω → Finset (Fin G.n)) (Cr Be Del : CallRec G s Ω → Finset (Fin G.m)) :
    CostAggregate.CallCounters lg.Call (Fin G.n) (Fin G.m) (WLab G s) where
  F := Log.forest hL
  src := G.src
  dst := G.dst
  val := eval G s
  full X := decide ((lg.recOf X).B' = (lg.recOf X).B)
  S X := (lg.recOf X).S
  Q X := (lg.recOf X).Q
  Fo X := Fo (lg.recOf X)
  J X := (lg.recOf X).J
  Wr X := (lg.recOf X).Wr
  Cr X := Cr (lg.recOf X)
  Be X := Be (lg.recOf X)
  Del X := Del (lg.recOf X)
  p X := (lg.recOf X).p
  mergeCost X := (lg.recOf X).cMerge
  cost X := (lg.recOf X).cost
  base X := (lg.recOf X).base

variable (hL : LogInv τ L0 lg) (Fo : CallRec G s Ω → Finset (Fin G.n))
  (Cr Be Del : CallRec G s Ω → Finset (Fin G.m))

/-- `Valid.jump_window` (DMSY26 Obs. 3.5 input). -/
theorem counters_jump_window : ∀ X, ∀ e ∈ (Log.counters hL Fo Cr Be Del).J X,
    ∃ Y, (Log.counters hL Fo Cr Be Del).F.parent Y = some X ∧
      (Log.counters hL Fo Cr Be Del).src e ∈ (Log.counters hL Fo Cr Be Del).F.U Y ∧
      (Log.counters hL Fo Cr Be Del).F.B Y ≤ (Log.counters hL Fo Cr Be Del).val e ∧
      (Log.counters hL Fo Cr Be Del).val e < (Log.counters hL Fo Cr Be Del).F.B X := by
  intro X e he
  obtain ⟨a, r', h1, hsrc, hlo, hhi⟩ := hL.jump X.1 (lg.recOf X) (recOf_mem X) e he
  refine ⟨⟨X.1 ++ [a], mem_paths.mpr ⟨r', h1⟩⟩, child_parentOf hL h1, ?_, ?_, hhi⟩
  · show G.src e ∈ (lg.recOf _).U
    rw [recOf_eq hL.nodup h1]; exact hsrc
  · show (lg.recOf _).B ≤ eval G s e
    rw [recOf_eq hL.nodup h1]; exact hlo

/-- `Valid.wr_own`. -/
theorem counters_wr_own : ∀ X, ∀ e ∈ (Log.counters hL Fo Cr Be Del).Wr X,
    (Log.counters hL Fo Cr Be Del).Own X ((Log.counters hL Fo Cr Be Del).src e) := by
  intro X e he
  obtain ⟨hsrc, hch⟩ := hL.wr X.1 (lg.recOf X) (recOf_mem X) e he
  refine ⟨hsrc, fun Y hY => ?_⟩
  obtain ⟨a, ha⟩ := parentOf_child hL hY
  have hm : (X.1 ++ [a], lg.recOf Y) ∈ lg := ha ▸ recOf_mem Y
  exact hch a _ hm

/-- `Valid.full_S`. -/
theorem counters_full_S : ∀ X, (Log.counters hL Fo Cr Be Del).full X = true →
    (Log.counters hL Fo Cr Be Del).S X ⊆ (Log.counters hL Fo Cr Be Del).F.U X := by
  intro X hX
  have heq : (lg.recOf X).B' = (lg.recOf X).B := of_decide_eq_true hX
  exact (hL.facts _ _ (recOf_mem X)).full_S heq

/-- `Valid.base_leaf`. -/
theorem counters_base_leaf : ∀ X Y, (Log.counters hL Fo Cr Be Del).base X = true →
    (Log.counters hL Fo Cr Be Del).F.parent Y ≠ some X := by
  intro X Y hb hY
  obtain ⟨a, ha⟩ := parentOf_child hL hY
  have hm : (X.1 ++ [a], lg.recOf Y) ∈ lg := ha ▸ recOf_mem Y
  exact hL.base X.1 (lg.recOf X) (recOf_mem X) hb a _ hm

/-- `Valid.depth_le` with `Lmax = L0` (the level of the root). -/
theorem counters_depth_le : ∀ X, (Log.counters hL Fo Cr Be Del).F.depth X ≤ L0 := by
  intro X
  have := hL.depth X.1 (lg.recOf X) (recOf_mem X)
  show X.1.length ≤ L0
  omega

/-- `Valid.Q_sub`. -/
theorem counters_Q_sub : ∀ X, (Log.counters hL Fo Cr Be Del).Q X ⊆ (Log.counters hL Fo Cr Be Del).S X :=
  fun X => (hL.facts _ _ (recOf_mem X)).Q_sub

/-- `Valid.partial_p` (in fact for every call). -/
theorem counters_p_le : ∀ X, (Log.counters hL Fo Cr Be Del).p X ≤ ((Log.counters hL Fo Cr Be Del).S X).card :=
  fun X => (hL.facts _ _ (recOf_mem X)).p_le

/-- Partial calls return at least `τ` of their level. -/
theorem counters_partial_card : ∀ X, (Log.counters hL Fo Cr Be Del).full X = false →
    τ (lg.recOf X).lvl ≤ ((Log.counters hL Fo Cr Be Del).F.U X).card := by
  intro X hX
  have hne : (lg.recOf X).B' ≠ (lg.recOf X).B := of_decide_eq_false hX
  exact (hL.facts _ _ (recOf_mem X)).partial_card
    (lt_of_le_of_ne (hL.facts _ _ (recOf_mem X)).B'_le hne)

/-- The total cost of the log is the sum of the per-call costs. -/
theorem counters_cost_sum : ∑ X, (Log.counters hL Fo Cr Be Del).cost X = lg.cost := by
  classical
  show ∑ X : lg.Call, (lg.recOf X).cost = (lg.map fun x => x.2.cost).sum
  have hnd : (lg.map Prod.fst).Nodup := hL.nodup
  -- the map `x ↦ x.1` is a bijection from the entries of `lg` onto `lg.paths`
  have hnd' : lg.Nodup := List.Nodup.of_map _ hnd
  rw [← List.sum_toFinset _ hnd']
  refine Finset.sum_bij (fun X _ => (X.1, lg.recOf X)) ?_ ?_ ?_ ?_
  · intro X _; exact List.mem_toFinset.mpr (recOf_mem X)
  · intro X _ Y _ h
    exact Subtype.ext (Prod.mk.inj h).1
  · intro x hx
    have hx' := List.mem_toFinset.mp hx
    refine ⟨⟨x.1, mem_paths.mpr ⟨x.2, hx'⟩⟩, Finset.mem_univ _, ?_⟩
    show (x.1, lg.recOf _) = x
    rw [recOf_eq hL.nodup hx']
  · intro X _; rfl


/-- The counters with CALL-indexed FindPivots/partition counters (agent-03's homes-based `Cr`/`Be`
depend on the children, not only on the record). -/
noncomputable def Log.countersC (hL : LogInv τ L0 lg)
    (Fo : lg.Call → Finset (Fin G.n)) (Cr Be Del : lg.Call → Finset (Fin G.m)) :
    CostAggregate.CallCounters lg.Call (Fin G.n) (Fin G.m) (WLab G s) :=
  { Log.counters hL (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) with
    Fo := Fo, Cr := Cr, Be := Be, Del := Del }

section countersC

variable (Fo' : lg.Call → Finset (Fin G.n)) (Cr' Be' Del' : lg.Call → Finset (Fin G.m))

theorem countersC_jump_window : ∀ X, ∀ e ∈ (Log.countersC hL Fo' Cr' Be' Del').J X,
    ∃ Y, (Log.countersC hL Fo' Cr' Be' Del').F.parent Y = some X ∧
      (Log.countersC hL Fo' Cr' Be' Del').src e ∈ (Log.countersC hL Fo' Cr' Be' Del').F.U Y ∧
      (Log.countersC hL Fo' Cr' Be' Del').F.B Y ≤ (Log.countersC hL Fo' Cr' Be' Del').val e ∧
      (Log.countersC hL Fo' Cr' Be' Del').val e < (Log.countersC hL Fo' Cr' Be' Del').F.B X :=
  counters_jump_window hL (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) (fun _ => ∅)

theorem countersC_wr_own : ∀ X, ∀ e ∈ (Log.countersC hL Fo' Cr' Be' Del').Wr X,
    (Log.countersC hL Fo' Cr' Be' Del').Own X ((Log.countersC hL Fo' Cr' Be' Del').src e) :=
  counters_wr_own hL (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) (fun _ => ∅)

theorem countersC_full_S : ∀ X, (Log.countersC hL Fo' Cr' Be' Del').full X = true →
    (Log.countersC hL Fo' Cr' Be' Del').S X ⊆ (Log.countersC hL Fo' Cr' Be' Del').F.U X :=
  counters_full_S hL (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) (fun _ => ∅)

theorem countersC_base_leaf : ∀ X Y, (Log.countersC hL Fo' Cr' Be' Del').base X = true →
    (Log.countersC hL Fo' Cr' Be' Del').F.parent Y ≠ some X :=
  counters_base_leaf hL (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) (fun _ => ∅)

theorem countersC_depth_le : ∀ X, (Log.countersC hL Fo' Cr' Be' Del').F.depth X ≤ L0 :=
  counters_depth_le hL (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) (fun _ => ∅)

theorem countersC_Q_sub : ∀ X, (Log.countersC hL Fo' Cr' Be' Del').Q X ⊆
    (Log.countersC hL Fo' Cr' Be' Del').S X :=
  counters_Q_sub hL (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) (fun _ => ∅)

theorem countersC_p_le : ∀ X, (Log.countersC hL Fo' Cr' Be' Del').p X ≤
    ((Log.countersC hL Fo' Cr' Be' Del').S X).card :=
  counters_p_le hL (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) (fun _ => ∅)

theorem countersC_partial_card : ∀ X, (Log.countersC hL Fo' Cr' Be' Del').full X = false →
    τ (lg.recOf X).lvl ≤ ((Log.countersC hL Fo' Cr' Be' Del').F.U X).card :=
  counters_partial_card hL (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) (fun _ => ∅)

theorem countersC_cost_sum : ∑ X, (Log.countersC hL Fo' Cr' Be' Del').cost X = lg.cost :=
  counters_cost_sum hL (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) (fun _ => ∅)

end countersC

end forest


/-! ## The top-level run -/

section top

variable {Φ Ω : Type} {DC : DCost}

/-- **Top-level summary.**  A top-level run `BMSSP(⊤, {s}, l)` with `τ l > n` from the initial
labels is exact, preserves the persistent invariant, and its log satisfies `LogInv` (so it has a
call forest, handled ranges and the L4-owned counter facts); its cost index is the sum of the
per-call costs of the counters (`counters_cost_sum`). -/
theorem bmsspC_top {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} (hFPC : FPCSound G s FPC Inv)
    (τ : ℕ → ℕ) (l : ℕ) (hτ : G.n < τ l) {Blow : WLab G s} (hlow : Blow ≤ initLabels s s)
    {φ φ' : Φ} (hI : Inv φ) {res : Result G s} {lg : Log G s Ω}
    (hrel : BMSSPC G s FPC DC τ l Blow ⊤ {s} (initLabels s) φ res φ' lg) :
    (∀ v, Complete res.2.2.2 v) ∧ Inv φ' ∧ LogInv τ l lg := by
  obtain ⟨hex, hI'⟩ := bmsspC_top_exact hFPC τ l hτ hlow hI hrel
  have hlow' : ∀ x ∈ ({s} : Finset (Fin G.n)), Blow ≤ dis (s := s) x := by
    intro x hx
    rw [Finset.mem_singleton.mp hx, ← initLabels_source]
    exact hlow
  obtain ⟨-, -, hlog⟩ := bmsspC_log hFPC τ l Blow ⊤ {s} (initLabels s) φ res φ' lg callPre_top hI
    hlow' le_top hrel
  exact ⟨hex, hI', hlog.inv⟩

end top

end BM
end CHD
end Frontier
