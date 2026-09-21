import Frontier.CHD.QWit

/-!
# Frontier.CHD.QWitProv — local provenance of every traced derivation (tracker O22(a), part 2; owner agent-03)

**NON-GATE** (Layer A).  For every `BMSSPC` derivation (any FindPivots relation satisfying `FPCSound`) from
labels in which the source is complete, the log satisfies `LocalProv` and the keys of the returned store come from
the log (`RetProv`).  With `QWit.qwit_of_prov` this gives the `Q`-witness fields of `CostAggregate.Valid`.

Key facts: the keys of the loop store are pivots/re-selected pivots (in `S \ Q`), keys of returned child stores
(recursively: members of `S` of the child's log, or heads of its events), or heads of the window relaxations of
earlier iterations; a relaxation never inserts the source (its label is the empty walk).
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n} {Φ Ω : Type} {DC : DCost}

/-! ## Labels -/

section Labels

theorem dis_source : dis (s := s) s = ((toW ([] : List (Fin G.m)) : WalkOrd G s) : WLab G s) := by
  rw [dis_of_reachable ⟨[], IsWalk.nil s⟩, path_source]

/-- A valid relaxation never targets the source while the source is complete. -/
theorem valid_ne_source {d : Labels G s} (hw : WalkInv d) (hs : d s ≤ dis (s := s) s) {B : WLab G s}
    {e : Fin G.m} (hv : ValidRelax G s d B e) : G.dst e ≠ s := by
  intro hdst
  have hle := hv.1
  rw [hdst] at hle
  have h0 := (dis_source (G := G) (s := s))
  have hb := hle.trans (hs.trans h0.le)
  by_cases htop : d (G.src e) = ⊤
  · rw [htop, ext_top] at hb
    exact absurd hb (not_le.mpr (WithTop.coe_lt_top _))
  · obtain ⟨p, hp⟩ : ∃ p : List (Fin G.m), d (G.src e) = ((toW p : WalkOrd G s) : WLab G s) := by
      obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp htop
      exact ⟨a, ha.symm⟩
    rw [hp, ext_coe] at hb
    have hlt : (toW ([] : List (Fin G.m)) : WalkOrd G s) < toW (p ++ [e]) := by
      have := lt_append (s := s) (P := ([] : List (Fin G.m))) (R := p ++ [e]) (by simp)
      simpa using this
    exact absurd (WithTop.coe_le_coe.mp hb) (not_le.mpr hlt)

/-- The canonical value of an edge is at most its relaxation value under walk labels. -/
theorem eval_le_ext {d : Labels G s} (hw : WalkInv d) (e : Fin G.m) : eval G s e ≤ ext (d (G.src e)) e := by
  unfold eval
  by_cases htop : d (G.src e) = ⊤
  · rw [htop, ext_top]; exact le_top
  · obtain ⟨p, hp⟩ : ∃ p : List (Fin G.m), d (G.src e) = ((toW p : WalkOrd G s) : WLab G s) := by
      obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp htop
      exact ⟨a, ha.symm⟩
    have hwk : G.IsWalk s (G.src e) p := hw _ p hp
    have hreach : G.Reachable s (G.src e) := ⟨p, hwk⟩
    rw [hp, dis_of_reachable hreach]
    exact ext_le_ext (path_isMinWalk hreach).1 hwk ((path_isMinWalk hreach).2 p hwk) e rfl

/-- **Keys of a relaxation fold**: old keys, or heads of valid relaxations under smaller walk labels. -/
theorem foldl_keys (B : WLab G s) (lo : Option (WLab G s)) (P : Fin G.n → Prop) :
    ∀ (L : List (Fin G.m)) (st : Labels G s × DS G s), WalkInv st.1 →
      (∀ y, st.2 y ≠ none → P y) →
      (∀ e ∈ L, ∀ d' : Labels G s, WalkInv d' → (∀ v, d' v ≤ st.1 v) → ValidRelax G s d' B e →
        P (G.dst e)) →
      ∀ y, (L.foldl (relaxIns G s B lo) st).2 y ≠ none → P y := by
  intro L
  induction L with
  | nil => intro st _ h0 _ y hy; exact h0 y hy
  | cons e L ih =>
    intro st hw h0 hins y hy
    rw [List.foldl_cons] at hy
    have hle1 : ∀ v, (relaxIns G s B lo st e).1 v ≤ st.1 v := fun v => relaxIns_fst_le B lo st e v
    refine ih (relaxIns G s B lo st e) (relaxIns_walk B lo st e hw) ?_ ?_ y hy
    · intro y' hy'
      obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hy'
      rcases relaxIns_snd_cases B lo st e hk with h | ⟨rfl, hv, -, -⟩
      · exact h0 y' (by rw [h]; simp)
      · exact hins e List.mem_cons_self st.1 hw (fun _ => le_rfl) hv
    · intro e' he' d' hw' hd' hv'
      exact hins e' (List.mem_cons_of_mem _ he') d' hw' (fun v => (hd' v).trans (hle1 v)) hv'

end Labels

/-! ## Monotonicity of events and provenance in the log -/

section Mono

theorem isEvent_mono {lg lg' : Log G s Ω} (h : ∀ x, x ∈ lg → x ∈ lg') {e : Fin G.m} {α : List ℕ}
    (he : IsEvent lg e α) : IsEvent lg' e α := by
  obtain ⟨q, r, hq, hev, ha⟩ := he
  refine ⟨q, r, h _ hq, hev, ?_⟩
  rcases ha with ⟨hb, hJ, a, r', rfl, hr', hu⟩ | ha
  · exact Or.inl ⟨hb, hJ, a, r', rfl, h _ hr', hu⟩
  · exact Or.inr ha

theorem isEvent_shift {lg : Log G s Ω} (i : ℕ) {e : Fin G.m} {α : List ℕ} (he : IsEvent lg e α) :
    IsEvent (lg.shift i) e (i :: α) := by
  obtain ⟨q, r, hq, hev, ha⟩ := he
  refine ⟨i :: q, r, mem_shift.mpr ⟨q, rfl, hq⟩, hev, ?_⟩
  rcases ha with ⟨hb, hJ, a, r', rfl, hr', hu⟩ | ⟨rfl, hk⟩
  · exact Or.inl ⟨hb, hJ, a, r', rfl, mem_shift.mpr ⟨q ++ [a], rfl, hr'⟩, hu⟩
  · exact Or.inr ⟨rfl, hk⟩

theorem prov_mono {lg lg' : Log G s Ω} (h : ∀ x, x ∈ lg → x ∈ lg') {z : List ℕ} {i : ℕ} {v : Fin G.n}
    (hp : Prov lg z i v) : Prov lg' z i v := by
  rcases hp with ⟨e, α, hev, hd, hvs, a, α', hα, ha⟩ | ⟨y, r', hy, hvS, a, y', hy', ha⟩
  · exact Or.inl ⟨e, α, isEvent_mono h hev, hd, hvs, a, α', hα, ha⟩
  · exact Or.inr ⟨y, r', h _ hy, hvS, a, y', hy', ha⟩

theorem prov_shift {lg : Log G s Ω} (i : ℕ) {z : List ℕ} {j : ℕ} {v : Fin G.n} (hp : Prov lg z j v) :
    Prov (lg.shift i) (i :: z) j v := by
  rcases hp with ⟨e, α, hev, hd, hvs, a, α', rfl, ha⟩ | ⟨y, r', hy, hvS, a, y', rfl, ha⟩
  · exact Or.inl ⟨e, _, isEvent_shift i hev, hd, hvs, a, α', rfl, ha⟩
  · exact Or.inr ⟨i :: (z ++ a :: y'), r', mem_shift.mpr ⟨_, rfl, hy⟩, hvS, a, y', rfl, ha⟩

end Mono

/-! ## Provenance predicates -/

section Preds

variable (G s) in
/-- Returned-store provenance: every key is in `S` of a call of the log, or the head `≠ s` of an event. -/
def RetProv (lg : Log G s Ω) (D : DS G s) : Prop :=
  ∀ v, D v ≠ none → (∃ y r', (y, r') ∈ lg ∧ v ∈ r'.S) ∨ (∃ e α, IsEvent lg e α ∧ G.dst e = v ∧ v ≠ s)

/-- Loop provenance for iteration `j`: a window relaxation of an earlier iteration, an event of an earlier
sub-call subtree, or a member of `S` of such a subtree. -/
def LProv (lg : Log G s Ω) (J : Finset (Fin G.m)) (j : ℕ) (v : Fin G.n) : Prop :=
  (∃ e ∈ J, G.dst e = v ∧ v ≠ s ∧ ∃ a r', a < j ∧ ([a], r') ∈ lg ∧ G.src e ∈ r'.U) ∨
  (∃ e α, IsEvent lg e α ∧ G.dst e = v ∧ v ≠ s ∧ ∃ a α', α = a :: α' ∧ a < j) ∨
  (∃ y r', (y, r') ∈ lg ∧ v ∈ r'.S ∧ ∃ a y', y = a :: y' ∧ a < j)

theorem lprov_mono {lg lg' : Log G s Ω} (h : ∀ x, x ∈ lg → x ∈ lg') {J J' : Finset (Fin G.m)} (hJ : J ⊆ J')
    {j : ℕ} {v : Fin G.n} (hp : LProv lg J j v) : LProv lg' J' j v := by
  rcases hp with ⟨e, he, hd, hvs, a, r', ha, hr', hu⟩ | ⟨e, α, hev, hd, hvs, a, α', hα, ha⟩ |
      ⟨y, r', hy, hvS, a, y', hy', ha⟩
  · exact Or.inl ⟨e, hJ he, hd, hvs, a, r', ha, h _ hr', hu⟩
  · exact Or.inr (Or.inl ⟨e, α, isEvent_mono h hev, hd, hvs, a, α', hα, ha⟩)
  · exact Or.inr (Or.inr ⟨y, r', h _ hy, hvS, a, y', hy', ha⟩)

theorem lprov_le {lg : Log G s Ω} {J : Finset (Fin G.m)} {j j' : ℕ} (hjj : j ≤ j') {v : Fin G.n}
    (hp : LProv lg J j v) : LProv lg J j' v := by
  rcases hp with ⟨e, he, hd, hvs, a, r', ha, hr', hu⟩ | ⟨e, α, hev, hd, hvs, a, α', hα, ha⟩ |
      ⟨y, r', hy, hvS, a, y', hy', ha⟩
  · exact Or.inl ⟨e, he, hd, hvs, a, r', by omega, hr', hu⟩
  · exact Or.inr (Or.inl ⟨e, α, hev, hd, hvs, a, α', hα, by omega⟩)
  · exact Or.inr (Or.inr ⟨y, r', hy, hvS, a, y', hy', by omega⟩)

variable (G s) in
/-- Sub-derivations with provenance. -/
def SubProv (Inv : Φ → Prop) (sub : SubRelC G s Φ Ω) : Prop :=
  ∀ Blow B S d φ res φ' lg, CallPre B S d → Inv φ → (∀ x ∈ S, Blow ≤ dis (s := s) x) → Blow ≤ B →
    d s ≤ dis (s := s) s → sub Blow B S d φ res φ' lg → LocalProv lg ∧ RetProv G s lg res.2.2.1

end Preds

/-! ## The base case -/

section Base

variable {B : WLab G s} {τ : ℕ} {S : Finset (Fin G.n)}

/-- Keys of the base-case store: members of `S`, or heads `≠ s` of relaxations out of extracted vertices below
`B`. -/
theorem baseLoopC_keysP :
    ∀ {st st' : Labels G s × DS G s × Finset (Fin G.n)} {c : ℕ}, BaseLoopC G s DC B τ st st' c →
      WalkInv st.1 → st.1 s ≤ dis (s := s) s →
      (∀ v, st.2.1 v ≠ none → v ∈ S ∨ ∃ e, G.src e ∈ st.2.2 ∧ eval G s e < B ∧ G.dst e = v ∧ v ≠ s) →
      st.2.2 ⊆ st'.2.2 ∧
      (∀ v, st'.2.1 v ≠ none → v ∈ S ∨ ∃ e, G.src e ∈ st'.2.2 ∧ eval G s e < B ∧ G.dst e = v ∧ v ≠ s) := by
  intro st st' c h
  induction h with
  | stop st _ => intro _ _ hk; exact ⟨subset_rfl, hk⟩
  | step d D U u val L st' c hu hmin hcard hL _ ih =>
    intro hw hs hk
    have hw' := foldl_relaxIns_walk B none L (d, D.deleteSet {u}) hw
    have hs' : (L.foldl (relaxIns G s B none) (d, D.deleteSet {u})).1 s ≤ dis (s := s) s :=
      (foldl_relaxIns_fst_le B none L _ s).trans hs
    have hk' : ∀ v, (L.foldl (relaxIns G s B none) (d, D.deleteSet {u})).2 v ≠ none →
        v ∈ S ∨ ∃ e, G.src e ∈ insert u U ∧ eval G s e < B ∧ G.dst e = v ∧ v ≠ s := by
      intro v hv
      refine foldl_keys B none
        (fun v => v ∈ S ∨ ∃ e, G.src e ∈ insert u U ∧ eval G s e < B ∧ G.dst e = v ∧ v ≠ s)
        L (d, D.deleteSet {u}) hw ?_ ?_ v hv
      · intro y hy
        have hy' : D y ≠ none := by
          intro hD; apply hy; simp [DS.deleteSet, hD]
        rcases hk y hy' with h | ⟨e, h1, h2, h3, h4⟩
        · exact Or.inl h
        · exact Or.inr ⟨e, Finset.mem_insert_of_mem h1, h2, h3, h4⟩
      · intro e he d' hw'' hd' hv
        have hsrc : G.src e = u := by
          have := (hL.2 e).mp he
          simpa using this
        refine Or.inr ⟨e, by rw [hsrc]; exact Finset.mem_insert_self _ _,
          lt_of_le_of_lt (eval_le_ext hw'' e) hv.2, rfl, ?_⟩
        exact valid_ne_source hw'' ((hd' s).trans hs) hv
    obtain ⟨hsub, hfin⟩ := ih hw' hs' hk'
    exact ⟨(Finset.subset_insert _ _).trans hsub, hfin⟩

/-- **Provenance of a base call.** -/
theorem baseC_prov {Blow : WLab G s} {d0 : Labels G s} {φ0 φ1 : Φ} {res : Result G s} {lg : Log G s Ω}
    (hw : WalkInv d0) (hs : d0 s ≤ dis (s := s) s)
    (hrel : BaseC G s DC Blow B S d0 φ0 τ res φ1 lg) : LocalProv lg ∧ RetProv G s lg res.2.2.1 := by
  obtain ⟨st, c, hloop, hU, hD, -, -, -, -, rfl⟩ := hrel
  refine ⟨fun z i r h => ?_, fun v hv => ?_⟩
  · rcases List.mem_singleton.mp h with heq
    have := congrArg Prod.fst heq
    simp at this
  · rw [hD] at hv
    have h0 : ∀ v, (insertMany G s DS.empty S d0) v ≠ none → v ∈ S ∨
        ∃ e, G.src e ∈ (∅ : Finset (Fin G.n)) ∧ eval G s e < B ∧ G.dst e = v ∧ v ≠ s := by
      intro v hv
      rw [insertMany_empty_apply] at hv
      split_ifs at hv with h
      · exact Or.inl h
      · exact absurd rfl hv
    rcases (baseLoopC_keysP hloop hw hs h0).2 v hv with h | ⟨e, h1, h2, h3, h4⟩
    · exact Or.inl ⟨[], _, List.mem_singleton_self _, h⟩
    · refine Or.inr ⟨e, [], ⟨[], _, List.mem_singleton_self _, ?_, Or.inr ⟨rfl, Or.inl rfl⟩⟩, h3, h4⟩
      classical
      unfold evOf
      rw [if_pos rfl]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; rw [hU]; exact h1, h2⟩

end Base

/-! ## The loop -/

section Loop

variable {B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {p : ℕ}
  {P0 : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {B'0 : WLab G s}

/-- **Provenance through the loop.**  `Old` is the provenance of the keys present before iteration `i`. -/
theorem loopC_prov (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W)
    {τ : ℕ → ℕ} {Inv : Φ → Prop} {sub : SubRelC G s Φ Ω} {l : ℕ} (hsub : GoodSub G s τ Inv l sub)
    (hsubp : SubProv G s Inv sub) {τl : ℕ} :
    ∀ i (σ : LState G s p) φ σ' φ' lg J cm c,
      LoopC G s DC sub (l + 1) B τl i σ φ σ' φ' lg J cm c →
      ∀ (Old : Fin G.n → Prop), LInv G s B S d0 d1 P0 B'0 σ → Inv φ → σ.d s ≤ dis (s := s) s →
      (∀ v, σ.D v ≠ none → (v ∈ S ∧ v ∉ Q) ∨ Old v) →
      (∀ j r, ([j], r) ∈ lg → ∀ v ∈ r.S, (v ∈ S ∧ v ∉ Q) ∨ Old v ∨ LProv lg J j v) ∧
      (∀ z j r, (z ++ [j], r) ∈ lg → z ≠ [] → ∀ v ∈ r.S,
        (∃ rz, (z, rz) ∈ lg ∧ v ∈ rz.S ∧ v ∉ rz.Q) ∨ Prov lg z j v) ∧
      (∀ v, σ'.D v ≠ none → (v ∈ S ∧ v ∉ Q) ∨ Old v ∨ ∃ j, LProv lg J j v) ∧
      σ'.d s ≤ dis (s := s) s := by
  intro i σ φ σ' φ' lg J cm c hloop
  induction hloop with
  | stop i σ φ hstop =>
    intro Old _ _ hs hK
    refine ⟨fun j r h => absurd h List.not_mem_nil, fun z j r h => absurd h List.not_mem_nil,
      fun v hv => ?_, hs⟩
    rcases hK v hv with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  | step i σ σ' φ φ1 φ' S0 Bi D1 B'i Ui Di dsub L' piv' lg lg' J' cm c _ hne hpull' _ _ hsubrel
      hnd hmem hres hrest ih =>
    intro Old h hI hs hK
    -- the sub-call (as in `loopC_recall`)
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
    obtain ⟨hLP, hRP⟩ := hsubp σ.B' Bi (expand σ S0 Bi) σ.d φ (B'i, Ui, Di, dsub) φ1 lg
      hsp hI hlowdis hBlt.le hs hsubrel
    obtain ⟨ri, hri, -, -, -, hriS, -, hriU⟩ := hclog.root
    -- the next state (as in `loopC_recall`)
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
    have hshape := (loopC_log hpre hfp hsub _ _ _ _ _ _ _ _ _ hrest hnext hI1).2.2.2.shape
    have hs' : (nextState B σ Bi B'i Ui D1 Di dsub L' piv').d s ≤ dis (s := s) s :=
      (foldl_relaxIns_fst_le B (some Bi) L' _ s).trans ((hpost.mono s).trans hs)
    -- the provenance of the keys present after this iteration
    let Old' : Fin G.n → Prop := fun v => Old v ∨
      (∃ e ∈ L', G.dst e = v ∧ v ≠ s ∧ G.src e ∈ Ui) ∨
      (∃ y r', (y, r') ∈ lg ∧ v ∈ r'.S) ∨ (∃ e α, IsEvent lg e α ∧ G.dst e = v ∧ v ≠ s)
    have hK' : ∀ v, (nextState B σ Bi B'i Ui D1 Di dsub L' piv').D v ≠ none →
        (v ∈ S ∧ v ∉ Q) ∨ Old' v := by
      intro v hv
      obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hv
      rcases insertMany_key_cases hk with hk1 | ⟨hmemr, -⟩
      · have hk1' : (L'.foldl (relaxIns G s B (some Bi)) (dsub, (D1.merge Di).deleteSet Ui)).2 v ≠ none := by
          rw [hk1]; simp
        refine foldl_keys B (some Bi) (fun v => (v ∈ S ∧ v ∉ Q) ∨ Old' v) L' _ hpost.walk ?_ ?_ v hk1'
        · intro y hy
          have hy' : (D1.merge Di) y ≠ none := by
            intro h0; apply hy; simp [DS.deleteSet, h0]
          by_cases hD1 : D1 y = none
          · have hDi : Di y ≠ none := by
              intro h0; apply hy'; simp [DS.merge, hD1, h0, DS.mergeVal]
            rcases hRP y hDi with h' | h'
            · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
            · exact Or.inr (Or.inr (Or.inr (Or.inr h')))
          · have hσ : σ.D y ≠ none := by
              intro h0; apply hD1; rw [hpull'.rest y]; split_ifs <;> simp [h0]
            rcases hK y hσ with h' | h'
            · exact Or.inl h'
            · exact Or.inr (Or.inl h')
        · intro e he d' hw' hd' hv'
          refine Or.inr (Or.inr (Or.inl ⟨e, he, rfl, ?_, ((hmem e).mp he).1⟩))
          exact valid_ne_source hw' ((hd' s).trans ((hpost.mono s).trans hs)) hv'
      · obtain ⟨j, rfl, hj1, hj2⟩ := mem_reselected.mp hmemr
        have hrs := (hres.resel j hj1 hj2).1
        have hP0 : piv' j ∈ P0 j := h.Psub j (Finset.mem_sdiff.mp hrs).1
        exact Or.inl ⟨(hfp.groups j).2 hP0, fun hq => Finset.disjoint_left.mp (hfp.qdisj j) hq hP0⟩
    obtain ⟨ha, hb, hc, hd⟩ := ih Old' hnext hI1 hs' hK'
    -- membership in the step's log
    have hin1 : ∀ x, x ∈ lg.shift i → x ∈ lg.shift i ++ lg' := fun x hx => List.mem_append_left _ hx
    have hin2 : ∀ x, x ∈ lg' → x ∈ lg.shift i ++ lg' := fun x hx => List.mem_append_right _ hx
    have hJ2 : J' ⊆ L'.toFinset ∪ J' := Finset.subset_union_right
    have hri' : ([i], ri) ∈ lg.shift i ++ lg' := hin1 _ (mem_shift.mpr ⟨[], rfl, hri⟩)
    -- translate the rest-of-loop provenance
    have hOld' : ∀ v j, i < j → Old' v → Old v ∨ LProv (lg.shift i ++ lg') (L'.toFinset ∪ J') j v := by
      intro v j hij hv
      rcases hv with h1 | ⟨e, he, hd, hvs, hu⟩ | ⟨y, r', hy, hvS⟩ | ⟨e, α, hev, hd, hvs⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨e, Finset.mem_union_left _ (List.mem_toFinset.mpr he), hd, hvs, i, ri, hij,
          hri', by rw [hriU]; exact hu⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨i :: y, r', hin1 _ (mem_shift.mpr ⟨y, rfl, hy⟩), hvS, i, y, rfl, hij⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨e, i :: α, isEvent_mono hin1 (isEvent_shift i hev), hd, hvs, i, α, rfl,
          hij⟩))
    refine ⟨fun j r hjr v hv => ?_, fun z j r hzr hz v hv => ?_, fun v hv => ?_, hd⟩
    · rcases List.mem_append.mp hjr with h1 | h2
      · -- the sub-call of this iteration
        obtain ⟨q', hq', hq'r⟩ := mem_shift.mp h1
        obtain ⟨rfl, rfl⟩ : j = i ∧ q' = [] := by
          simp only [List.cons.injEq] at hq'
          exact ⟨hq'.1, hq'.2.symm⟩
        have hrr : r = ri := rec_unique hclog.inv.nodup hq'r hri
        subst hrr
        rw [hriS] at hv
        rcases mem_expand.mp hv with hv0 | ⟨j', -, -, hvP, -⟩
        · obtain ⟨k, hk, -⟩ := (hpull'.pulled v).mp hv0
          rcases hK v (by rw [hk]; simp) with h' | h'
          · exact Or.inl h'
          · exact Or.inr (Or.inl h')
        · have hP0 : v ∈ P0 j' := h.Psub j' hvP
          exact Or.inl ⟨(hfp.groups j').2 hP0, fun hq => Finset.disjoint_left.mp (hfp.qdisj j') hq hP0⟩
      · obtain ⟨j0, q0, hq0, hj0⟩ := hshape _ _ h2
        have hjj : j = j0 := by
          simp only [List.cons.injEq] at hq0; exact hq0.1
        rcases ha j r h2 v hv with h' | h' | h'
        · exact Or.inl h'
        · rcases hOld' v j (by omega) h' with h'' | h''
          · exact Or.inr (Or.inl h'')
          · exact Or.inr (Or.inr h'')
        · exact Or.inr (Or.inr (lprov_mono hin2 hJ2 h'))
    · rcases List.mem_append.mp hzr with h1 | h2
      · obtain ⟨q', hq', hq'r⟩ := mem_shift.mp h1
        obtain ⟨a, z0, rfl⟩ := List.exists_cons_of_ne_nil hz
        simp only [List.cons_append, List.cons.injEq] at hq'
        obtain ⟨rfl, rfl⟩ := hq'
        rcases hLP z0 j r hq'r v hv with ⟨rz, hrz, hvS, hvQ⟩ | hpv
        · exact Or.inl ⟨rz, hin1 _ (mem_shift.mpr ⟨z0, rfl, hrz⟩), hvS, hvQ⟩
        · exact Or.inr (prov_mono hin1 (prov_shift _ hpv))
      · rcases hb z j r h2 hz v hv with ⟨rz, hrz, hvS, hvQ⟩ | hpv
        · exact Or.inl ⟨rz, hin2 _ hrz, hvS, hvQ⟩
        · exact Or.inr (prov_mono hin2 hpv)
    · rcases hc v hv with h' | h' | ⟨j, h'⟩
      · exact Or.inl h'
      · rcases hOld' v (i + 1) (by omega) h' with h'' | h''
        · exact Or.inr (Or.inl h'')
        · exact Or.inr (Or.inr ⟨i + 1, h''⟩)
      · exact Or.inr (Or.inr ⟨j, lprov_mono hin2 hJ2 h'⟩)

end Loop

/-! ## A recursive call and all levels -/

section Call

/-- **Provenance of a recursive call.** -/
theorem callC_prov {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} (hFPC : FPCSound G s FPC Inv)
    {τ : ℕ → ℕ} {sub : SubRelC G s Φ Ω} {l : ℕ} (hsub : GoodSub G s τ Inv l sub)
    (hsubp : SubProv G s Inv sub) {Blow B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s}
    {φ0 φ2 : Φ} {res : Result G s} {lg : Log G s Ω}
    (hpre : CallPre B S d0) (hI : Inv φ0) (hlow : ∀ x ∈ S, Blow ≤ dis (s := s) x)
    (hs : d0 s ≤ dis (s := s) s)
    (hrel : CallC G s FPC DC sub (l + 1) Blow B S d0 φ0 (τ (l + 1)) res φ2 lg) :
    LocalProv lg ∧ RetProv G s lg res.2.2.1 := by
  classical
  obtain ⟨d1, p, P, Q, W, φ1, ω, cfp, piv, σ, lgc, J, cm, cl, L, B'f, T6, W', hfprel, hpiv,
    hloop, hB'e, hB'n, hT6, hW', hL, hres, hlg⟩ := hrel
  obtain ⟨R, hR, hRb, hRS, hRQ, hRJ, hRWr, hRB⟩ : ∃ R : CallRec G s Ω, lg = ([], R) :: lgc ∧
      R.base = false ∧ R.S = S ∧ R.Q = Q ∧ R.J = J ∧ R.Wr = L.toFinset ∧ R.B = B :=
    ⟨_, hlg, rfl, rfl, rfl, rfl, rfl, rfl⟩
  subst hR
  subst hres
  have hlow' : ∀ x ∈ S, Blow ≤ d0 x := fun x hx => (hlow x hx).trans (hpre.walk.sound x)
  obtain ⟨hfp, hI1⟩ := hFPC _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpre hI hlow' hfprel
  have h0 := linv_init hpre hfp hpiv
  have hs1 : (initState B d1 P piv).d s ≤ dis (s := s) s := (hfp.le s).trans hs
  have hK0 : ∀ v, (initState B d1 P piv).D v ≠ none → (v ∈ S ∧ v ∉ Q) ∨ False := by
    intro v hv
    simp only [initState] at hv
    rw [insertMany_empty_apply] at hv
    split_ifs at hv with hvp
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hvp
      have hPj := (hpiv j).1
      exact Or.inl ⟨(hfp.groups j).2 hPj, fun hq => Finset.disjoint_left.mp (hfp.qdisj j) hq hPj⟩
    · exact absurd rfl hv
  have hwalk : WalkInv σ.d := (loopC_log hpre hfp hsub _ _ _ _ _ _ _ _ _ hloop h0 hI1).1.walk
  obtain ⟨ha, hb, hc, hd⟩ :=
    loopC_prov hpre hfp hsub hsubp _ _ _ _ _ _ _ _ _ hloop (fun _ => False) h0 hI1 hs1 hK0
  have hin : ∀ x, x ∈ lgc → x ∈ ([], R) :: lgc := fun x hx => List.mem_cons_of_mem _ hx
  have hRev : ∀ e, e ∈ R.J → e ∈ evOf R := by
    intro e he
    unfold evOf
    rw [if_neg (by rw [hRb]; decide)]
    exact Finset.mem_union_left _ he
  -- events of the root: jumps anchored at the returning child
  have hJev : ∀ e ∈ J, ∀ a r', ([a], r') ∈ lgc → G.src e ∈ r'.U → IsEvent (([], R) :: lgc) e [a] := by
    intro e he a r' hr' hu
    have he' : e ∈ R.J := by rw [hRJ]; exact he
    exact ⟨[], R, List.mem_cons_self, hRev e he', Or.inl ⟨hRb, he', a, r', rfl, hin _ hr', hu⟩⟩
  refine ⟨fun z j r' hmem v hv => ?_, fun v hv => ?_⟩
  · have hmem' : (z ++ [j], r') ∈ lgc := by
      rcases List.mem_cons.mp hmem with heq | h'
      · have := congrArg Prod.fst heq
        simp at this
      · exact h'
    by_cases hz : z = []
    · subst hz
      rcases ha j r' hmem' v hv with h' | h' | h'
      · exact Or.inl ⟨R, List.mem_cons_self, by rw [hRS]; exact h'.1, by rw [hRQ]; exact h'.2⟩
      · exact (h' : False).elim
      · rcases h' with ⟨e, he, hd, hvs, a, r'', ha', hr'', hu⟩ | ⟨e, α, hev, hd, hvs, a, α', rfl, ha'⟩ |
          ⟨y, r'', hy, hvS, a, y', rfl, ha'⟩
        · exact Or.inr (Or.inl ⟨e, [a], hJev e he a r'' hr'' hu, hd, hvs, a, [], rfl, ha'⟩)
        · exact Or.inr (Or.inl ⟨e, a :: α', isEvent_mono hin hev, hd, hvs, a, α', rfl, ha'⟩)
        · exact Or.inr (Or.inr ⟨a :: y', r'', hin _ hy, hvS, a, y', rfl, ha'⟩)
    · rcases hb z j r' hmem' hz v hv with ⟨rz, hrz, hvS, hvQ⟩ | hpv
      · exact Or.inl ⟨rz, hin _ hrz, hvS, hvQ⟩
      · exact Or.inr (prov_mono hin hpv)
  · -- the returned store
    have hv' : (L.foldl (relaxIns G s B (some B'f)) (σ.d, insertMany G s σ.D T6 σ.d)).2 v ≠ none := by
      intro h0; apply hv; simp [DS.deleteSet, h0]
    refine foldl_keys B (some B'f) (fun v => (∃ y r', (y, r') ∈ ([], R) :: lgc ∧ v ∈ r'.S) ∨
      ∃ e α, IsEvent (([], R) :: lgc) e α ∧ G.dst e = v ∧ v ≠ s) L _ hwalk ?_ ?_ v hv'
    · intro y hy
      obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hy
      rcases insertMany_key_cases hk with hk1 | ⟨hyT, -⟩
      · rcases hc y (by rw [hk1]; simp) with h' | h' | ⟨j, h'⟩
        · exact Or.inl ⟨[], R, List.mem_cons_self, by rw [hRS]; exact h'.1⟩
        · exact (h' : False).elim
        · rcases h' with ⟨e, he, hd, hvs, a, r'', -, hr'', hu⟩ | ⟨e, α, hev, hd, hvs, -⟩ |
            ⟨y', r'', hy', hvS, -⟩
          · exact Or.inr ⟨e, [a], hJev e he a r'' hr'' hu, hd, hvs⟩
          · exact Or.inr ⟨e, α, isEvent_mono hin hev, hd, hvs⟩
          · exact Or.inl ⟨y', r'', hin _ hy', hvS⟩
      · exact Or.inl ⟨[], R, List.mem_cons_self, by rw [hRS]; exact ((hT6 y).mp hyT).1⟩
    · intro e he d' hw' hd' hv''
      have heW : e ∈ R.Wr := by rw [hRWr]; exact List.mem_toFinset.mpr he
      have hev : e ∈ evOf R := by
        unfold evOf
        rw [if_neg (by rw [hRb]; decide)]
        refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨heW, ?_⟩)
        rw [hRB]
        exact lt_of_le_of_lt (eval_le_ext hw' e) hv''.2
      exact Or.inr ⟨e, [], ⟨[], R, List.mem_cons_self, hev, Or.inr ⟨rfl, Or.inr heW⟩⟩, rfl,
        valid_ne_source hw' ((hd' s).trans hd) hv''⟩

/-- **Every derivation of the traced BMSSP recursion has local provenance** (all levels). -/
theorem bmsspC_prov {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} (hFPC : FPCSound G s FPC Inv)
    (τ : ℕ → ℕ) : ∀ l, SubProv G s Inv (BMSSPC G s FPC DC τ l)
  | 0 => by
    intro Blow B S d φ res φ' lg hpre _ _ _ hs hrel
    exact baseC_prov hpre.walk hs hrel
  | l + 1 => by
    intro Blow B S d φ res φ' lg hpre hI hlow _ hs hrel
    exact callC_prov hFPC (bmsspC_log hFPC τ l) (bmsspC_prov hFPC τ l) hpre hI hlow hs hrel

/-- **The `Q`-witness fields of `Valid` for a traced top-level run** (tracker O22(a) + O22(b)): from a call with
`S ⊆ {s}` and a complete source label. -/
theorem bmsspC_qwit {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} (hFPC : FPCSound G s FPC Inv) (τ : ℕ → ℕ)
    {l : ℕ} {Blow B : WLab G s} {S : Finset (Fin G.n)} {d : Labels G s} {φ φ' : Φ} {res : Result G s}
    {lg : Log G s Ω} (hpre : CallPre B S d) (hI : Inv φ) (hlow : ∀ x ∈ S, Blow ≤ dis (s := s) x)
    (hBB : Blow ≤ B) (hs : d s ≤ dis (s := s) s) (hS : S ⊆ {s})
    (hrel : BMSSPC G s FPC DC τ l Blow B S d φ res φ' lg) (e0 : Fin G.m) :
    ∃ hL : LogInv τ l lg, ∃ wit : lg.Call → Fin G.n → Fin G.m,
      (∀ X, (lg.recOf X).B' = (lg.recOf X).B → ∀ v ∈ (lg.recOf X).Q, v ≠ s → G.dst (wit X v) = v) ∧
      (∀ v X X', (lg.recOf X).B' = (lg.recOf X).B → (lg.recOf X').B' = (lg.recOf X').B →
        v ∈ (lg.recOf X).Q → v ∈ (lg.recOf X').Q → wit X v = wit X' v → X = X') ∧
      (∀ X X', (lg.recOf X).B' = (lg.recOf X).B → (lg.recOf X').B' = (lg.recOf X').B →
        s ∈ (lg.recOf X).Q → s ∈ (lg.recOf X').Q → X = X') := by
  obtain ⟨-, -, hclog⟩ := bmsspC_log hFPC τ l Blow B S d φ res φ' lg hpre hI hlow hBB hrel
  have hLP := (bmsspC_prov hFPC τ l Blow B S d φ res φ' lg hpre hI hlow hBB hs hrel).1
  obtain ⟨r0, hr0, -, -, -, hr0S, -, -⟩ := hclog.root
  have hroot : ∀ r, ([], r) ∈ lg → r.S ⊆ {s} := by
    intro r hr
    have := rec_unique hclog.inv.nodup hr hr0
    subst this
    rw [hr0S]; exact hS
  exact ⟨hclog.inv, qwit_of_prov hclog.inv hLP hroot e0⟩

end Call

end BM
end CHD
end Frontier
