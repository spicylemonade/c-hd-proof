import Frontier.CHD.Basic

/-!
# Frontier.CHD.BM — the corrected BMSSP recursion over walk labels, and its correctness

Owner: agent-01 (work package L4 of COORD G2-2).  NON-GATE.

This file ports agent-01's gen-1-based proof (`A01.BMSSPRec`, receipt L4 v1) to the shared C-HD
interface `Frontier.CHD.Basic` (walk labels in the full walk order, canonical paths `OnPath`,
`CallPre`, `FPContract`, `PullSpec`).  It defines the BMSSP recursion (DMSY26 Alg. 3 and 4 with
the B1 fixes FIX-STALE, FIX-RESEL, FIX-EMPTY, FIX-BASE; the optional pivot switch BM.22 omitted)
as a relational big-step semantics, parameterized by an abstract FindPivots relation, and proves
B1 Lemma S2.1 (= corrected DMSY26 Lemmas 3.7/3.8) at every level, plus top-level exactness.

No cost statement is made here.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-! ## Relational semantics -/

section defs

variable (G s)

/-- Insert every `y ∈ T` with value `f y` (keep the smaller value). -/
noncomputable def insertMany (D : DS G s) (T : Finset (Fin G.n)) (f : Fin G.n → WLab G s) :
    DS G s :=
  fun y => if y ∈ T then DS.mergeVal (D y) (some (f y)) else D y

/-- DMSY26 `Relax(u, e, B)` is valid: `d[u] ⊕ e ≤ d[v]` and `d[u] ⊕ e < B`. -/
def ValidRelax (d : Labels G s) (B : WLab G s) (e : Fin G.m) : Prop :=
  ext (d (G.src e)) e ≤ d (G.dst e) ∧ ext (d (G.src e)) e < B

/-- One relaxation with insertion into `D` (BM.19–21 / BM.27–28 with threshold `lo`; BC.7 with
`lo = none`). -/
noncomputable def relaxIns (B : WLab G s) (lo : Option (WLab G s))
    (st : Labels G s × DS G s) (e : Fin G.m) : Labels G s × DS G s := by
  classical
  exact
    if ValidRelax G s st.1 B e then
      (Function.update st.1 (G.dst e) (ext (st.1 (G.src e)) e),
        match lo with
        | none => st.2.insert (G.dst e) (ext (st.1 (G.src e)) e)
        | some b => if b ≤ ext (st.1 (G.src e)) e then
            st.2.insert (G.dst e) (ext (st.1 (G.src e)) e) else st.2)
    else st

/-- `L` enumerates, without repetition, the out-edges of the vertices of `U`. -/
def Enumerates (L : List (Fin G.m)) (U : Finset (Fin G.n)) : Prop :=
  L.Nodup ∧ ∀ e, e ∈ L ↔ G.src e ∈ U

/-- A result `(B', U, D, d)` of a BMSSP call. -/
abbrev Result := WLab G s × Finset (Fin G.n) × DS G s × Labels G s

/-- The base-case loop (BC.3–BC.7). -/
inductive BaseLoop (B : WLab G s) (τ : ℕ) :
    Labels G s × DS G s × Finset (Fin G.n) → Labels G s × DS G s × Finset (Fin G.n) → Prop
  | stop (st : Labels G s × DS G s × Finset (Fin G.n)) :
      (st.2.1.IsEmpty ∨ τ ≤ st.2.2.card) → BaseLoop B τ st st
  | step (d : Labels G s) (D : DS G s) (U : Finset (Fin G.n)) (u : Fin G.n) (val : WLab G s)
      (L : List (Fin G.m)) (st' : Labels G s × DS G s × Finset (Fin G.n)) :
      D u = some val → (∀ y v, D y = some v → val ≤ v) → U.card < τ →
      Enumerates G L {u} →
      BaseLoop B τ
        ((L.foldl (relaxIns G s B none) (d, D.deleteSet {u})).1,
         (L.foldl (relaxIns G s B none) (d, D.deleteSet {u})).2, insert u U) st' →
      BaseLoop B τ (d, D, U) st'

/-- The base case (BC.1–BC.9, FIX-BASE). -/
def BaseRel (B : WLab G s) (S : Finset (Fin G.n)) (d0 : Labels G s) (τ : ℕ)
    (res : Result G s) : Prop :=
  ∃ st : Labels G s × DS G s × Finset (Fin G.n),
    BaseLoop G s B τ (d0, insertMany G s DS.empty S d0, ∅) st ∧
    res.2.1 = st.2.2 ∧ res.2.2.1 = st.2.1 ∧ res.2.2.2 = st.1 ∧
    (st.2.1.IsEmpty → res.1 = B) ∧
    (¬ st.2.1.IsEmpty → ∃ y, st.2.1 y = some res.1 ∧ ∀ z v, st.2.1 z = some v → res.1 ≤ v)

/-- Loop state of a recursive call with `p` pivot groups. -/
structure LState (p : ℕ) where
  d : Labels G s
  D : DS G s
  P : Fin p → Finset (Fin G.n)
  piv : Fin p → Fin G.n
  U : Finset (Fin G.n)
  B' : WLab G s

variable {G s}

/-- The expansion of a pulled set by the groups of pulled current pivots (BM.11–12). -/
noncomputable def expand {p : ℕ} (σ : LState G s p) (S0 : Finset (Fin G.n)) (Bi : WLab G s) :
    Finset (Fin G.n) := by
  classical
  exact S0 ∪ Finset.univ.filter (fun v => ∃ j : Fin p, σ.piv j ∈ S0 ∧ σ.piv j ∈ σ.P j ∧
    v ∈ σ.P j ∧ σ.d v < Bi)

/-- Re-selection of pivots (BM.16–18, BM.23 with FIX-RESEL). -/
structure Reselect {p : ℕ} (σ : LState G s p) (Ui : Finset (Fin G.n)) (d2 : Labels G s)
    (piv' : Fin p → Fin G.n) : Prop where
  resel : ∀ j, σ.piv j ∈ Ui → (σ.P j \ Ui).Nonempty →
    piv' j ∈ σ.P j \ Ui ∧ ∀ x ∈ σ.P j \ Ui, d2 (piv' j) ≤ d2 x
  keep : ∀ j, ¬ (σ.piv j ∈ Ui ∧ (σ.P j \ Ui).Nonempty) → piv' j = σ.piv j

/-- The set of re-selected pivots (inserted at BM.23). -/
noncomputable def reselected {p : ℕ} (σ : LState G s p) (Ui : Finset (Fin G.n))
    (piv' : Fin p → Fin G.n) : Finset (Fin G.n) := by
  classical
  exact Finset.univ.image piv' |>.filter
    (fun x => ∃ j, piv' j = x ∧ σ.piv j ∈ Ui ∧ (σ.P j \ Ui).Nonempty)

variable (G s)

/-- The main loop of a recursive call (BM.9–BM.24). -/
inductive LoopRel {p : ℕ} (sub : WLab G s → Finset (Fin G.n) → Labels G s → Result G s → Prop)
    (B : WLab G s) (τ : ℕ) : LState G s p → LState G s p → Prop
  | stop (σ : LState G s p) : (τ < σ.U.card ∨ σ.D.IsEmpty) → LoopRel sub B τ σ σ
  | step (σ σ' : LState G s p) (S0 : Finset (Fin G.n)) (Bi : WLab G s) (D1 : DS G s)
      (B'i : WLab G s) (Ui : Finset (Fin G.n)) (Di : DS G s) (d1 : Labels G s)
      (L : List (Fin G.m)) (piv' : Fin p → Fin G.n) :
      σ.U.card ≤ τ → ¬ σ.D.IsEmpty →
      PullSpec σ.D B S0 Bi D1 →
      sub Bi (expand σ S0 Bi) σ.d (B'i, Ui, Di, d1) →
      Enumerates G L Ui →
      Reselect σ Ui (L.foldl (relaxIns G s B (some Bi)) (d1, (D1.merge Di).deleteSet Ui)).1 piv' →
      LoopRel sub B τ
        { d := (L.foldl (relaxIns G s B (some Bi)) (d1, (D1.merge Di).deleteSet Ui)).1
          D := insertMany G s
                (L.foldl (relaxIns G s B (some Bi)) (d1, (D1.merge Di).deleteSet Ui)).2
                (reselected σ Ui piv')
                (L.foldl (relaxIns G s B (some Bi)) (d1, (D1.merge Di).deleteSet Ui)).1
          P := fun j => σ.P j \ Ui
          piv := piv'
          U := σ.U ∪ Ui
          B' := B'i } σ' →
      LoopRel sub B τ σ σ'

/-- An abstract FindPivots relation: bound, frontier set and input labels ↦ output labels,
`p` pivot groups `P`, failed roots `Q` and completed region `W`. -/
abbrev FPRel := WLab G s → Finset (Fin G.n) → Labels G s →
  Labels G s → (p : ℕ) → (Fin p → Finset (Fin G.n)) → Finset (Fin G.n) → Finset (Fin G.n) → Prop

/-- One recursive call, given the relation `sub` of the sub-calls (BM.1–BM.31).  The
finalization data are given by characterizations. -/
def CallRel (FP : FPRel G s) (sub : WLab G s → Finset (Fin G.n) → Labels G s → Result G s → Prop)
    (B : WLab G s) (S : Finset (Fin G.n)) (d0 : Labels G s) (τ : ℕ) (res : Result G s) : Prop :=
  ∃ (d1 : Labels G s) (p : ℕ) (P : Fin p → Finset (Fin G.n)) (Q W : Finset (Fin G.n))
    (piv : Fin p → Fin G.n) (σ : LState G s p) (L : List (Fin G.m)) (B'f : WLab G s)
    (T6 W' : Finset (Fin G.n)),
    FP B S d0 d1 p P Q W ∧
    -- BM.7: each group's pivot is a minimum of the group
    (∀ j, piv j ∈ P j ∧ ∀ x ∈ P j, d1 (piv j) ≤ d1 x) ∧
    -- BM.8–BM.24
    LoopRel G s sub B τ
      { d := d1, D := insertMany G s DS.empty (Finset.univ.image piv) d1,
        P := P, piv := piv, U := ∅,
        B' := min B (Finset.univ.inf fun j => d1 (piv j)) } σ ∧
    -- BM.24a (FIX-EMPTY)
    (σ.D.IsEmpty → B'f = B) ∧ (¬ σ.D.IsEmpty → B'f = σ.B') ∧
    -- BM.25: the re-inserted part of `S`
    (∀ x, x ∈ T6 ↔ x ∈ S ∧ B'f ≤ σ.d x ∧ σ.d x < B) ∧
    -- BM.26: `W'`
    (∀ x, x ∈ W' ↔ (x ∈ W ∧ x ∉ σ.U) ∧ σ.d x < B'f) ∧
    -- BM.27–BM.31
    Enumerates G L W' ∧
    res = (B'f, σ.U ∪ W',
      ((L.foldl (relaxIns G s B (some B'f)) (σ.d, insertMany G s σ.D T6 σ.d)).2).deleteSet W',
      (L.foldl (relaxIns G s B (some B'f)) (σ.d, insertMany G s σ.D T6 σ.d)).1)

/-- The BMSSP relation at every level; `τ l` is the workload cap of level `l`. -/
def BMSSPRel (FP : FPRel G s) (τ : ℕ → ℕ) :
    ℕ → WLab G s → Finset (Fin G.n) → Labels G s → Result G s → Prop
  | 0 => fun B S d res => BaseRel G s B S d (τ 0) res
  | l + 1 => fun B S d res => CallRel G s FP (BMSSPRel FP τ l) B S d (τ (l + 1)) res

/-- A FindPivots relation meets `FPContract` on every call satisfying `CallPre`. -/
def FPSound (FP : FPRel G s) : Prop :=
  ∀ B S d0 d1 p (P : Fin p → Finset (Fin G.n)) Q W,
    CallPre B S d0 → FP B S d0 d1 p P Q W → FPContract B S d0 d1 p P Q W

/-- Postconditions (B1 S2 (R1)–(R7)) of a call that started from labels `d0`, returning
`res = (B', U, D, d)`; `cap` is the partial-execution size guarantee. -/
structure CallPost (B : WLab G s) (S : Finset (Fin G.n)) (d0 : Labels G s) (cap : ℕ)
    (res : Result G s) : Prop where
  B'_le : res.1 ≤ B
  U_eq : ∀ v, v ∈ res.2.1 ↔ v ∈ Utilde res.1 (S : Set (Fin G.n))
  U_complete : ∀ u ∈ res.2.1, Complete res.2.2.2 u
  certified : ∀ v ∈ Utilde B (S : Set (Fin G.n)), v ∉ res.2.1 →
    ∃ y, res.2.2.1 y = some (dis (s := s) y) ∧ Complete res.2.2.2 y ∧ OnPath (s := s) y v
  keys : ∀ y k, res.2.2.1 y = some k → y ∈ Utilde B (S : Set (Fin G.n)) ∧ y ∉ res.2.1 ∧
    res.1 ≤ dis (s := s) y ∧ res.2.2.2 y ≤ k ∧ k < B
  empty_iff : res.1 = B ↔ res.2.2.1.IsEmpty
  partial_card : res.1 < B → cap ≤ res.2.1.card
  B'_ge : ∀ k, k ≤ B → (∀ x ∈ S, k ≤ dis (s := s) x) → k ≤ res.1
  confined : ∀ v, res.2.2.2 v ≠ d0 v → v ∈ Utilde B (S : Set (Fin G.n))
  S_keys : ∀ x ∈ S, x ∉ res.2.1 → ∃ k, res.2.2.1 x = some k ∧ k ≤ d0 x
  mono : ∀ v, res.2.2.2 v ≤ d0 v
  walk : WalkInv res.2.2.2
  /-- (S2 Lemma S2.4) every out-edge of a returned vertex, with candidate below `B`, has been
  relaxed: the head's label is at most the candidate. -/
  scanned : ∀ u ∈ res.2.1, ∀ e, G.src e = u → ext (dis (s := s) u) e < B →
    res.2.2.2 (G.dst e) ≤ ext (dis (s := s) u) e

end defs

/-! ## Generic facts on labels, `D` and relaxation folds -/

section generic

theorem foldl_invariant {β γ : Type*} (f : β → γ → β) (P : β → Prop) :
    ∀ (L : List γ) (b : β), P b → (∀ b c, c ∈ L → P b → P (f b c)) → P (L.foldl f b)
  | [], _, h0, _ => h0
  | c :: L, b, h0, h => by
    rw [List.foldl_cons]
    exact foldl_invariant f P L (f b c) (h b c (List.mem_cons_self ..) h0)
      (fun b' c' hc' => h b' c' (List.mem_cons_of_mem _ hc'))

/-- A finite label is (the image of) an edge list. -/
theorem exists_list_of_ne_top {x : WLab G s} (h : x ≠ ⊤) :
    ∃ q : List (Fin G.m), x = ((toW q : WalkOrd G s) : WLab G s) := by
  obtain ⟨p, hp⟩ := WithTop.ne_top_iff_exists.mp h
  exact ⟨p, hp.symm⟩

/-- The extension of a walk label is at least the head's canonical label. -/
theorem dis_le_ext {d : Labels G s} (hw : WalkInv d) (e : Fin G.m) :
    dis (s := s) (G.dst e) ≤ ext (d (G.src e)) e := by
  by_cases h : d (G.src e) = ⊤
  · rw [h, ext_top]; exact le_top
  · obtain ⟨q, hq⟩ := exists_list_of_ne_top h
    have hqw : G.IsWalk s (G.src e) q := hw _ q hq
    rw [hq, ext_coe]
    exact dis_le_walk (walk_ext hqw e rfl)

/-- A tight edge out of a vertex with its canonical label is on the head's canonical path. -/
theorem onPath_of_tight {e : Fin G.m} (htight : ext (dis (s := s) (G.src e)) e = dis (s := s) (G.dst e))
    (hsrc : dis (s := s) (G.src e) ≠ ⊤) : OnPath (s := s) (G.src e) (G.dst e) := by
  have hsr : G.Reachable s (G.src e) := by
    by_contra hc; exact hsrc (dis_of_not_reachable hc)
  have hdr : G.Reachable s (G.dst e) := by
    by_contra hc
    rw [dis_of_not_reachable hc, dis_of_reachable hsr, ext_coe] at htight
    exact WithTop.coe_ne_top htight
  have heq : path (s := s) (G.dst e) = path (s := s) (G.src e) ++ [e] := by
    rw [dis_of_reachable hsr, dis_of_reachable hdr, ext_coe] at htight
    exact (WithTop.coe_inj.mp htight).symm
  exact ⟨hdr, path (s := s) (G.src e), [e], heq, (path_isMinWalk hsr).1, IsWalk.single e⟩

theorem complete_of_le {d d' : Labels G s} {v : Fin G.n} (hc : Complete d v)
    (hle : d' v ≤ d v) (hs : Sound d') : Complete d' v :=
  le_antisymm (hle.trans hc.le) (hs v)

theorem ne_top_of_lt {x B : WLab G s} (h : x < B) : x ≠ ⊤ := by
  rintro rfl; exact not_top_lt h

/-- Relaxing a valid edge keeps labels walks. -/
theorem walkInv_update {d : Labels G s} (hw : WalkInv d) {e : Fin G.m} :
    WalkInv (Function.update d (G.dst e) (ext (d (G.src e)) e)) := by
  intro v p hp
  by_cases hv : v = G.dst e
  · subst hv
    simp only [Function.update_self] at hp
    by_cases h : d (G.src e) = ⊤
    · rw [h, ext_top] at hp; exact absurd hp.symm (WithTop.coe_ne_top)
    · obtain ⟨q, hq⟩ := exists_list_of_ne_top h
      have hqw : G.IsWalk s (G.src e) q := hw _ q hq
      rw [hq, ext_coe] at hp
      have hpq : p = q ++ [e] := (WithTop.coe_inj.mp hp).symm
      rw [hpq]
      exact walk_ext hqw e rfl
  · rw [Function.update_of_ne hv] at hp
    exact hw v p hp

namespace DSx

theorem mergeVal_cases (a b : Option (WLab G s)) (k : WLab G s) (h : DS.mergeVal a b = some k) :
    a = some k ∨ b = some k := by
  cases a with
  | none => exact Or.inr (by simpa [DS.mergeVal] using h)
  | some ka =>
    cases b with
    | none => exact Or.inl (by simpa [DS.mergeVal] using h)
    | some kb =>
      simp only [DS.mergeVal, Option.some.injEq] at h
      rcases min_choice ka kb with h' | h' <;> rw [h'] at h <;> simp [h]

theorem mergeVal_le_left {a b : Option (WLab G s)} {ka : WLab G s} (ha : a = some ka) :
    ∃ k, DS.mergeVal a b = some k ∧ k ≤ ka := by
  subst ha
  cases b with
  | none => exact ⟨ka, rfl, le_rfl⟩
  | some kb => exact ⟨min ka kb, rfl, min_le_left _ _⟩

theorem mergeVal_le_right {a b : Option (WLab G s)} {kb : WLab G s} (hb : b = some kb) :
    ∃ k, DS.mergeVal a b = some k ∧ k ≤ kb := by
  subst hb
  cases a with
  | none => exact ⟨kb, rfl, le_rfl⟩
  | some ka => exact ⟨min ka kb, rfl, min_le_right _ _⟩

theorem le_mergeVal {a b : Option (WLab G s)} {c k : WLab G s} (h : DS.mergeVal a b = some k)
    (ha : ∀ ka, a = some ka → c ≤ ka) (hb : ∀ kb, b = some kb → c ≤ kb) : c ≤ k := by
  rcases mergeVal_cases a b k h with h' | h'
  · exact ha k h'
  · exact hb k h'

end DSx

theorem merge_apply (D D' : DS G s) (y : Fin G.n) : (D.merge D') y = DS.mergeVal (D y) (D' y) :=
  rfl

theorem deleteSet_apply (D : DS G s) (T : Finset (Fin G.n)) (y : Fin G.n) :
    D.deleteSet T y = if y ∈ T then none else D y := rfl

theorem insertMany_apply (D : DS G s) (T : Finset (Fin G.n)) (f : Fin G.n → WLab G s)
    (y : Fin G.n) : insertMany G s D T f y = if y ∈ T then DS.mergeVal (D y) (some (f y)) else D y :=
  rfl

theorem insertMany_empty_apply (T : Finset (Fin G.n)) (f : Fin G.n → WLab G s) (y : Fin G.n) :
    insertMany G s DS.empty T f y = if y ∈ T then some (f y) else none := by
  unfold insertMany DS.empty
  by_cases hy : y ∈ T <;> simp [hy, DS.mergeVal]

theorem insertMany_key_cases {D : DS G s} {T : Finset (Fin G.n)} {f : Fin G.n → WLab G s}
    {y : Fin G.n} {k : WLab G s} (hk : insertMany G s D T f y = some k) :
    D y = some k ∨ (y ∈ T ∧ k = f y) := by
  rw [insertMany_apply] at hk
  split_ifs at hk with hy
  · rcases DSx.mergeVal_cases _ _ _ hk with h | h
    · exact Or.inl h
    · simp only [Option.some.injEq] at h; exact Or.inr ⟨hy, h.symm⟩
  · exact Or.inl hk

theorem insertMany_le {D : DS G s} (T : Finset (Fin G.n)) (f : Fin G.n → WLab G s) {y : Fin G.n}
    {k : WLab G s} (hk : D y = some k) : ∃ k', insertMany G s D T f y = some k' ∧ k' ≤ k := by
  rw [insertMany_apply]
  split_ifs
  · exact DSx.mergeVal_le_left hk
  · exact ⟨k, hk, le_rfl⟩

theorem insertMany_mem {D : DS G s} {T : Finset (Fin G.n)} (f : Fin G.n → WLab G s) {y : Fin G.n}
    (hy : y ∈ T) : ∃ k', insertMany G s D T f y = some k' ∧ k' ≤ f y := by
  rw [insertMany_apply, if_pos hy]
  exact DSx.mergeVal_le_right rfl

variable (G s) in
/-- Stored values dominate current labels (B1 S2 (V1)). -/
def StoredGe (d : Labels G s) (D : DS G s) : Prop := ∀ y k, D y = some k → d y ≤ k

theorem storedGe_mono {d d' : Labels G s} {D : DS G s} (h : StoredGe G s d D)
    (hle : ∀ v, d' v ≤ d v) : StoredGe G s d' D :=
  fun y k hk => (hle y).trans (h y k hk)

theorem storedGe_merge {d : Labels G s} {D D' : DS G s} (h : StoredGe G s d D)
    (h' : StoredGe G s d D') : StoredGe G s d (D.merge D') := by
  intro y k hk
  rw [merge_apply] at hk
  exact DSx.le_mergeVal hk (h y) (h' y)

theorem storedGe_deleteSet {d : Labels G s} {D : DS G s} (T : Finset (Fin G.n))
    (h : StoredGe G s d D) : StoredGe G s d (D.deleteSet T) := by
  intro y k hk
  rw [deleteSet_apply] at hk
  split_ifs at hk
  exact h y k hk

theorem storedGe_insertMany {d : Labels G s} {D : DS G s} (T : Finset (Fin G.n))
    (h : StoredGe G s d D) : StoredGe G s d (insertMany G s D T d) := by
  intro y k hk
  rw [insertMany_apply] at hk
  split_ifs at hk
  · exact DSx.le_mergeVal hk (h y)
      (fun kb hkb => by simp only [Option.some.injEq] at hkb; rw [hkb])
  · exact h y k hk

theorem relaxIns_fst_le (B : WLab G s) (lo : Option (WLab G s)) (st : Labels G s × DS G s)
    (e : Fin G.m) (v : Fin G.n) : (relaxIns G s B lo st e).1 v ≤ st.1 v := by
  unfold relaxIns
  split_ifs with h
  · by_cases hv : v = G.dst e
    · subst hv; simp only [Function.update_self]; exact h.1
    · simp [Function.update_of_ne hv]
  · exact le_rfl

theorem foldl_relaxIns_fst_le (B : WLab G s) (lo : Option (WLab G s)) (L : List (Fin G.m))
    (st : Labels G s × DS G s) (v : Fin G.n) :
    (L.foldl (relaxIns G s B lo) st).1 v ≤ st.1 v := by
  induction L generalizing st with
  | nil => exact le_rfl
  | cons e L ih => exact (ih _).trans (relaxIns_fst_le B lo st e v)

theorem relaxIns_walk (B : WLab G s) (lo : Option (WLab G s)) (st : Labels G s × DS G s)
    (e : Fin G.m) (h : WalkInv st.1) : WalkInv (relaxIns G s B lo st e).1 := by
  unfold relaxIns
  split_ifs
  · exact walkInv_update h
  · exact h

theorem foldl_relaxIns_walk (B : WLab G s) (lo : Option (WLab G s)) (L : List (Fin G.m))
    (st : Labels G s × DS G s) (h : WalkInv st.1) : WalkInv (L.foldl (relaxIns G s B lo) st).1 :=
  foldl_invariant _ (fun st => WalkInv st.1) L st h (fun b c _ hb => relaxIns_walk B lo b c hb)

theorem relaxIns_storedGe (B : WLab G s) (lo : Option (WLab G s)) (st : Labels G s × DS G s)
    (e : Fin G.m) (h : StoredGe G s st.1 st.2) :
    StoredGe G s (relaxIns G s B lo st e).1 (relaxIns G s B lo st e).2 := by
  intro y k hk
  unfold relaxIns at hk ⊢
  split_ifs at hk ⊢ with hv
  · have hins : ∀ D : DS G s, StoredGe G s st.1 D →
        (D.insert (G.dst e) (ext (st.1 (G.src e)) e)) y = some k →
        Function.update st.1 (G.dst e) (ext (st.1 (G.src e)) e) y ≤ k := by
      intro D hD hk'
      unfold DS.insert at hk'
      by_cases hy : y = G.dst e
      · subst hy
        simp only [Function.update_self] at hk' ⊢
        refine DSx.le_mergeVal hk' (fun ka hka => ?_) (fun kb hkb => ?_)
        · exact hv.1.trans (hD _ ka hka)
        · simp only [Option.some.injEq] at hkb; rw [hkb]
      · rw [Function.update_of_ne hy] at hk' ⊢
        exact hD y k hk'
    have hkeep : ∀ D : DS G s, StoredGe G s st.1 D → D y = some k →
        Function.update st.1 (G.dst e) (ext (st.1 (G.src e)) e) y ≤ k := by
      intro D hD hk'
      refine le_trans ?_ (hD y k hk')
      by_cases hy : y = G.dst e
      · subst hy; simp only [Function.update_self]; exact hv.1
      · simp [Function.update_of_ne hy]
    cases lo with
    | none => exact hins st.2 h hk
    | some b =>
      simp only at hk ⊢
      split_ifs at hk with hb
      · exact hins st.2 h hk
      · exact hkeep st.2 h hk
  · exact h y k hk

theorem foldl_relaxIns_storedGe (B : WLab G s) (lo : Option (WLab G s)) (L : List (Fin G.m))
    (st : Labels G s × DS G s) (h : StoredGe G s st.1 st.2) :
    StoredGe G s (L.foldl (relaxIns G s B lo) st).1 (L.foldl (relaxIns G s B lo) st).2 :=
  foldl_invariant _ (fun st => StoredGe G s st.1 st.2) L st h
    (fun b c _ hb => relaxIns_storedGe B lo b c hb)

theorem relaxIns_snd_le (B : WLab G s) (lo : Option (WLab G s)) (st : Labels G s × DS G s)
    (e : Fin G.m) (y : Fin G.n) (k : WLab G s) (hk : st.2 y = some k) :
    ∃ k', (relaxIns G s B lo st e).2 y = some k' ∧ k' ≤ k := by
  unfold relaxIns
  have hins : ∃ k', (st.2.insert (G.dst e) (ext (st.1 (G.src e)) e)) y = some k' ∧ k' ≤ k := by
    unfold DS.insert
    by_cases hy : y = G.dst e
    · subst hy; simp only [Function.update_self]; exact DSx.mergeVal_le_left hk
    · rw [Function.update_of_ne hy]; exact ⟨k, hk, le_rfl⟩
  split_ifs with hv
  · cases lo with
    | none => exact hins
    | some b =>
      simp only
      split_ifs with hb
      · exact hins
      · exact ⟨k, hk, le_rfl⟩
  · exact ⟨k, hk, le_rfl⟩

theorem foldl_relaxIns_snd_le (B : WLab G s) (lo : Option (WLab G s)) (L : List (Fin G.m)) :
    ∀ (st : Labels G s × DS G s) (y : Fin G.n) (k : WLab G s), st.2 y = some k →
      ∃ k', (L.foldl (relaxIns G s B lo) st).2 y = some k' ∧ k' ≤ k := by
  induction L with
  | nil => intro st y k hk; exact ⟨k, hk, le_rfl⟩
  | cons e L ih =>
    intro st y k hk
    obtain ⟨k1, hk1, hle1⟩ := relaxIns_snd_le B lo st e y k hk
    obtain ⟨k2, hk2, hle2⟩ := ih _ y k1 hk1
    exact ⟨k2, hk2, hle2.trans hle1⟩

theorem relaxIns_changed (B : WLab G s) (lo : Option (WLab G s)) (st : Labels G s × DS G s)
    (e : Fin G.m) (v : Fin G.n) (h : (relaxIns G s B lo st e).1 v ≠ st.1 v) :
    (relaxIns G s B lo st e).1 v < st.1 v ∧ (relaxIns G s B lo st e).1 v < B := by
  unfold relaxIns at h ⊢
  split_ifs at h ⊢ with hv
  · by_cases hve : v = G.dst e
    · subst hve
      simp only [Function.update_self] at h ⊢
      exact ⟨lt_of_le_of_ne hv.1 h, hv.2⟩
    · simp [Function.update_of_ne hve] at h
  · exact absurd rfl h

theorem foldl_relaxIns_changed (B : WLab G s) (lo : Option (WLab G s)) (L : List (Fin G.m)) :
    ∀ (st : Labels G s × DS G s) (v : Fin G.n), (L.foldl (relaxIns G s B lo) st).1 v ≠ st.1 v →
      (L.foldl (relaxIns G s B lo) st).1 v < st.1 v ∧
        (L.foldl (relaxIns G s B lo) st).1 v < B := by
  induction L with
  | nil => intro st v h; exact absurd rfl h
  | cons e L ih =>
    intro st v h
    rw [List.foldl_cons] at h ⊢
    by_cases h1 : (L.foldl (relaxIns G s B lo) (relaxIns G s B lo st e)).1 v =
        (relaxIns G s B lo st e).1 v
    · have h2 : (relaxIns G s B lo st e).1 v ≠ st.1 v := by rw [← h1]; exact h
      obtain ⟨hlt, hkey⟩ := relaxIns_changed B lo st e v h2
      rw [h1]; exact ⟨hlt, hkey⟩
    · obtain ⟨hlt, hkey⟩ := ih _ v h1
      exact ⟨lt_of_lt_of_le hlt (relaxIns_fst_le B lo st e v), hkey⟩

/-- One relaxation: a key after it was a key before (same value) or is the head of a valid
relaxation admitted by the threshold, with the candidate as value. -/
theorem relaxIns_snd_cases (B : WLab G s) (lo : Option (WLab G s)) (st : Labels G s × DS G s)
    (e : Fin G.m) {y : Fin G.n} {k : WLab G s} (hk : (relaxIns G s B lo st e).2 y = some k) :
    st.2 y = some k ∨
      (y = G.dst e ∧ ValidRelax G s st.1 B e ∧
        (∀ b, lo = some b → b ≤ ext (st.1 (G.src e)) e) ∧ k = ext (st.1 (G.src e)) e) := by
  unfold relaxIns at hk
  split_ifs at hk with hv
  · have hins : ∀ (h : ∀ b, lo = some b → b ≤ ext (st.1 (G.src e)) e),
        (st.2.insert (G.dst e) (ext (st.1 (G.src e)) e)) y = some k →
        st.2 y = some k ∨
          (y = G.dst e ∧ ValidRelax G s st.1 B e ∧
            (∀ b, lo = some b → b ≤ ext (st.1 (G.src e)) e) ∧ k = ext (st.1 (G.src e)) e) := by
      intro hlo hk'
      unfold DS.insert at hk'
      by_cases hy : y = G.dst e
      · subst hy
        simp only [Function.update_self] at hk'
        rcases DSx.mergeVal_cases _ _ _ hk' with h | h
        · exact Or.inl h
        · simp only [Option.some.injEq] at h
          exact Or.inr ⟨rfl, hv, hlo, h.symm⟩
      · rw [Function.update_of_ne hy] at hk'
        exact Or.inl hk'
    cases lo with
    | none => exact hins (fun b hb => by simp at hb) hk
    | some b =>
      simp only at hk
      split_ifs at hk with hb
      · exact hins (fun b' hb' => by simp only [Option.some.injEq] at hb'; subst hb'; exact hb) hk
      · exact Or.inl hk
  · exact Or.inl hk

/-- **Key provenance in relaxation folds out of complete vertices.** -/
theorem foldl_relaxIns_keys (B : WLab G s) (lo : Option (WLab G s))
    (P : Fin G.n → WLab G s → Prop) :
    ∀ (L : List (Fin G.m)) (st : Labels G s × DS G s), Sound st.1 →
      (∀ e ∈ L, Complete st.1 (G.src e)) →
      (∀ y k, st.2 y = some k → P y k) →
      (∀ e ∈ L, ∀ d' : Labels G s, Sound d' → (∀ v, d' v ≤ st.1 v) →
        Complete d' (G.src e) → ValidRelax G s d' B e →
        (∀ b, lo = some b → b ≤ ext (dis (s := s) (G.src e)) e) →
        P (G.dst e) (ext (dis (s := s) (G.src e)) e)) →
      ∀ y k, (L.foldl (relaxIns G s B lo) st).2 y = some k → P y k := by
  intro L
  induction L with
  | nil => intro st _ _ h0 _ y k hk; exact h0 y k hk
  | cons e L ih =>
    intro st hs hsrc h0 hins y k hk
    rw [List.foldl_cons] at hk
    have hle1 : ∀ v, (relaxIns G s B lo st e).1 v ≤ st.1 v := fun v => relaxIns_fst_le B lo st e v
    have hs1 : Sound (relaxIns G s B lo st e).1 := by
      intro v
      by_cases h : (relaxIns G s B lo st e).1 v = st.1 v
      · rw [h]; exact hs v
      · -- a changed label is a candidate `ext (d u) e`, which is at least the canonical label
        unfold relaxIns at h ⊢
        split_ifs at h ⊢ with hv
        · by_cases hve : v = G.dst e
          · subst hve
            simp only [Function.update_self]
            -- the tail is complete, hence a walk label (or `⊤`)
            have hc := hsrc e (List.mem_cons_self ..)
            rw [hc]
            by_cases hdt : dis (s := s) (G.src e) = ⊤
            · rw [hdt, ext_top]; exact le_top
            · have hr : G.Reachable s (G.src e) := by
                by_contra hc'; exact hdt (dis_of_not_reachable hc')
              rw [dis_of_reachable hr, ext_coe]
              exact dis_le_walk (walk_ext (path_isMinWalk hr).1 e rfl)
          · simp [Function.update_of_ne hve] at h
        · exact absurd rfl h
    refine ih _ hs1 ?_ ?_ ?_ y k hk
    · intro e' he'
      exact complete_of_le (hsrc e' (List.mem_cons_of_mem _ he')) (hle1 _) hs1
    · intro y' k' hk'
      rcases relaxIns_snd_cases B lo st e hk' with h | ⟨rfl, hv, hlo, rfl⟩
      · exact h0 y' k' h
      · have hse : st.1 (G.src e) = dis (s := s) (G.src e) := hsrc e (List.mem_cons_self ..)
        rw [hse] at hlo ⊢
        exact hins e (List.mem_cons_self ..) st.1 hs (fun _ => le_rfl) hse hv hlo
    · intro e' he' d' hs' hd' hsrc' hv' hlo'
      exact hins e' (List.mem_cons_of_mem _ he') d' hs' (fun v => (hd' v).trans (hle1 v))
        hsrc' hv' hlo'

/-- **Canonical relaxation inside a fold**: a tight edge out of a complete vertex, with candidate
below `B`, makes its head complete, and (if the threshold admits it) leaves the head as a key with
stored value at most its canonical label. -/
theorem foldl_relaxIns_canonical (B : WLab G s) (lo : Option (WLab G s)) :
    ∀ (L : List (Fin G.m)) (st : Labels G s × DS G s) (e : Fin G.m), e ∈ L →
      WalkInv st.1 → Complete st.1 (G.src e) →
      dis (s := s) (G.dst e) = ext (dis (s := s) (G.src e)) e →
      dis (s := s) (G.dst e) < B →
      Complete (L.foldl (relaxIns G s B lo) st).1 (G.dst e) ∧
      ((∀ b, lo = some b → b ≤ dis (s := s) (G.dst e)) →
        ∃ k, (L.foldl (relaxIns G s B lo) st).2 (G.dst e) = some k ∧ k ≤ dis (s := s) (G.dst e)) := by
  intro L
  induction L with
  | nil => intro st e he; simp at he
  | cons e' L ih =>
    intro st e he hw hsrc htight hB
    rw [List.foldl_cons]
    have hw1 : WalkInv (relaxIns G s B lo st e').1 := relaxIns_walk B lo st e' hw
    rcases List.mem_cons.mp he with rfl | he
    · have hvalid : ValidRelax G s st.1 B e := by
        refine ⟨?_, ?_⟩
        · rw [hsrc, ← htight]; exact hw.sound _
        · rw [hsrc, ← htight]; exact hB
      have h1 : (relaxIns G s B lo st e).1 (G.dst e) = dis (s := s) (G.dst e) := by
        unfold relaxIns; rw [if_pos hvalid]
        simp only [Function.update_self]; rw [hsrc, ← htight]
      refine ⟨complete_of_le h1 (foldl_relaxIns_fst_le B lo L _ _)
          (foldl_relaxIns_walk B lo L _ hw1).sound, fun hlo => ?_⟩
      have h2 : ∃ k, (relaxIns G s B lo st e).2 (G.dst e) = some k ∧ k ≤ dis (s := s) (G.dst e) := by
        unfold relaxIns; rw [if_pos hvalid]
        have hcand : ext (st.1 (G.src e)) e = dis (s := s) (G.dst e) := by rw [hsrc, ← htight]
        cases lo with
        | none =>
          simp only [DS.insert, Function.update_self, hcand]
          exact DSx.mergeVal_le_right rfl
        | some b =>
          simp only
          rw [if_pos (by rw [hcand]; exact hlo b rfl)]
          simp only [DS.insert, Function.update_self, hcand]
          exact DSx.mergeVal_le_right rfl
      obtain ⟨k, hk, hkle⟩ := h2
      obtain ⟨k', hk', hk'le⟩ := foldl_relaxIns_snd_le B lo L _ _ k hk
      exact ⟨k', hk', hk'le.trans hkle⟩
    · have hsrc' : Complete (relaxIns G s B lo st e').1 (G.src e) :=
        complete_of_le hsrc (relaxIns_fst_le B lo st e' _) hw1.sound
      exact ih _ e he hw1 hsrc' htight hB

/-- **Scanning in a fold**: after folding over a list containing `e`, whose source keeps its
canonical label, the head's label is at most the candidate (if the candidate is below `B`). -/
theorem foldl_relaxIns_scan (B : WLab G s) (lo : Option (WLab G s)) :
    ∀ (L : List (Fin G.m)) (st : Labels G s × DS G s) (e : Fin G.m), e ∈ L →
      WalkInv st.1 → Complete st.1 (G.src e) → ext (dis (s := s) (G.src e)) e < B →
      (L.foldl (relaxIns G s B lo) st).1 (G.dst e) ≤ ext (dis (s := s) (G.src e)) e := by
  intro L
  induction L with
  | nil => intro st e he; simp at he
  | cons e' L ih =>
    intro st e he hw hsrc hB
    rw [List.foldl_cons]
    have hw1 : WalkInv (relaxIns G s B lo st e').1 := relaxIns_walk B lo st e' hw
    rcases List.mem_cons.mp he with rfl | he
    · have h1 : (relaxIns G s B lo st e).1 (G.dst e) ≤ ext (dis (s := s) (G.src e)) e := by
        unfold relaxIns
        split_ifs with hv
        · simp only [Function.update_self]; rw [hsrc]
        · have hcand : ext (st.1 (G.src e)) e < B := by rw [hsrc]; exact hB
          have : ¬ ext (st.1 (G.src e)) e ≤ st.1 (G.dst e) := fun hle => hv ⟨hle, hcand⟩
          rw [hsrc] at this
          exact (not_le.mp this).le
      exact (foldl_relaxIns_fst_le B lo L _ _).trans h1
    · have hsrc' : Complete (relaxIns G s B lo st e').1 (G.src e) :=
        complete_of_le hsrc (relaxIns_fst_le B lo st e' _) hw1.sound
      exact ih _ e he hw1 hsrc' hB

end generic

/-! ## Call-level basics -/

section callbasic

variable {B : WLab G s} {S : Finset (Fin G.n)} {d d0 : Labels G s}

theorem S_sub_of_pre (h : CallPre B S d) : ∀ x ∈ S, x ∈ Utilde B (S : Set (Fin G.n)) := by
  intro x hx
  have hlt := h.inRange x hx
  have hfin : d x ≠ ⊤ := ne_top_of_lt hlt
  obtain ⟨q, hq⟩ := exists_list_of_ne_top hfin
  have hr : G.Reachable s x := ⟨q, h.walk x q hq⟩
  exact ⟨lt_of_le_of_lt (h.walk.sound x) hlt, x, hx, onPath_self hr⟩

/-- A valid relaxation out of a complete vertex of `Ũ(B, S)` lands in `Ũ(B, S)` (B1 S1 L3+). -/
theorem mem_UK_of_valid (hpre : CallPre B S d0) (hs : Sound d) (hmono : ∀ v, d v ≤ d0 v)
    {e : Fin G.m} (hsrcU : G.src e ∈ Utilde B (S : Set (Fin G.n))) (hsrc : Complete d (G.src e))
    (hv : ValidRelax G s d B e) : G.dst e ∈ Utilde B (S : Set (Fin G.n)) := by
  have hdisfin : dis (s := s) (G.src e) ≠ ⊤ := ne_top_of_lt hsrcU.1
  have hcand_ge : dis (s := s) (G.dst e) ≤ ext (d (G.src e)) e := by
    rw [hsrc]
    have hr : G.Reachable s (G.src e) := by
      by_contra hc; exact hdisfin (dis_of_not_reachable hc)
    rw [dis_of_reachable hr, ext_coe]
    exact dis_le_walk (walk_ext (path_isMinWalk hr).1 e rfl)
  have hkey : dis (s := s) (G.dst e) < B := lt_of_le_of_lt hcand_ge hv.2
  by_contra hnot
  have hc := hpre.claimC _ hkey hnot
  have hdc : d (G.dst e) = dis (s := s) (G.dst e) := complete_of_le hc (hmono _) hs
  have htight : ext (dis (s := s) (G.src e)) e = dis (s := s) (G.dst e) := by
    rw [← hsrc]
    exact le_antisymm (hv.1.trans hdc.le) hcand_ge
  obtain ⟨-, z, hz, hzvis⟩ := hsrcU
  exact hnot ⟨hkey, z, hz, hzvis.trans (onPath_of_tight htight hdisfin)⟩

end callbasic

/-! ## Base case (B1 S2 §S2.3) -/

section base

variable (G s) in
/-- The base-case loop invariant (B1 S2 (K0)–(K4) plus bookkeeping). -/
structure BInv (B : WLab G s) (S : Finset (Fin G.n)) (d0 : Labels G s) (d : Labels G s)
    (D : DS G s) (U : Finset (Fin G.n)) : Prop where
  walk : WalkInv d
  mono : ∀ v, d v ≤ d0 v
  confined : ∀ v, d v ≠ d0 v → v ∈ Utilde B (S : Set (Fin G.n))
  stored : ∀ y k, D y = some k → k = d y ∧ k < B
  keysU : ∀ y k, D y = some k → y ∉ U
  keysUK : ∀ y k, D y = some k → y ∈ Utilde B (S : Set (Fin G.n))
  complete : ∀ u ∈ U, Complete d u
  UUK : ∀ u ∈ U, u ∈ Utilde B (S : Set (Fin G.n))
  order : ∀ u ∈ U, ∀ y k, D y = some k → d u < k
  frontier : ∀ v ∈ Utilde B (S : Set (Fin G.n)), v ∉ U →
    ∃ y, D y = some (dis (s := s) y) ∧ Complete d y ∧ OnPath (s := s) y v
  Skeys : ∀ x ∈ S, x ∉ U → ∃ k, D x = some k ∧ k ≤ d0 x
  scanned : ∀ u ∈ U, ∀ e, G.src e = u → ext (dis (s := s) u) e < B →
    d (G.dst e) ≤ ext (dis (s := s) u) e

variable {B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s}

theorem bInv_init (hpre : CallPre B S d0) :
    BInv G s B S d0 d0 (insertMany G s DS.empty S d0) ∅ where
  walk := hpre.walk
  mono := fun _ => le_rfl
  confined := fun _ h => absurd rfl h
  stored := by
    intro y k hk
    rw [insertMany_empty_apply] at hk
    split_ifs at hk with hy
    simp only [Option.some.injEq] at hk
    exact ⟨hk.symm, hk ▸ hpre.inRange y hy⟩
  keysU := fun _ _ _ => Finset.notMem_empty _
  keysUK := by
    intro y k hk
    rw [insertMany_empty_apply] at hk
    split_ifs at hk with hy
    exact S_sub_of_pre hpre y hy
  complete := by simp
  UUK := by simp
  order := by simp
  frontier := by
    intro v hv _
    rcases hpre.frontier v hv with ⟨h, -⟩ | ⟨y, hyS, hyc, hvis⟩
    · exact absurd h (Set.notMem_empty v)
    · refine ⟨y, ?_, hyc, hvis⟩
      rw [insertMany_empty_apply, if_pos (Finset.mem_coe.mp hyS), hyc]
  Skeys := by
    intro x hx _
    refine ⟨d0 x, ?_, le_rfl⟩
    rw [insertMany_empty_apply, if_pos hx]
  scanned := by simp

variable (G s) in
/-- Invariant of the relaxation fold out of the extracted vertex `u`. -/
structure BFold (B : WLab G s) (S : Finset (Fin G.n)) (d0 d : Labels G s) (U : Finset (Fin G.n))
    (u : Fin G.n) (st : Labels G s × DS G s) : Prop where
  walk : WalkInv st.1
  le : ∀ v, st.1 v ≤ d v
  stored : ∀ y k, st.2 y = some k → k = st.1 y ∧ k < B
  notU : ∀ y k, st.2 y = some k → y ∉ insert u U
  above : ∀ y k, st.2 y = some k → d u < k
  inUK : ∀ y k, st.2 y = some k → y ∈ Utilde B (S : Set (Fin G.n))
  confined : ∀ v, st.1 v ≠ d0 v → v ∈ Utilde B (S : Set (Fin G.n))

theorem bFold_step {d : Labels G s} {D : DS G s} {U : Finset (Fin G.n)} {u : Fin G.n}
    {val : WLab G s} (hpre : CallPre B S d0) (h : BInv G s B S d0 d D U) (hu : D u = some val)
    {st : Labels G s × DS G s} (hst : BFold G s B S d0 d U u st) {e : Fin G.m}
    (he : G.src e = u) (hucomp : Complete d u) :
    BFold G s B S d0 d U u (relaxIns G s B none st e) := by
  have hstu : st.1 u = d u := by
    rw [hucomp]; exact complete_of_le hucomp (hst.le u) hst.walk.sound
  by_cases hv : ValidRelax G s st.1 B e
  · have hstep : relaxIns G s B none st e =
        (Function.update st.1 (G.dst e) (ext (st.1 (G.src e)) e),
          st.2.insert (G.dst e) (ext (st.1 (G.src e)) e)) := by
      unfold relaxIns; rw [if_pos hv]
    have hcand : ext (st.1 (G.src e)) e = ext (d u) e := by rw [he, hstu]
    have hufin : d u ≠ ⊤ := by
      have := (h.stored u val hu).2
      rw [(h.stored u val hu).1] at this
      exact ne_top_of_lt this
    have hgt : d u < ext (d u) e := lt_ext_of_ne_top hufin e
    -- the head is neither `u` nor in `U`
    have hdst_notU : G.dst e ∉ insert u U := by
      intro hmem
      rcases Finset.mem_insert.mp hmem with h1 | h1
      · have := hv.1
        rw [hcand, h1, hstu] at this
        exact absurd this (not_le.mpr hgt)
      · have hc : st.1 (G.dst e) = d (G.dst e) := by
          rw [h.complete _ h1]; exact complete_of_le (h.complete _ h1) (hst.le _) hst.walk.sound
        have hord := h.order _ h1 u val hu
        rw [(h.stored u val hu).1] at hord
        have := hv.1
        rw [hcand, hc] at this
        exact absurd (lt_of_lt_of_le hgt this) (not_lt.mpr hord.le)
    have huUK : u ∈ Utilde B (S : Set (Fin G.n)) := h.keysUK u val hu
    have hdstUK : G.dst e ∈ Utilde B (S : Set (Fin G.n)) :=
      mem_UK_of_valid hpre hst.walk.sound (fun v => (hst.le v).trans (h.mono v)) (he ▸ huUK)
        (by show st.1 (G.src e) = _; rw [he, hstu, hucomp]) hv
    rw [hstep]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := relaxIns_walk B none st e hst.walk
      rw [hstep] at this; exact this
    · intro v
      by_cases hve : v = G.dst e
      · subst hve; simp only [Function.update_self]; exact hv.1.trans (hst.le _)
      · simp only [Function.update_of_ne hve]; exact hst.le v
    · intro y k hk
      simp only [DS.insert] at hk ⊢
      by_cases hy : y = G.dst e
      · subst hy
        simp only [Function.update_self] at hk ⊢
        refine ⟨?_, ?_⟩
        · cases hold : st.2 (G.dst e) with
          | none =>
            rw [hold] at hk; simp only [DS.mergeVal, Option.some.injEq] at hk; exact hk.symm
          | some k0 =>
            rw [hold] at hk
            simp only [DS.mergeVal, Option.some.injEq] at hk
            have hk0 := (hst.stored _ k0 hold).1
            have : ext (st.1 (G.src e)) e ≤ k0 := by rw [hk0]; exact hv.1
            rw [← hk, min_eq_right this]
        · rcases DSx.mergeVal_cases _ _ k hk with h1 | h1
          · exact (hst.stored _ k h1).2
          · simp only [Option.some.injEq] at h1; rw [← h1]; exact hv.2
      · rw [Function.update_of_ne hy] at hk
        simp only [Function.update_of_ne hy]
        exact hst.stored y k hk
    · intro y k hk
      simp only [DS.insert] at hk
      by_cases hy : y = G.dst e
      · subst hy; exact hdst_notU
      · rw [Function.update_of_ne hy] at hk; exact hst.notU y k hk
    · intro y k hk
      simp only [DS.insert] at hk
      by_cases hy : y = G.dst e
      · subst hy
        simp only [Function.update_self] at hk
        rcases DSx.mergeVal_cases _ _ k hk with h1 | h1
        · exact hst.above _ k h1
        · simp only [Option.some.injEq] at h1
          rw [← h1, hcand]
          exact hgt
      · rw [Function.update_of_ne hy] at hk; exact hst.above y k hk
    · intro y k hk
      simp only [DS.insert] at hk
      by_cases hy : y = G.dst e
      · subst hy; exact hdstUK
      · rw [Function.update_of_ne hy] at hk; exact hst.inUK y k hk
    · intro v hv'
      by_cases hve : v = G.dst e
      · subst hve; exact hdstUK
      · simp only [Function.update_of_ne hve] at hv'; exact hst.confined v hv'
  · have hstep : relaxIns G s B none st e = st := by unfold relaxIns; rw [if_neg hv]
    rw [hstep]; exact hst

theorem deleteSet_singleton_apply (D : DS G s) (u y : Fin G.n) :
    D.deleteSet {u} y = if y = u then none else D y := by
  simp [DS.deleteSet]

/-- The extracted minimum key of the base case is complete (B1 S2 (K4)). -/
theorem base_extract_complete {d : Labels G s} {D : DS G s} {U : Finset (Fin G.n)} {u : Fin G.n}
    {val : WLab G s} (h : BInv G s B S d0 d D U) (hu : D u = some val)
    (hmin : ∀ y v, D y = some v → val ≤ v) : Complete d u := by
  by_contra hinc
  obtain ⟨y, hy, hyc, hvis⟩ := h.frontier u (h.keysUK u val hu) (h.keysU u val hu)
  have hyu : y ≠ u := by rintro rfl; exact hinc hyc
  have h1 := hvis.dis_lt hyu
  have h2 : dis (s := s) u ≤ val := by
    rw [(h.stored u val hu).1]; exact h.walk.sound u
  exact absurd (hmin y _ hy) (not_le.mpr (lt_of_lt_of_le h1 h2))

/-- One base-case iteration preserves the invariant. -/
theorem bInv_step {d : Labels G s} {D : DS G s} {U : Finset (Fin G.n)} {u : Fin G.n}
    {val : WLab G s} {L : List (Fin G.m)} (hpre : CallPre B S d0) (h : BInv G s B S d0 d D U)
    (hu : D u = some val) (hmin : ∀ y v, D y = some v → val ≤ v) (hL : Enumerates G L {u}) :
    BInv G s B S d0 (L.foldl (relaxIns G s B none) (d, D.deleteSet {u})).1
      (L.foldl (relaxIns G s B none) (d, D.deleteSet {u})).2 (insert u U) := by
  have hucomp := base_extract_complete h hu hmin
  have hval : val = d u := (h.stored u val hu).1
  have hufin : d u ≠ ⊤ := by
    have := (h.stored u val hu).2; rw [hval] at this; exact ne_top_of_lt this
  have hBF0 : BFold G s B S d0 d U u (d, D.deleteSet {u}) := by
    refine ⟨h.walk, fun _ => le_rfl, ?_, ?_, ?_, ?_, h.confined⟩
    · intro y k hk
      simp only at hk ⊢
      rw [deleteSet_singleton_apply] at hk
      split_ifs at hk with hy
      exact h.stored y k hk
    · intro y k hk
      simp only at hk ⊢
      rw [deleteSet_singleton_apply] at hk
      split_ifs at hk with hy
      intro hmem
      rcases Finset.mem_insert.mp hmem with h1 | h1
      · exact hy h1
      · exact h.keysU y k hk h1
    · intro y k hk
      simp only at hk ⊢
      rw [deleteSet_singleton_apply] at hk
      split_ifs at hk with hy
      have hle : d u ≤ k := by rw [← hval]; exact hmin y k hk
      refine lt_of_le_of_ne hle ?_
      rw [(h.stored y k hk).1]
      -- distinct vertices never share a finite label
      intro heq
      obtain ⟨q, hq⟩ := exists_list_of_ne_top hufin
      have hqu : G.IsWalk s u q := h.walk u q hq
      have hqy : G.IsWalk s y q := h.walk y q (by rw [← heq, hq])
      exact hy ((endV_of_isWalk hqy).symm.trans (endV_of_isWalk hqu))
    · intro y k hk
      simp only at hk ⊢
      rw [deleteSet_singleton_apply] at hk
      split_ifs at hk with hy
      exact h.keysUK y k hk
  have hBF : BFold G s B S d0 d U u (L.foldl (relaxIns G s B none) (d, D.deleteSet {u})) :=
    foldl_invariant _ (BFold G s B S d0 d U u) L _ hBF0 fun st e he hst =>
      bFold_step hpre h hu hst (by simpa using (hL.2 e).mp he) hucomp
  set st' := L.foldl (relaxIns G s B none) (d, D.deleteSet {u}) with hst'
  have hcompl : ∀ w, Complete d w → Complete st'.1 w :=
    fun w hw => complete_of_le hw (hBF.le w) hBF.walk.sound
  refine ⟨hBF.walk, fun v => (hBF.le v).trans (h.mono v), hBF.confined, hBF.stored, hBF.notU,
    hBF.inUK, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hcompl _ hucomp
    · exact hcompl _ (h.complete w hw)
  · intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact h.keysUK _ val hu
    · exact h.UUK w hw
  · intro w hw y k hk
    have habove := hBF.above y k hk
    rcases Finset.mem_insert.mp hw with rfl | hw
    · rw [hcompl _ hucomp, ← hucomp]; exact habove
    · rw [hcompl _ (h.complete w hw), ← h.complete w hw]
      have := h.order w hw u val hu
      rw [hval] at this
      exact this.trans habove
  · intro v hv hvU
    have hvU' : v ∉ U := fun h' => hvU (Finset.mem_insert_of_mem h')
    have hvu : v ≠ u := fun h' => hvU (h' ▸ Finset.mem_insert_self u U)
    obtain ⟨y0, hy0, hy0c, hvis⟩ := h.frontier v hv hvU'
    by_cases hy0u : y0 = u
    · subst hy0u
      obtain ⟨e, hsu, hdu, -, hon2, hdis⟩ := hvis.exists_exit ({y0} : Set (Fin G.n)) rfl
        (by simpa using hvu)
      have hse : G.src e = y0 := hsu
      have hB : dis (s := s) (G.dst e) < B := lt_of_le_of_lt hon2.dis_le hv.1
      have hcan := foldl_relaxIns_canonical (s := s) B none L (d, D.deleteSet {y0}) e
        ((hL.2 e).mpr (by simp [hse])) h.walk (by show d (G.src e) = _; rw [hse]; exact hucomp)
        hdis hB
      obtain ⟨hc1, hc2⟩ := hcan
      obtain ⟨k, hk, -⟩ := hc2 (fun b hb => absurd hb (by simp))
      refine ⟨G.dst e, ?_, hc1, hon2⟩
      rw [hk, (hBF.stored _ k hk).1, hc1]
    · have hy0' : (D.deleteSet {u}) y0 = some (dis (s := s) y0) := by
        rw [deleteSet_singleton_apply, if_neg hy0u]; exact hy0
      obtain ⟨k, hk, -⟩ := foldl_relaxIns_snd_le B none L (d, D.deleteSet {u}) y0 _ hy0'
      refine ⟨y0, ?_, hcompl _ hy0c, hvis⟩
      rw [hk, (hBF.stored _ k hk).1, hcompl _ hy0c]
  · intro x hx hxU
    have hxU' : x ∉ U := fun h' => hxU (Finset.mem_insert_of_mem h')
    have hxu : x ≠ u := fun h' => hxU (h' ▸ Finset.mem_insert_self u U)
    obtain ⟨k, hk, hkle⟩ := h.Skeys x hx hxU'
    have hk' : (D.deleteSet {u}) x = some k := by
      rw [deleteSet_singleton_apply, if_neg hxu]; exact hk
    obtain ⟨k', hk'', hk'le⟩ := foldl_relaxIns_snd_le B none L (d, D.deleteSet {u}) x k hk'
    exact ⟨k', hk'', hk'le.trans hkle⟩
  · intro w hw e he hB
    rcases Finset.mem_insert.mp hw with rfl | hw
    · have heL : e ∈ L := (hL.2 e).mpr (by simp [he])
      have := foldl_relaxIns_scan (s := s) B none L (d, D.deleteSet {w}) e heL h.walk
        (by show d (G.src e) = _; rw [he]; exact hucomp) (by rw [he]; exact hB)
      rw [he] at this
      exact this
    · exact (hBF.le _).trans (h.scanned w hw e he hB)

theorem baseLoop_inv {τ : ℕ} (hpre : CallPre B S d0) :
    ∀ st st', BaseLoop G s B τ st st' → BInv G s B S d0 st.1 st.2.1 st.2.2 →
      BInv G s B S d0 st'.1 st'.2.1 st'.2.2 ∧ (st'.2.1.IsEmpty ∨ τ ≤ st'.2.2.card) := by
  intro st st' hloop
  induction hloop with
  | stop st hstop => exact fun h => ⟨h, hstop⟩
  | step d D U u val L st' hu hmin _ hL _ ih =>
    intro h
    exact ih (bInv_step hpre h hu hmin hL)

/-- **Base case correctness** (B1 S2 §S2.3, with FIX-BASE). -/
theorem baseRel_post {τ : ℕ} {res : Result G s} (hpre : CallPre B S d0)
    (hres : BaseRel G s B S d0 τ res) : CallPost G s B S d0 τ res := by
  obtain ⟨⟨dS, DS0, US⟩, hloop, hU, hD, hd, hempty, hmin⟩ := hres
  obtain ⟨h, hstop⟩ := baseLoop_inv hpre _ _ hloop (bInv_init hpre)
  obtain ⟨B', U, D, d⟩ := res
  simp only at h hstop hU hD hd hempty hmin
  subst hU hD hd
  have hB'le : B' ≤ B := by
    by_cases he : D.IsEmpty
    · rw [hempty he]
    · obtain ⟨y, hy, -⟩ := hmin he
      exact (h.stored y B' hy).2.le
  have hU_below : ∀ u ∈ U, dis (s := s) u < B' := by
    intro u hu
    by_cases he : D.IsEmpty
    · rw [hempty he]; exact (h.UUK u hu).1
    · obtain ⟨y, hy, -⟩ := hmin he
      rw [← h.complete u hu]; exact h.order u hu y B' hy
  have hkey_ge : ∀ y k, D y = some k → B' ≤ k := by
    intro y k hk
    by_cases he : D.IsEmpty
    · exact absurd hk (by rw [he y]; simp)
    · obtain ⟨_, _, hmin'⟩ := hmin he; exact hmin' y k hk
  have hUeq : ∀ v, v ∈ U ↔ v ∈ Utilde B' (S : Set (Fin G.n)) := by
    intro v
    constructor
    · intro hv
      exact ⟨hU_below v hv, (h.UUK v hv).2⟩
    · intro hv
      by_contra hvU
      have hvB : v ∈ Utilde B (S : Set (Fin G.n)) := ⟨lt_of_lt_of_le hv.1 hB'le, hv.2⟩
      obtain ⟨y, hy, -, hvis⟩ := h.frontier v hvB hvU
      have := hkey_ge y _ hy
      exact absurd (lt_of_le_of_lt (this.trans hvis.dis_le) hv.1) (lt_irrefl _)
  refine ⟨hB'le, hUeq, h.complete, ?_, ?_, ?_, ?_, ?_, h.confined, h.Skeys, h.mono, h.walk,
    h.scanned⟩
  · intro v hv hvU
    exact h.frontier v hv hvU
  · intro y k hk
    refine ⟨h.keysUK y k hk, h.keysU y k hk, ?_, ?_, (h.stored y k hk).2⟩
    · by_contra hlt
      exact h.keysU y k hk ((hUeq y).mpr ⟨not_le.mp hlt, (h.keysUK y k hk).2⟩)
    · rw [(h.stored y k hk).1]
  · constructor
    · intro hB
      have hB' : B' = B := hB
      by_contra he
      obtain ⟨y, hy, -⟩ := hmin he
      have := (h.stored y B' hy).2
      rw [hB'] at this
      exact lt_irrefl _ this
    · intro he; exact hempty he
  · intro hlt
    rcases hstop with he | hcard
    · exact absurd (hempty he) (ne_of_lt hlt)
    · exact hcard
  · intro k hkB hk
    by_cases he : D.IsEmpty
    · rw [hempty he]; exact hkB
    · obtain ⟨y, hy, -⟩ := hmin he
      obtain ⟨-, z, hz, hzvis⟩ := h.keysUK y B' hy
      calc k ≤ dis (s := s) z := hk z hz
        _ ≤ dis (s := s) y := hzvis.dis_le
        _ ≤ d y := h.walk.sound y
        _ = B' := (h.stored y B' hy).1.symm

end base

/-! ## The loop invariant (B1 S2 Steps 0–1) -/

section contract

variable (G s)

/-- The set `A` of S2 Step 0: vertices of `Ũ` whose canonical path visits a vertex of `P_ini`
that was complete when FindPivots returned. -/
def Aset (B : WLab G s) (S : Finset (Fin G.n)) (d1 : Labels G s) {p : ℕ}
    (P0 : Fin p → Finset (Fin G.n)) : Set (Fin G.n) :=
  {v | v ∈ Utilde B (S : Set (Fin G.n)) ∧ ∃ j, ∃ y ∈ P0 j, Complete d1 y ∧ OnPath (s := s) y v}

/-- S2 Step 1: `y` is certified in loop state `σ`. -/
def Certified {p : ℕ} (σ : LState G s p) (y : Fin G.n) : Prop :=
  Complete σ.d y ∧
    (σ.D y = some (dis (s := s) y) ∨
      ∃ j, y ∈ σ.P j ∧ ∃ k, σ.D (σ.piv j) = some k ∧ k ≤ dis (s := s) y)

/-- The loop invariant (B1 S2 (J1)–(J4) plus bookkeeping). -/
structure LInv (B : WLab G s) (S : Finset (Fin G.n)) (d0 d1 : Labels G s) {p : ℕ}
    (P0 : Fin p → Finset (Fin G.n)) (B'0 : WLab G s) (σ : LState G s p) : Prop where
  walk : WalkInv σ.d
  mono : ∀ v, σ.d v ≤ d1 v
  confined : ∀ v, σ.d v ≠ d0 v → v ∈ Utilde B (S : Set (Fin G.n))
  storedGe : StoredGe G s σ.d σ.D
  keys : ∀ y k, σ.D y = some k → y ∈ Aset G s B S d1 P0 ∧ y ∉ σ.U ∧
    σ.B' ≤ dis (s := s) y ∧ k < B
  Pmem : ∀ j, ∀ y ∈ σ.P j, y ∈ Aset G s B S d1 P0 ∧ y ∉ σ.U ∧ σ.B' ≤ dis (s := s) y
  Psub : ∀ j, σ.P j ⊆ P0 j
  U_A : ∀ u ∈ σ.U, u ∈ Aset G s B S d1 P0
  U_complete : ∀ u ∈ σ.U, Complete σ.d u
  U_below : ∀ u ∈ σ.U, dis (s := s) u < σ.B'
  A_below : ∀ v ∈ Aset G s B S d1 P0, dis (s := s) v < σ.B' → v ∈ σ.U
  certified : ∀ v ∈ Aset G s B S d1 P0, v ∉ σ.U →
    ∃ y, Certified G s σ y ∧ OnPath (s := s) y v
  pivots : ∀ j, (σ.P j).Nonempty → σ.piv j ∈ σ.P j ∧ σ.D (σ.piv j) ≠ none
  B'_le : σ.B' ≤ B
  B'_ge : B'0 ≤ σ.B'
  scanned : ∀ u ∈ σ.U, ∀ e, G.src e = u → ext (dis (s := s) u) e < B →
    σ.d (G.dst e) ≤ ext (dis (s := s) u) e

end contract

section basic

variable {B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {p : ℕ}
  {P0 : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)}

/-- (A-closure) -/
theorem Aset_closure {v y : Fin G.n} (hv : v ∈ Aset G s B S d1 P0)
    (hy : y ∈ Utilde B (S : Set (Fin G.n))) (hvis : OnPath (s := s) v y) :
    y ∈ Aset G s B S d1 P0 := by
  obtain ⟨-, j, z, hz, hzc, hzv⟩ := hv
  exact ⟨hy, j, z, hz, hzc, hzv.trans hvis⟩

/-- `Ũ` is closed under canonical-path successors, below the bound. -/
theorem UK_closure {B' : WLab G s} {S' : Finset (Fin G.n)} {v y : Fin G.n}
    (hv : v ∈ Utilde B' (S' : Set (Fin G.n))) (hvis : OnPath (s := s) v y)
    (hy : dis (s := s) y < B') : y ∈ Utilde B' (S' : Set (Fin G.n)) := by
  obtain ⟨-, z, hz, hzv⟩ := hv
  exact ⟨hy, z, hz, hzv.trans hvis⟩

/-- (A-contains-P) -/
theorem Pini_sub_A (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W) {j : Fin p}
    {x : Fin G.n} (hx : x ∈ P0 j) : x ∈ Aset G s B S d1 P0 := by
  have hxU : x ∈ Utilde B (S : Set (Fin G.n)) := S_sub_of_pre hpre x ((hfp.groups j).2 hx)
  by_cases hc : Complete d1 x
  · exact ⟨hxU, j, x, hx, hc, onPath_self (hxU.2.choose_spec.2.1)⟩
  · rcases hfp.frontier x hxU with ⟨-, h⟩ | ⟨y, ⟨j', hy⟩, hyc, hyv⟩
    · exact absurd h hc
    · exact ⟨hxU, j', y, hy, hyc, hyv⟩

/-- Vertices of `Ũ \ A` are in `W` and complete after FindPivots. -/
theorem Wc_complete (hfp : FPContract B S d0 d1 p P0 Q W) {v : Fin G.n}
    (hv : v ∈ Utilde B (S : Set (Fin G.n))) (hvA : v ∉ Aset G s B S d1 P0) :
    v ∈ W ∧ Complete d1 v := by
  rcases hfp.frontier v hv with h | ⟨y, ⟨j, hy⟩, hyc, hyv⟩
  · exact h
  · exact absurd ⟨hv, j, y, hy, hyc, hyv⟩ hvA

/-- The canonical label of a head is at most the extension of the tail's canonical label. -/
theorem dis_le_ext_dis {e : Fin G.m} (hr : dis (s := s) (G.src e) ≠ ⊤) :
    dis (s := s) (G.dst e) ≤ ext (dis (s := s) (G.src e)) e := by
  have hsr : G.Reachable s (G.src e) := by
    by_contra hc; exact hr (dis_of_not_reachable hc)
  rw [dis_of_reachable hsr, ext_coe]
  exact dis_le_walk (walk_ext (path_isMinWalk hsr).1 e rfl)

/-- The initial progress bound `B'_0 = min(B, min_j d[p_j])` (BM.8). -/
noncomputable def initB' (B : WLab G s) (d1 : Labels G s) (piv : Fin p → Fin G.n) : WLab G s :=
  min B (Finset.univ.inf fun j => d1 (piv j))

/-- The initial loop state (BM.5–BM.8). -/
noncomputable def initState (B : WLab G s) (d1 : Labels G s) (P0 : Fin p → Finset (Fin G.n))
    (piv : Fin p → Fin G.n) : LState G s p :=
  { d := d1, D := insertMany G s DS.empty (Finset.univ.image piv) d1,
    P := P0, piv := piv, U := ∅, B' := initB' B d1 piv }

/-- (A-bound) -/
theorem A_bound {piv : Fin p → Fin G.n}
    (hpiv : ∀ j, piv j ∈ P0 j ∧ ∀ x ∈ P0 j, d1 (piv j) ≤ d1 x)
    {v : Fin G.n} (hv : v ∈ Aset G s B S d1 P0) :
    initB' B d1 piv ≤ dis (s := s) v := by
  obtain ⟨-, j, y, hy, hyc, hyv⟩ := hv
  calc initB' B d1 piv ≤ Finset.univ.inf fun j => d1 (piv j) := min_le_right _ _
    _ ≤ d1 (piv j) := Finset.inf_le (Finset.mem_univ j)
    _ ≤ d1 y := (hpiv j).2 y hy
    _ = dis (s := s) y := hyc
    _ ≤ dis (s := s) v := hyv.dis_le

theorem linv_init (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W)
    {piv : Fin p → Fin G.n} (hpiv : ∀ j, piv j ∈ P0 j ∧ ∀ x ∈ P0 j, d1 (piv j) ≤ d1 x) :
    LInv G s B S d0 d1 P0 (initB' B d1 piv) (initState B d1 P0 piv) where
  walk := hfp.walk
  mono := fun _ => le_rfl
  confined := hfp.changed
  storedGe := by
    intro y k hk
    simp only [initState] at hk ⊢
    rw [insertMany_empty_apply] at hk
    split_ifs at hk
    simp only [Option.some.injEq] at hk
    rw [hk]
  keys := by
    intro y k hk
    simp only [initState] at hk ⊢
    rw [insertMany_empty_apply] at hk
    split_ifs at hk with hy
    simp only [Option.some.injEq] at hk
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
    have hA := Pini_sub_A hpre hfp (hpiv j).1
    refine ⟨hA, Finset.notMem_empty _, A_bound hpiv hA, ?_⟩
    rw [← hk]
    exact lt_of_le_of_lt (hfp.le _) (hpre.inRange _ ((hfp.groups j).2 (hpiv j).1))
  Pmem := by
    intro j y hy
    have hA := Pini_sub_A hpre hfp hy
    exact ⟨hA, Finset.notMem_empty _, A_bound hpiv hA⟩
  Psub := fun _ => subset_rfl
  U_A := by simp [initState]
  U_complete := by simp [initState]
  U_below := by simp [initState]
  A_below := by
    intro v hv hlt
    exact absurd (A_bound hpiv hv) (not_le.mpr hlt)
  certified := by
    intro v hv _
    obtain ⟨-, j, y, hy, hyc, hyv⟩ := hv
    refine ⟨y, ⟨hyc, Or.inr ⟨j, hy, d1 (piv j), ?_, ?_⟩⟩, hyv⟩
    · simp only [initState]
      rw [insertMany_empty_apply, if_pos (Finset.mem_image_of_mem _ (Finset.mem_univ j))]
    · rw [← hyc]; exact (hpiv j).2 y hy
  pivots := by
    intro j _
    refine ⟨(hpiv j).1, ?_⟩
    simp only [initState]
    rw [insertMany_empty_apply, if_pos (Finset.mem_image_of_mem _ (Finset.mem_univ j))]
    simp
  B'_le := min_le_left _ _
  B'_ge := le_rfl
  scanned := by simp [initState]

theorem mem_expand {σ : LState G s p} {S0 : Finset (Fin G.n)} {Bi : WLab G s} {x : Fin G.n} :
    x ∈ expand σ S0 Bi ↔ x ∈ S0 ∨
      ∃ j, σ.piv j ∈ S0 ∧ σ.piv j ∈ σ.P j ∧ x ∈ σ.P j ∧ σ.d x < Bi := by
  unfold expand
  simp

theorem mem_reselected {σ : LState G s p} {Ui : Finset (Fin G.n)} {piv' : Fin p → Fin G.n}
    {x : Fin G.n} : x ∈ reselected σ Ui piv' ↔
      ∃ j, piv' j = x ∧ σ.piv j ∈ Ui ∧ (σ.P j \ Ui).Nonempty := by
  unfold reselected
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨-, h⟩; exact h
  · rintro ⟨j, hj, h⟩; exact ⟨⟨j, hj⟩, j, hj, h⟩

end basic

/-! ## The loop step (S2 Steps 2–4) -/

section step

variable {B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {p : ℕ}
  {P0 : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {B'0 : WLab G s}
  {σ : LState G s p} {S0 : Finset (Fin G.n)} {Bi : WLab G s} {D1 : DS G s}

/-- (S-a) -/
theorem Si_facts (h : LInv G s B S d0 d1 P0 B'0 σ) (hpull : PullSpec σ.D B S0 Bi D1)
    {x : Fin G.n} (hx : x ∈ expand σ S0 Bi) :
    (x ∈ Aset G s B S d1 P0 ∧ x ∉ σ.U ∧ σ.B' ≤ dis (s := s) x) ∧ σ.d x < Bi := by
  rcases mem_expand.mp hx with hx0 | ⟨j, -, -, hxP, hxlt⟩
  · obtain ⟨k, hk, hklt⟩ := (hpull.pulled x).mp hx0
    obtain ⟨hA, hU, hB, -⟩ := h.keys x k hk
    exact ⟨⟨hA, hU, hB⟩, lt_of_le_of_lt (h.storedGe x k hk) hklt⟩
  · exact ⟨h.Pmem j x hxP, hxlt⟩

/-- (S-b) -/
theorem certified_mem_expand (h : LInv G s B S d0 d1 P0 B'0 σ)
    (hpull : PullSpec σ.D B S0 Bi D1) {y : Fin G.n} (hc : Certified G s σ y)
    (hlt : dis (s := s) y < Bi) : y ∈ expand σ S0 Bi := by
  obtain ⟨hyc, hc⟩ := hc
  rcases hc with hkey | ⟨j, hyP, k, hk, hkle⟩
  · exact mem_expand.mpr (Or.inl ((hpull.pulled y).mpr ⟨_, hkey, hlt⟩))
  · have hpj : σ.piv j ∈ S0 := (hpull.pulled _).mpr ⟨k, hk, lt_of_le_of_lt hkle hlt⟩
    have hpP := (h.pivots j ⟨y, hyP⟩).1
    exact mem_expand.mpr (Or.inr ⟨j, hpj, hpP, hyP, by rw [hyc]; exact hlt⟩)

theorem UKi_sub (h : LInv G s B S d0 d1 P0 B'0 σ) (hpull : PullSpec σ.D B S0 Bi D1)
    {v : Fin G.n} (hv : v ∈ Utilde Bi (expand σ S0 Bi : Set (Fin G.n))) :
    v ∈ Aset G s B S d1 P0 ∧ v ∉ σ.U ∧ σ.B' ≤ dis (s := s) v := by
  obtain ⟨hvlt, z, hz, hzv⟩ := hv
  obtain ⟨⟨hzA, -, hzB⟩, -⟩ := Si_facts h hpull hz
  have hvB : dis (s := s) v < B := lt_of_lt_of_le hvlt hpull.bound
  have hvA : v ∈ Aset G s B S d1 P0 := Aset_closure hzA (UK_closure hzA.1 hzv hvB) hzv
  have hge : σ.B' ≤ dis (s := s) v := hzB.trans hzv.dis_le
  exact ⟨hvA, fun hvU => absurd (h.U_below v hvU) (not_lt.mpr hge), hge⟩

/-- **S2 Step 2**: the sub-call satisfies the call preconditions. -/
theorem step_pre (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W)
    (h : LInv G s B S d0 d1 P0 B'0 σ) (hpull : PullSpec σ.D B S0 Bi D1) :
    CallPre Bi (expand σ S0 Bi) σ.d where
  walk := h.walk
  claimC := by
    intro v hvlt hvnot
    have hvB : dis (s := s) v < B := lt_of_lt_of_le hvlt hpull.bound
    by_cases hvUK : v ∈ Utilde B (S : Set (Fin G.n))
    · by_cases hvA : v ∈ Aset G s B S d1 P0
      · by_cases hvU : v ∈ σ.U
        · exact h.U_complete v hvU
        · obtain ⟨y, hyc, hyv⟩ := h.certified v hvA hvU
          have hyS := certified_mem_expand h hpull hyc (lt_of_le_of_lt hyv.dis_le hvlt)
          exact absurd ⟨hvlt, y, hyS, hyv⟩ hvnot
      · have hc := (Wc_complete hfp hvUK hvA).2
        exact complete_of_le hc (h.mono v) h.walk.sound
    · have hc := hpre.claimC v hvB hvUK
      exact complete_of_le hc ((h.mono v).trans (hfp.le v)) h.walk.sound
  frontier := by
    intro v hv
    obtain ⟨hvA, hvU, -⟩ := UKi_sub h hpull hv
    obtain ⟨y, hyc, hyv⟩ := h.certified v hvA hvU
    exact Or.inr ⟨y, certified_mem_expand h hpull hyc (lt_of_le_of_lt hyv.dis_le hv.1),
      hyc.1, hyv⟩
  inRange := fun x hx => (Si_facts h hpull hx).2

theorem pull_rest_some (hpull : PullSpec σ.D B S0 Bi D1) {y : Fin G.n} {k : WLab G s}
    (hk : D1 y = some k) : σ.D y = some k ∧ y ∉ S0 := by
  rw [hpull.rest y] at hk
  split_ifs at hk with hy
  exact ⟨hk, hy⟩

theorem pull_rest_keep (hpull : PullSpec σ.D B S0 Bi D1) {y : Fin G.n} (hy : y ∉ S0) :
    D1 y = σ.D y := by
  rw [hpull.rest y, if_neg hy]

/-- **S2 Steps 3–4**: after the sub-call, Merge, FIX-STALE deletion, the relaxations out of
`U_i` and the re-selection, the loop invariant holds for the next state. -/
theorem step_post (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W)
    (h : LInv G s B S d0 d1 P0 B'0 σ) (hne : ¬ σ.D.IsEmpty) (hpull : PullSpec σ.D B S0 Bi D1)
    {cap : ℕ} {B'i : WLab G s} {Ui : Finset (Fin G.n)} {Di : DS G s} {d1' : Labels G s}
    (hpost : CallPost G s Bi (expand σ S0 Bi) σ.d cap (B'i, Ui, Di, d1'))
    {L : List (Fin G.m)} (hL : Enumerates G L Ui) {piv' : Fin p → Fin G.n}
    (hres : Reselect σ Ui
      (L.foldl (relaxIns G s B (some Bi)) (d1', (D1.merge Di).deleteSet Ui)).1 piv') :
    LInv G s B S d0 d1 P0 B'0
      { d := (L.foldl (relaxIns G s B (some Bi)) (d1', (D1.merge Di).deleteSet Ui)).1
        D := insertMany G s
              (L.foldl (relaxIns G s B (some Bi)) (d1', (D1.merge Di).deleteSet Ui)).2
              (reselected σ Ui piv')
              (L.foldl (relaxIns G s B (some Bi)) (d1', (D1.merge Di).deleteSet Ui)).1
        P := fun j => σ.P j \ Ui
        piv := piv'
        U := σ.U ∪ Ui
        B' := B'i } := by
  set Si := expand σ S0 Bi with hSi
  set st0 : Labels G s × DS G s := (d1', (D1.merge Di).deleteSet Ui) with hst0
  set st2 := L.foldl (relaxIns G s B (some Bi)) st0 with hst2
  set d2 := st2.1 with hd2
  set Dn := insertMany G s st2.2 (reselected σ Ui piv') d2 with hDn
  have hsubpre : CallPre Bi Si σ.d := step_pre hpre hfp h hpull
  have hBiB : Bi ≤ B := hpull.bound
  -- Step 3
  have hB'Bi : σ.B' ≤ Bi := by
    obtain ⟨y, hy⟩ := hpull.nonempty (by
      by_contra hc; push_neg at hc; exact hne hc)
    obtain ⟨k, hk, hklt⟩ := (hpull.pulled y).mp hy
    obtain ⟨-, -, hB, -⟩ := h.keys y k hk
    exact (hB.trans ((h.walk.sound y).trans (h.storedGe y k hk))).trans hklt.le
  have hB'ge : σ.B' ≤ B'i :=
    hpost.B'_ge σ.B' hB'Bi (fun x hx => (Si_facts h hpull hx).1.2.2)
  have hB'iBi : B'i ≤ Bi := hpost.B'_le
  have hUi : ∀ u ∈ Ui, u ∈ Aset G s B S d1 P0 ∧ u ∉ σ.U ∧ dis (s := s) u < B'i ∧
      Complete d1' u := by
    intro u hu
    have hu' := (hpost.U_eq u).mp hu
    have huBi : u ∈ Utilde Bi (Si : Set (Fin G.n)) := ⟨lt_of_lt_of_le hu'.1 hB'iBi, hu'.2⟩
    obtain ⟨hA, hU, -⟩ := UKi_sub h hpull huBi
    exact ⟨hA, hU, hu'.1, hpost.U_complete u hu⟩
  have hAbelow : ∀ v ∈ Aset G s B S d1 P0, dis (s := s) v < B'i → v ∈ σ.U ∨ v ∈ Ui := by
    intro v hvA hvlt
    by_cases hvU : v ∈ σ.U
    · exact Or.inl hvU
    · obtain ⟨y, hyc, hyv⟩ := h.certified v hvA hvU
      have hyS : y ∈ Si := certified_mem_expand h hpull hyc
        (lt_of_le_of_lt hyv.dis_le (lt_of_lt_of_le hvlt hB'iBi))
      exact Or.inr ((hpost.U_eq v).mpr ⟨hvlt, y, hyS, hyv⟩)
  have hAge : ∀ v ∈ Aset G s B S d1 P0, v ∉ σ.U → v ∉ Ui → B'i ≤ dis (s := s) v := by
    intro v hvA hvU hvUi
    by_contra hc
    rcases hAbelow v hvA (not_le.mp hc) with h1 | h1
    · exact hvU h1
    · exact hvUi h1
  -- labels
  have hw1 : WalkInv d1' := hpost.walk
  have hle1 : ∀ v, d1' v ≤ σ.d v := hpost.mono
  have hle2 : ∀ v, d2 v ≤ d1' v := fun v => foldl_relaxIns_fst_le B (some Bi) L st0 v
  have hw2 : WalkInv d2 := foldl_relaxIns_walk B (some Bi) L st0 hw1
  have hle2d1 : ∀ v, d2 v ≤ d1 v := fun v => (hle2 v).trans ((hle1 v).trans (h.mono v))
  have hcomp2 : ∀ v, Complete σ.d v → Complete d2 v :=
    fun v hv => complete_of_le hv ((hle2 v).trans (hle1 v)) hw2.sound
  have hcomp2' : ∀ v, Complete d1' v → Complete d2 v :=
    fun v hv => complete_of_le hv (hle2 v) hw2.sound
  have hLsrc : ∀ e ∈ L, Complete st0.1 (G.src e) := by
    intro e he
    have hsrc : G.src e ∈ Ui := by simpa using (hL.2 e).mp he
    exact (hUi _ hsrc).2.2.2
  -- stored values dominate labels
  have hsg0 : StoredGe G s st0.1 st0.2 := by
    have hD1 : StoredGe G s d1' D1 := by
      intro y k hk
      obtain ⟨hk', -⟩ := pull_rest_some hpull hk
      exact (hle1 y).trans (h.storedGe y k hk')
    have hDi : StoredGe G s d1' Di := fun y k hk => (hpost.keys y k hk).2.2.2.1
    exact storedGe_deleteSet Ui (storedGe_merge hD1 hDi)
  have hsg2 : StoredGe G s d2 st2.2 := foldl_relaxIns_storedGe B (some Bi) L st0 hsg0
  have hsgn : StoredGe G s d2 Dn := storedGe_insertMany _ hsg2
  -- exact keys persist
  have hexact : ∀ y k, st0.2 y = some k → k ≤ dis (s := s) y → Dn y = some (dis (s := s) y) := by
    intro y k hk hkle
    obtain ⟨k2, hk2, hk2le⟩ : ∃ k', st2.2 y = some k' ∧ k' ≤ k :=
      foldl_relaxIns_snd_le B (some Bi) L st0 y k hk
    obtain ⟨k3, hk3, hk3le⟩ : ∃ k', Dn y = some k' ∧ k' ≤ k2 :=
      insertMany_le (reselected σ Ui piv') d2 hk2
    have hge : dis (s := s) y ≤ k3 := (hw2.sound y).trans (hsgn y k3 hk3)
    rw [hk3, le_antisymm (hk3le.trans (hk2le.trans hkle)) hge]
  have hst0_apply : ∀ y, st0.2 y = if y ∈ Ui then none else DS.mergeVal (D1 y) (Di y) :=
    fun y => rfl
  have hDi_exact : ∀ y, Di y = some (dis (s := s) y) → Dn y = some (dis (s := s) y) := by
    intro y hy
    have hyUi : y ∉ Ui := (hpost.keys y _ hy).2.1
    obtain ⟨k, hk, hkle⟩ := DSx.mergeVal_le_right (a := D1 y) hy
    have hst : st0.2 y = some k := by rw [hst0_apply, if_neg hyUi]; exact hk
    exact hexact y k hst hkle
  have hkeep : ∀ y k, st0.2 y = some k → ∃ k', Dn y = some k' ∧ k' ≤ k := by
    intro y k hk
    obtain ⟨k2, hk2, hk2le⟩ : ∃ k', st2.2 y = some k' ∧ k' ≤ k :=
      foldl_relaxIns_snd_le B (some Bi) L st0 y k hk
    obtain ⟨k3, hk3, hk3le⟩ : ∃ k', Dn y = some k' ∧ k' ≤ k2 :=
      insertMany_le (reselected σ Ui piv') d2 hk2
    exact ⟨k3, hk3, hk3le.trans hk2le⟩
  -- the key property of the new structure
  let Pk : Fin G.n → WLab G s → Prop := fun y k =>
    y ∈ Aset G s B S d1 P0 ∧ y ∉ σ.U ∧ y ∉ Ui ∧ B'i ≤ dis (s := s) y ∧ k < B
  have hPk0 : ∀ y k, st0.2 y = some k → Pk y k := by
    intro y k hk
    rw [hst0_apply] at hk
    split_ifs at hk with hyUi
    rcases DSx.mergeVal_cases _ _ _ hk with h1 | h1
    · obtain ⟨hk', -⟩ := pull_rest_some hpull h1
      obtain ⟨hA, hU, -, hkB⟩ := h.keys y k hk'
      exact ⟨hA, hU, hyUi, hAge y hA hU hyUi, hkB⟩
    · obtain ⟨hyUK, -, hB', -, hkBi⟩ := hpost.keys y k h1
      obtain ⟨hA, hU, -⟩ := UKi_sub h hpull hyUK
      exact ⟨hA, hU, hyUi, hB', lt_of_lt_of_le hkBi hBiB⟩
  have hPkL : ∀ e ∈ L, ∀ d' : Labels G s, Sound d' → (∀ v, d' v ≤ st0.1 v) →
      Complete d' (G.src e) → ValidRelax G s d' B e →
      (∀ b, some Bi = some b → b ≤ ext (dis (s := s) (G.src e)) e) →
      Pk (G.dst e) (ext (dis (s := s) (G.src e)) e) := by
    intro e he d' hs' hd' hsrc' hv hlo
    have hsrc : G.src e ∈ Ui := by simpa using (hL.2 e).mp he
    obtain ⟨hsA, -, hslt, -⟩ := hUi _ hsrc
    have hd'0 : ∀ v, d' v ≤ d0 v := fun v =>
      (hd' v).trans ((hle1 v).trans ((h.mono v).trans (hfp.le v)))
    have hvUK : G.dst e ∈ Utilde B (S : Set (Fin G.n)) :=
      mem_UK_of_valid hpre hs' hd'0 hsA.1 hsrc' hv
    have hcandB : ext (dis (s := s) (G.src e)) e < B := by
      rw [← hsrc']; exact hv.2
    have hloBi : Bi ≤ ext (dis (s := s) (G.src e)) e := hlo Bi rfl
    have hsfin : dis (s := s) (G.src e) ≠ ⊤ := ne_top_of_lt hsA.1.1
    have htight : Complete d' (G.dst e) → OnPath (s := s) (G.src e) (G.dst e) := by
      intro hc
      have hle := hv.1
      rw [hsrc', hc] at hle
      exact onPath_of_tight (le_antisymm hle (dis_le_ext_dis hsfin)) hsfin
    have hvA : G.dst e ∈ Aset G s B S d1 P0 := by
      by_contra hvA
      have hc1 := (Wc_complete hfp hvUK hvA).2
      have hc' : Complete d' (G.dst e) :=
        complete_of_le hc1 ((hd' _).trans ((hle1 _).trans (h.mono _))) hs'
      exact hvA (Aset_closure hsA hvUK (htight hc'))
    have hnotin : ∀ w, Complete d' w → dis (s := s) w < B'i → G.dst e ≠ w := by
      intro w hwc hwlt hw
      subst hw
      have hle := hv.1
      rw [hwc, hsrc'] at hle
      have : ext (dis (s := s) (G.src e)) e < Bi := lt_of_le_of_lt hle (lt_of_lt_of_le hwlt hB'iBi)
      exact absurd hloBi (not_le.mpr this)
    have hvU : G.dst e ∉ σ.U := by
      intro hvU
      exact hnotin _ (complete_of_le (h.U_complete _ hvU) ((hd' _).trans (hle1 _)) hs')
        (lt_of_lt_of_le (h.U_below _ hvU) hB'ge) rfl
    have hvUi : G.dst e ∉ Ui := by
      intro hvUi
      obtain ⟨-, -, hlt', hc'⟩ := hUi _ hvUi
      exact hnotin _ (complete_of_le hc' (hd' _) hs') hlt' rfl
    exact ⟨hvA, hvU, hvUi, hAge _ hvA hvU hvUi, hcandB⟩
  have hPk2 : ∀ y k, st2.2 y = some k → Pk y k :=
    foldl_relaxIns_keys B (some Bi) Pk L st0 hw1.sound hLsrc hPk0 hPkL
  have hPkn : ∀ y k, Dn y = some k → Pk y k := by
    intro y k hk
    rcases insertMany_key_cases hk with h1 | ⟨hy, rfl⟩
    · exact hPk2 y k h1
    · obtain ⟨j, rfl, hpUi, hne'⟩ := mem_reselected.mp hy
      obtain ⟨hmem, -⟩ := hres.resel j hpUi hne'
      obtain ⟨hPj, hnotUi⟩ := Finset.mem_sdiff.mp hmem
      obtain ⟨hA, hU, -⟩ := h.Pmem j _ hPj
      refine ⟨hA, hU, hnotUi, hAge _ hA hU hnotUi, ?_⟩
      have hS : piv' j ∈ S := (hfp.groups j).2 (h.Psub j hPj)
      exact lt_of_le_of_lt ((hle2d1 _).trans (hfp.le _)) (hpre.inRange _ hS)
  refine
    { walk := hw2
      mono := hle2d1
      confined := ?_
      storedGe := hsgn
      keys := ?_
      Pmem := ?_
      Psub := fun j => (Finset.sdiff_subset).trans (h.Psub j)
      U_A := ?_
      U_complete := ?_
      U_below := ?_
      A_below := ?_
      certified := ?_
      pivots := ?_
      B'_le := hB'iBi.trans hBiB
      B'_ge := h.B'_ge.trans hB'ge
      scanned := ?_ }
  · -- confined
    intro v hv
    change d2 v ≠ d0 v at hv
    by_cases h2 : d2 v = d1' v
    · rw [h2] at hv
      by_cases h1 : d1' v = σ.d v
      · rw [h1] at hv; exact h.confined v hv
      · exact (UKi_sub h hpull (hpost.confined v h1)).1.1
    · obtain ⟨hlt, hkey⟩ := foldl_relaxIns_changed B (some Bi) L st0 v h2
      by_contra hvUK
      have hc := hpre.claimC v (lt_of_le_of_lt (hw2.sound v) hkey) hvUK
      have : d2 v < dis (s := s) v := by
        calc d2 v < d1' v := hlt
          _ ≤ d0 v := (hle1 v).trans ((h.mono v).trans (hfp.le v))
          _ = dis (s := s) v := hc
      exact absurd (hw2.sound v) (not_le.mpr this)
  · -- keys
    intro y k hk
    obtain ⟨hA, hU, hUi', hB', hkB⟩ := hPkn y k hk
    exact ⟨hA, fun hm => (Finset.mem_union.mp hm).elim hU hUi', hB', hkB⟩
  · -- Pmem
    intro j y hy
    obtain ⟨hyP, hyUi⟩ := Finset.mem_sdiff.mp hy
    obtain ⟨hA, hU, -⟩ := h.Pmem j y hyP
    exact ⟨hA, fun hm => (Finset.mem_union.mp hm).elim hU hyUi, hAge y hA hU hyUi⟩
  · -- U_A
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact h.U_A u hu
    · exact (hUi u hu).1
  · -- U_complete
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact hcomp2 u (h.U_complete u hu)
    · exact hcomp2' u (hUi u hu).2.2.2
  · -- U_below
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact lt_of_lt_of_le (h.U_below u hu) hB'ge
    · exact (hUi u hu).2.2.1
  · -- A_below
    intro v hvA hvlt
    rcases hAbelow v hvA hvlt with h1 | h1
    · exact Finset.mem_union_left _ h1
    · exact Finset.mem_union_right _ h1
  · -- certified (S2 Step 4, J3)
    intro v hvA hvnot
    have hvU : v ∉ σ.U := fun hm => hvnot (Finset.mem_union_left _ hm)
    have hvUi : v ∉ Ui := fun hm => hvnot (Finset.mem_union_right _ hm)
    have hvB : dis (s := s) v < B := hvA.1.1
    by_cases hcase : ∃ x ∈ Ui, OnPath (s := s) x v
    · -- Case 1: the canonical path leaves U_i through an exit edge
      obtain ⟨x, hxUi, hxv⟩ := hcase
      obtain ⟨e, hsUi, hdUi, -, hbv, htight⟩ := hxv.exists_exit (Ui : Set (Fin G.n)) hxUi hvUi
      obtain ⟨-, -, hslt, hsc⟩ := hUi _ hsUi
      have hbB : dis (s := s) (G.dst e) < B := lt_of_le_of_lt hbv.dis_le hvB
      by_cases hbBi : dis (s := s) (G.dst e) < Bi
      · have hsUK : G.src e ∈ Utilde Bi (Si : Set (Fin G.n)) := by
          have := (hpost.U_eq _).mp hsUi
          exact ⟨lt_of_lt_of_le this.1 hB'iBi, this.2⟩
        have hab : OnPath (s := s) (G.src e) (G.dst e) :=
          onPath_of_tight htight.symm (ne_top_of_lt hslt)
        have hbUK : G.dst e ∈ Utilde Bi (Si : Set (Fin G.n)) := UK_closure hsUK hab hbBi
        obtain ⟨y', hy'D, hy'c, hy'v⟩ := hpost.certified _ hbUK hdUi
        exact ⟨y', ⟨hcomp2' y' hy'c, Or.inl (hDi_exact y' hy'D)⟩, hy'v.trans hbv⟩
      · have he : e ∈ L := (hL.2 e).mpr (by simpa using hsUi)
        obtain ⟨hbc, hbk⟩ := foldl_relaxIns_canonical (s := s) B (some Bi) L st0 e he hw1
          hsc htight hbB
        obtain ⟨k, hk, hkle⟩ := hbk (fun b hb => by
          simp only [Option.some.injEq] at hb; subst hb; exact not_lt.mp hbBi)
        obtain ⟨k3, hk3, hk3le⟩ : ∃ k', Dn (G.dst e) = some k' ∧ k' ≤ k :=
          insertMany_le (reselected σ Ui piv') d2 hk
        have hge : dis (s := s) (G.dst e) ≤ k3 := (hw2.sound _).trans (hsgn _ k3 hk3)
        refine ⟨G.dst e, ⟨hbc, Or.inl ?_⟩, hbv⟩
        show Dn (G.dst e) = _
        rw [hk3, le_antisymm (hk3le.trans hkle) hge]
    · -- Case 2: the canonical path avoids U_i
      push_neg at hcase
      obtain ⟨y, ⟨hyc, hyc'⟩, hyv⟩ := h.certified v hvA hvU
      have hyUi : y ∉ Ui := fun hm => hcase y hm hyv
      by_cases hyS : y ∈ Si
      · have hyUK : y ∈ Utilde Bi (Si : Set (Fin G.n)) := S_sub_of_pre hsubpre y hyS
        obtain ⟨y', hy'D, hy'c, hy'v⟩ := hpost.certified y hyUK hyUi
        exact ⟨y', ⟨hcomp2' y' hy'c, Or.inl (hDi_exact y' hy'D)⟩, hy'v.trans hyv⟩
      · have hyS0 : y ∉ S0 := fun hm => hyS (mem_expand.mpr (Or.inl hm))
        rcases hyc' with hkey | ⟨j, hyP, k, hk, hkle⟩
        · obtain ⟨k0, hk0, hk0le⟩ := DSx.mergeVal_le_left (b := Di y) hkey
          have : st0.2 y = some k0 := by
            rw [hst0_apply, if_neg hyUi, pull_rest_keep hpull hyS0]
            exact hk0
          exact ⟨y, ⟨hcomp2 y hyc, Or.inl (hexact y k0 this hk0le)⟩, hyv⟩
        · have hyP' : y ∈ σ.P j \ Ui := Finset.mem_sdiff.mpr ⟨hyP, hyUi⟩
          refine ⟨y, ⟨hcomp2 y hyc, Or.inr ⟨j, hyP', ?_⟩⟩, hyv⟩
          by_cases hpUi : σ.piv j ∈ Ui
          · obtain ⟨hmem, hmin⟩ := hres.resel j hpUi ⟨y, hyP'⟩
            have hrs : piv' j ∈ reselected σ Ui piv' :=
              mem_reselected.mpr ⟨j, rfl, hpUi, ⟨y, hyP'⟩⟩
            obtain ⟨k', hk', hk'le⟩ : ∃ k', Dn (piv' j) = some k' ∧ k' ≤ d2 (piv' j) :=
              insertMany_mem (D := st2.2) d2 hrs
            refine ⟨k', hk', hk'le.trans ?_⟩
            have := hmin y hyP'
            rw [hcomp2 y hyc] at this
            exact this
          · have hkeepj : piv' j = σ.piv j := hres.keep j (fun hc => hpUi hc.1)
            show ∃ k, Dn (piv' j) = some k ∧ k ≤ dis (s := s) y
            rw [hkeepj]
            by_cases hpS0 : σ.piv j ∈ S0
            · have hpSi : σ.piv j ∈ Si := mem_expand.mpr (Or.inl hpS0)
              obtain ⟨k'', hk'', hk''le⟩ := hpost.S_keys _ hpSi hpUi
              obtain ⟨k0, hk0, hk0le⟩ := DSx.mergeVal_le_right (a := D1 (σ.piv j)) hk''
              have hst : st0.2 (σ.piv j) = some k0 := by
                rw [hst0_apply, if_neg hpUi]
                exact hk0
              obtain ⟨k', hk', hk'le⟩ := hkeep _ _ hst
              refine ⟨k', hk', hk'le.trans (hk0le.trans (hk''le.trans ?_))⟩
              exact (h.storedGe _ k hk).trans hkle
            · obtain ⟨k0, hk0, hk0le⟩ := DSx.mergeVal_le_left (b := Di (σ.piv j)) hk
              have hst : st0.2 (σ.piv j) = some k0 := by
                rw [hst0_apply, if_neg hpUi, pull_rest_keep hpull hpS0]
                exact hk0
              obtain ⟨k', hk', hk'le⟩ := hkeep _ _ hst
              exact ⟨k', hk', hk'le.trans (hk0le.trans hkle)⟩
  · -- pivots (J4)
    intro j hj
    by_cases hpUi : σ.piv j ∈ Ui
    · obtain ⟨hmem, -⟩ := hres.resel j hpUi hj
      have hrs : piv' j ∈ reselected σ Ui piv' := mem_reselected.mpr ⟨j, rfl, hpUi, hj⟩
      obtain ⟨k', hk', -⟩ : ∃ k', Dn (piv' j) = some k' ∧ k' ≤ d2 (piv' j) :=
        insertMany_mem (D := st2.2) d2 hrs
      refine ⟨hmem, ?_⟩
      show Dn (piv' j) ≠ none
      rw [hk']; simp
    · have hkeepj : piv' j = σ.piv j := hres.keep j (fun hc => hpUi hc.1)
      have hPj : (σ.P j).Nonempty := hj.mono Finset.sdiff_subset
      obtain ⟨hpP, hpD⟩ := h.pivots j hPj
      refine ⟨?_, ?_⟩
      · show piv' j ∈ σ.P j \ Ui
        rw [hkeepj]; exact Finset.mem_sdiff.mpr ⟨hpP, hpUi⟩
      show Dn (piv' j) ≠ none
      rw [hkeepj]
      obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hpD
      by_cases hpS0 : σ.piv j ∈ S0
      · have hpSi : σ.piv j ∈ Si := mem_expand.mpr (Or.inl hpS0)
        obtain ⟨k'', hk'', -⟩ := hpost.S_keys _ hpSi hpUi
        obtain ⟨k0, hk0, -⟩ := DSx.mergeVal_le_right (a := D1 (σ.piv j)) hk''
        have hst : st0.2 (σ.piv j) = some k0 := by
          rw [hst0_apply, if_neg hpUi]
          exact hk0
        obtain ⟨k', hk', -⟩ := hkeep _ _ hst
        rw [hk']; simp
      · obtain ⟨k0, hk0, -⟩ := DSx.mergeVal_le_left (b := Di (σ.piv j)) hk
        have hst : st0.2 (σ.piv j) = some k0 := by
          rw [hst0_apply, if_neg hpUi, pull_rest_keep hpull hpS0]
          exact hk0
        obtain ⟨k', hk', -⟩ := hkeep _ _ hst
        rw [hk']; simp
  · -- scanned (S2 Lemma S2.4)
    intro u hu e he hB
    rcases Finset.mem_union.mp hu with hu | hu
    · exact ((hle2 _).trans (hle1 _)).trans (h.scanned u hu e he hB)
    · have heL : e ∈ L := (hL.2 e).mpr (by rw [he]; exact hu)
      have := foldl_relaxIns_scan (s := s) B (some Bi) L st0 e heL hw1
        (by rw [he]; exact (hUi u hu).2.2.2) (by rw [he]; exact hB)
      rw [he] at this
      exact this

end step

/-! ## The loop and the finalization (S2 Step 5) -/

section final

variable {B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {p : ℕ}
  {P0 : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {B'0 : WLab G s}

/-- The main loop preserves the invariant, given correct sub-calls. -/
theorem loop_inv (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W) {cap : ℕ}
    {sub : WLab G s → Finset (Fin G.n) → Labels G s → Result G s → Prop}
    (hsub : ∀ B S d res, CallPre B S d → sub B S d res → CallPost G s B S d cap res) {τ : ℕ} :
    ∀ σ σ' : LState G s p, LoopRel G s sub B τ σ σ' → LInv G s B S d0 d1 P0 B'0 σ →
      LInv G s B S d0 d1 P0 B'0 σ' ∧ (τ < σ'.U.card ∨ σ'.D.IsEmpty) := by
  intro σ σ' hloop
  induction hloop with
  | stop σ hstop => exact fun h => ⟨h, hstop⟩
  | step σ σ' S0 Bi D1 B'i Ui Di dsub L piv' _ hne hpull hsubrel hL hres _ ih =>
    intro h
    have hsp := step_pre hpre hfp h hpull
    have hpost := hsub _ _ _ _ hsp hsubrel
    exact ih (step_post hpre hfp h hne hpull hpost hL hres)

theorem CallPost.of_cap_le {B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s}
    {cap cap' : ℕ} {res : Result G s} (h : CallPost G s B S d0 cap res) (hc : cap' ≤ cap) :
    CallPost G s B S d0 cap' res :=
  { h with partial_card := fun hlt => hc.trans (h.partial_card hlt) }

/-- **S2 Step 5 (finalization, BM.24a–BM.31)**. -/
theorem final_post (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W)
    {piv : Fin p → Fin G.n} (hpiv : ∀ j, piv j ∈ P0 j ∧ ∀ x ∈ P0 j, d1 (piv j) ≤ d1 x)
    {σ : LState G s p} (h : LInv G s B S d0 d1 P0 (initB' B d1 piv) σ) {τ : ℕ}
    (hstop : τ < σ.U.card ∨ σ.D.IsEmpty) {B'f : WLab G s}
    (hB'e : σ.D.IsEmpty → B'f = B) (hB'n : ¬ σ.D.IsEmpty → B'f = σ.B')
    {T6 W' : Finset (Fin G.n)}
    (hT6 : ∀ x, x ∈ T6 ↔ x ∈ S ∧ B'f ≤ σ.d x ∧ σ.d x < B)
    (hW' : ∀ x, x ∈ W' ↔ (x ∈ W ∧ x ∉ σ.U) ∧ σ.d x < B'f)
    {L : List (Fin G.m)} (hL : Enumerates G L W') :
    CallPost G s B S d0 (τ + 1)
      (B'f, σ.U ∪ W',
        ((L.foldl (relaxIns G s B (some B'f)) (σ.d, insertMany G s σ.D T6 σ.d)).2).deleteSet W',
        (L.foldl (relaxIns G s B (some B'f)) (σ.d, insertMany G s σ.D T6 σ.d)).1) := by
  set D6 := insertMany G s σ.D T6 σ.d with hD6
  set st := L.foldl (relaxIns G s B (some B'f)) (σ.d, D6) with hst
  set dF := st.1 with hdF
  set DF := st.2.deleteSet W' with hDF
  have hDF_apply : ∀ y, DF y = if y ∈ W' then none else st.2 y := fun y => rfl
  have hB'fle : B'f ≤ B := by
    by_cases he : σ.D.IsEmpty
    · rw [hB'e he]
    · rw [hB'n he]; exact h.B'_le
  have hB'fge : σ.B' ≤ B'f := by
    by_cases he : σ.D.IsEmpty
    · rw [hB'e he]; exact h.B'_le
    · rw [hB'n he]
  have hUbelow : ∀ u ∈ σ.U, dis (s := s) u < B'f :=
    fun u hu => lt_of_lt_of_le (h.U_below u hu) hB'fge
  have hE : ∀ v ∈ Aset G s B S d1 P0, dis (s := s) v < B'f → v ∈ σ.U := by
    intro v hvA hvlt
    by_cases he : σ.D.IsEmpty
    · by_contra hvU
      obtain ⟨y, ⟨-, hc⟩, -⟩ := h.certified v hvA hvU
      rcases hc with hk | ⟨j, -, k, hk, -⟩
      · rw [he y] at hk; exact absurd hk (by simp)
      · rw [he _] at hk; exact absurd hk (by simp)
    · rw [hB'n he] at hvlt; exact h.A_below v hvA hvlt
  have hWc : ∀ v ∈ Utilde B (S : Set (Fin G.n)), v ∉ Aset G s B S d1 P0 →
      v ∈ W ∧ Complete σ.d v ∧ v ∉ σ.U := by
    intro v hv hvA
    obtain ⟨hvW, hvc⟩ := Wc_complete hfp hv hvA
    exact ⟨hvW, complete_of_le hvc (h.mono v) h.walk.sound, fun hvU => hvA (h.U_A v hvU)⟩
  have hW'c : ∀ x ∈ W', Complete σ.d x := by
    intro x hx
    obtain ⟨⟨hxW, hxU⟩, hxlt⟩ := (hW' x).mp hx
    have hxUK := hfp.region hxW
    by_cases hxA : x ∈ Aset G s B S d1 P0
    · exact absurd (hE x hxA (lt_of_le_of_lt (h.walk.sound x) hxlt)) hxU
    · exact (hWc x hxUK hxA).2.1
  have hUfin : ∀ v, v ∈ σ.U ∪ W' ↔ v ∈ Utilde B'f (S : Set (Fin G.n)) := by
    intro v
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact ⟨hUbelow v hv, (h.U_A v hv).1.2⟩
      · obtain ⟨⟨hvW, -⟩, hvlt⟩ := (hW' v).mp hv
        exact ⟨lt_of_le_of_lt (h.walk.sound v) hvlt, (hfp.region hvW).2⟩
    · intro hv
      have hvB : v ∈ Utilde B (S : Set (Fin G.n)) := ⟨lt_of_lt_of_le hv.1 hB'fle, hv.2⟩
      by_cases hvA : v ∈ Aset G s B S d1 P0
      · exact Finset.mem_union_left _ (hE v hvA hv.1)
      · obtain ⟨hvW, hvc, hvU⟩ := hWc v hvB hvA
        exact Finset.mem_union_right _ ((hW' v).mpr ⟨⟨hvW, hvU⟩, by rw [hvc]; exact hv.1⟩)
  have hleF : ∀ v, dF v ≤ σ.d v := fun v => foldl_relaxIns_fst_le B (some B'f) L (σ.d, D6) v
  have hwF : WalkInv dF := foldl_relaxIns_walk B (some B'f) L (σ.d, D6) h.walk
  have hcompF : ∀ v, Complete σ.d v → Complete dF v :=
    fun v hv => complete_of_le hv (hleF v) hwF.sound
  have hLsrc : ∀ e ∈ L, Complete (σ.d, D6).1 (G.src e) := by
    intro e he
    exact hW'c _ ((hL.2 e).mp he)
  have hsg6 : StoredGe G s σ.d D6 := storedGe_insertMany T6 h.storedGe
  have hsgst : StoredGe G s dF st.2 := foldl_relaxIns_storedGe B (some B'f) L (σ.d, D6) hsg6
  have hsgF : StoredGe G s dF DF := storedGe_deleteSet W' hsgst
  have hexact : ∀ y k, D6 y = some k → k ≤ dis (s := s) y → y ∉ W' →
      DF y = some (dis (s := s) y) := by
    intro y k hk hkle hyW
    obtain ⟨k2, hk2, hk2le⟩ : ∃ k', st.2 y = some k' ∧ k' ≤ k :=
      foldl_relaxIns_snd_le B (some B'f) L (σ.d, D6) y k hk
    have hge : dis (s := s) y ≤ k2 := (hwF.sound y).trans (hsgst y k2 hk2)
    rw [hDF_apply, if_neg hyW, hk2, le_antisymm (hk2le.trans hkle) hge]
  let Pf : Fin G.n → WLab G s → Prop := fun y k =>
    y ∈ Utilde B (S : Set (Fin G.n)) ∧ y ∉ σ.U ∧ B'f ≤ dis (s := s) y ∧ k < B
  have hPf6 : ∀ y k, D6 y = some k → Pf y k := by
    intro y k hk
    rcases insertMany_key_cases hk with h1 | ⟨hy, rfl⟩
    · have hne : ¬ σ.D.IsEmpty := fun he => absurd (he y ▸ h1) (by simp)
      obtain ⟨hA, hU, hB', hkB⟩ := h.keys y k h1
      exact ⟨hA.1, hU, by rw [hB'n hne]; exact hB', hkB⟩
    · obtain ⟨hyS, hyge, hylt⟩ := (hT6 y).mp hy
      have hyUK := S_sub_of_pre hpre y hyS
      have hyU : y ∉ σ.U := by
        intro hyU
        rw [h.U_complete y hyU] at hyge
        exact absurd hyge (not_le.mpr (hUbelow y hyU))
      refine ⟨hyUK, hyU, ?_, hylt⟩
      by_contra hc
      push_neg at hc
      by_cases hyA : y ∈ Aset G s B S d1 P0
      · exact hyU (hE y hyA hc)
      · rw [(hWc y hyUK hyA).2.1] at hyge
        exact absurd hyge (not_le.mpr hc)
  have hPfL : ∀ e ∈ L, ∀ d' : Labels G s, Sound d' → (∀ v, d' v ≤ (σ.d, D6).1 v) →
      Complete d' (G.src e) → ValidRelax G s d' B e →
      (∀ b, some B'f = some b → b ≤ ext (dis (s := s) (G.src e)) e) →
      Pf (G.dst e) (ext (dis (s := s) (G.src e)) e) := by
    intro e he d' hs' hd' hsrc' hv hlo
    have hsW' : G.src e ∈ W' := (hL.2 e).mp he
    have hsUK : G.src e ∈ Utilde B (S : Set (Fin G.n)) := hfp.region ((hW' _).mp hsW').1.1
    have hd'0 : ∀ v, d' v ≤ d0 v := fun v => (hd' v).trans ((h.mono v).trans (hfp.le v))
    have hvUK := mem_UK_of_valid hpre hs' hd'0 hsUK hsrc' hv
    have hcandB : ext (dis (s := s) (G.src e)) e < B := by rw [← hsrc']; exact hv.2
    have hloB : B'f ≤ ext (dis (s := s) (G.src e)) e := hlo B'f rfl
    have hnotc : ∀ w, Complete d' w → dis (s := s) w < B'f → G.dst e ≠ w := by
      intro w hwc hwlt hw
      subst hw
      have hle := hv.1
      rw [hwc, hsrc'] at hle
      exact absurd hloB (not_le.mpr (lt_of_le_of_lt hle hwlt))
    have hvU : G.dst e ∉ σ.U := by
      intro hvU
      exact hnotc _ (complete_of_le (h.U_complete _ hvU) (hd' _) hs') (hUbelow _ hvU) rfl
    refine ⟨hvUK, hvU, ?_, hcandB⟩
    by_contra hc
    push_neg at hc
    by_cases hvA : G.dst e ∈ Aset G s B S d1 P0
    · exact hvU (hE _ hvA hc)
    · exact hnotc _ (complete_of_le (hWc _ hvUK hvA).2.1 (hd' _) hs') hc rfl
  have hPfst : ∀ y k, st.2 y = some k → Pf y k :=
    foldl_relaxIns_keys B (some B'f) Pf L (σ.d, D6) h.walk.sound hLsrc hPf6 hPfL
  have hPfF : ∀ y k, DF y = some k → Pf y k ∧ y ∉ W' := by
    intro y k hk
    rw [hDF_apply] at hk
    split_ifs at hk with hyW
    exact ⟨hPfst y k hk, hyW⟩
  have hsurv : ∀ y k, σ.D y = some k → ∃ k', DF y = some k' ∧ k' ≤ k := by
    intro y k hk
    obtain ⟨k6, hk6, hk6le⟩ : ∃ k', D6 y = some k' ∧ k' ≤ k := insertMany_le T6 _ hk
    obtain ⟨k2, hk2, hk2le⟩ : ∃ k', st.2 y = some k' ∧ k' ≤ k6 :=
      foldl_relaxIns_snd_le B (some B'f) L (σ.d, D6) y k6 hk6
    have hyW : y ∉ W' := by
      intro hyW
      have hne : ¬ σ.D.IsEmpty := fun he => absurd (he y ▸ hk) (by simp)
      obtain ⟨-, -, hB', -⟩ := h.keys y k hk
      have hlt := ((hW' y).mp hyW).2
      rw [hB'n hne] at hlt
      exact absurd (hB'.trans (h.walk.sound y)) (not_le.mpr hlt)
    exact ⟨k2, by rw [hDF_apply, if_neg hyW]; exact hk2, hk2le.trans hk6le⟩
  refine
    { B'_le := hB'fle
      U_eq := hUfin
      U_complete := ?_
      certified := ?_
      keys := ?_
      empty_iff := ?_
      partial_card := ?_
      B'_ge := ?_
      confined := ?_
      S_keys := ?_
      mono := fun v => (hleF v).trans ((h.mono v).trans (hfp.le v))
      walk := hwF
      scanned := ?_ }
  · intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact hcompF u (h.U_complete u hu)
    · exact hcompF u (hW'c u hu)
  · -- certified (R2)
    intro v hv hvnot
    have hvnot' : v ∉ Utilde B'f (S : Set (Fin G.n)) := fun hm => hvnot ((hUfin v).mpr hm)
    by_cases he : σ.D.IsEmpty
    · exact absurd ⟨by rw [hB'e he]; exact hv.1, hv.2⟩ hvnot'
    · by_cases hvA : v ∈ Aset G s B S d1 P0
      · have hvU : v ∉ σ.U := fun hm => hvnot (Finset.mem_union_left _ hm)
        obtain ⟨y, ⟨hyc, hc⟩, hyv⟩ := h.certified v hvA hvU
        rcases hc with hk | ⟨j, hyP, -, -, -⟩
        · obtain ⟨k6, hk6, hk6le⟩ : ∃ k', D6 y = some k' ∧ k' ≤ _ := insertMany_le T6 _ hk
          have hyW : y ∉ W' := by
            intro hyW
            obtain ⟨-, -, hB', -⟩ := h.keys y _ hk
            have hlt := ((hW' y).mp hyW).2
            rw [hB'n he, hyc] at hlt
            exact absurd hB' (not_le.mpr hlt)
          exact ⟨y, hexact y k6 hk6 hk6le hyW, hcompF y hyc, hyv⟩
        · obtain ⟨hyA, hyU, hyB'⟩ := h.Pmem j y hyP
          have hyS : y ∈ S := (hfp.groups j).2 (h.Psub j hyP)
          have hyT : y ∈ T6 := (hT6 y).mpr ⟨hyS, by rw [hB'n he, hyc]; exact hyB',
            by rw [hyc]; exact hyA.1.1⟩
          obtain ⟨k6, hk6, hk6le⟩ : ∃ k', D6 y = some k' ∧ k' ≤ σ.d y :=
            insertMany_mem (D := σ.D) σ.d hyT
          have hyW : y ∉ W' := by
            intro hyW
            have hlt := ((hW' y).mp hyW).2
            rw [hB'n he, hyc] at hlt
            exact absurd hyB' (not_le.mpr hlt)
          exact ⟨y, hexact y k6 hk6 (by rw [hyc] at hk6le; exact hk6le) hyW, hcompF y hyc, hyv⟩
      · rcases hpre.frontier v hv with ⟨h0, -⟩ | ⟨q0, hq0S, hq0c, hq0v⟩
        · exact absurd h0 (Set.notMem_empty v)
        have hq0S' : q0 ∈ S := Finset.mem_coe.mp hq0S
        have hq0UK : q0 ∈ Utilde B (S : Set (Fin G.n)) := S_sub_of_pre hpre q0 hq0S'
        have hq0A : q0 ∉ Aset G s B S d1 P0 := fun hm => hvA (Aset_closure hm hv hq0v)
        obtain ⟨hq0W, hq0c', hq0U⟩ := hWc q0 hq0UK hq0A
        have hq0B : dis (s := s) q0 < B := lt_of_le_of_lt hq0v.dis_le hv.1
        by_cases hq0lt : dis (s := s) q0 < B'f
        · have hq0W' : q0 ∈ W' := (hW' q0).mpr ⟨⟨hq0W, hq0U⟩, by rw [hq0c']; exact hq0lt⟩
          have hvW' : v ∉ W' := fun hm => hvnot (Finset.mem_union_right _ hm)
          obtain ⟨e, hsW', hdW', -, hbv, htight⟩ :=
            hq0v.exists_exit (W' : Set (Fin G.n)) hq0W' hvW'
          have hbB : dis (s := s) (G.dst e) < B := lt_of_le_of_lt hbv.dis_le hv.1
          have hsUK : G.src e ∈ Utilde B (S : Set (Fin G.n)) := hfp.region ((hW' _).mp hsW').1.1
          have hab : OnPath (s := s) (G.src e) (G.dst e) :=
            onPath_of_tight htight.symm (ne_top_of_lt hsUK.1)
          have hbUK : G.dst e ∈ Utilde B (S : Set (Fin G.n)) := UK_closure hsUK hab hbB
          have hbA : G.dst e ∉ Aset G s B S d1 P0 := fun hm => hvA (Aset_closure hm hv hbv)
          obtain ⟨hbW, hbc, hbU⟩ := hWc _ hbUK hbA
          have hbge : B'f ≤ dis (s := s) (G.dst e) := by
            by_contra hc
            exact hdW' ((hW' _).mpr ⟨⟨hbW, hbU⟩, by rw [hbc]; exact not_le.mp hc⟩)
          have he' : e ∈ L := (hL.2 e).mpr hsW'
          obtain ⟨hbcF, hbk⟩ := foldl_relaxIns_canonical (s := s) B (some B'f) L (σ.d, D6) e he'
            h.walk (hW'c _ hsW') htight hbB
          obtain ⟨k, hk, hkle⟩ := hbk (fun b hb => by
            simp only [Option.some.injEq] at hb; subst hb; exact hbge)
          have hge : dis (s := s) (G.dst e) ≤ k := (hwF.sound _).trans (hsgst _ k hk)
          refine ⟨G.dst e, ?_, hbcF, hbv⟩
          show DF (G.dst e) = _
          have hdW'' : G.dst e ∉ W' := hdW'
          rw [hDF_apply, if_neg hdW'', hk, le_antisymm hkle hge]
        · have hq0T : q0 ∈ T6 := (hT6 q0).mpr ⟨hq0S', by rw [hq0c']; exact not_lt.mp hq0lt,
            by rw [hq0c']; exact hq0B⟩
          obtain ⟨k6, hk6, hk6le⟩ : ∃ k', D6 q0 = some k' ∧ k' ≤ σ.d q0 :=
            insertMany_mem (D := σ.D) σ.d hq0T
          have hq0W' : q0 ∉ W' := by
            intro hm
            have hlt := ((hW' q0).mp hm).2
            rw [hq0c'] at hlt
            exact hq0lt hlt
          exact ⟨q0, hexact q0 k6 hk6 (by rw [hq0c'] at hk6le; exact hk6le) hq0W',
            hcompF q0 hq0c', hq0v⟩
  · -- keys (R3)
    intro y k hk
    obtain ⟨⟨hyUK, hyU, hyB'f, hkB⟩, hyW⟩ := hPfF y k hk
    exact ⟨hyUK, fun hm => (Finset.mem_union.mp hm).elim hyU hyW, hyB'f, hsgF y k hk, hkB⟩
  · -- empty_iff (R4)
    constructor
    · intro hB'fB
      intro y
      by_contra hy
      obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hy
      obtain ⟨⟨-, -, hyB'f, hkB⟩, -⟩ := hPfF y k hk
      have : B'f < B'f := by
        calc B'f ≤ dis (s := s) y := hyB'f
          _ ≤ dF y := hwF.sound y
          _ ≤ k := hsgF y k hk
          _ < B := hkB
          _ = B'f := hB'fB.symm
      exact lt_irrefl _ this
    · intro hFe
      by_contra hne'
      have hne : ¬ σ.D.IsEmpty := by
        intro he; exact hne' (hB'e he)
      unfold DS.IsEmpty at hne
      push_neg at hne
      obtain ⟨y, hy⟩ := hne
      obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hy
      obtain ⟨k', hk', -⟩ := hsurv y k hk
      have hFe' : DF y = none := hFe y
      rw [hFe'] at hk'
      exact absurd hk' (by simp)
  · -- partial_card (R4)
    intro hlt
    rcases hstop with hc | he
    · exact hc.trans_le (Finset.card_le_card Finset.subset_union_left)
    · exact absurd (hB'e he) (ne_of_lt hlt)
  · -- B'_ge (R5)
    intro k hkB hk
    by_cases he : σ.D.IsEmpty
    · rw [hB'e he]; exact hkB
    · rw [hB'n he]
      refine le_trans ?_ h.B'_ge
      refine le_min hkB (Finset.le_inf fun j _ => ?_)
      exact (hk _ ((hfp.groups j).2 (hpiv j).1)).trans (hfp.walk.sound _)
  · -- confined (R6)
    intro v hv
    change dF v ≠ d0 v at hv
    by_cases h2 : dF v = σ.d v
    · rw [h2] at hv; exact h.confined v hv
    · obtain ⟨hlt, hkey⟩ := foldl_relaxIns_changed B (some B'f) L (σ.d, D6) v h2
      by_contra hvUK
      have hc := hpre.claimC v (lt_of_le_of_lt (hwF.sound v) hkey) hvUK
      have : dF v < dis (s := s) v := by
        calc dF v < σ.d v := hlt
          _ ≤ d0 v := (h.mono v).trans (hfp.le v)
          _ = dis (s := s) v := hc
      exact absurd (hwF.sound v) (not_le.mpr this)
  · -- S_keys (R7)
    intro x hx hxnot
    have hxUK := S_sub_of_pre hpre x hx
    have hxnot' : x ∉ Utilde B'f (S : Set (Fin G.n)) := fun hm => hxnot ((hUfin x).mpr hm)
    have hxge : B'f ≤ dis (s := s) x := by
      by_contra hc; exact hxnot' ⟨not_le.mp hc, hxUK.2⟩
    have hxle0 : σ.d x ≤ d0 x := (h.mono x).trans (hfp.le x)
    have hxT : x ∈ T6 := (hT6 x).mpr ⟨hx, hxge.trans (h.walk.sound x),
      lt_of_le_of_lt hxle0 (hpre.inRange x hx)⟩
    obtain ⟨k6, hk6, hk6le⟩ : ∃ k', D6 x = some k' ∧ k' ≤ σ.d x :=
      insertMany_mem (D := σ.D) σ.d hxT
    obtain ⟨k2, hk2, hk2le⟩ : ∃ k', st.2 x = some k' ∧ k' ≤ k6 :=
      foldl_relaxIns_snd_le B (some B'f) L (σ.d, D6) x k6 hk6
    have hxW : x ∉ W' := fun hm => hxnot (Finset.mem_union_right _ hm)
    refine ⟨k2, ?_, hk2le.trans (hk6le.trans hxle0)⟩
    show DF x = some k2
    rw [hDF_apply, if_neg hxW]; exact hk2
  · -- scanned (S2 Lemma S2.4)
    intro u hu e he hB
    show dF (G.dst e) ≤ _
    rcases Finset.mem_union.mp hu with hu | hu
    · exact (hleF _).trans (h.scanned u hu e he hB)
    · have heL : e ∈ L := (hL.2 e).mpr (by rw [he]; exact hu)
      have := foldl_relaxIns_scan (s := s) B (some B'f) L (σ.d, D6) e heL h.walk
        (by rw [he]; exact hW'c u hu) (by rw [he]; exact hB)
      rw [he] at this
      exact this

end final

/-! ## The main theorems -/

section main

/-- **Recursive case of Lemma S2.1**. -/
theorem callRel_post {FP : FPRel G s} (hFP : FPSound G s FP)
    {sub : WLab G s → Finset (Fin G.n) → Labels G s → Result G s → Prop} {cap : ℕ}
    (hsub : ∀ B S d res, CallPre B S d → sub B S d res → CallPost G s B S d cap res)
    {B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} {τ : ℕ} {res : Result G s}
    (hpre : CallPre B S d0) (hrel : CallRel G s FP sub B S d0 τ res) :
    CallPost G s B S d0 (τ + 1) res := by
  obtain ⟨d1, p, P, Q, W, piv, σ, L, B'f, T6, W', hfprel, hpiv, hloop, hB'e, hB'n, hT6, hW',
    hL, rfl⟩ := hrel
  have hfp : FPContract B S d0 d1 p P Q W := hFP B S d0 d1 p P Q W hpre hfprel
  have h0 := linv_init hpre hfp hpiv
  obtain ⟨h, hstop⟩ := loop_inv hpre hfp hsub _ _ hloop h0
  exact final_post hpre hfp hpiv h hstop hB'e hB'n hT6 hW' hL

/-- **Lemma S2.1 (all levels)**: every derivation of the relational BMSSP from a call
satisfying `CallPre` yields a result satisfying `CallPost`. -/
theorem bmssp_post {FP : FPRel G s} (hFP : FPSound G s FP) (τ : ℕ → ℕ) :
    ∀ (l : ℕ) (B : WLab G s) (S : Finset (Fin G.n)) (d : Labels G s) (res : Result G s),
      CallPre B S d → BMSSPRel G s FP τ l B S d res → CallPost G s B S d (τ l) res
  | 0, B, S, d, res, hpre, hrel => baseRel_post hpre hrel
  | l + 1, B, S, d, res, hpre, hrel =>
    (callRel_post hFP (bmssp_post hFP τ l) hpre hrel).of_cap_le (Nat.le_succ _)

/-- The initial labels: the empty walk at the source, `⊤` elsewhere. -/
noncomputable def initLabels (s : Fin G.n) : Labels G s := fun v =>
  if v = s then ((toW ([] : List (Fin G.m)) : WalkOrd G s) : WLab G s) else ⊤

theorem initLabels_source : initLabels (G := G) s s = dis (s := s) s := by
  have hr : G.Reachable s s := ⟨[], IsWalk.nil s⟩
  simp only [initLabels, ite_true]
  rw [dis_of_reachable hr, path_source]

theorem callPre_top : CallPre (⊤ : WLab G s) {s} (initLabels s) where
  walk := by
    intro v p hp
    unfold initLabels at hp
    split_ifs at hp with h
    · subst h
      have : p = [] := (WithTop.coe_inj.mp hp).symm
      subst this
      exact IsWalk.nil v
    · exact absurd hp.symm WithTop.coe_ne_top
  claimC := by
    intro v hv hvnot
    exfalso
    apply hvnot
    have hr : G.Reachable s v := by
      by_contra hc; rw [dis_of_not_reachable hc] at hv; exact lt_irrefl _ hv
    have hs : OnPath (s := s) s v := by
      refine ⟨hr, [], path (s := s) v, by simp, IsWalk.nil s, (path_isMinWalk hr).1⟩
    exact ⟨hv, s, Finset.mem_coe.mpr (Finset.mem_singleton_self s), hs⟩
  frontier := by
    have := isFrontier_init (G := G) (s := s) (d := initLabels s) initLabels_source
    simpa using this
  inRange := by
    intro x hx
    rw [Finset.mem_singleton.mp hx]
    simp only [initLabels, ite_true]
    exact WithTop.coe_lt_top _

/-- **Top-level exactness** (B1 Corollary S2.2): if the top call `BMSSP(⊤, {s}, l)` with
`τ l > n` returns `res`, its labels are exactly the canonical labels (`⊤` for unreachable
vertices), for any FindPivots relation meeting the contract. -/
theorem bmssp_top_exact {FP : FPRel G s} (hFP : FPSound G s FP) (τ : ℕ → ℕ) (l : ℕ)
    (hτ : G.n < τ l) {res : Result G s}
    (hrel : BMSSPRel G s FP τ l ⊤ {s} (initLabels s) res) :
    ∀ v, Complete res.2.2.2 v := by
  have hpost := bmssp_post hFP τ l ⊤ {s} (initLabels s) res callPre_top hrel
  have hB' : res.1 = ⊤ := by
    by_contra hne
    have hcard := hpost.partial_card (lt_of_le_of_ne le_top hne)
    have hle : res.2.1.card ≤ G.n := by
      calc res.2.1.card ≤ (Finset.univ : Finset (Fin G.n)).card :=
            Finset.card_le_card (Finset.subset_univ _)
        _ = G.n := Finset.card_fin G.n
    omega
  intro v
  by_cases hr : G.Reachable s v
  · have hvU : v ∈ res.2.1 := by
      rw [hpost.U_eq v, hB']
      have hs : OnPath (s := s) s v :=
        ⟨hr, [], path (s := s) v, by simp, IsWalk.nil s, (path_isMinWalk hr).1⟩
      refine ⟨?_, s, Finset.mem_coe.mpr (Finset.mem_singleton_self s), hs⟩
      rw [dis_of_reachable hr]; exact WithTop.coe_lt_top _
    exact hpost.U_complete v hvU
  · have h1 := hpost.walk.sound v
    show res.2.2.2 v = dis (s := s) v
    rw [dis_of_not_reachable hr] at h1 ⊢
    exact top_le_iff.mp h1

/-- **Top-level output**: the returned labels form an exact SSSP solution (`Graph.IsSSSP`, real
lengths, `⊤` for unreachable vertices). -/
theorem bmssp_top_isSSSP {FP : FPRel G s} (hFP : FPSound G s FP) (τ : ℕ → ℕ) (l : ℕ)
    (hτ : G.n < τ l) {res : Result G s}
    (hrel : BMSSPRel G s FP τ l ⊤ {s} (initLabels s) res) :
    G.IsSSSP s (fun v => labelLen (res.2.2.2 v)) :=
  isSSSP_of_complete (bmssp_top_exact hFP τ l hτ hrel)

end main

/-! ## Window scans (tracker O8)

The implementation relaxes, at BM.19–21, only the out-edges of `U_i` whose candidate lies in the
window `[B_i, B)` (C-HD: monotone pointers into weight-sorted out-lists).  The relation relaxes
every out-edge.  The lemmas below show both give the same state, so a windowed scan is a valid
derivation of `LoopRel.step`. -/

section window

/-- A relaxation whose head already carries a label at most the candidate, and whose candidate is
below the insertion threshold, changes nothing. -/
theorem relaxIns_noop (B : WLab G s) (b : WLab G s) (st : Labels G s × DS G s) (e : Fin G.m)
    (hle : st.1 (G.dst e) ≤ ext (st.1 (G.src e)) e) (hlt : ext (st.1 (G.src e)) e < b) :
    relaxIns G s B (some b) st e = st := by
  unfold relaxIns
  split_ifs with hv
  · have heq : st.1 (G.dst e) = ext (st.1 (G.src e)) e := le_antisymm hle hv.1
    have hd : Function.update st.1 (G.dst e) (ext (st.1 (G.src e)) e) = st.1 := by
      rw [← heq]; exact Function.update_eq_self _ _
    simp only [hd]
    rw [if_neg (not_le.mpr hlt)]
  · rfl

/-- Appending no-op relaxations does not change a fold's result. -/
theorem foldl_relaxIns_append_noop (B b : WLab G s) :
    ∀ (R : List (Fin G.m)) (st : Labels G s × DS G s), WalkInv st.1 →
      (∀ e ∈ R, Complete st.1 (G.src e) ∧ st.1 (G.dst e) ≤ ext (dis (s := s) (G.src e)) e ∧
        ext (dis (s := s) (G.src e)) e < b) →
      R.foldl (relaxIns G s B (some b)) st = st := by
  intro R
  induction R with
  | nil => intro st _ _; rfl
  | cons e R ih =>
    intro st hw hR
    rw [List.foldl_cons]
    obtain ⟨hc, hle, hlt⟩ := hR e (List.mem_cons_self ..)
    have h1 : relaxIns G s B (some b) st e = st := by
      apply relaxIns_noop
      · rw [hc]; exact hle
      · rw [hc]; exact hlt
    rw [h1]
    exact ih st hw (fun e' he' => hR e' (List.mem_cons_of_mem _ he'))

/-- Relaxations of edges with candidate `≥ B` are no-ops. -/
theorem relaxIns_noop_above (B : WLab G s) (lo : Option (WLab G s)) (st : Labels G s × DS G s)
    (e : Fin G.m) (hge : B ≤ ext (st.1 (G.src e)) e) : relaxIns G s B lo st e = st := by
  unfold relaxIns
  rw [if_neg (fun hv => absurd hv.2 (not_lt.mpr hge))]

/-- **Window-scan refinement (O8).** Let the labels `st.1` make every vertex of `Ui` complete and
satisfy the sub-call's scan property (every out-edge of `Ui` with candidate below `B_i` already has
its head at most the candidate).  If `L'` lists, without repetition, exactly the out-edges of `Ui`
whose candidate lies in `[B_i, B)` — in ANY order — then there is an enumeration `L` of all
out-edges of `Ui` whose fold (as used by `LoopRel.step`) equals the fold of `L'`. -/
theorem window_scan {Bi B : WLab G s} (hBiB : Bi ≤ B) {Ui : Finset (Fin G.n)}
    {st : Labels G s × DS G s}
    (hw : WalkInv st.1) (hcomp : ∀ u ∈ Ui, Complete st.1 u)
    (hscan : ∀ u ∈ Ui, ∀ e, G.src e = u → ext (dis (s := s) u) e < Bi →
      st.1 (G.dst e) ≤ ext (dis (s := s) u) e)
    {L' : List (Fin G.m)} (hnd : L'.Nodup)
    (hmem : ∀ e, e ∈ L' ↔ G.src e ∈ Ui ∧ Bi ≤ ext (dis (s := s) (G.src e)) e ∧
      ext (dis (s := s) (G.src e)) e < B) :
    ∃ L, Enumerates G L Ui ∧
      L.foldl (relaxIns G s B (some Bi)) st = L'.foldl (relaxIns G s B (some Bi)) st := by
  classical
  -- the remaining out-edges of `Ui`: those below `B_i` and those at or above `B`
  obtain ⟨Rlow, hRlnd, hRl⟩ : ∃ R : List (Fin G.m), R.Nodup ∧
      ∀ e, e ∈ R ↔ G.src e ∈ Ui ∧ ext (dis (s := s) (G.src e)) e < Bi :=
    ⟨(Finset.univ.filter fun e => G.src e ∈ Ui ∧ ext (dis (s := s) (G.src e)) e < Bi).toList,
      Finset.nodup_toList _, by simp⟩
  obtain ⟨Rhigh, hRhnd, hRh⟩ : ∃ R : List (Fin G.m), R.Nodup ∧
      ∀ e, e ∈ R ↔ G.src e ∈ Ui ∧ B ≤ ext (dis (s := s) (G.src e)) e :=
    ⟨(Finset.univ.filter fun e => G.src e ∈ Ui ∧ B ≤ ext (dis (s := s) (G.src e)) e).toList,
      Finset.nodup_toList _, by simp⟩
  refine ⟨L' ++ Rlow ++ Rhigh, ⟨?_, ?_⟩, ?_⟩
  · refine List.Nodup.append (List.Nodup.append hnd hRlnd ?_) hRhnd ?_
    · rw [List.disjoint_left]
      intro e he he'
      exact absurd ((hRl e).mp he').2 (not_lt.mpr ((hmem e).mp he).2.1)
    · rw [List.disjoint_left]
      intro e he he'
      have hge := ((hRh e).mp he').2
      rcases List.mem_append.mp he with h1 | h1
      · exact absurd ((hmem e).mp h1).2.2 (not_lt.mpr hge)
      · exact absurd (lt_of_lt_of_le ((hRl e).mp h1).2 hBiB) (not_lt.mpr hge)
  · intro e
    simp only [List.mem_append]
    constructor
    · rintro ((h | h) | h)
      · exact ((hmem e).mp h).1
      · exact ((hRl e).mp h).1
      · exact ((hRh e).mp h).1
    · intro hsrc
      by_cases hlow : ext (dis (s := s) (G.src e)) e < Bi
      · exact Or.inl (Or.inr ((hRl e).mpr ⟨hsrc, hlow⟩))
      · by_cases hhigh : B ≤ ext (dis (s := s) (G.src e)) e
        · exact Or.inr ((hRh e).mpr ⟨hsrc, hhigh⟩)
        · exact Or.inl (Or.inl ((hmem e).mpr ⟨hsrc, not_lt.mp hlow, not_le.mp hhigh⟩))
  · rw [List.foldl_append, List.foldl_append]
    set st' := L'.foldl (relaxIns G s B (some Bi)) st with hst'
    have hw' : WalkInv st'.1 := foldl_relaxIns_walk B (some Bi) L' st hw
    have hle' : ∀ v, st'.1 v ≤ st.1 v := fun v => foldl_relaxIns_fst_le B (some Bi) L' st v
    have hcomp' : ∀ u ∈ Ui, Complete st'.1 u :=
      fun u hu => complete_of_le (hcomp u hu) (hle' u) hw'.sound
    have hlow : Rlow.foldl (relaxIns G s B (some Bi)) st' = st' := by
      apply foldl_relaxIns_append_noop B Bi Rlow st' hw'
      intro e he
      obtain ⟨hsrc, hlt⟩ := (hRl e).mp he
      exact ⟨hcomp' _ hsrc, (hle' _).trans (hscan _ hsrc e rfl hlt), hlt⟩
    rw [hlow]
    have hhigh : ∀ (R : List (Fin G.m)) (st'' : Labels G s × DS G s),
        (∀ e ∈ R, Complete st''.1 (G.src e) ∧ B ≤ ext (dis (s := s) (G.src e)) e) →
        R.foldl (relaxIns G s B (some Bi)) st'' = st'' := by
      intro R
      induction R with
      | nil => intro _ _; rfl
      | cons e R ih =>
        intro st'' hR
        rw [List.foldl_cons]
        obtain ⟨hc, hge⟩ := hR e (List.mem_cons_self ..)
        rw [relaxIns_noop_above B (some Bi) st'' e (by rw [hc]; exact hge)]
        exact ih st'' (fun e' he' => hR e' (List.mem_cons_of_mem _ he'))
    apply hhigh
    intro e he
    obtain ⟨hsrc, hge⟩ := (hRh e).mp he
    exact ⟨hcomp' _ hsrc, hge⟩

/-- **O8 for `LoopRel.step`**: after a sub-call `(B_i, S_i)` with postcondition `CallPost`, the
relaxation fold of BM.19–21 over all out-edges of `U_i` may be replaced by a scan of the window
edges only (candidate in `[B_i, B)`, any order, no repetition). -/
theorem window_scan_step {Bi B : WLab G s} (hBiB : Bi ≤ B) {Si : Finset (Fin G.n)}
    {dσ : Labels G s} {cap : ℕ} {B'i : WLab G s} {Ui : Finset (Fin G.n)} {Di : DS G s}
    {d1' : Labels G s} (hpost : CallPost G s Bi Si dσ cap (B'i, Ui, Di, d1')) (D0 : DS G s)
    {L' : List (Fin G.m)} (hnd : L'.Nodup)
    (hmem : ∀ e, e ∈ L' ↔ G.src e ∈ Ui ∧ Bi ≤ ext (dis (s := s) (G.src e)) e ∧
      ext (dis (s := s) (G.src e)) e < B) :
    ∃ L, Enumerates G L Ui ∧
      L.foldl (relaxIns G s B (some Bi)) (d1', D0) =
        L'.foldl (relaxIns G s B (some Bi)) (d1', D0) :=
  window_scan hBiB (st := (d1', D0)) hpost.walk hpost.U_complete
    (fun u hu e he hlt => hpost.scanned u hu e he hlt) hnd hmem

end window

end BM
end CHD
end Frontier
