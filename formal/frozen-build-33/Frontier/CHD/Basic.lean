import Frontier.CHD.WalkOrder

/-!
# Frontier.CHD.Basic — shared Layer-A interface for the C-HD formalization (v2, walk order)

Owner: agent-08 (work package L1, COORD G2-2).  NON-GATE: definitions and elementary lemmas only.

## Conventions (binding for all C-HD Layer-A files; see the L1 architecture post)

* Graphs: `Frontier.Graph` (explicit multigraph, `ℝ≥0` weights), source `s`.
* **Labels are walks** (B1 S1 §A): a label is `⊤` or an edge list read as a walk from `s`, in the
  full walk order `κ` of `Frontier.CHD.WalkOrder` (`WLab G s := WithTop (WalkOrd G s)`).  Distinct
  vertices never share a finite label (the end vertex is part of `κ`), so labels double as keys and
  bounds `B` are labels.  The relaxation is `ext λ e = λ ++ [e]`.  The version-stamped 5-tuples of
  B1 are the Layer-B implementation of these O(1) comparisons.
* **Canonical paths** `path v` are unique (`IsMinWalk`); `dis v` is the canonical label;
  "the shortest path of `v` visits `y`" is `OnPath y v`.
* **The D store** `DS G s := Fin G.n → Option (WLab G s)` with `insert`/`merge`/`deleteSet` and the
  `PullSpec` of DMSY26 Lemma 3.4.
* **Cost-indexed relations**: each algorithm step is a constructor of an inductive relation
  carrying a `Nat` cost equal to the RAM cost of the step under the OPERATION TABLE (1 per value
  addition/comparison — i.e. per label extension / label comparison —, 1 per word op / array
  read / array write, 1 per element of an explicitly stored list that is iterated, bitmap
  membership/insert/delete 1, allocation of `k` cells `k`; no choice/argmin/sort without paying).
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-! ## Labels -/

variable (G s) in
/-- Walk labels. -/
abbrev WLab := WithTop (WalkOrd G s)

variable (G s) in
/-- Tentative labels of all vertices. -/
abbrev Labels := Fin G.n → WLab G s

/-- The relaxation `λ ⊕ e`: extend the walk by `e` (`⊤ ⊕ e = ⊤`). -/
def ext (lab : WLab G s) (e : Fin G.m) : WLab G s :=
  lab.map fun p => (toW ((p : List (Fin G.m)) ++ [e]) : WalkOrd G s)

@[simp] theorem ext_top (e : Fin G.m) : ext (⊤ : WLab G s) e = ⊤ := rfl

theorem ext_coe (p : List (Fin G.m)) (e : Fin G.m) :
    ext (((toW p : WalkOrd G s) : WLab G s)) e = ((toW (p ++ [e]) : WalkOrd G s) : WLab G s) := rfl

/-- Labels are walks to the right vertex (the standing invariant of B1 S1, R1). -/
def WalkInv (d : Labels G s) : Prop :=
  ∀ v (p : List (Fin G.m)), d v = ((toW p : WalkOrd G s) : WLab G s) → G.IsWalk s v p

/-- Sound labels: never below the canonical label. -/
def Sound (d : Labels G s) : Prop := ∀ v, dis (s := s) v ≤ d v

/-- `v` is complete: its label is the canonical label. -/
def Complete (d : Labels G s) (v : Fin G.n) : Prop := d v = dis (s := s) v

theorem WalkInv.sound {d : Labels G s} (h : WalkInv d) : Sound d := by
  intro v
  by_cases hv : d v = ⊤
  · rw [hv]; exact le_top
  · obtain ⟨p, hp⟩ := WithTop.ne_top_iff_exists.mp hv
    rw [← hp]
    exact dis_le_walk (h v p hp.symm)

/-- (T2) A relaxation never lowers a label below its tail's label. -/
theorem lt_ext_of_ne_top {lab : WLab G s} (h : lab ≠ ⊤) (e : Fin G.m) : lab < ext lab e := by
  obtain ⟨p, rfl⟩ := WithTop.ne_top_iff_exists.mp h
  exact WithTop.coe_lt_coe.mpr (lt_append (s := s) (P := (p : List (Fin G.m))) (by simp))

/-- (T1) Relaxation is monotone for labels that are walks to the same vertex. -/
theorem ext_le_ext {u : Fin G.n} {p q : List (Fin G.m)} (hp : G.IsWalk s u p)
    (hq : G.IsWalk s u q) (h : (toW p : WalkOrd G s) ≤ toW q) (e : Fin G.m) (he : G.src e = u) :
    ext (((toW p : WalkOrd G s) : WLab G s)) e ≤ ext (((toW q : WalkOrd G s) : WLab G s)) e := by
  rw [ext_coe, ext_coe]
  subst he
  exact WithTop.coe_le_coe.mpr (append_le_append hp hq (IsWalk.single e) h)

/-- Relaxing a walk label gives a walk label for the head. -/
theorem walk_ext {u : Fin G.n} {p : List (Fin G.m)} (hp : G.IsWalk s u p) (e : Fin G.m)
    (he : G.src e = u) : G.IsWalk s (G.dst e) (p ++ [e]) := by
  subst he
  exact hp.append (IsWalk.single e)

/-- Consecutive vertices on a canonical path: the canonical label of the successor is the
extension of the predecessor's. -/
theorem dis_succ_on_path {v : Fin G.n} (hv : G.Reachable s v) {P R : List (Fin G.m)} {e : Fin G.m}
    (hPR : path (s := s) v = P ++ e :: R) (hP : G.IsWalk s (G.src e) P)
    (hR : G.IsWalk (G.dst e) v R) :
    dis (s := s) (G.dst e) = ext (dis (s := s) (G.src e)) e ∧ OnPath (s := s) (G.dst e) v ∧
      OnPath (s := s) (G.src e) v := by
  have hmin : IsMinWalk (s := s) v ((P ++ [e]) ++ R) := by
    rw [List.append_assoc]; simpa [hPR] using path_isMinWalk (s := s) hv
  have hPe : G.IsWalk s (G.dst e) (P ++ [e]) := hP.append (IsWalk.single e)
  have h1 : path (s := s) (G.dst e) = P ++ [e] := path_eq_of_isMinWalk (hmin.prefix hPe hR)
  have hmin2 : IsMinWalk (s := s) (G.dst e) (P ++ [e]) := h1 ▸ path_isMinWalk ⟨_, hPe⟩
  have h2 : path (s := s) (G.src e) = P :=
    path_eq_of_isMinWalk (hmin2.prefix hP (IsWalk.single e))
  refine ⟨?_, ⟨hv, P ++ [e], R, by rw [hPR]; simp, hPe, hR⟩,
    ⟨hv, P, e :: R, hPR, hP, IsWalk.cons hR⟩⟩
  rw [dis_of_reachable ⟨_, hPe⟩, dis_of_reachable ⟨_, hP⟩, h1, h2, ext_coe]

/-! ## Frontier notions over canonical paths -/

/-- `Ũ(B, S)`: vertices whose canonical label is below `B` and whose canonical path visits `S`. -/
def Utilde (B : WLab G s) (S : Set (Fin G.n)) : Set (Fin G.n) :=
  {v | dis (s := s) v < B ∧ ∃ y ∈ S, OnPath (s := s) y v}

/-- `⟨X, Y⟩` is a frontier for `U`: every `v ∈ U` is in `X` and complete, or its canonical path
visits a complete vertex of `Y`. -/
def IsFrontier (d : Labels G s) (U X Y : Set (Fin G.n)) : Prop :=
  ∀ v ∈ U, (v ∈ X ∧ Complete d v) ∨ ∃ y ∈ Y, Complete d y ∧ OnPath (s := s) y v

/-- `R(B, Z)`: out-neighbours of `Z` outside `Z` validly (tightly) relaxed from `Z` below `B`. -/
def Relaxed (d : Labels G s) (B : WLab G s) (Z : Set (Fin G.n)) : Set (Fin G.n) :=
  {v | v ∉ Z ∧ ∃ e, G.src e ∈ Z ∧ G.dst e = v ∧ d v = ext (d (G.src e)) e ∧ d v < B}

theorem Complete.of_le {d d' : Labels G s} {v : Fin G.n} (h : Complete d v) (hsound : Sound d')
    (hle : d' v ≤ d v) : Complete d' v :=
  le_antisymm (hle.trans h.le) (hsound v)

/-- Observation 2.1(1): frontiers survive further sound, monotone relaxation. -/
theorem IsFrontier.of_le {d d' : Labels G s} {U X Y : Set (Fin G.n)} (hF : IsFrontier d U X Y)
    (hsound : Sound d') (hle : ∀ v, d' v ≤ d v) : IsFrontier d' U X Y := by
  intro v hv
  rcases hF v hv with ⟨hX, hc⟩ | ⟨y, hy, hc, hvis⟩
  · exact Or.inl ⟨hX, hc.of_le hsound (hle v)⟩
  · exact Or.inr ⟨y, hy, hc.of_le hsound (hle y), hvis⟩

theorem IsFrontier.mono {d : Labels G s} {U U' X X' Y Y' : Set (Fin G.n)}
    (hF : IsFrontier d U X Y) (hU : U' ⊆ U) (hX : X ⊆ X') (hY : Y ⊆ Y') :
    IsFrontier d U' X' Y' := by
  intro v hv
  rcases hF v (hU hv) with ⟨hx, hc⟩ | ⟨y, hy, hc, hvis⟩
  · exact Or.inl ⟨hX hx, hc⟩
  · exact Or.inr ⟨y, hY hy, hc, hvis⟩

/-- Observation 2.1(3). -/
theorem utilde_subset {B : WLab G s} {S Y : Set (Fin G.n)} (hY : Y ⊆ Utilde B S) :
    Utilde B Y ⊆ Utilde B S := by
  rintro v ⟨hvB, y, hy, hvis⟩
  obtain ⟨-, x, hx, hxy⟩ := hY hy
  exact ⟨hvB, x, hx, hxy.trans hvis⟩

theorem utilde_mono_bound {B B' : WLab G s} {S : Set (Fin G.n)} (h : B' ≤ B) :
    Utilde B' S ⊆ Utilde B S :=
  fun _ hv => ⟨lt_of_lt_of_le hv.1 h, hv.2⟩

theorem utilde_mono_set {B : WLab G s} {S S' : Set (Fin G.n)} (h : S ⊆ S') :
    Utilde B S ⊆ Utilde B S' := by
  rintro v ⟨hvB, y, hy, hvis⟩
  exact ⟨hvB, y, h hy, hvis⟩

/-- Observation 2.1(4). -/
theorem IsFrontier.restrict {d : Labels G s} {B : WLab G s} {S X Y : Set (Fin G.n)}
    (hF : IsFrontier d (Utilde B S) X Y) (hY : Y ⊆ Utilde B S) :
    IsFrontier d (Utilde B Y) ∅ Y := by
  rintro v ⟨-, y, hy, hvis⟩
  by_cases hc : Complete d y
  · exact Or.inr ⟨y, hy, hc, hvis⟩
  · rcases hF y (hY hy) with ⟨-, hc'⟩ | ⟨y', hy', hc', hvis'⟩
    · exact absurd hc' hc
    · exact Or.inr ⟨y', hy', hc', hvis'.trans hvis⟩

/-- Dijkstra's selection rule: a minimum label of `Y` is complete. -/
theorem IsFrontier.complete_of_min {d : Labels G s} {B : WLab G s} {S X Y : Set (Fin G.n)}
    (hF : IsFrontier d (Utilde B S) X Y) (hY : Y ⊆ Utilde B S) (hsound : Sound d)
    {y : Fin G.n} (hy : y ∈ Y) (hmin : ∀ y' ∈ Y, d y ≤ d y') : Complete d y := by
  rcases hF y (hY hy) with ⟨-, hc⟩ | ⟨y', hy', hc', hvis⟩
  · exact hc
  · refine le_antisymm ?_ (hsound y)
    calc d y ≤ d y' := hmin y' hy'
      _ = dis (s := s) y' := hc'
      _ ≤ dis (s := s) y := hvis.dis_le

/-- Observation 2.1(5): everything of `Ũ` below every label of `Y` is already in `X` and complete. -/
theorem IsFrontier.below {d : Labels G s} {B : WLab G s} {S X Y : Set (Fin G.n)}
    (hF : IsFrontier d (Utilde B S) X Y) {v : Fin G.n} (hv : v ∈ Utilde B S)
    (hbelow : ∀ y ∈ Y, dis (s := s) v < d y) : v ∈ X ∧ Complete d v := by
  rcases hF v hv with h | ⟨y, hy, hc, hyv⟩
  · exact h
  · have h1 := hbelow y hy
    rw [hc] at h1
    exact absurd hyv.dis_le (not_le.mpr h1)

/-- The exit edge of a canonical path leaving a set. -/
theorem OnPath.exists_exit {y v : Fin G.n} (h : OnPath (s := s) y v) (Z : Set (Fin G.n))
    (hy : y ∈ Z) (hv : v ∉ Z) :
    ∃ e, G.src e ∈ Z ∧ G.dst e ∉ Z ∧ OnPath (s := s) (G.src e) v ∧ OnPath (s := s) (G.dst e) v ∧
      dis (s := s) (G.dst e) = ext (dis (s := s) (G.src e)) e := by
  obtain ⟨R, hR, hw⟩ := h.path_prefix
  obtain ⟨q₁, e, q₂, rfl, h₁, hsZ, hdZ, h₂⟩ := hw.exists_exit Z hy hv
  have hPy : G.IsWalk s y (path (s := s) y) := (path_isMinWalk h.reachable_left).1
  have hP : G.IsWalk s (G.src e) (path (s := s) y ++ q₁) := hPy.append h₁
  have hPR : path (s := s) v = (path (s := s) y ++ q₁) ++ e :: q₂ := by
    rw [hR, List.append_assoc]
  obtain ⟨hdis, hon₂, hon₁⟩ := dis_succ_on_path h.1 hPR hP h₂
  exact ⟨e, hsZ, hdZ, hon₁, hon₂, hdis⟩

/-- **Framework step** (DMSY26 §2.5): after making `Z` complete and relaxing every edge out of
`Z` whose candidate is below `B`, `⟨X ∪ Z, (Y \ Z) ∪ R(B, Z)⟩` is again a frontier. -/
theorem IsFrontier.step {d d' : Labels G s} {B : WLab G s} {U X Y Z : Set (Fin G.n)}
    (hF : IsFrontier d U X Y) (hU : ∀ v ∈ U, dis (s := s) v < B)
    (hsound : Sound d') (hle : ∀ v, d' v ≤ d v) (hZ : ∀ z ∈ Z, Complete d' z)
    (hrelax : ∀ e, G.src e ∈ Z → ext (d' (G.src e)) e < B → d' (G.dst e) ≤ ext (d' (G.src e)) e) :
    IsFrontier d' U (X ∪ Z) ((Y \ Z) ∪ Relaxed d' B Z) := by
  intro v hvU
  rcases hF v hvU with ⟨hX, hc⟩ | ⟨y, hy, hc, hvis⟩
  · exact Or.inl ⟨Or.inl hX, hc.of_le hsound (hle v)⟩
  · by_cases hyZ : y ∈ Z
    · by_cases hvZ : v ∈ Z
      · exact Or.inl ⟨Or.inr hvZ, hZ v hvZ⟩
      · obtain ⟨e, hsZ, hdZ, -, hon₂, hdis⟩ := hvis.exists_exit Z hyZ hvZ
        have hcs : d' (G.src e) = dis (s := s) (G.src e) := hZ _ hsZ
        have htight : ext (d' (G.src e)) e = dis (s := s) (G.dst e) := by rw [hcs, hdis]
        have hdB : dis (s := s) (G.dst e) < B := lt_of_le_of_lt hon₂.dis_le (hU v hvU)
        have hrel := hrelax e hsZ (by rw [htight]; exact hdB)
        have hcd : Complete d' (G.dst e) := le_antisymm (hrel.trans htight.le) (hsound _)
        refine Or.inr ⟨G.dst e, Or.inr ⟨hdZ, e, hsZ, rfl, ?_, ?_⟩, hcd, hon₂⟩
        · rw [hcd, htight]
        · rw [hcd]; exact hdB
    · exact Or.inr ⟨y, Or.inl ⟨hy, hyZ⟩, hc.of_le hsound (hle y), hvis⟩

/-- **Frontier split** (DMSY26 Lemma 3.6). -/
theorem IsFrontier.split {d : Labels G s} {B Bs : WLab G s} {S X Y Ys : Set (Fin G.n)}
    (hF : IsFrontier d (Utilde B S) X Y)
    (hYs₁ : ∀ y ∈ Y, d y < Bs → y ∈ Ys) (hYs₂ : Ys ⊆ Utilde B S) :
    IsFrontier d (Utilde Bs Ys) ∅ Ys := by
  rintro v ⟨hvB, y, hy, hvis⟩
  by_cases hc : Complete d y
  · exact Or.inr ⟨y, hy, hc, hvis⟩
  · rcases hF y (hYs₂ hy) with ⟨-, hc'⟩ | ⟨y', hy', hc', hvis'⟩
    · exact absurd hc' hc
    · refine Or.inr ⟨y', hYs₁ y' hy' ?_, hc', hvis'.trans hvis⟩
      rw [hc']
      exact lt_of_le_of_lt (hvis'.trans hvis).dis_le hvB

/-- Termination of the framework: an empty frontier side means `U ⊆ X` is complete. -/
theorem IsFrontier.complete_of_empty {d : Labels G s} {U X : Set (Fin G.n)}
    (hF : IsFrontier d U X ∅) : ∀ v ∈ U, v ∈ X ∧ Complete d v := by
  intro v hv
  rcases hF v hv with h | ⟨y, hy, -⟩
  · exact h
  · exact absurd hy (Set.notMem_empty y)

/-- The initial frontier `⟨∅, {s}⟩` for `Ũ(⊤, {s})`, which is every reachable vertex. -/
theorem isFrontier_init {d : Labels G s} (hs : d s = dis (s := s) s) :
    IsFrontier d (Utilde (s := s) ⊤ {s}) ∅ {s} := by
  rintro v ⟨-, y, hy, hvis⟩
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact Or.inr ⟨y, rfl, hs, hvis⟩

theorem utilde_top_source : Utilde (s := s) ⊤ {s} = {v | G.Reachable s v} := by
  ext v
  simp only [Utilde, Set.mem_singleton_iff, exists_eq_left, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨-, h⟩; exact h.1
  · intro h
    refine ⟨?_, h, [], path (s := s) v, by simp, IsWalk.nil s, (path_isMinWalk h).1⟩
    rw [dis_of_reachable h]; exact WithTop.coe_lt_top _

/-! ## Reading back exact real distances -/

/-- The real length of a label (`⊤` for `⊤`). -/
def labelLen (lab : WLab G s) : ℝ≥0∞ :=
  match lab with
  | ⊤ => ⊤
  | (p : WalkOrd G s) => ((G.len (p : List (Fin G.m)) : ℝ≥0) : ℝ≥0∞)

/-- Complete labels give exact real distances (including `⊤` for unreachable vertices). -/
theorem labelLen_dis (v : Fin G.n) : labelLen (dis (s := s) v) = G.dist s v := by
  by_cases h : G.Reachable s v
  · rw [dis_of_reachable h]
    exact len_path h
  · rw [dis_of_not_reachable h, dist_eq_top_iff.mpr h]
    rfl

/-- **Output bridge**: if every vertex is complete, reading the labels' lengths solves SSSP. -/
theorem isSSSP_of_complete {d : Labels G s} (h : ∀ v, Complete d v) :
    G.IsSSSP s (fun v => labelLen (d v)) := fun v => by
  show labelLen (d v) = G.dist s v
  rw [h v, labelLen_dis]

/-! ## Safety of permanent edge deletion below a call's lower bound (C-HD fix A / FH.9) -/

/-- If the tail's canonical label is at least `x` and the head's label is below `x`, no later sound
labelling pointwise below the current one lets `e` improve the head: the edge may be deleted. -/
theorem not_improves_of_below {d d' : Labels G s} {e : Fin G.m} {x : WLab G s}
    (hx : x ≤ dis (s := s) (G.src e)) (hv : d (G.dst e) < x)
    (hsound : Sound d') (hle : ∀ v, d' v ≤ d v) :
    ¬ ext (d' (G.src e)) e < d' (G.dst e) := by
  intro himp
  have h1 : x ≤ d' (G.src e) := hx.trans (hsound _)
  have hne : d' (G.src e) ≠ ⊤ := by
    intro htop; rw [htop, ext_top] at himp; exact absurd himp (not_lt.mpr le_top)
  have h2 : d' (G.src e) ≤ ext (d' (G.src e)) e := (lt_ext_of_ne_top hne e).le
  exact absurd (lt_of_lt_of_le hv (h1.trans h2)) (not_lt.mpr (himp.le.trans (hle _)))

/-! ## The D store (DMSY26 Lemma 3.4, by its stored values) -/

variable (G s) in
/-- The partial-sorting structure `D`, by its stored labels (`none` = not a key). -/
abbrev DS := Fin G.n → Option (WLab G s)

namespace DS

/-- The empty structure. -/
def empty : DS G s := fun _ => none

/-- `D` has no key. -/
def IsEmpty (D : DS G s) : Prop := ∀ y, D y = none

/-- Merging stored values: keep the smaller one. -/
noncomputable def mergeVal : Option (WLab G s) → Option (WLab G s) → Option (WLab G s)
  | none, b => b
  | a, none => a
  | some a, some b => some (min a b)

/-- `Insert(y, λ)`: add `y` with value `λ`, or lower its stored value to `min`. -/
noncomputable def insert (D : DS G s) (y : Fin G.n) (lam : WLab G s) : DS G s :=
  Function.update D y (mergeVal (D y) (some lam))

/-- `Delete(y)` for every `y ∈ T`. -/
noncomputable def deleteSet (D : DS G s) (T : Finset (Fin G.n)) : DS G s :=
  fun y => if y ∈ T then none else D y

/-- `Merge(D')`. -/
noncomputable def merge (D D' : DS G s) : DS G s := fun y => mergeVal (D y) (D' y)

end DS

/-- Pull specification (DMSY26 Lemma 3.4): the pulled set `S'` is exactly the set of keys whose
stored value is below the returned separator `x ≤ Bd`; pulled keys are removed; a nonempty
structure pulls at least one key.  Size and cost clauses are package L3's cost contract. -/
structure PullSpec (D : DS G s) (Bd : WLab G s) (S' : Finset (Fin G.n)) (x : WLab G s)
    (D' : DS G s) : Prop where
  pulled : ∀ y, y ∈ S' ↔ ∃ v, D y = some v ∧ v < x
  rest : ∀ y, D' y = if y ∈ S' then none else D y
  bound : x ≤ Bd
  nonempty : (∃ y, D y ≠ none) → S'.Nonempty

/-! ## Call precondition and the FindPivots correctness contract -/

/-- Preconditions of a BMSSP call `(B, S)` on labels `d`: labels are walks (hence sound),
everything below `B` outside `Ũ(B, S)` is complete (B1 "Claim C"), `⟨∅, S⟩` is a frontier for
`Ũ(B, S)`, and `S` lies below `B`. -/
structure CallPre (B : WLab G s) (S : Finset (Fin G.n)) (d : Labels G s) : Prop where
  walk : WalkInv d
  claimC : ∀ v, dis (s := s) v < B → v ∉ Utilde B (S : Set (Fin G.n)) → Complete d v
  frontier : IsFrontier d (Utilde B (S : Set (Fin G.n))) ∅ (S : Set (Fin G.n))
  inRange : ∀ x ∈ S, d x < B

/-- **FindPivots correctness contract** (B1 FP1/FP2/FP3/FP5-style; C-HD: leaves are never in
`W`).  Only these properties are used by the BMSSP correctness proof; sizes, trees, `Q`-charging
and all costs belong to the cost contract (packages L2/L5). -/
structure FPContract (B : WLab G s) (S : Finset (Fin G.n)) (d d' : Labels G s) (p : ℕ)
    (P : Fin p → Finset (Fin G.n)) (Q W : Finset (Fin G.n)) : Prop where
  /-- labels only decrease, stay walks -/
  le : ∀ v, d' v ≤ d v
  walk : WalkInv d'
  /-- every changed label lies in `Ũ(B, S)` -/
  changed : ∀ v, d' v ≠ d v → v ∈ Utilde B (S : Set (Fin G.n))
  /-- FP1: `⟨W, ⋃ P_j⟩` is a frontier for `Ũ(B, S)` -/
  frontier : IsFrontier d' (Utilde B (S : Set (Fin G.n))) (W : Set (Fin G.n))
    {x | ∃ j, x ∈ P j}
  /-- FP2: groups are nonempty, pairwise disjoint subsets of `S`; `Q ⊆ S` is disjoint from the
  groups; groups and `Q` cover `S` (so `P_1, …, P_p, Q` partition `S`) -/
  groups : ∀ j, (P j).Nonempty ∧ P j ⊆ S
  gdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j)
  qsub : Q ⊆ S
  qdisj : ∀ j, Disjoint Q (P j)
  cover : ∀ x ∈ S, x ∈ Q ∨ ∃ j, x ∈ P j
  /-- FP3: the completed region lies in `Ũ(B, S)` -/
  region : (W : Set (Fin G.n)) ⊆ Utilde B (S : Set (Fin G.n))

end CHD
end Frontier
