import Frontier.CHD.Basic
import Frontier.CHD.Partition
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Frontier.CHD.FindPivots — FindPivots-HD: one local search (C-HD package L2, Layer A)

Owner: agent-05.  NON-GATE (Layer A; see the L1 architecture post).

Formalizes ONE local search of FindPivots-HD (agent-09 C_HD_PROOF_v1/v2, lines FH.4–FH.21) over
the shared interface `Frontier.CHD.Basic` (walk labels in the full walk order, canonical paths):
local Dijkstra from a root `x` with upper bound `B`, the call's `L_X = d_B[S]` (FH.9: a scanned
in-range edge `(u,v)` with `d v < L_X` is DELETED from `Out(u)`, cost `O(1)`; PAPER_CHD Lemma L),
member cap `k`, LEAVES (invalid in-range targets: counted in `K`, never explored, not in `val`),
contact with the trees `T` built earlier in the invocation (FH.11–FH.12), and leaf promotion
(FH.19).  Deleted edges (the persistent set `D`) are not scanned and cost nothing; the static
invariant `Dinv D` (every deleted edge goes to a strictly smaller canonical label) replaces any
temporal flag lemma.

Main results:
* `Scan.inv`, `Search.inv`: walk-labels, heap/val/extracted-set invariants, extraction order,
  "no valid relaxation reaches an extracted vertex" (D-b), and the scanned-edge closure;
* `Search.failed_complete` (paper lemma H1): if a search whose root `x` is COMPLETE with
  `L_X ≤ d x` FAILS and the deleted set satisfies `Dinv`, every `v` whose canonical path visits
  `x` and with `dis v < B` ends in `val` with its canonical label.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

variable (G s) in
/-- Fixed data of one FindPivots-HD invocation. -/
structure FPCtx where
  /-- upper bound `B` of the call -/
  B : WLab G s
  /-- the call's `L_X = d_B[S]` (FH.9 deletion threshold; any lower bound of `S`'s labels works) -/
  Lx : WLab G s
  /-- member cap `k` -/
  k : ℕ
  /-- the sorted out-lists (P4); only membership and order matter -/
  out : Fin G.n → List (Fin G.m)
  /-- cost of one heap insertion / decrease-key (unsorted array over the ≤ `k` members: `O(1)`) -/
  hins : ℕ
  /-- cost of one heap extract-min (unsorted array: `O(k)` comparisons; see the cost note:
  a binary heap would make a search cost `Θ(k² lg k)`) -/
  hext : ℕ

variable (G s) in
/-- State of one local search. -/
structure SSt where
  /-- global labels -/
  d : Labels G s
  /-- deleted edges (persistent): not present in the out-lists -/
  D : Finset (Fin G.m)
  /-- heap contents (bitmap view; the heap itself is package L3's binary heap) -/
  H : Finset (Fin G.n)
  /-- search members in order of arrival (explored members and leaves) -/
  K : List (Fin G.n)
  /-- the valid part (root and validly relaxed members) -/
  val : Finset (Fin G.n)
  /-- extracted vertices -/
  done : Finset (Fin G.n)
  /-- first-discovery parents of the members (FH.14; never re-set) -/
  kpar : Fin G.n → Fin G.n
  /-- the contact edge `(u, v)` of a contact search (FH.12), if any -/
  hit : Option (Fin G.n × Fin G.n)

/-- DMSY26 `Relax` validity (re-confirmation included; the bound test is FH.8). -/
def Ok (d : Labels G s) (u : Fin G.n) (e : Fin G.m) : Prop := ext (d u) e ≤ d (G.dst e)

open Classical in
/-- The labels after `Relax(u, e)` (FH.10). -/
noncomputable def relaxL (d : Labels G s) (u : Fin G.n) (e : Fin G.m) : Labels G s :=
  if Ok d u e then Function.update d (G.dst e) (ext (d u) e) else d

open Classical in
/-- FH.13–FH.16: a NEW member `dst e` (valid: explored member; invalid: leaf). -/
noncomputable def addNew (σ : SSt G s) (u : Fin G.n) (e : Fin G.m) : SSt G s :=
  if Ok σ.d u e then
    { σ with d := relaxL σ.d u e, K := σ.K ++ [G.dst e],
             val := insert (G.dst e) σ.val, H := insert (G.dst e) σ.H,
             kpar := Function.update σ.kpar (G.dst e) u }
  else { σ with K := σ.K ++ [G.dst e], kpar := Function.update σ.kpar (G.dst e) u }

open Classical in
/-- FH.18–FH.19: an improvement of an existing member (leaf promotion included). -/
noncomputable def improve (σ : SSt G s) (u : Fin G.n) (e : Fin G.m) : SSt G s :=
  if Ok σ.d u e then
    { σ with d := relaxL σ.d u e, val := insert (G.dst e) σ.val, H := insert (G.dst e) σ.H }
  else σ

open Classical in
/-- Heap cost of a step: one heap insertion/decrease-key iff the relaxation is valid. -/
noncomputable def okCost (c : FPCtx G s) (d : Labels G s) (u : Fin G.n) (e : Fin G.m) : ℕ :=
  if Ok d u e then c.hins else 0

/-- Outcome of scanning the rest of an out-list. -/
inductive ScanRes where
  /-- exhausted or cut by the range stop: continue with the next extraction -/
  | cont
  /-- contact with an existing tree (FH.12) -/
  | contact
  /-- the member cap was reached (FH.17) -/
  | full
  deriving DecidableEq

/-- Word/value operations charged per scanned edge (read edge, form `ext`, compare with `B` and
`L_X`, bitmap tests, list append/unlink, label write): a constant of the operation table. -/
def scanC : ℕ := 12

/-- Scanning the remaining out-edges `L` of the extracted vertex `u` (FH.7–FH.19), with cost. -/
inductive Scan (c : FPCtx G s) (T : Finset (Fin G.n)) (u : Fin G.n) :
    SSt G s → List (Fin G.m) → SSt G s → ScanRes → ℕ → Prop
  | nil (σ : SSt G s) : Scan c T u σ [] σ .cont 0
  | del (σ σ' : SSt G s) (e : Fin G.m) (L : List (Fin G.m)) (r : ScanRes) (n : ℕ) :
      e ∈ σ.D → Scan c T u σ L σ' r n → Scan c T u σ (e :: L) σ' r n
  | brk (σ : SSt G s) (e : Fin G.m) (L : List (Fin G.m)) :
      e ∉ σ.D → ¬ ext (σ.d u) e < c.B →
      Scan c T u σ (e :: L) σ .cont scanC
  | lxdel (σ σ' : SSt G s) (e : Fin G.m) (L : List (Fin G.m)) (r : ScanRes) (n : ℕ) :
      e ∉ σ.D → ext (σ.d u) e < c.B → σ.d (G.dst e) < c.Lx →
      Scan c T u { σ with D := insert e σ.D } L σ' r n →
      Scan c T u σ (e :: L) σ' r (n + scanC)
  | contact (σ : SSt G s) (e : Fin G.m) (L : List (Fin G.m)) :
      e ∉ σ.D → ext (σ.d u) e < c.B → ¬ σ.d (G.dst e) < c.Lx → G.dst e ∈ T →
      Scan c T u σ (e :: L) { σ with d := relaxL σ.d u e, hit := some (u, G.dst e) } .contact scanC
  | newFull (σ : SSt G s) (e : Fin G.m) (L : List (Fin G.m)) :
      e ∉ σ.D → ext (σ.d u) e < c.B → ¬ σ.d (G.dst e) < c.Lx → G.dst e ∉ T →
      G.dst e ∉ σ.K → c.k ≤ (addNew σ u e).K.length →
      Scan c T u σ (e :: L) (addNew σ u e) .full (scanC + okCost c σ.d u e)
  | newCont (σ σ' : SSt G s) (e : Fin G.m) (L : List (Fin G.m)) (r : ScanRes) (n : ℕ) :
      e ∉ σ.D → ext (σ.d u) e < c.B → ¬ σ.d (G.dst e) < c.Lx → G.dst e ∉ T →
      G.dst e ∉ σ.K → (addNew σ u e).K.length < c.k →
      Scan c T u (addNew σ u e) L σ' r n →
      Scan c T u σ (e :: L) σ' r (n + scanC + okCost c σ.d u e)
  | inK (σ σ' : SSt G s) (e : Fin G.m) (L : List (Fin G.m)) (r : ScanRes) (n : ℕ) :
      e ∉ σ.D → ext (σ.d u) e < c.B → ¬ σ.d (G.dst e) < c.Lx → G.dst e ∉ T →
      G.dst e ∈ σ.K → Scan c T u (improve σ u e) L σ' r n →
      Scan c T u σ (e :: L) σ' r (n + scanC + okCost c σ.d u e)

/-- Outcome of one search. -/
inductive SearchRes where
  | failed
  | success
  | contact
  deriving DecidableEq

/-- The search loop (FH.5–FH.19): extract a minimum-label vertex of the heap (charged `c.hext`)
and scan its out-list. -/
inductive Search (c : FPCtx G s) (T : Finset (Fin G.n)) :
    SSt G s → SSt G s → SearchRes → ℕ → Prop
  | empty (σ : SSt G s) : σ.H = ∅ → σ.K.length < c.k → Search c T σ σ .failed 1
  | capped (σ : SSt G s) : c.k ≤ σ.K.length → Search c T σ σ .success 1
  | stepCont (σ σ' σ'' : SSt G s) (u : Fin G.n) (res : SearchRes) (n n' : ℕ) :
      σ.K.length < c.k → u ∈ σ.H → (∀ y ∈ σ.H, σ.d u ≤ σ.d y) →
      Scan c T u { σ with H := σ.H.erase u, done := insert u σ.done } (c.out u) σ' .cont n →
      Search c T σ' σ'' res n' →
      Search c T σ σ'' res (n + n' + c.hext + 1)
  | stepContact (σ σ' : SSt G s) (u : Fin G.n) (n : ℕ) :
      σ.K.length < c.k → u ∈ σ.H → (∀ y ∈ σ.H, σ.d u ≤ σ.d y) →
      Scan c T u { σ with H := σ.H.erase u, done := insert u σ.done } (c.out u) σ' .contact n →
      Search c T σ σ' .contact (n + c.hext + 1)
  | stepFull (σ σ' : SSt G s) (u : Fin G.n) (n : ℕ) :
      σ.K.length < c.k → u ∈ σ.H → (∀ y ∈ σ.H, σ.d u ≤ σ.d y) →
      Scan c T u { σ with H := σ.H.erase u, done := insert u σ.done } (c.out u) σ' .full n →
      Search c T σ σ' .success (n + c.hext + 1)

/-- The initial state of a search from root `x` (FH.4). -/
def initSt (d : Labels G s) (D : Finset (Fin G.m)) (x : Fin G.n) : SSt G s :=
  { d := d, D := D, H := {x}, K := [x], val := {x}, done := ∅, kpar := id, hit := none }

/-! ## Invariants of one search -/

section Invariants

variable (c : FPCtx G s)

/-- Out-lists list exactly the out-edges of each vertex. -/
def OutOK : Prop := ∀ u e, e ∈ c.out u ↔ G.src e = u

/-- Invariants of a search state (`c` is kept as a parameter for the cost/contract layers). -/
structure SInv (c : FPCtx G s) (σ : SSt G s) : Prop where
  walk : WalkInv σ.d
  heapVal : σ.H ⊆ σ.val
  valK : ∀ v ∈ σ.val, v ∈ σ.K
  valDone : σ.val ⊆ σ.done ∪ σ.H
  doneH : Disjoint σ.done σ.H
  finVal : ∀ v ∈ σ.val, σ.d v ≠ ⊤
  order : ∀ v ∈ σ.done, ∀ y ∈ σ.H, σ.d v ≤ σ.d y

/-- Additional invariants while the extracted vertex `u` is being scanned. -/
structure CurInv (σ : SSt G s) (u : Fin G.n) : Prop where
  mem : u ∈ σ.done
  fin : σ.d u ≠ ⊤
  doneLe : ∀ v ∈ σ.done, σ.d v ≤ σ.d u
  leHeap : ∀ y ∈ σ.H, σ.d u ≤ σ.d y

variable {c}

theorem ext_ne_top_of_lt {lab : WLab G s} {e : Fin G.m} {B : WLab G s} (h : ext lab e < B) :
    ext lab e ≠ ⊤ := fun ht => by rw [ht] at h; exact absurd h (not_lt_of_ge le_top)

theorem le_ext (lab : WLab G s) (e : Fin G.m) : lab ≤ ext lab e := by
  by_cases h : lab = ⊤
  · rw [h, ext_top]
  · exact (lt_ext_of_ne_top h e).le

/-- (D-b) No valid relaxation reaches an extracted vertex. -/
theorem not_ok_of_done {σ : SSt G s} {u : Fin G.n} (hC : CurInv σ u) {e : Fin G.m}
    (hv : G.dst e ∈ σ.done) : ¬ Ok σ.d u e := by
  intro hok
  exact absurd (lt_of_le_of_lt (hC.doneLe _ hv) (lt_ext_of_ne_top hC.fin e)) (not_lt_of_ge hok)

theorem relaxL_apply_self {d : Labels G s} {u : Fin G.n} {e : Fin G.m} (hok : Ok d u e) :
    relaxL d u e (G.dst e) = ext (d u) e := by
  simp [relaxL, hok]

theorem relaxL_apply_ne {d : Labels G s} {u : Fin G.n} {e : Fin G.m} {v : Fin G.n}
    (hv : v ≠ G.dst e) : relaxL d u e v = d v := by
  unfold relaxL
  split_ifs
  · exact Function.update_of_ne hv _ _
  · rfl

theorem relaxL_le (d : Labels G s) (u : Fin G.n) (e : Fin G.m) (v : Fin G.n) :
    relaxL d u e v ≤ d v := by
  unfold relaxL
  split_ifs with hok
  · by_cases hv : v = G.dst e
    · subst hv; rw [Function.update_self]; exact hok
    · rw [Function.update_of_ne hv]
  · exact le_rfl

theorem relaxL_of_not_ok {d : Labels G s} {u : Fin G.n} {e : Fin G.m} (h : ¬ Ok d u e) :
    relaxL d u e = d := by
  simp [relaxL, h]

/-- Relaxation along an out-edge of `u` keeps labels walks. -/
theorem WalkInv.relaxL {d : Labels G s} (h : WalkInv d) {u : Fin G.n} {e : Fin G.m}
    (he : G.src e = u) : WalkInv (relaxL d u e) := by
  intro v p hp
  by_cases hok : Ok d u e
  · by_cases hv : v = G.dst e
    · subst hv
      rw [relaxL_apply_self hok] at hp
      by_cases hu : d u = ⊤
      · rw [hu, ext_top] at hp; exact absurd hp.symm (WithTop.coe_ne_top)
      · obtain ⟨q0, hq0⟩ := WithTop.ne_top_iff_exists.mp hu
        obtain ⟨q, hq⟩ : ∃ q : List (Fin G.m), d u = ((toW q : WalkOrd G s) : WLab G s) :=
          ⟨q0, hq0.symm⟩
        have hwq : G.IsWalk s u q := h u q hq
        rw [hq, ext_coe] at hp
        have hpq : p = q ++ [e] := (WithTop.coe_injective hp).symm
        rw [hpq]
        exact walk_ext hwq e he
    · rw [relaxL_apply_ne hv] at hp; exact h v p hp
  · rw [relaxL_of_not_ok hok] at hp; exact h v p hp

/-- One scan step changes the state monotonically; every changed label enters `val`; labels of
extracted vertices never change. -/
structure Grows (σ σ1 : SSt G s) : Prop where
  dle : ∀ v, σ1.d v ≤ σ.d v
  D : σ.D ⊆ σ1.D
  val : σ.val ⊆ σ1.val
  done : σ1.done = σ.done
  K : σ.K <+: σ1.K
  chg : ∀ v, σ1.d v ≠ σ.d v → v ∈ σ1.val
  doneFix : ∀ v ∈ σ.done, σ1.d v = σ.d v

theorem Grows.refl (σ : SSt G s) : Grows σ σ :=
  ⟨fun _ => le_rfl, subset_rfl, subset_rfl, rfl, List.prefix_refl _, fun _ h => absurd rfl h,
    fun _ _ => rfl⟩

theorem Grows.trans {σ σ1 σ2 : SSt G s} (h1 : Grows σ σ1) (h2 : Grows σ1 σ2) :
    Grows σ σ2 where
  dle v := (h2.dle v).trans (h1.dle v)
  D := h1.D.trans h2.D
  val := h1.val.trans h2.val
  done := h2.done.trans h1.done
  K := h1.K.trans h2.K
  chg v hv := by
    by_cases h : σ2.d v = σ1.d v
    · exact h2.val (h1.chg v (by rwa [← h]))
    · exact h2.chg v h
  doneFix v hv := by rw [h2.doneFix v (h1.done ▸ hv), h1.doneFix v hv]

/-- A valid relaxation into a new target (FH.13–FH.15, FH.19). -/
theorem inv_ok_insert (hout : OutOK c) {σ : SSt G s} {u : Fin G.n} {e : Fin G.m}
    (hI : SInv c σ) (hC : CurInv σ u) (he : e ∈ c.out u) (hB : ext (σ.d u) e < c.B)
    (hok : Ok σ.d u e) (K' : List (Fin G.n)) (hK : σ.K <+: K')
    (hK' : G.dst e ∈ K') (kp : Fin G.n → Fin G.n) :
    SInv c { σ with d := relaxL σ.d u e, K := K', val := insert (G.dst e) σ.val,
                    H := insert (G.dst e) σ.H, kpar := kp } ∧
    CurInv { σ with d := relaxL σ.d u e, K := K', val := insert (G.dst e) σ.val,
                    H := insert (G.dst e) σ.H, kpar := kp } u ∧
    Grows σ { σ with d := relaxL σ.d u e, K := K', val := insert (G.dst e) σ.val,
                     H := insert (G.dst e) σ.H, kpar := kp } := by
  set v := G.dst e with hvdef
  have hvd : v ∉ σ.done := fun h => not_ok_of_done hC h hok
  have hcand_top : ext (σ.d u) e ≠ ⊤ := ext_ne_top_of_lt hB
  have hdv : relaxL σ.d u e v = ext (σ.d u) e := relaxL_apply_self hok
  have hdw : ∀ w, w ≠ v → relaxL σ.d u e w = σ.d w := fun w hw => relaxL_apply_ne hw
  have huv : u ≠ v := fun h => hvd (h ▸ hC.mem)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨hC.mem, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, rfl, hK, ?_, ?_⟩⟩
  all_goals (try dsimp only)
  · exact hI.walk.relaxL ((hout u e).mp he)
  · exact Finset.insert_subset_insert _ hI.heapVal
  · intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hK'
    · exact hK.subset (hI.valK w hw)
  · intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
    · rcases Finset.mem_union.mp (hI.valDone hw) with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem h)
  · rw [Finset.disjoint_insert_right]
    exact ⟨hvd, hI.doneH⟩
  · intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · rw [hdv]; exact hcand_top
    · by_cases hwv : w = v
      · subst hwv; rw [hdv]; exact hcand_top
      · rw [hdw w hwv]; exact hI.finVal w hw
  · intro w hw y hy
    have hwv : w ≠ v := fun h => hvd (h ▸ hw)
    rw [hdw w hwv]
    rcases Finset.mem_insert.mp hy with rfl | hy
    · rw [hdv]; exact (hC.doneLe w hw).trans (le_ext _ e)
    · by_cases hyv : y = v
      · subst hyv; rw [hdv]; exact (hC.doneLe w hw).trans (le_ext _ e)
      · rw [hdw y hyv]; exact hI.order w hw y hy
  · rw [hdw u huv]; exact hC.fin
  · intro w hw
    have hwv : w ≠ v := fun h => hvd (h ▸ hw)
    rw [hdw w hwv, hdw u huv]; exact hC.doneLe w hw
  · intro y hy
    rw [hdw u huv]
    rcases Finset.mem_insert.mp hy with rfl | hy
    · rw [hdv]; exact le_ext _ e
    · by_cases hyv : y = v
      · subst hyv; rw [hdv]; exact le_ext _ e
      · rw [hdw y hyv]; exact hC.leHeap y hy
  · exact fun w => relaxL_le σ.d u e w
  · exact subset_rfl
  · exact Finset.subset_insert _ _
  · intro w hw
    by_contra hwn
    have hwv : w ≠ v := fun h => hwn (h ▸ Finset.mem_insert_self _ _)
    exact hw (hdw w hwv)
  · intro w hw
    exact hdw w (fun h => hvd (h ▸ hw))

theorem inv_addNew (hout : OutOK c) {σ : SSt G s} {u : Fin G.n} {e : Fin G.m}
    (hI : SInv c σ) (hC : CurInv σ u) (he : e ∈ c.out u) (hB : ext (σ.d u) e < c.B) :
    SInv c (addNew σ u e) ∧ CurInv (addNew σ u e) u ∧ Grows σ (addNew σ u e) := by
  by_cases hok : Ok σ.d u e
  · have h := inv_ok_insert hout hI hC he hB hok (σ.K ++ [G.dst e])
      (List.prefix_append _ _) (List.mem_append_right _ (List.mem_singleton_self _))
      (Function.update σ.kpar (G.dst e) u)
    simpa [addNew, hok] using h
  · have hs : addNew σ u e =
        { σ with K := σ.K ++ [G.dst e], kpar := Function.update σ.kpar (G.dst e) u } := by
      simp [addNew, hok]
    rw [hs]
    refine ⟨⟨hI.walk, hI.heapVal, fun w hw => List.mem_append_left _ (hI.valK w hw),
      hI.valDone, hI.doneH, hI.finVal, hI.order⟩, ⟨hC.mem, hC.fin, hC.doneLe, hC.leHeap⟩,
      ⟨fun _ => le_rfl, subset_rfl, subset_rfl, rfl, List.prefix_append _ _,
        fun _ h => absurd rfl h, fun _ _ => rfl⟩⟩

theorem inv_improve (hout : OutOK c) {σ : SSt G s} {u : Fin G.n} {e : Fin G.m}
    (hI : SInv c σ) (hC : CurInv σ u) (he : e ∈ c.out u) (hB : ext (σ.d u) e < c.B)
    (hKv : G.dst e ∈ σ.K) :
    SInv c (improve σ u e) ∧ CurInv (improve σ u e) u ∧ Grows σ (improve σ u e) := by
  by_cases hok : Ok σ.d u e
  · have h := inv_ok_insert hout hI hC he hB hok σ.K (List.prefix_refl _) hKv σ.kpar
    simpa [improve, hok] using h
  · have hs : improve σ u e = σ := by simp [improve, hok]
    rw [hs]
    exact ⟨hI, hC, Grows.refl σ⟩

theorem inv_lxdel {σ : SSt G s} {u : Fin G.n} (e : Fin G.m) (hI : SInv c σ) (hC : CurInv σ u) :
    SInv c { σ with D := insert e σ.D } ∧ CurInv { σ with D := insert e σ.D } u ∧
      Grows σ { σ with D := insert e σ.D } :=
  ⟨⟨hI.walk, hI.heapVal, hI.valK, hI.valDone, hI.doneH, hI.finVal, hI.order⟩,
    ⟨hC.mem, hC.fin, hC.doneLe, hC.leHeap⟩,
    ⟨fun _ => le_rfl, Finset.subset_insert _ _, subset_rfl, rfl, List.prefix_refl _,
      fun _ h => absurd rfl h, fun _ _ => rfl⟩⟩

theorem inv_contact (hout : OutOK c) {σ : SSt G s} {u : Fin G.n} {e : Fin G.m}
    (hI : SInv c σ) (hC : CurInv σ u) (he : e ∈ c.out u) (hB : ext (σ.d u) e < c.B) :
    SInv c { σ with d := relaxL σ.d u e, hit := some (u, G.dst e) } ∧
      CurInv { σ with d := relaxL σ.d u e, hit := some (u, G.dst e) } u := by
  by_cases hok : Ok σ.d u e
  · set v := G.dst e with hvdef
    have hvd : v ∉ σ.done := fun h => not_ok_of_done hC h hok
    have hcand_top : ext (σ.d u) e ≠ ⊤ := ext_ne_top_of_lt hB
    have hdv : relaxL σ.d u e v = ext (σ.d u) e := relaxL_apply_self hok
    have hdw : ∀ w, w ≠ v → relaxL σ.d u e w = σ.d w := fun w hw => relaxL_apply_ne hw
    have huv : u ≠ v := fun h => hvd (h ▸ hC.mem)
    refine ⟨⟨?_, hI.heapVal, hI.valK, hI.valDone, hI.doneH, ?_, ?_⟩, ⟨hC.mem, ?_, ?_, ?_⟩⟩
    all_goals (try dsimp only)
    · exact hI.walk.relaxL ((hout u e).mp he)
    · intro w hw
      by_cases hwv : w = v
      · subst hwv; rw [hdv]; exact hcand_top
      · rw [hdw w hwv]; exact hI.finVal w hw
    · intro w hw y hy
      have hwv : w ≠ v := fun h => hvd (h ▸ hw)
      rw [hdw w hwv]
      by_cases hyv : y = v
      · subst hyv; rw [hdv]; exact (hC.doneLe w hw).trans (le_ext _ e)
      · rw [hdw y hyv]; exact hI.order w hw y hy
    · rw [hdw u huv]; exact hC.fin
    · intro w hw
      have hwv : w ≠ v := fun h => hvd (h ▸ hw)
      rw [hdw w hwv, hdw u huv]; exact hC.doneLe w hw
    · intro y hy
      rw [hdw u huv]
      by_cases hyv : y = v
      · subst hyv; rw [hdv]; exact le_ext _ e
      · rw [hdw y hyv]; exact hC.leHeap y hy
  · rw [relaxL_of_not_ok hok]
    exact ⟨⟨hI.walk, hI.heapVal, hI.valK, hI.valDone, hI.doneH, hI.finVal, hI.order⟩,
      ⟨hC.mem, hC.fin, hC.doneLe, hC.leHeap⟩⟩


variable (c) in
/-- Closure of one scanned edge `e` of the extracted vertex `u`: if the candidate is in range,
the edge is deleted, or the target's label is at most the candidate, and equal only if valid. -/
def Closed (σ : SSt G s) (u : Fin G.n) (e : Fin G.m) : Prop :=
  ext (σ.d u) e < c.B →
    e ∈ σ.D ∨ (σ.d (G.dst e) ≤ ext (σ.d u) e ∧
      (σ.d (G.dst e) = ext (σ.d u) e → G.dst e ∈ σ.val))

theorem Closed.grows {σ σ1 : SSt G s} {w : Fin G.n} {e : Fin G.m} (h : Closed c σ w e)
    (hg : Grows σ σ1) (hw : σ1.d w = σ.d w) : Closed c σ1 w e := by
  intro hB
  rw [hw] at hB ⊢
  rcases h hB with hF | ⟨hle, heq⟩
  · exact Or.inl (hg.D hF)
  · refine Or.inr ⟨(hg.dle _).trans hle, fun h1 => ?_⟩
    by_cases h2 : σ1.d (G.dst e) = σ.d (G.dst e)
    · exact hg.val (heq (h2 ▸ h1))
    · exact hg.chg _ h2

variable (G s) in
/-- The sortedness relation on out-lists: along the list, candidates never decrease
(preprocessing P4 sorts by `(w e, id (dst e), id e)`, which gives this for every tail label). -/
def SortedRel (e e' : Fin G.m) : Prop := ∀ lab : WLab G s, ext lab e ≤ ext lab e'

variable (c) in
/-- Out-lists are sorted by candidate (DMSY/C-HD preprocessing P4). -/
def OutSorted : Prop := ∀ u, (c.out u).Pairwise (SortedRel G s)

theorem closed_of_addNew {σ : SSt G s} {u : Fin G.n} {e : Fin G.m} (hC : CurInv σ u) :
    Closed c (addNew σ u e) u e := by
  intro _
  by_cases hok : Ok σ.d u e
  · have hvd : G.dst e ∉ σ.done := fun h => not_ok_of_done hC h hok
    have huv : u ≠ G.dst e := fun h => hvd (h ▸ hC.mem)
    have hu : relaxL σ.d u e u = σ.d u := relaxL_apply_ne huv
    simp only [addNew, hok, ite_true, hu]
    exact Or.inr ⟨by rw [relaxL_apply_self hok], fun _ => Finset.mem_insert_self _ _⟩
  · simp only [addNew, hok, ite_false]
    have hlt : σ.d (G.dst e) < ext (σ.d u) e := lt_of_not_ge hok
    exact Or.inr ⟨le_of_lt hlt, fun h => absurd h (ne_of_lt hlt)⟩

theorem closed_of_improve {σ : SSt G s} {u : Fin G.n} {e : Fin G.m} (hC : CurInv σ u) :
    Closed c (improve σ u e) u e := by
  intro _
  by_cases hok : Ok σ.d u e
  · have hvd : G.dst e ∉ σ.done := fun h => not_ok_of_done hC h hok
    have huv : u ≠ G.dst e := fun h => hvd (h ▸ hC.mem)
    have hu : relaxL σ.d u e u = σ.d u := relaxL_apply_ne huv
    simp only [improve, hok, ite_true, hu]
    exact Or.inr ⟨by rw [relaxL_apply_self hok], fun _ => Finset.mem_insert_self _ _⟩
  · simp only [improve, hok, ite_false]
    have hlt : σ.d (G.dst e) < ext (σ.d u) e := lt_of_not_ge hok
    exact Or.inr ⟨le_of_lt hlt, fun h => absurd h (ne_of_lt hlt)⟩

/-- Scan invariant: invariants are preserved; non-contact scans grow the state; a completed
(`cont`) scan leaves every edge of the scanned list closed; labels only decrease. -/
theorem Scan.inv (hout : OutOK c) (hsort : OutSorted c) {T : Finset (Fin G.n)} {u : Fin G.n}
    {σ σ' : SSt G s} {L : List (Fin G.m)} {r : ScanRes} {n : ℕ} (h : Scan c T u σ L σ' r n)
    (hL : L <:+ c.out u) (hI : SInv c σ) (hC : CurInv σ u) :
    SInv c σ' ∧ CurInv σ' u ∧ (r ≠ .contact → Grows σ σ') ∧
      (r = .cont → ∀ e ∈ L, Closed c σ' u e) ∧
      ((∀ v, σ'.d v ≤ σ.d v) ∧ σ.val ⊆ σ'.val ∧ σ.D ⊆ σ'.D) := by
  induction h with
  | nil σ => exact ⟨hI, hC, fun _ => Grows.refl σ, fun _ e he => absurd he List.not_mem_nil,
      fun _ => le_rfl, subset_rfl, subset_rfl⟩
  | del σ σ' e L r n hdel h' ih =>
    have hL' : L <:+ c.out u := (List.suffix_cons e L).trans hL
    obtain ⟨hI', hC', hg, hcl, hm⟩ := ih hL' hI hC
    refine ⟨hI', hC', hg, fun hr e' he' => ?_, hm⟩
    rcases List.mem_cons.mp he' with rfl | he'
    · exact fun _ => Or.inl ((hg (by rw [hr]; decide)).D hdel)
    · exact hcl hr e' he'
  | brk σ e L hF hB =>
    refine ⟨hI, hC, fun _ => Grows.refl σ, fun _ e' he' hB' => ?_,
      fun _ => le_rfl, subset_rfl, subset_rfl⟩
    exfalso
    rcases List.mem_cons.mp he' with rfl | he'
    · exact hB hB'
    · have hpw : (e :: L).Pairwise (SortedRel G s) := (hsort u).sublist hL.sublist
      have hrel := List.rel_of_pairwise_cons hpw he'
      exact hB (lt_of_le_of_lt (hrel (σ.d u)) hB')
  | lxdel σ σ' e L r n hF hB hlow h' ih =>
    have hL' : L <:+ c.out u := (List.suffix_cons e L).trans hL
    obtain ⟨hI1, hC1, hg1⟩ := inv_lxdel e hI hC
    obtain ⟨hI', hC', hg, hcl, hm1, hm2, hm3⟩ := ih hL' hI1 hC1
    refine ⟨hI', hC', fun hr => hg1.trans (hg hr), fun hr e' he' => ?_,
      fun v => (hm1 v).trans (hg1.dle v), hg1.val.trans hm2, hg1.D.trans hm3⟩
    rcases List.mem_cons.mp he' with rfl | he'
    · exact fun _ => Or.inl ((hg (by rw [hr]; decide)).D (Finset.mem_insert_self _ _))
    · exact hcl hr e' he'
  | contact σ e L hF hB _ _ =>
    have he : e ∈ c.out u := hL.subset List.mem_cons_self
    obtain ⟨hI', hC'⟩ := inv_contact hout hI hC he hB
    exact ⟨hI', hC', fun h => absurd rfl h, fun h => absurd h (by decide),
      fun v => relaxL_le σ.d u e v, subset_rfl, subset_rfl⟩
  | newFull σ e L hF hB _ _ _ _ =>
    have he : e ∈ c.out u := hL.subset List.mem_cons_self
    obtain ⟨hI', hC', hg⟩ := inv_addNew hout hI hC he hB
    exact ⟨hI', hC', fun _ => hg, fun h => absurd h (by decide), hg.dle, hg.val, hg.D⟩
  | newCont σ σ' e L r n hF hB _ _ _ _ h' ih =>
    have he : e ∈ c.out u := hL.subset List.mem_cons_self
    have hL' : L <:+ c.out u := (List.suffix_cons e L).trans hL
    obtain ⟨hI1, hC1, hg1⟩ := inv_addNew hout hI hC he hB
    obtain ⟨hI', hC', hg, hcl, hm1, hm2, hm3⟩ := ih hL' hI1 hC1
    refine ⟨hI', hC', fun hr => hg1.trans (hg hr), fun hr e' he' => ?_,
      fun v => (hm1 v).trans (hg1.dle v), hg1.val.trans hm2, hg1.D.trans hm3⟩
    rcases List.mem_cons.mp he' with rfl | he'
    · have hg' := hg (by rw [hr]; decide)
      exact (closed_of_addNew hC).grows hg' (hg'.doneFix u hC1.mem)
    · exact hcl hr e' he'
  | inK σ σ' e L r n hF hB _ _ hK h' ih =>
    have he : e ∈ c.out u := hL.subset List.mem_cons_self
    have hL' : L <:+ c.out u := (List.suffix_cons e L).trans hL
    obtain ⟨hI1, hC1, hg1⟩ := inv_improve hout hI hC he hB hK
    obtain ⟨hI', hC', hg, hcl, hm1, hm2, hm3⟩ := ih hL' hI1 hC1
    refine ⟨hI', hC', fun hr => hg1.trans (hg hr), fun hr e' he' => ?_,
      fun v => (hm1 v).trans (hg1.dle v), hg1.val.trans hm2, hg1.D.trans hm3⟩
    rcases List.mem_cons.mp he' with rfl | he'
    · have hg' := hg (by rw [hr]; decide)
      exact (closed_of_improve hC).grows hg' (hg'.doneFix u hC1.mem)
    · exact hcl hr e' he'

/-- The extraction step (FH.6). -/
theorem inv_extract {σ : SSt G s} {u : Fin G.n} (hI : SInv c σ) (hu : u ∈ σ.H)
    (hmin : ∀ y ∈ σ.H, σ.d u ≤ σ.d y) :
    SInv c { σ with H := σ.H.erase u, done := insert u σ.done } ∧
      CurInv { σ with H := σ.H.erase u, done := insert u σ.done } u := by
  refine ⟨⟨hI.walk, ?_, hI.valK, ?_, ?_, hI.finVal, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  all_goals (try dsimp only)
  · exact (Finset.erase_subset _ _).trans hI.heapVal
  · intro w hw
    rcases Finset.mem_union.mp (hI.valDone hw) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem h)
    · by_cases hwu : w = u
      · subst hwu; exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
      · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hwu, h⟩)
  · rw [Finset.disjoint_insert_left]
    exact ⟨Finset.notMem_erase _ _, hI.doneH.mono_right (Finset.erase_subset _ _)⟩
  · intro w hw y hy
    have hy' : y ∈ σ.H := Finset.mem_of_mem_erase hy
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hmin y hy'
    · exact hI.order w hw y hy'
  · exact Finset.mem_insert_self _ _
  · exact hI.finVal u (hI.heapVal hu)
  · intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact le_rfl
    · exact hI.order w hw u hu
  · intro y hy
    exact hmin y (Finset.mem_of_mem_erase hy)

/-- Search invariant: invariants are preserved, labels only decrease, `val` only grows, and a
FAILED search ends with an empty heap and every scanned edge of every extracted vertex closed. -/
theorem Search.inv (hout : OutOK c) (hsort : OutSorted c) {T : Finset (Fin G.n)}
    {σ σ' : SSt G s} {res : SearchRes} {n : ℕ} (h : Search c T σ σ' res n) (hI : SInv c σ)
    (hCl : ∀ w ∈ σ.done, ∀ e ∈ c.out w, Closed c σ w e) :
    SInv c σ' ∧ (∀ v, σ'.d v ≤ σ.d v) ∧ σ.val ⊆ σ'.val ∧ σ.D ⊆ σ'.D ∧
      (res = .failed → σ'.H = ∅ ∧ σ'.K.length < c.k ∧
        ∀ w ∈ σ'.done, ∀ e ∈ c.out w, Closed c σ' w e) := by
  induction h with
  | empty σ hH hK => exact ⟨hI, fun _ => le_rfl, subset_rfl, subset_rfl, fun _ => ⟨hH, hK, hCl⟩⟩
  | capped σ _ =>
    exact ⟨hI, fun _ => le_rfl, subset_rfl, subset_rfl, fun h => absurd h (by decide)⟩
  | stepCont σ σ' σ'' u res n n' _ hu hmin hscan _ ih =>
    obtain ⟨hI0, hC0⟩ := inv_extract hI hu hmin
    obtain ⟨hI1, -, hg, hcl, hm1, hm2, hm3⟩ :=
      Scan.inv hout hsort hscan (List.suffix_refl _) hI0 hC0
    have hg' := hg (by decide)
    have hCl1 : ∀ w ∈ σ'.done, ∀ e ∈ c.out w, Closed c σ' w e := by
      intro w hw e he
      rw [hg'.done] at hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hcl rfl e he
      · have h0 : Closed c { σ with H := σ.H.erase u, done := insert u σ.done } w e :=
          hCl w hw e he
        exact h0.grows hg' (hg'.doneFix w (Finset.mem_insert_of_mem hw))
    obtain ⟨hI2, hm1', hm2', hm3', hf⟩ := ih hI1 hCl1
    exact ⟨hI2, fun v => (hm1' v).trans (hm1 v), hm2.trans hm2', hm3.trans hm3', hf⟩
  | stepContact σ σ' u n _ hu hmin hscan =>
    obtain ⟨hI0, hC0⟩ := inv_extract hI hu hmin
    obtain ⟨hI1, -, -, -, hm1, hm2, hm3⟩ :=
      Scan.inv hout hsort hscan (List.suffix_refl _) hI0 hC0
    exact ⟨hI1, hm1, hm2, hm3, fun h => absurd h (by decide)⟩
  | stepFull σ σ' u n _ hu hmin hscan =>
    obtain ⟨hI0, hC0⟩ := inv_extract hI hu hmin
    obtain ⟨hI1, -, -, -, hm1, hm2, hm3⟩ :=
      Scan.inv hout hsort hscan (List.suffix_refl _) hI0 hC0
    exact ⟨hI1, hm1, hm2, hm3, fun h => absurd h (by decide)⟩


/-- **Lemma H1 (failed-search completeness).**  If a search that starts with a COMPLETE member
`x` of `val` FAILS, and every deleted edge goes to a strictly smaller canonical label (`Dinv`, so
canonical edges are never deleted), then every `v` whose canonical path visits `x` and with
`dis v < B` ends in `val` with its canonical label. -/
theorem Search.failed_complete (hout : OutOK c) (hsort : OutSorted c) {T : Finset (Fin G.n)}
    {σ0 σ' : SSt G s} {n : ℕ} {x : Fin G.n} (h : Search c T σ0 σ' .failed n) (hI : SInv c σ0)
    (hCl : ∀ w ∈ σ0.done, ∀ e ∈ c.out w, Closed c σ0 w e) (hxval : x ∈ σ0.val)
    (hx : Complete σ0.d x)
    (hD : ∀ e ∈ σ'.D, dis (s := s) (G.dst e) < dis (s := s) (G.src e)) {v : Fin G.n}
    (hvis : OnPath (s := s) x v) (hvB : dis (s := s) v < c.B) :
    v ∈ σ'.val ∧ Complete σ'.d v := by
  obtain ⟨hI', hle, hval, -, hf⟩ := Search.inv hout hsort h hI hCl
  obtain ⟨hH, -, hcl⟩ := hf rfl
  have hsound : Sound σ'.d := hI'.walk.sound
  obtain ⟨R, hR, hwR⟩ := hvis.path_prefix
  have hPx : G.IsWalk s x (path (s := s) x) := (path_isMinWalk hvis.reachable_left).1
  have main : ∀ R1 R2 : List (Fin G.m), R = R1 ++ R2 → ∀ z, G.IsWalk x z R1 →
      z ∈ σ'.val ∧ Complete σ'.d z ∧ dis (s := s) x ≤ dis (s := s) z ∧
        OnPath (s := s) z v := by
    intro R1
    induction R1 using List.reverseRecOn with
    | nil =>
      intro R2 _ z hz
      rw [isWalk_nil_iff] at hz
      subst hz
      exact ⟨hval hxval, le_antisymm ((hle x).trans hx.le) (hsound x), le_rfl, hvis⟩
    | append_singleton R0 e ih =>
      intro R2 hR12 z hz
      obtain ⟨hR0, rfl⟩ := IsWalk.concat_iff.mp hz
      obtain ⟨hyval, hyc, hxy, -⟩ := ih ([e] ++ R2) (by rw [hR12, List.append_assoc]) _ hR0
      have hR2 : G.IsWalk (G.dst e) v R2 := by
        rw [hR12] at hwR
        obtain ⟨w, hw1, hw2⟩ := hwR.of_append
        obtain ⟨-, rfl⟩ := IsWalk.concat_iff.mp hw1
        exact hw2
      have hPR : path (s := s) v = (path (s := s) x ++ R0) ++ e :: R2 := by
        rw [hR, hR12]; simp [List.append_assoc]
      obtain ⟨hdis, hon2, -⟩ := dis_succ_on_path hvis.1 hPR (hPx.append hR0) hR2
      have hyext : G.src e ∈ σ'.done := by
        rcases Finset.mem_union.mp (hI'.valDone hyval) with h1 | h1
        · exact h1
        · rw [hH] at h1; exact absurd h1 (Finset.notMem_empty _)
      have he : e ∈ c.out (G.src e) := (hout _ e).mpr rfl
      have hcand : ext (σ'.d (G.src e)) e = dis (s := s) (G.dst e) := by rw [hyc, hdis]
      have hzB : dis (s := s) (G.dst e) < c.B := lt_of_le_of_lt hon2.dis_le hvB
      have hyfin : dis (s := s) (G.src e) ≠ ⊤ := by
        rw [dis_of_reachable ⟨_, hPx.append hR0⟩]; exact WithTop.coe_ne_top
      have hxz : dis (s := s) x < dis (s := s) (G.dst e) := by
        rw [hdis]; exact lt_of_le_of_lt hxy (lt_ext_of_ne_top hyfin e)
      rcases hcl _ hyext e he (by rw [hcand]; exact hzB) with hF | ⟨hle', heq⟩
      · exfalso
        have h1 := hD e hF
        rw [hdis] at h1
        exact absurd h1 (not_lt_of_ge (lt_ext_of_ne_top hyfin e).le)
      · rw [hcand] at hle' heq
        have hdeq : σ'.d (G.dst e) = dis (s := s) (G.dst e) := le_antisymm hle' (hsound _)
        exact ⟨heq hdeq, hdeq, hxz.le, hon2⟩
  obtain ⟨hvval, hvc, -, -⟩ := main R [] (by simp) v hwR
  exact ⟨hvval, hvc⟩


/-- A valid relaxation into a COMPLETE vertex certifies that the tail is complete and lies on the
head's canonical path (the tie case of B1 L3+). -/
theorem valid_into_complete {d : Labels G s} (hw : WalkInv d) {u : Fin G.n} {e : Fin G.m}
    (he : G.src e = u) (hu : d u ≠ ⊤) (hok : Ok d u e) (hc : Complete d (G.dst e)) :
    Complete d u ∧ OnPath (s := s) u (G.dst e) := by
  obtain ⟨q0, hq0⟩ := WithTop.ne_top_iff_exists.mp hu
  obtain ⟨q, hq⟩ : ∃ q : List (Fin G.m), d u = ((toW q : WalkOrd G s) : WLab G s) :=
    ⟨q0, hq0.symm⟩
  have hwq : G.IsWalk s u q := hw u q hq
  have hwe : G.IsWalk s (G.dst e) (q ++ [e]) := walk_ext hwq e he
  have hle : ext (d u) e ≤ dis (s := s) (G.dst e) := hc ▸ hok
  rw [hq, ext_coe] at hle
  have hge := dis_le_walk (s := s) hwe
  have heq : dis (s := s) (G.dst e) = ((toW (q ++ [e]) : WalkOrd G s) : WLab G s) :=
    le_antisymm hge hle
  have hreach : G.Reachable s (G.dst e) := ⟨_, hwe⟩
  rw [dis_of_reachable hreach] at heq
  have hpath : path (s := s) (G.dst e) = q ++ [e] := WithTop.coe_injective heq
  have hmin : IsMinWalk (s := s) (G.dst e) (q ++ [e]) := hpath ▸ path_isMinWalk hreach
  have hpu : path (s := s) u = q := path_eq_of_isMinWalk (hmin.prefix hwq (he ▸ IsWalk.single e))
  refine ⟨?_, hreach, q, [e], hpath, hwq, he ▸ IsWalk.single e⟩
  show d u = dis (s := s) u
  rw [hq, dis_of_reachable ⟨q, hwq⟩, hpu]

/-- Confinement invariant relative to the invocation's initial labels `d0` and the target set
`U = Ũ(B, S)`: valid and extracted vertices, and every changed label, lie in `U`; the deleted
edge set satisfies `Dinv`. -/
structure Conf (d0 : Labels G s) (U : Set (Fin G.n)) (σ : SSt G s) : Prop where
  val : ∀ v ∈ σ.val, v ∈ U
  done : ∀ v ∈ σ.done, v ∈ U
  chg : ∀ v, σ.d v ≠ d0 v → v ∈ U
  /-- `Dinv` (PAPER_CHD Lemma L(b)): deleted edges go to strictly smaller canonical labels -/
  dinv : ∀ e ∈ σ.D, dis (s := s) (G.dst e) < dis (s := s) (G.src e)

/-- The confinement step: a valid in-range relaxation from a vertex of `Ũ(B,S)` stays in it,
given Claim C at the invocation start. -/
theorem valid_mem_utilde {S : Set (Fin G.n)} {d0 d : Labels G s}
    (hclaim : ∀ v, dis (s := s) v < c.B → v ∉ Utilde c.B S → Complete d0 v)
    (hwalk : WalkInv d) (hchg : ∀ v, d v ≠ d0 v → v ∈ Utilde c.B S) {u : Fin G.n} {e : Fin G.m}
    (he : G.src e = u) (hu : d u ≠ ⊤) (huU : u ∈ Utilde c.B S) (hok : Ok d u e)
    (hB : ext (d u) e < c.B) : G.dst e ∈ Utilde c.B S := by
  by_contra hnot
  have hdisB : dis (s := s) (G.dst e) < c.B := by
    have h1 := (hwalk.relaxL he).sound (G.dst e)
    rw [relaxL_apply_self hok] at h1
    exact lt_of_le_of_lt h1 hB
  have hc0 := hclaim _ hdisB hnot
  have hsame : d (G.dst e) = d0 (G.dst e) := by
    by_contra h; exact hnot (hchg _ h)
  have hc : Complete d (G.dst e) := by
    show d (G.dst e) = dis (s := s) (G.dst e); rw [hsame]; exact hc0
  obtain ⟨-, hon⟩ := valid_into_complete hwalk he hu hok hc
  obtain ⟨-, y, hy, hyu⟩ := huU
  exact hnot ⟨hdisB, y, hy, hyu.trans hon⟩


section ConfSec

variable {S : Set (Fin G.n)} {d0 : Labels G s}

theorem conf_ok_insert {σ : SSt G s} {u : Fin G.n} {e : Fin G.m}
    (hclaim : ∀ v, dis (s := s) v < c.B → v ∉ Utilde c.B S → Complete d0 v)
    (hI : SInv c σ) (hC : CurInv σ u) (hcf : Conf d0 (Utilde c.B S) σ) (he : G.src e = u)
    (hok : Ok σ.d u e) (hB : ext (σ.d u) e < c.B) (K' : List (Fin G.n))
    (kp : Fin G.n → Fin G.n) :
    Conf d0 (Utilde c.B S)
      { σ with d := relaxL σ.d u e, K := K', val := insert (G.dst e) σ.val,
               H := insert (G.dst e) σ.H, kpar := kp } := by
  have hmem := valid_mem_utilde hclaim hI.walk hcf.chg he hC.fin (hcf.done u hC.mem) hok hB
  refine ⟨?_, hcf.done, ?_, hcf.dinv⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hmem
    · exact hcf.val v hv
  · intro v hv
    by_cases hve : v = G.dst e
    · subst hve; exact hmem
    · have : relaxL σ.d u e v = σ.d v := relaxL_apply_ne hve
      exact hcf.chg v (by simpa [this] using hv)

theorem Scan.conf (hout : OutOK c)
    (hclaim : ∀ v, dis (s := s) v < c.B → v ∉ Utilde c.B S → Complete d0 v)
    (hLxU : ∀ v ∈ Utilde c.B S, c.Lx ≤ dis (s := s) v)
    {T : Finset (Fin G.n)} {u : Fin G.n} {σ σ' : SSt G s} {L : List (Fin G.m)} {r : ScanRes}
    {n : ℕ} (h : Scan c T u σ L σ' r n) (hL : L <:+ c.out u) (hI : SInv c σ)
    (hC : CurInv σ u) (hcf : Conf d0 (Utilde c.B S) σ) : Conf d0 (Utilde c.B S) σ' := by
  induction h with
  | nil σ => exact hcf
  | del σ σ' e L r n _ _ ih => exact ih ((List.suffix_cons e L).trans hL) hI hC hcf
  | brk σ e L _ _ => exact hcf
  | lxdel σ σ' e L r n _ _ hlow _ ih =>
    obtain ⟨hI1, hC1, -⟩ := inv_lxdel e hI hC
    have he : e ∈ c.out u := hL.subset List.mem_cons_self
    have hsrc : G.src e = u := (hout u e).mp he
    have hnew : dis (s := s) (G.dst e) < dis (s := s) (G.src e) := by
      rw [hsrc]
      exact lt_of_le_of_lt (hI.walk.sound _) (lt_of_lt_of_le hlow (hLxU u (hcf.done u hC.mem)))
    refine ih ((List.suffix_cons e L).trans hL) hI1 hC1 ⟨hcf.val, hcf.done, hcf.chg, ?_⟩
    intro e' he'
    rcases Finset.mem_insert.mp he' with rfl | he'
    · exact hnew
    · exact hcf.dinv e' he'
  | contact σ e L hF hB _ _ =>
    have he : e ∈ c.out u := hL.subset List.mem_cons_self
    have hsrc : G.src e = u := (hout u e).mp he
    by_cases hok : Ok σ.d u e
    · have hmem := valid_mem_utilde hclaim hI.walk hcf.chg hsrc hC.fin (hcf.done u hC.mem) hok hB
      refine ⟨hcf.val, hcf.done, fun v hv => ?_, hcf.dinv⟩
      by_cases hve : v = G.dst e
      · subst hve; exact hmem
      · have : relaxL σ.d u e v = σ.d v := relaxL_apply_ne hve
        exact hcf.chg v (by simpa [this] using hv)
    · have hs : relaxL σ.d u e = σ.d := relaxL_of_not_ok hok
      exact ⟨hcf.val, hcf.done, fun v hv => hcf.chg v (by simpa [hs] using hv), hcf.dinv⟩
  | newFull σ e L hF hB _ _ _ _ =>
    have he : e ∈ c.out u := hL.subset List.mem_cons_self
    have hsrc : G.src e = u := (hout u e).mp he
    by_cases hok : Ok σ.d u e
    · have h := conf_ok_insert hclaim hI hC hcf hsrc hok hB (σ.K ++ [G.dst e])
        (Function.update σ.kpar (G.dst e) u)
      simpa [addNew, hok] using h
    · simpa [addNew, hok] using (⟨hcf.val, hcf.done, hcf.chg, hcf.dinv⟩ :
        Conf d0 (Utilde c.B S)
          { σ with K := σ.K ++ [G.dst e], kpar := Function.update σ.kpar (G.dst e) u })
  | newCont σ σ' e L r n hF hB _ _ _ _ _ ih =>
    have he : e ∈ c.out u := hL.subset List.mem_cons_self
    have hsrc : G.src e = u := (hout u e).mp he
    obtain ⟨hI1, hC1, -⟩ := inv_addNew hout hI hC he hB
    refine ih ((List.suffix_cons e L).trans hL) hI1 hC1 ?_
    by_cases hok : Ok σ.d u e
    · have h := conf_ok_insert hclaim hI hC hcf hsrc hok hB (σ.K ++ [G.dst e])
        (Function.update σ.kpar (G.dst e) u)
      simpa [addNew, hok] using h
    · simpa [addNew, hok] using (⟨hcf.val, hcf.done, hcf.chg, hcf.dinv⟩ :
        Conf d0 (Utilde c.B S)
          { σ with K := σ.K ++ [G.dst e], kpar := Function.update σ.kpar (G.dst e) u })
  | inK σ σ' e L r n hF hB _ _ hK _ ih =>
    have he : e ∈ c.out u := hL.subset List.mem_cons_self
    have hsrc : G.src e = u := (hout u e).mp he
    obtain ⟨hI1, hC1, -⟩ := inv_improve hout hI hC he hB hK
    refine ih ((List.suffix_cons e L).trans hL) hI1 hC1 ?_
    by_cases hok : Ok σ.d u e
    · have h := conf_ok_insert hclaim hI hC hcf hsrc hok hB σ.K σ.kpar
      simpa [improve, hok] using h
    · simpa [improve, hok] using hcf

theorem Search.conf (hout : OutOK c) (hsort : OutSorted c)
    (hclaim : ∀ v, dis (s := s) v < c.B → v ∉ Utilde c.B S → Complete d0 v)
    (hLxU : ∀ v ∈ Utilde c.B S, c.Lx ≤ dis (s := s) v)
    {T : Finset (Fin G.n)} {σ σ' : SSt G s} {res : SearchRes} {n : ℕ}
    (h : Search c T σ σ' res n) (hI : SInv c σ) (hcf : Conf d0 (Utilde c.B S) σ) :
    Conf d0 (Utilde c.B S) σ' := by
  induction h with
  | empty σ _ _ => exact hcf
  | capped σ _ => exact hcf
  | stepCont σ σ' σ'' u res n n' _ hu hmin hscan _ ih =>
    obtain ⟨hI0, hC0⟩ := inv_extract hI hu hmin
    have hcf0 : Conf d0 (Utilde c.B S) { σ with H := σ.H.erase u, done := insert u σ.done } :=
      ⟨hcf.val, fun v hv => by
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact hcf.val v (hI.heapVal hu)
        · exact hcf.done v hv, hcf.chg, hcf.dinv⟩
    obtain ⟨hI1, -⟩ := Scan.inv hout hsort hscan (List.suffix_refl _) hI0 hC0
    exact ih hI1 (Scan.conf hout hclaim hLxU hscan (List.suffix_refl _) hI0 hC0 hcf0)
  | stepContact σ σ' u n _ hu hmin hscan =>
    obtain ⟨hI0, hC0⟩ := inv_extract hI hu hmin
    have hcf0 : Conf d0 (Utilde c.B S) { σ with H := σ.H.erase u, done := insert u σ.done } :=
      ⟨hcf.val, fun v hv => by
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact hcf.val v (hI.heapVal hu)
        · exact hcf.done v hv, hcf.chg, hcf.dinv⟩
    exact Scan.conf hout hclaim hLxU hscan (List.suffix_refl _) hI0 hC0 hcf0
  | stepFull σ σ' u n _ hu hmin hscan =>
    obtain ⟨hI0, hC0⟩ := inv_extract hI hu hmin
    have hcf0 : Conf d0 (Utilde c.B S) { σ with H := σ.H.erase u, done := insert u σ.done } :=
      ⟨hcf.val, fun v hv => by
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact hcf.val v (hI.heapVal hu)
        · exact hcf.done v hv, hcf.chg, hcf.dinv⟩
    exact Scan.conf hout hclaim hLxU hscan (List.suffix_refl _) hI0 hC0 hcf0

end ConfSec

end Invariants

/-! ## The invocation loop (FH.1–FH.23) and the FindPivots contract -/

theorem Scan.K_prefix {c : FPCtx G s} {T : Finset (Fin G.n)} {u : Fin G.n} {σ σ' : SSt G s}
    {L : List (Fin G.m)} {r : ScanRes} {n : ℕ} (h : Scan c T u σ L σ' r n) : σ.K <+: σ'.K := by
  induction h with
  | nil σ => exact List.prefix_refl _
  | del _ _ _ _ _ _ _ _ ih => exact ih
  | brk σ _ _ _ _ => exact List.prefix_refl _
  | lxdel _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | contact σ _ _ _ _ _ _ => exact List.prefix_refl _
  | newFull σ e _ _ _ _ _ _ _ =>
    by_cases hok : Ok σ.d u e <;> simp [addNew, hok]
  | newCont σ σ' e _ _ _ _ _ _ _ _ _ _ ih =>
    refine List.IsPrefix.trans ?_ ih
    by_cases hok : Ok σ.d u e <;> simp [addNew, hok]
  | inK σ σ' e _ _ _ _ _ _ _ _ _ ih =>
    refine List.IsPrefix.trans ?_ ih
    by_cases hok : Ok σ.d u e <;> simp [improve, hok]

theorem Search.K_prefix {c : FPCtx G s} {T : Finset (Fin G.n)} {σ σ' : SSt G s}
    {res : SearchRes} {n : ℕ} (h : Search c T σ σ' res n) : σ.K <+: σ'.K := by
  induction h with
  | empty σ _ _ => exact List.prefix_refl _
  | capped σ _ => exact List.prefix_refl _
  | stepCont _ _ _ _ _ _ _ _ _ _ hscan _ ih => exact (Scan.K_prefix hscan).trans ih
  | stepContact _ _ _ _ _ _ _ hscan => have h1 := Scan.K_prefix hscan; exact h1
  | stepFull _ _ _ _ _ _ _ hscan => have h1 := Scan.K_prefix hscan; exact h1

/-- The parent path from `u` up to `x` (fuel-bounded). -/
def kpath {α : Type*} [DecidableEq α] (kpar : α → α) (x : α) : ℕ → α → List α
  | 0, u => [u]
  | f + 1, u => if u = x then [u] else u :: kpath kpar x f (kpar u)

open Frontier.CHD.Partition in
/-- Merge a contact search `K` (root `x`, first-discovery parents `kpar`) into the tree `Tr`
through the contact edge `(u, v)`, re-rooting `K` at `u` along its parent path (agent-03's
`mergeAt_parentFirst` shape). -/
noncomputable def mergeTree (Tr : Partition.TreeRec (Fin G.n)) (K : List (Fin G.n))
    (kpar : Fin G.n → Fin G.n) (x u v : Fin G.n) : Partition.TreeRec (Fin G.n) :=
  { root := Tr.root,
    ord := Tr.ord ++ kpath kpar x K.length u ++ K.filter (fun y => y ∉ kpath kpar x K.length u),
    par := reroot (kpath kpar x K.length u) v (fun w => if w ∈ K then kpar w else Tr.par w) }

/-- The forest after a non-failed search (FH.12 merge on contact, FH.20 new tree on success). -/
noncomputable def growForest (res : SearchRes) (trees : List (Partition.TreeRec (Fin G.n)))
    (x : Fin G.n) (σ : SSt G s) : List (Partition.TreeRec (Fin G.n)) :=
  match res, σ.hit with
  | .contact, some (u, v) =>
      trees.map (fun Tr => if v ∈ Tr.ord then mergeTree Tr σ.K σ.kpar x u v else Tr)
  | _, _ => trees ++ [⟨x, σ.K, σ.kpar⟩]

variable (G s) in
/-- State of one FindPivots-HD invocation. -/
structure IState where
  /-- global labels -/
  d : Labels G s
  /-- deleted edges (persistent across calls) -/
  D : Finset (Fin G.m)
  /-- vertices of the trees built so far (FH.3 `fmark`) -/
  tv : Finset (Fin G.n)
  /-- union of the valid parts of failed searches -/
  W : Finset (Fin G.n)
  /-- failed roots -/
  Q : Finset (Fin G.n)
  /-- the trees built so far, as parent-first records (input of the tree partition, agent-03) -/
  trees : List (Partition.TreeRec (Fin G.n))

/-- The invocation loop over the frontier list (FH.2–FH.22).  A root already in a tree is
skipped (FH.3); a failed search records its VALID part in `W` and its root in `Q` (FH.21);
a successful or contact search adds all its members (leaves included) to the trees (FH.12/FH.20). -/
inductive Invoke (c : FPCtx G s) : IState G s → List (Fin G.n) → IState G s → ℕ → Prop
  | nil (ι : IState G s) : Invoke c ι [] ι 0
  | skip (ι ι' : IState G s) (x : Fin G.n) (L : List (Fin G.n)) (n : ℕ) :
      x ∈ ι.tv → Invoke c ι L ι' n → Invoke c ι (x :: L) ι' (n + 1)
  | fail (ι ι' : IState G s) (x : Fin G.n) (L : List (Fin G.n)) (σ' : SSt G s) (n n' : ℕ) :
      x ∉ ι.tv → Search c ι.tv (initSt ι.d ι.D x) σ' .failed n →
      Invoke c { ι with d := σ'.d, D := σ'.D, W := ι.W ∪ σ'.val, Q := insert x ι.Q } L ι' n' →
      Invoke c ι (x :: L) ι' (n + n' + σ'.K.length + 2)
  | grow (ι ι' : IState G s) (x : Fin G.n) (L : List (Fin G.n)) (σ' : SSt G s)
      (res : SearchRes) (n n' : ℕ) :
      x ∉ ι.tv → res ≠ .failed → Search c ι.tv (initSt ι.d ι.D x) σ' res n →
      Invoke c { ι with d := σ'.d, D := σ'.D, tv := ι.tv ∪ σ'.K.toFinset,
                        trees := growForest res ι.trees x σ' } L ι' n' →
      Invoke c ι (x :: L) ι' (n + n' + σ'.K.length + 2)

/-- The contract of MakePivots (B1 MP.1–MP.10, tree partition by DMSY26 Lemma A.1) used by the
correctness proof: nonempty, pairwise disjoint groups of `S \ Q` covering every root that lies
in a tree.  (Piece sizes and the pivot bound belong to the cost contract.) -/
structure MakePivotsRel (S Q tv : Finset (Fin G.n)) (p : ℕ) (P : Fin p → Finset (Fin G.n)) :
    Prop where
  groups : ∀ j, (P j).Nonempty ∧ P j ⊆ S
  gdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j)
  qdisj : ∀ j, Disjoint Q (P j)
  cover : ∀ x ∈ S, x ∉ Q → x ∈ tv → ∃ j, x ∈ P j

variable (c : FPCtx G s) in
/-- Invariant of an invocation relative to its initial labels `d0` and frontier `S`. -/
structure IInv (d0 : Labels G s) (S : Finset (Fin G.n)) (ι : IState G s) : Prop where
  walk : WalkInv ι.d
  le : ∀ v, ι.d v ≤ d0 v
  chg : ∀ v, ι.d v ≠ d0 v → v ∈ Utilde c.B (S : Set (Fin G.n))
  dinv : ∀ e ∈ ι.D, dis (s := s) (G.dst e) < dis (s := s) (G.src e)
  Wsub : ∀ v ∈ ι.W, v ∈ Utilde c.B (S : Set (Fin G.n))
  Qsub : ι.Q ⊆ S
  Qdone : ∀ y ∈ ι.Q, ∀ v ∈ Utilde c.B (S : Set (Fin G.n)), Complete d0 y →
    OnPath (s := s) y v → v ∈ ι.W ∧ Complete ι.d v

theorem initSt_inv {c : FPCtx G s} {d : Labels G s} {D : Finset (Fin G.m)} {x : Fin G.n}
    (hw : WalkInv d) (hx : d x ≠ ⊤) : SInv c (initSt d D x) where
  walk := hw
  heapVal := subset_rfl
  valK v hv := by simp only [initSt, Finset.mem_singleton] at hv; subst hv; simp [initSt]
  valDone v hv := Finset.mem_union_right _ hv
  doneH := Finset.disjoint_empty_left _
  finVal v hv := by simp only [initSt, Finset.mem_singleton] at hv; subst hv; exact hx
  order v hv := absurd hv (Finset.notMem_empty v)

theorem Invoke.inv {c : FPCtx G s} (hout : OutOK c) (hsort : OutSorted c) {S : Finset (Fin G.n)}
    {d0 : Labels G s} (hpre : CallPre c.B S d0) (hLxS : ∀ x ∈ S, c.Lx ≤ d0 x)
    {ι ι' : IState G s} {L : List (Fin G.n)} {n : ℕ} (h : Invoke c ι L ι' n)
    (hLS : ∀ x ∈ L, x ∈ S) (hI : IInv c d0 S ι) :
    IInv c d0 S ι' ∧ (∀ x ∈ L, x ∈ ι'.Q ∨ x ∈ ι'.tv) ∧ ι.Q ⊆ ι'.Q ∧ ι.tv ⊆ ι'.tv := by
  have hLxU : ∀ v ∈ Utilde c.B (S : Set (Fin G.n)), c.Lx ≤ dis (s := s) v := by
    intro v hv
    rcases hpre.frontier v hv with ⟨hX, -⟩ | ⟨y, hy, hyc, hyv⟩
    · exact absurd hX (Set.notMem_empty v)
    · calc c.Lx ≤ d0 y := hLxS y hy
        _ = dis (s := s) y := hyc
        _ ≤ dis (s := s) v := hyv.dis_le
  induction h with
  | nil ι => exact ⟨hI, fun x hx => absurd hx List.not_mem_nil, subset_rfl, subset_rfl⟩
  | skip ι ι' x L n hx _ ih =>
    obtain ⟨hI', hcov, hQ, htv⟩ := ih (fun y hy => hLS y (List.mem_cons_of_mem _ hy)) hI
    refine ⟨hI', fun y hy => ?_, hQ, htv⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact Or.inr (htv hx)
    · exact hcov y hy
  | fail ι ι' x L σ' n n' hx hsearch _ ih =>
    have hxS : x ∈ S := hLS x List.mem_cons_self
    have hxB : d0 x < c.B := hpre.inRange x hxS
    have hxtop : ι.d x ≠ ⊤ := ne_top_of_lt (lt_of_le_of_lt (hI.le x) hxB)
    have hS0 : SInv c (initSt ι.d ι.D x) := initSt_inv hI.walk hxtop
    obtain ⟨hIs, hle, hval, hF, hf⟩ :=
      Search.inv hout hsort hsearch hS0 (fun w hw => absurd hw (Finset.notMem_empty w))
    have hd0top : d0 x ≠ ⊤ := ne_top_of_lt hxB
    have hxreach : G.Reachable s x := by
      obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hd0top
      exact ⟨q, hpre.walk x q hq.symm⟩
    have hxU : x ∈ Utilde c.B (S : Set (Fin G.n)) :=
      ⟨lt_of_le_of_lt (hpre.walk.sound x) hxB, x, hxS, onPath_self hxreach⟩
    have hcf0 : Conf d0 (Utilde c.B (S : Set (Fin G.n))) (initSt ι.d ι.D x) :=
      ⟨fun v hv => by simp only [initSt, Finset.mem_singleton] at hv; subst hv; exact hxU,
        fun v hv => absurd hv (Finset.notMem_empty v), hI.chg, hI.dinv⟩
    have hcf := Search.conf hout hsort (d0 := d0) hpre.claimC hLxU hsearch hS0 hcf0
    have hsound' : Sound σ'.d := hIs.walk.sound
    have hI1 : IInv c d0 S
        { ι with d := σ'.d, D := σ'.D, W := ι.W ∪ σ'.val, Q := insert x ι.Q } := by
      refine ⟨hIs.walk, fun v => (hle v).trans (hI.le v), hcf.chg, hcf.dinv, ?_, ?_, ?_⟩
      · intro v hv
        rcases Finset.mem_union.mp hv with h1 | h1
        · exact hI.Wsub v h1
        · exact hcf.val v h1
      · exact Finset.insert_subset hxS hI.Qsub
      · intro y hy v hvU hyc hyv
        rcases Finset.mem_insert.mp hy with rfl | hy
        · have hyc' : Complete (initSt ι.d ι.D y).d y :=
            le_antisymm ((hI.le y).trans hyc.le) (hI.walk.sound y)
          obtain ⟨hvv, hvc⟩ := Search.failed_complete hout hsort hsearch hS0
            (fun w hw => absurd hw (Finset.notMem_empty w)) (by simp [initSt]) hyc' hcf.dinv hyv
            hvU.1
          exact ⟨Finset.mem_union_right _ hvv, hvc⟩
        · obtain ⟨hvW, hvc⟩ := hI.Qdone y hy v hvU hyc hyv
          exact ⟨Finset.mem_union_left _ hvW, hvc.of_le hsound' (hle v)⟩
    obtain ⟨hI', hcov, hQ, htv⟩ := ih (fun y hy => hLS y (List.mem_cons_of_mem _ hy)) hI1
    refine ⟨hI', fun y hy => ?_, (Finset.subset_insert _ _).trans hQ, htv⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact Or.inl (hQ (Finset.mem_insert_self _ _))
    · exact hcov y hy
  | grow ι ι' x L σ' res n n' hx _ hsearch _ ih =>
    have hxS : x ∈ S := hLS x List.mem_cons_self
    have hxB : d0 x < c.B := hpre.inRange x hxS
    have hxtop : ι.d x ≠ ⊤ := ne_top_of_lt (lt_of_le_of_lt (hI.le x) hxB)
    have hS0 : SInv c (initSt ι.d ι.D x) := initSt_inv hI.walk hxtop
    obtain ⟨hIs, hle, -, -, -⟩ :=
      Search.inv hout hsort hsearch hS0 (fun w hw => absurd hw (Finset.notMem_empty w))
    have hd0top : d0 x ≠ ⊤ := ne_top_of_lt hxB
    have hxreach : G.Reachable s x := by
      obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hd0top
      exact ⟨q, hpre.walk x q hq.symm⟩
    have hxU : x ∈ Utilde c.B (S : Set (Fin G.n)) :=
      ⟨lt_of_le_of_lt (hpre.walk.sound x) hxB, x, hxS, onPath_self hxreach⟩
    have hcf0 : Conf d0 (Utilde c.B (S : Set (Fin G.n))) (initSt ι.d ι.D x) :=
      ⟨fun v hv => by simp only [initSt, Finset.mem_singleton] at hv; subst hv; exact hxU,
        fun v hv => absurd hv (Finset.notMem_empty v), hI.chg, hI.dinv⟩
    have hcf := Search.conf hout hsort (d0 := d0) hpre.claimC hLxU hsearch hS0 hcf0
    have hsound' : Sound σ'.d := hIs.walk.sound
    have hxK : x ∈ σ'.K := (Search.K_prefix hsearch).subset (by simp [initSt])
    have hI1 : IInv c d0 S
        { ι with d := σ'.d, D := σ'.D, tv := ι.tv ∪ σ'.K.toFinset,
                 trees := growForest res ι.trees x σ' } := by
      refine ⟨hIs.walk, fun v => (hle v).trans (hI.le v), hcf.chg, hcf.dinv, hI.Wsub,
        hI.Qsub, ?_⟩
      intro y hy v hvU hyc hyv
      obtain ⟨hvW, hvc⟩ := hI.Qdone y hy v hvU hyc hyv
      exact ⟨hvW, hvc.of_le hsound' (hle v)⟩
    obtain ⟨hI', hcov, hQ, htv⟩ := ih (fun y hy => hLS y (List.mem_cons_of_mem _ hy)) hI1
    refine ⟨hI', fun y hy => ?_, hQ, (Finset.subset_union_left).trans htv⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact Or.inr (htv (Finset.mem_union_right _ (List.mem_toFinset.mpr hxK)))
    · exact hcov y hy

/-- **FindPivots-HD meets the FindPivots contract** (`CHD.FPContract`, FP1/FP2/FP3 + label
properties), for every execution of the invocation loop followed by any MakePivots output, and
the deleted-edge set keeps `Dinv` (PAPER_CHD Lemma L(b)).  Hypotheses beyond `CallPre`: static
out-list facts, `L_X` below the labels of `S` (true for `L_X = d_B[S]`), `Dinv` of the input
deletions. -/
theorem findPivots_contract {c : FPCtx G s} (hout : OutOK c) (hsort : OutSorted c)
    {S : Finset (Fin G.n)} {SL : List (Fin G.n)} (hSL : ∀ x, x ∈ SL ↔ x ∈ S)
    {d0 : Labels G s} (hpre : CallPre c.B S d0) (hLxS : ∀ x ∈ S, c.Lx ≤ d0 x)
    {D0 : Finset (Fin G.m)} (hD0 : ∀ e ∈ D0, dis (s := s) (G.dst e) < dis (s := s) (G.src e))
    {ι' : IState G s} {n : ℕ} (hrun : Invoke c ⟨d0, D0, ∅, ∅, ∅, []⟩ SL ι' n)
    {p : ℕ} {P : Fin p → Finset (Fin G.n)} (hmp : MakePivotsRel S ι'.Q ι'.tv p P) :
    FPContract c.B S d0 ι'.d p P ι'.Q ι'.W ∧
      ∀ e ∈ ι'.D, dis (s := s) (G.dst e) < dis (s := s) (G.src e) := by
  have hI0 : IInv c d0 S ⟨d0, D0, ∅, ∅, ∅, []⟩ :=
    ⟨hpre.walk, fun _ => le_rfl, fun v h => absurd rfl h, hD0,
      fun v hv => absurd hv (Finset.notMem_empty v), Finset.empty_subset _,
      fun y hy => absurd hy (Finset.notMem_empty y)⟩
  obtain ⟨hI, hcov, -, -⟩ :=
    Invoke.inv hout hsort hpre hLxS hrun (fun x hx => (hSL x).mp hx) hI0
  have hsound : Sound ι'.d := hI.walk.sound
  have hproc : ∀ x ∈ S, x ∈ ι'.Q ∨ x ∈ ι'.tv := fun x hx => hcov x ((hSL x).mpr hx)
  refine ⟨⟨hI.le, hI.walk, hI.chg, ?_, hmp.groups, hmp.gdisj, hI.Qsub, hmp.qdisj, ?_, hI.Wsub⟩,
    hI.dinv⟩
  · intro v hv
    rcases hpre.frontier v hv with ⟨hX, -⟩ | ⟨y, hy, hyc, hyv⟩
    · exact absurd hX (Set.notMem_empty v)
    · by_cases hyQ : y ∈ ι'.Q
      · exact Or.inl (hI.Qdone y hyQ v hv hyc hyv)
      · have hytv : y ∈ ι'.tv := (hproc y hy).resolve_left hyQ
        obtain ⟨j, hj⟩ := hmp.cover y hy hyQ hytv
        exact Or.inr ⟨y, ⟨j, hj⟩, hyc.of_le hsound (hI.le y), hyv⟩
  · intro x hx
    by_cases hxQ : x ∈ ι'.Q
    · exact Or.inl hxQ
    · exact Or.inr (hmp.cover x hx hxQ ((hproc x hx).resolve_left hxQ))

variable (G s) in
/-- **FindPivots-HD as an `FPRel`** for the BMSSP recursion (package L4's `FPRel`/`FPSound`):
some admissible context -- static sorted out-lists listing exactly the out-edges, `L_X` below the
labels of `S` (e.g. `L_X = d_B[S]`), input deletions with `Dinv` -- and some execution of the
invocation loop over some list of `S`, followed by a MakePivots output.  (That the real run
supplies such a context and derivation at every call is the recursion's obligation O14; `Dinv` is
re-established by `findPivots_contract`'s second conclusion.) -/
def FindPivotsHD (B : WLab G s) (S : Finset (Fin G.n)) (d0 d1 : Labels G s) (p : ℕ)
    (P : Fin p → Finset (Fin G.n)) (Q W : Finset (Fin G.n)) : Prop :=
  ∃ (c : FPCtx G s) (SL : List (Fin G.n)) (D0 : Finset (Fin G.m)) (ι' : IState G s) (n : ℕ),
    c.B = B ∧ OutOK c ∧ OutSorted c ∧ (∀ x, x ∈ SL ↔ x ∈ S) ∧ (∀ x ∈ S, c.Lx ≤ d0 x) ∧
    (∀ e ∈ D0, dis (s := s) (G.dst e) < dis (s := s) (G.src e)) ∧
    Invoke c ⟨d0, D0, ∅, ∅, ∅, []⟩ SL ι' n ∧ MakePivotsRel S ι'.Q ι'.tv p P ∧
    d1 = ι'.d ∧ Q = ι'.Q ∧ W = ι'.W

/-- **Soundness of FindPivots-HD in the shape of L4's `FPSound`**: from `CallPre` alone. -/
theorem findPivotsHD_sound :
    ∀ B S d0 d1 p (P : Fin p → Finset (Fin G.n)) Q W,
      CallPre B S d0 → FindPivotsHD G s B S d0 d1 p P Q W → FPContract B S d0 d1 p P Q W := by
  intro B S d0 d1 p P Q W hpre hfp
  obtain ⟨c, SL, D0, ι', n, hB, hout, hsort, hSL, hLx, hD0, hrun, hmp, rfl, rfl, rfl⟩ := hfp
  subst hB
  exact (findPivots_contract hout hsort hSL hpre hLx hD0 hrun hmp).1

/-! ## HD1: the cost of one search (paper H4) -/

section Cost

variable (c : FPCtx G s) in
/-- Cost potential: every deleted edge pays `scanC` (its scan and O(1) unlink), every search
member pays `scanC + hins` (the scan that created it and its heap insertion). -/
def pot (σ : SSt G s) : ℕ :=
  scanC * σ.D.card + (scanC + c.hins) * σ.K.length

/-- Simple out-lists: the heads of each out-list are pairwise distinct (after P2 dedup). -/
def Simple (c : FPCtx G s) : Prop := ∀ u, ((c.out u).map G.dst).Nodup

theorem okCost_le (c : FPCtx G s) (d : Labels G s) (u : Fin G.n) (e : Fin G.m) :
    okCost c d u e ≤ c.hins := by
  unfold okCost; split_ifs <;> omega

theorem scanC_le (c : FPCtx G s) (x : ℕ) : scanC ≤ (scanC + c.hins) * (1 + x) :=
  calc scanC ≤ scanC + c.hins := Nat.le_add_right _ _
    _ = (scanC + c.hins) * 1 := (Nat.mul_one _).symm
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)

theorem countP_le_cons {α : Type*} (p : α → Bool) (a : α) (l : List α) :
    l.countP p ≤ (a :: l).countP p := by
  rw [List.countP_cons]; split <;> omega

theorem pot_addNew (c : FPCtx G s) (σ : SSt G s) (u : Fin G.n) (e : Fin G.m) :
    pot c (addNew σ u e) = pot c σ + (scanC + c.hins) := by
  unfold pot addNew
  split_ifs <;> simp [List.length_append] <;> ring

theorem pot_improve (c : FPCtx G s) (σ : SSt G s) (u : Fin G.n) (e : Fin G.m) :
    pot c (improve σ u e) = pot c σ := by
  unfold pot improve
  split_ifs <;> rfl

theorem pot_lxdel (c : FPCtx G s) (σ : SSt G s) {e : Fin G.m} (he : e ∉ σ.D) :
    pot c { σ with D := insert e σ.D } = pot c σ + scanC := by
  unfold pot
  simp only [Finset.card_insert_of_notMem he]
  ring

theorem Scan.done_eq {c : FPCtx G s} {T : Finset (Fin G.n)} {u : Fin G.n} {σ σ' : SSt G s}
    {L : List (Fin G.m)} {r : ScanRes} {n : ℕ} (h : Scan c T u σ L σ' r n) : σ'.done = σ.done := by
  induction h with
  | nil σ => rfl
  | del _ _ _ _ _ _ _ _ ih => exact ih
  | brk σ _ _ _ _ => rfl
  | lxdel _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | contact σ _ _ _ _ _ _ => rfl
  | newFull σ e _ _ _ _ _ _ _ => by_cases hok : Ok σ.d u e <;> simp [addNew, hok]
  | newCont σ σ' e _ _ _ _ _ _ _ _ _ _ ih =>
    rw [ih]; by_cases hok : Ok σ.d u e <;> simp [addNew, hok]
  | inK σ σ' e _ _ _ _ _ _ _ _ _ ih =>
    rw [ih]; by_cases hok : Ok σ.d u e <;> simp [improve, hok]

/-- Cost of scanning a list: `n + pot σ ≤ pot σ' + (scanC + hins)·(1 + #edges of L into the final
`K`)`.  With simple lists the last count is at most `|K|`. -/
theorem Scan.cost {c : FPCtx G s} {T : Finset (Fin G.n)} {u : Fin G.n} {σ σ' : SSt G s}
    {L : List (Fin G.m)} {r : ScanRes} {n : ℕ} (h : Scan c T u σ L σ' r n) :
    n + pot c σ ≤ pot c σ' + (scanC + c.hins) * (1 + L.countP (fun e => G.dst e ∈ σ'.K)) := by
  induction h with
  | nil σ => simp
  | del σ σ' e L r n _ _ ih =>
    refine ih.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _)
    exact Nat.add_le_add_left (countP_le_cons _ _ _) _
  | brk σ e L _ _ =>
    have := scanC_le c ((e :: L).countP (fun e => G.dst e ∈ σ.K))
    omega
  | lxdel σ σ' e L r n hF _ _ _ ih =>
    rw [pot_lxdel c σ hF] at ih
    have hc : L.countP (fun e => G.dst e ∈ σ'.K) ≤ (e :: L).countP (fun e => G.dst e ∈ σ'.K) :=
      countP_le_cons _ _ _
    have := Nat.mul_le_mul_left (scanC + c.hins) (Nat.add_le_add_left hc 1)
    omega
  | contact σ e L _ _ _ _ =>
    have hp : pot c { σ with d := relaxL σ.d u e, hit := some (u, G.dst e) } = pot c σ := rfl
    rw [hp]
    exact Nat.add_le_add_right (scanC_le c _) _ |>.trans (le_of_eq (Nat.add_comm _ _))
  | newFull σ e L _ _ _ _ _ _ =>
    rw [pot_addNew]
    have := okCost_le c σ.d u e
    have h2 : 0 ≤ (scanC + c.hins) * (1 + (e :: L).countP (fun e => G.dst e ∈ (addNew σ u e).K)) :=
      Nat.zero_le _
    omega
  | newCont σ σ' e L r n _ _ _ _ _ _ _ ih =>
    rw [pot_addNew] at ih
    have := okCost_le c σ.d u e
    have hc : L.countP (fun e => G.dst e ∈ σ'.K) ≤ (e :: L).countP (fun e => G.dst e ∈ σ'.K) :=
      countP_le_cons _ _ _
    have := Nat.mul_le_mul_left (scanC + c.hins) (Nat.add_le_add_left hc 1)
    omega
  | inK σ σ' e L r n _ _ _ _ hK hscan ih =>
    rw [pot_improve] at ih
    have hpre : (improve σ u e).K <+: σ'.K := Scan.K_prefix hscan
    have hKe : G.dst e ∈ σ'.K := by
      have : (improve σ u e).K = σ.K := by
        by_cases hok : Ok σ.d u e <;> simp [improve, hok]
      exact hpre.subset (this ▸ hK)
    have hc : (e :: L).countP (fun e => G.dst e ∈ σ'.K) =
        L.countP (fun e => G.dst e ∈ σ'.K) + 1 := by
      rw [List.countP_cons_of_pos]; simpa using hKe
    rw [hc]
    have := okCost_le c σ.d u e
    have h3 : (scanC + c.hins) * (1 + (L.countP (fun e => G.dst e ∈ σ'.K) + 1)) =
        (scanC + c.hins) * (1 + L.countP (fun e => G.dst e ∈ σ'.K)) + (scanC + c.hins) := by ring
    rw [h3]
    omega

theorem countP_le_length_of_nodup {L : List (Fin G.m)} (hL : (L.map G.dst).Nodup)
    (K : List (Fin G.n)) : L.countP (fun e => G.dst e ∈ K) ≤ K.length := by
  classical
  rw [List.countP_eq_length_filter]
  have hnd : ((L.filter (fun e => G.dst e ∈ K)).map G.dst).Nodup :=
    hL.sublist (List.Sublist.map G.dst List.filter_sublist)
  have hsub : ((L.filter (fun e => G.dst e ∈ K)).map G.dst).toFinset ⊆ K.toFinset := by
    intro v hv
    simp only [List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq] at hv
    obtain ⟨e, ⟨-, he⟩, rfl⟩ := hv
    exact List.mem_toFinset.mpr he
  calc (L.filter (fun e => G.dst e ∈ K)).length
      = ((L.filter (fun e => G.dst e ∈ K)).map G.dst).length := (List.length_map _).symm
    _ = ((L.filter (fun e => G.dst e ∈ K)).map G.dst).toFinset.card :=
        (List.toFinset_card_of_nodup hnd).symm
    _ ≤ K.toFinset.card := Finset.card_le_card hsub
    _ ≤ K.length := List.toFinset_card_le _


variable (c : FPCtx G s) in
/-- The per-extraction charge of a search ending with member list of length `K`. -/
def extC (K : ℕ) : ℕ := (scanC + c.hins) * (1 + K) + c.hext + 1

/-- **HD1 (paper H4), potential form.**  For every search execution:
`n + pot σ + extC |K'| · |done σ| ≤ pot σ' + extC |K'| · |done σ'| + 1`. -/
theorem Search.cost {c : FPCtx G s} (hout : OutOK c) (hsort : OutSorted c) (hsimp : Simple c)
    {T : Finset (Fin G.n)} {σ σ' : SSt G s} {res : SearchRes} {n : ℕ}
    (h : Search c T σ σ' res n) (hI : SInv c σ) :
    n + pot c σ + extC c σ'.K.length * σ.done.card ≤
      pot c σ' + extC c σ'.K.length * σ'.done.card + 1 := by
  induction h with
  | empty σ _ _ => omega
  | capped σ _ => omega
  | stepCont σ σ1 σ'' u res n n' _ hu hmin hscan hrest ih =>
    obtain ⟨hI0, hC0⟩ := inv_extract hI hu hmin
    obtain ⟨hI1, -⟩ := Scan.inv hout hsort hscan (List.suffix_refl _) hI0 hC0
    have hs := Scan.cost hscan
    have hK1 : σ1.K <+: σ''.K := Search.K_prefix hrest
    have hcnt : (c.out u).countP (fun e => G.dst e ∈ σ1.K) ≤ σ''.K.length :=
      (countP_le_length_of_nodup (hsimp u) σ1.K).trans hK1.length_le
    have hdone : σ1.done.card = σ.done.card + 1 := by
      rw [Scan.done_eq hscan]
      exact Finset.card_insert_of_notMem (Finset.disjoint_right.mp hI.doneH hu)
    have hpot0 : pot c { σ with H := σ.H.erase u, done := insert u σ.done } = pot c σ := rfl
    rw [hpot0] at hs
    have hm := Nat.mul_le_mul_left (scanC + c.hins) (Nat.add_le_add_left hcnt 1)
    have hih := ih hI1
    rw [hdone] at hih
    unfold extC at hih ⊢
    nlinarith [hih, hs, hm]
  | stepContact σ σ1 u n _ hu hmin hscan =>
    have hs := Scan.cost hscan
    have hcnt : (c.out u).countP (fun e => G.dst e ∈ σ1.K) ≤ σ1.K.length :=
      countP_le_length_of_nodup (hsimp u) σ1.K
    have hdone : σ1.done.card = σ.done.card + 1 := by
      rw [Scan.done_eq hscan]
      exact Finset.card_insert_of_notMem (Finset.disjoint_right.mp hI.doneH hu)
    have hpot0 : pot c { σ with H := σ.H.erase u, done := insert u σ.done } = pot c σ := rfl
    rw [hpot0] at hs
    have hm := Nat.mul_le_mul_left (scanC + c.hins) (Nat.add_le_add_left hcnt 1)
    rw [hdone]
    unfold extC
    nlinarith [hs, hm]
  | stepFull σ σ1 u n _ hu hmin hscan =>
    have hs := Scan.cost hscan
    have hcnt : (c.out u).countP (fun e => G.dst e ∈ σ1.K) ≤ σ1.K.length :=
      countP_le_length_of_nodup (hsimp u) σ1.K
    have hdone : σ1.done.card = σ.done.card + 1 := by
      rw [Scan.done_eq hscan]
      exact Finset.card_insert_of_notMem (Finset.disjoint_right.mp hI.doneH hu)
    have hpot0 : pot c { σ with H := σ.H.erase u, done := insert u σ.done } = pot c σ := rfl
    rw [hpot0] at hs
    have hm := Nat.mul_le_mul_left (scanC + c.hins) (Nat.add_le_add_left hcnt 1)
    rw [hdone]
    unfold extC
    nlinarith [hs, hm]


theorem Scan.done_val {c : FPCtx G s} {T : Finset (Fin G.n)} {u : Fin G.n} {σ σ' : SSt G s}
    {L : List (Fin G.m)} {r : ScanRes} {n : ℕ} (h : Scan c T u σ L σ' r n) :
    σ.val ⊆ σ'.val := by
  induction h with
  | nil σ => exact subset_rfl
  | del _ _ _ _ _ _ _ _ ih => exact ih
  | brk σ _ _ _ _ => exact subset_rfl
  | lxdel _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | contact σ _ _ _ _ _ _ => exact subset_rfl
  | newFull σ e _ _ _ _ _ _ _ =>
    by_cases hok : Ok σ.d u e <;> simp [addNew, hok, Finset.subset_insert]
  | newCont σ σ' e _ _ _ _ _ _ _ _ _ _ ih =>
    refine Finset.Subset.trans ?_ ih
    by_cases hok : Ok σ.d u e <;> simp [addNew, hok, Finset.subset_insert]
  | inK σ σ' e _ _ _ _ _ _ _ _ _ ih =>
    refine Finset.Subset.trans ?_ ih
    by_cases hok : Ok σ.d u e <;> simp [improve, hok, Finset.subset_insert]

theorem Scan.K_le {c : FPCtx G s} {T : Finset (Fin G.n)} {u : Fin G.n} {σ σ' : SSt G s}
    {L : List (Fin G.m)} {r : ScanRes} {n : ℕ} (h : Scan c T u σ L σ' r n)
    (hk : σ.K.length < c.k) : σ'.K.length ≤ c.k := by
  induction h with
  | nil σ => omega
  | del _ _ _ _ _ _ _ _ ih => exact ih hk
  | brk σ _ _ _ _ => omega
  | lxdel _ _ _ _ _ _ _ _ _ _ ih => exact ih hk
  | contact σ _ _ _ _ _ _ => exact le_of_lt hk
  | newFull σ e _ _ _ _ _ _ _ =>
    have : (addNew σ u e).K.length = σ.K.length + 1 := by
      by_cases hok : Ok σ.d u e <;> simp [addNew, hok]
    omega
  | newCont _ _ _ _ _ _ _ _ _ _ _ hlt _ ih => exact ih hlt
  | inK σ σ' e _ _ _ _ _ _ _ _ _ ih =>
    have : (improve σ u e).K.length = σ.K.length := by
      by_cases hok : Ok σ.d u e <;> simp [improve, hok]
    exact ih (by omega)

/-- Along a search, extracted vertices stay valid and members stay within the cap. -/
theorem Search.done_val_K {c : FPCtx G s} (hout : OutOK c) (hsort : OutSorted c)
    {T : Finset (Fin G.n)} {σ σ' : SSt G s} {res : SearchRes} {n : ℕ}
    (h : Search c T σ σ' res n) (hI : SInv c σ) (hdv : σ.done ⊆ σ.val) (hK : σ.K.length ≤ c.k) :
    σ'.done ⊆ σ'.val ∧ σ'.K.length ≤ c.k := by
  induction h with
  | empty σ _ _ => exact ⟨hdv, hK⟩
  | capped σ _ => exact ⟨hdv, hK⟩
  | stepCont σ σ1 σ'' u res n n' hlt hu hmin hscan _ ih =>
    obtain ⟨hI0, hC0⟩ := inv_extract hI hu hmin
    obtain ⟨hI1, -⟩ := Scan.inv hout hsort hscan (List.suffix_refl _) hI0 hC0
    have h1 : σ1.done ⊆ σ1.val := by
      rw [Scan.done_eq hscan]
      refine Finset.Subset.trans ?_ (Scan.done_val hscan)
      exact Finset.insert_subset (hI.heapVal hu) hdv
    exact ih hI1 h1 (Scan.K_le hscan hlt)
  | stepContact σ σ1 u n hlt hu hmin hscan =>
    refine ⟨?_, Scan.K_le hscan hlt⟩
    rw [Scan.done_eq hscan]
    refine Finset.Subset.trans ?_ (Scan.done_val hscan)
    exact Finset.insert_subset (hI.heapVal hu) hdv
  | stepFull σ σ1 u n hlt hu hmin hscan =>
    refine ⟨?_, Scan.K_le hscan hlt⟩
    rw [Scan.done_eq hscan]
    refine Finset.Subset.trans ?_ (Scan.done_val hscan)
    exact Finset.insert_subset (hI.heapVal hu) hdv

/-- **HD1 (paper H4) for one search from its root**: the charged cost is at most the deletion and
member potential created plus `extC k · k + 1`, i.e. `O(k²·(scanC + hins) + k·hext)` plus
`scanC` per deleted edge -- `O(k²)` with the unsorted-array local heap (`hins = O(1)`,
`hext = O(k)`). -/
theorem search_cost_le {c : FPCtx G s} (hout : OutOK c) (hsort : OutSorted c) (hsimp : Simple c)
    (hk : 1 ≤ c.k) {T : Finset (Fin G.n)} {d : Labels G s} {D : Finset (Fin G.m)} {x : Fin G.n}
    {σ' : SSt G s} {res : SearchRes} {n : ℕ} (h : Search c T (initSt d D x) σ' res n)
    (hS0 : SInv c (initSt d D x)) :
    n + pot c (initSt d D x) ≤ pot c σ' + extC c c.k * c.k + 1 := by
  have hc := Search.cost hout hsort hsimp h hS0
  have hdone0 : (initSt d D x).done.card = 0 := by simp [initSt]
  rw [hdone0, Nat.mul_zero, Nat.add_zero] at hc
  obtain ⟨hdv, hK⟩ := Search.done_val_K hout hsort h hS0 (by simp [initSt])
    (by simp [initSt]; omega)
  obtain ⟨hIs, -⟩ := Search.inv hout hsort h hS0 (fun w hw => by simp [initSt] at hw)
  have hdK : σ'.done.card ≤ σ'.K.length :=
    calc σ'.done.card ≤ σ'.val.card := Finset.card_le_card hdv
      _ ≤ σ'.K.toFinset.card := Finset.card_le_card (fun v hv => List.mem_toFinset.mpr (hIs.valK v hv))
      _ ≤ σ'.K.length := List.toFinset_card_le _
  have hext : extC c σ'.K.length ≤ extC c c.k := by
    unfold extC
    have := Nat.mul_le_mul_left (scanC + c.hins) (Nat.add_le_add_left hK 1)
    omega
  have : extC c σ'.K.length * σ'.done.card ≤ extC c c.k * c.k :=
    Nat.mul_le_mul hext (hdK.trans hK)
  omega

end Cost

/-! ## Existence of executions (Layer A totality, A2) -/

theorem Scan.exists_run (c : FPCtx G s) (T : Finset (Fin G.n)) (u : Fin G.n) :
    ∀ (L : List (Fin G.m)) (σ : SSt G s), ∃ σ' r n, Scan c T u σ L σ' r n := by
  classical
  intro L
  induction L with
  | nil => intro σ; exact ⟨σ, .cont, 0, Scan.nil σ⟩
  | cons e L ih =>
    intro σ
    by_cases hD : e ∈ σ.D
    · obtain ⟨σ', r, n, h⟩ := ih σ
      exact ⟨σ', r, n, Scan.del σ σ' e L r n hD h⟩
    by_cases hB : ext (σ.d u) e < c.B
    swap
    · exact ⟨σ, .cont, scanC, Scan.brk σ e L hD hB⟩
    by_cases hlx : σ.d (G.dst e) < c.Lx
    · obtain ⟨σ', r, n, h⟩ := ih { σ with D := insert e σ.D }
      exact ⟨σ', r, n + scanC, Scan.lxdel σ σ' e L r n hD hB hlx h⟩
    by_cases hT : G.dst e ∈ T
    · exact ⟨_, .contact, scanC, Scan.contact σ e L hD hB hlx hT⟩
    by_cases hK : G.dst e ∈ σ.K
    · obtain ⟨σ', r, n, h⟩ := ih (improve σ u e)
      exact ⟨σ', r, n + scanC + okCost c σ.d u e, Scan.inK σ σ' e L r n hD hB hlx hT hK h⟩
    by_cases hfull : c.k ≤ (addNew σ u e).K.length
    · exact ⟨_, .full, _, Scan.newFull σ e L hD hB hlx hT hK hfull⟩
    · obtain ⟨σ', r, n, h⟩ := ih (addNew σ u e)
      exact ⟨σ', r, n + scanC + okCost c σ.d u e,
        Scan.newCont σ σ' e L r n hD hB hlx hT hK (lt_of_not_ge hfull) h⟩

/-- Every search from an invariant state has an execution (it terminates: every extraction
adds a new vertex to `done`, and valid relaxations never re-enter extracted vertices). -/
theorem Search.exists_run {c : FPCtx G s} (hout : OutOK c) (hsort : OutSorted c)
    (T : Finset (Fin G.n)) :
    ∀ (m : ℕ) (σ : SSt G s), G.n - σ.done.card ≤ m → SInv c σ →
      ∃ σ' res n, Search c T σ σ' res n := by
  classical
  intro m
  induction m with
  | zero =>
    intro σ hm hI
    by_cases hk : c.k ≤ σ.K.length
    · exact ⟨σ, .success, 1, Search.capped σ hk⟩
    · by_cases hH : σ.H = ∅
      · exact ⟨σ, .failed, 1, Search.empty σ hH (lt_of_not_ge hk)⟩
      · exfalso
        obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hH
        have hud : u ∉ σ.done := Finset.disjoint_right.mp hI.doneH hu
        have hcard : σ.done.card < G.n := by
          have h1 : (insert u σ.done).card ≤ G.n := by
            simpa using Finset.card_le_univ (insert u σ.done)
          rw [Finset.card_insert_of_notMem hud] at h1; omega
        omega
  | succ m ih =>
    intro σ hm hI
    by_cases hk : c.k ≤ σ.K.length
    · exact ⟨σ, .success, 1, Search.capped σ hk⟩
    by_cases hH : σ.H = ∅
    · exact ⟨σ, .failed, 1, Search.empty σ hH (lt_of_not_ge hk)⟩
    obtain ⟨u, hu, hmin⟩ := Finset.exists_min_image σ.H σ.d
      (Finset.nonempty_iff_ne_empty.mpr hH)
    obtain ⟨hI0, hC0⟩ := inv_extract hI hu hmin
    obtain ⟨σ1, r, n1, hscan⟩ :=
      Scan.exists_run c T u (c.out u) { σ with H := σ.H.erase u, done := insert u σ.done }
    have hud : u ∉ σ.done := Finset.disjoint_right.mp hI.doneH hu
    cases r with
    | contact => exact ⟨σ1, .contact, _, Search.stepContact σ σ1 u n1 (lt_of_not_ge hk) hu hmin hscan⟩
    | full => exact ⟨σ1, .success, _, Search.stepFull σ σ1 u n1 (lt_of_not_ge hk) hu hmin hscan⟩
    | cont =>
      obtain ⟨hI1, -⟩ := Scan.inv hout hsort hscan (List.suffix_refl _) hI0 hC0
      have hdone : σ1.done.card = σ.done.card + 1 := by
        rw [Scan.done_eq hscan]; exact Finset.card_insert_of_notMem hud
      obtain ⟨σ', res, n', h'⟩ := ih σ1 (by omega) hI1
      exact ⟨σ', res, _, Search.stepCont σ σ1 σ' u res n1 n' (lt_of_not_ge hk) hu hmin hscan h'⟩

/-- Every invocation over any list of `S` has an execution. -/
theorem Invoke.exists_run {c : FPCtx G s} (hout : OutOK c) (hsort : OutSorted c)
    {S : Finset (Fin G.n)} {d0 : Labels G s} (hpre : CallPre c.B S d0) :
    ∀ (L : List (Fin G.n)) (ι : IState G s), (∀ x ∈ L, x ∈ S) → WalkInv ι.d →
      (∀ v, ι.d v ≤ d0 v) → ∃ ι' n, Invoke c ι L ι' n := by
  classical
  intro L
  induction L with
  | nil => intro ι _ _ _; exact ⟨ι, 0, Invoke.nil ι⟩
  | cons x L ih =>
    intro ι hLS hw hle
    by_cases hx : x ∈ ι.tv
    · obtain ⟨ι', n, h⟩ := ih ι (fun y hy => hLS y (List.mem_cons_of_mem _ hy)) hw hle
      exact ⟨ι', n + 1, Invoke.skip ι ι' x L n hx h⟩
    have hxS : x ∈ S := hLS x List.mem_cons_self
    have hxtop : ι.d x ≠ ⊤ := ne_top_of_lt (lt_of_le_of_lt (hle x) (hpre.inRange x hxS))
    have hS0 : SInv c (initSt ι.d ι.D x) := initSt_inv hw hxtop
    obtain ⟨σ', res, n, hs⟩ := Search.exists_run hout hsort ι.tv G.n (initSt ι.d ι.D x)
      (Nat.sub_le _ _) hS0
    obtain ⟨hIs, hle', -, -, -⟩ :=
      Search.inv hout hsort hs hS0 (fun w hw => absurd hw (Finset.notMem_empty w))
    by_cases hres : res = .failed
    · subst hres
      obtain ⟨ι', n', h⟩ := ih
          { ι with d := σ'.d, D := σ'.D, W := ι.W ∪ σ'.val, Q := insert x ι.Q }
          (fun y hy => hLS y (List.mem_cons_of_mem _ hy)) hIs.walk
          (fun v => (hle' v).trans (hle v))
      exact ⟨ι', _, Invoke.fail ι ι' x L σ' n n' hx hs h⟩
    · obtain ⟨ι', n', h⟩ := ih
          { ι with d := σ'.d, D := σ'.D, tv := ι.tv ∪ σ'.K.toFinset,
                   trees := growForest res ι.trees x σ' }
          (fun y hy => hLS y (List.mem_cons_of_mem _ hy)) hIs.walk
          (fun v => (hle' v).trans (hle v))
      exact ⟨ι', _, Invoke.grow ι ι' x L σ' res n n' hx hres hs h⟩

/-- A MakePivots output always exists (e.g. singleton groups); the real tree-partition output
(package Partition, agent-03) is one particular witness of `MakePivotsRel`. -/
theorem makePivots_exists (S Q tv : Finset (Fin G.n)) :
    ∃ p P, MakePivotsRel S Q tv p P := by
  classical
  let R := ((S \ Q) ∩ tv).toList
  refine ⟨R.length, fun j => {R.get j}, ⟨fun j => ⟨⟨_, Finset.mem_singleton_self _⟩, ?_⟩,
    fun i j hij => ?_, fun j => ?_, fun x hxS hxQ hxt => ?_⟩⟩
  · intro y hy
    rw [Finset.mem_singleton] at hy
    subst hy
    have := Finset.mem_toList.mp (List.get_mem R j)
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp this).1).1
  · rw [Finset.disjoint_singleton]
    intro h
    exact hij ((Finset.nodup_toList _).get_inj_iff.mp h)
  · rw [Finset.disjoint_singleton_right]
    have := Finset.mem_toList.mp (List.get_mem R j)
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp this).1).2
  · have hmem : x ∈ R := Finset.mem_toList.mpr
      (Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨hxS, hxQ⟩, hxt⟩)
    obtain ⟨j, hj⟩ := List.get_of_mem hmem
    exact ⟨j, by rw [← hj]; exact Finset.mem_singleton_self _⟩

/-- **Existence of a FindPivots-HD run** at a call satisfying `CallPre`, for any admissible static
context (this is the part of obligation O14 that FindPivots itself owns: given the context, a
derivation of `FindPivotsHD` exists, so its soundness is not vacuous). -/
theorem findPivotsHD_exists {c : FPCtx G s} (hout : OutOK c) (hsort : OutSorted c)
    {S : Finset (Fin G.n)} {d0 : Labels G s} (hpre : CallPre c.B S d0)
    (hLx : ∀ x ∈ S, c.Lx ≤ d0 x) {D0 : Finset (Fin G.m)}
    (hD0 : ∀ e ∈ D0, dis (s := s) (G.dst e) < dis (s := s) (G.src e)) :
    ∃ d1 p P Q W, FindPivotsHD G s c.B S d0 d1 p P Q W := by
  classical
  obtain ⟨ι', n, hrun⟩ := Invoke.exists_run hout hsort hpre S.toList ⟨d0, D0, ∅, ∅, ∅, []⟩
    (fun x hx => Finset.mem_toList.mp hx) hpre.walk (fun _ => le_rfl)
  obtain ⟨p, P, hmp⟩ := makePivots_exists S ι'.Q ι'.tv
  exact ⟨ι'.d, p, P, ι'.Q, ι'.W, c, S.toList, D0, ι', n, rfl, hout, hsort,
    fun x => Finset.mem_toList, hLx, hD0, hrun, hmp, rfl, rfl, rfl⟩

/-! ## Interface lemmas requested by B-L2 (agent-09) -/

variable (c : FPCtx G s) in
/-- Out-lists have no repeated edge (true for CSR slot ranges; implied by `Simple`). -/
def OutNodup : Prop := ∀ u, (c.out u).Nodup

theorem outNodup_of_simple {c : FPCtx G s} (h : Simple c) : OutNodup c :=
  fun u => List.Nodup.of_map G.dst (h u)

/-- Deleted edges are skipped at no cost: scanning `dels ++ L` from a state in which every edge
of `dels` is deleted is the same as scanning `L`. -/
theorem Scan.append_dels {c : FPCtx G s} {T : Finset (Fin G.n)} {u : Fin G.n} {σ σ' : SSt G s}
    {r : ScanRes} {n : ℕ} :
    ∀ (dels L : List (Fin G.m)), (∀ e ∈ dels, e ∈ σ.D) →
      (Scan c T u σ (dels ++ L) σ' r n ↔ Scan c T u σ L σ' r n) := by
  intro dels
  induction dels with
  | nil => intro L _; simp
  | cons e dels ih =>
    intro L hd
    have he : e ∈ σ.D := hd e List.mem_cons_self
    have hrest : ∀ e' ∈ dels, e' ∈ σ.D := fun e' h => hd e' (List.mem_cons_of_mem _ h)
    constructor
    · intro h
      cases h with
      | del _ _ _ _ _ _ _ h' => exact (ih L hrest).mp h'
      | brk _ _ _ hnd _ => exact absurd he hnd
      | lxdel _ _ _ _ _ _ hnd _ _ _ => exact absurd he hnd
      | contact _ _ _ hnd _ _ _ => exact absurd he hnd
      | newFull _ _ _ hnd _ _ _ _ _ => exact absurd he hnd
      | newCont _ _ _ _ _ _ hnd _ _ _ _ _ _ => exact absurd he hnd
      | inK _ _ _ _ _ _ hnd _ _ _ _ _ => exact absurd he hnd
    · intro h
      exact Scan.del σ σ' e (dels ++ L) r n he ((ih L hrest).mpr h)

/-! ## Search trees: parent-first member lists (for the tree partition / pivot bound) -/

section Trees

open Frontier.CHD.Partition

/-- Tree invariant of a search from root `x`: the member list is a parent-first order for the
first-discovery parents, disjoint from the earlier trees `T`, and every parent is joined to its
child by an out-edge of the parent. -/
structure TreeInv (c : FPCtx G s) (T : Finset (Fin G.n)) (x : Fin G.n) (σ : SSt G s) : Prop where
  pf : ParentFirst σ.kpar x σ.K
  disj : ∀ v ∈ σ.K, v ∉ T
  edge : ∀ v ∈ σ.K, v ≠ x → ∃ e ∈ c.out (σ.kpar v), G.dst e = v

theorem TreeInv.congr {c : FPCtx G s} {T : Finset (Fin G.n)} {x : Fin G.n} {σ σ1 : SSt G s}
    (h : TreeInv c T x σ) (hK : σ1.K = σ.K) (hkp : σ1.kpar = σ.kpar) : TreeInv c T x σ1 := by
  obtain ⟨hpf, hd, he⟩ := h
  exact ⟨hK ▸ hkp ▸ hpf, hK ▸ hd, fun v hv hvx => hkp ▸ he v (hK ▸ hv) hvx⟩

theorem treeInv_addNew {c : FPCtx G s} {T : Finset (Fin G.n)} {x u : Fin G.n} {σ : SSt G s}
    {e : Fin G.m} (h : TreeInv c T x σ) (hu : u ∈ σ.K) (he : e ∈ c.out u) (hT : G.dst e ∉ T)
    (hK : G.dst e ∉ σ.K) : TreeInv c T x (addNew σ u e) := by
  classical
  have hK' : (addNew σ u e).K = σ.K ++ [G.dst e] := by
    by_cases hok : Ok σ.d u e <;> simp [addNew, hok]
  have hkp : (addNew σ u e).kpar = Function.update σ.kpar (G.dst e) u := by
    by_cases hok : Ok σ.d u e <;> simp [addNew, hok]
  obtain ⟨⟨hnd, hhd, hpar⟩, hdisj, hedge⟩ := h
  have hxK : x ∈ σ.K := by
    cases hl : σ.K with
    | nil => rw [hl] at hhd; simp at hhd
    | cons a t => rw [hl] at hhd; simp only [List.head?_cons, Option.some.injEq] at hhd; subst hhd; simp
  have hvx : G.dst e ≠ x := fun h => hK (h ▸ hxK)
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hK']; exact List.nodup_append.mpr ⟨hnd, List.nodup_singleton _,
      fun a ha b hb => by rw [List.mem_singleton] at hb; subst hb; exact fun h => hK (h ▸ ha)⟩
  · rw [hK']
    cases hl : σ.K with
    | nil => rw [hl] at hhd; simp at hhd
    | cons a t => rw [hl] at hhd; simpa using hhd
  · intro pre post w hdec hpre
    rw [hK'] at hdec
    rw [hkp]
    by_cases hw : w = G.dst e
    · subst hw
      rw [Function.update_self]
      -- `pre` must be exactly `σ.K`
      have hpost : post = [] := by
        rcases List.eq_nil_or_concat post with h0 | ⟨L, b, rfl⟩
        · exact h0
        · exfalso
          have : σ.K ++ [G.dst e] = (pre ++ G.dst e :: L) ++ [b] := by rw [hdec]; simp
          have h1 := List.append_inj' this rfl
          have hmem : G.dst e ∈ σ.K := by rw [h1.1]; simp
          exact hK hmem
      subst hpost
      have : pre = σ.K := by
        have h2 : σ.K ++ [G.dst e] = pre ++ [G.dst e] := by simpa using hdec
        exact (List.append_inj' h2 rfl).1.symm
      rw [this]; exact hu
    · rw [Function.update_of_ne hw]
      -- `w` lies in `σ.K`
      have hwK : w ∈ σ.K := by
        have : w ∈ σ.K ++ [G.dst e] := by rw [hdec]; simp
        rcases List.mem_append.mp this with h1 | h1
        · exact h1
        · exact absurd (List.mem_singleton.mp h1) hw
      obtain ⟨pre', post', hdec'⟩ := List.append_of_mem hwK
      have hpp : pre = pre' := by
        have h3 : σ.K ++ [G.dst e] = pre' ++ w :: (post' ++ [G.dst e]) := by rw [hdec']; simp
        exact prefix_unique_of_nodup (List.nodup_append.mpr ⟨hnd, List.nodup_singleton _,
          fun a ha b hb => by rw [List.mem_singleton] at hb; subst hb; exact fun h => hK (h ▸ ha)⟩)
          hdec h3
      subst hpp
      exact hpar pre post' w hdec' hpre
  · intro v hv
    rw [hK'] at hv
    rcases List.mem_append.mp hv with h1 | h1
    · exact hdisj v h1
    · rw [List.mem_singleton.mp h1]; exact hT
  · intro v hv hvx'
    rw [hK'] at hv
    rw [hkp]
    rcases List.mem_append.mp hv with h1 | h1
    · have hne : v ≠ G.dst e := fun h => hK (h ▸ h1)
      rw [Function.update_of_ne hne]; exact hedge v h1 hvx'
    · rw [List.mem_singleton.mp h1, Function.update_self]
      exact ⟨e, he, rfl⟩

theorem treeInv_improve {c : FPCtx G s} {T : Finset (Fin G.n)} {x u : Fin G.n} {σ : SSt G s}
    {e : Fin G.m} (h : TreeInv c T x σ) : TreeInv c T x (improve σ u e) := by
  refine h.congr ?_ ?_ <;> by_cases hok : Ok σ.d u e <;> simp [improve, hok]

theorem Scan.treeInv {c : FPCtx G s} {T : Finset (Fin G.n)} {x u : Fin G.n} {σ σ' : SSt G s}
    {L : List (Fin G.m)} {r : ScanRes} {n : ℕ} (h : Scan c T u σ L σ' r n) (hL : L <:+ c.out u)
    (hu : u ∈ σ.K) (hT : TreeInv c T x σ) : TreeInv c T x σ' := by
  induction h with
  | nil σ => exact hT
  | del _ _ e L _ _ _ _ ih => exact ih ((List.suffix_cons e L).trans hL) hu hT
  | brk σ _ _ _ _ => exact hT
  | lxdel _ _ e L _ _ _ _ _ _ ih => exact ih ((List.suffix_cons e L).trans hL) hu (hT.congr rfl rfl)
  | contact σ _ _ _ _ _ _ => exact hT.congr rfl rfl
  | newFull σ e L _ _ _ hTe hK _ =>
    exact treeInv_addNew hT hu (hL.subset List.mem_cons_self) hTe hK
  | newCont σ σ' e L _ _ _ _ _ hTe hK _ _ ih =>
    have hK' : (addNew σ u e).K = σ.K ++ [G.dst e] := by
      by_cases hok : Ok σ.d u e <;> simp [addNew, hok]
    exact ih ((List.suffix_cons e L).trans hL) (by rw [hK']; exact List.mem_append_left _ hu)
      (treeInv_addNew hT hu (hL.subset List.mem_cons_self) hTe hK)
  | inK σ σ' e L _ _ _ _ _ _ _ _ ih =>
    have hK' : (improve σ u e).K = σ.K := by
      by_cases hok : Ok σ.d u e <;> simp [improve, hok]
    exact ih ((List.suffix_cons e L).trans hL) (by rw [hK']; exact hu) (treeInv_improve hT)

theorem Search.treeInv {c : FPCtx G s} (hout : OutOK c) (hsort : OutSorted c)
    {T : Finset (Fin G.n)} {x : Fin G.n} {σ σ' : SSt G s} {res : SearchRes} {n : ℕ}
    (h : Search c T σ σ' res n) (hI : SInv c σ) (hTI : TreeInv c T x σ) : TreeInv c T x σ' := by
  induction h with
  | empty σ _ _ => exact hTI
  | capped σ _ => exact hTI
  | stepCont σ σ1 σ'' u res n n' _ hu hmin hscan _ ih =>
    obtain ⟨hI0, hC0⟩ := inv_extract hI hu hmin
    obtain ⟨hI1, -⟩ := Scan.inv hout hsort hscan (List.suffix_refl _) hI0 hC0
    exact ih hI1 (Scan.treeInv hscan (List.suffix_refl _) (hI.valK u (hI.heapVal hu))
      (hTI.congr rfl rfl))
  | stepContact σ σ1 u n _ hu _ hscan =>
    exact Scan.treeInv hscan (List.suffix_refl _) (hI.valK u (hI.heapVal hu)) (hTI.congr rfl rfl)
  | stepFull σ σ1 u n _ hu _ hscan =>
    exact Scan.treeInv hscan (List.suffix_refl _) (hI.valK u (hI.heapVal hu)) (hTI.congr rfl rfl)

theorem treeInv_initSt {c : FPCtx G s} {T : Finset (Fin G.n)} {d : Labels G s}
    {D : Finset (Fin G.m)} {x : Fin G.n} (hx : x ∉ T) : TreeInv c T x (initSt d D x) := by
  refine ⟨⟨by simp [initSt], by simp [initSt], ?_⟩, ?_, ?_⟩
  · intro pre post v hdec hpre
    simp only [initSt] at hdec
    rcases pre with _ | ⟨a, pre⟩
    · exact absurd rfl hpre
    · simp at hdec
  · intro v hv; simp only [initSt, List.mem_singleton] at hv; subst hv; exact hx
  · intro v hv hvx; simp only [initSt, List.mem_singleton] at hv; exact absurd hv hvx


theorem idx_par_lt {α : Type*} [DecidableEq α] {kpar : α → α} {x u : α} {K : List α}
    (hpf : ParentFirst kpar x K) (hu : u ∈ K) (hux : u ≠ x) :
    kpar u ∈ K ∧ K.idxOf (kpar u) < K.idxOf u := by
  obtain ⟨hnd, hhd, hpar⟩ := hpf
  obtain ⟨pre, post, hdec⟩ := List.append_of_mem hu
  have hpre : pre ≠ [] := by
    rintro rfl
    simp only [List.nil_append] at hdec
    rw [hdec] at hhd; simp at hhd; exact hux hhd
  have hp := hpar pre post u hdec hpre
  have hupre : u ∉ pre := by
    rw [hdec] at hnd; exact fun hm => (List.nodup_append.mp hnd).2.2 u hm u List.mem_cons_self rfl
  refine ⟨by rw [hdec]; exact List.mem_append_left _ hp, ?_⟩
  rw [hdec, List.idxOf_append_of_mem hp, List.idxOf_append_of_notMem hupre, List.idxOf_cons_self]
  simpa using List.idxOf_lt_length_of_mem hp

/-- Properties of `kpath` along a parent-first order: it runs from `u` to `x` inside `K`, without
repetition, each step following `kpar`, and never above `u` in the order. -/
theorem kpath_spec {α : Type*} [DecidableEq α] {kpar : α → α} {x : α} {K : List α}
    (hpf : ParentFirst kpar x K) :
    ∀ (f : ℕ) (u : α), u ∈ K → K.idxOf u ≤ f →
      (∀ y ∈ kpath kpar x f u, y ∈ K ∧ K.idxOf y ≤ K.idxOf u) ∧ x ∈ kpath kpar x f u ∧
      (kpath kpar x f u).head? = some u ∧ (kpath kpar x f u).Nodup ∧
      (∀ pre post a b, kpath kpar x f u = pre ++ a :: b :: post → b = kpar a) := by
  have hxidx : K.idxOf x = 0 := by
    obtain ⟨-, hhd, -⟩ := hpf
    cases K with
    | nil => simp at hhd
    | cons a t => simp only [List.head?_cons, Option.some.injEq] at hhd; subst hhd; simp
  intro f
  induction f with
  | zero =>
    intro u hu hidx
    have hux : u = x := by
      by_contra hne
      have := (idx_par_lt hpf hu hne).2
      omega
    subst hux
    simp only [kpath]
    refine ⟨fun y hy => ?_, List.mem_singleton_self _, rfl, List.nodup_singleton _, ?_⟩
    · rw [List.mem_singleton] at hy; subst hy; exact ⟨hu, le_rfl⟩
    · intro pre post a b h
      rcases pre with _ | ⟨c, pre⟩ <;> simp at h
  | succ f ih =>
    intro u hu hidx
    by_cases hux : u = x
    · subst hux
      simp only [kpath, ite_true]
      refine ⟨fun y hy => ?_, List.mem_singleton_self _, rfl, List.nodup_singleton _, ?_⟩
      · rw [List.mem_singleton] at hy; subst hy; exact ⟨hu, le_rfl⟩
      · intro pre post a b h
        rcases pre with _ | ⟨c, pre⟩ <;> simp at h
    · simp only [kpath, hux, ite_false]
      obtain ⟨hpK, hplt⟩ := idx_par_lt hpf hu hux
      obtain ⟨hA, hB, hC, hD, hE⟩ := ih (kpar u) hpK (by omega)
      refine ⟨fun y hy => ?_, List.mem_cons_of_mem _ hB, rfl, ?_, ?_⟩
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨hu, le_rfl⟩
        · obtain ⟨h1, h2⟩ := hA y hy; exact ⟨h1, by omega⟩
      · refine List.nodup_cons.mpr ⟨fun hm => ?_, hD⟩
        obtain ⟨-, h2⟩ := hA u hm
        omega
      · intro pre post a b h
        rcases pre with _ | ⟨c, pre⟩
        · simp only [List.nil_append, List.cons.injEq] at h
          obtain ⟨hua, htail⟩ := h
          subst hua
          have : (kpath kpar x f (kpar u)).head? = some b := by rw [htail]; rfl
          rw [hC] at this
          exact (Option.some.inj this).symm
        · simp only [List.cons_append, List.cons.injEq] at h
          exact hE pre post a b h.2


theorem Scan.contact_info {c : FPCtx G s} {T : Finset (Fin G.n)} {u : Fin G.n} {σ σ' : SSt G s}
    {L : List (Fin G.m)} {r : ScanRes} {n : ℕ} (h : Scan c T u σ L σ' r n) (hr : r = .contact) :
    ∃ e ∈ L, σ'.hit = some (u, G.dst e) ∧ G.dst e ∈ T := by
  induction h with
  | nil σ => exact absurd hr (by decide)
  | del _ _ e _ _ _ _ _ ih =>
    obtain ⟨e', he', h1, h2⟩ := ih hr; exact ⟨e', List.mem_cons_of_mem _ he', h1, h2⟩
  | brk σ _ _ _ _ => exact absurd hr (by decide)
  | lxdel _ _ e _ _ _ _ _ _ _ ih =>
    obtain ⟨e', he', h1, h2⟩ := ih hr; exact ⟨e', List.mem_cons_of_mem _ he', h1, h2⟩
  | contact σ e L _ _ _ hT => exact ⟨e, List.mem_cons_self, rfl, hT⟩
  | newFull σ e L _ _ _ _ _ _ => exact absurd hr (by decide)
  | newCont _ _ e _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨e', he', h1, h2⟩ := ih hr; exact ⟨e', List.mem_cons_of_mem _ he', h1, h2⟩
  | inK _ _ e _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨e', he', h1, h2⟩ := ih hr; exact ⟨e', List.mem_cons_of_mem _ he', h1, h2⟩

theorem Scan.full_info {c : FPCtx G s} {T : Finset (Fin G.n)} {u : Fin G.n} {σ σ' : SSt G s}
    {L : List (Fin G.m)} {r : ScanRes} {n : ℕ} (h : Scan c T u σ L σ' r n) (hr : r = .full) :
    c.k ≤ σ'.K.length := by
  induction h with
  | nil σ => exact absurd hr (by decide)
  | del _ _ _ _ _ _ _ _ ih => exact ih hr
  | brk σ _ _ _ _ => exact absurd hr (by decide)
  | lxdel _ _ _ _ _ _ _ _ _ _ ih => exact ih hr
  | contact σ _ _ _ _ _ _ => exact absurd hr (by decide)
  | newFull σ e L _ _ _ _ _ hk => exact hk
  | newCont _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih hr
  | inK _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih hr

/-- What a successful or contact search delivers for the forest. -/
theorem Search.result_info {c : FPCtx G s} (hout : OutOK c) (hsort : OutSorted c)
    {T : Finset (Fin G.n)} {σ σ' : SSt G s}
    {res : SearchRes} {n : ℕ} (h : Search c T σ σ' res n) (hI : SInv c σ) :
    (res = .success → c.k ≤ σ'.K.length) ∧
      (res = .contact → ∃ u v, σ'.hit = some (u, v) ∧ u ∈ σ'.K ∧ v ∈ T ∧
        ∃ e ∈ c.out u, G.dst e = v) := by
  induction h with
  | empty σ _ _ => exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  | capped σ hk => exact ⟨fun _ => hk, fun h => absurd h (by decide)⟩
  | stepCont σ σ1 σ'' u res n n' _ hu hmin hscan hrest ih =>
    obtain ⟨hI0, hC0⟩ := inv_extract hI hu hmin
    obtain ⟨hI1, -⟩ := Scan.inv hout hsort hscan (List.suffix_refl _) hI0 hC0
    exact ih hI1
  | stepContact σ σ1 u n _ hu _ hscan =>
    refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
    obtain ⟨e, he, hhit, hT⟩ := Scan.contact_info hscan rfl
    refine ⟨u, G.dst e, hhit, ?_, hT, e, he, rfl⟩
    exact (Scan.K_prefix hscan).subset (hI.valK u (hI.heapVal hu))
  | stepFull σ σ1 u n hlt _ _ hscan =>
    exact ⟨fun _ => Scan.full_info hscan rfl, fun h => absurd h (by decide)⟩


/-- Forest invariant of an invocation: parent-first trees of at least `k` vertices each,
pairwise vertex-disjoint, whose vertices are exactly the tree-vertex set `tv`. -/
structure FInv (c : FPCtx G s) (ι : IState G s) : Prop where
  pf : ∀ Tr ∈ ι.trees, ParentFirst Tr.par Tr.root Tr.ord
  size : ∀ Tr ∈ ι.trees, c.k ≤ Tr.ord.length
  tv : ∀ v, v ∈ ι.tv ↔ ∃ Tr ∈ ι.trees, v ∈ Tr.ord
  disj : ι.trees.Pairwise (fun a b => ∀ w ∈ a.ord, w ∉ b.ord)

theorem mem_mergeTree_ord {Tr : TreeRec (Fin G.n)} {K : List (Fin G.n)} {kpar : Fin G.n → Fin G.n}
    {x u v w : Fin G.n} (hpathK : ∀ y ∈ kpath kpar x K.length u, y ∈ K) :
    w ∈ (mergeTree Tr K kpar x u v).ord ↔ w ∈ Tr.ord ∨ w ∈ K := by
  classical
  simp only [mergeTree, List.mem_append, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ((h | h) | ⟨h, -⟩)
    · exact Or.inl h
    · exact Or.inr (hpathK w h)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (Or.inl h)
    · by_cases hp : w ∈ kpath kpar x K.length u
      · exact Or.inl (Or.inr hp)
      · exact Or.inr ⟨h, hp⟩

theorem growForest_inv {c : FPCtx G s} (hout : OutOK c) (hsort : OutSorted c) {ι : IState G s}
    {x : Fin G.n} {σ' : SSt G s} {res : SearchRes} {n : ℕ} (hx : x ∉ ι.tv) (hres : res ≠ .failed)
    (hs : Search c ι.tv (initSt ι.d ι.D x) σ' res n) (hS0 : SInv c (initSt ι.d ι.D x))
    (hF : FInv c ι) :
    FInv c { ι with d := σ'.d, D := σ'.D, tv := ι.tv ∪ σ'.K.toFinset,
                    trees := growForest res ι.trees x σ' } := by
  classical
  have hTI : TreeInv c ι.tv x σ' := Search.treeInv hout hsort hs hS0 (treeInv_initSt hx)
  obtain ⟨hsucc, hcont⟩ := Search.result_info hout hsort hs hS0
  have hKtv : ∀ w ∈ σ'.K, w ∉ ι.tv := hTI.disj
  cases res with
  | failed => exact absurd rfl hres
  | success =>
    have hgf : growForest .success ι.trees x σ' = ι.trees ++ [⟨x, σ'.K, σ'.kpar⟩] := by
      simp [growForest]
    have hk := hsucc rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro Tr hTr
      rw [hgf] at hTr
      rcases List.mem_append.mp hTr with h | h
      · exact hF.pf Tr h
      · rw [List.mem_singleton] at h; subst h; exact hTI.pf
    · intro Tr hTr
      rw [hgf] at hTr
      rcases List.mem_append.mp hTr with h | h
      · exact hF.size Tr h
      · rw [List.mem_singleton] at h; subst h; exact hk
    · intro v
      show v ∈ ι.tv ∪ σ'.K.toFinset ↔ ∃ Tr ∈ growForest .success ι.trees x σ', v ∈ Tr.ord
      rw [hgf, Finset.mem_union, hF.tv v, List.mem_toFinset]
      constructor
      · rintro (⟨Tr, hTr, hv⟩ | hv)
        · exact ⟨Tr, List.mem_append_left _ hTr, hv⟩
        · exact ⟨⟨x, σ'.K, σ'.kpar⟩, List.mem_append_right _ (List.mem_singleton_self _), hv⟩
      · rintro ⟨Tr, hTr, hv⟩
        rcases List.mem_append.mp hTr with h | h
        · exact Or.inl ⟨Tr, h, hv⟩
        · rw [List.mem_singleton] at h; subst h; exact Or.inr hv
    · show (growForest .success ι.trees x σ').Pairwise _
      rw [hgf, List.pairwise_append]
      refine ⟨hF.disj, List.pairwise_singleton _ _, fun a ha b hb w hw => ?_⟩
      rw [List.mem_singleton] at hb; subst hb
      exact fun hwK => hKtv w hwK ((hF.tv w).mpr ⟨a, ha, hw⟩)
  | contact =>
    obtain ⟨u, v, hhit, huK, hvT, -⟩ := hcont rfl
    have hgf : growForest .contact ι.trees x σ' =
        ι.trees.map (fun Tr => if v ∈ Tr.ord then mergeTree Tr σ'.K σ'.kpar x u v else Tr) := by
      simp [growForest, hhit]
    obtain ⟨hpA, hpB, hpC, hpD, hpE⟩ := kpath_spec hTI.pf σ'.K.length u huK
      (List.idxOf_lt_length_of_mem huK).le
    have hpathK : ∀ y ∈ kpath σ'.kpar x σ'.K.length u, y ∈ σ'.K := fun y hy => (hpA y hy).1
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro Tr' hTr'
      rw [hgf, List.mem_map] at hTr'
      obtain ⟨Tr, hTr, rfl⟩ := hTr'
      by_cases hvTr : v ∈ Tr.ord
      · simp only [hvTr, ite_true, mergeTree]
        exact mergeAt_parentFirst (hF.pf Tr hTr) hTI.pf
          (fun y hy hyK => hKtv y hyK ((hF.tv y).mpr ⟨Tr, hTr, hy⟩)) hvTr hpD hpathK hpB hpC hpE
      · simp only [hvTr, ite_false]; exact hF.pf Tr hTr
    · intro Tr' hTr'
      rw [hgf, List.mem_map] at hTr'
      obtain ⟨Tr, hTr, rfl⟩ := hTr'
      by_cases hvTr : v ∈ Tr.ord
      · simp only [hvTr, ite_true, mergeTree, List.length_append]
        have := hF.size Tr hTr; omega
      · simp only [hvTr, ite_false]; exact hF.size Tr hTr
    · intro w
      show w ∈ ι.tv ∪ σ'.K.toFinset ↔ ∃ Tr ∈ growForest .contact ι.trees x σ', w ∈ Tr.ord
      rw [hgf, Finset.mem_union, List.mem_toFinset]
      obtain ⟨Tv, hTv, hvTv⟩ := (hF.tv v).mp hvT
      constructor
      · rintro (hw | hw)
        · obtain ⟨Tr, hTr, hwTr⟩ := (hF.tv w).mp hw
          refine ⟨_, List.mem_map_of_mem hTr, ?_⟩
          by_cases hvTr : v ∈ Tr.ord
          · simp only [hvTr, ite_true]; exact (mem_mergeTree_ord hpathK).mpr (Or.inl hwTr)
          · simp only [hvTr, ite_false]; exact hwTr
        · refine ⟨_, List.mem_map_of_mem hTv, ?_⟩
          simp only [hvTv, ite_true]; exact (mem_mergeTree_ord hpathK).mpr (Or.inr hw)
      · rintro ⟨Tr', hTr', hw⟩
        rw [List.mem_map] at hTr'
        obtain ⟨Tr, hTr, rfl⟩ := hTr'
        by_cases hvTr : v ∈ Tr.ord
        · simp only [hvTr, ite_true] at hw
          rcases (mem_mergeTree_ord hpathK).mp hw with h | h
          · exact Or.inl ((hF.tv w).mpr ⟨Tr, hTr, h⟩)
          · exact Or.inr h
        · simp only [hvTr, ite_false] at hw
          exact Or.inl ((hF.tv w).mpr ⟨Tr, hTr, hw⟩)
    · show (growForest .contact ι.trees x σ').Pairwise _
      rw [hgf, List.pairwise_map]
      refine hF.disj.imp_of_mem (fun {a b} ha hb hab => ?_)
      intro w hw hwb
      by_cases hva : v ∈ a.ord <;> by_cases hvb : v ∈ b.ord
      · exact hab v hva hvb
      · simp only [hva, ite_true, hvb, ite_false] at hw hwb
        rcases (mem_mergeTree_ord hpathK).mp hw with h | h
        · exact hab w h hwb
        · exact hKtv w h ((hF.tv w).mpr ⟨b, hb, hwb⟩)
      · simp only [hva, ite_false, hvb, ite_true] at hw hwb
        rcases (mem_mergeTree_ord hpathK).mp hwb with h | h
        · exact hab w hw h
        · exact hKtv w h ((hF.tv w).mpr ⟨a, ha, hw⟩)
      · simp only [hva, ite_false, hvb, ite_false] at hw hwb
        exact hab w hw hwb


theorem Invoke.forest {c : FPCtx G s} (hout : OutOK c) (hsort : OutSorted c)
    {S : Finset (Fin G.n)} {d0 : Labels G s} (hpre : CallPre c.B S d0)
    {ι ι' : IState G s} {L : List (Fin G.n)} {n : ℕ} (h : Invoke c ι L ι' n)
    (hLS : ∀ x ∈ L, x ∈ S) (hw : WalkInv ι.d) (hle : ∀ v, ι.d v ≤ d0 v) (hF : FInv c ι) :
    FInv c ι' := by
  induction h with
  | nil ι => exact hF
  | skip ι ι' x L n _ _ ih => exact ih (fun y hy => hLS y (List.mem_cons_of_mem _ hy)) hw hle hF
  | fail ι ι' x L σ' n n' hx hs _ ih =>
    have hxS : x ∈ S := hLS x List.mem_cons_self
    have hxtop : ι.d x ≠ ⊤ := ne_top_of_lt (lt_of_le_of_lt (hle x) (hpre.inRange x hxS))
    have hS0 : SInv c (initSt ι.d ι.D x) := initSt_inv hw hxtop
    obtain ⟨hIs, hle', -, -, -⟩ :=
      Search.inv hout hsort hs hS0 (fun w hw => absurd hw (Finset.notMem_empty w))
    exact ih (fun y hy => hLS y (List.mem_cons_of_mem _ hy)) hIs.walk
      (fun v => (hle' v).trans (hle v)) ⟨hF.pf, hF.size, hF.tv, hF.disj⟩
  | grow ι ι' x L σ' res n n' hx hres hs _ ih =>
    have hxS : x ∈ S := hLS x List.mem_cons_self
    have hxtop : ι.d x ≠ ⊤ := ne_top_of_lt (lt_of_le_of_lt (hle x) (hpre.inRange x hxS))
    have hS0 : SInv c (initSt ι.d ι.D x) := initSt_inv hw hxtop
    obtain ⟨hIs, hle', -, -, -⟩ :=
      Search.inv hout hsort hs hS0 (fun w hw => absurd hw (Finset.notMem_empty w))
    exact ih (fun y hy => hLS y (List.mem_cons_of_mem _ hy)) hIs.walk
      (fun v => (hle' v).trans (hle v)) (growForest_inv hout hsort hx hres hs hS0 hF)

/-- The MakePivots output of the tree partition (agent-03's `makePivots` over
`forestPieces k trees`), as groups indexed by `Fin p`. -/
noncomputable def forestGroups (S Q : Finset (Fin G.n)) (k : ℕ)
    (trees : List (TreeRec (Fin G.n))) : List (List (Fin G.n)) :=
  makePivots S Q (forestPieces k trees)

/-- **MakePivots from the tree partition** meets `MakePivotsRel`, with the pivot-count bound
`p·(k−1) ≤ Σ (|T|−1)` and group sizes `< 3k` (agent-03's `forest_groups_spec`). -/
theorem forestGroups_rel {c : FPCtx G s} {ι : IState G s} (hF : FInv c ι) (hk : 2 ≤ c.k)
    (S : Finset (Fin G.n)) :
    MakePivotsRel S ι.Q ι.tv (forestGroups S ι.Q c.k ι.trees).length
      (fun j => ((forestGroups S ι.Q c.k ι.trees).get j).toFinset) ∧
    (∀ j, ((forestGroups S ι.Q c.k ι.trees).get j).length < 3 * c.k) ∧
    (forestGroups S ι.Q c.k ι.trees).length * (c.k - 1) ≤
      (ι.trees.map (fun T => T.ord.length - 1)).sum := by
  classical
  obtain ⟨h1, h2, h3, h4, h5⟩ := forest_groups_spec S ι.Q hk ι.trees hF.pf hF.size
  set gs := forestGroups S ι.Q c.k ι.trees with hgs
  refine ⟨⟨fun j => ?_, fun i j hij => ?_, fun j => ?_, fun x hxS hxQ hxt => ?_⟩,
    fun j => h4 _ (List.get_mem _ _), h5⟩
  · obtain ⟨hne, -, hsub⟩ := h1 _ (List.get_mem gs j)
    refine ⟨?_, fun y hy => (hsub y (List.mem_toFinset.mp hy)).1⟩
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hne
    exact ⟨y, List.mem_toFinset.mpr hy⟩
  · rw [Finset.disjoint_left]
    intro y hyi hyj
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact List.pairwise_iff_get.mp h2 i j hlt y (List.mem_toFinset.mp hyi)
        (List.mem_toFinset.mp hyj)
    · exact List.pairwise_iff_get.mp h2 j i hlt y (List.mem_toFinset.mp hyj)
        (List.mem_toFinset.mp hyi)
  · rw [Finset.disjoint_left]
    intro y hyQ hyj
    exact (h1 _ (List.get_mem gs j)).2.2 y (List.mem_toFinset.mp hyj) |>.2 hyQ
  · obtain ⟨Tr, hTr, hxTr⟩ := (hF.tv x).mp hxt
    obtain ⟨g, hg, hxg⟩ := h3 Tr hTr x hxTr hxS hxQ
    obtain ⟨j, rfl⟩ := List.get_of_mem hg
    exact ⟨j, List.mem_toFinset.mpr hxg⟩


/-- The tree-vertex set has exactly `Σ |T|` elements (the trees are disjoint parent-first lists). -/
theorem FInv.card_tv {c : FPCtx G s} {ι : IState G s} (hF : FInv c ι) :
    ι.tv.card = (ι.trees.map (fun T => T.ord.length)).sum := by
  classical
  have hnd : (ι.trees.flatMap (fun T => T.ord)).Nodup := by
    rw [List.nodup_flatMap]
    exact ⟨fun T hT => (hF.pf T hT).1, hF.disj.imp (fun h a ha hb => h a ha hb)⟩
  have heq : ι.tv = (ι.trees.flatMap (fun T => T.ord)).toFinset := by
    ext v
    rw [hF.tv v, List.mem_toFinset, List.mem_flatMap]
  rw [heq, List.toFinset_card_of_nodup hnd, List.length_flatMap]

/-- **FindPivots-HD with the tree-partition MakePivots**: the full contract, `Dinv`, group sizes
`< 3k`, and the pivot-count bound `p·(k−1) ≤ |tree vertices|` (the input of T-PIV). -/
theorem findPivots_contract_forest {c : FPCtx G s} (hout : OutOK c) (hsort : OutSorted c)
    (hk : 2 ≤ c.k) {S : Finset (Fin G.n)} {SL : List (Fin G.n)} (hSL : ∀ x, x ∈ SL ↔ x ∈ S)
    {d0 : Labels G s} (hpre : CallPre c.B S d0) (hLxS : ∀ x ∈ S, c.Lx ≤ d0 x)
    {D0 : Finset (Fin G.m)} (hD0 : ∀ e ∈ D0, dis (s := s) (G.dst e) < dis (s := s) (G.src e))
    {ι' : IState G s} {n : ℕ} (hrun : Invoke c ⟨d0, D0, ∅, ∅, ∅, []⟩ SL ι' n) :
    FPContract c.B S d0 ι'.d (forestGroups S ι'.Q c.k ι'.trees).length
        (fun j => ((forestGroups S ι'.Q c.k ι'.trees).get j).toFinset) ι'.Q ι'.W ∧
      (∀ e ∈ ι'.D, dis (s := s) (G.dst e) < dis (s := s) (G.src e)) ∧
      (∀ j, ((forestGroups S ι'.Q c.k ι'.trees).get j).length < 3 * c.k) ∧
      (forestGroups S ι'.Q c.k ι'.trees).length * (c.k - 1) ≤ ι'.tv.card := by
  have hF0 : FInv c (⟨d0, D0, ∅, ∅, ∅, []⟩ : IState G s) :=
    ⟨fun T hT => absurd hT List.not_mem_nil, fun T hT => absurd hT List.not_mem_nil,
      fun v => by simp, List.Pairwise.nil⟩
  have hF := Invoke.forest hout hsort hpre hrun (fun x hx => (hSL x).mp hx) hpre.walk
    (fun _ => le_rfl) hF0
  obtain ⟨hmp, hsz, hcnt⟩ := forestGroups_rel hF hk S
  obtain ⟨hcon, hdinv⟩ := findPivots_contract hout hsort hSL hpre hLxS hD0 hrun hmp
  refine ⟨hcon, hdinv, hsz, hcnt.trans ?_⟩
  rw [hF.card_tv]
  exact List.sum_le_sum (fun T _ => Nat.sub_le _ _)


/-- HD1, member-sensitive form: a search from its root costs at most `scanC` per new deletion
plus `(scanC + hins + extC k)` per final member, plus 1. -/
theorem search_cost_members {c : FPCtx G s} (hout : OutOK c) (hsort : OutSorted c)
    (hsimp : Simple c) (hk : 1 ≤ c.k) {T : Finset (Fin G.n)} {d : Labels G s}
    {D : Finset (Fin G.m)} {x : Fin G.n} {σ' : SSt G s} {res : SearchRes} {n : ℕ}
    (h : Search c T (initSt d D x) σ' res n) (hS0 : SInv c (initSt d D x)) :
    n + scanC * D.card ≤ scanC * σ'.D.card + σ'.K.length * (scanC + c.hins + extC c c.k) + 1 := by
  have hc := Search.cost hout hsort hsimp h hS0
  have hdone0 : (initSt d D x).done.card = 0 := by simp [initSt]
  rw [hdone0, Nat.mul_zero, Nat.add_zero] at hc
  obtain ⟨hdv, hK⟩ := Search.done_val_K hout hsort h hS0 (by simp [initSt])
    (by simp [initSt]; omega)
  obtain ⟨hIs, -⟩ := Search.inv hout hsort h hS0 (fun w hw => by simp [initSt] at hw)
  have hdK : σ'.done.card ≤ σ'.K.length :=
    calc σ'.done.card ≤ σ'.val.card := Finset.card_le_card hdv
      _ ≤ σ'.K.toFinset.card := Finset.card_le_card (fun v hv => List.mem_toFinset.mpr (hIs.valK v hv))
      _ ≤ σ'.K.length := List.toFinset_card_le _
  have hext : extC c σ'.K.length ≤ extC c c.k := by
    unfold extC
    have := Nat.mul_le_mul_left (scanC + c.hins) (Nat.add_le_add_left hK 1)
    omega
  have h2 : extC c σ'.K.length * σ'.done.card ≤ extC c c.k * σ'.K.length :=
    Nat.mul_le_mul hext hdK
  have hpot0 : pot c (initSt d D x) = scanC * D.card + (scanC + c.hins) * 1 := by
    simp [pot, initSt]
  have hpot' : pot c σ' = scanC * σ'.D.card + (scanC + c.hins) * σ'.K.length := rfl
  rw [hpot0, hpot'] at hc
  nlinarith [hc, h2]

/-- **T-FP (paper §5.1): cost of one FindPivots-HD invocation.**  With
`A := scanC + hins + extC k + 1` (`O(k)` for the array heap), processing a duplicate-free root
list costs at most `scanC` per new deletion, `A` per new tree vertex, `A·k` per new failed root,
and `3` per root. -/
theorem Invoke.cost {c : FPCtx G s} (hout : OutOK c) (hsort : OutSorted c) (hsimp : Simple c)
    (hk : 1 ≤ c.k) {S : Finset (Fin G.n)} {d0 : Labels G s} (hpre : CallPre c.B S d0)
    {ι ι' : IState G s} {L : List (Fin G.n)} {n : ℕ} (h : Invoke c ι L ι' n)
    (hLS : ∀ x ∈ L, x ∈ S) (hnd : L.Nodup) (hLQ : ∀ x ∈ L, x ∉ ι.Q) (hw : WalkInv ι.d)
    (hle : ∀ v, ι.d v ≤ d0 v) :
    n + scanC * ι.D.card + (scanC + c.hins + extC c c.k + 1) * (ι.tv.card + c.k * ι.Q.card) ≤
      scanC * ι'.D.card + (scanC + c.hins + extC c c.k + 1) * (ι'.tv.card + c.k * ι'.Q.card) +
        3 * L.length := by
  induction h with
  | nil ι => simp
  | skip ι ι' x L n _ _ ih =>
    have := ih (fun y hy => hLS y (List.mem_cons_of_mem _ hy)) (List.nodup_cons.mp hnd).2
      (fun y hy => hLQ y (List.mem_cons_of_mem _ hy)) hw hle
    simp only [List.length_cons]; omega
  | fail ι ι' x L σ' n n' hx hs _ ih =>
    have hxS : x ∈ S := hLS x List.mem_cons_self
    have hxtop : ι.d x ≠ ⊤ := ne_top_of_lt (lt_of_le_of_lt (hle x) (hpre.inRange x hxS))
    have hS0 : SInv c (initSt ι.d ι.D x) := initSt_inv hw hxtop
    obtain ⟨hIs, hle', -, -, -⟩ :=
      Search.inv hout hsort hs hS0 (fun w hw => absurd hw (Finset.notMem_empty w))
    have hsc := search_cost_members hout hsort hsimp hk hs hS0
    obtain ⟨-, hK⟩ := Search.done_val_K hout hsort hs hS0 (by simp [initSt])
      (by simp [initSt]; omega)
    have hxQ : x ∉ ι.Q := hLQ x List.mem_cons_self
    have hQc : (insert x ι.Q).card = ι.Q.card + 1 := Finset.card_insert_of_notMem hxQ
    have hnd' := List.nodup_cons.mp hnd
    have ih' := ih (fun y hy => hLS y (List.mem_cons_of_mem _ hy)) hnd'.2
      (fun y hy => by
        simp only [Finset.mem_insert, not_or]
        exact ⟨fun h => hnd'.1 (h ▸ hy), hLQ y (List.mem_cons_of_mem _ hy)⟩)
      hIs.walk (fun v => (hle' v).trans (hle v))
    simp only at ih'
    rw [hQc] at ih'
    simp only [List.length_cons]
    have hKk : σ'.K.length * (scanC + c.hins + extC c c.k) ≤
        c.k * (scanC + c.hins + extC c c.k) := Nat.mul_le_mul_right _ hK
    nlinarith [hsc, ih', hKk]
  | grow ι ι' x L σ' res n n' hx hres hs _ ih =>
    have hxS : x ∈ S := hLS x List.mem_cons_self
    have hxtop : ι.d x ≠ ⊤ := ne_top_of_lt (lt_of_le_of_lt (hle x) (hpre.inRange x hxS))
    have hS0 : SInv c (initSt ι.d ι.D x) := initSt_inv hw hxtop
    obtain ⟨hIs, hle', -, -, -⟩ :=
      Search.inv hout hsort hs hS0 (fun w hw => absurd hw (Finset.notMem_empty w))
    have hsc := search_cost_members hout hsort hsimp hk hs hS0
    have hTI : TreeInv c ι.tv x σ' := Search.treeInv hout hsort hs hS0 (treeInv_initSt hx)
    have htvc : (ι.tv ∪ σ'.K.toFinset).card = ι.tv.card + σ'.K.length := by
      rw [Finset.card_union_of_disjoint (Finset.disjoint_right.mpr
        (fun v hv => hTI.disj v (List.mem_toFinset.mp hv))),
        List.toFinset_card_of_nodup hTI.pf.1]
    have hnd' := List.nodup_cons.mp hnd
    have ih' := ih (fun y hy => hLS y (List.mem_cons_of_mem _ hy)) hnd'.2
      (fun y hy => hLQ y (List.mem_cons_of_mem _ hy)) hIs.walk (fun v => (hle' v).trans (hle v))
    simp only at ih'
    rw [htvc] at ih'
    simp only [List.length_cons]
    nlinarith [hsc, ih']


/-! ## Deletions only grow -/

theorem addNew_D (σ : SSt G s) (u : Fin G.n) (e : Fin G.m) : (addNew σ u e).D = σ.D := by
  unfold addNew; split_ifs <;> rfl

theorem improve_D (σ : SSt G s) (u : Fin G.n) (e : Fin G.m) : (improve σ u e).D = σ.D := by
  unfold improve; split_ifs <;> rfl

theorem Scan.D_mono {c : FPCtx G s} {T : Finset (Fin G.n)} {u : Fin G.n} {σ σ' : SSt G s}
    {L : List (Fin G.m)} {r : ScanRes} {n : ℕ} (h : Scan c T u σ L σ' r n) : σ.D ⊆ σ'.D := by
  induction h with
  | nil => exact subset_rfl
  | del _ _ _ _ _ _ _ _ ih => exact ih
  | brk => exact subset_rfl
  | lxdel σ _ e _ _ _ _ _ _ _ ih => exact (Finset.subset_insert e σ.D).trans ih
  | contact => exact subset_rfl
  | newFull σ e => intro x hx; rwa [addNew_D]
  | newCont σ _ e _ _ _ _ _ _ _ _ _ _ ih => intro x hx; exact ih (by rwa [addNew_D])
  | inK σ _ e _ _ _ _ _ _ _ _ _ ih => intro x hx; exact ih (by rwa [improve_D])

theorem Search.D_mono {c : FPCtx G s} {T : Finset (Fin G.n)} {σ σ' : SSt G s} {r : SearchRes}
    {n : ℕ} (h : Search c T σ σ' r n) : σ.D ⊆ σ'.D := by
  induction h with
  | empty => exact subset_rfl
  | capped => exact subset_rfl
  | stepCont _ _ _ _ _ _ _ _ _ _ hs _ ih => exact hs.D_mono.trans ih
  | stepContact _ _ _ _ _ _ _ hs => exact hs.D_mono
  | stepFull _ _ _ _ _ _ _ hs => exact hs.D_mono

theorem Invoke.D_mono {c : FPCtx G s} {ι ι' : IState G s} {L : List (Fin G.n)} {n : ℕ}
    (h : Invoke c ι L ι' n) : ι.D ⊆ ι'.D := by
  induction h with
  | nil => exact subset_rfl
  | skip _ _ _ _ _ _ _ ih => exact ih
  | fail _ _ _ _ _ _ _ _ hs _ ih => exact hs.D_mono.trans ih
  | grow _ _ _ _ _ _ _ _ _ _ hs _ ih => exact hs.D_mono.trans ih

/-! ## The pinned, cost-indexed FindPivots-HD relation (obligation O21) -/

/-- `L_X = d_B[S] = min({B} ∪ {d x : x ∈ S})` (FH.1). -/
noncomputable def lxOf (B : WLab G s) (S : Finset (Fin G.n)) (d : Labels G s) : WLab G s :=
  B ⊓ S.inf d

theorem lxOf_le {B : WLab G s} {S : Finset (Fin G.n)} {d : Labels G s} {x : Fin G.n}
    (hx : x ∈ S) : lxOf B S d ≤ d x :=
  inf_le_right.trans (Finset.inf_le hx)

/-- The context of one invocation with PINNED parameters: bound `B`, deletion threshold `Lx`,
the global cap `k`, the fixed out-lists and the heap costs. -/
def pinCtx (out : Fin G.n → List (Fin G.m)) (k hins hext : ℕ) (B Lx : WLab G s) : FPCtx G s :=
  { B := B, Lx := Lx, k := k, out := out, hins := hins, hext := hext }

/-- The per-unit charge of the invocation cost bound: `A = scanC + hins + extC k + 1 = O(k)`
(with `hins = O(1)`, `hext = O(k)` for the unsorted-array heap). -/
def fpA (k hins hext : ℕ) : ℕ := scanC + hins + ((scanC + hins) * (1 + k) + hext + 1) + 1

/-- **FindPivots-HD, cost-indexed, with explicit deletion threshold `Lx`**: from labels `d0`
and input deletions `Din`, some duplicate-free enumeration of `S` is processed by the invocation
loop with context `pinCtx out k hins hext B Lx`, ending in labels `d1`, deletions `Dout`, failed
roots `Q`, region `W`, forest `trees`, at cost `cost`. -/
def FindPivotsCL (out : Fin G.n → List (Fin G.m)) (k hins hext : ℕ) (Lx B : WLab G s)
    (S : Finset (Fin G.n)) (d0 : Labels G s) (Din : Finset (Fin G.m)) (d1 : Labels G s)
    (Dout : Finset (Fin G.m)) (Q W : Finset (Fin G.n)) (trees : List (TreeRec (Fin G.n)))
    (cost : ℕ) : Prop :=
  ∃ (SL : List (Fin G.n)) (ι' : IState G s), SL.Nodup ∧ (∀ x, x ∈ SL ↔ x ∈ S) ∧
    Invoke (pinCtx out k hins hext B Lx) ⟨d0, Din, ∅, ∅, ∅, []⟩ SL ι' cost ∧
    d1 = ι'.d ∧ Dout = ι'.D ∧ Q = ι'.Q ∧ W = ι'.W ∧ trees = ι'.trees ∧ S.card = SL.length

/-- **FindPivots-HD, pinned** (agent-07's O21): `Lx = d_B[S]` of the call. -/
def FindPivotsC (out : Fin G.n → List (Fin G.m)) (k hins hext : ℕ) (B : WLab G s)
    (S : Finset (Fin G.n)) (d0 : Labels G s) (Din : Finset (Fin G.m)) (d1 : Labels G s)
    (Dout : Finset (Fin G.m)) (Q W : Finset (Fin G.n)) (trees : List (TreeRec (Fin G.n)))
    (cost : ℕ) : Prop :=
  FindPivotsCL out k hins hext (lxOf B S d0) B S d0 Din d1 Dout Q W trees cost

/-- **Soundness, deletions, pivot bound and cost** of the cost-indexed relation, for any
threshold `Lx` below the labels of `S`. -/
theorem findPivotsCL_spec {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}
    (hout : ∀ u e, e ∈ out u ↔ G.src e = u) (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (hsimp : ∀ u, ((out u).map G.dst).Nodup) (hk : 2 ≤ k) {Lx B : WLab G s}
    {S : Finset (Fin G.n)} {d0 : Labels G s} {Din : Finset (Fin G.m)}
    (hpre : CallPre B S d0) (hLxS : ∀ x ∈ S, Lx ≤ d0 x)
    (hDin : ∀ e ∈ Din, dis (s := s) (G.dst e) < dis (s := s) (G.src e))
    {d1 : Labels G s} {Dout : Finset (Fin G.m)} {Q W : Finset (Fin G.n)}
    {trees : List (TreeRec (Fin G.n))} {cost : ℕ}
    (h : FindPivotsCL out k hins hext Lx B S d0 Din d1 Dout Q W trees cost) :
    FPContract B S d0 d1 (forestGroups S Q k trees).length
        (fun j => ((forestGroups S Q k trees).get j).toFinset) Q W ∧
      (∀ e ∈ Dout, dis (s := s) (G.dst e) < dis (s := s) (G.src e)) ∧
      Din ⊆ Dout ∧
      (∀ j, ((forestGroups S Q k trees).get j).length < 3 * k) ∧
      (forestGroups S Q k trees).length * (k - 1) ≤
        (trees.flatMap (fun T => T.ord)).length ∧
      cost + scanC * Din.card ≤
        scanC * Dout.card + fpA k hins hext * ((trees.flatMap (fun T => T.ord)).length +
          k * Q.card) + 3 * S.card := by
  obtain ⟨SL, ι', hnd, hSL, hrun, rfl, rfl, rfl, rfl, rfl, hcard⟩ := h
  set c := pinCtx out k hins hext B Lx with hc
  have hout' : OutOK c := hout
  have hsort' : OutSorted c := hsort
  have hsimp' : Simple c := hsimp
  have hpre' : CallPre c.B S d0 := hpre
  obtain ⟨hcon, hdinv, hsz, hcnt⟩ :=
    findPivots_contract_forest hout' hsort' hk hSL hpre' hLxS hDin hrun
  have hF0 : FInv c (⟨d0, Din, ∅, ∅, ∅, []⟩ : IState G s) :=
    ⟨fun T hT => absurd hT List.not_mem_nil, fun T hT => absurd hT List.not_mem_nil,
      fun v => by simp, List.Pairwise.nil⟩
  have hF := Invoke.forest hout' hsort' hpre' hrun (fun x hx => (hSL x).mp hx) hpre.walk
    (fun _ => le_rfl) hF0
  have htv : ι'.tv.card = (ι'.trees.flatMap (fun T => T.ord)).length := by
    rw [hF.card_tv, List.length_flatMap]
  have hcost := Invoke.cost hout' hsort' hsimp' (by show 1 ≤ k; omega) hpre' hrun
    (fun x hx => (hSL x).mp hx) hnd (fun x _ => Finset.notMem_empty x) hpre.walk (fun _ => le_rfl)
  refine ⟨hcon, hdinv, Invoke.D_mono hrun, hsz, htv ▸ hcnt, ?_⟩
  simp only [Finset.card_empty, Nat.mul_zero, Nat.add_zero] at hcost
  rw [htv, ← hcard] at hcost
  exact hcost

/-- The same for the pinned threshold `Lx = d_B[S]`. -/
theorem findPivotsC_spec {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}
    (hout : ∀ u e, e ∈ out u ↔ G.src e = u) (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (hsimp : ∀ u, ((out u).map G.dst).Nodup) (hk : 2 ≤ k) {B : WLab G s}
    {S : Finset (Fin G.n)} {d0 : Labels G s} {Din : Finset (Fin G.m)}
    (hpre : CallPre B S d0) (hDin : ∀ e ∈ Din, dis (s := s) (G.dst e) < dis (s := s) (G.src e))
    {d1 : Labels G s} {Dout : Finset (Fin G.m)} {Q W : Finset (Fin G.n)}
    {trees : List (TreeRec (Fin G.n))} {cost : ℕ}
    (h : FindPivotsC out k hins hext B S d0 Din d1 Dout Q W trees cost) :
    FPContract B S d0 d1 (forestGroups S Q k trees).length
        (fun j => ((forestGroups S Q k trees).get j).toFinset) Q W ∧
      (∀ e ∈ Dout, dis (s := s) (G.dst e) < dis (s := s) (G.src e)) ∧
      Din ⊆ Dout ∧
      (∀ j, ((forestGroups S Q k trees).get j).length < 3 * k) ∧
      (forestGroups S Q k trees).length * (k - 1) ≤
        (trees.flatMap (fun T => T.ord)).length ∧
      cost + scanC * Din.card ≤
        scanC * Dout.card + fpA k hins hext * ((trees.flatMap (fun T => T.ord)).length +
          k * Q.card) + 3 * S.card :=
  findPivotsCL_spec hout hsort hsimp hk hpre (fun _ hx => lxOf_le hx) hDin h

/-- **Totality** of the cost-indexed relation (agent-08's R4 / O14 for FindPivots): every call
satisfying `CallPre` has a run, for every threshold, input deletion set and parameters. -/
theorem findPivotsCL_total {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}
    (hout : ∀ u e, e ∈ out u ↔ G.src e = u) (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (Lx : WLab G s) {B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s}
    (Din : Finset (Fin G.m)) (hpre : CallPre B S d0) :
    ∃ d1 Dout Q W trees cost, FindPivotsCL out k hins hext Lx B S d0 Din d1 Dout Q W trees cost := by
  classical
  set c := pinCtx out k hins hext B Lx
  have hout' : OutOK c := hout
  have hsort' : OutSorted c := hsort
  obtain ⟨ι', n, hrun⟩ := Invoke.exists_run hout' hsort' (S := S) (d0 := d0) hpre S.toList
    ⟨d0, Din, ∅, ∅, ∅, []⟩ (fun x hx => Finset.mem_toList.mp hx) hpre.walk (fun _ => le_rfl)
  exact ⟨ι'.d, ι'.D, ι'.Q, ι'.W, ι'.trees, n, S.toList, ι', Finset.nodup_toList S,
    fun x => Finset.mem_toList, hrun, rfl, rfl, rfl, rfl, rfl, (Finset.length_toList S).symm⟩

theorem findPivotsC_total {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}
    (hout : ∀ u e, e ∈ out u ↔ G.src e = u) (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    {B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} (Din : Finset (Fin G.m))
    (hpre : CallPre B S d0) :
    ∃ d1 Dout Q W trees cost, FindPivotsC out k hins hext B S d0 Din d1 Dout Q W trees cost :=
  findPivotsCL_total hout hsort _ Din hpre

/-! ## Lemma F2: foreign tree vertices (PAPER_CHD Lemma F2; tracker O3)

A tree vertex outside `Ũ(B, S)` (a FOREIGN leaf) is complete before and after the invocation, and
its canonical label lies in `[L_X, B)`.  The proof needs only the search invariant `KI`:
labels are walks below `d0`, and every member is in `Ũ(B, S)` or has its canonical label in
`[L_X, B)` (a label-independent fact, hence stable under later relaxations). -/

/-- The per-member fact of Lemma F2. -/
def F2Fact (c : FPCtx G s) (S : Finset (Fin G.n)) (v : Fin G.n) : Prop :=
  v ∈ Utilde c.B (S : Set (Fin G.n)) ∨ (c.Lx ≤ dis (s := s) v ∧ dis (s := s) v < c.B)

/-- The search-state invariant of Lemma F2. -/
structure KI (c : FPCtx G s) (S : Finset (Fin G.n)) (d0 : Labels G s) (σ : SSt G s) : Prop where
  walk : WalkInv σ.d
  le : ∀ v, σ.d v ≤ d0 v
  mem : ∀ v ∈ σ.K, F2Fact c S v

theorem addNew_d (σ : SSt G s) (u : Fin G.n) (e : Fin G.m) :
    (addNew σ u e).d = relaxL σ.d u e := by
  unfold addNew; split_ifs with h
  · rfl
  · exact (relaxL_of_not_ok h).symm

theorem addNew_K (σ : SSt G s) (u : Fin G.n) (e : Fin G.m) :
    (addNew σ u e).K = σ.K ++ [G.dst e] := by
  unfold addNew; split_ifs <;> rfl

theorem improve_d (σ : SSt G s) (u : Fin G.n) (e : Fin G.m) :
    (improve σ u e).d = relaxL σ.d u e := by
  unfold improve; split_ifs with h
  · rfl
  · exact (relaxL_of_not_ok h).symm

theorem improve_K (σ : SSt G s) (u : Fin G.n) (e : Fin G.m) : (improve σ u e).K = σ.K := by
  unfold improve; split_ifs <;> rfl

section F2

variable {c : FPCtx G s} {S : Finset (Fin G.n)} {d0 : Labels G s}

/-- The key step: the target of a scanned, undeleted (`¬ d v < L_X`), in-range edge satisfies the
F2 fact — if it is outside `Ũ(B, S)`, `claimC` makes it complete, so its label is canonical. -/
theorem f2_target (hpre : CallPre c.B S d0) {σ : SSt G s} (hI : KI c S d0 σ) {u : Fin G.n}
    {e : Fin G.m} (he : G.src e = u) (hB : ext (σ.d u) e < c.B)
    (hLx : ¬ σ.d (G.dst e) < c.Lx) : F2Fact c S (G.dst e) := by
  have hdis : dis (s := s) (G.dst e) < c.B := by
    by_cases hok : Ok σ.d u e
    · have h1 := (hI.walk.relaxL he).sound (G.dst e)
      rw [relaxL_apply_self hok] at h1
      exact lt_of_le_of_lt h1 hB
    · have hlt : σ.d (G.dst e) < ext (σ.d u) e := not_le.mp hok
      exact lt_of_le_of_lt (hI.walk.sound _) (hlt.trans hB)
  by_cases hU : G.dst e ∈ Utilde c.B (S : Set (Fin G.n))
  · exact Or.inl hU
  · refine Or.inr ⟨?_, hdis⟩
    have hc : d0 (G.dst e) = dis (s := s) (G.dst e) := hpre.claimC _ hdis hU
    have heq : σ.d (G.dst e) = dis (s := s) (G.dst e) :=
      le_antisymm ((hI.le _).trans hc.le) (hI.walk.sound _)
    rw [← heq]; exact not_lt.mp hLx

theorem KI.relax {σ : SSt G s} (hI : KI c S d0 σ) {u : Fin G.n} {e : Fin G.m}
    (he : G.src e = u) : WalkInv (relaxL σ.d u e) ∧ ∀ v, relaxL σ.d u e v ≤ d0 v :=
  ⟨hI.walk.relaxL he, fun v => (relaxL_le σ.d u e v).trans (hI.le v)⟩

theorem KI.addNew (hpre : CallPre c.B S d0) {σ : SSt G s} (hI : KI c S d0 σ) {u : Fin G.n}
    {e : Fin G.m} (he : G.src e = u) (hB : ext (σ.d u) e < c.B)
    (hLx : ¬ σ.d (G.dst e) < c.Lx) : KI c S d0 (addNew σ u e) := by
  obtain ⟨hw, hle⟩ := hI.relax he
  refine ⟨by rw [addNew_d]; exact hw, by rw [addNew_d]; exact hle, ?_⟩
  rw [addNew_K]
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact hI.mem v hv
  · rw [List.mem_singleton.mp hv]; exact f2_target hpre hI he hB hLx

theorem Scan.kinv (hpre : CallPre c.B S d0) {T : Finset (Fin G.n)} {u : Fin G.n}
    {σ σ' : SSt G s} {L : List (Fin G.m)} {r : ScanRes} {n : ℕ} (h : Scan c T u σ L σ' r n)
    (hL : ∀ e ∈ L, G.src e = u) (hI : KI c S d0 σ) : KI c S d0 σ' := by
  induction h with
  | nil => exact hI
  | del σ σ' e L r n _ _ ih => exact ih (fun e' he' => hL e' (List.mem_cons_of_mem _ he')) hI
  | brk => exact hI
  | lxdel σ σ' e L r n _ _ _ _ ih =>
    exact ih (fun e' he' => hL e' (List.mem_cons_of_mem _ he')) ⟨hI.walk, hI.le, hI.mem⟩
  | contact σ e L _ _ _ _ =>
    obtain ⟨hw, hle⟩ := hI.relax (hL e List.mem_cons_self)
    exact ⟨hw, hle, hI.mem⟩
  | newFull σ e L _ hB hLx _ _ _ => exact hI.addNew hpre (hL e List.mem_cons_self) hB hLx
  | newCont σ σ' e L r n _ hB hLx _ _ _ _ ih =>
    exact ih (fun e' he' => hL e' (List.mem_cons_of_mem _ he'))
      (hI.addNew hpre (hL e List.mem_cons_self) hB hLx)
  | inK σ σ' e L r n _ _ _ _ _ _ ih =>
    obtain ⟨hw, hle⟩ := hI.relax (hL e List.mem_cons_self)
    exact ih (fun e' he' => hL e' (List.mem_cons_of_mem _ he'))
      ⟨by rw [improve_d]; exact hw, by rw [improve_d]; exact hle, by rw [improve_K]; exact hI.mem⟩

theorem Search.kinv (hout : OutOK c) (hpre : CallPre c.B S d0) {T : Finset (Fin G.n)}
    {σ σ' : SSt G s} {res : SearchRes} {n : ℕ} (h : Search c T σ σ' res n)
    (hI : KI c S d0 σ) : KI c S d0 σ' := by
  induction h with
  | empty => exact hI
  | capped => exact hI
  | stepCont σ σ' σ'' u res n n' _ _ _ hs _ ih =>
    exact ih (hs.kinv hpre (fun e he => (hout u e).mp he) ⟨hI.walk, hI.le, hI.mem⟩)
  | stepContact σ σ' u n _ _ _ hs =>
    exact hs.kinv hpre (fun e he => (hout u e).mp he) ⟨hI.walk, hI.le, hI.mem⟩
  | stepFull σ σ' u n _ _ _ hs =>
    exact hs.kinv hpre (fun e he => (hout u e).mp he) ⟨hI.walk, hI.le, hI.mem⟩

theorem f2_init (hpre : CallPre c.B S d0) {d : Labels G s} {D : Finset (Fin G.m)} {x : Fin G.n}
    (hx : x ∈ S) (hw : WalkInv d) (hle : ∀ v, d v ≤ d0 v) : KI c S d0 (initSt d D x) := by
  refine ⟨hw, hle, fun v hv => ?_⟩
  have hv : v = x := by simpa [initSt] using hv
  subst hv
  have hxB : d0 v < c.B := hpre.inRange v hx
  have hreach : G.Reachable s v := by
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hxB)
    exact ⟨q, hpre.walk v q hq.symm⟩
  exact Or.inl ⟨lt_of_le_of_lt (hpre.walk.sound v) hxB, v, hx, onPath_self hreach⟩

theorem Invoke.kinv (hout : OutOK c) (hpre : CallPre c.B S d0) {ι ι' : IState G s}
    {L : List (Fin G.n)} {n : ℕ} (h : Invoke c ι L ι' n) (hLS : ∀ x ∈ L, x ∈ S)
    (hw : WalkInv ι.d) (hle : ∀ v, ι.d v ≤ d0 v) (htv : ∀ v ∈ ι.tv, F2Fact c S v) :
    WalkInv ι'.d ∧ (∀ v, ι'.d v ≤ d0 v) ∧ ∀ v ∈ ι'.tv, F2Fact c S v := by
  induction h with
  | nil => exact ⟨hw, hle, htv⟩
  | skip ι ι' x L n _ _ ih =>
    exact ih (fun y hy => hLS y (List.mem_cons_of_mem _ hy)) hw hle htv
  | fail ι ι' x L σ' n n' _ hs _ ih =>
    have hk := hs.kinv hout hpre (f2_init hpre (hLS x List.mem_cons_self) hw hle)
    exact ih (fun y hy => hLS y (List.mem_cons_of_mem _ hy)) hk.walk hk.le htv
  | grow ι ι' x L σ' res n n' _ _ hs _ ih =>
    have hk := hs.kinv hout hpre (f2_init hpre (hLS x List.mem_cons_self) hw hle)
    refine ih (fun y hy => hLS y (List.mem_cons_of_mem _ hy)) hk.walk hk.le ?_
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact htv v hv
    · exact hk.mem v (List.mem_toFinset.mp hv)

end F2

/-- `L_X = d_B[S]` dominates every common lower bound of `B` and the labels of `S` (so
`B_low ≤ L_X`, the other half of tracker O3). -/
theorem le_lxOf {Blow B : WLab G s} {S : Finset (Fin G.n)} {d : Labels G s} (hB : Blow ≤ B)
    (hS : ∀ x ∈ S, Blow ≤ d x) : Blow ≤ lxOf B S d :=
  le_inf hB (Finset.le_inf hS)

/-- **Lemma F2** (PAPER_CHD; tracker O3) for the cost-indexed relation: every tree vertex outside
`Ũ(B, S)` (a foreign leaf) is complete both before and after the invocation, and its canonical
label lies in `[L_X, B)`. -/
theorem findPivotsCL_foreign {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}
    (hout : ∀ u e, e ∈ out u ↔ G.src e = u) (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    {Lx B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} {Din : Finset (Fin G.m)}
    {d1 : Labels G s} {Dout : Finset (Fin G.m)} {Q W : Finset (Fin G.n)}
    {trees : List (TreeRec (Fin G.n))} {cost : ℕ} (hpre : CallPre B S d0)
    (h : FindPivotsCL out k hins hext Lx B S d0 Din d1 Dout Q W trees cost) :
    ∀ T ∈ trees, ∀ v ∈ T.ord, v ∉ Utilde B (S : Set (Fin G.n)) →
      Lx ≤ dis (s := s) v ∧ dis (s := s) v < B ∧ Complete d0 v ∧ Complete d1 v := by
  obtain ⟨SL, ι', -, hSL, hrun, rfl, rfl, rfl, rfl, rfl, -⟩ := h
  set c := pinCtx out k hins hext B Lx
  have hout' : OutOK c := hout
  have hsort' : OutSorted c := hsort
  have hpre' : CallPre c.B S d0 := hpre
  have hF0 : FInv c (⟨d0, Din, ∅, ∅, ∅, []⟩ : IState G s) :=
    ⟨fun T hT => absurd hT List.not_mem_nil, fun T hT => absurd hT List.not_mem_nil,
      fun v => by simp, List.Pairwise.nil⟩
  have hF := Invoke.forest hout' hsort' hpre' hrun (fun x hx => (hSL x).mp hx) hpre.walk
    (fun _ => le_rfl) hF0
  obtain ⟨hw, hle, htv⟩ := Invoke.kinv hout' hpre' hrun (fun x hx => (hSL x).mp hx) hpre.walk
    (fun _ => le_rfl) (fun v hv => absurd hv (Finset.notMem_empty v))
  intro T hT v hv hU
  rcases htv v ((hF.tv v).mpr ⟨T, hT, hv⟩) with hU' | ⟨hLx, hB⟩
  · exact absurd hU' hU
  · have hc0 : Complete d0 v := hpre.claimC v hB hU
    exact ⟨hLx, hB, hc0, le_antisymm ((hle v).trans hc0.le) (hw.sound v)⟩

/-- Lemma F2 for the pinned relation (`L_X = d_B[S]`). -/
theorem findPivotsC_foreign {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}
    (hout : ∀ u e, e ∈ out u ↔ G.src e = u) (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    {B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} {Din : Finset (Fin G.m)}
    {d1 : Labels G s} {Dout : Finset (Fin G.m)} {Q W : Finset (Fin G.n)}
    {trees : List (TreeRec (Fin G.n))} {cost : ℕ} (hpre : CallPre B S d0)
    (h : FindPivotsC out k hins hext B S d0 Din d1 Dout Q W trees cost) :
    ∀ T ∈ trees, ∀ v ∈ T.ord, v ∉ Utilde B (S : Set (Fin G.n)) →
      lxOf B S d0 ≤ dis (s := s) v ∧ dis (s := s) v < B ∧ Complete d0 v ∧ Complete d1 v :=
  findPivotsCL_foreign hout hsort hpre h

/-! ## Tree-vertex count `#tv ≤ k·|S|` (for L5's `partial_Fo`) -/

/-- Every search ends with at most `k` members. -/
theorem Search.K_le {c : FPCtx G s} {T : Finset (Fin G.n)} {σ σ' : SSt G s} {res : SearchRes}
    {n : ℕ} (h : Search c T σ σ' res n) (hK : σ.K.length ≤ c.k) : σ'.K.length ≤ c.k := by
  induction h with
  | empty => exact hK
  | capped => exact hK
  | stepCont σ σ' σ'' u res n n' hlt _ _ hs _ ih => exact ih (hs.K_le hlt)
  | stepContact σ σ' u n hlt _ _ hs => exact hs.K_le hlt
  | stepFull σ σ' u n hlt _ _ hs => exact hs.K_le hlt

/-- Each processed root adds at most `k` tree vertices. -/
theorem Invoke.tv_card {c : FPCtx G s} {ι ι' : IState G s} {L : List (Fin G.n)} {n : ℕ}
    (h : Invoke c ι L ι' n) (hk : 1 ≤ c.k) : ι'.tv.card ≤ ι.tv.card + c.k * L.length := by
  classical
  induction h with
  | nil => simp
  | skip ι ι' x L n _ _ ih =>
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one]; omega
  | fail ι ι' x L σ' n n' _ _ _ ih =>
    dsimp only at ih
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one]; omega
  | grow ι ι' x L σ' res n n' _ _ hs _ ih =>
    dsimp only at ih
    have hK : σ'.K.length ≤ c.k := hs.K_le (by simpa [initSt] using hk)
    have hU : (ι.tv ∪ σ'.K.toFinset).card ≤ ι.tv.card + c.k :=
      (Finset.card_union_le _ _).trans (by have := List.toFinset_card_le σ'.K; omega)
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one]; omega

/-- **`#tv ≤ k·|S|`** for the cost-indexed relation (L5's `partial_Fo` input). -/
theorem findPivotsCL_tv_card {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}
    (hout : ∀ u e, e ∈ out u ↔ G.src e = u) (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (hk : 1 ≤ k) {Lx B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s}
    {Din : Finset (Fin G.m)} {d1 : Labels G s} {Dout : Finset (Fin G.m)} {Q W : Finset (Fin G.n)}
    {trees : List (TreeRec (Fin G.n))} {cost : ℕ} (hpre : CallPre B S d0)
    (h : FindPivotsCL out k hins hext Lx B S d0 Din d1 Dout Q W trees cost) :
    (trees.flatMap (fun T => T.ord)).length ≤ k * S.card := by
  obtain ⟨SL, ι', -, hSL, hrun, rfl, rfl, rfl, rfl, rfl, hcard⟩ := h
  set c := pinCtx out k hins hext B Lx
  have hout' : OutOK c := hout
  have hsort' : OutSorted c := hsort
  have hpre' : CallPre c.B S d0 := hpre
  have hF0 : FInv c (⟨d0, Din, ∅, ∅, ∅, []⟩ : IState G s) :=
    ⟨fun T hT => absurd hT List.not_mem_nil, fun T hT => absurd hT List.not_mem_nil,
      fun v => by simp, List.Pairwise.nil⟩
  have hF := Invoke.forest hout' hsort' hpre' hrun (fun x hx => (hSL x).mp hx) hpre.walk
    (fun _ => le_rfl) hF0
  have htv : ι'.tv.card = (ι'.trees.flatMap (fun T => T.ord)).length := by
    rw [hF.card_tv, List.length_flatMap]
  have h1 := Invoke.tv_card hrun (show 1 ≤ c.k from hk)
  simp only [Finset.card_empty, Nat.zero_add] at h1
  rw [← htv, hcard]
  exact h1

/-! ## Tree edges (for agent-03's O10 home charging)

Every non-root vertex `y` of a tree of the forest is joined to its parent by a real graph edge `e`
(`{src e, dst e} = {par y, y}`; the orientation flips on re-rooted contact paths), whose tail was
extracted by some search, hence lies in `Ũ(B, S)`. -/

/-- Parents of non-root members were extracted. -/
def TreeDone (x : Fin G.n) (σ : SSt G s) : Prop := ∀ v ∈ σ.K, v ≠ x → σ.kpar v ∈ σ.done

theorem addNew_done (σ : SSt G s) (u : Fin G.n) (e : Fin G.m) : (addNew σ u e).done = σ.done := by
  unfold addNew; split_ifs <;> rfl

theorem addNew_kpar (σ : SSt G s) (u : Fin G.n) (e : Fin G.m) :
    (addNew σ u e).kpar = Function.update σ.kpar (G.dst e) u := by
  unfold addNew; split_ifs <;> rfl

theorem improve_done (σ : SSt G s) (u : Fin G.n) (e : Fin G.m) : (improve σ u e).done = σ.done := by
  unfold improve; split_ifs <;> rfl

theorem improve_kpar (σ : SSt G s) (u : Fin G.n) (e : Fin G.m) : (improve σ u e).kpar = σ.kpar := by
  unfold improve; split_ifs <;> rfl

theorem treeDone_addNew {x u : Fin G.n} {σ : SSt G s} {e : Fin G.m} (h : TreeDone x σ)
    (hu : u ∈ σ.done) (hK : G.dst e ∉ σ.K) : TreeDone x (addNew σ u e) := by
  intro v hv hvx
  rw [addNew_K] at hv
  rw [addNew_kpar, addNew_done]
  rcases List.mem_append.mp hv with h1 | h1
  · have hne : v ≠ G.dst e := fun h => hK (h ▸ h1)
    rw [Function.update_of_ne hne]; exact h v h1 hvx
  · rw [List.mem_singleton.mp h1, Function.update_self]; exact hu

theorem treeDone_improve {x u : Fin G.n} {σ : SSt G s} {e : Fin G.m} (h : TreeDone x σ) :
    TreeDone x (improve σ u e) := by
  intro v hv hvx
  rw [improve_K] at hv
  rw [improve_kpar, improve_done]
  exact h v hv hvx

theorem Scan.treeDone {c : FPCtx G s} {T : Finset (Fin G.n)} {x u : Fin G.n} {σ σ' : SSt G s}
    {L : List (Fin G.m)} {r : ScanRes} {n : ℕ} (h : Scan c T u σ L σ' r n) (hu : u ∈ σ.done)
    (hTD : TreeDone x σ) : TreeDone x σ' := by
  induction h with
  | nil => exact hTD
  | del _ _ _ _ _ _ _ _ ih => exact ih hu hTD
  | brk => exact hTD
  | lxdel _ _ _ _ _ _ _ _ _ _ ih => exact ih hu hTD
  | contact => exact hTD
  | newFull σ e L _ _ _ _ hK _ => exact treeDone_addNew hTD hu hK
  | newCont σ σ' e L r n _ _ _ _ hK _ _ ih =>
    exact ih (by rw [addNew_done]; exact hu) (treeDone_addNew hTD hu hK)
  | inK σ σ' e L r n _ _ _ _ _ _ ih =>
    exact ih (by rw [improve_done]; exact hu) (treeDone_improve hTD)

theorem Search.treeDone {c : FPCtx G s} {T : Finset (Fin G.n)} {x : Fin G.n} {σ σ' : SSt G s}
    {res : SearchRes} {n : ℕ} (h : Search c T σ σ' res n) (hTD : TreeDone x σ) :
    TreeDone x σ' := by
  induction h with
  | empty => exact hTD
  | capped => exact hTD
  | stepCont σ σ1 σ'' u res n n' _ _ _ hscan _ ih =>
    exact ih (hscan.treeDone (Finset.mem_insert_self u σ.done)
      (fun v hv hvx => Finset.mem_insert_of_mem (hTD v hv hvx)))
  | stepContact σ σ1 u n _ _ _ hscan =>
    exact hscan.treeDone (Finset.mem_insert_self u σ.done)
      (fun v hv hvx => Finset.mem_insert_of_mem (hTD v hv hvx))
  | stepFull σ σ1 u n _ _ _ hscan =>
    exact hscan.treeDone (Finset.mem_insert_self u σ.done)
      (fun v hv hvx => Finset.mem_insert_of_mem (hTD v hv hvx))

theorem treeDone_initSt {d : Labels G s} {D : Finset (Fin G.m)} {x : Fin G.n} :
    TreeDone x (initSt d D x) := by
  intro v hv hvx
  simp only [initSt, List.mem_singleton] at hv
  exact absurd hv hvx

/-- A contact search ends with its contact vertex extracted and the contact edge scanned. -/
theorem Search.hit_done {c : FPCtx G s} {T : Finset (Fin G.n)} {σ σ' : SSt G s}
    {res : SearchRes} {n : ℕ} (h : Search c T σ σ' res n) (hr : res = .contact) :
    ∃ u e, σ'.hit = some (u, G.dst e) ∧ u ∈ σ'.done ∧ e ∈ c.out u ∧ G.dst e ∈ T := by
  induction h with
  | empty => exact absurd hr (by decide)
  | capped => exact absurd hr (by decide)
  | stepCont _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih hr
  | stepContact σ σ1 u n _ _ _ hscan =>
    obtain ⟨e, he, hhit, hT⟩ := Scan.contact_info hscan rfl
    refine ⟨u, e, hhit, ?_, he, hT⟩
    rw [Scan.done_eq hscan]
    exact Finset.mem_insert_self _ _
  | stepFull => exact absurd hr (by decide)

theorem kpath_ne_of_succ {α : Type*} [DecidableEq α] {kpar : α → α} {x : α} :
    ∀ (f : ℕ) (u : α) (pre post : List α) (a b : α),
      kpath kpar x f u = pre ++ a :: b :: post → a ≠ x
  | 0, u, pre, post, a, b, h => by
    simp only [kpath] at h
    rcases pre with _ | ⟨c, pre⟩ <;> simp at h
  | f + 1, u, pre, post, a, b, h => by
    simp only [kpath] at h
    by_cases hux : u = x
    · simp only [hux, ite_true] at h
      rcases pre with _ | ⟨c, pre⟩ <;> simp at h
    · simp only [hux, ite_false] at h
      rcases pre with _ | ⟨c, pre⟩
      · simp only [List.nil_append, List.cons.injEq] at h
        rw [← h.1]; exact hux
      · simp only [List.cons_append, List.cons.injEq] at h
        exact kpath_ne_of_succ f (kpar u) pre post a b h.2

/-- The tree-edge property of a forest. -/
def TEdge (B : WLab G s) (S : Finset (Fin G.n)) (trees : List (TreeRec (Fin G.n))) : Prop :=
  ∀ Tr ∈ trees, ∀ y ∈ Tr.ord, y ≠ Tr.root → ∃ e : Fin G.m,
    ((G.src e = Tr.par y ∧ G.dst e = y) ∨ (G.src e = y ∧ G.dst e = Tr.par y)) ∧
    G.src e ∈ Utilde B (S : Set (Fin G.n))

theorem growForest_tedge {c : FPCtx G s} (hout : OutOK c) (hsort : OutSorted c)
    {S : Finset (Fin G.n)} {ι : IState G s} {x : Fin G.n} {σ' : SSt G s} {res : SearchRes}
    {n : ℕ} (hx : x ∉ ι.tv) (hres : res ≠ .failed)
    (hs : Search c ι.tv (initSt ι.d ι.D x) σ' res n) (hS0 : SInv c (initSt ι.d ι.D x))
    (hF : FInv c ι) (hTE : TEdge c.B S ι.trees)
    (hdU : ∀ w ∈ σ'.done, w ∈ Utilde c.B (S : Set (Fin G.n))) :
    TEdge c.B S (growForest res ι.trees x σ') := by
  classical
  have hTI : TreeInv c ι.tv x σ' := Search.treeInv hout hsort hs hS0 (treeInv_initSt hx)
  have hTD : TreeDone x σ' := Search.treeDone hs treeDone_initSt
  have hKtv : ∀ w ∈ σ'.K, w ∉ ι.tv := hTI.disj
  -- an edge from the first-discovery parent
  have hkedge : ∀ y ∈ σ'.K, y ≠ x → ∃ e : Fin G.m, G.src e = σ'.kpar y ∧ G.dst e = y ∧
      G.src e ∈ Utilde c.B (S : Set (Fin G.n)) := by
    intro y hy hyx
    obtain ⟨e, he, hdst⟩ := hTI.edge y hy hyx
    have hsrc : G.src e = σ'.kpar y := (hout _ e).mp he
    exact ⟨e, hsrc, hdst, hsrc ▸ hdU _ (hTD y hy hyx)⟩
  cases res with
  | failed => exact absurd rfl hres
  | success =>
    have hgf : growForest .success ι.trees x σ' = ι.trees ++ [⟨x, σ'.K, σ'.kpar⟩] := by
      simp [growForest]
    rw [hgf]
    intro Tr hTr y hy hyr
    rcases List.mem_append.mp hTr with h | h
    · exact hTE Tr h y hy hyr
    · rw [List.mem_singleton] at h; subst h
      obtain ⟨e, h1, h2, h3⟩ := hkedge y hy hyr
      exact ⟨e, Or.inl ⟨h1, h2⟩, h3⟩
  | contact =>
    obtain ⟨u, ec, hhit, hud, hec, hvT⟩ := Search.hit_done hs rfl
    have hgf : growForest .contact ι.trees x σ' = ι.trees.map (fun Tr =>
        if G.dst ec ∈ Tr.ord then mergeTree Tr σ'.K σ'.kpar x u (G.dst ec) else Tr) := by
      simp [growForest, hhit]
    have huK : u ∈ σ'.K := by
      obtain ⟨-, hc⟩ := Search.result_info hout hsort hs hS0
      obtain ⟨u', v', hhit', hu'K, -⟩ := hc rfl
      rw [hhit] at hhit'
      rw [(Prod.mk.inj (Option.some.inj hhit')).1]; exact hu'K
    obtain ⟨hpA, hpB, hpC, hpD, hpE⟩ := kpath_spec hTI.pf σ'.K.length u huK
      (List.idxOf_lt_length_of_mem huK).le
    have hpathK : ∀ y ∈ kpath σ'.kpar x σ'.K.length u, y ∈ σ'.K := fun y hy => (hpA y hy).1
    rw [hgf]
    intro Tr' hTr' y hy hyr
    rw [List.mem_map] at hTr'
    obtain ⟨Tr, hTr, rfl⟩ := hTr'
    by_cases hvTr : G.dst ec ∈ Tr.ord
    · simp only [hvTr, ite_true, mergeTree] at hy hyr ⊢
      set f : Fin G.n → Fin G.n := fun w => if w ∈ σ'.K then σ'.kpar w else Tr.par w
      rcases List.mem_append.mp hy with hy1 | hy3
      · rcases List.mem_append.mp hy1 with hy1 | hy2
        · -- an old tree vertex
          have hytv : y ∈ ι.tv := (hF.tv y).mpr ⟨Tr, hTr, hy1⟩
          have hyK : y ∉ σ'.K := fun h => hKtv y h hytv
          have hyp : y ∉ kpath σ'.kpar x σ'.K.length u := fun h => hyK (hpathK y h)
          rw [reroot_not_mem hyp]
          simp only [f, hyK, ite_false]
          exact hTE Tr hTr y hy1 hyr
        · -- a vertex of the re-rooted path
          obtain ⟨pre, post, hdec⟩ := List.append_of_mem hy2
          rcases List.eq_nil_or_concat pre with hpre | ⟨pre', a, hpre⟩
          · subst hpre
            simp only [List.nil_append] at hdec
            have hyu : y = u := by
              have h1 : (kpath σ'.kpar x σ'.K.length u).head? = some y := by rw [hdec]; rfl
              rw [hpC] at h1
              exact (Option.some.inj h1).symm
            rw [hdec, reroot_head (hdec ▸ hpD)]
            refine ⟨ec, Or.inr ⟨hyu ▸ (hout u ec).mp hec, rfl⟩, ?_⟩
            rw [(hout u ec).mp hec]; exact hdU u hud
          · subst hpre
            have hdec' : kpath σ'.kpar x σ'.K.length u = pre' ++ a :: y :: post := by rw [hdec]; simp
            rw [reroot_succ hpD pre' post a y hdec']
            have hya : y = σ'.kpar a := hpE pre' post a y hdec'
            have haK : a ∈ σ'.K := hpathK a (by rw [hdec']; simp)
            have hax : a ≠ x := kpath_ne_of_succ _ _ pre' post a y hdec'
            obtain ⟨e, h1, h2, h3⟩ := hkedge a haK hax
            exact ⟨e, Or.inr ⟨h1.trans hya.symm, h2⟩, h3⟩
      · -- another member of the contact search
        rw [List.mem_filter] at hy3
        obtain ⟨hyK, hyp⟩ := hy3
        have hyp' : y ∉ kpath σ'.kpar x σ'.K.length u := by simpa using hyp
        rw [reroot_not_mem hyp']
        simp only [f, hyK, ite_true]
        have hyx : y ≠ x := fun h => hyp' (h ▸ hpB)
        obtain ⟨e, h1, h2, h3⟩ := hkedge y hyK hyx
        exact ⟨e, Or.inl ⟨h1, h2⟩, h3⟩
    · simp only [hvTr, ite_false] at hy hyr ⊢
      exact hTE Tr hTr y hy hyr

/-- The tree-edge property is preserved by the invocation loop. -/
theorem Invoke.tedge {c : FPCtx G s} (hout : OutOK c) (hsort : OutSorted c)
    {S : Finset (Fin G.n)} {d0 : Labels G s} (hpre : CallPre c.B S d0)
    (hLxS : ∀ x ∈ S, c.Lx ≤ d0 x) {ι ι' : IState G s} {L : List (Fin G.n)} {n : ℕ}
    (h : Invoke c ι L ι' n) (hLS : ∀ x ∈ L, x ∈ S) (hI : IInv c d0 S ι) (hF : FInv c ι)
    (hTE : TEdge c.B S ι.trees) : TEdge c.B S ι'.trees := by
  have hLxU : ∀ v ∈ Utilde c.B (S : Set (Fin G.n)), c.Lx ≤ dis (s := s) v := by
    intro v hv
    rcases hpre.frontier v hv with ⟨hX, -⟩ | ⟨y, hy, hyc, hyv⟩
    · exact absurd hX (Set.notMem_empty v)
    · calc c.Lx ≤ d0 y := hLxS y hy
        _ = dis (s := s) y := hyc
        _ ≤ dis (s := s) v := hyv.dis_le
  induction h with
  | nil => exact hTE
  | skip ι ι' x L n _ _ ih => exact ih (fun y hy => hLS y (List.mem_cons_of_mem _ hy)) hI hF hTE
  | fail ι ι' x L σ' n n' hx hsearch _ ih =>
    have h1 := Invoke.fail ι _ x [] σ' n 0 hx hsearch (Invoke.nil _)
    have hL1 : ∀ y ∈ [x], y ∈ S := fun y hy => by
      rw [List.mem_singleton] at hy; rw [hy]; exact hLS x List.mem_cons_self
    have hI1 := (Invoke.inv hout hsort hpre hLxS h1 hL1 hI).1
    have hF1 := Invoke.forest hout hsort hpre h1 hL1 hI.walk hI.le hF
    exact ih (fun y hy => hLS y (List.mem_cons_of_mem _ hy)) hI1 hF1 hTE
  | grow ι ι' x L σ' res n n' hx hres hsearch _ ih =>
    have h1 := Invoke.grow ι _ x [] σ' res n 0 hx hres hsearch (Invoke.nil _)
    have hL1 : ∀ y ∈ [x], y ∈ S := fun y hy => by
      rw [List.mem_singleton] at hy; rw [hy]; exact hLS x List.mem_cons_self
    have hI1 := (Invoke.inv hout hsort hpre hLxS h1 hL1 hI).1
    have hF1 := Invoke.forest hout hsort hpre h1 hL1 hI.walk hI.le hF
    have hxS : x ∈ S := hLS x List.mem_cons_self
    have hxB : d0 x < c.B := hpre.inRange x hxS
    have hxtop : ι.d x ≠ ⊤ := ne_top_of_lt (lt_of_le_of_lt (hI.le x) hxB)
    have hS0 : SInv c (initSt ι.d ι.D x) := initSt_inv hI.walk hxtop
    have hd0top : d0 x ≠ ⊤ := ne_top_of_lt hxB
    have hxreach : G.Reachable s x := by
      obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hd0top
      exact ⟨q, hpre.walk x q hq.symm⟩
    have hxU : x ∈ Utilde c.B (S : Set (Fin G.n)) :=
      ⟨lt_of_le_of_lt (hpre.walk.sound x) hxB, x, hxS, onPath_self hxreach⟩
    have hcf0 : Conf d0 (Utilde c.B (S : Set (Fin G.n))) (initSt ι.d ι.D x) :=
      ⟨fun v hv => by simp only [initSt, Finset.mem_singleton] at hv; subst hv; exact hxU,
        fun v hv => absurd hv (Finset.notMem_empty v), hI.chg, hI.dinv⟩
    have hcf := Search.conf hout hsort (d0 := d0) hpre.claimC hLxU hsearch hS0 hcf0
    have hTE1 := growForest_tedge hout hsort hx hres hsearch hS0 hF hTE hcf.done
    exact ih (fun y hy => hLS y (List.mem_cons_of_mem _ hy)) hI1 hF1 hTE1

/-- **Tree edges and duplicate-free tree vertices** for the cost-indexed relation (inputs of
agent-03's O10 home charging and of `FPData.tvs`): every non-root tree vertex `y` is joined to its
parent by a graph edge `e` (either orientation) whose tail lies in `Ũ(B, S)`, and the concatenated
tree orders are duplicate-free. -/
theorem findPivotsCL_tedge {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}
    (hout : ∀ u e, e ∈ out u ↔ G.src e = u) (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    {Lx B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} {Din : Finset (Fin G.m)}
    {d1 : Labels G s} {Dout : Finset (Fin G.m)} {Q W : Finset (Fin G.n)}
    {trees : List (TreeRec (Fin G.n))} {cost : ℕ} (hpre : CallPre B S d0)
    (hLxS : ∀ x ∈ S, Lx ≤ d0 x) (hDin : ∀ e ∈ Din, dis (s := s) (G.dst e) < dis (s := s) (G.src e))
    (h : FindPivotsCL out k hins hext Lx B S d0 Din d1 Dout Q W trees cost) :
    TEdge B S trees ∧ (trees.flatMap (fun T => T.ord)).Nodup := by
  obtain ⟨SL, ι', -, hSL, hrun, rfl, rfl, rfl, rfl, rfl, -⟩ := h
  set c := pinCtx out k hins hext B Lx
  have hout' : OutOK c := hout
  have hsort' : OutSorted c := hsort
  have hpre' : CallPre c.B S d0 := hpre
  have hI0 : IInv c d0 S ⟨d0, Din, ∅, ∅, ∅, []⟩ :=
    ⟨hpre.walk, fun _ => le_rfl, fun v h => absurd rfl h, hDin,
      fun v hv => absurd hv (Finset.notMem_empty v), Finset.empty_subset _,
      fun y hy => absurd hy (Finset.notMem_empty y)⟩
  have hF0 : FInv c (⟨d0, Din, ∅, ∅, ∅, []⟩ : IState G s) :=
    ⟨fun T hT => absurd hT List.not_mem_nil, fun T hT => absurd hT List.not_mem_nil,
      fun v => by simp, List.Pairwise.nil⟩
  have hTE0 : TEdge c.B S ([] : List (TreeRec (Fin G.n))) := fun T hT => absurd hT List.not_mem_nil
  have hTE := Invoke.tedge hout' hsort' hpre' hLxS hrun (fun x hx => (hSL x).mp hx) hI0 hF0 hTE0
  have hF := Invoke.forest hout' hsort' hpre' hrun (fun x hx => (hSL x).mp hx) hpre.walk
    (fun _ => le_rfl) hF0
  refine ⟨hTE, ?_⟩
  rw [List.nodup_flatMap]
  exact ⟨fun T hT => (hF.pf T hT).1, hF.disj.imp (fun h a ha hb => h a ha hb)⟩

end Trees

end CHD
end Frontier
