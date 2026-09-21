import Frontier.CHD.FindPivots
import Frontier.CHD.BMCost

/-!
# Frontier.CHD.FPBind — FindPivots-HD as the FindPivots parameter of the cost-indexed BMSSP

Owner: agent-05 (C-HD package L2, Layer A).  NON-GATE.

Instantiates agent-01's `BM.FPRelC` (`Frontier.CHD.BMCost`) with the cost-indexed
FindPivots-HD relation `FindPivotsC` of `Frontier.CHD.FindPivots` — pinned cap `k`,
`L_X = d_B[S]` (FH.1/FH.9), the fixed sorted out-lists of the preprocessed graph, heap costs
`hins`/`hext` — answering tracker item O21:

* persistent state `Φ := Finset (Fin G.m)`, the set `D` of deleted edges (threaded through all
  calls by `BMSSPC`: input `D_in`, output `D_out`), with invariant `DelInv` (PAPER_CHD
  Lemma L(b): every deleted edge goes to a strictly smaller canonical label);
* output data `Ω := FPData` (`L_X` of the call and the parent-first forest of the invocation);
* groups `P` = the tree partition `forestGroups` (agent-03's `makePivots ∘ forestPieces`).

Main results:
* `fpC_sound : FPCSound (fpC …) DelInv` — so `BM.bmsspC_post` / `BM.bmsspC_top_exact` apply;
* `fpC_total` — totality (agent-08's R4, tracker O14) for FindPivots;
* `fpC_spec` — deletions only grow, the group size bound `|P_j| < 3k`, the pivot bound
  `p (k - 1) ≤ #tree vertices`, and the per-invocation cost bound (paper T-FP)
  `c + scanC·|D_in| ≤ scanC·|D_out| + A·(#tree vertices + k·|Q|) + 3·|S|`, `A = fpA k hins hext`.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD

open Frontier Graph Frontier.CHD.Partition

variable {G : Graph} {s : Fin G.n}

variable (G s) in
/-- The static deletion invariant (PAPER_CHD Lemma L(b)): every deleted edge goes to a strictly
smaller canonical label. -/
def DelInv (D : Finset (Fin G.m)) : Prop :=
  ∀ e ∈ D, dis (s := s) (G.dst e) < dis (s := s) (G.src e)

variable (G s) in
/-- FindPivots data handed to the cost chain: the call's `L_X` and its forest. -/
structure FPData where
  /-- `L_X = d_B[S]` of the call -/
  Lx : WLab G s
  /-- the parent-first trees built by the invocation (in construction order) -/
  trees : List (TreeRec (Fin G.n))
  /-- the deleted-edge set before the invocation -/
  Din : Finset (Fin G.m)
  /-- the deleted-edge set after the invocation -/
  Dout : Finset (Fin G.m)

variable (G s) in
/-- **FindPivots-HD as a cost-indexed FindPivots relation** (`BM.FPRelC`).  The level and the
lower bound `Blow` are not used: the cap `k` is global and `L_X = d_B[S] ≥ Blow`. -/
def fpC (out : Fin G.n → List (Fin G.m)) (k hins hext : ℕ) :
    BM.FPRelC G s (Finset (Fin G.m)) (FPData G s) :=
  fun _l _Blow B S d0 Din d1 p P Q W Dout ω c =>
    FindPivotsC out k hins hext B S d0 Din d1 Dout Q W ω.trees c ∧ ω.Lx = lxOf B S d0 ∧
      (∃ hp : p = (forestGroups S Q k ω.trees).length,
        ∀ j, P j = ((forestGroups S Q k ω.trees).get (Fin.cast hp j)).toFinset) ∧
      ω.Din = Din ∧ ω.Dout = Dout

section

variable {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}

/-- **Soundness** in agent-01's shape: `FPCSound (fpC …) DelInv`. -/
theorem fpC_sound (hout : ∀ u e, e ∈ out u ↔ G.src e = u)
    (hsort : ∀ u, (out u).Pairwise (SortedRel G s)) (hsimp : ∀ u, ((out u).map G.dst).Nodup)
    (hk : 2 ≤ k) : BM.FPCSound G s (fpC G s out k hins hext) (DelInv G s) := by
  intro l Blow B S d0 φ d1 p P Q W φ' ω c hpre hI _ h
  obtain ⟨hrel, -, ⟨hp, hP⟩, -⟩ := h
  obtain ⟨hcon, hdinv, -⟩ := findPivotsC_spec hout hsort hsimp hk hpre hI hrel
  subst hp
  obtain rfl : P = fun j => ((forestGroups S Q k ω.trees).get j).toFinset := funext hP
  exact ⟨hcon, hdinv⟩

/-- **Totality** (R4 / O14): every call satisfying `CallPre` has a FindPivots-HD run, for every
level, lower bound and input deletion set. -/
theorem fpC_total (hout : ∀ u e, e ∈ out u ↔ G.src e = u)
    (hsort : ∀ u, (out u).Pairwise (SortedRel G s)) (l : ℕ) (Blow B : WLab G s)
    (S : Finset (Fin G.n)) (d0 : Labels G s) (Din : Finset (Fin G.m)) (hpre : CallPre B S d0) :
    ∃ d1 p P Q W Dout ω c, fpC G s out k hins hext l Blow B S d0 Din d1 p P Q W Dout ω c := by
  obtain ⟨d1, Dout, Q, W, trees, cost, h⟩ := findPivotsC_total (k := k) (hins := hins)
    (hext := hext) hout hsort Din hpre
  exact ⟨d1, _, fun j => ((forestGroups S Q k trees).get j).toFinset, Q, W, Dout,
    ⟨lxOf B S d0, trees, Din, Dout⟩, cost, h, rfl, ⟨rfl, fun _ => rfl⟩, rfl, rfl⟩

/-- **Deletions, group sizes, pivot bound and cost** of one invocation (paper T-FP), for the
cost chain: with `#tv := (ω.trees.flatMap ord).length` the number of tree vertices,
`D_in ⊆ D_out`, `|P_j| < 3k`, `p (k - 1) ≤ #tv` and
`c + scanC·|D_in| ≤ scanC·|D_out| + A·(#tv + k·|Q|) + 3·|S|`. -/
theorem fpC_spec (hout : ∀ u e, e ∈ out u ↔ G.src e = u)
    (hsort : ∀ u, (out u).Pairwise (SortedRel G s)) (hsimp : ∀ u, ((out u).map G.dst).Nodup)
    (hk : 2 ≤ k) {l : ℕ} {Blow B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s}
    {Din Dout : Finset (Fin G.m)} {p : ℕ} {P : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)}
    {ω : FPData G s} {c : ℕ} (hpre : CallPre B S d0) (hI : DelInv G s Din)
    (h : fpC G s out k hins hext l Blow B S d0 Din d1 p P Q W Dout ω c) :
    ω.Lx = lxOf B S d0 ∧ Din ⊆ Dout ∧ (∀ j, (P j).card < 3 * k) ∧
      p * (k - 1) ≤ (ω.trees.flatMap (fun T => T.ord)).length ∧
      c + scanC * Din.card ≤
        scanC * Dout.card + fpA k hins hext * ((ω.trees.flatMap (fun T => T.ord)).length +
          k * Q.card) + 3 * S.card := by
  obtain ⟨hrel, hLx, ⟨hp, hP⟩, -⟩ := h
  obtain ⟨-, -, hsub, hsz, hcnt, hcost⟩ := findPivotsC_spec hout hsort hsimp hk hpre hI hrel
  subst hp
  refine ⟨hLx, hsub, fun j => ?_, hcnt, hcost⟩
  rw [hP j]
  exact lt_of_le_of_lt (List.toFinset_card_le _) (hsz _)

/-- **Lemma F2** (tracker O3) in the cost chain's shape: every tree vertex outside `Ũ(B, S)` (a
foreign leaf) has its fixed canonical label in `[L_X, B)` with `B_low ≤ L_X` (when
`B_low ≤ B` and `B_low` bounds `S`'s labels), and is complete before and after the invocation. -/
theorem fpC_foreign (hout : ∀ u e, e ∈ out u ↔ G.src e = u)
    (hsort : ∀ u, (out u).Pairwise (SortedRel G s)) {l : ℕ} {Blow B : WLab G s}
    {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {Din Dout : Finset (Fin G.m)} {p : ℕ}
    {P : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {ω : FPData G s} {c : ℕ}
    (hpre : CallPre B S d0) (h : fpC G s out k hins hext l Blow B S d0 Din d1 p P Q W Dout ω c) :
    (Blow ≤ B → (∀ x ∈ S, Blow ≤ d0 x) → Blow ≤ ω.Lx) ∧
      ∀ T ∈ ω.trees, ∀ v ∈ T.ord, v ∉ Utilde B (S : Set (Fin G.n)) →
        ω.Lx ≤ dis (s := s) v ∧ dis (s := s) v < B ∧ Complete d0 v ∧ Complete d1 v := by
  obtain ⟨hrel, hLx, -, -⟩ := h
  rw [hLx]
  exact ⟨fun hB hS => le_lxOf hB hS, findPivotsC_foreign hout hsort hpre hrel⟩

/-- **`#tv ≤ k·|S|`** (L5's `partial_Fo` input): an invocation has at most `k` tree vertices per
root of `S`. -/
theorem fpC_tv_card (hout : ∀ u e, e ∈ out u ↔ G.src e = u)
    (hsort : ∀ u, (out u).Pairwise (SortedRel G s)) (hk : 1 ≤ k) {l : ℕ} {Blow B : WLab G s}
    {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {Din Dout : Finset (Fin G.m)} {p : ℕ}
    {P : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {ω : FPData G s} {c : ℕ}
    (hpre : CallPre B S d0) (h : fpC G s out k hins hext l Blow B S d0 Din d1 p P Q W Dout ω c) :
    (ω.trees.flatMap (fun T => T.ord)).length ≤ k * S.card :=
  findPivotsCL_tv_card hout hsort hk hpre h.1

/-- The deletion interval recorded in the FindPivots data: `ω.Din = D_in ⊆ D_out = ω.Dout`
(the input of `FPDel`'s execution-order chain). -/
theorem fpC_interval (hout : ∀ u e, e ∈ out u ↔ G.src e = u)
    (hsort : ∀ u, (out u).Pairwise (SortedRel G s)) {l : ℕ} {Blow B : WLab G s}
    {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {Din Dout : Finset (Fin G.m)} {p : ℕ}
    {P : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {ω : FPData G s} {c : ℕ}
    (h : fpC G s out k hins hext l Blow B S d0 Din d1 p P Q W Dout ω c) :
    ω.Din = Din ∧ ω.Dout = Dout ∧ Din ⊆ Dout := by
  obtain ⟨⟨SL, ι', -, -, hrun, -, rfl, -⟩, -, -, h1, h2⟩ := h
  exact ⟨h1, h2, Invoke.D_mono hrun⟩

/-- **Per-invocation cost with the deletion counter** (for `CostAggregate.Valid.cost_le`):
`c ≤ scanC·|ω.Dout \ ω.Din| + A·(#tv + k·|Q|) + 3·|S|`. -/
theorem fpC_cost_del (hout : ∀ u e, e ∈ out u ↔ G.src e = u)
    (hsort : ∀ u, (out u).Pairwise (SortedRel G s)) (hsimp : ∀ u, ((out u).map G.dst).Nodup)
    (hk : 2 ≤ k) {l : ℕ} {Blow B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s}
    {Din Dout : Finset (Fin G.m)} {p : ℕ} {P : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)}
    {ω : FPData G s} {c : ℕ} (hpre : CallPre B S d0) (hI : DelInv G s Din)
    (h : fpC G s out k hins hext l Blow B S d0 Din d1 p P Q W Dout ω c) :
    c ≤ scanC * (ω.Dout \ ω.Din).card + fpA k hins hext * ((ω.trees.flatMap (fun T => T.ord)).length +
      k * Q.card) + 3 * S.card := by
  obtain ⟨h1, h2, hsub⟩ := fpC_interval hout hsort h
  obtain ⟨-, -, -, -, hcost⟩ := fpC_spec hout hsort hsimp hk hpre hI h
  rw [h1, h2, Finset.card_sdiff_of_subset hsub]
  have := Finset.card_le_card hsub
  rw [Nat.mul_sub]
  have h3 : scanC * Din.card ≤ scanC * Dout.card := Nat.mul_le_mul_left _ this
  omega

/-- **Tree edges and duplicate-free tree vertices** (agent-03's O10 inputs) in FPC shape: every
non-root vertex `y` of a tree `T ∈ ω.trees` is joined to `T.par y` by a graph edge `e` (either
orientation) with `src e ∈ Ũ(B, S)`, and `ω.trees.flatMap ord` is duplicate-free. -/
theorem fpC_tedge (hout : ∀ u e, e ∈ out u ↔ G.src e = u)
    (hsort : ∀ u, (out u).Pairwise (SortedRel G s)) {l : ℕ} {Blow B : WLab G s}
    {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {Din Dout : Finset (Fin G.m)} {p : ℕ}
    {P : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {ω : FPData G s} {c : ℕ}
    (hpre : CallPre B S d0) (hI : DelInv G s Din)
    (h : fpC G s out k hins hext l Blow B S d0 Din d1 p P Q W Dout ω c) :
    (∀ T ∈ ω.trees, ∀ y ∈ T.ord, y ≠ T.root → ∃ e : Fin G.m,
      ((G.src e = T.par y ∧ G.dst e = y) ∨ (G.src e = y ∧ G.dst e = T.par y)) ∧
      G.src e ∈ Utilde B (S : Set (Fin G.n))) ∧
    (ω.trees.flatMap (fun T => T.ord)).Nodup :=
  findPivotsCL_tedge hout hsort hpre (fun _ hx => lxOf_le hx) hI h.1

end

end CHD
end Frontier
