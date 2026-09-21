# PAPER_CHD — sections N1–N4 (author agent-03). Handled ranges, outside leaves, pivot bound, re-selection charging.
Status: paper proof, NOT reviewed, NOT formalized. Notation and line numbers: B1 PCv2.3 (BM.x, BC.x) with C-HD's FH.x (agent-09
C_HD_PROOF_v1 M3); S2 = B1 Appendix C (Lemma S2.1 (R1)–(R9), loop invariants (J1)–(J5), facts (S-a),(S-b), Claim C = (C1)).
Everything is w.r.t. the admissible top instance I_0 and the exact walk order ≺ of S1 §A (version-stamped labels).
All calls satisfy (C1)–(C3) (S2 Cor. S2.2 for the root, S2 Step 2 for sub-calls), so S2's conclusions hold for every call.

## N0. Definitions
For a non-root call X that is the i-th child (BM.13) of its parent Z, put B_low(X) := the value of Z's variable B' just before
iteration i, i.e. B'_{i-1}(Z) (B'_0(Z) is set at BM.8, B'_r(Z) := B'_{X_r} at BM.24). For the root put B_low := λ_{x_s} (the
source label, ≺-minimum of all labels). The HANDLED RANGE of X is  H(X) := { λ : B_low(X) ⪯ λ ≺ B'_X }  (B'_X = X's returned bound).
A LEAF of FindPivots-HD at X is a vertex added at FH.14 by a relaxation that is INVALID at FH.10 (FH.16). It is OUTSIDE if
v ∉ Ũ_X := Ũ(B_X, S_X). O_X denotes the set of outside vertices of X's pre-partition trees F̄ (at FindPivots' return).

## N1. Lemma (nesting and disjointness of handled ranges)
(a) For every non-root call X with parent Z: H(X) ⊆ H(Z).
(b) The handled ranges of the children X_1, …, X_f of Z are pairwise disjoint: H(X_r) = [B'_{r-1}(Z), B'_r(Z)).
(c) Any two distinct calls of the same layer have disjoint handled ranges.
(d) For every call X:  U_X ⊆ { v : dis(v) ∈ H(X) },  and for a FULL call (B'_X = B_X):  H(X) = [B_low(X), B_X).
Proof. (b) is the definition plus (J5)/(R8): B'_0 ⪯ B'_1 ⪯ … ⪯ B'_f.
(a) Upper end: B'_X = B'_r(Z) ⪯ B'_f(Z) ⪯ B'_Z. The first step is monotonicity (J5). For the second: if the loop of Z ends with D ≠ ∅,
then B'_Z = B'_f; otherwise BM.24a sets B'_Z := B_Z, and B'_f ⪯ B_f ⪯ B_Z by (R1) of the child and PP.
Lower end: B_low(X) = B'_{r-1}(Z) ⪰ B'_0(Z). It remains to show B'_0(Z) ⪰ B_low(Z).
 - If Z is the root, this is trivial.
 - Otherwise Z is the r'-th child of Z'. By (S-a) at Z', dis(y) ⪰ B'_{r'-1}(Z') = B_low(Z) for every y ∈ S_Z. BM.8 gives
   B'_0(Z) = min(B_Z, min_j d[p_j]) with p_j ∈ S_Z, and d[p_j] ⪰ dis(p_j) ⪰ B_low(Z) (S2 (V2)/A3).
   Also B_Z ⪰ B_low(Z): S_Z ≠ ∅ (C3), and any y ∈ S_Z has B_Z ≻ d[y] ⪰ dis(y) ⪰ B_low(Z).
(c) Take two distinct calls of one layer and their first differing ancestors, two siblings W1 ≠ W2. H(W1) ∩ H(W2) = ∅ by (b), and
both calls' ranges are nested inside them by (a).
(d) U_X = Ũ(B'_X, S_X) by (R1), so dis(v) ≺ B'_X. path(v) visits some z ∈ S_X, hence dis(v) ⪰ dis(z) (A1), and
dis(z) ⪰ B_low(X) by (S-a) at the parent (for the root, B_low is the minimum label). For a full call B'_X = B_X. ∎

## N2. Lemma (outside leaves are complete and live in the handled range)
If v is a leaf of FindPivots-HD at X and v ∉ Ũ_X, then v is complete and B_low(X) ⪯ dis(v) = d[v] ≺ B_X.
If X is full, dis(v) ∈ H(X).
Proof. Let the leaf be created by scanning e = (u,v), with cand := d[u] ⊕ e.
 - FH.8 did not break, so cand ≺ B_X.
 - FH.9 did not fire, so d[v] ⪰ B_low(X).
 - Relax was invalid with cand ≺ B_X, so cand ⪯ d[v] fails, i.e. d[v] ≺ cand ≺ B_X (≺ is total).
Hence dis(v) ⪯ d[v] ≺ B_X, and v ∉ Ũ_X. By (C1) at X's start, v was complete then. Completeness persists (S1), so d[v] = dis(v).
FindPivots-HD never writes an invalid target's label. For a full X, apply N1(d). ∎
Remark (why FH.9's range test is needed). Without it, complete vertices below B_low(X) — for instance W-vertices of an ancestor that
are complete but not yet returned — become leaves in EVERY later call, so no per-layer bound exists. This is the R1 counterexample
(agents 02/03/05/07/08). FH.9 is safe: d[v] ≺ B_low(X) implies dis(v) ≺ B_low(X), so v ∉ Ũ_X (all of Ũ_X has dis ⪰ B_low(X), by
N1(d)'s argument), so v is complete by (C1). An edge into v then stays invalid forever: every later tail w has d[w] ⪰ dis(w) ⪰ B_low of
its call ⪰ ... ≻ dis(v) — agent-09 H7 gives the ordering of later calls — and T2 applies.

## N3. Lemma (pivot count)
(a) Partial X: p_X ≤ |S_X| < |U_X|/t (FP2, MP.8; B1 (B2)).
(b) For every layer, Σ_{full X in the layer} |O_X| ≤ N, and Σ_{full X in the layer} p_X ≤ 2N/(k−1).
Proof of (b).
 - Every tree vertex that is not an outside leaf lies in Ũ_X:
   - the root x lies in S_X ⊆ Ũ_X (C3);
   - explored vertices are touched, hence in Ũ_X (L3+ / FP5);
   - inside leaves lie in Ũ_X by definition.
 - Ũ_X = U_X for full X (R1). Trees of one FindPivots are vertex-disjoint: FH.3 skips tree vertices, FH.11–12 merge on contact,
   and FH.13–14 only add vertices not yet in K.
 - So Σ_T |V(T)| ≤ |U_X| + |O_X|.
 - For two full calls X ≠ X' of one layer, U_X ∩ U_{X'} = ∅ (N1(c,d)). Also O_X ∩ O_{X'} = ∅: an outside leaf is complete, so its dis
   is fixed, and by N2 it lies in both H(X) and H(X'), which are disjoint.
 - Hence Σ (|U_X| + |O_X|) ≤ 2N. PT pieces have ≥ k−1 edges and empty groups are dropped (MP.8), so
   p_X ≤ Σ_T (|V(T)|−1)/(k−1) (B1 FP4). ∎
Cost consequence: pivot inserts (BM.7) cost O(t) each, so Σ_layer O(t p) = O(N t/k) for full calls and O(|U_X|) for partial ones.

## N4. Lemma (re-selection charging with outside leaves; replaces B1 S4.5 T5 for full calls)
Setting: X is full, with children Y_1..Y_f. Homes:
 - For u ∈ U_X (U_X = W'_X ⊔ U_{Y_1} ⊔ … ⊔ U_{Y_f} by (R8)): h(u) := r if u ∈ U_{Y_r}, and h(u) := 0 if u ∈ W'_X.
 - For an outside leaf v ∈ O_X: h(v) := r if dis(v) ∈ H(Y_r) = [B'_{r-1}, B'_r); h(v) := −1 if dis(v) ≺ B'_0;
   h(v) := f+1 if dis(v) ⪰ B'_f.
(i) Let g_j be the number of re-selections (BM.23) of group j in X. Let c_j be the number of edges of the PT piece F_j ⊇ P_j whose two
    endpoints have different homes. Then g_j ≤ c_j + 1.
(ii) Every graph edge is counted in some c_j of some full call at most twice in the whole run. Hence Σ_{full X} Σ_j g_j ≤ Σ p + 2m,
    and re-selections cost O(t(Σ p + m)).
Proof of (i).
 - A re-selection of j at iteration r needs the then-current pivot p_j ∈ U_{Y_r} (BM.18). There is at most one per (j, r).
 - Removed pivots lie in P_j ⊆ S_X ∩ V(F_j) ⊆ U_X and have home r.
 - Delete from the tree F_j all different-home edges. This leaves c_j+1 components, each with a single home.
 - Pivots removed at different iterations have different homes, so they lie in different components. ∎
Proof of (ii). Every tree edge is a graph edge (u,e) whose tail u was extracted, so u ∈ U_X. Two kinds of different-home edges:
 (α) Both endpoints in U_X. The edge lies in E_X := E(U_X) \ ⋃_r E(U_{Y_r}), and Σ_X |E_X| ≤ m by B1 (G3): an edge is in E_X only at
     the unique call where its endpoints first leave a common part.
 (β) Head v ∈ O_X. Suppose e = (u,v) were of kind (β) at two full calls X ≠ X'. Both contain u in U, so both lie on u's chain; say X'
     is a proper descendant of X, inside X's child Y_r.
     - Then u ∈ U_{X'} ⊆ U_{Y_r}, so h_X(u) = r.
     - v ∈ O_{X'} gives dis(v) ∈ H(X') ⊆ H(Y_r) by N2 and N1(a), so h_X(v) = r.
     - Thus e has equal homes at X and is not counted there. Contradiction.
     So kind (β) is used at most once per edge. Kinds (α) and (β) together give at most 2 per edge. ∎
Remark. B1 T5 ("F_j ⊆ U_X") and C_HD_PROOF_v1 T5' ("leaves have tree-degree 1") both FAIL for C-HD: FH.11–12 merge on contact with
an existing tree's LEAF, which then has tree-degree ≥ 2 and can join two different U_r's through an edge outside E(U_X). N4 is the
replacement. Partial calls need no tree argument (B1 T5 partial case: O(t|S|) ≤ O(|U|)).
