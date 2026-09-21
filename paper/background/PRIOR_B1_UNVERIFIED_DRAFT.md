# MASTER DOCUMENT — B1: bootstrapped DMSY26, a deterministic directed SSSP algorithm running in O(m·√log n·(log log n · log log log n)^{1/4}) time on sparse graphs

- Editor: agent-10.
- Section authors: agent-02 (S1 foundations, S7 novelty), agent-08 (S2 corrected core, S3 FindPivots), agent-05 (S4 time and space; independently re-derived by agent-01), agent-04 (S5 data structures and pseudocode).
- Implementations (S6): agent-07, agent-01, agent-04, agent-09, agent-08, agent-06.
- Formal reviewers: agent-09 (#1) and agent-06 (#2). Third reviewer: agent-03. Reviewers wrote no proof sections.

**STATUS: v1.4 FINAL. SUCCESS CLAIM (posted on the board 2026-09-20 ~08:05 UTC).** Every gate item in §9 is closed.
- All sections are frozen (frozen/MANIFEST.tsv, 45 entries, all verified).
- Each section has two formal reviews CORRECT (agent-09, agent-06), plus a third reviewer (agent-03).
- The integrated body has delta verdicts CORRECT from both formal reviewers: agent-09 on v1.2/v1.2.1, agent-06 on v1.2. v1.3 and v1.4 are bookkeeping only.
- Claim-time novelty re-checks (agent-04 and agent-10) found no competitor.
- The self-contained document is MASTER_B1_FULL.md. The tracker is validation_tracker.md.

Version log:
- v0, 07:20 UTC: skeleton.
- v1, 07:50 UTC (board clock): integrated body, final section references, review matrix.
- v1.1, 07:57 UTC: all sections frozen (frozen/MANIFEST.tsv); S3 formal review #1 recorded; final S6 re-run on frozen PCv2.3 recorded (Appendix G).
- v1.2, 08:0x UTC: the integrated-review must-fixes.
- v1.2.1, 08:0x UTC: presentation only. §2.5 steps 1 and 5 are reordered: BFS before dispatch, branches listed separately (this is agent-06 F2). |U_x| ≤ 4k is cited from S4_final. No mathematical change.
- v1.4, ~08:05 UTC: final. Gate table closed; the agent-09/agent-06/agent-03 review files are frozen as Appendices R11–R27; the claim-time novelty re-check is recorded.
- v1.3, 08:0x UTC: bookkeeping from agent-06's delta review #2 (CORRECT on v1.2).
  - F1: A′ review entries.
  - F3: independent E2 reproduction.
  - F5: GM.0 is always executed.
  - No mathematical change.
  - Option-A theorem wording, with the dispatcher Appendix A′ (frozen PCGMv1.2) and its time proof Appendix E3 (frozen S4GMadd).
  - SS.7′/Lemma N0 in place of an undefined n_0.
  - GM.0 for multigraphs.
  - The statement-level S5 correction (§6b).
  - The minor items from agents 09 (M3–M5) and 03 (1–3).

---

## §0 Summary

**Result.** A deterministic algorithm in the comparison-addition model computes exact single-source shortest-path distances, with a shortest-path tree, on directed graphs with nonnegative real weights. For m = O(n) it takes O(n + m·√log n·(log log n · log log log n)^{1/4}) time. This is asymptotically smaller than the 2026 bound of Duan, Mao, Shu and Yin (DMSY26), which is O(m√(log n log log n)) on sparse graphs. The improvement factor is Θ((log log n / log log log n)^{1/4}).

**Idea.** In DMSY26, the sparse bottleneck is the per-vertex, per-level cost f of the local searches inside FindPivots:
- f = Θ(log k), paid by a Fibonacci-heap local Dijkstra;
- failed searches must cost k·f ≤ t each;
- pivots cost t/k per vertex per level.

Together this gives Θ(m·√(log n·f)). We replace each local Dijkstra by a size-capped run of (a corrected) DMSY26 BMSSP itself. The capped run has top threshold τ = k and operates on the global labels, read as a deadline instance: current labels act as caps. Vertices of already-built trees are walls, meaning that relaxations into them are suppressed and recorded as hits, which are merged afterwards. This lowers f to Θ(√(log k log log k)).

**By-products: errata to DMSY26.** The team found eight errata (§6), with O(1)-overhead fixes. The literal pseudocode returns correct distances in all our tests, but its time analysis is invalid as written, and one natural partial fix produces wrong output (E2). Our proof therefore re-proves the core instead of citing DMSY26's Lemmas 3.7 and 3.8.

**Prior art credited.** Kadria and Roditty (arXiv 2609.15247, Sep 2026) use DMSY26's BMSSP as a bounded local search to build balls. They do this for undirected graphs, randomized, with fresh labels, and obtain the same bound shape for undirected graphs. They list the directed case as open (§8).

## §1 Model and problem

- **Input.** A directed graph G = (V, E) with n = |V| and m = |E|. Parallel edges, self-loops, zero-weight edges and zero-weight cycles are allowed. Weights w: E → R≥0. A source s ∈ V.
- **Output.**
  - For every v, dist(v) = dis_G(s, v) ∈ R≥0 ∪ {∞}.
  - pred(v) ∈ V ∪ {nil}, such that the pred pointers form a shortest-path arborescence rooted at s on the reachable set. Every pred edge is tight.
  - Unreachable v get dist = ∞ and pred = nil.
- **Model.** Deterministic comparison-addition model. Real weights are accessed only by comparisons and additions, each costing O(1). Vertex ids, hop counts, version counters, sizes and pointers are handled with standard word-RAM operations on O(log(n+m))-bit integers. Hop counts are at most n', and versions are at most the running time. No other operation is applied to weights.

## §2 Main theorem

**Theorem B1.** There is a deterministic comparison-addition algorithm for directed SSSP with nonnegative real weights that runs in time

  T(n, m) = O( n + min{ m·√log n·(LL·LLL)^{1/4},  m·√log n + √(m n log n · LL) } )

and space O(n + m), where LL = log log n and LLL = log log log n. Parallel edges are allowed: the O(m) step GM.0 keeps one minimum-weight edge per ordered pair, so log n is used throughout.

- **Sparse case, the goal-relevant statement.** For m = O(n) the time is **O(n + m·√log n·(LL·LLL)^{1/4})**. This is o(m√(log n · LL)), the 2026 bound, by a factor Θ((LLL/LL)^{1/4}).
- **Never worse than DMSY26.** T = O(n + m√log n + √(mn log n · LL)) always.
- **Strict improvement range.** T is better by an ω(1) factor exactly when m/n = o(√(LL/LLL)). This includes all sparse graphs.
- **How it is achieved.** An O(1) integer dispatcher (Appendix A′, GM.1–GM.9; time proof Appendix E3, Cor. S4-GM) chooses between two branches:
  - BOOT: the frozen algorithm PCv2.3 with δ = 3. It runs in O(n + m√log n (LL·LLL)^{1/4}) for every m.
  - PLAIN: the corrected DMSY26, meaning the same core with FindPivots-D and a general degree bound δ. It runs within DMSY26's bound.
  - The choice depends only on n and m.

**Comparison convention.**
- DMSY26 assume m ≥ n − 1 (every vertex reachable). Any algorithm that outputs all n distances pays Ω(n). So we compare on inputs with m ≥ n − 1, or equivalently with an additive O(n) on both sides.
- For general inputs the algorithm prunes to the reachable part in O(n + m) time.
- We compare worst-case upper bounds. We claim no lower bound for DMSY26's algorithm.

**Honesty note: the improvement is purely asymptotic ("galactic").**
- The gain factor (LL/LLL)^{1/4} grows extremely slowly. For n = 2^64 the leading factors are about 15.9 vs 19.6, before constants.
- The time analysis needs the side constraints k ≥ 2, k ≥ t_in, t_in³2^{t_in} < k, 3k ≤ t, 3k_in ≤ t_in, and in PLAIN also δ ≤ lg k_D. The driver checks them explicitly (SS.7′, Appendix A′). If they fail, it runs Dijkstra.
- **Lemma N0** (Appendix A′): there is an absolute n_0 such that the test passes for **every** n′ ≥ n_0, so the fallback is O(1) in the asymptotic statement.
- S4's remaining constraint (P4) holds identically by the choice of k and Lemma I (agent-05, 07:57), so it needs no runtime test.
- With the literal formulas, n_0 is astronomical: the relaxed form first holds around log₂ n′ ≈ 10^6 (S4 v5 M1). Correctness never depends on the parameters.
- We make no practical-speedup claim.

**Remarks (not part of Theorem B1).**
- (i) *Deterministic undirected corollary.* Run on the bidirected version of an undirected graph, B1 gives a deterministic undirected algorithm with the sparse bound of Kadria–Roditty's randomized algorithm (KR's derandomization question, answered in terms of the bound).
- (ii) *Deeper nesting.* S4 §S4.11 (Lemma M) and S3 Theorem S3.6 give, with nesting depth 3, O(m√log n·LL^{1/4}·LLL^{1/8}·(log⁽⁴⁾ n)^{1/8}). This is strictly below KR's undirected bound.
  - The frozen PCv2.3 is depth 1. Depth ≥ 2 needs one ZSTAMP/hitlist/HOOK/TSTAMP array set per depth (pseudocode §6 last note).
  - agent-01's optional addendum NB specifies it. It was pre-reviewed by agent-03, agent-06 and agent-05, and has N-version evidence from agent-04 and agent-07.
  - **NOT claimed here.**
- (iii) *Wider general-m range.* A general-δ bootstrap would give m√log n·LL^{1/4}(1 + LLL·n/m)^{1/4}, with strict range m/n = o(√LL). This comes from S4 §S4.9 and uses inner group size k′ = ⌊t′/(3(δ + lg t′))⌋. It has no frozen pseudocode, so it is **not claimed**.

## §2.5 Proof of Theorem B1: assembly

All line numbers refer to the frozen pseudocode PCv2.3 (Appendix A). Section versions are those frozen in Appendices B–H.

1. **Preprocessing and dispatch.** Sources: pseudocode SS.2–SS.6 and §8.1, Appendix A′ (GM.0–GM.9, SS.7′), and S5. The steps run in this order.
   - (a) SS.2–SS.4: BFS from s gives the reachable set R and the edge set E_R, with self-loops dropped. Vertices outside R get dist = ∞ and pred = nil. A self-loop relaxation is never valid (S1 T2).
   - (b) GM.0: parallel edges are deduplicated in O(m). Edges are bucketed by ordered id pairs, the minimum weight is kept, and ties are broken by edge id. A non-minimal parallel edge is never on a canonical walk (S1 §A). Afterwards m_R ≤ n_R(n_R − 1).
     - **GM.0 is always executed** in the algorithm of Theorem B1, although the frozen A′ text calls it "optional" (agent-06 F5). It costs O(m + n) and is harmless when m_R ≤ n_R², and it makes log(n + m) = O(log n) in every case.
   - (c) GM.1–GM.9: BOOT or PLAIN is chosen from (n_R, m_R) using O(1) integer arithmetic.
   - (d) Degree reduction.
     - BOOT (SS.5) uses δ = 3. The result H has N′ ≤ |R| + 2m_R vertices and O(m_R) edges.
     - PLAIN (GM.7) uses the general δ, giving degree ≤ δ and N′ = O(m_R/δ + n_R).
     - Both build zero-weight gadget cycles. For every v ∈ R and every x ∈ cyc[v], the length component of dis_H(x_s, x) equals dis_G(s, v).
   - (e) SS.7′: if the side constraints fail, run Dijkstra with the same labels. This happens only for n′ < n_0, by Lemma N0.
   - Cost of (a)–(e): O(n + m) time and space.
2. **Correctness of the top call (both branches).** BMSSP(∞, {x_s}, L) on the global instance I_0 is a full execution and makes every vertex of H complete. This is S2 **Corollary S2.2**. It follows from **Lemma S2.1**, whose only assumption on FindPivots is the contract FP1–FP6 of §4. The branches differ only in the FindPivots routine: FindPivots-B in BOOT, FindPivots-D in PLAIN. The SS.7′ fallback is plain Dijkstra with the same labels.
3. **The FindPivots routines satisfy FP1–FP6.** FindPivots-D satisfies them on every admissible instance, for any δ (**S3 §3.1**); this covers PLAIN. FindPivots-B satisfies them on I_0 (**S3 §3.2 and Theorem S3.6**); this covers BOOT. The latter uses:
   - S1: the labels (§A), admissible instances (§B), the deadline instance I_x (D1–D3, suppression variant), SP/SP' (checked against the pseudocode), Claim C and L3+ (§D);
   - S2 applied inside I_x (Cor. S2.3), with FindPivots-D satisfying FP on every admissible instance (**S3 §3.1**);
   - S2 **Lemma S2.4 (scan lemma)**, used for failed-search exactness (S3 §3.2.3).
4. **Output** (SS.10–SS.12; S5, pseudocode §8.3).
   - dist(v) is the length component of d[e_v], where e_v is a minimum-hop vertex of cyc[v].
   - pred(v) = orig(tail(d[e_v].e)).
   - The pred edge is tight, and hops strictly decrease along pred. So pred is an arborescence rooted at s.
   - Cost O(n + m).
5. **Time.** Sources: S4_final §S4.1–§S4.7, the F1–F9 discharge table in cost_analysis §13, and Appendix E3.
   - **BOOT.** For δ = 3 the total is O(m t + N′·(log N′/t)·g + N′ log t). Here:
     - g = Θ(√(log k log log k)) is the inner per-vertex cost (S4 Lemma I);
     - k = ⌊t/(3G(t))⌋ (pseudocode §8.2; FIX-SIZE 3k ≤ t);
     - with t from §8.2 this gives O(m √log n (LL·LLL)^{1/4}), for every m.
   - **Ingredients of BOOT:**
     - insertion-event uniqueness (S2 Lemma S2.5 = S4 Lemma G2);
     - the Q-appearance bound (S4 Lemma G4);
     - partial ⇒ |U| > t|S| (S4 B2, FIX-SIZE);
     - the inner output bound |U_x| ≤ 4k (S4_final I1; cost_analysis v5 states the weaker 8k);
     - FP7 (§4).
   - **PLAIN.** Cor. S4-GM (Appendix E3) gives O(m√log n + √(mn log n·LL)) via S4-T with f = δ + lg k_D.
   - **Dispatcher.** It attains the minimum of the two branches up to constants (Cor. S4-GM).
   - **Other costs.** Preprocessing, dispatch and output add O(n + m).
6. **Space** (S4 §8; S5 Lemma MS and §5): O(n + m).
7. **Comparison.** See §2 and S4 §5–§6.

## §3 Section map and review matrix

"#1" means agent-09, "#2" means agent-06, and "3rd" means agent-03. The versions shown are the ones reviewed. A later version must add only reviewer-requested edits.

| Section | Content | File (author) | #1 | #2 | 3rd | Other checks |
|---|---|---|---|---|---|---|
| PC | the single line-numbered algorithm text | agent-04 pseudocode.md (FROZEN PCv2.3) | CORRECT (v2.3, gate G1) | CORRECT (v2) | implementable (v2) | editor line-by-line check; six implementations |
| S1 | 5-tuple version-stamped labels (full walk order); admissible instances; deadline instance D1–D3; SP/SP'; Claim C; L3+; depth induction | agent-02 L1_foundations.md (FROZEN S1v2.6) | CORRECT (v2) | CORRECT (v2.5; s1–s4 addressed in v2.6) | CORRECT (v1); frozen v2.6 re-reviewed 07:55: CORRECT | editor re-read §D (v2.5); STRONG D2 executable test (agent-02: 3840 runs, 0 fails) |
| S2 | corrected BMSSP core; Lemma S2.1 (R1–R9), Cor. S2.2/S2.3; Lemma S2.4 scan; Lemma S2.5 insertion events | agent-08 S2_core.md (FROZEN S2v1.3) | CORRECT (v1.0; N1–N6 addressed) | CORRECT (v1.1 + v1.2 delta; c1–c5 addressed) | CORRECT (v1.0) | editor_check_S2.md (Appendix X2); independent proof agent-02 (Appendix X1) |
| S3 | FindPivots-D and FindPivots-B satisfy FP; Theorem S3.6 | agent-08 S3_findpivots.md (FROZEN S3v1.4) | CORRECT (v1.0; T1–T5 addressed in v1.4) | CORRECT (v1.1; t1–t4 addressed) | CORRECT (v1.0) | editor read (v1.1); agent-01 executable cross-check; agent-04 nested-depth evidence |
| S4 | time and space; F1–F9 discharge; Lemma G2; depth-3 Lemma M | agent-05 S4_final.md (FROZEN S4final) + cost_analysis.md v5 (FROZEN, Appendix E2) | CORRECT (v3) | CORRECT (v4) | CORRECT (v3) | agent-01 independent re-derivation; S4_final checked by its author against frozen PCv2.3 |
| S5 | block structure D with Delete (Lemma DS), membership stacks (Lemma MS), space, pre/post-processing | agent-04 S5_data_structure.md (FROZEN S5v1.2) | CORRECT (v1; v1.2 consistent) | CORRECT (v1.1) | reviewed v1: **found the Merge-chunking bug** (a chunk closed inside an unordered D′-block breaks SEP; agent-04 confirmed it 300/300). Fixed in v1.2, and v1.2 is CORRECT | agent-02 extra review of v1.2: statement-level corner case M-5 (§6b), confirmed by agent-06 |
| A′ | dispatcher GM.0–GM.9 plus the SS.7′ checkable test with Lemma N0 | agent-04 pseudocode_addendum_GM.md (FROZEN PCGMv1.2) | checked 07:54:59 (correctness by S2 + S3 §3.1; PLAIN time by S4-T) | +1, resolves A1/A2 (07:55:55); delta review of master v1.2: CORRECT (08:01:49) | +1 (07:54:18) | N-versions by agent-04 (tests_gm 300/0; the editor re-ran it: 300/0), agent-07 (1632/0) and agent-01 (PLAIN, 1000/0) |
| E3 | Cor. S4-GM, the dispatcher time bound | agent-05 S4_addendum_GM.md (FROZEN S4GMadd) | agrees (M1 option A) | +1 (PLAIN time check) | CORRECT (07:57:01) | agent-08 informal re-check CORRECT |
| S6 | tests (§7) | six codebases; report FROZEN S6final (Appendix G) | — | — | — | final editor re-run on frozen PCv2.3, all pass |
| S7 | novelty (§8) | agent-02 S7_novelty.md v2 + source_map.md v2 (FROZEN) | independent check (agent-09) | — | independent check (agent-03) | independent checks by agents 01, 04, 05 and 10; pre-claim re-run by agent-02 (arXiv cs.DS to Sep 18) |

## §4 The FindPivots contract FP (the interface between S2 and S3), final wording

**Context.** X = BMSSP(B, S, l) is a call on an admissible instance I. At its start:
- (C1) Claim C holds;
- (C2) ⟨∅, S⟩ is a frontier for Ũ := Ũ_I(B, S);
- (C3) d[x] ≺ B for every x ∈ S.

FindPivots(B, S), with an integer k ≥ 1 (the time bounds use k ≥ 2), returns sets P_1..P_p, Q and W such that:
- **FP1.** ⟨W, P_1 ∪ … ∪ P_p⟩ is a frontier for Ũ, with completeness measured at the return.
- **FP2.** P_1, …, P_p and Q are pairwise disjoint and nonempty, and their union is S.
- **FP3.** Q ⊆ W ⊆ Ũ, and W = ⋃_{x∈Q} W_x with x ∈ W_x and |W_x| < k.
- **FP4.** There are pairwise vertex-disjoint pre-partition trees F̄, each with ≥ k vertices, inside Ũ, over edges of the instance graph. Their Lemma A.1 pieces F_1..F_p are edge-disjoint, with P_j ⊆ V(F_j) and |V(F_j)| < 3k. Moreover p ≤ |S| and p ≤ Σ(|V(F̄)| − 1)/(k − 1) ≤ |Ũ|/(k − 1).
- **FP5 (SP).** Every Relax(u, ·) has u ∈ S or u touched earlier in X. Hence, by S1 L3+, every changed vertex, tree vertex and W-vertex lies in Ũ.
- **FP6.** No operation on any D structure of the host recursion.
- **FP7 (time).**
  - FindPivots-D: O((Σ_T |V(T)| + |S| + k|Q|)(δ + log k)).
  - FindPivots-B: O(g·min(|Ũ|, 8k|S|) + min(|Ũ|, g·k·|S|) + g|S| + g·k·|Q|).
  - Both are O(g|U| + t|Q|) under S4's coupling k·g ≤ 2C_g t.

S2 uses only FP1, FP2, FP3 (W ⊆ Ũ), FP5 and FP6. The time analysis uses FP4 and FP7. S3 proves FP1–FP7 for FindPivots-D on every admissible instance, and for FindPivots-B on every admissible host (Theorem S3.6).

**Decisions fixed by the editor, with the reasons given on the board.**
- Labels are S1's version-stamped 5-tuples (len, hops, v, e, ver[tail]). They realise the exact full walk order, and ancestor-closure holds (S1 A2′).
- Walls use SUPPRESSION (RX.4–RX.5).
- FIX-STALE is implemented by deletion (BM.15, BM.29).
- The pivot invariant is S2's certification (b), which is required only for COMPLETE P-vertices. This avoids the failure of DMSY26's "d[p_j] ≤ d_B[P̂_j]" under stale stored values (editor_check_S2.md).

## §5 The algorithm (overview; the precise text is Appendix A = PCv2.3)

- **Driver and dispatch** (SS.1–SS.13 plus Appendix A′). BFS prune, then GM.0 multigraph reduction, then the O(1) dispatcher (BOOT = PCv2.3 with δ = 3; PLAIN = corrected DMSY26 with a general δ), then the SS.7′ side-constraint test (Dijkstra fallback below n_0), then the main call, then the map-back.
- **Main recursion** BMSSP (BM.1–BM.31). This is DMSY26 Alg. 3 with the fixes FIX-STALE (BM.15, BM.29), FIX-RESEL (BM.23), FIX-EMPTY (BM.24a), FIX-SIZE (3k ≤ t), the owner-aware membership lookups (BM.12/17/22/30), and the base case with FIX-BASE (BC.1–BC.9).
- **FindPivots-B** (FB.1–FB.21), used by the outer recursion. For each x ∈ S not already in a tree:
  1. Run InnerSearch(x) = BMSSP(B, {x}, l_in, P_in, τ := k) on the global labels, with walls on the vertices of the trees built so far.
  2. If a hit was recorded, merge N_x into the hit tree via the hit edge (FB.11–FB.14).
  3. Otherwise, if the search was partial or |U_x| ≥ k, create a new tree on N_x with the edges tpar0 (FB.15–FB.17).
  4. Otherwise the search failed: W_x = U_x, and x ∈ Q (FB.18–FB.19).
  5. Finally partition the trees and form P_j (MP, PT).
- **FindPivots-D** (FD.1–FD.21) is DMSY26 Alg. 2 (Fibonacci-heap local Dijkstra), used inside inner searches.
- **Parameters** (pseudocode §8.2):
  - t = ⌈(log n')^{1/2}(log log n')^{1/4}(log log log n')^{1/4}⌉ and g(t) = ⌈√(log t · log log t)⌉;
  - k = ⌊t/(3g)⌋;
  - t_in = ⌈√(log k log log k)⌉ and k_in = ⌊t_in/(3 log t_in)⌋;
  - l_in = min{l ≥ 1 : t_in³ 2^{l·t_in} ≥ k}.

## §6 Errata to DMSY26 (arXiv 2602.07868v2) found by the team

Fix names are unified across sections.

| # | DMSY26 location | problem | fix | found by | evidence |
|---|---|---|---|---|---|
| E1 | Alg. 3 Lines 15–20; Lemma 3.7 invariant 2; Lemma 3.8; Obs. 3.5 | settled U_i keep stale D entries, so U_i overlap and Line-24 insertions repeat; the time analysis is invalid as written | **FIX-STALE**: delete U_i/W' from D (or a per-instance done-filter at Pull) | agents 08, 03, 02, 01, 09, 06 (independently) | agent-03: 239 overlaps in 200 graphs, 0 after the fix; agent-01: 226 → 0; agent-09: 4276 double settles in 660 runs; agent-06: 213k duplicate U memberships in 200 graphs |
| E2 | Alg. 4 (base case) | B' is taken from the last Pull, but the last vertex's relaxations can insert keys below it. The call then claims FULL with D nonempty, so Lemmas 3.1/3.7 fail. Combined with FIX-STALE as a done-filter this gives **wrong output** | **FIX-BASE**: check the threshold before extracting; B' := min stored value in D, else B | agents 01, 04, 09, 06 | agent-09 witness_F2_replay.py (3×3 bidirected grid). Independently reproduced in agent-06's codebase with tests/e2_min.py, a 5-vertex multigraph with t = 1, k = 2: done-filter without FIX-BASE gives WRONG output, with FIX-BASE it is correct, and the fully literal version is correct. |
| E3 | Alg. 3 exit | D is empty after a partial last sub-call, yet B' ≠ B | **FIX-EMPTY**: B' := B | agent-03 | agent-03 exp |
| E4 | Lemma 3.1 / Line 13 | the frontier grows by < 3k per pulled pivot (constants only) | **FIX-SIZE**: 3k ≤ t | agents 09, 10, 05, 04 | note_I2_I7.md |
| E5 | Remark 3.3; Sec. 2.5 "R ⊆ Ũ" | stated without proof; needs an invariant | **FIX-INV**: Claim C with confinement L3+ (S1 §D; S2 Step 2) | agents 06, 02, 09 | agent-09 debug2.py (multi-root counterexample) |
| E6 | Sec. 2.3 tie-breaking; proof of Obs. 2.1(4) | 4-tuples do not realise the full path order: a comparison against a bound derived from the same vertex goes wrong, and ancestor-closure fails | **FIX-TIES**: version-stamped labels. The Obs. 2.1(4) statement also has a 4-tuple proof (first Y-vertex) | agents 10, 09, 01, 02 | agent-09 cmp_modes.py; counterexample in the board ruling |
| E7 | Lemma 3.4 | "M ≥ log(N/M)" fails at l = 1; only log(N/M) = O(M) is needed | restate the requirement (S5 (A_M)) | agent-04 | |
| E8 | Alg. 3 Lines 19/28 | re-selection from a P_j emptied later in the same U_i takes argmin over ∅ | **FIX-RESEL**: re-select only if P_j ≠ ∅ | agents 08, 04, 07 (independently) | agent-07: crash in 201/468 runs without the guard |

## §6b Statement-level corrections to frozen sections (no algorithm change)

- **S5 v1.2, Lemma DS, Merge precondition (i).** Reported by agent-02 as M-5 and confirmed by agent-06.
  - *Replace* "every stored value of D′ < every stored value of D" *by* "every stored value of D′ is < the smallest stored value of D, **and** D's first block is non-empty or D is a single empty block".
  - The SEP argument for the chunk blocks needs D′ < s_2, the separator of D's second block. That holds under the restated precondition.
  - **The only call site, BM.14, satisfies it.** Between BM.10 and BM.14, D is untouched. After a Pull with |D| > M, the first block is R ∋ x = B_i, and every D′ value is ≺ B_i = min(R) < s_2. After a Pull with |D| ≤ M, D is a single empty block.
  - Equivalently, Merge may first discard empty leading blocks, charged to their creation.
- **pseudocode_addendum_GM.md v1.2, line 43.** Wording nit from agent-05's 07:56:40 post; no semantic change.

## §7 Tests (S6): independent, exact, reproducible

- **Setup.** Six independent codebases, all using exact arithmetic (Python ints and Fractions).
- **Oracles.** Binary-heap Dijkstra, Bellman–Ford, and an oracle-free certificate checker. Most codebases also assert the lemma-level invariants on every call, against an exact oracle of that call's instance, including every inner deadline instance.
- **Status.** Finite tests are evidence, not proof.
- **Editor re-runs.** The editor re-ran every suite at 07:44–07:50 UTC, and again for the final record at 07:51–07:56 UTC after PCv2.3 was frozen.
- **Final re-run results.** In **Appendix G (FROZEN S6final)**, with raw logs in agents/agent-10/work/s6_runs/ and the runner at s6_final_rerun.sh. Highlights:
  - agent-07: 1040 runs, 0 failures, no violations (full-walk shadow checker);
  - agent-01: 92 × 4 configs, 0/0;
  - agent-04: 200 + 60 deep-nesting runs, 0 fails;
  - agent-09: 1485 runs, 0 fails;
  - agent-08: 3 × 300 OK;
  - agent-06: 1656 runs, 0 wrong.
- **Dispatcher (A′).** Editor re-run of `cd /research/agents/agent-04/work/impl && python3 tests_gm.py 300`: 300 runs, 0 fails. It covers both branches: BOOT with δ = 3, and PLAIN with δ ∈ {3, 4, 6, 10}. Also agent-07 N-version of GM v1.2: 1632 runs, 0 fails, δ ∈ {3, 4, 5, 8}. agent-01 PLAIN: 1000 runs, 0 fails.
- **agent-09 strict frozen-PC mode** (M3). Editor re-run of `cd /research/agents/agent-09/work/impl && PC=1 python3 run_tests.py quick 13`: 1485 runs, 0 fails. This mode uses deletion FIX-STALE, BC.5, BM.24a, FB hits and N-trees.
- **Tester-independent differential checks.** agent-03, who wrote none of the implementations, ran agents/agent-03/work/xcheck/xcheck.py with its own generators, reference and certificate: 5750 bootstrapped plus 3299 plain runs of the PC-faithful agent-04 and agent-07 implementations, 0 wrong and 0 certificate failures.
- **Further evidence.**
  - agent-08's TV variant (exact frozen-PC label order with a full-walk shadow checker): 2250 trials, 0 violations. It also caught a version-order mutant.
  - agent-06 independently reproduced E2 in its own codebase: done-filter without FIX-BASE gives the wrong answer on a 5-vertex witness.
  - agent-02's STRONG D2 test: the inner-run trace on H equals the same code run on the constructed G_x. 3840 runs, 0 fails, mutation-sensitive.
- The table below records the first round of re-runs.

| impl | author | semantics | command (run from the listed directory) | editor re-run result |
|---|---|---|---|---|
| sssp/b1.py | agent-07 | PC line-tagged; full-walk shadow checker; nesting depth 0/1/2; suppress and sink; raw and δ = 3 | `cd /research/agents/agent-07/work && python3 tests/run_b1.py --seeds 1 --check --quick` | runs = 520, failures = 0, violations NONE; every FB path (merge, new, failed) exercised |
| impl/bmssp.py | agent-01 | master semantics; asserts Claim C, L3+, FP, S2 invariants, Obs. 3.5, Q-bound | `cd /research/agents/agent-01/work/impl && python3 run_tests.py 3 31 master_t2k2,master_t1k4,dmsy26_fixed` | 69 graphs × 3 configs: 0 bad, 0 viol |
| impl/bsssp.py | agent-04 | mirrors PC tags; exact S5 structure; inner deadline-instance oracle | `cd /research/agents/agent-04/work/impl && python3 tests_full.py` | 200 runs, 0 fails; agent-09 witness replay OK |
| impl/bmssp.py | agent-09 | fast 5-tuples vs explicit full-path labels; nesting depth 1/2 | `cd /research/agents/agent-09/work/impl && python3 run_tests.py` | 1089 runs, 0 fails |
| impl/bdmsy.py | agent-08 | S2 listing; per-call oracle asserts | `cd /research/agents/agent-08/work/impl && python3 test_bdmsy.py` | classic, B and B_sink: 200 trials each, OK (check=True) |
| a06_dmsy26.py | agent-06 | modes dijkstra / fresh / boot; exact invariant checker | `cd /research/agents/agent-06/work && python3 tests/test_modes.py` | 1656 runs, 0 wrong; violations only in the deliberately naive 'fresh' mode (negative control for obstruction O1) |

**Families covered.**
- Zero-weight SCCs and cycles, and massive (len, hops) ties.
- Parallel edges, self-loops, and isolated or unreachable parts.
- Brooms, hubs, (bidirected) grids, layered DAGs, and paths with back edges.
- Huge and tiny Fractions, and a Bellman–Ford adversary.
- zero_cycle_leaves (the O1 family), stale_chain (the E1 family), and pivot-defeating families.

**Errata witnesses.**
- E1: agent-08 gap_demo.py, agent-03 exp/stale_check2.py, agent-06 tests/test_stale.py.
- E2: agent-09 witness_F2_replay.py.
- E8: runs without the BM.23 guard.

## §8 Novelty (S7). Dated 2026-09-20; must be re-run before the claim

**Directed frontier.** DMSY26 (arXiv 2602.07868v2, Feb 2026; ICALP 2026) gives O(m√log n + √(mn log n log log n)). No v3 exists, and no later directed worst-case improvement was found. The papers citing it (Semantic Scholar, via agent-04) are:
- Kadria–Roditty, 2609.15247;
- Bin Cai, 2609.04825;
- 2609.14126 (unrelated);
- 2607.19346 (not comparable).

**Kadria–Roditty (arXiv 2609.15247, 2026-09-14).** Undirected, RANDOMIZED, O(m√log n (LL·LLL)^{1/4}).
- Their BoundSSSP (Lemma 7 / App. B) is DMSY26's BMSSP used as a fresh-label bounded search. It is prior art for "BMSSP as a local search", and we credit it.
- Their Sec. 4 leaves the directed and deterministic cases open, with BundleDijkstra as the named directed obstruction.

**What is new here.**
1. Bootstrapping DMSY26's OWN FindPivots.
2. Deadline instances on the global labels. Fresh labels provably fail here: agent-06's O1 gives Θ(n log n).
3. Suppression walls with merges, and the cap τ = k.
4. The resulting deterministic directed bound.
5. The errata E1–E8.

**Bin Cai (arXiv 2609.04825).** Instance-dependent OPT_DIST bounds only; not a worst-case competitor.

**Hair–Li–Li–Zhang (arXiv 2607.19346).** Real, possibly negative, weights. Las Vegas randomized, time m^{1+o(1)} with m^{o(1)} = 2^{O(√(log n log log n))} (their Thm 1.1, verified by agent-02). That factor is far above polylog, so the result is not a competitor for nonnegative weights.

**Other 2026 items.** Different problems: negative integer weights, n^{2+o(1)} negative real weights, DAG preservers, and power-law graphs.

**Lesson (agent-09 M5).** Title-only scans miss papers: agent-09's July scan missed 2607.19346. Citation graphs and abstract search are needed too.

**Searches.** agent-02 (web and arXiv cs.DS listings, Aug–Sep 2026), agent-04 (Semantic Scholar citations), agent-01 (web and arXiv), agent-09 (arXiv cs.DS Mar–Sep 2026, targeted web searches), agent-03 (web and the arXiv recent listing), and agent-10 (web, arXiv title search, and the 2607.19346 main theorem).

## §9 Completion gate (native /goal and GOAL.md)

| Gate | Status |
|---|---|
| G1 precise implementable pseudocode | DONE: PCv2.3 frozen (#1 agent-09 v2.3; #2 agent-06 v2; 3rd implementable), plus dispatcher addendum A′ frozen (PCGMv1.2; #1 checked, #2 +1); six implementations follow PC, and three follow A′ |
| G2 correctness: ties | DONE: S1 §A (FIX-TIES); reviewed by #1, #2 and 3rd |
| G3 correctness: zero weights and zero cycles | DONE: hops component, strict growth (S1 T2); tested on zero-SCC families |
| G4 correctness: unreachable, isolated, parallel edges, self-loops | DONE: BFS prune (SS.2); labels stay ∞ (Cor. S2.2); self-loops dropped (SS.4); parallel edges ordered by edge ids (S1 §A) |
| G5 inner run = core on I_x | DONE: S1 D1–D3 + SP'; reviewed by #1, #2 and 3rd |
| G6 FindPivots-B satisfies FP | DONE: S3 (FROZEN v1.4) reviewed CORRECT by #1, #2 and 3rd |
| G7 corrected core | DONE: S2 reviewed CORRECT by #1, #2 and 3rd; independent proof by agent-02 |
| G8 worst-case time, including preprocessing, output, base case and inner overheads | DONE: S4 reviewed by #1, #2 and 3rd; F1–F9 discharged (S4 §13); dispatcher time Cor. S4-GM (E3; 3rd CORRECT; #1/#2 agree); GM.0 multigraph step O(m) |
| G9 space O(n+m) | DONE: S4 §8, S5 Lemma MS; reviewed |
| G10 strict improvement on general sparse inputs | DONE: S4_final Cor. S4-S; strict range m/n = o(√(LL/LLL)) by Cor. S4-GM; never worse than DMSY26; convention §2 |
| G11 novelty vs current literature | DONE. Six independent searches; agent-02's pre-claim re-run (arXiv cs.DS recent/new through Fri Sep 18, cs.DM, web); **claim-time re-checks** by agent-04 (~08:03 UTC: full cs.DS recent listing, 139 entries, Sep 14–18; Semantic Scholar citations of 2602.07868 unchanged; web) and agent-10 (~08:02 UTC: web searches). No competitor. arXiv does not announce on weekends, so no newer listing exists |
| G12 independent reproducible tests | DONE: final editor re-run of six codebases on frozen PCv2.3 (Appendix G; logs in s6_runs/): 0 wrong outputs; 0 invariant violations outside the deliberate negative control |
| G13 two substantive independent reviews recorded on the board | DONE. Every section has #1 agent-09 and #2 agent-06 CORRECT, plus agent-03 third. Integrated body: the v1/v1.1 reviews found M1/A1/A2 (fixed in v1.2); the delta verdicts are **#1 agent-09 CORRECT (08:02:11, v1.2/v1.2.1)** and **#2 agent-06 CORRECT (08:01:49, v1.2)**. Review files are frozen (R1–R27) |
| G14 every identified gap resolved | DONE. Tracker I1–I22 are resolved. Section-review items are addressed in the frozen versions. Integrated-review items M1/A1, A2, M2–M5, agent-03 1–3, agent-06 F1–F5 and M-5 (§6b) are resolved, **confirmed by both delta verdicts, which report no open gaps** |


---

# APPENDICES (frozen section texts; digests verify against frozen/MANIFEST.tsv)


## Appendix A — Pseudocode (agent-04), the single algorithm text

Frozen label `PCv2.3`, source `/research/agents/agent-04/work/pseudocode.md`, sha256 `970ce218d4256daa3e5e90c7c90a69918f6c473afe0ae738d595ee82550806d7`, frozen 2026-09-20T07:48:35Z.

# Implementable pseudocode: bootstrapped DMSY26 (BMSSP with FindPivots-B)

agent-04, v2.2, 2026-09-20 (v2: aligned to S1 v2.2 = version-stamped labels + SUPPRESSION sinks (editor: final); v2.1: review nits of agent-02/agent-10 applied, FIX-RESEL naming, BM.29 remark; v2.2: agent-03 review: explicit Pmem owner test (I20), tree-size note; v2.3: agent-06 formal review q1-q4, owner test written on the lines themselves). This is the single line-numbered algorithm text for the integrated document (agent-08 integrator).
Proofs in S1 (agent-02), S2/S3 (agent-08) and S4 (agent-05) should cite lines such as `BM.10`.
S5 (data structure, `S5_data_structure.md`) and the space/preprocessing/output accounting (Sec. 9 below) are mine.
**Status: pseudocode, not a proof.** Deviations from DMSY26 (arXiv 2602.07868v2) are marked **[FIX-x]** or **[NEW-x]**.

---------------------------------------------------------------------------------------------------
## 0. Conventions

- Model: comparison-addition on edge weights. Integers (ids, hop counts, sizes, levels, timestamps) use ordinary RAM operations.
  This is legal because they are not weights.
- **Labels** (S1 v2.2 Sec. A, [FIX-TIES]) are `INF` or 5-tuples `(len, hops, v, e, a)`:
  - `len` is a real and `hops` an int;
  - `v` is the labelled vertex and `e` the last edge (edge ids are distinct, so parallel edges are distinguished);
  - `a` is the version `ver[tail(e)]` at the time the label was written.
  The source label is `(0, 0, xs, NOEDGE, 0)`. `ver[v]` starts at 0 and is incremented exactly when `d[v]` strictly decreases.
- **Order** `cmp(lam, mu)`:
  - compare `(len, hops)` lexicographically, then `id(v)`, then `id(e)` (with `NOEDGE` smallest);
  - if all of these are equal, the label with the LARGER version is smaller;
  - equal versions mean the same represented walk, and `INF` is the maximum.
  This decides the full walk order of the represented walks (S1 v2.2), using one real comparison plus O(1) integer comparisons. `<=` means `<` or equal.
- For an edge `e = (u, v, w)`: `d[u] (+) e := (d[u].len + w, d[u].hops + 1, v, e, ver[u])`, which costs one real addition.
  `INF (+) e := INF`.
- Global arrays over V(H), where H is the preprocessed graph: `d[.]` (label), `ver[.]` (version). The output predecessor of v is `tail(d[v].e)`.
- A timestamp mark `mark_X[v] = id` means v is in set X of invocation id. New ids come from one global counter and are never reused.
  So "clearing" a mark set costs O(1).

---------------------------------------------------------------------------------------------------
## 1. Relax, Out, touch hook (global)

```
RX.1  Relax(u, e=(u,v,w), B):
RX.2      cand := d[u] (+) e
RX.3      if not (cand <= d[v] and cand < B): return False
RX.4      if HOOK != 0 and sinkstamp[v] = ZSTAMP:      # SUPPRESSION (S1 v2.2 Sec. C): would-be-valid
RX.5          hitlist.append((u, e)) ; return False      #   relaxation into a sink: record hit, do not relax
RX.6      if cand < d[v]: d[v] := cand ; ver[v] := ver[v] + 1   # strict decrease
RX.7                                                     # else cand = d[v]: re-confirmation, no change
RX.8      if HOOK != 0: TouchHook(v)
RX.9      return True                                    # "valid relaxation"; v is "touched"

OU.1  Out(u): return the list of out-edges of u in H     # (no sink test needed under suppression)
```
- `HOOK != 0` holds exactly during an InnerSearch (FB.6).
- The sink set is `Z = {v : sinkstamp[v] = ZSTAMP}`, the vertices of the F-bar trees built so far in the current FindPivots-B.
- Under suppression a sink is never touched. So sinks never enter any inner structure and are never scanned. Hence `Out` needs no test, and the inner run is literally a run on `H - Z` except for the hit records (S1 D2).
- Re-confirmation (RX.7) counts as a touch but changes nothing, not even `ver`.

---------------------------------------------------------------------------------------------------
## 2. Parameter records

A record `P = (t, k, FP, depth)` holds:
- `t`, the level-size parameter;
- `k`, the tree size for pivots;
- `FP`, the FindPivots routine: `FindPivots-B` for the outer algorithm, `FindPivots-D` for the inner one;
- `depth`, the bootstrap depth: 0 = outer, 1 = inner. It selects the per-depth mark arrays.

Level-l workload: `Lambda(P, l) := P.t^3 * 2^(l*P.t)`. Pull size: `M(P, l) := P.t * 2^((l-1)*P.t)` for l >= 1.

Requirement **[FIX-L13]**, equivalent to the master's FIX-SIZE up to constants: `3*P.k <= P.t`.
Then the Line-13 expansion gives `|S_i| <= M(1 + 3k - 1) = 3kM <= t^2 2^((l-1)t)` (each pulled pivot adds fewer than 3k vertices), so the DMSY26 bound `|S| <= t^2 2^{lt}` holds verbatim.
Also "partial => |U| > t|S|" holds. The master's alternative is sigma_l = 4t^2 2^{lt}, which gives |U| > t|S|/4. Either works; this is agent-09's I2.

---------------------------------------------------------------------------------------------------
## 3. Main recursion BMSSP (DMSY26 Alg. 3 with fixes)

`BMSSP(B, S, l, P, tau)` returns `(B', U, D)`. Here tau is the workload cap:
- normally `tau = Lambda(P, l)`;
- only the top call of an InnerSearch uses `tau = k_outer` [NEW-CAP].

```
BM.1   BMSSP(B, S, l, P, tau):
BM.2     if l = 0: return BaseCase(B, S, P, tau)
BM.3     D := NewDS(M := M(P,l), bound B)                         # Sec. S5; owner id = new id
BM.4     (Pl[1..p], Q, W) := P.FP(B, S, P)                        # FindPivots-B (depth 0) / FindPivots-D (depth 1)
BM.5     for j := 1..p:
BM.6         for x in Pl[j]: PushPmem(x, owner=this call, j)       # nested P-membership (S5 Sec. 4)
BM.7         piv[j] := argmin_{x in Pl[j]} d[x] ; D.Insert(piv[j], d[piv[j]])
BM.8     B' := min(B, min_j d[piv[j]]) ; U := empty ; J := empty
BM.9     while |U| <= tau and not D.IsEmpty():
BM.10        (Si, Bi) := D.Pull()
BM.11        for x in (keys pulled at BM.10):                      # expansion (DMSY26 Line 13)
BM.12            j := Pmem(x, owner=this call) ; if j != none and piv[j] = x: Si := Si + {v in Pl[j] : d[v] < Bi}
BM.13        (B'i, Ui, Di) := BMSSP(Bi, Si, l-1, P, Lambda(P, l-1))
BM.14        D.Merge(Di)
BM.15        for u in Ui: D.Delete(u)                              # [FIX-F1] agent-08 GAP / agent-03 A3-1
BM.16        for u in Ui:
BM.17            j := Pmem(u, owner=this call) ; if j != none: remove u from Pl[j] ; PopPmem(u, owner=this call)
BM.18                if piv[j] = u and Pl[j] nonempty: J := J + {j}
BM.19        for u in Ui: for e=(u,v,w) in Out(u):
BM.20            if Relax(u, e, B) and d[u] (+) e >= Bi:
BM.21                D.Insert(v, d[v])
BM.22                j := Pmem(v, owner=this call) ; if j != none and j not in J and d[piv[j]] > d[v]: piv[j] := v
BM.23        for j in J: if Pl[j] nonempty: piv[j] := argmin_{x in Pl[j]} d[x] ; D.Insert(piv[j], d[piv[j]])   # [FIX-RESEL]
BM.24        B' := B'i ; U := U + Ui ; J := empty
BM.24a   if D.IsEmpty(): B' := B                                   # [FIX-EMPTY] (agent-03, master E3)
BM.25    for x in S: if B' <= d[x] < B: D.Insert(x, d[x])
BM.26    W' := {x in W \ U : d[x] < B'}
BM.27    for u in W': for e=(u,v,w) in Out(u):
BM.28        if Relax(u, e, B) and d[u] (+) e >= B': D.Insert(v, d[v])
BM.29    for u in W': D.Delete(u)                                  # [FIX-F2] provably a no-op (S2 (R3)); kept for safety
BM.30    for j := 1..p: for x in Pl[j]: PopPmem(x, owner=this call)  # remove this call's remaining P-entries
BM.31    return (B', U + W', D)
```
Notes.
- **Pmem owner test (I20; agent-03).** `Pmem(v)` means: j if the TOP record of memP[v] has owner = this call, else `none`.
  BM.22 can relax a vertex v that is a P-member of an ANCESTOR call without being in S of this call; the owner test keeps it from being mistaken for a member of this call's Pl.
  During this call's own lines no descendant is live (its records were popped at its BM.30), so testing the top record suffices (S5 Lemma MS).
  `PushPmem`/`PopPmem` carry the same owner.
- BM.12 tests `piv[j] = x` for the CURRENT pivot. A stale pivot key, one whose pivot was replaced at BM.22, triggers no expansion.
- BM.15 and BM.29 imply that no key of the returned U is in the returned D. BM.29 never fires: S2 (R3) proves it, and agent-01 observed 0 firings.
  FIX-STALE is implemented by DELETION, not by filtering the Pull. So Pull returns at least one key whenever D is nonempty, S_i is never empty, and every sub-call has |U_i| >= 1 or ends full (agent-09 S4-review R1).
- BM.22 compares the CURRENT label d[piv[j]] (DMSY26 Line 26). The proof uses S2's certified-(b) invariant (J3), equivalently the editor's (J4'); no change to the code. BM.14's Merge precondition holds on STORED values: D_i's stored values are `< Bi <=` every stored value left in D after BM.10 (S5 Lemma DS).
- `Pl[j]` is a doubly linked list. The P-membership entry of x stores its list node, so BM.17 costs O(1).
- In a depth-1 (inner) call, `Relax` suppresses relaxations into sinks and fires the touch hook. Nothing else differs.
- BM.23 [FIX-RESEL] (found independently by agent-08 and agent-04): j enters J at BM.18 while Pl[j] is nonempty, but later vertices of the same U_i can empty it before BM.23.
  DMSY26 Alg. 3 lines 27-29 would then take argmin over an empty set; its prose says "for each non-empty P_j from j in J". So the test is made here.
- BM.24a: if D is empty when the loop ends, no frontier remains below B, so the call is full.
  Without it, a last partial sub-call with empty D_i would make X report B' < B together with an empty D.

---------------------------------------------------------------------------------------------------
## 4. Base case (DMSY26 Alg. 4 with the cap fix)

**[FIX-BC]** DMSY26 Alg. 4 returns the bound x of the LAST Pull. But the last extracted vertex's relaxations can insert keys below x.
Then `max_U dis < B' <= d_B[D]` (Lemma 3.7.2) fails.
The fix tests the cap BEFORE extracting, and returns the current minimum.

```
BC.1   BaseCase(B, S, P, tau):
BC.2     D := NewBST(bound B) ; for x in S: D.Insert(x, d[x]) ; U := empty      # S5 Sec. 3 (M = 1)
BC.3     while not D.IsEmpty():
BC.4         (u, val) := D.FindMin()
BC.5         if |U| >= tau: break                                   # u stays in D
BC.6         D.Delete(u) ; U := U + {u}
BC.7         for e=(u,v,w) in Out(u): if Relax(u, e, B): D.Insert(v, d[v])
BC.8     B' := B if D.IsEmpty() else D.FindMin().val
BC.9     return (B', U, D)
```
BC.2 inserts each x in S with its CURRENT label d[x], which may be smaller than the parent's stored value of x if that entry was stale (agent-06 q4).
So (K0) "stored value = current label" holds from the start. Inside BaseCase every label change goes through BC.7, which re-inserts. So stored value = current label for every key of this D, and BC is plain Dijkstra on its own D.
Output: full iff D is empty. `|U| <= tau`, and "partial" means `|U| = tau`.

---------------------------------------------------------------------------------------------------
## 5. FindPivots-D (DMSY26 Alg. 2, used by the INNER algorithm, depth 1)

Uses depth-1 mark arrays:
- `fmark1[v]` = invocation id if v is in an F-bar tree of this invocation;
- `ftree1[v]` = tree id;
- `kstamp1[v]` = id of the search whose K contains v;
- `kpar1[v]` = (parent, edge) inside the current K;
- `hstamp1` and the heap-node pointer for heap membership.

```
FD.1   FindPivots-D(B, S, P):
FD.2     id := new id ; trees := [] ; Wlist := [] ; Q := []
FD.3     for x in S:
FD.4         if fmark1[x] = id: continue
FD.5         sid := new id ; H := FibHeap{(x, d[x])} ; K := [x] ; kstamp1[x] := sid
FD.6         while H nonempty and |K| < P.k:
FD.7             u := H.ExtractMin()
FD.8             for e=(u,v,w) in Out(u):
FD.9                 if Relax(u, e, B):
FD.10                    if kstamp1[v] != sid: kstamp1[v] := sid ; K.append(v)
FD.11                    kpar1[v] := (u, e)                         # replaces v's old K-edge
FD.12                    if fmark1[v] = id:                         # hit an existing tree: merge and stop
FD.13                        T := ftree1[v] ; add K and edges {kpar1[y] : y in K, y != x} to T
FD.14                        for y in K: fmark1[y] := id ; ftree1[y] := T
FD.15                        goto NEXT
FD.16                    if v in H: H.DecreaseKey(v, d[v]) else: H.Insert(v, d[v])
FD.17        if |K| >= P.k: T := new tree (vertices K, edges {kpar1[y] : y in K, y != x}) ; trees.append(T)
FD.18                       for y in K: fmark1[y] := id ; ftree1[y] := T
FD.19        else: Wlist.append(K) ; Q.append(x)                    # failed search: H empty, |K| < k
FD.20      NEXT:
FD.21    return MakePivots(S, Q, trees, Wlist, P.k, depth=1)
```
- At FD.13 the vertex v is the only vertex of K already in a tree, so the union is a tree.
- K's edges are the current kpar1 edges. These are graph edges, and they form an arborescence rooted at x.

```
MP.1   MakePivots(S, Q, trees, Wlist, k, depth):
MP.2     sid := new id ; for x in S: inS_depth[x] := sid ; for x in Q: inQ_depth[x] := sid
MP.3     Pl := [] ; aid := new id
MP.4     for T in trees:
MP.5         for F in Partition(T, k):                              # Sec. 7: edge-disjoint subtrees, sizes in [k,3k)
MP.6             cur := [x in F : inS_depth[x] = sid and inQ_depth[x] != sid and assigned_depth[x] != aid]
MP.7             for x in cur: assigned_depth[x] := aid
MP.8             if cur nonempty: Pl.append(cur)                    # empty groups dropped (p <= |S|)
MP.9     W := concatenation of Wlist (a vertex may occur in several W_j; dedupe with a stamp)
MP.10    return (Pl, Q, W)
```

---------------------------------------------------------------------------------------------------
## 6. FindPivots-B (OUTER algorithm, depth 0) and InnerSearch   [NEW-FPB]

Uses depth-0 arrays:
- `sinkstamp[v]` (sink / F-bar membership), `ftree0[v]`, `tpar0[v]` (copied tree edge);
- `touched[v]`, with the lists `Tlist` and `hitlist` (hits are recorded by RX.4-RX.5).

The inner parameter record `Pin = (t_in, k_in, FindPivots-D, 1)` and the inner top level `l_in` are fixed in Sec. 8.

```
FB.1   FindPivots-B(B, S, P):                                       # P = outer record, k := P.k
FB.2     ZSTAMP := new id ; trees := [] ; Wlist := [] ; Q := []
FB.3     for x in S:
FB.4         if sinkstamp[x] = ZSTAMP: continue                     # x already in an F-bar tree
FB.5         TSTAMP := new id ; touched[x] := TSTAMP ; Tlist := [x] ; hitlist := [] ; HOOK := 1
FB.6         (B'x, Ux, Dx) := BMSSP(B, {x}, l_in, Pin, tau := P.k)  # InnerSearch(x): capped inner run
FB.7         HOOK := 0 ; Dx.Destroy()                               # pops Dx's membership entries
FB.8         full := (B'x = B)
FB.9         N := Tlist                                             # touched vertices plus x; no sinks (suppression)
FB.10        for v in N, v != x: tpar0[v] := d[v].e                 # COPY tree edges now: later searches may relax v
FB.11        if hitlist nonempty:                                   # merge case
FB.12            (u, e) := hitlist[0] ; z := head(e) ; T := ftree0[z]  # u in N, z a sink
FB.13            add vertices N, edges {tpar0[v] : v in N, v != x}, and edge e = (u, z) to T
FB.14            for v in N: sinkstamp[v] := ZSTAMP ; ftree0[v] := T
FB.15        elif (not full) or |Ux| >= P.k:                         # new-tree case
FB.16            T := new tree (vertices N, edges {tpar0[v] : v in N, v != x}) ; trees.append(T)
FB.17            for v in N: sinkstamp[v] := ZSTAMP ; ftree0[v] := T
FB.18        else:                                                  # failed: full, |Ux| < k, no sink touched
FB.19            Wlist.append(Ux) ; Q.append(x)
FB.20    ZSTAMP := 0
FB.21    return MakePivots(S, Q, trees, Wlist, P.k, depth=0)

TH.1   TouchHook(v):                                                # called from RX.8 while HOOK = 1
TH.2     if touched[v] != TSTAMP: touched[v] := TSTAMP ; Tlist.append(v)
```
Notes.
- FB.12: the hit's tail u is x or a touched vertex, by SP (agent-02 S1): every Relax(u, .) of the run has u = x or u touched earlier in the run. So u is in N.
  The tree edge e = (u, z) is an edge of H with both endpoints in U~(B, S) (S1 L3+ for u; z is in an earlier tree).
- FB.10: for every touched v, at the end of the run the tail of `d[v].e` is in N.
  - If the last write of d[v] happened in this run, its tail relaxed in this run, so it is x or touched earlier (SP).
  - Otherwise every touch of v in this run was a re-confirmation from some u: cand = d[u] (+) e = d[v], so d[v].e = e and tail(e) = u, which relaxed in this run.
  - Acyclic and rooted at x: if tpar0[v] = (u, v), then d[v] = (u's label at version a) (+) e is strictly greater than u's current label (S1 T2 and A3). So labels strictly decrease along tpar0 towards the root.
    x itself is never relaxed validly in its own run (A3 in I_x), so x is the unique root.
- Hit scope (agent-06 q2): hitlist collects hits from EVERY Relax executed during InnerSearch(x), at all inner levels: FD.9 (inner FindPivots-D), BM.20/BM.28 and BC.7.
  Failed-search exactness (S3.2.3) needs only the hits produced by the scans of completed vertices (S2 Lemma S2.4). FD.9 hits are extra and harmless: a hit only turns a would-be FAIL into a MERGE.
- Precedence (agent-06 q3): FB.11 chooses MERGE whenever a hit was recorded, even if the inner run was partial or |Ux| >= k. This is fine: N joins an existing tree, and S4 (3.2) covers both orders.
- FB.13 merges with ONE hit only (agent-06 G5). The merged vertex sets are disjoint from all trees, so the F-bar trees stay vertex-disjoint.
- In the new-tree case no hit happened, so `Ux` is contained in N and `|N| >= |Ux| >= k`.
  In the failed case `Ux = N` (full execution: agent-02 D1/D2).

Tree edges need not be shortest-path edges; DMSY26 uses them only for connectivity and charging (T5). They are graph edges with both ends in U~(B,S) (S1 L3+).
- `Dx` is discarded, and inner results never enter the outer D. This is what keeps the outer Q-accounting unchanged.
- Tree size (agent-03 review (3)): the tree built at FB.13/FB.16 has vertex set N = all touched vertices, which may exceed `|Ux| <= 8k`.
  |N| is bounded by the inner run's work, O(c_in k) = O(t). So S4's bound is `|union F-bar| <= min(|U~|, O(t)|S|)`, and all conclusions are unchanged.
- Inner calls nest D's and P-entries above the outer call's entries. The per-vertex stacks of S5 Sec. 4 keep all lookups O(1).
- HOOK and TSTAMP are global. FindPivots-B is never re-entered from inside an InnerSearch, because the inner algorithm uses FindPivots-D.
  So one set of depth-0 arrays suffices. Iterated bootstrapping would use one array set per depth.

---------------------------------------------------------------------------------------------------
## 7. Tree partition (DMSY26 Alg. 5 / Lemma A.1), iterative

```
PT.1   Partition(T, s):            # T: tree given by its vertex list and edge list (undirected); |T| >= s
PT.2     build adjacency lists of T ; r := any vertex ; groups := []
PT.3     iterative DFS from r; each frame f = (vertex v, parent, iterator, set Uv initialised to {v}):
PT.4       when child c returns set Uc to frame of v:  Uv := Uv + Uc
PT.5            if |Uv| >= s: groups.append(Uv) ; Uv := {v}
PT.6       when all children of v are done: return Uv to the parent frame
PT.7     rest := set returned by r
PT.8     if groups empty: groups := [rest] else: groups[last] := groups[last] + rest
PT.9     return groups                      # each group induces a subtree; sizes in [s, 3s) (Lemma A.1)
```
Sets are lists. `Uv + Uc` concatenates two lists that are disjoint as vertex sets, in O(1) with linked lists.
Total time O(|T|).

---------------------------------------------------------------------------------------------------
## 8. Driver, preprocessing, parameters, output

```
SS.1   SSSP(G = (V, E, w), s):                      # directed; w >= 0 reals; parallel edges/self-loops allowed
SS.2     Rch := vertices reachable from s (BFS over E)                          # O(n+m)
SS.3     for v in V \ Rch: dist[v] := INF ; pred[v] := BOT
SS.4     E_R := [(u,v,w) in E : u in Rch and u != v]                              # drops self-loops only
SS.5     (H, cyc, xs) := DegreeReduce(Rch, E_R, s)                               # Sec. 8.1; max in+out degree <= 3
SS.6     for x in V(H): d[x] := INF ; ver[x] := 0 ; d[xs] := (0, 0, xs, NOEDGE, 0)
SS.7     n' := |V(H)| ; if n' < n0: run binary-heap Dijkstra on H (same Relax, same order) ; goto SS.10
SS.8     choose (Pout, Pin, l_in, L) by Sec. 8.2
SS.9     (B', U, D) := BMSSP(INF, {xs}, L, Pout, Lambda(Pout, L))             # full execution (Lambda >= n')
SS.10    for v in Rch:                                                          # output back-mapping, Sec. 8.3
SS.11        e_v := argmin_{x in cyc[v]} d[x].hops
SS.12        dist[v] := d[e_v].len ; pred[v] := (v = s) ? BOT : orig(tail(d[e_v].e))
SS.13    return (dist, pred)
```

### 8.1 DegreeReduce (DMSY26 Sec. 2.1 with delta = 3)
For each v in Rch with total degree `Delta_v` (in + out over E_R, counting parallel edges):
- create `c_v := max(1, Delta_v)` new vertices `cyc[v] = (x_{v,1} .. x_{v,c_v})`;
- if `c_v >= 2`, add the zero-weight directed cycle `x_{v,1} -> x_{v,2} -> ... -> x_{v,c_v} -> x_{v,1}`;
- assign the incident edges of v to distinct cycle vertices, one each;
- for each edge `(u,v,w)` in E_R, add `(x_u, x_v, w)` between the cycle vertices assigned to that edge;
- set `orig(x_{v,i}) := v` and `xs := x_{s,1}`.

Every vertex of H then has at most 3 incident edges (<= 2 in, <= 2 out), and `n' <= 2|E_R| + |Rch|`.
Distances between vertices of the same cycle are 0. Vertex ids of H are 0..n'-1.
(The unreduced graph can be used for small-degree tests, since correctness does not depend on the degree.)

### 8.2 Parameters (asymptotic regime; any positive values keep correctness)
All logs are base 2 with `lg x := max(1, log2 x)`.
```
t     := max(2, ceil( lg(n')^(1/2) * lg(lg n')^(1/4) * lg(lg lg n')^(1/4) ))
g(t)  := ceil( sqrt( lg t * lg lg t ) )
k     := max(1, floor( t / (3 * g(t)) ))                 # outer tree size;  3k <= t   [FIX-L13]
L     := ceil( lg n' / t )                               # outer top level
t_in  := max(2, ceil( sqrt( lg k * lg lg k ) ))
k_in  := max(1, floor( t_in / (3 * lg t_in) ))           # inner FindPivots-D tree size; 3k_in <= t_in
l_in  := min{ l >= 1 : t_in^3 * 2^(l*t_in) >= k }        # inner top level (>= 1, agent-05 I1); cap tau = k (FB.6)
Pout := (t, k, FindPivots-B, 0) ; Pin := (t_in, k_in, FindPivots-D, 1)
```
For testing, any small values exercise the code paths: t = t_in = 2, k = k_in = 1, L = ceil(lg n'/t).
Correctness claims must not depend on these values; only the running-time analysis uses Sec. 8.2.
**Regime of the time analysis (agent-06 q1; S4 M1).** The running-time analysis assumes n' >= n_0.
- For such n' the Sec. 8.2 formulas give k >= 2 (FP4 uses p <= |union F-bar|/(k-1)), 3k <= t, k*g <= C_g t, k >= t_in, and Lambda_in(1) < k.
- Below n_0, SS.7 runs Dijkstra, which is O(1) time since n_0 is a constant.
- With the literal Sec. 8.2 formulas n_0 is astronomically large (S4 v5 M1: the constraints first hold around log2 n ~ 10^6 to 10^13). The improvement is purely asymptotic.

### 8.3 Output back-mapping
- `dist[v] = d[x].len` for every x in cyc[v]. All vertices of the cycle have equal length, because the cycle has zero weight and hops only break ties.
- `e_v` = the minimum-hop vertex of cyc[v], i.e. the minimum-(len, hops) vertex, since all gadget vertices have equal len. Its canonical predecessor `p*(e_v)` lies outside cyc[v] (or v = s): an inside predecessor would have the same len and fewer hops. Ties in hops are harmless.
  So `pred[v] := orig(tail(d[e_v].e))` is an original in-neighbour, and `d[e_v].e` is the image of an original edge, not a gadget-cycle edge.
- The edge is tight: `dist[v] = dist[pred v] + w`.
- `hops(e_{pred v}) < hops(e_v)`, so the pred graph is acyclic and rooted at s. This holds even with zero-weight edges and cycles in G.
- Cost: O(n' + n).

---------------------------------------------------------------------------------------------------
## 9. Space, preprocessing and output costs (agent-04, G9). Proof sketch; details in S5 Sec. 5

- H, d, pe, mark arrays: O(m + n) words.
- The live D's are those of the calls on the current recursion stack (outer levels L..0, plus inner levels l_in..0 during an InnerSearch), at most one per level.
  - `|D_X| <= N_X = O(t^4 2^{l t})` and `|D_X| <= n'`, so their sum is `O(n') + O(sum of a geometric series) = O(n')`.
  - The same holds for live P-entries (`|P_X| <= |S_X| <= t^2 2^{lt}`) and the U/W lists of live frames.
- The membership-stack entries equal the live D-keys plus P-entries: O(n').
- Trees of one FindPivots call are vertex-disjoint: O(n'). At most one Fibonacci heap is live at a time: O(k_in * delta).
- Total space **O(m + n)**. Preprocessing (BFS, self-loop removal, degree reduction): O(m + n). Output: O(m + n).


## Appendix A′ — Dispatcher addendum GM.0–GM.9 + SS.7′ + Lemma N0 (agent-04)

Frozen label `PCGMv1.2`, source `/research/agents/agent-04/work/pseudocode_addendum_GM.md`, sha256 `cb45aca8090e8b3919b79ad12e32930ab5ca26fd85a33d01d942de073c66c6e4`, frozen 2026-09-20T07:57:10Z.

# Addendum GM to FROZEN pseudocode PCv2.3: general-m dispatcher (needed for Theorem B1's "never worse than DMSY26")

agent-04, 2026-09-20, v1.2. This is a proposed addendum. It does NOT modify any frozen line of PCv2.3 (sha256 970ce218...806d7).
It adds lines GM.1–GM.9, which replace SS.5 and SS.8 of the driver when the dispatcher chooses the DMSY26 branch.

## Why it is needed

PCv2.3 §8.1 fixes the degree bound δ = 3 and §8.2 always bootstraps. For dense inputs this gives
O(m √log n (LL·LLL)^{1/4}), which is WORSE than DMSY26's O(m √log n) when m/n ≥ LL.
MASTER §2 claims "T is never worse than DMSY26". Its general-m formula comes from S4.9 / cost_analysis §6, and these assume:
- a degree bound δ = Θ(min(m/n, log log n)), and
- "taking the better of the two" variants.

Neither is in the frozen text. The goal-relevant SPARSE claim is unaffected.

## Lines

```
GM.0  (optional, only needed if m_R > n_R^2, i.e. heavy multigraphs; agent-05 remark)
      keep one minimum-weight edge per ordered pair (u, v): bucket E_R by (id(u), id(v)) with radix sort on
      integer ids, then take the minimum within each bucket with weight comparisons, ties broken by edge id.
      O(m) time. Afterwards m_R <= n_R(n_R - 1), so lg N = O(log n) in all bounds.
      A non-minimal parallel edge is never on a canonical path (S1 section A, edge-id order).
GM.1  (after SS.4)  n_R := |Rch| ; m_R := |E_R| ; LL := lg lg n_R ; LLL := lg lg lg n_R      # integer logs, O(1)
GM.2  if m_R <= n_R * floor( sqrt(LL / LLL) ) / c_GM :          # c_GM an absolute constant
GM.3       BRANCH := BOOT     # run PCv2.3 unchanged (SS.5 with delta = 3, SS.8 = Sec. 8.2, FindPivots-B)
GM.4  else:
GM.5       BRANCH := PLAIN    # corrected DMSY26: same BM/BC code, FindPivots-D at the top level
GM.6       delta := max(3, floor( min(m_R / n_R, LL) / 4 ))           # DMSY26 Sec. 2.1 / 3 choice
GM.7       DegreeReduce_delta: every v in Rch becomes a zero-weight directed cycle of
           max(1, ceil(Delta_v / (delta - 2))) vertices; each cycle vertex gets at most delta - 2 incident
           original edges (plus its two cycle edges). Then N <= n_R + 2 m_R / (delta - 2) = O(m_R / delta + n_R),
           and max in+out degree <= delta.
GM.8       t_D := max(2, ceil( sqrt( lg N * lg lg N / delta ) )) ; k_D := max(2, floor( t_D / (3 lg t_D) ))   # as S4_addendum_GM
           L_D := min{ L >= 1 : t_D^3 2^{L t_D} >= N } ; Pout := (t_D, k_D, FindPivots-D, depth = 0)
GM.9       SS.9 with Pout, then SS.10-SS.13 unchanged (the gadget map-back works for any delta: every gadget is a
           zero-weight cycle, and the min-hop vertex's canonical tail lies outside it)
```

- BRANCH = PLAIN is exactly the corrected DMSY26: BM/BC of PCv2.3 with FindPivots-D (FD, MP, PT) at the top level. It is the implementations' `plain` mode.
- Correctness: S2 Lemma S2.1 / Cor. S2.2, with S3 §3.1 (FindPivots-D satisfies FP on every admissible instance).
- Time: S4 Theorem S4-T with f = δ + lg k_D (the S4.9 "Dijkstra" row). This gives DMSY26's O(m √log n + √(m n log n LL)).
- DMSY26's simplifying side condition δ <= lg k is not needed by S4-T: f = δ + lg k is carried explicitly.

## Resulting theorem statement (proposed wording for MASTER §2)

    T(n, m) = O( n + m √log n + min{ √(m n log n · LL),  m √log n (LL · LLL)^{1/4} } ),

- The BOOT branch gives m √log n (LL·LLL)^{1/4}: after the δ = 3 reduction N = O(m_R), and PCv2.3 as frozen gives this for every m.
- The PLAIN branch gives DMSY26's bound.
- The dispatcher threshold GM.2 selects, up to constants, the smaller of the two.
- T is never worse than DMSY26.
- It is strictly better by a factor ω(1) exactly when m/n = o(√(LL/LLL)), which includes all sparse graphs.

The wider range m/n = o(√LL) of MASTER §2 v1 needs a THIRD branch: bootstrap with a general degree bound δ, inner group size k' = floor(t'/(3(δ + lg t'))) as in S4.9, and the matching outer/inner t. That branch has no pseudocode.
I recommend either:
- (a) stating the theorem with the range o(√(LL/LLL)) above, supported by existing reviewed sections plus this addendum; or
- (b) having agent-05 specify the general-δ bootstrap parameters so that it can be added as GM.10+ and reviewed.

For the goal, (a) suffices.

## SS.7' (agent-06 formal master review A2): a checkable fallback test replacing "if n' < n0"

```
SS.7'  compute the Sec. 8.2 parameters (t, g(t), k, t_in, k_in, l_in) from n'
       if NOT ( k >= 2  and  k >= t_in  and  t_in^3 * 2^(t_in) < k  and  3k <= t  and  3*k_in <= t_in ) :
           run binary-heap Dijkstra on H with the same Relax/label order (S1 labels) ; goto SS.10
       (BRANCH = PLAIN, GM.8: likewise fall back to Dijkstra if NOT (k_D >= 2 and 3 k_D <= t_D and delta <= lg k_D))
```

The last two conjuncts hold by the floors in the definitions of k and k_in. They are listed so that the test is self-contained.
The conjunct t_in^3 2^{t_in} < k implies l_in >= 2 as well as Lambda_in(1) < k. S4's relaxed form (t_in^3 <= k when l_in = 1) could replace it; the strict form is the simpler statement.

**Lemma N0.** There is an absolute constant n_0 such that for every n' >= n_0 the SS.7' test passes.
*Proof sketch* (agent-06 A2(i)):
- t ≥ (log n')^{1/2} and g(t) = O(sqrt(log t log log t)), so k ≥ t/(3g) − 1 = (log n')^{1/2 − o(1)} → ∞. In particular k ≥ 2 eventually.
- t_in = O(sqrt(log k · log log k)) = o(log k). Hence t_in^3 2^{t_in} = 2^{o(log k)} = k^{o(1)} < k, and t_in ≤ k, for all large k.
- Since k → ∞ as n' → ∞, all conjuncts hold for n' ≥ n_0. ∎

Hence the Dijkstra fallback is executed only on inputs with n' < n_0, and costs O(n_0 log n_0) = O(1) in the asymptotic statement.
The analysis (S4) applies whenever the test passes. Correctness never depends on the test (S2/S3 hold for all parameter values).
Estimates of n_0 for the literal formulas: S4 v5 M1 (astronomical; the result is purely asymptotic).

## Summary of what the addendum adds to FROZEN PCv2.3
- GM.1–GM.9: the O(1) dispatcher. BOOT = PCv2.3 as frozen; PLAIN = corrected DMSY26 with a general-delta gadget reduction.
- SS.7': a checkable n_0 test.

Both are implemented in impl/bsssp_gm.py (the dispatcher and general delta; tests_gm.py: 300 runs, 0 fails). SS.7' is a driver-level check.
The time proof of the dispatcher is agent-05's S4_addendum_GM.md (Corollary S4-GM), which is consistent with GM.1–GM.9.
(v1.2: k_D := max(2, .) and the PLAIN fallback conditions are aligned with it; GM.0 is the optional multigraph step.)


## Appendix B — S1 Foundations (agent-02)

Frozen label `S1v2.6`, source `/research/agents/agent-02/work/L1_foundations.md`, sha256 `e27edeaf7a655183d6853680bd67170a3f2a1b9556fb00dbc060c408bd457613`, frozen 2026-09-20T07:51:13Z.

# L1 + L3 foundations for bootstrapped DMSY26 (agent-02) — v2.6, 2026-09-20 (ties: version stamps; walls: SUPPRESSION (final); agent-09 R1–R5 and agent-06 s1–s4 addressed; SP verified vs pseudocode v2)

Drop-in section for agent-08's integrated document (bootstrapped FindPivots, "FindPivots-B").
Status: written proof, NOT yet reviewed. Please attack. Notation follows DMSY26 (arXiv 2602.07868v2)
where possible.

Contents
- A. Labels, the full walk order with O(1) version-stamp comparisons, canonical tree, ancestor closure
- B. Abstract instances with initial upper-bound labels (covers the outer run and every inner search)
- C. The deadline instance G_x of a local search, and execution equivalence (L1)
- D. Claim C and "touched vertices lie in U~" (L3, and the call-level version L3+)
- E. What DMSY26's proofs use (checklist for the integrated proof)

---------------------------------------------------------------------------------------------------

## A. Labels and the order ≺ (full walk order, O(1) comparisons via version stamps)

Graph H = (V_H, E_H, w), directed, w : E_H -> R_{>=0}; parallel edges and self-loops allowed. Vertices
and edges carry distinct integer ids. (Following agent-10's warning: we do NOT use bare 4-tuples as the
semantic order, because under 4-tuple "completeness" a complete vertex can have an incomplete canonical
ancestor — correct (length, hops) but wrong predecessor — and DMSY26 Obs. 2.1(4) uses ancestor-closure.)

**Walk order.** For a walk P = (y_0, e_1, y_1, ..., e_q, y_q) define
  κ(P) := ( ℓ(P), q, id(y_q), id(e_q), id(e_{q-1}), ..., id(e_1) ),   ℓ(P) = Σ w(e_i),
compared lexicographically (a shorter sequence that is a proper prefix of a longer one is smaller; this
case never arises between walks with equal (ℓ, q)). For walks from a fixed start vertex, κ is injective.
Write P ≺ Q iff κ(P) < κ(Q). (This is KR's order [2609.15247, Sec. 2.2] refined by edge ids, so that
parallel edges are handled.)

**Facts (KR Property 1–2, same proofs).** For walks from a common start:
 (O1) ≺ is a total order refining (ℓ, q);
 (O2) suffix invariance: P ≺ Q (both ending at u) ⇒ P∘R ≺ Q∘R for every walk R starting at u;
 (O3) a proper prefix is strictly smaller (every edge increases q);
 (O4) for every reachable v the ≺-minimum walk P(v) exists, is a simple path, and every prefix of P(v)
      is the ≺-minimum walk to its endpoint; hence {P(v)} is an arborescence T* rooted at the start.
 (O5) removing a closed subwalk strictly decreases κ (ℓ does not increase, q decreases).

**Labels as walk handles; O(1) comparison.** Each vertex v stores a version counter ver[v] (initially 0)
and a label d[v] ∈ {∞} ∪ {(ℓ, q, v, e, a)}, where e = (u, v) is the last edge and a is the value of
ver[u] when the label was written. The label *represents* the walk W(v) := W^{(a)}(u) ∘ e, where
W^{(a)}(u) is the walk represented by u's label at version a (source: the fixed walk of λ_σ).
ver[v] is incremented exactly when d[v] strictly decreases (see Relax). Since u's represented walks
strictly decrease with its version, W^{(b)}(u) ≺ W^{(a)}(u) for b > a, and by (O2):

  compare(λ = (ℓ,q,v,e,a), μ = (ℓ',q',v',e',a')):  by (ℓ, q), then id(v), then id(e), then a' < a
  means λ ≺ μ  (same last edge, newer version of the tail = strictly smaller walk);  a = a' means
  the same walk.

This decides κ-order of the represented walks exactly, with ONE real comparison plus O(1) integer
comparisons. Bounds B are label snapshots (or ∞) and are compared the same way. The only real-number
operations are the comparison of ℓ's and the addition ℓ + w(e) in the extension
  λ ⊕ e := (λ.ℓ + w(e), λ.q + 1, head(e), e, ver[tail(e)])   for λ = d[tail(e)],   ∞ ⊕ e := ∞.
So everything is in the comparison-addition model (ids, hop counts, versions are integers, not weights).

**T1 (monotone).** If λ ⪯ μ represent walks to u and e = (u, v), then λ ⊕ e ⪯ μ ⊕ e, with equality
iff λ = μ.   (O2)
**T2 (strict growth).** λ ⊕ e ≻ λ' for every label λ' of a walk that is a (weak) prefix of λ's walk;
in particular a relaxation can never lower a label below the label of its own tail.   (O3)

**Standing invariant (R1, agent-09).** Every label, cap, bound, source label and D-snapshot that ever
exists represents a walk that starts at the GLOBAL source s of the degree-reduced graph G (relaxed
labels extend such walks; inner source labels and caps are current global labels; bounds are
snapshots of labels, or ∞). Hence all comparisons in O1–O5, T1, T2 are between walks from the common
start s, and κ is injective on them.

**Order-agnosticism (R2, agent-09).** Nothing below depends on the particular tie-breaking order:
any total order on s-walks that satisfies O1–O5 and is realized exactly by an O(1) comparison of
stored labels suffices. The edge-id order κ above works on multigraphs. The vertex-pred variant
κ₅(W) = (ℓ, q, v, u, κ₅(W|u)) with labels (ℓ, q, v, u, ver[u]) (agent-09's prototype) is exact on
SIMPLE graphs (agent-01 exhibits a misordering with parallel edges of different weights), and the
δ = 3 degree-reduced graph is simple after dropping self-loops and keeping one minimum-weight edge per
ordered pair (O(m) by bucketing on integer ids).

---------------------------------------------------------------------------------------------------

## B. Instances

**Instance.** I = (H, σ, λ_σ, c): graph H, source σ ∈ V_H, a source label λ_σ representing a fixed
walk W_σ ending at σ (at the top level the empty walk at s), and initial labels c(v) for
v ∈ V_H \ {σ}, each ∞ or a label representing some walk ending at v (possibly a walk NOT in H, e.g. a
G-walk from s when I is an inner instance).

Examples.
- Outer (global) instance: I_0 = (G, s, empty walk at s, c ≡ ∞), G the degree-reduced input graph.
- Inner instance of a local search from x: I_x = (G_x, x, d_0[x], d_0|_{R_x}) — Section C.

**Walk labels / distance.** For a walk P in H from σ, L(P) := the label of W_σ ∘ P (compare via κ).
dis_I(v) := min_≺ { L(P) : P walk σ ~> v in H } (∞ if unreachable); it exists and is a simple path
by (O5). p*(v) := tail of the last edge of the minimizing walk; path_I(v) := the T*_I path σ ~> v
(O4). "The shortest path of v visits X" means path_I(v) ∩ X ≠ ∅ (endpoints included).

**Lemma A1 (canonical tree, subpath optimality).** For v ≠ σ reachable, with e* the last edge of
path_I(v): dis_I(p*(v)) ⊕ e* = dis_I(v); every prefix of path_I(v) is path_I of its endpoint; and
dis_I(y) ≺ dis_I(v) for every y ≠ v on path_I(v). dis_I(σ) = λ_σ.  (O2–O4.)

**Algorithm state.** d[σ] = λ_σ, d[v] = c(v) initially. The ONLY way a label changes:
  Relax(u, v, e, B):  cand := d[u] ⊕ e;
                      if cand ≺ d[v] and cand ≺ B: d[v] := cand; ver[v] += 1; return True
                      if cand = d[v] and cand ≺ B: return True          # re-confirmation, no change
                      return False
A call returning True is a *valid relaxation*; v is then *touched* (re-confirmations count as touches;
cf. agent-06 G2). cand = d[v] means the identical represented walk.

**Admissibility of an instance:** (I0) c(v) ⪰ dis_I(v) for all v ≠ σ in V_H.

**Lemma A3 (upper bounds, monotonicity).** Under (I0), at all times d[v] ⪰ dis_I(v) for all v ∈ V_H,
d[σ] = λ_σ, and labels are non-increasing.
*Proof.* Induction over valid relaxations: cand = d[u] ⊕ e ⪰ dis_I(u) ⊕ e (T1) = label of a walk to v
in H, hence ⪰ dis_I(v). A relaxation into σ is never valid: by (I0) and the induction hypothesis
d[u] ⪰ dis_I(u) = L(W_σ∘P_u) for a walk P_u from σ to u in H (if dis_I(u) = ∞ then d[u] = ∞ and
cand = ∞), so cand = d[u] ⊕ e ⪰ L(W_σ∘P_u∘e) ≻ λ_σ (T1, O3). [wording per agent-06 (s1)] ∎

**Complete:** v is complete iff d[v] = dis_I(v), i.e. v's label represents the unique ≺-shortest walk.
Once complete, always complete, and a complete label never changes again (no strict decrease possible).

**Lemma A2' (ancestor closure).** If v is complete then every vertex on path_I(v) is complete.
*Proof.* d[v] = (…, e*, a) represents W^{(a)}(p*(v)) ∘ e* = the ≺-shortest walk to v, whose prefix is
the ≺-shortest walk to p*(v) (O4); so p*(v)'s label at version a was complete, hence p*(v) is complete
now (complete labels never change, and versions only change on strict decreases). Induct. ∎
(This is exactly the property that fails for bare 4-tuples; with version stamps it holds.)

**Lemma A4 (canonical relaxation).** If u = p*(v) is complete and dis_I(v) ≺ B, then
Relax(u, v, e*, B) is valid and afterwards v is complete (a re-confirmation if v was already complete —
this is why Relax returns True on equality).  (cand = dis_I(u) ⊕ e* = dis_I(v) ⪯ d[v].) ∎

**Output.** At termination every vertex reachable from s is complete (DMSY26 Thm 1.1 / our main
theorem), so d[v].ℓ = true distance, the last-edge fields form the unique arborescence T*_{I_0}, and
unreachable vertices keep ∞. Ties, zero weights and zero cycles are covered by (O1)–(O5); canonical
paths never traverse a zero cycle (O4/O5). Mapping back through degree reduction: dist(v) := d[x].ℓ
for any vertex x of the gadget C_v (all gadget vertices of v have equal ℓ since the gadget cycle has
weight 0 and is strongly connected; O(n + m) output time).

---------------------------------------------------------------------------------------------------

## C. The deadline instance of a local search (L1)

Context: an outer call X = BMSSP(B, S, l) on instance I (normally I = I_0) runs FindPivots-B(B, S).
For some x ∈ S it starts InnerSearch(x). Let d_0 denote the global labels at that moment, and let
Z ⊆ V_H be the current *sink set* (vertices of the F̄-trees built so far in this FindPivots-B call;
x ∉ Z because such x are skipped). During InnerSearch(x) the global Relax is used with bounds ⪯ B.

**Wall semantics (H) = SUPPRESSION — FINAL (editor ruling 07:34:58; pseudocode RX.4–RX.5).** A
would-be-valid relaxation into a sink (cand ⪯ d[z] and cand ≺ B', z ∈ Z) is not performed; the pair
(u, e) is recorded as a *hit*. Sink labels never change during InnerSearch(x), and sinks never enter
any inner structure. [Variant (S), documented only: relaxations INTO sinks are performed and sink
out-edges are never scanned; the differences are marked [S] below.]

**Admissible walks.** A walk P = (x = y_0, y_1, ..., y_q) in H is admissible if for every 1 <= i <= q:
  (i)  L_x(P_{<=i}) ⪯ d_0[y_i]  and  L_x(P_{<=i}) ≺ B, where L_x(P') denotes the label of the walk
       W_x ∘ P' and W_x is the walk represented by λ_x := d_0[x] (x's label does not change during
       its own search: a relaxation into x would represent a walk with W_x as a proper prefix, O3);
  (ii) y_i ∉ Z for all 1 <= i <= q.   [S: only for 1 <= i < q, i.e. a sink may be the last vertex.]
Let R_x := { v ≠ x : some admissible walk ends at v } and, for v ∈ R_x,
D(v) := min_≺ { L_x(P) : P admissible, ending at v }.

**The instance.** G_x := the induced subgraph H[R_x ∪ {x}] (R_x ∩ Z = ∅ by (ii)).
[S: vertex set R_x ∪ {x}, edges (u, v) with u, v ∈ R_x ∪ {x} and u ∉ Z.]
I_x := (G_x, x, λ_x = d_0[x], c_x = d_0|_{R_x}).

**Lemma D1.** For v ∈ R_x: dis_{I_x}(v) = D(v), D(v) ⪯ d_0[v], D(v) ≺ B. Hence I_x satisfies (I0),
and every vertex of G_x is reachable from x with distance ≺ B: U~_{I_x}(B, {x}) = R_x ∪ {x}
(x itself has dis = d_0[x] ≺ B, since x ∈ S and d[x] ≺ B for all x ∈ S by the FP context (C3);
x ∉ R_x because a walk returning to x has W_x as a proper prefix).
*Proof.* Every vertex y_i (i >= 1) of an admissible walk is in R_x (its prefix is admissible), so
admissible walks are walks of G_x [S: edges leave x or a non-sink by (ii)]: dis_{I_x}(v) ⪯ D(v).
Conversely let P = path_{I_x}(v) = (x = y_0, ..., y_q = v). By A1 in I_x, L_x(P_{<=i}) =
dis_{I_x}(y_i) ⪯ D(y_i) ⪯ d_0[y_i] (first part applied to y_i, then the definition of D) and
D(y_i) ≺ B; every y_i (i >= 1) lies in R_x, hence is not a sink [S: every internal y_i has an out-edge
in G_x, hence is not a sink]. Thus P is admissible and D(v) ⪯ L_x(P) = dis_{I_x}(v). ∎

**Structural property (SP / SP')** — must hold for the pseudocode of the core BMSSP (with the FindPivots
used at that level) run on any instance with source σ:
  (SP)  every Relax(u, ·) executed has u = σ or u touched earlier in the same run;
  (SP') every vertex that ever occurs in a heap, a D (as a key), an S, a P_j, a W, a W' or a U of the run,
        or whose label/stored value is read by any comparison of the run other than the validity test
        of a Relax, is σ or was touched earlier in the same run (agent-09 R3).
SP' covers the non-Relax label reads: FindPivots-D heap keys, D insert/pull/merge/delete values, the
separators B_i, Line-13 picks d[v] ≺ B_i, the Line-25/26 pivot comparison, the argmin over P_j
(Lines 6/28), Line 32/33 tests, the W' test (Line 34), and base-case BST keys.
Verified against agent-04's pseudocode.md v2 (board post 07:35:26): Relax sites BM.19–20, BM.27–28, BC.7,
FD.9 and the inner run FB.6; read sites BM.7/8/12/22/23/25/26 and FB.10; FIX-STALE/EMPTY/BASE/J and the
BM.12 expansion perform no relaxations. (Proof: induction over the recursion — keys enter these
structures only after a valid relaxation, or as members of S / P_j ⊆ S / W, all of which are σ or
touched.)

**Lemma D2 (execution equivalence).** During InnerSearch(x) every PERFORMED valid relaxation
Relax(u, v, e, B') has u ∈ R_x ∪ {x}, v ∈ R_x and e ∈ E(G_x). Consequently (with SP' for all non-Relax
reads, which therefore only involve vertices of R_x ∪ {x}) the run on the global labels performs exactly
the same label changes, reads and comparisons, in the same order, as the same code run on instance
I_x; the only difference is that on H it also scans edges leaving R_x ∪ {x}, each such Relax returning
False or yielding a hit (O(1) time each, already counted in DMSY26's δ-per-scanned-vertex term). Labels
of vertices outside R_x ∪ {x}, in particular of all sinks, never change.
**Membership lookups (agent-06 (s2)).** Execution equivalence also needs the integer membership lookups of
the inner run to be OWNER-AWARE: Pmem(v) (BM.12/17/22) returns a group only if the top P-record of v belongs
to the current call, and D.Insert/Delete/Merge touch only records of the current D. This is S5 Lemma MS
(per-vertex membership stacks with owner test; pseudocode v2.2, tracker I20). With it, the inner run never
reads or modifies P- or D-records of outer calls, so it behaves exactly as the run on I_x (where no outer
records exist), and FP6 holds.
*Proof.* Induction over the relaxations of the run. By SP, u = x or u was touched earlier in the run,
so u ∈ R_x ∪ {x} (induction hypothesis), hence u ∉ Z. By the induction hypothesis the run so far is a
run on I_x, so A3 applies in I_x: d[u] ⪰ D(u) (with d[x] = λ_x = D(x) by convention). If the relaxation
is valid and performed then v ∉ Z (relaxations into sinks are suppressed) and
  D(u) ⊕ e ⪯ d[u] ⊕ e = cand ⪯ d[v] ⪯ d_0[v]  and  D(u) ⊕ e ⪯ cand ≺ B' ⪯ B      (T1, A3).
Let P_u be an admissible walk attaining D(u) (P_u = (x) if u = x). Then P_u ∘ e is admissible: the
prefix conditions are inherited, the last step satisfies (i) by the display and (ii) as v ∉ Z. So
v ∈ R_x and e ∈ E(G_x). [S: u ∉ Z because sink out-edges are never scanned; v may be a sink.] ∎

**Lemma D3 (inner preconditions).** At the start of InnerSearch(x), x is complete in I_x
(d[x] = λ_x = dis_{I_x}(x)), and ⟨∅, {x}⟩ is a frontier for U~_{I_x}(B, {x}) = R_x ∪ {x}: every
path_{I_x}(v) starts at the complete vertex x. So the top inner call BMSSP(B, {x}, l*) meets the
preconditions of the corrected Lemma 3.1 (S2) on instance I_x — **whether or not x is complete in the
outer instance**. Claim C (Section D) holds trivially for this top call.

**Remarks.**
1. D1–D3 assume nothing about d_0 beyond A3 in the outer instance. In particular the outer labels need
   not be relaxed: edges (a, b) with d_0[a] ⊕ e ≺ d_0[b] may exist. Such edges are irrelevant to I_x
   unless a ∈ R_x. Vertices outside R_x ∪ {x} are read only inside failing Relax checks (or hit
   records) and never enter any set of the inner run (agent-06 G1).
2. Why not "super-source with cap edges σ* → v of weight d_0[v]" (my first wording, corrected by
   agent-07): in that graph an equal-label tie can route path(v) through a cap edge. Then v is
   incomplete but outside U~(B, {x}), which violates Claim C. In I_x there are no cap edges. Caps
   only (a) define R_x and (b) serve as initial upper-bound labels, which (I0) permits.
3. Z and d_0 are frozen for the duration of InnerSearch(x): F̄-trees are updated only after the inner
   call returns. So I_x is a fixed instance.
4. **Failed-search exactness (agent-08's L2).** Suppose the inner run is a full execution. Then, by the
   corrected Lemma 3.1 on I_x, U_x = R_x ∪ {x} and every vertex of it is complete in I_x:
   d[v] = D(v). Suppose moreover that no hit was recorded. Then the walls had no effect: let R'_x be the
   region defined without condition (ii); if R'_x ≠ R_x, take a walk that is admissible without (ii)
   and truncate it at its first sink z. Its prefix up to z's predecessor u is admissible, so
   u ∈ R_x ∪ {x} is completed by the full run. The relaxation (u, z) is would-be-valid once u is
   complete (cand = D(u) ⊕ e ⪯ the walk's label ⪯ d_0[z], and ≺ B). **Lemma S2-scan** (= S2 Lemma
   S2.4): every vertex that enters U of a call has all its out-edges Relax-scanned at least once while
   complete, with THAT call's own bound; for the top inner call this is the outer bound B (base case
   BC.7, BM.19, BM.27) [agent-06 (s4)]. So a hit would have been recorded, a contradiction. Hence R'_x = R_x.
   [S: if U_x ∩ Z = ∅ then R_x ∩ Z = ∅ (full execution gives R_x ⊆ U_x), and a walk admissible except
   for an internal sink has an admissible prefix ending at its first internal sink, so R_x = R'_x.]
   If x is complete in the OUTER instance, then for every v with dis(v) ≺ B and x ∈ path(v), write the
   segment of path(v) from x as (x = y_0, y_1, ..., y_r = v). For each i: dis(y_i) = L_x((y_0, ..., y_i))
   (A1, and W_x = path(x) because x is complete), dis(y_i) ⪯ d_0[y_i] (A3 in the outer instance), and
   dis(y_i) ⪯ dis(v) ≺ B. So every prefix satisfies (i) and the unblocked (ii), i.e. the segment is
   admissible in R'_x = R_x (agent-09 R4(b)), and D(v) ⪯ L_x(segment) = dis(v). Conversely D(v) is the
   label of an s-walk to v (R1), so D(v) ⪰ dis(v). Hence D(v) = dis(v). The full run makes v complete
   in I_x, i.e. d[v] = dis_{I_x}(v) = D(v) (D1), so d[v] = dis(v): v is complete in the outer instance.

---------------------------------------------------------------------------------------------------

## D. Claim C and "touched ⊆ U~" (L3, L3+)

Fix an instance I with (I0). All notions (dis, path, complete, U~) are w.r.t. I.
Recall U~(B, S) := { v : dis(v) ≺ B and path(v) ∩ S ≠ ∅ } (DMSY26 Sec. 2.4).

**Claim C.** At the moment any call BMSSP(B, S, l) on I begins, every v with dis(v) ≺ B and
v ∉ U~(B, S) is complete.

**Lemma L3+ (confinement).** Assume Claim C holds at the start of a call X = BMSSP(B, S, l) and
S ⊆ U~(B, S) (true since every x ∈ S has d[x] ≺ B). Then every vertex touched during X (in its
FindPivots, in its own relaxations, or inside any of its descendants — and, for FindPivots-B, inside
any InnerSearch it launches) lies in U~(B, S).
*Proof.* By SP applied inside X (every relaxation in X is from a vertex of S or a vertex touched
earlier in X; for InnerSearch(x), x ∈ S), induct over the valid relaxations of X in time order. Let
Relax(u, v, e, B') be valid with B' ⪯ B and u ∈ U~(B, S) (u ∈ S or touched earlier: induction
hypothesis). Then dis(v) ⪯ cand ≺ B. Suppose v ∉ U~(B, S). By Claim C, v was complete at the start
of X, hence d[v] = dis(v) still (A3). Validity gives cand ⪯ d[v] = dis(v) ⪯ cand, so
d[u] ⊕ e = dis(v): the relaxation produced the ≺-shortest walk to v, so e = e* (the last edge of
path(v)), u = p*(v), and path(v) = path(u) ∘ e* (A1). path(u) visits S (u ∈ U~(B, S)), hence path(v)
visits S and v ∈ U~(B, S) — contradiction. ∎
(For InnerSearch the relaxations happen on global labels, but they are relaxations in the outer
instance I as well, so the same argument applies verbatim. Hits are not relaxations. The argument
never uses completeness of x.)

**Corollary L3.** Every F̄-tree vertex and every W-vertex produced by FindPivots-D or FindPivots-B in
call X lies in U~(B, S) (they are S-vertices or touched). This is the claim of DMSY26 Remark 3.3
("vertices of F_j are in U~"), which DMSY26 state without proof; it is needed both for correctness
(the W'-completeness step of Lemma 3.7 applies the frontier ⟨W, P_ini⟩ to v ∈ W', which requires
v ∈ U~) and for the time analysis (p <= |U~|/k; F_j ⊆ U in full executions for the Line-29 charging).
Also: every vertex whose label is modified by sub-call i lies in U~_i = U~(B_i, S_i) (used in the
P̂-maintenance step of the corrected Lemma 3.7, R6 case (a)).

**Proof of Claim C.** In the integrated document the proof for sub-calls is S2 Step 2 (C1) (agent-08
S2_core.md), stated with S2's certified-frontier invariants (J1)–(J5); that is the normative proof
(agent-06 (s3)). The sketch below, in R6 notation, is kept as an independent cross-check only.
*Sketch* (induction over calls in execution order, jointly with the corrected Lemma 3.7
(S2 / R6_core_invariants.md) for the already-finished calls). Top call of an instance (S = {σ}):
path(v) ∋ σ for every reachable v, so nothing to prove. Now let Y = BMSSP(B_i, S_i, l-1) be the i-th
sub-call of X = BMSSP(B, S, l), and let v satisfy dis(v) ≺ B_i ⪯ B and v ∉ U~(B_i, S_i).
- If v ∉ U~(B, S): complete at the start of X by Claim C for X; still complete (A3).
- If v ∈ U~(B, S): by the precondition of X, path(v) contains a vertex y ∈ S that was complete at
  the start of X.
  - y ∈ Q: y's local search failed and y is complete, so by failed-search exactness (Remark C.4 for
    FindPivots-B, DMSY26 Lemma 3.2 for FindPivots-D) v ∈ W and v is complete.
  - y ∈ P_ini: then v ∈ U~_P := U~(B, P_ini). By the corrected loop invariants (R6: (J2) at the
    beginning of iteration i), either v ∈ U — then v is complete — or path(v) contains a complete
    z ∈ D^acc ∪ P̂ with dis(z) ⪯ dis(v) ≺ B_i. By R6 Claim P such z is in S_i (an accurate key with
    stored value dis(z) ≺ B_i is pulled; a complete z ∈ P̂_j has stored value of piv[j] ⪯ dis(z) ≺ B_i,
    so piv[j] is pulled and BM.12 adds z). Hence v ∈ U~(B_i, S_i) — contradiction.
(Every y ∈ S lies in exactly one of Q, P_ini: P_j ⊆ S \ Q, and every S-vertex not in Q ends up in
some F̄-tree, hence in some F_j after partitioning (MP.6).) ∎

Dependency order (no circularity): for a call X, Claim C(X) ⇒ L3+(X) ⇒ [FindPivots output
properties for X, incl. W ⊆ U~] ⇒ corrected Lemma 3.7 invariants in X's loop (using the finished
sub-calls' postconditions) ⇒ Claim C(next sub-call of X). For FindPivots-B, failed-search exactness
uses the full correctness of the core with FindPivots-D on the (different) instances I_x, which is
proved first, independently.

**Multi-level bootstrapping (agent-09 R5, agent-03 (e)).** With nesting depth D the statement is an
induction on depth: depth 0 = the core with FindPivots-D on any admissible instance; depth j = the core
with FindPivots-B whose inner runs are depth-(j−1) runs on deadline instances. A nested instance
I_{x2} is defined relative to the instance H = G_{x1} of the enclosing inner run, with caps = the global
labels at its start and sinks = the F̄-vertices of the enclosing FindPivots-B call. D1–D3 apply verbatim
to it, because they use only (I0) for H and SP/SP' of the enclosing run (x2 is x1 or touched in the
run on I_{x1}), and every label is still an s-walk (R1). Claim C and L3+ are proved per instance.

---------------------------------------------------------------------------------------------------

## E. What DMSY26's correctness proofs use (checklist)

Reading of DMSY26 Sec. 2.4–3.5. Each item should be re-proved in the integrated document for a
general instance I satisfying (I0):
- Obs. 2.1 (1)-(5): uses A1 (prefix structure, strict order along paths), A2' (ancestor closure, for
  (4)), A3 (upper bounds, persistence).
  (2) "the minimum of Y is complete": if y = argmin_Y d were incomplete, path(y) contains a complete
  z ∈ Y, z ≠ y, and dis(z) ≺ dis(y) ⪯ d[y] (A1 strict), contradicting minimality.
- **Obs. 2.1(4)' (no ancestor closure needed; agent-10's proof).** If ⟨X, Y⟩ is a frontier for
  U~(B, S) and Y ⊆ U~(B, S), then ⟨∅, Y⟩ is a frontier for U~(B, Y). Proof: for v ∈ U~(B, Y) let y_1 be
  the FIRST vertex of Y on path(v). If y_1 were incomplete, then (y_1 ∈ Y ⊆ U~, frontier condition (2))
  path(y_1) contains a complete y' ∈ Y; y' lies on path(v) strictly before y_1, contradicting the choice
  of y_1. So y_1 is complete and on path(v). ∎  This proof is valid under BOTH tie semantics (bare
  4-tuples, where A2' fails, and version-stamped walk order), so S2 may cite Obs. 2.1(4)' either way.
- Sec. 2.5 frontier update: uses A4 on the first edge of path(v) leaving Z.
- Lemma 3.2 / Remark 3.3 (FindPivots): uses L3 (vertices in U~), failed-search exactness.
- Lemma 3.6: A1, A3.
- Lemma 3.7: Lemma 3.2, Lemma 3.6, Obs. 2.1, Sec. 2.5, Pull/Merge semantics of D (Lemma 3.4),
  L3+ for sub-calls (modified labels lie in U~_i), W ⊆ U~ (L3).
- Lemma 3.8: Lemma 3.7 (bounds B'_{i-1} ⪯ dis(U_i) ≺ B'_i) — uses only ≺ as a total order on labels.
- Time (Obs. 3.5, Lemma 3.9): Lemma 3.7/3.8, L3 (p <= |U~|/k, F_j ⊆ U in full executions), degree
  bound δ, and the Q-appearance argument (which uses that Q-vertices are not inserted into D, and
  that each D-insertion of a vertex is caused by a distinct valid relaxation of one of its in-edges
  from a vertex completed inside the call — worth re-proving carefully, agent-05/agent-01).
None of these uses that initial labels are path labels of H, nor completeness of the source in any
larger instance; only (I0) and the Relax discipline. Hence they apply to I_x (Section C).

---------------------------------------------------------------------------------------------------

## F. A gap in DMSY26 Lemma 3.7 (stale D-entries) and the fix — HISTORICAL (superseded by S2)

*Status: superseded. The normative statement and proof of the corrected invariants is S2 (agent-08,
S2_core.md, Lemma S2.1, certified frontier); R6_core_invariants.md is an independent cross-check. This
section records the original finding (E1) and is not part of the proof.*

**The claim in DMSY26.** Proof of Lemma 3.7, item "D ∪ P loses only vertices in U_i":
"U_i is not in D, no need to remove: ∀u ∈ U_i, d[u] = dis(u) < B' ≤ d_B[D]", resting on invariant 2
"d_B[D ∪ P] ≥ B'", proved by "after Pull d_B[D] ≥ B_i; for any v added into D, d[v] ≥ B'_i".
Here d_B[D] is defined with the CURRENT labels d[·].

**Why it fails.** The labels of keys that are already in the parent's D (and not pulled) can decrease
*inside* sub-call i: its FindPivots local searches, and deeper Line-24/37/base-case relaxations,
relax global labels of any vertex of U~_i = U~(B_i, S_i) (L3+), and nothing re-inserts them into the
parent's D. Witness pattern (inside some call X): u ∈ U_1 relaxes a heavy non-canonical edge (u, v),
d[u] + w(u,v) ≥ B_1, so v is inserted into X's D with value μ (Line 24). Later S_i = Pull() contains
the complete canonical ancestor z of v (d[z] ≺ B_i ⪯ μ, so v is not pulled). Sub-call i completes v
(v ∈ U_i, since dis(v) ≺ B'_i and path(v) ∋ z ∈ S_i). Now v ∈ U_i and v is still a key of X's D
with stale value μ, so d_B[D] ≤ d[v] ≺ B'_i and invariant 2 fails. Later a Pull returns v again;
v ∈ S_{i'} for i' > i, v is complete, and sub-call i' "completes" v and re-explores its subtree:
U_i ∩ U_{i'} ≠ ∅ (contradicting Lemma 3.8's disjointness), v's out-edges re-enter Line 24
(contradicting Obs. 3.5 — Relax with ⪯ re-validates equal labels), and the work on the re-explored
subtree is not paid for by the time analysis. Concrete micro-instance of the pattern:
s→u (1), s→z (5), u→v (100), z→v (1), with u completed in an earlier sub-call and z pulled later
(needs a level/M setting where u and z are pulled in different iterations; agent-07/agent-09 please
reproduce in the faithful implementation with an assertion "U_i pairwise disjoint").
The same pattern appears in DMMSY25 Lemma 3.7 proposition (b) (the proof only treats D_{i+1} \ D_i and
implicitly assumes keys of D_i \ S_i have dis ⪰ B_i) and Lemma 3.10.

**Fix (cost O(1) per affected entry).** Keep a global flag done[v], set when v is added to any U
(base case, Line 30, Line 38). Every Pull result is filtered: S_i := { x ∈ Pull() : not done[x] }
(entries removed this way were paid for at insertion). If the filtered S_i is empty, set
B'_i := B_i, U_i := ∅, D_i := ∅ and continue the loop. Equivalently: after each sub-call, delete
U_i ∩ keys(D) (the key table of Lemma 3.4 supports O(1) deletion; empty blocks are removed lazily,
amortized against the ≥ M/3 insertions that filled them).

**Correct invariant (replace DMSY26's invariants 1–2).** Let val_D(y) be the stored value of key y
(val_D(y) ⪰ d[y] always) and D^acc := { y ∈ keys(D) : y complete and val_D(y) = d[y] }. At the start
of iteration i:
 (1') ⟨U, D^acc ∪ P̂⟩ is a frontier for U~_P, and keys(D) ∩ U = ∅ after filtering;
 (2') every y ∈ keys(D) ∪ P with y ∉ U has dis(y) ⪰ B'_{i-1} (TRUE distances, not labels —
      the version DMMSY25 Lemma 3.10 actually needs);
 (3') for each nonempty P_j: the stored value of p_j's D-entry is ⪯ d_B[P̂_j] (stored value, not
      d[p_j]; this is what DMSY26's case analysis actually establishes and what Pull uses).
Sketch of why (1') is preserved: an accurate complete entry keeps its value forever (complete labels
never change), and it cannot enter U_i unpulled (it has dis = val ⪰ B_i ⪰ B'_i); coverage lost
because a pulled S_i-vertex entered U_i is regained from the sub-call guarantee, which must itself be
stated with accurate entries: ⟨U_i, D_i^acc⟩ is a frontier for U~_i (strengthened Lemma 3.7(1));
S_i \ U_i are re-inserted at the sub-call's Line 33 with current labels, and R(B_i, U_i) entries
are inserted at the moment of the (last) valid relaxation from a complete vertex — Relax's ⪯ makes
the re-relaxation at Line 22/35 re-insert a vertex whose label was earlier set by a FindPivots
relaxation from the same (now complete) vertex. Pull returns every accurate complete key with
dis ≺ B_i, and Lemma 3.6 then goes through with D^acc.
This needs a careful full rewrite of Lemma 3.7 in the integrated document (agent-08 / agent-09).

---------------------------------------------------------------------------------------------------

## G. Tie semantics: the two admissible choices — EDITOR RULING 07:29:10: (TV) adopted

Everything in Sections B–F is stated so that it holds under either choice below; only Section A differs.
- **(T4) bare DMSY26 4-tuples** (ℓ, h, v, pred): "complete" := 4-tuple equality with dis4. Order facts
  T1/T2/A1/A3/A4 hold; **A2' (ancestor closure) FAILS** (agent-10's example: s→a, s→b, a→u, b→u, u→v,
  all weight 1, id a < b; relax via b first: d[u] = (2,2,u,b) incomplete, then d[v] = (3,3,v,u) = dis4(v)
  complete). Every proof must avoid ancestor closure; Obs. 2.1(4)' above is the replacement for the
  one DMSY26 use found so far. L3+ uses "cand = dis4(v) ⇒ 4th component = p*(v)"; D1–D3, Claim C, W-
  exactness never use ancestor closure. Parallel edges: fine (different weights differ in ℓ; equal
  weights give identical tuples).
- **(TV) version-stamped full walk order** (Section A as written): A2' holds, so DMSY26's arguments can
  be used as written; costs one integer version per vertex and a 5th label component; every comparison
  site must use the version-aware compare (agent-01's coverage list V3.2 enumerates them).
Ruling: (TV) is used by the master document (agent-09 checked 693 runs of 5-tuple labels against explicit
full-path labels, 0 differences). (T4) is kept here only as documentation; Obs. 2.1(4)' is a remark.


## Appendix C — S2 Corrected BMSSP core (agent-08)

Frozen label `S2v1.3`, source `/research/agents/agent-08/work/S2_core.md`, sha256 `0730b87c29c4fa4549bcd637a93f8b14a262a314e610c283213d7bb91a106258`, frozen 2026-09-20T07:51:13Z.

# S2 — Corrected BMSSP core on admissible instances (agent-08), v1.3, 2026-09-20

v1.3: agent-06 formal review #2 clarifications c1 (instance graph = G_x for inner instances, so canonical
relaxations are never suppressed), c5 (cross-reference: S4's (B2) needs τ ≥ t|S|, FIX-SIZE); c2, c3 were
already covered by v1.2 (PP equality; Lemma S2.5 = the edge-once corollary).

v1.2: addresses formal review #1 (agent-09 N1–N6), agent-03's review (1)–(5), agent-01's notes (a)–(b), editor
checklist: PP as an equality; Merge precondition; Lemma S2.5 (insertion-event uniqueness, for S4 G2/G4);
scope/composition (§S2.2); explicit multi-switch chain in Case 2c; equality re-relaxations at BM.20; lazy-filter
equivalence (§S2.5 item 7); old pivots remain ordinary keys.

v1.1: line numbers now refer to the MASTER pseudocode (agent-04 pseudocode.md v2: BM.x, BC.x);
added Lemma S2.4 (all out-edges of settled vertices are Relax-scanned while complete; needed by S1
Remark 4 under suppression); remark on (J4') vs (3'); BM.29 shown redundant.

Status: written proof, NOT yet reviewed. Formal reviewers: agent-09, agent-06 (agent-03 third).
Executable companion: /research/agents/agent-08/work/impl/bdmsy.py (every statement (R1)–(R9) below
is asserted at run time against an oracle of the instance, for every call of every outer and inner
instance; see §S2.6).

Dependencies (S1 = agent-02 L1_foundations.md v2.x): instance I = (H, σ, λ_σ, c) with (I0);
order ≺ on labels; dis_I, path_I(v), p*(v), complete; Relax; Lemmas A1 (canonical tree, subpath
optimality, strict increase along paths), A3 (upper bounds, labels non-increasing), A4 (canonical
relaxation), structural property SP, Lemma L3+ (confinement), Claim C (statement).
**This section does NOT use ancestor closure (A2')**; every argument below is valid both for the
version-stamped labels (TV) and for bare 4-tuples (T4), provided "complete", dis, ≺ are read in one
semantics throughout.

FindPivots is used only through the interface FP1–FP6 of MASTER_B1.md §4 (restated in §S2.1).

---------------------------------------------------------------------------------------------------

## S2.0 Notation

All notions are w.r.t. a fixed admissible instance I. For a bound B (a label or +∞) and a vertex set S:
  Ũ(B, S) := { v : dis(v) ≺ B and path(v) ∩ S ≠ ∅ }.
A vertex y is *on path(v)* if it is one of the vertices of path(v) (endpoints included).
For X ⊆ V write dis(X) ⪰ β for "dis(x) ⪰ β for all x ∈ X".

**Data structure D (interface; implementation and cost: S5, agent-04).** D stores a set keys(D) of
vertices, each key y with a *stored value* val(y) (a label). Operations:
- Insert(y, λ): if y ∉ keys(D) add y with val(y) := λ; else val(y) := min(val(y), λ).
- Delete(y): remove y if present.
- Merge(D'): Insert(y, val_{D'}(y)) for every key y of D'.
- Pull(): let M be D's parameter. Returns (S', x): if |keys(D)| ≤ M then S' = keys(D) and x = B
  (the bound D was initialized with); otherwise S' = the M keys of smallest stored value and x = the
  smallest stored value among the remaining keys. S' is removed from D.
  **Pull property (PP):** S' = { y ∈ keys(D) : val(y) ≺ x } (as an EQUALITY), x ⪯ B, and S' ≠ ∅ if
  keys(D) ≠ ∅. The equality holds because stored values of distinct keys are distinct (a stored value is a
  label of its own key, and labels of different vertices differ in the vertex component), so the M smallest
  are exactly the keys below the (M+1)-st value; x ⪯ B because every stored value is ≺ B (by (R3) for
  D_i-values and the Relax bound for all other insertions; see Step 5).
  **Merge precondition (S5 Lemma DS).** At BM.14 every stored value of D_i is ≺ B_i ((R3) of the sub-call)
  and every stored value remaining in D is ⪰ B_i (PP; D is untouched during the sub-call, (R9)); so the
  values of D_i precede those of D, which is what S5's linear-time Merge requires.
Stored values are never compared with anything but labels/bounds; they are labels.
Two trivial facts used throughout:
 (V1) val(y) ⪰ d[y] for every key y at every time (a key is inserted with its current label or with a
      stored value of another D, and labels never increase — A3);
 (V2) hence val(y) ⪰ dis(y).
A key y is **certified** if y is complete and val(y) = d[y] (= dis(y)). A certified key stays
certified as long as it is a key (complete labels never change; val cannot go below dis).

**The FindPivots interface** (MASTER §4), for a call X = BMSSP(B, S, l) at whose start Claim C holds,
⟨∅, S⟩ is a frontier for Ũ := Ũ(B, S), and d[x] ≺ B for x ∈ S. FindPivots(B, S) returns P_1..P_p, Q, W
with:
- FP1 ⟨W, P_1 ∪ … ∪ P_p⟩ is a frontier for Ũ: every v ∈ Ũ is (in W and complete) or path(v) contains
  a complete vertex of P_ini := P_1 ∪ … ∪ P_p (completeness at the moment FindPivots returns).
- FP2 P_1..P_p, Q pairwise disjoint, nonempty, union S.
- FP3 Q ⊆ W ⊆ Ũ, |W| < k|Q| (W = ⋃_{x∈Q} W_x, |W_x| < k).
- FP4 (trees; analysis only).  - FP5 SP holds inside FindPivots, hence (L3+) every vertex whose label
  changes lies in Ũ.  - FP6 FindPivots performs no operation on any D of any BMSSP call of I.
S2 uses FP1, FP2, FP3 (only W ⊆ Ũ), FP5, FP6.

---------------------------------------------------------------------------------------------------

## S2.1 The corrected algorithm (per instance I)

The algorithm is the MASTER text agents/agent-04/work/pseudocode.md v2, Sections 3–4 (BM.1–BM.31,
BC.1–BC.9), run on the admissible instance I. Parameters: k ≥ 1; for l ≥ 1 a Pull size M_l ≥ 1 and a
threshold Λ_l ≥ 1; base threshold Λ_0 ≥ 1; the top call of an InnerSearch uses τ = k (NEW-CAP),
every other call τ = Λ_l. For the proofs only the following reading of the lines matters:

| line(s) | action |
|---|---|
| BM.4 | FindPivots(B, S) → P_1..P_p, Q, W (FP1–FP6) |
| BM.7 | p_j := argmin_{P_j} d; D.Insert(p_j, d[p_j]) |
| BM.8 | B'_0 := min(B, min_j d[p_j]); U := ∅ |
| BM.9 | while \|U\| ≤ τ and D ≠ ∅ |
| BM.10 | (S_i, B_i) := D.Pull() |
| BM.11–12 | for each PULLED x that is the CURRENT pivot p_j: S_i := S_i ∪ {v ∈ P_j : d[v] ≺ B_i} |
| BM.13 | (B'_i, U_i, D_i) := BMSSP(B_i, S_i, l−1) |
| BM.14 | D.Merge(D_i) |
| BM.15 ★ | for u ∈ U_i: D.Delete(u)  (FIX-STALE) |
| BM.16–18 | remove U_i from the P_j; J := {j : old p_j ∈ U_i, P_j ≠ ∅ at that moment} |
| BM.19–21 | for u ∈ U_i, e = (u,v) ∈ Out(u): if Relax(u,e,B) and d[u] ⊕ e ⪰ B_i: D.Insert(v, d[v]) |
| BM.22 | if v ∈ P_j, j ∉ J, d[p_j] ≻ d[v]: p_j := v  (optional; see Remark S2.5.6) |
| BM.23 ★ | for j ∈ J with P_j ≠ ∅: p_j := argmin_{P_j} d; D.Insert(p_j, d[p_j])  (FIX-J) |
| BM.24 | B' := B'_i; U := U ∪ U_i |
| BM.24a ★ | if D = ∅: B' := B  (FIX-EMPTY) |
| BM.25 | for x ∈ S: if B' ⪯ d[x] ≺ B: D.Insert(x, d[x]) |
| BM.26 | W' := {x ∈ W \ U : d[x] ≺ B'} |
| BM.27–28 | for u ∈ W', e ∈ Out(u): if Relax(u,e,B) and d[u] ⊕ e ⪰ B': D.Insert(v, d[v]) |
| BM.29 | for u ∈ W': D.Delete(u)  (FIX-F2; REDUNDANT: by (J2)/(R3) no key is in W' — it deletes nothing) |
| BM.31 | return (B', U ∪ W', D) |
| BC.2 | D := {(x, d[x]) : x ∈ S} (BST keyed by stored value); U := ∅ |
| BC.3–6 | while D ≠ ∅: u := FindMin; if \|U\| ≥ τ: break; Delete(u); U := U ∪ {u} |
| BC.7 | for e ∈ Out(u): if Relax(u, e, B): D.Insert(v, d[v]) |
| BC.8 ★ | B' := B if D = ∅ else min stored value  (FIX-BASE) |

Remarks on the ★ changes.
- BM.15 (FIX-STALE; errata E1). DMSY26's claim "U_i is not in D" is false; without BM.15 the U_i
  overlap (agent-08 gap_demo.py: 48/300 random trials; also agents 01/02/03/06/09). O(|U_i|) per
  iteration with the key table (S5). Equivalent alternative: filter Pull by a done[] flag.
- BM.23 (FIX-J; found independently by agent-08 and agent-04): j may enter J while P_j ≠ ∅ and P_j can
  then be emptied by later vertices of the same U_i; DMSY26 Alg. 3 Line 28 would take argmin over ∅.
- BM.24a (FIX-EMPTY; errata E3, agent-03). Needed for "B' = B ⟺ D = ∅".
- BC.5/BC.8 (FIX-BASE; errata E2, agents 01/04/06/09): threshold tested before extraction, B' = the
  minimum stored value remaining AFTER the last relaxations.
- Out(u) is the out-list of u in the host graph. For an inner instance I_x under SUPPRESSION (master
  ruling), RX.4–5 turn every would-be-valid relaxation into a sink into a recorded hit returning False;
  by S1 D2 all other relaxations leaving R_x ∪ {x} return False as well. So w.r.t. the instance graph
  G_x the extra scanned edges are no-ops, and the lemma below is applied with H = G_x.

---------------------------------------------------------------------------------------------------

## S2.2 The main lemma

**Lemma S2.1 (correctness of BMSSP; replaces DMSY26 Lemmas 3.7 and 3.8).** Let X = BMSSP(B, S, l, τ)
be a call on an admissible instance I such that at its start
 (C1) Claim C holds: every v with dis(v) ≺ B and v ∉ Ũ(B, S) is complete;
 (C2) ⟨∅, S⟩ is a frontier for Ũ := Ũ(B, S): path(v) contains a complete vertex of S, for all v ∈ Ũ;
 (C3) S ≠ ∅ and d[x] ≺ B for every x ∈ S (hence S ⊆ Ũ).
(Throughout, path(·), p*(·), dis and Ũ are taken in the instance graph H of I. For an inner instance I_x
(S1 §C, suppression) H = G_x = H_host[R_x ∪ {x}], which contains no sink; hence every canonical edge used
below (the A4 relaxations in (K3), Step 4 Case 1 and the (R2) prefix argument) is an edge of G_x into a
non-sink, and RX.4–5 never suppress it.)
Then X terminates and returns (B', U, D) such that:
 (R1) B' ⪯ B, U = Ũ(B', S), and every vertex of U is complete.
 (R2) (certified frontier) every v ∈ Ũ \ U has a certified key of D on path(v).
 (R3) keys(D) ⊆ Ũ \ U; every key y satisfies B' ⪯ dis(y) ⪯ d[y] ⪯ val(y) ≺ B.
 (R4) B' = B ⟺ keys(D) = ∅. If B' ≺ B then |U| > τ for l ≥ 1, and |U| ≥ τ for l = 0.
 (R5) B' ⪰ min_{x∈S} dis(x).
 (R6) every vertex touched during X lies in Ũ (this is L3+ of S1; it uses (C1), (C3) and SP).
 (R7) S \ U ⊆ keys(D), and val(x) ⪯ d_0[x] for x ∈ S \ U, where d_0[x] is x's label at X's start.
 (R8) (l ≥ 1) U is the disjoint union of U_1, …, U_f (f = #iterations) and W', and for every i,
      B'_{i−1} ⪯ dis(u) ≺ B'_i for all u ∈ U_i, with B'_0 ⪯ B'_1 ⪯ … ⪯ B'_f.
 (R9) the returned D is the only D of X that survives; X leaves no key in any D of an ancestor
      call except through the returned D (FP6; BM.3–BM.31 only touch X's own D).

Size statements (|S| bounds, |U| ≤ const·Λ_l, cost) are in S4 and use (R4), (R8). Note (agent-06 c5): (R4)
only gives |U| > τ; the S4 consequence "partial ⇒ |U| > t|S|" (S4 (B2)) additionally needs τ ≥ t·max|S|,
which is FIX-SIZE / FIX-L13 (3k ≤ t in pseudocode Sec. 2) and, for the inner top call, k ≥ t_in·1.

**Corollary S2.2 (top level).** For I_0 (source s, c ≡ ∞) and l_top with Λ_{l_top} ≥ n, the call
BMSSP(∞, {s}, l_top) returns U = {v : v reachable from s}, all complete, and D = ∅.
*Proof.* (C1) is vacuous (every reachable v has s ∈ path(v); unreachable v have dis = ∞ ⊀ ∞).
(C2): s is complete (d[s] = λ_s = dis(s), A3). (C3) ✓. By (R4), B' ≺ ∞ would force |U| > Λ_{l_top} ≥ n,
impossible, so B' = ∞, D = ∅, and U = Ũ(∞, {s}) = reachable set, complete (R1). Unreachable
vertices are never touched (a touched vertex has a finite label, hence finite dis, A3) and keep ∞. ∎

**Corollary S2.3 (inner top call).** For an inner instance I_x (S1 §C) the call
BMSSP_{I_x}(B, {x}, l*, τ = k) satisfies (C1)–(C3) (S1 Lemma D3), so (R1)–(R9) hold in I_x.

**Scope and composition.** Lemma S2.1 is a statement about ONE admissible instance and ONE FindPivots
routine satisfying FP. It is applied (i) to I_0 with FindPivots-B (FP by S3 §S3.2), (ii) to every inner
instance I_x with FindPivots-D (FP on any admissible instance by S3 §S3.1), and (iii) for iterated
bootstrapping, by induction on the depth: FindPivots-B running inside a deadline instance satisfies FP by
S3 §S3.5 (whose proof uses Lemma S2.1 for the next depth), and nested instances are admissible by S1 R5.
The induction is well founded: the depth-D routine uses only Lemma S2.1 at depth D + 1, and the deepest
depth uses FindPivots-D.

---------------------------------------------------------------------------------------------------

## S2.3 Proof of Lemma S2.1 for l = 0 (BaseCase)

During BaseCase only its own BC.7 relaxations change labels, and each changed label is immediately
inserted, so
 (K0) val(y) = d[y] for every key y at all times.
Let u_1, u_2, … be the extracted vertices in order.

(K1) *Extracted stored values are strictly increasing, and every insertion after the extraction of
u_j has value ≻ d[u_j].* Initially keys = S. When u_j is extracted it is the minimum key; every later
insertion is cand = d[u_{j'}] ⊕ e ≻ d[u_{j'}] (T2) for some j' ≥ j, and by induction d[u_{j'}] ⪰ d[u_j].

(K2) *keys(D) ∩ U = ∅ and no vertex is extracted twice.* A key enters U only by extraction, which
removes it from D. It remains to show that no valid relaxation ever targets a vertex w ∈ U. Let the
relaxation be executed while processing u_j (BC.7), and let w = u_{j''} with j'' ≤ j. A self-loop
(w = u_j) is never valid (T2). For j'' < j, w is complete since its extraction (K4, induction on j) and
d[w] ≺ d[u_j] by (K1); a valid relaxation into w needs cand ⪯ d[w], but cand = d[u_j] ⊕ e ≻ d[u_j] ≻ d[w]
(T2). So w is never re-inserted.

(K3) *Frontier.* Every v ∈ Ũ \ U has a certified key on path(v) (before each extraction).
Initially U = ∅ and (C2) gives a complete x ∈ S on path(v); x is a key with val(x) = d[x] (K0).
Maintenance: when u is extracted, only vertices v whose certified key was u can lose their witness.
Let a be the last vertex of path(v) lying in U (after adding u; a exists since u ∈ path(v)) and b the
successor of a on path(v) (exists, v ∉ U). a is complete (K4), dis(b) ⪯ dis(v) ≺ B. When a was
extracted (now or earlier) BC.7 executed Relax(a, b, e*, B), which is valid and makes b complete
(A4), and inserted b with value dis(b). b ∉ U; keys leave the base-case D only by extraction (BC.6), so b
is still a key, certified by (K0).

(K4) *Every extracted vertex is complete.* u = the minimum key; u ∈ Ũ (u ∈ S, or touched: R6).
If u were incomplete, (K3) gives a certified key y ≠ u on path(u) with val(y) = dis(y) ≺ dis(u) ⪯ d[u]
= val(u) (A1 strictness, A3, K0), contradicting minimality.

At return: if D = ∅ then B' = B; (K3) with no keys means Ũ ⊆ U; U ⊆ Ũ since extracted vertices are
keys, hence in Ũ (R6); so U = Ũ = Ũ(B, S). If D ≠ ∅, the loop stopped because |U| ≥ τ, and
B' = min stored value ≺ B. By (K1), B' ≻ d[u_last] ⪰ d[u] = dis(u) for all u ∈ U, so U ⊆ Ũ(B', S).
Conversely a v ∈ Ũ(B', S) \ U would have (K3) a certified key y with val(y) = dis(y) ⪯ dis(v) ≺ B' =
min stored value — impossible. So U = Ũ(B', S): (R1), (R4). (R2) = (K3). (R3): keys ⊆ Ũ (S or
touched, R6), ∉ U (K2); val ≺ B (Relax bound); val = d ⪰ dis; dis(y) ⪰ B' since otherwise
y ∈ Ũ(B', S) = U. (R5): B' = B ⪰ dis(S), or B' = val(y) ⪰ dis(y) ⪰ dis(x) for the S-vertex x on
path(y). (R7): S-keys leave D only by extraction; stored values only decrease. (R6): S1 L3+. ∎

---------------------------------------------------------------------------------------------------

## S2.4 Proof of Lemma S2.1 for l ≥ 1

Induction on l; for the sub-calls we use Lemma S2.1 at level l − 1 (their preconditions are verified
in Step 2). Fix X = BMSSP(B, S, l, τ) satisfying (C1)–(C3). Ũ := Ũ(B, S).

### Step 0: the sets A and W^c

After BM.4, let P_ini := P_1 ∪ … ∪ P_p and define
  A := { v ∈ Ũ : path(v) contains a vertex of P_ini that is complete at the end of BM.4 }.
By FP1, every v ∈ Ũ \ A is in W and complete ("W^c-vertices").
(A-closure) If v ∈ A, y ∈ Ũ and v is on path(y), then y ∈ A (path(v) is a prefix of path(y), A1).
(A-contains-P) P_ini ⊆ A: x ∈ P_ini lies in Ũ (C3); if x is complete, x itself is the witness;
if x is incomplete, x is not a W^c-vertex, so x ∈ A by FP1.
(A-bound) dis(v) ⪰ B'_0 for all v ∈ A: path(v) contains a complete y ∈ P_j for some j, and
dis(v) ⪰ dis(y) = d[y] ⪰ d[p_j] ⪰ B'_0 (A1, BM.7 argmin, BM.8).

### Step 1: loop invariants

Call y **certified** (at a given moment) if y is complete and either
 (a) y is a certified key of D (val(y) = d[y]), or
 (b) y ∈ P_j for some j, p_j ∈ keys(D) and val(p_j) ⪯ d[y].
At the start of iteration i (i.e. before BM.10; for i = 1 right after BM.8), with
U = U_1 ∪ … ∪ U_{i−1}:
 (J1) U ⊆ A, U is complete, and A ∩ {dis ≺ B'_{i−1}} ⊆ U ⊆ {dis ≺ B'_{i−1}}.
 (J2) keys(D) ∪ P ⊆ A \ U, where P := P_1 ∪ … ∪ P_p (current, after removals), and
      dis(y) ⪰ B'_{i−1} for every y ∈ keys(D) ∪ P.
 (J3) every v ∈ A \ U has a certified vertex on path(v).
 (J4) for every j with P_j ≠ ∅: p_j ∈ P_j and p_j ∈ keys(D).
 (J5) U_1, …, U_{i−1} are pairwise disjoint; B'_0 ⪯ B'_1 ⪯ … ⪯ B'_{i−1}.

*Initialization (i = 1).* U = ∅. (J1): A ∩ {dis ≺ B'_0} = ∅ by (A-bound). (J2): keys(D) = pivots
⊆ P_ini ⊆ A (A-contains-P); dis ⪰ B'_0 on A (A-bound). (J3): for v ∈ A pick a complete y ∈ P_j on
path(v); p_j is a key with val(p_j) = d[p_j] ⪯ d[y] (BM.7), so y is certified (b). (J4): BM.7.
(J5) trivial.

### Step 2: the sub-call satisfies (C1)–(C3)

Fix iteration i. Let S_i be the set after BM.12. Two facts:
 (S-a) S_i ⊆ keys(D) ∪ P (as of BM.10) ⊆ A \ U and dis(S_i) ⪰ B'_{i−1}   [J2].
 (S-b) every certified y with dis(y) ≺ B_i lies in S_i. If y is certified by (a), val(y) = dis(y) ≺ B_i,
       so y ∈ S_i by (PP). If by (b), val(p_j) ⪯ d[y] = dis(y) ≺ B_i, so p_j (a key, J4) is pulled
       (PP), p_j is P_j's current pivot, and BM.12 adds {v ∈ P_j : d[v] ≺ B_i} ∋ y.
Let Ũ_i := Ũ(B_i, S_i). Every v ∈ Ũ_i lies in A \ U: path(v) visits some z ∈ S_i ⊆ A, and
dis(v) ≺ B_i ⪯ B (PP: x ⪯ B), so v ∈ Ũ; v ∈ A by (A-closure); dis(v) ⪰ dis(z) ⪰ B'_{i−1}, so v ∉ U (J1).
(C3): pulled keys have d ⪯ val ≺ B_i (V1, PP); BM.12 additions have d ≺ B_i; S_i ≠ ∅ (PP).
(C2): v ∈ Ũ_i ⊆ A \ U has, by (J3), a certified y on path(v); dis(y) ⪯ dis(v) ≺ B_i, so y ∈ S_i
by (S-b), and y is complete.
(C1): let dis(v) ≺ B_i and v ∉ Ũ_i. If v ∉ Ũ: complete by (C1) for X (and completeness persists).
If v ∈ Ũ \ A: complete (W^c). If v ∈ U: complete (J1). If v ∈ A \ U: (J3) gives a certified y on
path(v) with dis(y) ≺ B_i, so y ∈ S_i (S-b) and v ∈ Ũ_i — contradiction.
Hence Lemma S2.1 (level l − 1) applies to the sub-call: (R1)–(R9) hold for (B'_i, U_i, D_i). Note D is
not modified during the sub-call (R9, FP6).

### Step 3: characterization of U_i (gives J1, J5 for i + 1)

(B-mono) B'_i ⪰ B'_{i−1}: by (R5) for the sub-call and (S-a), B'_i ⪰ min dis(S_i) ⪰ B'_{i−1}.
(U-in) U_i ⊆ A ∩ {B'_{i−1} ⪯ dis ≺ B'_i}: U_i = Ũ(B'_i, S_i) ⊆ Ũ_i ⊆ A \ U (Step 2), and every
u ∈ U_i has dis(u) ⪰ dis(z) ⪰ B'_{i−1} for the z ∈ S_i on path(u).
(U-out) A ∩ {B'_{i−1} ⪯ dis ≺ B'_i} ⊆ U_i: such v is not in U (J1), so (J3) gives a certified y on
path(v); dis(y) ≺ B'_i ⪯ B_i, so y ∈ S_i (S-b); thus v ∈ Ũ(B'_i, S_i) = U_i.
Hence U_i is disjoint from U (U ⊆ {dis ≺ B'_{i−1}}), complete (R1), and U ∪ U_i satisfies (J1) with
B'_i; (J5) holds.

### Step 4: maintenance of (J2)–(J4) through BM.14–BM.24

(Equality re-relaxations at BM.20: an edge already relaxed by the sub-call may be re-relaxed here with
cand = d[v] (re-confirmation, Relax returns True); such cand is ≺ B_i whenever the sub-call made it, so the
test d[u] ⊕ e ⪰ B_i rejects it and no insertion results. Only cand ⪰ B_i leads to BM.21.)
Keys after BM.24 are of four kinds.
(k1) old keys (in D before BM.10, not pulled). A pulled key is removed by Pull; an old key y ∈ U_i is
     deleted by BM.15. So a surviving old key y lies in A \ (U ∪ U_i) (J2), hence dis(y) ⪰ B'_i by
     the new (J1).
(k2) keys of D_i (BM.14). By (R3) for the sub-call: y ∈ Ũ_i \ U_i ⊆ A, and dis(y) ⪰ B'_i; so
     y ∉ U ∪ U_i (dis ranges). BM.15 therefore deletes none of them.
(k3) BM.21 insertions v. The relaxation (u, v) is valid with u ∈ U_i, so v ∈ Ũ (R6 for X). If v is
     complete, then cand ⪯ d[v] = dis(v) ⪯ cand, so cand = dis(v); equality of labels means equality of
     the represented walks (TV: the last-edge field; T4: the pred field), so u = p*(v), e is the canonical
     edge and path(v) = path(u) ∘ e (A1): v ∈ A by (A-closure) (u ∈ U_i ⊆ A). If v is incomplete then v is no W^c-vertex, so v ∈ A
     (FP1). Moreover v ∉ U ∪ U_i: a complete w ∈ U ∪ U_i has dis(w) ≺ B'_i ⪯ B_i ⪯ cand, while a
     valid relaxation into w needs cand ⪯ d[w] = dis(w). Hence dis(v) ⪰ B'_i by (J1).
(k4) BM.23 pivots: vertices of P_j, which avoid U ∪ U_i by BM.17 (P-vertices are removed when
     they enter U_i and never re-enter P).
So (J2) holds at the start of iteration i + 1 (P ⊆ A \ (U ∪ U_i) likewise).

(J4): let P_j ≠ ∅ after BM.23.
 - If j ∈ J: BM.23 re-selected p_j ∈ P_j and inserted it.
 - Else, if BM.22 changed p_j to v in this iteration: v ∈ P_j was inserted at BM.21.
 - Else p_j is unchanged and p_j ∉ U_i (otherwise j ∈ J). If p_j was not pulled at BM.10 it is still a
   key (it is not deleted by BM.15). If p_j was pulled, then p_j ∈ S_i \ U_i, so p_j ∈ keys(D_i) by (R7)
   for the sub-call, and BM.14 re-inserted it; BM.15 does not delete it.

(J3): let v ∈ A \ (U ∪ U_i) and let y be the certified vertex on path(v) at the start of iteration i.
We exhibit a certified vertex on path(v) after BM.24. Recall the sub-call does not modify D, and
certification (a) or (b) at the start of the iteration refers to D before BM.10.
 Case 1: some vertex of path(v) lies in U_i. Let a be the LAST vertex of path(v) in U_i and b its
   successor on path(v) (v ∉ U_i). a is complete (R1); dis(b) ⪯ dis(v) ≺ B.
   - If dis(b) ≺ B_i: path(b) = path(a) ∘ e* visits S_i (a ∈ U_i ⊆ Ũ_i), so b ∈ Ũ_i \ U_i; by (R2) for
     the sub-call there is a certified key y' of D_i on path(b) ⊆ path(v). After BM.14
     val_D(y') = min(old, val_{D_i}(y')) = dis(y') (both ⪰ dis(y') by V2); y' ∉ U_i (R3), so BM.15
     keeps it: y' is a certified key of D.
   - If dis(b) ⪰ B_i: BM.19–20 relax (a, b, e*) with bound B: valid, b becomes complete (A4), and
     cand = dis(b) ⪰ B_i, so BM.21 inserts b with value dis(b): b is a certified key.
 Case 2: no vertex of path(v) lies in U_i. Then y ∉ U_i.
   - 2a: y ∈ S_i. Then y ∈ Ũ_i \ U_i, and (R2) for the sub-call gives a certified key y' of D_i on
     path(y) ⊆ path(v); as in Case 1, y' is a certified key of D after BM.14–15.
   - 2b: y ∉ S_i and y was certified by (a). y was not pulled, so it is an old key; it is not in U_i, so
     BM.15 keeps it; its stored value is unchanged or decreased by BM.14/21, but it cannot drop
     below dis(y) = val(y) (V2). Still certified (a).
   - 2c: y ∉ S_i and y was certified by (b): y ∈ P_j (still, as y ∉ U_i), val(p_j) ⪯ d[y].
     · If j ∈ J (the old pivot entered U_i): P_j ∋ y is nonempty, BM.23 selects
       p_j = argmin_{P_j} d, inserted with value d[p_j] ⪯ d[y]: certified (b).
     · Else, if BM.22 changed p_j in this iteration, say through the pivots p^(0) = p_j(old), p^(1), …,
       p^(r) = final, in this order: each p^(s) (s ≥ 1) was inserted at BM.21 with value d[p^(s)] immediately
       before the change, and the change required d[p^(s−1)] ≻ d[p^(s)] at that moment. Hence, writing
       d_s for the label of p^(s) at the time of its own insertion,
         val(p^(r)) ⪯ d_r ≺ d[p^(r−1)] ⪯ val(p^(r−1)) ⪯ … ⪯ val(p^(1)) ⪯ d_1 ≺ d[p^(0)] ⪯ val(p^(0)) ⪯ d[y],
       using V1 at each change time and that stored values only decrease; d[y] is constant because y is
       complete. p^(r) is a key (inserted at BM.21, never deleted in this iteration since p^(r) ∉ U_i:
       BM.21 targets avoid U_i by (k3)). So y is certified (b). The old pivots p^(0..r−1) remain ORDINARY
       keys of D (no special role; BM.12 expands only through the current pivot).
     · Else p_j is unchanged and p_j ∉ U_i. If p_j was not pulled it is still a key with
       val(p_j) ⪯ d[y] (values only decrease). If p_j was pulled (p_j ∈ S_i \ U_i), then by (R7) for the
       sub-call p_j ∈ keys(D_i) with val_{D_i}(p_j) ⪯ d_0[p_j] ⪯ val_old(p_j) ⪯ d[y] (d_0 = label at
       the sub-call's start; V1 at BM.10), and BM.14 re-inserts it. Certified (b).
 In all cases path(v) has a certified vertex after BM.24. ∎(Step 4)

### Step 5: termination and the return values

*Every iteration has U_i ≠ ∅.* S_i ≠ ∅ and S_i ⊆ Ũ(B_i, S_i) (C3 for the sub-call). If B'_i = B_i then
U_i = Ũ(B_i, S_i) ⊇ S_i ≠ ∅ (R1). Otherwise B'_i ≺ B_i and (R4) for the sub-call gives |U_i| ≥ τ_{l−1} ≥ 1.
Since the U_i are pairwise disjoint (J5) subsets of V, the loop runs at most |V| times; recursion depth
is l, and FindPivots terminates (FP). Hence X terminates.

Let f ≥ 0 be the number of iterations.
(i) If the loop stops with D = ∅, then (J3) forces A \ U = ∅ (a certified vertex needs a key of D:
    (a) directly, (b) through p_j), i.e. A ⊆ U; BM.24a sets B' := B. If f = 0 this is the case p = 0.
(ii) Otherwise |U| > τ, and B' = B'_f. We claim B'_f ≺ B: by (J2) every key y has
    B'_f ⪯ dis(y) ⪯ val(y) ≺ B.
In both cases (J1) gives
 (E) A ∩ {dis ≺ B'} ⊆ U ⊆ A ∩ {dis ≺ B'}   (case (i): A ⊆ U ⊆ {dis ≺ B'_f} ⊆ {dis ≺ B}).

*W' is complete.* Let x ∈ W' (x ∈ W \ U, d[x] ≺ B'). x ∈ Ũ (FP3). If x were incomplete, x ∈ A
(not W^c), and dis(x) ⪯ d[x] ≺ B', so x ∈ U by (E) — contradiction.

(R1) U_fin := U ∪ W'. ⊆: U ⊆ Ũ ∩ {dis ≺ B'} by (E); W' ⊆ Ũ with dis ⪯ d ≺ B'. ⊇: let v ∈ Ũ,
dis(v) ≺ B'. If v ∈ A then v ∈ U (E). Otherwise v is a W^c-vertex: v ∈ W, complete, d[v] = dis(v) ≺ B',
so v ∈ U or v ∈ W'. All of U_fin is complete. B' ⪯ B.
(R8) from (J5), Step 3 and the definition of W' (W' ∩ U = ∅).
(R3) Keys at the end of the loop have dis ⪰ B'_f (J2); in case (i) there are none, in case (ii)
B' = B'_f. Keys inserted at BM.25/BM.28 have d ⪰ B'; such a key y cannot be in U_fin: y ∈ U_fin would
be complete with dis(y) ≺ B' ⪯ d[y] = dis(y). So keys ∉ U_fin and, for every key, dis(y) ⪰ B' (else
y ∈ Ũ(B', S) = U_fin, using keys ⊆ Ũ: every key is an S-vertex or touched, R6). val ≺ B for every
insertion (Relax bound B; S-vertices have d ≺ B, C3; stored values of D_i are ≺ B_i ⪯ B). Chain
B' ⪯ dis ⪯ d ⪯ val by V1–V2.
(R4) Case (i): B' = B; BM.25 (needs B ⪯ d[x] ≺ B) and BM.28 (needs cand ⪰ B and cand ≺ B) insert
nothing, so D = ∅. Case (ii): B' ≺ B, |U_fin| ≥ |U| > τ. Hence B' = B ⟺ D = ∅.
(R2) Let v ∈ Ũ \ U_fin; by (R1) dis(v) ⪰ B'. In case (i) Ũ \ U_fin = ∅ (Ũ ⊆ {dis ≺ B} = {dis ≺ B'}).
In case (ii):
 - v ∈ A \ U: (J3) at loop end gives a certified y on path(v). If (a): y remains a certified key (the
   only later deletion, BM.29, deletes W'-vertices, and y ∉ W' since d[y] = dis(y) ⪰ B'). If (b): y ∈ P_j ⊆ S is complete and y ∉ U (P ∩ U = ∅), so y ∈ A \ U and
   dis(y) ⪰ B' (E); d[y] = dis(y) ∈ [B', B) (y ∈ Ũ), so BM.25 inserts y with value dis(y): certified.
 - v ∈ Ũ \ A (a W^c-vertex). By (C2) path(v) contains a vertex of S that was complete at X's start; let
   q be the first such vertex. q ∉ P_ini (else v ∈ A, completeness persists), so q ∈ Q (FP2). Let
   q = z_0, z_1, …, z_r = v be the part of path(v) from q. Each z_j ∈ Ũ (dis(z_j) ⪯ dis(v) ≺ B and
   q ∈ path(z_j)), and z_j ∉ A (else v ∈ A by A-closure), so each z_j is a W^c-vertex (in W, complete)
   and z_j ∉ U (U ⊆ A). Hence z_j ∈ U_fin ⟺ z_j ∈ W' ⟺ dis(z_j) ≺ B'. As dis increases along the path,
   these z_j form a prefix z_0 … z_{a−1} with a ≤ r (v ∉ U_fin).
   · a = 0: dis(q) = d[q] ∈ [B', B), so BM.25 inserts q with value dis(q): certified, on path(v).
   · a ≥ 1: z_{a−1} ∈ W' is complete and dis(z_a) ≺ B, so the BM.27–28 relaxation of (z_{a−1}, z_a, e*)
     is valid, makes z_a complete (A4), and cand = dis(z_a) ⪰ B', so z_a is inserted with value
     dis(z_a): certified, on path(v).
(R5) Case (i): B' = B ≻ dis(x) for x ∈ S (C3). Case (ii): B' = B'_f ⪰ … ⪰ B'_0 ⪰ min_j d[p_j]
 ⪰ min_j dis(p_j) ⪰ min_{x∈S} dis(x).
(R6) S1 Lemma L3+ (hypotheses (C1), (C3), SP; FP5 covers FindPivots).
(R7) Let x ∈ S \ U_fin. x ∈ Ũ (C3), so dis(x) ⪰ B' by (R1); d[x] ⪰ dis(x) ⪰ B' and d[x] ≺ B, so BM.25
 inserts x with value d[x] ⪯ d_0[x] (A3).
(R9) By inspection and FP6. ∎ (Lemma S2.1)

---------------------------------------------------------------------------------------------------

## S2.5 What changed relative to DMSY26 Lemma 3.7, and why the new statement suffices

1. DMSY26 states ⟨U, D⟩ is a frontier using CURRENT labels and D ⊇ (S \ U) ∪ R(B, U). With stale
   stored values this is not what Pull needs. (R2) (certified frontier: complete keys whose STORED
   value equals the label) is exactly what the parent's Pull uses (S-b), and it is maintained.
2. P̂_j (DMSY26's "necessary vertices") is replaced by certification (b): only COMPLETE P-vertices
   need to be covered by their group's pivot, and the invariant is on the pivot's STORED value
   (val(p_j) ⪯ d[y]), which is what Pull tests (agent-02's (3') is the same observation).
3. Disjointness/interval structure (R8) is derived from the characterization Step 3, which needs
   (J2): no key of D is ever in U — this is where FIX-STALE (BM.15) is used (k1).
4. Nothing here uses ancestor closure (A2'): every "complete" vertex used as a witness is shown
   complete directly (by (C2), FP1, (R1), A4).
5. The time analysis (S4) additionally needs: (R4) (partial ⇒ |U| > τ), (R8) (disjoint U_i, so
   Σ_i |U_i| ≤ |U|), (R3)/(R7) for insertion counting, and Observation 3.5 (each edge enters BM.20
   at most once): this is Lemma S2.5 below.
7. Lazy done-filter (agent-09 N1). Implementations that, instead of BM.15, discard keys already in U at
   Pull time (a per-INSTANCE done flag; inner instances have their own flags) are equivalent provided that
   (a) Pull never returns a done key, (b) flags are per instance, and (c) either "D ≠ ∅" counts only live
   keys, or an iteration whose filtered pull is empty is allowed: then the sub-call has S = ∅ and must
   return (B_i, ∅, ∅) in O(1), charged to the ≥ 1 discarded entry. With (c)-second option Lemma S2.1 must be
   read with S = ∅ allowed in sub-calls (trivial). The master pseudocode uses deletion, where S_i ≠ ∅ always.

6. Pivot invariant. agent-02's (3') ("val(p_j) ⪯ d[v] for all v ∈ P̂_j") is NOT maintained by BM.22,
   which compares the pivot's CURRENT label (editor_check_S2.md). S2 never needs (3'): certification (b)
   is required only for COMPLETE vertices y ∈ P_j, whose labels never change, and it is preserved by
   BM.22 because a switch to v' happens only when d[v'] ≺ d[p_j] ⪯ val(p_j), and v' was just inserted with
   val(v') = d[v'] (Step 4, Case 2c). A non-complete v ∈ P_j needs no pivot coverage at all: (J3) only
   requires SOME certified vertex on each path. This is the editor's (J4') restricted to complete vertices;
   BM.22 is therefore correct but optional (removing it keeps every invariant).

---------------------------------------------------------------------------------------------------

## S2.4b Lemma S2.4 (settled vertices are scanned while complete)

**Lemma S2.4.** Let X = BMSSP(B, S, l, τ) satisfy (C1)–(C3) and return (B', U, D). For every u ∈ U and
every out-edge e of u in the host graph, X executes (directly, not only in a descendant) a call
Relax(u, e, B) — with X's OWN bound B — at a moment when u is complete.
*Proof.* l = 0: u was extracted at BC.6, is complete from then on (K4), and BC.7 scans all of Out(u) with
bound B. l ≥ 1: if u ∈ U_i, then u is complete when the sub-call returns (R1 of the child) and BM.19–20
scan Out(u) with bound B; if u ∈ W', u is complete (Step 5) and BM.27–28 scan Out(u) with bound B. ∎
Use (S1 Remark 4, suppression semantics): if the TOP call of InnerSearch(x) is full, every u ∈ U_x is
scanned with the outer bound B while complete in I_x; a would-be-valid relaxation into a sink at that
moment is recorded as a hit (RX.4–5). Hence "full and no hit" implies that no sink is admissibly
reachable, i.e. the blocking was vacuous.

---------------------------------------------------------------------------------------------------

## S2.4c Lemma S2.5 (insertion-event uniqueness; used by S4 G2 and G4)

Call an *insertion event of edge e = (u, v)* a D.Insert(v, ·) executed immediately after a valid
Relax(u, e, ·) at BM.21, BM.28 or BC.7 of some call of the instance.

**Lemma S2.5.** In a run of the top call on an admissible instance (with all calls satisfying (C1)–(C3)),
every edge e = (u, v) has at most one insertion event. FindPivots (FP6) and inner runs (private D's) cause
none in the host instance.
*Proof.* BM.19/BM.27/BC.7 relax out-edges only of vertices of a child's U_i, of W', or of extracted
vertices, respectively; so an insertion event of e occurs only in calls X whose returned U contains u, and
in each such call the out-edges of u are scanned at most once (U_i disjoint (R8); W' and extraction once).
The calls whose U contains u form a chain X_0 ⊃ X_1 ⊃ … ⊃ X_q (U's of calls at one level are disjoint, by
(R8) applied inductively; each U_{X_{r+1}} ⊆ U_{X_r}), where X_q is the call in which u itself was settled
(extracted in a base case, or u ∈ W'_{X_q}). All scans of u happen after u became complete (Lemma S2.4),
and u's label never changes afterwards (in particular ver[u] does not change), so every scan of e computes
the SAME candidate c := dis(u) ⊕ e. The insertion windows are:
 - at X_r (r < q), BM.20: c ⪰ B_{X_{r+1}} (the child's bound) and c ≺ B_{X_r} (Relax bound):
   c ∈ [B_{X_{r+1}}, B_{X_r});
 - at X_q: BM.28 requires c ∈ [B'_{X_q}, B_{X_q}), BC.7 requires c ≺ B_{X_q}; both ⊆ (−∞, B_{X_q}).
Since B_{X_q} ⪯ B_{X_{q−1}} ⪯ … ⪯ B_{X_0} (a child's bound is a Pull separator ⪯ its parent's bound, PP),
these windows are pairwise disjoint, so c lies in at most one of them. ∎

---------------------------------------------------------------------------------------------------

## S2.6 Executable check

bdmsy.py implements BM/BC as above (BM.15 switchable by fix_delete, BM.24a by full_fix; BM.29 omitted,
which is justified by (R3)), classic FindPivots (DMSY26 Alg. 2) and FindPivots-B. With check=True it asserts,
for EVERY call of EVERY instance (outer I_0 and each inner I_x, with an oracle computed for that
instance from the caps at its start): (C1) as Pre2, (C2) as Pre1, (R1), (R2) (certified-key frontier),
(R3) (incl. val ⪰ d), (R4), (R6), and U_i-disjointness. Status (2026-09-20 ~08:00Z): 150 + 150
trials (classic, bootstrapped) with 0 violations; background run of 3200 more in progress
(impl/bg_tests_1.log). With fix_delete=False, 48/300 trials violate DISJ/(R3) (gap_demo.py).


## Appendix D — S3 FindPivots-D / FindPivots-B satisfy FP (agent-08)

Frozen label `S3v1.4`, source `/research/agents/agent-08/work/S3_findpivots.md`, sha256 `e76ae63b93b304163847fe2cb0201ac83c6823e99923bf887c7950a6a176b363`, frozen 2026-09-20T07:51:13Z.

# S3 — FindPivots-D and FindPivots-B satisfy the FP contract (agent-08), v1.4, 2026-09-20

v1.4: agent-09 formal review #1 items T1 (the scan is by the TOP inner call, with bound B), T2 (tie semantics at
S3.2.3(i)), T4 (p-bound with N-trees), T5 (degenerate case: x touched by an earlier search); T3 was in v1.1.

v1.3: agent-06 formal review #2 minor items t1 (re-confirmation case in FD induction), t2 (sink labels
frozen during a search), t3 (k ≥ 2 only for the counting bound). t4 is for the master §4 (FP7 wording).

v1.2: agent-06 c4 (a failed root later absorbed into a tree stays in Q); agent-03 items (2) why U_x ⊆ N,
(3) completeness persistence and no blocking in FindPivots-D; editor: Theorem S3.6 states FP for
FindPivots-B on a GENERAL admissible host instance (needed for depth ≥ 3 nesting).

v1.1: bookkeeping bound Σ|N| ≤ min(|Ũ|, O(gk)|S|) in FP7(B) (agent-02, agent-03); explicit proof of x ∈ U_x;
cites S2 v1.2 (Lemma S2.4 = scan lemma, Lemma S2.5 = insertion-event uniqueness).

Status: written proof, NOT yet reviewed. Formal reviewers: agent-09, agent-06 (agent-03 third).
Algorithm text: MASTER pseudocode agents/agent-04/work/pseudocode.md v2 (RX, OU, FD, MP, FB, TH, PT).
Wall semantics: SUPPRESSION (master ruling 07:34:58; RX.4–5). The sink ("relax-into") variant is §S3.4.
Dependencies: S1 (agent-02 L1_foundations.md v2.5: A1, A3, A4, T2, D1–D3, SP/SP', L3+, Claim C),
S2 (agent-08 S2_core.md v1.2: Lemma S2.1, Corollary S2.3, Lemma S2.4 (scan), Lemma S2.5). No ancestor
closure is used.

Context for both routines. X = BMSSP(B, S, l) is a call on an admissible host instance I (host graph H,
normally I = I_0) such that (C1) Claim C holds at X's start, (C2) ⟨∅, S⟩ is a frontier for
Ũ := Ũ(B, S), (C3) d[x] ≺ B for all x ∈ S. FindPivots(B, S) is executed at BM.4 with integer k ≥ 2.

**FP (restated; MASTER §4 with the FP7 correction of §S3.1.4).**
- FP1 ⟨W, P_ini⟩ is a frontier for Ũ, P_ini := P_1 ∪ … ∪ P_p: every v ∈ Ũ is (in W and complete) or
  path(v) contains a vertex of P_ini that is complete when FindPivots returns.
- FP2 P_1, …, P_p, Q are pairwise disjoint, nonempty, with union S.
- FP3 Q ⊆ W ⊆ Ũ; W = ⋃_{x∈Q} W_x with x ∈ W_x and |W_x| < k; hence |W| < k|Q|.
- FP4 there are pairwise vertex-disjoint trees F̄_1, … (pre-partition trees), each with ≥ k vertices,
  all inside Ũ, over edges of H (as undirected graphs); F_1, …, F_p are pairwise edge-disjoint subtrees
  with P_j ⊆ V(F_j) and |V(F_j)| < 3k; p ≤ |S| and p ≤ Σ(|V(F̄)| − 1)/(k − 1) ≤ |Ũ|/(k − 1).
- FP5 (SP) every Relax(u, ·) executed has u ∈ S or u touched earlier in X; hence (L3+) every vertex whose
  label changes, and every vertex placed in a tree or in W, lies in Ũ.
- FP6 no operation on any D structure of any BMSSP call of the host instance.
- FP7 time (§S3.1.4, §S3.2.5).

---------------------------------------------------------------------------------------------------

## S3.1 FindPivots-D (FD.1–FD.21, MP.1–MP.10) on any admissible instance

Used by the inner algorithm (instances I_x) and valid on any admissible instance (in particular on I_0,
where it is DMSY26 Alg. 2). One *search* = one execution of FD.5–FD.19 for one x ∈ S.

### S3.1.1 Local facts about one search from x

(D-a) *Heap discipline.* Every vertex in the Fibonacci heap H has heap key = its current label (FD.16
inserts or decrease-keys after every valid relaxation of a vertex of H; nothing else changes labels
during the search).
(D-b) *Extraction keys strictly increase, and no extracted vertex is relaxed again in the same search.*
When u is extracted it has the minimum key; every later valid relaxation produces cand = d[u'] ⊕ e ≻ d[u']
(T2) for an extracted u' whose key is ⪰ d[u] (induction). A valid relaxation into an already extracted w
would need cand ⪯ d[w] ⪯ d[u'] (w extracted before u', its label unchanged by induction) — impossible.
Hence FD.16 never re-inserts an extracted vertex; extracted vertices keep their labels during the search.
(D-c) *K is an arborescence.* K = {x} ∪ {vertices validly relaxed during the search}. For y ∈ K \ {x},
kpar1[y] = (u, e) where u is the vertex being processed at y's last relaxation (FD.11), so u ∈ K is
extracted, and by (D-b) either y is never extracted or it is extracted after u. Hence kpar1 pointers
strictly decrease the extraction index; (K, {kpar1[y]}) is a tree with |K| − 1 edges rooted at x, over
edges of H.
(D-d) *Vertices of K and trees.* The trees of the current invocation do not change during a search.
Every y ∈ K \ {x} was tested at FD.12 when first added; x was tested at FD.4. So if the search reaches
FD.17/FD.19, K ∩ (existing trees) = ∅; if it exits at FD.15, K ∩ (existing trees) = {v} (the hit vertex).
(D-e) *|K| ≤ k − 1 + δ.* The loop runs only while |K| < k, and one extraction adds ≤ δ vertices.

### S3.1.2 FP1 (frontier)

Let v ∈ Ũ. By (C2) path(v) contains a vertex q ∈ S that is complete at the start of FindPivots; q stays
complete (complete labels never change, A3), and so does every vertex that becomes complete later. If
q ∈ P_ini we are done. (Searches executed before q's search cannot block q's path: FindPivots-D has no walls;
an earlier tree met by q's search triggers FD.12–15, which puts q into a tree, i.e. q ∉ Q.) Otherwise q ∈ Q (FP2 below), i.e. the search from q ran (FD.4
did not skip it, else q would lie in a tree and hence in some P_j) and ended at FD.19: the loop exited with
|K| < k, so H = ∅, and FD.15 was never taken.
Let q = z_0, z_1, …, z_r = v be the part of path(v) from q. We show by induction on j that z_j is
extracted during q's search and is complete. j = 0: H = {q} initially, q complete. Step j → j + 1: when
z_j is extracted (complete), FD.8–9 execute Relax(z_j, e*, B) for the canonical edge e* = (z_j, z_{j+1});
since dis(z_{j+1}) ⪯ dis(v) ≺ B this relaxation is valid and makes z_{j+1} complete (A4) — possibly as a
re-confirmation, if an earlier search already set d[z_{j+1}] = dis(z_{j+1}); Relax still returns True, so
FD.10–FD.16 still put z_{j+1} into K and (below) into H. z_{j+1} is not in
an existing tree (else FD.15 would be taken). It has not been extracted before: an earlier extraction of
z_{j+1} would have heap key d[z_{j+1}] ⪰ dis(z_{j+1}) ≻ dis(z_j) = key of the LATER extraction of z_j,
contradicting (D-b). So FD.16 puts z_{j+1} into H, and since H is empty at the end, z_{j+1} is extracted
later, complete (labels never go below dis). Thus v = z_r ∈ K = W_q ⊆ W and v is complete. ∎

### S3.1.3 FP2–FP6

FP2. Q = the roots of searches ending at FD.19. P_j ⊆ S \ Q (MP.6), pairwise disjoint (assignment
stamp), nonempty (MP.8). Every x ∈ S \ Q lies in a tree at the end: it was skipped at FD.4 (then it is in a
tree), or its search ended at FD.13–15 (x ∈ K is added to T) or FD.17 (x ∈ K). Trees are never split or
shrunk, the partition groups of a tree cover all its vertices (PT, Lemma A.1), so MP.6 assigns x to the
first group containing it. Hence ⋃ P_j ∪ Q = S.
FP3. For x ∈ Q, W_x := K ∋ x with |K| < k (FD.19). W ⊆ Ũ: K ⊆ S ∪ touched, and L3+.
(agent-06 c4) A root q ∈ Q whose search failed may later be relaxed by another search and put into a tree.
It stays in Q (MP.6 excludes Q from every P_j), W_q is unchanged, and FP1's Q-case still applies to it:
completeness of the vertices of W_q, once established, persists.
FP4. Pre-partition trees: FD.17 creates (K, kpar1-edges), a tree with |K| ≥ k vertices (D-c); FD.13 adds
(K, kpar1-edges) to T, where K ∩ V(T) = {v} (D-d): the union of two trees sharing exactly one vertex is a
tree. Trees are vertex-disjoint (D-d), contained in S ∪ touched ⊆ Ũ (L3+), and have ≥ k vertices. PT
(DMSY26 Lemma A.1) splits each tree T into edge-disjoint subtrees with vertex counts in [k, 3k); groups of
different trees are vertex-disjoint. P_j ⊆ V(F_j) by MP.6. Counting: the P_j are disjoint nonempty subsets
of S, so p ≤ |S|; each group has ≥ k vertices, hence ≥ k − 1 edges, and the groups of T are edge-disjoint,
so T has ≤ (|V(T)| − 1)/(k − 1) groups; p ≤ Σ_T (|V(T)| − 1)/(k − 1) ≤ |Ũ|/(k − 1). (This count needs k ≥ 2,
which holds in the regime n' ≥ n_0 of S4; every correctness statement of S3 holds for all k ≥ 1.)
FP5. FD.9 relaxes from the extracted u, which is x ∈ S or was inserted into H after a valid relaxation
(touched). This is SP; L3+ gives the rest.
FP6. FD/MP use only the heap, the K lists, stamps and trees.

### S3.1.4 FP7 (time) — corrected statement

Each extraction costs O(log k) amortized (Fibonacci heap with ≤ k − 1 + δ elements, D-e) plus O(δ) for
scanning Out(u); each search costs O(|K| (δ + log k)) since every extracted vertex is in K.
- Failed searches: |K| < k, total O(|Q| k (δ + log k)).
- Searches ending in FD.13–15 or FD.17: K \ {hit vertex} consists of NEW tree vertices (D-d), so their total
  is ≤ Σ_T |V(T)| + |S|.
- MP and PT: O(Σ_T |V(T)| + |S|).
**FP7(D):** FindPivots-D costs O((Σ_T |V(T)| + |S| + k|Q|)(δ + log k)), with Σ_T |V(T)| ≤ min(|Ũ|,
(k − 1 + δ)|S|) (trees are disjoint subsets of Ũ; each search adds ≤ |K| ≤ k − 1 + δ new vertices).
(The MASTER §4 wording "O((p' + |Q|) k (δ + log k)), p' = number of pre-partition trees" undercounts
merges: a tree can absorb many merged searches. The corrected form above is what DMSY26's own time
analysis actually uses: Σ_T|V(T)| ≤ |U| in full executions and ≤ (k+δ)|S| ≤ (k+δ)|U|/t in partial ones.)

---------------------------------------------------------------------------------------------------

## S3.2 FindPivots-B (FB.1–FB.21, TH, RX.4–5): bootstrapped, suppression semantics

One *search* = one execution of FB.5–FB.19 for one x ∈ S. During it (HOOK = 1) the sink set
Z = {v : sinkstamp[v] = ZSTAMP} = vertices of the trees built so far in this invocation is frozen, and
Relax suppresses every would-be-valid relaxation into Z, recording it as a hit (RX.4–5).

### S3.2.1 The inner run is a correct BMSSP run on I_x

Let d_0 be the labels at FB.5. By S1 §C (suppression variant) the inner run FB.6 is the run of BMSSP
(with FindPivots-D inside, parameter record Pin) on the admissible instance
  I_x = (G_x, x, λ_x = d_0[x], c_x = d_0|R_x),  G_x = H[R_x ∪ {x}],  R_x ∩ Z = ∅,
in the sense of S1 D2 (every performed valid relaxation stays inside G_x; every other scanned edge is a
no-op or a hit; all non-Relax reads concern vertices of R_x ∪ {x}, SP'). By S1 D3 and Corollary S2.3 the
top inner call BMSSP_{I_x}(B, {x}, l_in, τ = k) satisfies (C1)–(C3) in I_x, so by Lemma S2.1 (in I_x;
FindPivots-D satisfies FP on I_x by §S3.1, which holds for every admissible instance):
 (I-1) U_x = Ũ_{I_x}(B'_x, {x}), complete in I_x (d[v] = dis_{I_x}(v) for v ∈ U_x); and x ∈ U_x:
       U_x ≠ ∅ (if B'_x = B then U_x = R_x ∪ {x} ∋ x by (I-3); if B'_x ≺ B then |U_x| > k ≥ 1 by (I-2)), and
       every v ∈ U_x has x ∈ path_{I_x}(v) with dis_{I_x}(x) = λ_x ⪯ dis_{I_x}(v) ≺ B'_x, so x ∈ U_x.
 (I-2) B'_x = B ⟺ D_x = ∅; if B'_x ≺ B then |U_x| > k (R4 with τ = k).
 (I-3) If B'_x = B ("full"), then U_x = Ũ_{I_x}(B, {x}) = R_x ∪ {x} (S1 D1).
 (I-4) (Lemma S2.4) every u ∈ U_x has all of Out(u) Relax-scanned with bound B by the top inner call while
       u is complete in I_x.
Let N := {x} ∪ {vertices touched during the inner run} (FB.9; TH collects exactly the vertices for which
RX.8 fired). Since suppressed relaxations never touch, N ∩ Z = ∅. By SP (inner run) and L3+ (host), N ⊆ Ũ.
Also U_x ⊆ N: a vertex other than x enters any structure of the inner run (an inner D, a base-case BST, a
FindPivots-D heap or K-list, W, P_j, U) only after a valid relaxation of it in the run (SP'), i.e. only after
it was touched; every vertex of U_x entered some such structure.

### S3.2.2 The tree edges (FB.10) form an arborescence of H on N rooted at x

For v ∈ N \ {x}, tpar0[v] := d[v].e, read at FB.10 (right after the run). Its tail u lies in N: if d[v] was
last written (strict decrease) during the run, the writer's tail relaxed in the run, so it is x or touched
earlier (SP); otherwise every touch of v in the run was a re-confirmation from some u with
cand = d[u] ⊕ e = d[v] (equality of represented walks), so d[v].e = e, tail(e) = u, and u relaxed in the run
(this is agent-01's note (a); under (TV) labels equality means identical walk, hence identical last edge).
Along tpar0 labels strictly decrease: d[v] = (u's label at write/re-confirmation time) ⊕ e ≻ that label
⪰ u's current label (T2, A3). Hence tpar0 has no cycles; x is never validly relaxed in its own run (a walk
returning to x has W_x as a proper prefix, O3/A3 in I_x), so x is the unique root. (N, {tpar0[v]}) is a tree
with |N| − 1 edges of H.

### S3.2.3 FP1 (frontier) — the failed-search exactness

Let v ∈ Ũ and let q ∈ S be complete (at FindPivots' start) on path(v) (C2). If q ∈ P_ini, done.
Otherwise q ∈ Q: q was not skipped at FB.4 (else q lies in a tree, hence in some P_j), and its search
ended at FB.18–19: B'_q = B (full), |U_q| < k, and hitlist = ∅.
Let q = z_0, …, z_r = v be the part of path(v) from q, and let d_0, Z be the labels and sinks at q's FB.5.
Since d_0[q] = dis(q), the walk W_q represented by λ_q is path(q) (under the (TV) labels of the final ruling,
equality of labels is equality of represented walks; under bare 4-tuples one only gets (len, hops) of W_q =
(len, hops) of path(q), which suffices here because L_q(·) of an extension depends only on (len, hops) of
W_q, the end vertex and the last edge). So for every j the label L_q(z_0 … z_j) of W_q ∘ (z_0 … z_j) equals
the label of path(z_j), i.e. dis(z_j) (A1). Hence
 (i) L_q(z_0 … z_j) = dis(z_j) ⪯ d_0[z_j] (A3 in I) and dis(z_j) ⪯ dis(v) ≺ B.
 (ii) No z_j (j ≥ 1) is a sink. Otherwise let j ≥ 1 be minimal with z_j ∈ Z. The walk z_0 … z_{j−1} is
      admissible for I_q (by (i) and minimality), so z_{j−1} ∈ R_q ∪ {q} = U_q (I-3). By (I-4) — Lemma S2.4
      applied to the TOP inner call, whose own bound is the outer B (relaxations inside deeper inner calls,
      with bounds B_i ≺ B, would not suffice for candidates ⪰ B_i; if l_in = 0 the top call is a base case and
      BC.7 scans with bound B as well) — the top inner call executed Relax(z_{j−1}, e*, B) while z_{j−1} was
      complete in I_q, i.e. with
      d[z_{j−1}] = dis_{I_q}(z_{j−1}) = D(z_{j−1}) (S1 D1) ⪯ L_q(z_0 … z_{j−1}) = dis(z_{j−1}), hence
      d[z_{j−1}] = dis(z_{j−1}) (A3 in I). Then cand = dis(z_{j−1}) ⊕ e* = dis(z_j) (A1) ⪯ d_0[z_j] = d[z_j]
      and cand ≺ B, so RX.3 passes and RX.4–5 record a hit — contradicting hitlist = ∅. Here
      d[z_j] = d_0[z_j] because sink labels are frozen from q's FB.5 until the end of q's run: Z does not change
      during the search (FB.14/FB.17 run only after FB.6) and suppressed relaxations change nothing.
By (i) and (ii) the walk z_0 … z_r is admissible for I_q; so v ∈ R_q ∪ {q} = U_q (I-3) and
d[v] = D(v) ⪯ L_q(z_0 … z_r) = dis(v) ⪯ d[v], i.e. v is complete in I. As W_q = U_q (FB.19), v ∈ W and v is
complete. ∎

### S3.2.4 FP2–FP6

FP2. As in §S3.1.3: Q = roots of searches ending at FB.18–19; every x ∈ S \ Q lies in a tree (skipped at
FB.4, or x ∈ N added at FB.13/FB.16); MP.6 makes the P_j disjoint, nonempty, with ⋃ P_j ∪ Q = S. As in
§S3.1.3 (agent-06 c4), a failed root that a later search puts into a tree stays in Q.
FP3. For x ∈ Q, W_x := U_x ∋ x with |U_x| < k (FB.18). W ⊆ N-sets ⊆ Ũ (§S3.2.1).
FP4. Pre-partition trees are built only at FB.13 and FB.16, from N:
 - N ∩ (existing trees) = N ∩ Z = ∅ (suppression; x ∉ Z by FB.4), so trees stay vertex-disjoint.
 - FB.16 (new tree): |N| ≥ |U_x| ≥ k, since either |U_x| ≥ k or B'_x ≺ B and then |U_x| > k (I-2). The
   edge set is the tree of §S3.2.2.
 - FB.13 (merge): the hit (u, e) has u ∈ N (SP: u relaxed in the run) and z = head(e) ∈ V(T). The union of
   the tree (N, tpar0) and T, joined by the single edge e, is a tree (N ∩ V(T) = ∅). Trees only grow.
 - All tree vertices lie in S ∪ touched ⊆ Ũ; all tree edges are edges of H.
 - Partition, P_j ⊆ V(F_j), sizes, edge-disjointness and the bounds on p: exactly as in §S3.1.3. With N-trees,
   Σ_T|V(T)| = Σ|N| may exceed Σ|U_x|, but the trees are still vertex-disjoint subsets of Ũ, so
   p ≤ |Ũ|/(k − 1) (used for full executions, where Ũ = U), and p ≤ |S| (used for partial ones).
FP5. Every Relax in FindPivots-B is executed inside an inner run, from x ∈ S or from a vertex touched
earlier in that run (SP of the inner run); suppressed relaxations change no label. L3+ (host) applies.
FP6. Inner runs use private D structures, destroyed at FB.7; no inner key is ever inserted into a host D.

### S3.2.5 FP7 (time)

Let c_in(U_x) denote the cost of the inner run FB.6 (S4 (I1)–(I3): O(g (|U_x| + 1)) with
g = Θ(sqrt(log k log log k)) for constant δ, and |U_x| ≤ 8k by the top cap τ = k and the choice of l_in).
Bookkeeping per search (FB.5, FB.7–FB.19, TH) is O(|N| + 1), and |N| ≤ O(c_in(U_x)) (every touch is a
valid relaxation, counted in the inner cost). MP/PT cost O(Σ_T|V(T)| + |S|) with Σ_T |V(T)| = Σ |N| over
tree/merge searches.
- Failed searches: O(g k) each, O(g k |Q|) in total.
- Tree/merge searches: |U_x| ≤ |N| and the N are disjoint new tree vertices, so Σ |U_x| ≤ |Ũ|;
  also Σ |U_x| ≤ 8k |S|. Their inner-run cost is O(g · min(|Ũ|, 8k|S|) + g|S|).
- Bookkeeping (FB.10, FB.13, FB.16, TH, MP, PT): O(Σ |N| + |S|) where the sum is over tree/merge searches.
  Here Σ|N| = Σ_T |V(T)| ≤ |Ũ| (disjoint subsets of Ũ), and |N| ≤ O(cost of the inner run) = O(g |U_x| + g)
  = O(g k) per search, so Σ|N| ≤ min(|Ũ|, O(g k)|S|). (|N| can exceed |U_x|: touched-but-unsettled vertices
  of the inner run also become tree vertices.)
**FP7(B):** FindPivots-B costs O(g · min(|Ũ|, 8k|S|) + min(|Ũ|, g k |S|) + g |S| + g k |Q|).
With the S4 coupling k g ≤ 2C_g t and (B2) |S| < 4|U|/t for partial calls, every term is O(g|U| + t|Q|) for
partial X; for full X, Ũ = U and the bound is O(g|U| + g k |Q|) = O(g|U| + t|Q|) (S4 (3.4) unchanged).

---------------------------------------------------------------------------------------------------

## S3.3 Degenerate cases (explicitly)

- S = {x} with no admissible edge: the inner run returns U_x = {x}, full, no hit: x ∈ Q, W_x = {x}.
- x ∈ S was touched (its label lowered) by an EARLIER search of the same FindPivots-B call but is not in any
  tree (that search failed): x's own search runs normally on I_x with its CURRENT label as λ_x; D1–D3 need
  nothing else, since the caps of I_x are the labels at x's FB.5.
- k larger than the reachable region: every search fails; p = 0; BM.8 sets B'_0 = B; the core loop is empty.
- Zero-weight edges/cycles, ties, parallel edges: handled entirely by the label order (S1 A); nothing in
  FD/FB compares weights except through Relax and the heap/BST keys.
- Vertices unreachable from s are never touched (their labels stay ∞; S2 Cor. S2.2).

---------------------------------------------------------------------------------------------------

## S3.4 Variant: sink ("relax-into") semantics

If instead relaxations INTO sinks are performed and only sink OUT-edges are skipped (Out(u) = ∅ for
u ∈ Z), then: G_x keeps sinks as vertices without out-edges and admissible walks may end at a sink
(S1 §C variant (S)); N may contain sinks; a merge is triggered by N ∩ Z ≠ ∅; the merged tree is
(N \ Z, tpar0) plus, for each touched tree, one tpar0-edge into it (sinks are leaves of the tpar0 tree
because they never relax anything). FP1 is proved as in §S3.2.3 with (ii) replaced by: the first sink
z_j on the path is admissibly reachable, hence in U_q ⊆ N (full run), i.e. touched — contradicting
N ∩ Z = ∅. FP7 needs |U_x ∩ Z| ≤ δ (|U_x \ Z| + 1): each sink in U_x has its I_x-canonical predecessor in
U_x \ Z (U_x is closed under canonical predecessors, and sinks have no out-edges), and each non-sink has
≤ δ out-edges — charged per search (agent-09 S4 review R2). The general-m range then shrinks
(agent-05 S4 v3); the sparse bound is unchanged. agent-08's prototype implements both variants
(wall_mode='suppress' | 'sink'); both pass all checks.

## S3.5 Nesting (iterated bootstrapping)

**Theorem S3.6 (FP for FindPivots-B on a general admissible host).** Let I be ANY admissible instance
(S1 (I0)) on which a call X = BMSSP(B, S, l) satisfies (C1)–(C3), and let FindPivots-B run inside X with
inner algorithm A_in (a BMSSP whose FindPivots satisfies FP on every admissible instance). Then
FindPivots-B satisfies FP1–FP6, and FP7 with g the per-vertex cost of A_in's capped runs.
*Proof.* §S3.2 uses about the host only: admissibility (for S1 D1–D3, which S1 proves for an arbitrary
admissible host H, cf. S1 R5), SP of the host run, L3+ in the host, and Lemma S2.1/S2.4 for A_in on the
deadline instances I_x (admissible by D1). It never uses that I = I_0. ∎
Consequently depth-D bootstrapping is correct by induction on D: depth 1 = FindPivots-D (§S3.1, any
admissible instance); if A_D satisfies FP on every admissible instance (with Lemma S2.1 giving correctness of
A_D's BMSSP), then Theorem S3.6 gives FP for FindPivots-B with A_in = A_D, on every admissible host.

The proofs of §S3.2 use only that the host instance is admissible and satisfies SP; they apply verbatim
when FindPivots-B is run inside an inner instance (host = G_{x_1}, inner = G_{x_2} ⊆ G_{x_1}), with one
set of depth-d arrays per depth (S1 R5; pseudocode Sec. 6 last note).


## Appendix E — S4 Time and space (agent-05), final text

Frozen label `S4final`, source `/research/agents/agent-05/work/S4_final.md`, sha256 `824309056a8116b1e7e0e6bbcb17f8203fccd2e0556aa597168cca78e5f3859d`, frozen 2026-09-20T07:51:13Z.

# S4 — Running time and space of bootstrapped DMSY26 (drop-in for MASTER_B1 §8)

Author: agent-05. This is the clean text distilled from `cost_analysis.md` v5, which keeps the full
derivation history, the review log (§12) and the discharge table (§13). Reviews of the underlying
v3/v4/v5: agent-09 (formal #1), agent-06 (formal #2) and agent-03 (third) found it CORRECT,
conditional on the "Assumes" list below. All their items are incorporated.

Algorithm text: agents/agent-04/work/pseudocode.md v2.1. Lines BM.x, BC.x, FB.x, FD.x, MP.x, RX.x
and SS.x refer to it. Semantics: SUPPRESSION (final ruling). Logs are base 2 and lg x := max(1, log2 x).

---------------------------------------------------------------------------------------------------

## Assumes

- **A-S2** (S2 = agents/agent-08/work/S2_core.md). Lemma S2.1 (R1)-(R9) for every call on every
  admissible instance, with its preconditions (C1)-(C3) verified for the top calls (Cor. S2.2,
  Cor. S2.3) and for the sub-calls (S2 Step 2). Also Lemma S2.4 (scan lemma). Every iteration has
  U_i ≠ ∅ (S2 Step 5).
- **A-S3** (S3 = agents/agent-08/work/S3_findpivots.md). FindPivots-D and FindPivots-B satisfy FP1-FP7.
  In particular, for one FindPivots-B search from x:
  - U_x ∋ x; partial implies |U_x| > k; full implies U_x = R_x ∪ {x};
  - the touched set N_x satisfies U_x ⊆ N_x ⊆ Ũ(B,S) and N_x ∩ Z = ∅;
  - trees are vertex-disjoint, have >= k vertices, lie inside Ũ(B,S), and use edges of H;
  - failed searches have |W_x| < k;
  - FP2 (partition of S) and FP4 (P_j ⊆ V(F_j), |V(F_j)| < 3k, p <= |S|, p <= |Ũ|/(k-1)) hold.
  S3 §S3.5 extends this to FindPivots-B inside deadline instances; only the depth-3 remark needs it.
- **A-S1** (S1 = agents/agent-02/work/L1_foundations.md). D1-D3: the inner run is the core run on
  I_x. SP/SP': every relaxation and read is from x or a touched vertex. L3+. Labels are O(1)-size
  version-stamped tuples, compared with one real comparison.
- **A-S5** (S5 = agents/agent-04/work/S5_data_structure.md). Lemma DS: D over stored values with
  Insert O(log(N/M)) amortized, Pull O(|S'|), Merge O(|D'|), Delete O(1) amortized, valid when
  log(N/M) = O(M). Lemma MS: O(1) lookups via per-vertex membership stacks. Base-case BST with
  O(log size) operations.

## Provides

- **Theorem S4-T (time).** Let δ be the max degree after degree reduction, N the number of reduced
  vertices, and let the parameters satisfy (P1)-(P4) of §S4.1. Then SSSP runs in
  O(n + m + m t + N (log N / t)(g + δ) + N δ log t) time, where g bounds the per-vertex cost of the
  capped inner searches (§S4.3).
- **Corollary S4-S (sparse).** With pseudocode §8.2 parameters, δ = 3 and N >= n_0 (an absolute
  constant): O(n + m (log n)^{1/2} (log log n · log log log n)^{1/4}).
- **Corollary S4-G (general m, hybrid).** Choosing the better variant from m/n gives
  O(n + m sqrt(log n) + min{ sqrt(m n log n LL), m sqrt(log n) LL^{1/4} (1 + LLL n/m)^{1/4} }).
  This is strictly better than DMSY26 iff m/n = o(sqrt(log log n)).
- **Theorem S4-M (space).** O(n + m) words.
- **Lemma G2** (insertion-event uniqueness), **Lemma G4** (Q-appearances), **Lemma I** (inner cost).

---------------------------------------------------------------------------------------------------

## S4.1 Parameters and size bookkeeping

A parameter record is P = (t, k), with, for l >= 1, M_l = t 2^{(l-1)t} (Pull size) and
Λ_l = t^3 2^{lt} (loop threshold), and Λ_0 = t^3 (base threshold). The constraints are:
- (P1) t >= 2, 2 <= k, 3k <= t. This is pseudocode FIX-L13.
- (P2) inner record P' = (t', k') with 3k' <= t', and l* := min{ l >= 1 : Λ'_l >= k } for the inner top call.
- (P3) k >= t', and Λ'_{l*-1} <= k. The latter is the minimality of l* when l* >= 2, and means
  t'^3 <= k when l* = 1.
- (P4) k c(k) <= C_g t and t/k <= C_g g, where c(k) is the inner per-vertex cost of Lemma I.

**(B1) Frontier size.** A level-(l-1) child gets S_i = Pull() (at most M_l keys) plus, for each pulled
key that is a current pivot, fewer than 3k further vertices (BM.12, FP4). So
|S_i| <= 3k M_l <= t^2 2^{(l-1)t} =: σ_{l-1}. Stale pivot keys expand nothing (BM.12 tests piv[j] = x).

**(B2) Partial implies |U| > t|S|.** A partial level-l call has |U| > Λ_l = t σ_l >= t|S| (S2 R4). A
partial base call has |U| = Λ_0 = t^3 >= t|S|.

**(B3) Output size.** U is the disjoint union of U_1, …, U_f and W' (S2 R8). The loop exits once
|U| > Λ_l, so the last child overshoots by at most Ubar_{l-1}. Also |W'| <= |W| < k|Q| <= k σ_l <= Λ_l/3
by FP3 and (P1). Hence Ubar_l <= (4/3) Λ_l + Ubar_{l-1} <= 2 Λ_l for t >= 2, with Ubar_0 = Λ_0.

**(B4) Data-structure cost.** Keys inserted into D_X are S-vertices (BM.7, BM.23, BM.25), heads of
out-edges of U (BM.21, BM.28), and merged keys of children, which are of the same kinds. So
N_X <= |S| + δ|U| = O(δ t^3 2^{lt}), N_X/M_l = O(δ t^2 2^t), and log(N_X/M_l) = t + O(log t) = O(M_l) for
δ <= t. Lemma DS then gives: **Insert O(t) amortized, Pull and Merge linear, Delete O(1) amortized.**
Merge's precondition M_{l-1} < M_l/3 holds for t >= 2. The base-case BST holds O(δ t^3) items, so each
operation costs O(log t).

**(B5) Depth.** The root call BMSSP(∞, {x_s}, L) (SS.9) uses L := min{ l : Λ_l >= N } <= ceil(lg N / t).
By S2 Cor. S2.2 it is a full execution.

## S4.2 One insertion event per edge; Q-appearances

An *insertion event* is a Relax(u, e, ·) returning True that is followed by D.Insert(head(e)). Such
events happen only at BM.20-21, BM.27-28 and BC.7.

**Lemma G2.** On any admissible instance, every edge e = (u, v) has at most one insertion event.

*Proof.* u relaxes at those lines only as a member of the U of the executing call:
- u ∈ U_i of a child at BM.19;
- u ∈ W' at BM.27;
- u extracted at BC.6.

By (R8) the calls whose U contains u form a chain X_0 ⊃ … ⊃ X_q, one call per layer. At each such
event u is complete (child's R1; S2 Step 5; BC K4), so c := d[u] ⊕ e is the same at all of them. The
possible events:
- BM.20 in X_j (j < q) needs c ∈ [B_{X_{j+1}}, B_{X_j}).
- BM.28 needs c ∈ [B'_{X_q}, B_{X_q}), and occurs only at X_q (u ∈ W'_{X_q} means u is in no child's U).
- BC.7 needs c ≺ B_{X_q}, and occurs only at a base call X_q.
These intervals are pairwise disjoint because B_{X_q} ⪯ B_{X_{q-1}} ⪯ … ⪯ B_{X_0}. The argument uses
only the interval test, so it holds for re-confirmations (RX.7) as well. Relaxations inside inner runs
belong to the inner instance and insert only into its private D's (S3 FP6, S2 R9). ∎

**Lemma G4 (Q-appearances).** Summed over all outer calls X, sum |Q_X| <= N(δ+1) + N L/t. For every
vertex v, the number of FULL calls X with v ∈ Q_X is at most indeg(v) + [v = x_s].

*Proof.*
- **Partial calls.** |Q_X| <= |S_X| < |U_X|/t by (B2). The U_X of one layer are disjoint, so summing
  over the L+1 layers gives at most N L/t.
- **Full calls.** Let Y_1 ⊋ Y_2 ⊋ … be the full calls with v ∈ Q_{Y_a}. Since v ∈ S_{Y_a} ⊆ U_{Y_a},
  and the U's of one layer are disjoint, these calls form an ancestor chain.
- After FindPivots-B of Y_a, v is in no P_j of Y_a and not in D_{Y_a}, which starts with pivots only.
  To reach S_{Y_{a+1}}, v must enter some D inside T(Y_a).
- BM.7, BM.23, BM.25 and the picking at BM.12 all need v ∈ S of a later call in T(Y_a); that is
  circular. Merges move entries made in children, and deletions are not insertions. So the first
  entry is an insertion event on an in-edge of v inside T(Y_a).
- The event that brought v into S_{Y_a} happened before Y_a started. So distinct appearances use
  distinct in-edge events, and Lemma G2 bounds the chain length by indeg(v) + [v = x_s]. ∎

## S4.3 Cost of one inner search (Lemma I)

The inner run FB.6 is BMSSP(B, {x}, l*, P', τ = k) on I_x (S1 D2, S2 Cor. S2.3). It returns U_x.

**(I1)** |U_x| <= k + Ubar'_{l*-1} + |W'_top| <= k + 2k + k' <= 4k. Here Λ'_{l*-1} <= k by (P3), and
|W'_top| < k' because the top call has |S| = 1. With x ∈ U_x: **1 <= |U_x| <= 4k**.

**(I2)** At the top call, partial implies |U_x| > k >= t' = t'|S|. The top D has at most 1 + 4δk keys and
M' = t' 2^{(l*-1)t'} >= k/(t'^2 2^{t'}), so the insertion cost is t' + O(log t'). Every lower call is a
standard call, so (B1)-(B5) hold for it with primes.

**Lemma I (inner cost).** cost(FB.5-FB.19 for root x) <= C_in c(k) |U_x|, where
c(k) := l* (lg t' + δ) + δ t' + δ lg t'. With δ = 3 and t' := ceil(sqrt(lg k · lg lg k)):
**c(k) = O( sqrt( log k · log log k ) )**.

*Proof.* Global summation inside I_x (S2 Lemma S2.1 applied in I_x):
- (a) The inner U_Y of one layer are disjoint subsets of U_x, so sum_Y |U_Y| <= (l*+1)|U_x|. Every
  call has U_Y ≠ ∅, so #calls <= (l*+1)|U_x|. Pulls on nonempty D return nonempty sets (deletion form
  of FIX-STALE).
- (b) Inner insertion events are out-edges of inner-settled vertices, all of which lie in U_x, so
  there are at most δ|U_x| of them (G2 in I_x), each O(t').
  - Vertices lowered by inner FindPivots-D or 2-hop relaxations in partial inner calls are not settled.
    Their cost is inside (e).
- (c) Cross-edge re-selections number at most |E(U_x)| <= δ|U_x|, each O(t').
- (d) Inner Q-appearances number at most |U_x|(δ + 1 + l*/t') (G4 in I_x; x is never re-inserted),
  each costing O(k'(δ + lg k')) = O(t') by FP7(D), given k' <= t'/(3(δ + lg t')). For δ = 3 this is the pseudocode's k' = floor(t'/(3 lg t')) up to constants.
- (e) Direct per-vertex per-layer work is O(lg t' + δ):
  - FindPivots-D costs O((sum_T |V(T)| + |S| + k'|Q|)(δ + lg k')) with sum_T |V(T)| <= min(|Ũ_Y|, (k'+δ)|S_Y|),
    which is O(|U_Y|) also for partial Y by (B2);
  - pivot inserts O(t'/k') = O(lg t'); picking, scans, Pull/Merge/Delete O(1 + δ).
  - Base calls cost O(δ lg t') per vertex.
- (f) Bookkeeping: touch hook and Tlist O(|N_x|); hit list O(#Relax); tree-edge copy (FB.10) and
  merge O(|N_x|). Here |N_x| <= 1 + #valid Relax = O(inner work).
Summing: O(|U_x| (l*(lg t' + δ) + δ t' + δ lg t')). With l* <= ceil(lg k / t') and the stated t',
this is O((lg k/t') lg t' + t') = O(sqrt(lg k · lg lg k)). ∎

## S4.4 Cost of FindPivots-B at an outer call X

Split the searches of FB.3-FB.19 by outcome:
- **Tree/merge searches.** Their N_x are pairwise disjoint new tree vertices (suppression gives
  N_x ∩ Z = ∅; FB.4 skips tree roots). So sum |U_x| <= sum |N_x| <= |∪F̄| <= |Ũ(B,S)| (FP4), and also
  sum |U_x| <= 4k|S| by (I1).
- **Failed searches.** |U_x| < k, and there are |Q_X| of them.
- MakePivots and Partition (PT) cost O(|S| + sum |N_x|) = O(|S| + inner work).

Hence

    cost(FindPivots-B at X) <= C ( c(k) min(|Ũ(B,S)|, 4k|S|) + c(k) k |Q_X| + |S| ).        (S4.1)

- Full X (Ũ = U_X ⊇ S): at most C (c+1) |U_X| + C c k |Q_X|.
- Partial X (|S| < |U_X|/t): at most C (4kc/t + 1)|U_X| + C c k |Q_X|.
By (P4), in both cases: **O(g |U_X| + t |Q_X|)** with g := C_g c(k).

**Pivots.** Trees have >= k vertices and PT pieces have >= k-1 edges. MP.8 drops empty groups, so
p <= min(|S|, |∪F̄|/(k-1)). Hence p t <= 2(t/k)|U_X| = O(g|U_X|) for full X, and p t <= t|S| < |U_X| for
partial X.

## S4.5 Direct cost of one outer call (children excluded)

With T-numbers as in DMSY26 Lemma 3.9:
- **T1** FindPivots-B (BM.4), P-membership (BM.6), pivot inserts (BM.7): O(g|U| + t|Q_X|).
- **T2** Picking (BM.11-BM.12) costs O(|Pl[j]|) = O(k) per pulled current pivot.
  - Partial child: O(k|S_i|) <= O(k|U_i|/t) <= O(|U_i|).
  - Full child: the pivot enters U_i and triggers a BM.23 re-selection of cost Omega(t) >= Omega(k),
    which absorbs the picking. The exception, Pl[j] becoming empty, happens once per j: O(kp) = O(|U|).
- **T3** Pull (BM.10) costs O(|S_i|) = O(|U_i|): S_i ⊆ U_i if the child is full, |S_i| < |U_i|/t if
  partial. An unsettled pulled key that returns through the child's BM.25 and the Merge is re-inserted
  at the child's expense (T6 of the child) and re-pulled at this cost. Also counted here: Merge
  (BM.14), deletions (BM.15, BM.29), membership updates (BM.16-BM.18, BM.30), edge scans (BM.19,
  BM.27), BM.24a. Total O(δ|U|).
- **T4, T7** BM.21 and BM.28 inserts: O(t) per insertion event.
- **T5** Re-selection (BM.23) costs O(|Pl[j]| + t) = O(t).
  - Partial X: at most |S| re-selections, O(t|S|) = O(|U|).
  - Full X: O(pt + t|E_X|), where E_X := E(U_X) minus the union of the E(U_i). The former pivots of
    group j lie in g_j distinct U_i's, and F_j minus E_X has >= g_j components, so F_j has >= g_j - 1
    edges in E_X. This needs F_j ⊆ U_X, which holds since F_j ⊆ Ũ = U_X for full X (FP4). Merge edges
    end in earlier trees, which are ⊆ Ũ. The F_j are edge-disjoint.
- **T6** BM.25 costs O(t|S|), non-zero only for partial X, so O(|U|).
- **Overhead** O(1) per call, which is <= O(|U|) since U ≠ ∅.

So direct(X) <= C'' ((g + δ)|U_X| + t|Q_X| + t|E_X| + t·#events(X)). A base call costs O(δ|U| lg t) (B4).

## S4.6 Global summation (proof of Theorem S4-T)

Global facts:
- (G1) Per layer, sum |U_X| <= N (S2 R8, by induction down the call tree), and there are L+1 layers.
- (G2) sum over X of #events(X) <= m (Lemma G2).
- (G3) sum over X of |E_X| <= m. An edge is in E_X only at the call where its two endpoints first fall
  into different children (or into W').
- (G4) Lemma G4.
- (G5) The base calls' U's are disjoint.

Therefore:

    T_main <= C'' [ (g + δ)(L+1) N + t(N(δ+1) + N L/t) + t m + t m ] + O(δ N lg t)
           = O( m t + N (lg N/t)(g + δ) + N δ lg t ),

using δN = O(m). Adding preprocessing and output (S4.8), O(n + m), proves Theorem S4-T. ∎

## S4.7 Parameters, the sparse bound, and the constant n_0

These are pseudocode §8.2:
- t := ceil( lg(N)^{1/2} lg(lg N)^{1/4} lg(lg lg N)^{1/4} ), G(t) := ceil( sqrt(lg t · lg lg t) ),
  k := floor( t/(3G(t)) );
- t' := ceil( sqrt(lg k · lg lg k) ), k' := floor( t'/(3 lg t') ).

Then c(k) = O(G(k)) = O(G(t)) by Lemma I and monotonicity, so (P4) holds with g = Θ(G(t)). Since
lg t = (1/2 + o(1)) lg lg N, we have g = Θ( sqrt(lg lg N · lg lg lg N) ), and (lg N/t)·g = Θ(t).
Theorem S4-T with δ = 3 and N = O(m) gives

    O( n + m (log n)^{1/2} (log log n · log log log n)^{1/4} ),

which is o(m sqrt(log n log log n)) by a factor Θ((log log n / log log log n)^{1/4}).

**Feasibility.** (P1)-(P3) hold for all N >= n_0, where n_0 is an absolute constant: t'^3 2^{t'} = k^{o(1)}
and k -> ∞. Below n_0, SS.7 runs binary-heap Dijkstra in O(1) time.
- With the literal formulas, (P1)-(P3) in the relaxed form (t'^3 <= k when l* = 1) first hold around
  lg N ≈ 10^6. The strict form Λ'_1 < k first holds around lg N ≈ 10^13.
- **The improvement is purely asymptotic.** For example, at n = 2^64 the two leading factors, ignoring
  constants, are 15.9 vs 19.6. Correctness does not depend on the parameters.

## S4.8 Preprocessing, output, unreachable vertices

- SS.2-SS.4 (reachability by BFS; unreachable vertices get dist = ∞ and pred = ⊥; self-loops are
  dropped) cost O(n + m).
- SS.5 (degree reduction to max in-degree and out-degree 2, total degree 3; N <= 2m_R + n_R) costs O(n + m).
- SS.10-SS.12 (map back: dist(v) = the len of any gadget vertex; pred(v) via the minimum-hop gadget
  vertex e_v; acyclic because hops strictly decrease; each pred edge is tight) cost O(n + m) (S5).
- Integers (ids, hops, versions, stamps) are O(log n)-bit words. Every version increment is one Relax,
  so versions are at most poly(n + m).

## S4.9 General m (Corollary S4-G)

Degree reduction to δ = Θ(min(m/n, log log n)) gives N = O(m/δ), and Theorem S4-T becomes
T = O(m sqrt( log n (1 + f/δ) )), where f is the local-search cost per vertex:
- **Dijkstra (FindPivots-D at the outer level):** f/δ = 1 + lg k/δ. This is DMSY26.
- **Bootstrap:** f = c(k) = min over t' of [ (lg k/t')(lg t' + δ) + δ t' ] = Θ( sqrt( δ lg k (δ + lg lg k) ) ),
  so f/δ = Θ( sqrt( lg k (1 + lg lg k/δ) ) ).
  - The inner layers pay δ per vertex, because inner FindPivots-D and Line 23 scan all out-edges.
    This is the correction to earlier drafts.
  - For general δ choose the inner group size k' := floor(t'/(3(δ + lg t'))). Then each failed inner
    search costs O(t'), and the inner pivot cost t'/k' = O(δ + lg t') per vertex per layer.

Taking the better of the two gives Corollary S4-G. Bootstrapping wins exactly when δ = o(sqrt(log log n)).

## S4.10 Space (Theorem S4-M)

- Global: the graph, d[·], ver[·], per-depth stamp arrays, O(n + m).
- The live outer calls form one root-to-current path. The call at layer l stores
  O(|S_X| + δ|U_X| + |∪F̄| + |W|) = O(δ min(N, Λ_l)) words, and summing over the path gives
  O(δ(N + sum_{l<L} 2Λ_l)) = O(δN) = O(m), because the Λ_l grow geometrically and Λ_{L-1} < N.
- At most one inner run is live at a time, using O(δk) words plus its own geometric path, and at most
  one Fibonacci heap (O(k'δ)).
- Membership-stack entries number at most the live D-keys plus P-entries (Lemma MS).
- **Total: O(n + m).**

## S4.11 Remark (not part of the theorem): depth 3

This is cost_analysis.md §7, Lemma M. Use as the inner algorithm the bootstrapped algorithm itself
(A_2), with inner-inner FindPivots-D. The per-vertex cost of a capped A_2 search of size K is
c_2(K) = O((log K)^{1/2}(log log K · log log log K)^{1/4}). With t_0 = sqrt(log n · c_2(t_0)) the bound
becomes

    O( m (log n)^{1/2} (log log n)^{1/4} (log log log n)^{1/8} (log^{(4)} n)^{1/8} ),

which is below Kadria-Roditty's undirected randomized bound. It additionally requires S3 §S3.5 to be
confirmed by the formal reviewers, and a larger threshold n_0^{(3)}.

## S4.12 Where each assumption is proved

| used here | proved in |
|---|---|
| U = Ũ(B',S), disjoint U_i, U ≠ ∅, partial implies \|U\| > τ | S2 Lemma S2.1 (R1), (R4), (R8); Step 5 |
| inner run = core on I_x; x ∈ U_x; full implies U_x = R_x ∪ {x} | S1 D1-D3; S2 Cor. S2.3; S3 (I-1)-(I-3) |
| trees disjoint, >= k vertices, inside Ũ, edges of H; FP2, FP4 | S3 §S3.2.4 |
| failed searches exact, \|W_x\| < k | S3 §S3.2.3, FP3 |
| inner runs never touch outer D's | S2 (R9), S3 FP6 |
| D-operation costs, membership stacks, map-back | S5 Lemma DS, Lemma MS, pseudocode §8.3 |
| one insertion event per edge | Lemma G2 (this section) |
| Q-appearance bound | Lemma G4 (this section) |

Empirical sanity checks, finite and not proofs: agents/agent-05/work/s4check/ (I1, G4, pivot count,
partial size, per-layer disjointness): 0 violations in 1200 trials, the G4 ratio is exactly 1.00, and the
maximum |U_x|/k is 4.00, which attains the bound in (I1).


## Appendix E3 — Cor. S4-GM: dispatcher time bound (agent-05)

Frozen label `S4GMadd`, source `/research/agents/agent-05/work/S4_addendum_GM.md`, sha256 `057bf03e78a7dd457160621e6e41e6e927884961b92e234b683e088c63a4ab8b`, frozen 2026-09-20T07:57:10Z.

# S4 addendum GM-time (agent-05): running time of the dispatcher (option A)

This supports the must-fix M1 (agent-09) / A1 (agent-06) of the integrated-master reviews, together
with agent-04's pseudocode addendum GM (pseudocode_addendum_GM.md). It adds no new correctness claim:
- both branches run the corrected core (S2) with a FindPivots routine that satisfies FP on every
  admissible instance (S3 §3.1 for FindPivots-D, S3 §3.2/Thm S3.6 for FindPivots-B);
- both branches use degree reduction and map-back through zero-weight gadget cycles (S5 / pseudocode §8.1, §8.3).

## Statement

**Corollary S4-GM.** Use the dispatcher. If m_R <= n_R · sqrt(LL/LLL) (LL = lg lg n, LLL = lg lg lg n;
integer arithmetic on bit lengths), run PCv2.3 as frozen: BOOT, δ = 3. Otherwise run the corrected
plain DMSY26 (PLAIN) with FindPivots-D at the top level. The running time is

    T(n, m) = O( n + min{ m sqrt(log n) (LL · LLL)^{1/4},  m sqrt(log n) + sqrt(m n log n · LL) } ),

with space O(n + m).
- T is never worse than DMSY26's O(n + m sqrt(log n) + sqrt(mn log n LL)).
- T is strictly better, by an omega(1) factor, iff m/n = o( sqrt(LL/LLL) ). This includes every m = O(n).

(Here log n assumes m <= poly(n); see the remark on multigraphs below.)

## Proof (from Theorem S4-T of S4_final.md)

Theorem S4-T: T = O(n + m + m t + N (lg N / t)(g + δ) + N δ lg t) for any parameters satisfying (P1)-(P4),
where g bounds the per-vertex local-search cost and failed searches cost O(t) each (k·g <= C t).

**BOOT branch** (frozen PCv2.3, δ = 3, for ANY m).
- Degree reduction gives N <= n_R + 2 m_R = O(m + n), and lg N = O(log n) under m <= poly(n).
- S4_final §S4.7 applies verbatim. It never used m = O(n), only N = O(m + n) and δ = 3.
- So T_BOOT = O(n + m sqrt(log n)(LL · LLL)^{1/4}).

**PLAIN branch** (m_R > n_R sqrt(LL/LLL)).
- Degree reduction to δ := max(3, floor(min(m_R/n_R, LL)/4)) via gadget cycles of ceil(Δ_v/(δ-2))
  vertices, each hosting <= δ-2 external edges. This gives max degree <= δ and N = O(m/δ).
  Agent-06 notes the map-back works unchanged, because gadgets are zero-weight cycles.
- Local search is FindPivots-D (FP7(D)):
  - per explored vertex O(δ + lg k), and O(k(δ + lg k)) per failed search;
  - take k := max(2, floor(t/(3 lg t))), so 3k <= t and k(δ + lg k) = O(t) whenever δ <= lg k;
  - δ <= LL/4 <= lg k holds for large n, since lg k = (1/2 - o(1)) LL at t = Theta(sqrt(log n LL/δ)).
- So g = O(δ + lg t) = O(lg t), and the pivot term t/k = O(lg t).
- S4-T with N = O(m/δ) gives T = O(m t + (m/δ)(lg n/t) lg t + m lg t).
- With t := ceil( sqrt( lg N · lg lg N / δ ) ) this is O(m sqrt(log n · LL/δ) + m LL).
  - If δ = Theta(m/n) (i.e. m/n <= LL): O(sqrt(m n log n LL)).
  - If m/n > LL, δ = LL/4: O(m sqrt(log n)).
  - Hence T_PLAIN = O(m sqrt(log n) + sqrt(mn log n LL)), which is DMSY26's bound, now for the
    corrected algorithm.
- The inner-cost constraints of S4 (I1)-(I2) are not needed here, because PLAIN has no inner search.
  The size bookkeeping (B1)-(B5), Lemma G2 and Lemma G4 hold for every instance and every δ.

**Dispatcher cost.** Computing n_R, m_R, LL and LLL costs O(1) after the BFS.
- BOOT runs only when m_R <= n_R sqrt(LL/LLL). There T_BOOT = O(m sqrt(log n)(LL LLL)^{1/4}), and
  this is <= O(T_PLAIN): m <= n sqrt(LL/LLL) implies (LL LLL)^{1/4} <= sqrt(LL n/m).
- PLAIN runs otherwise. There m/n > sqrt(LL/LLL) implies T_PLAIN <= O(T_BOOT).
- So the dispatched time is O(min(T_BOOT, T_PLAIN)) up to constants.

**Strictness.**
- T_BOOT/T_PLAIN = (LL LLL)^{1/4} / (1 + sqrt(LL n/m)), which tends to 0 iff m/n = o(sqrt(LL/LLL)).
- For m = O(n) the ratio is Theta((LLL/LL)^{1/4}), which tends to 0.

**Space.** Both branches are O(n + m) (S4_final §S4.10; the plain branch is the same code with
FindPivots-D). ∎

## Remark: multigraphs and "log n"

With parallel edges m can exceed n^2, and then lg N = lg(n + 2m) is not O(log n). In that case:
- either state the bound with log(n + m);
- or add the O(m) preprocessing step "keep one minimum-weight edge per ordered pair (u, v)". It buckets
  by integer ids and uses one weight comparison per edge, so it is legal in the model. Ties are broken
  by edge id.
- After that step m <= n(n-1), and every bound above holds with log n.
- Correctness is unaffected, since a non-minimal parallel edge is never on a canonical path (S1 §A,
  edge-id order).
- For the goal-relevant sparse statement (m = O(n)) nothing changes.

## Relation to the earlier S4 §S4.9 formula

The refined branch m sqrt(log n) LL^{1/4}(1 + LLL n/m)^{1/4} (general-δ bootstrap, suppression) is
correct as a time analysis. However, it needs a general-δ bootstrap text (inner k' := floor(t'/(3(δ + lg t'))))
that is not in PCv2.3. Option A does not need it, at the cost of the slightly narrower strict range
o(sqrt(LL/LLL)) instead of o(sqrt(LL)). I recommend option A for the theorem, and moving the
refined formula to a non-claimed remark.


## Appendix F — S5 Data structure D, membership stacks, space, pre/post-processing (agent-04)

Frozen label `S5v1.2`, source `/research/agents/agent-04/work/S5_data_structure.md`, sha256 `440da8a1df740438b474ab4f20045a5064988522470ad164f3c115faf7bf3895`, frozen 2026-09-20T07:48:35Z.

# S5. The partial-order structure D (DMSY26 Lemma 3.4 with Delete) and nested membership

agent-04, v1.2, 2026-09-20 (v1.1: separator representation, map-back proof; v1.2: Merge chunking bug fixed (agent-03), review notes of agent-09 (1-4) and agent-03 (a,b)). Drop-in section for the integrated document. Line references such as BM.10 are to `pseudocode.md`.
**Status: written proof, not yet reviewed.**

## 1. Semantics: stored values, not labels

A structure D holds:
- a bound B (a label or INF);
- a set of **entries** (v, s_v) with pairwise distinct keys v (vertices) and **stored values** s_v, which are labels with s_v.v = v and s_v < B.

Two entries with different keys therefore never have equal stored values, so "the M smallest" is always well defined.

D never reads the global label array. A stored value is the label that was passed to the Insert that created or last lowered the entry.
Labels can decrease later without a new Insert, for example inside a sub-call. Such an entry is **stale**: s_v > d[v].
By A3 (labels only decrease) we always have **d[v] <= s_v**.
Every statement in this section is about stored values. The BMSSP invariants must be phrased with stored values where they talk about D. This is S2's job, and the point of agent-08's gap note.

Notation: `min(D)` is the smallest stored value, or B if D is empty. |D| is the number of entries.

## 2. Lemma DS (block structure, parameter M >= 2)

Let N be an upper bound on the number of entries ever added to D, by Insert or Merge, during its lifetime.
Assume
  (A_M)  lg(3N/M + 3) <= c_0 * M   for an absolute constant c_0.
D supports:

| operation | effect | amortized cost |
|---|---|---|
| Insert(v, lam) | requires lam.v = v and lam < B. If v is absent, add (v, lam). If lam < s_v, set s_v := lam. Otherwise nothing. | O(lg(N/M + 2)) |
| Delete(v) | remove the entry of v if present | O(1) |
| Merge(D') | requires (i) every stored value of D' < every stored value of D, and (ii) D' is a BST (M' = 1) or a block structure with parameter M' < M/3. Performs Insert(v, s'_v) for every entry of D' and destroys D'. | O(\|D'\| + 1) |
| Pull() | If \|D\| <= M: return (all keys, B) and empty D. Else return (S', x): S' = the M keys of smallest stored value, x = min stored value of the rest (so max_{S'} s < x <= every remaining s). Remove S'. | O(\|S'\| + 1) |
| IsEmpty, Size | | O(1) |
| Destroy | remove all entries (pops their membership entries, Sec. 4) | O(\|D\| + #blocks) |

The total time of any operation sequence is bounded by the sum of the amortized costs.
Only comparisons of labels are used on weights, plus integer and pointer operations.

**Correction to DMSY26.** DMSY26 states the requirement as M >= log(N/M). At level l = 1 we have M = t and N = Theta(t^4 2^t), so log(N/M) = t + O(log t) > M.
The requirement is false as written, but every use needs only (A_M), i.e. lg(N/M) = O(M).
- Outer and inner BMSSP levels l >= 1: M = t 2^{(l-1)t} >= t and N <= C t^4 2^{lt} delta.
- So N/M <= C delta t^3 2^t and lg(N/M) <= t + 3 lg t + O(1) <= 5M for t >= 2.
- This holds for the top inner call with cap tau = k too: N <= 1 + delta(k + Lambda(l_in - 1)) and M = t_in 2^{(l_in-1)t_in}, with k <= Lambda(l_in).

### Implementation
- **Blocks.** Each block b has a *separator* sep_b (a label, or -INF) and an unordered doubly linked list of entries.
  - Blocks live in a balanced search tree (red-black tree) ordered by separator, with a pointer to the first block. Each block stores its size.
  - Invariant (SEP): the first block has sep = -INF, separators are strictly increasing, and every entry of block b satisfies sep_b <= s < sep_{next(b)} (or < B for the last block).
  - So block b "owns" the half-open value interval [sep_b, sep_{next(b)}). These intervals partition [-INF, B), and any legal value has exactly one owning block, found by one tree search.
  - Values below the current smallest entry can always be inserted later: they go to the first block. BMSSP needs this, because after a Pull with bound B_i it inserts values in [B'_i, B_i) at BM.14 and BM.23.
- **Entries.** An entry stores (v, s_v, block pointer, list links).
  The key-to-entry lookup is the membership stack of v (Sec. 4), which is O(1).
- **Initialisation.** A single empty block [-INF, B). Cost O(1).

Operations:
1. **Insert(v, lam).**
   - Look up v. If present with s_v <= lam, stop.
   - If present with s_v > lam, unlink the old entry in O(1) and decrement its block's size.
   - Find the block owning lam (the last block with sep <= lam) by a tree search in O(lg #blocks), and append the entry.
   - If the block now has M + 1 entries, **split** it: find its median value mu by linear-time selection [BFPRT], move the entries >= mu to a new block with separator mu, and insert that block into the tree. Both halves have at most ceil((M+1)/2) entries, and (SEP) is preserved.
2. **Delete(v).** Look up v and unlink it in O(1). If its block becomes empty and is not the only block, remove the block from the tree (O(lg #blocks), charged to the block's creation).
   - Its interval is then owned automatically by the previous block.
   - If it was the first block, the new first block gets sep := -INF, which preserves (SEP).
3. **Merge(D').**
   - Traverse D' in increasing value order: blocks of D' in tree order, entries of a block in any order; if D' is a BST (M' = 1), in-order.
   - For each entry (v, s'): if v has an entry in D, then s_v > s' by the precondition; unlink it. It is the record directly below D''s record on v's membership stack (Lemma MS). Append (v, s') to a current chunk.
   - **Close a chunk only at a D'-block boundary** (anywhere, if D' is a BST): after finishing a D'-block, close the current chunk if it has at least ceil(M/3) entries.
     - The entries inside a D'-block are unordered. A chunk closed in the middle of a block would therefore interleave in value with the next chunk and violate (SEP). This was the bug in v1.1, found by agent-03.
     - Closing only at block boundaries (DMSY26 App. A.2 does the same) keeps chunks value-separated, because D'-blocks are.
     - Since D'-blocks have at most M' < M/3 entries, every closed chunk has size in [ceil(M/3), ceil(M/3) + M') ⊂ [M/3, 2M/3 + 1), so no split is needed.
     - Requirement (ii) holds at every use: D_i of BM.14 has parameter M(l-1) = M(l)/2^t < M(l)/3 for t >= 2, or is a BST. The children of the inner top call have M(l_in - 1) = M(l_in)/2^{t_in}. With t = 1 in tests only, the chunking bound is weaker but the implementation still preserves (SEP).
   - Closed chunks c_1 < c_2 < ... < c_r are then consecutive in value order and all lie below every entry of D.
   - Insert each closed chunk as a new block.
     - c_1 gets sep = -INF. Each c_i with i >= 2 gets sep = min(c_i), computed in O(M).
     - The old first block f of D gets sep := min(f) (an O(M) scan, charged to the >= M/3 merged entries) or is removed if empty.
     - Tree insertions cost O(lg #blocks) = O(M) each.
   - The final open chunk, with fewer than ceil(M/3) entries, is appended to c_r if r >= 1, and otherwise to D's first block (sep stays -INF). If that block exceeds M it is split.
   - (SEP) holds because each chunk's entries lie between its separator and the next separator (block-boundary closing).
4. **Pull().**
   - If |D| <= M: collect all entries, return (keys, B), and make D a single empty block.
   - Otherwise remove whole blocks from the front of the tree (O(lg #blocks) each, charged to their creation) until at least M + 1 entries are collected in C, with |C| <= 2M.
   - Select the (M+1)-th smallest stored value x in C by linear-time selection. S' := the M entries of C below x. The rest R := C \ S' has |R| <= M and contains x.
   - Make R a new first block with sep = -INF and insert it into the tree (O(lg #blocks), charged to the Pull). The next block keeps its separator, which is > every value in R because those values came from removed blocks. (SEP) holds.
   - Return (S', x). Every remaining stored value is >= x: those in R by the choice of x, and the others because they were never collected, so they lie above every collected value.

### Proof of the amortized bounds

(a) **Block count.** A block is created by (i) the initial block, (ii) a split, (iii) closing a Merge chunk, or (iv) the R-block of a Pull with |D| > M.
- (ii) A block produced by a split has at most ceil((M+1)/2) entries. It is split again only after at least M/2 further additions. A block from (iii) needs at least 2M/3 additions before it splits.
  - A block from (iv) can split after one addition, but that split is charged to the Pull, which returned M entries.
  - So #(ii) <= 2(#additions)/M + #(iv).
- (iii) #(iii) <= 3(#merged)/M.
- (iv) Each Pull of type (iv) removes M entries, so #(iv) <= N/M.
- Hence #blocks ever created <= 1 + O(N/M), and every tree operation costs O(lg(N/M + 2)).

(b) **Charging.** Each split, chunk closing and R-block creation costs O(M + lg #blocks), which is O(M) by (A_M).
- Splits are charged to the >= M/2 additions (or the Pull) that caused them.
- Chunk closings are charged to their >= M/3 merged entries.
- R-blocks are charged to their Pull's M outputs.
- Each block removal from the tree, by Pull or by Delete of the last entry, happens at most once per block and costs O(lg #blocks) = O(M). It is charged to the block's creation.
- This gives O(1) amortized per addition, merged entry and pulled entry, plus O(lg #blocks) per Insert for the tree search.

(c) **Pull selection.** O(|C|) = O(M) = O(|S'|).

(d) **Pull with |D| <= M.** O(|D| + #blocks) = O(|S'| + #blocks). The block removals are charged as in (b).

(e) **Merge.** O(|D'| + #blocks(D')) for the traversal. The blocks of D' are charged to their own creation inside D', and chunk closings as in (b). So O(|D'| + 1) amortized.

(f) **Delete.** O(1) plus a possible block removal, charged to its creation.
   An Insert that moves an existing entry may leave an EMPTY block in the tree (agent-03 (a)). Delete's "remove if empty" rule is not triggered then. This is harmless: the empty block is removed later by a Pull (or a Delete that finds it empty), and that removal is charged to its creation.
(g) **Each block is removed from the tree at most once** (agent-09 note 1). This is the fact used when a Pull removes many tiny or empty blocks: each removal costs O(lg #blocks) = O(M) by (A_M) and is charged to the block's creation, which happens once.

Note that no lower bound on block sizes is maintained.
DMSY26 normalises sizes to [M/3, M], but the block-count bound (a) makes this unnecessary: tree depth is bounded by the number of blocks ever created, not by the current size.
This is what makes Delete O(1) without joins.

### Correctness of Pull's separation (used by BM.10/BM.13)
After a Pull that returns (S', x) with |D| > M:
- every key of S' has stored value < x;
- every remaining entry has stored value >= x;
- |S'| = M.

After a Pull with |D| <= M, D is empty and x = B.
In both cases **min(D) >= x after the Pull** (stored values), and all pulled stored values are < x <= B.

### Merge precondition in BMSSP (BM.14)
- D_i is created inside sub-call i with bound B_i, so all its stored values are < B_i.
- After BM.10, every stored value in D is >= B_i.
- Between BM.10 and BM.14, D is not modified: the sub-call touches only its own structures and labels.

So the precondition holds on stored values, whatever the current labels are. Duplicate keys, i.e. a key in both D and D_i, are resolved in favour of D_i's smaller stored value, exactly as Insert would do.

## 3. The M = 1 variant (base case, BC.2)

A balanced search tree keyed by stored value. Insert, Delete, FindMin and IsEmpty each cost O(lg N).
Its key lookup also uses the membership stacks of Sec. 4 (with its own owner id), because it is merged into the parent's block structure at BM.14 (agent-09 note 4).
It is also Merge-able into a block structure (Sec. 2, Merge with an in-order traversal).
In BaseCase, N <= |S| + delta*tau <= t^2 + 3t^3, so the cost is O(lg t) per operation.
In the inner top call with l_in = 0, N <= 1 + 3k and the cost is O(lg k).

## 4. Nested membership without O(n) initialisation per structure

**Problem.** A BMSSP call X needs O(1) answers to "is v a key of D_X, and where is its entry" (BM.14/15/21/23/25/28/29) and "is v in some Pl[j] of X, and which j" (BM.12/17/22).
A vertex can be simultaneously:
- a key of D_X,
- a key of the D of every ancestor of X (possibly stale), and
- a key of D's inside a running InnerSearch.

The same holds for P-membership: S_Y contains elements of the parent's Pl[j], and Y re-partitions them.
One array per structure would cost Theta(n') initialisation per call.

**Solution: per-vertex membership stacks.** For every vertex v keep a singly linked stack `memD[v]` of records (owner id, entry pointer) and likewise `memP[v]` of records (owner id, j, list node).
- A structure (or call) creates its records with a fresh owner id.
- Push a record on insertion into D (or into Pl[j]).
- Pop it on deletion, extraction by Pull, move by Merge, or Destroy (for P: removal at BM.17 or BM.30).
- Lookup for owner X: look at the top record of v. If its owner is X, it is X's record; otherwise v is not a member of X.

**Lemma MS (stack discipline).** At every moment when the pseudocode performs a lookup, insertion or deletion for owner X, every record of an owner other than X that lies above X's record in any stack belongs to a structure that is no longer live.
Moreover, no such record exists: every stack has its live records ordered by creation time of their owners, with the currently accessed owner topmost.

*Proof.* Two facts from the pseudocode are used.
- D_X is EMPTY while FindPivots(X) runs: it is created at BM.3 and first filled at BM.7 (agent-09 note 2). So records pushed by inner searches never interleave with X's own D-records.
- X's P-records are pushed only at BM.6, after FindPivots.

Owners are created and destroyed in LIFO order along the recursion:
- a call creates D_X at BM.3 and its P-records at BM.6;
- its sub-calls and InnerSearches create and destroy theirs strictly inside its lifetime;
- a returned structure D_i is consumed by the caller's Merge at BM.14 before any other operation of the caller;
- the top InnerSearch structure D_x is destroyed at FB.7;
- P-records of X are popped at BM.17 or BM.30 before X returns.

So at any time the live owners are exactly the owners on the current call chain, plus possibly one just-returned D_i being merged.
X accesses its own records only while none of its descendants is running. During BM.14, D_i's records are the topmost and are popped entry by entry as they are moved; the record of X below is then on top.
A push by owner X therefore always goes on top of records of X's ancestors. By induction, the records of each stack are ordered by owner creation time.

When X looks up v, all owners created after X are dead and have removed all their records: Destroy, Pull and Merge pop, and the P-records are popped at BM.30. So the top record of v belongs to X or to an ancestor of X. ∎

Each push, pop and lookup is O(1). Destroy of D_x (FB.7) costs O(|D_x| + #blocks), charged to the insertions into D_x.

**Marks without stacks.** The following never need nesting within one depth, so a timestamp array per depth suffices:
- sinks, F-bar trees and copied tree edges (depth 0 only, one FindPivots-B at a time);
- inner F-bar marks, K-stamps and heap membership (depth 1; one FindPivots-D invocation is active at a time, because a call's FindPivots finishes before its sub-calls start);
- touched marks (depth 0);
- S/Q/assigned marks in MakePivots (set after all searches of that invocation, per depth).

Iterated bootstrapping to depth r uses r + 1 array sets. All of this is O(n') space.

## 5. Space bound (G9)

Let n' = |V(H)| <= 2m + n, and let delta = 3 be the degree bound.

1. Graph, labels d, pe, orig, cyc, all timestamp arrays, dist/pred output: O(m + n).
2. **Live structures.** At any time the live D's are those of the calls on the current recursion chain.
   - These are at most one per outer level l in {L, ..., 0}, plus, during an InnerSearch, at most one per inner level l in {l_in, ..., 0}, plus one D_i being merged.
   - A D at outer level l has at most N_l = C delta t^4 2^{lt} entries, and at most n' because keys are distinct.
   - Let l* be the largest l with N_l < n'. Levels l > l* contribute at most n' each, and there are at most 1 + ceil(lg(C delta t^4)/t) = O(1) of them, since t >= 4 lg t for large n'.
   - Levels l <= l* contribute sum_{l <= l*} N_l <= 2 N_{l*} < 2n'.
   - The same computation applies to the inner levels with N'_l <= C delta t_in^4 2^{l t_in} <= C' delta k 2^{t_in} <= n'.
   - Hence all live D-entries, their blocks and membership records: O(n').
3. **Live P-records and frame lists.** Pl of X has size <= |S_X| <= t^2 2^{lt}. U_X and W'_X are O(t^3 2^{lt}). |W_X| <= k|Q_X| <= k|S_X|. J_X <= p_X. By the same geometric argument: O(n').
4. **F-bar trees and W-lists** of one FindPivots-B or FindPivots-D invocation.
   - Trees are vertex-disjoint (FB.9/FB.14, FD.12-FD.18), so O(n').
   - Wlist entries: each failed search contributes < k vertices, and |W| <= k|Q| <= k|S_X| <= t^3 2^{lt}. Charged as in item 3, this gives O(n') over the chain.
   - Partition groups: O(|T|).
5. **Heaps.** At most one Fibonacci heap is live at a time (FD.5 creates it, the next search discards it), and it has at most k_in * delta + 1 nodes.
6. **Recursion stack.** L + l_in + 2 frames, each O(1) apart from the lists already counted.

**Total space O(m + n) words.** Each word holds a real (a length), an integer of O(lg n) bits, or a pointer.

## 6. Preprocessing and output time (part of G8)

- BFS reachability O(n + m).
- Self-loop removal O(m). A self-loop is never a valid relaxation by T2, so dropping it is harmless.
- DegreeReduce O(m + n); n' <= 2m + n and |E(H)| <= 3m + n.
- Initialising d: O(n').
- Parameters: O(1) integer arithmetic on n'.
- Output (SS.10-SS.12): O(n') for the per-cycle minimum-hop scan, plus O(n) for unreachable vertices.
  - **Correctness of the map-back (tracker I15).** At termination every H-vertex reachable from xs is complete, so d[x] = dis_H(x).
  - All vertices of a gadget cyc[v] share len = dist_G(s, v), because the gadget is a zero-weight strongly connected cycle and its external edges carry the original weights.
  - e_v := the minimum-hops vertex of cyc[v]; equivalently the minimum-(len, hops) vertex, and ties in hops are harmless. Its canonical last edge tail(d[e_v].e) lies outside cyc[v], because a predecessor inside the gadget would have the same len and one hop fewer. So the edge is the image of an original edge (u, v, w) with d[e_v].len = dist(u) + w: a TIGHT original edge.
  - pred[v] := u = orig(tail(d[e_v].e)). The tail y lies in cyc[u], so hops(e_u) <= hops(y) = hops(e_v) - 1. Thus hops(e_.) strictly decreases along pred, the pred graph is acyclic, and every chain ends at s, the only vertex with pred = BOT.
  - Zero-weight cycles in G and parallel edges are handled by the same argument. Self-loops were removed in preprocessing and cannot be tight predecessor edges in an acyclic pred graph anyway.
- Total: **O(m + n)**. This is dominated by the main recursion, since m >= n - 1 on the reachable part. The unreachable part costs O(n) without affecting the sparse bound, which is stated for m >= n - 1, as in DMSY26.


## Appendix G — S6 Test report (editor re-runs)

Frozen label `S6final`, source `/research/agents/agent-10/work/S6_test_report.md`, sha256 `5bf631dbde6fcf54415ee5a41cddf7e3345ebdec9c0a16265e6ed087875be4e8`, frozen 2026-09-20T07:54:14Z.

# S6 — Test report: final independent re-run by the editor (agent-10), 2026-09-20 07:51–07:56 UTC

All six implementations were written by different agents, independently of the proof texts. They were re-run sequentially by agent-10, one CPU worker at a time, after pseudocode PCv2.3 was frozen (sha256 970ce218…). All arithmetic is exact (Python ints and Fractions). Distances are compared with binary-heap Dijkstra and/or Bellman–Ford, and with an oracle-free certificate check: d(s) = 0, every edge satisfies the triangle inequality, pred edges are tight and form an arborescence, and unreachable vertices get INF.

Most suites also assert lemma-level invariants on every call against an exact oracle of that call's instance. This includes every inner deadline instance.

**These are finite tests: evidence, not proof.**

Semantics exercised: the master configuration (version-stamped full-walk labels, SUPPRESSION walls, FIX-STALE by deletion, FIX-BASE, FIX-EMPTY, FIX-RESEL, τ = k, l_in ≥ 1, one-hit merge, touched-set trees). Several suites also run nesting depth 2 and 3, the sink variant, and plain corrected DMSY26.

## Summary of the final re-run

| suite | author | command | result |
|---|---|---|---|
| agent07_b1 | agent-07 | `cd agents/agent-07/work && python3 tests/run_b1.py --seeds 2 --check --quick` | runs=1040 (2 seeds) failures=0; invariant violations NONE (full-walk shadow checker on every Relax; per-instance oracles incl. every inner search); all FindPivots-B paths exercised (e.g. tiny/d2/red: 18375 inner searches, 545 merges, 12317 new trees, 5513 failed) |
| agent01_impl | agent-01 | `cd agents/agent-01/work/impl && python3 run_tests.py 4 77 master_t2k2,master_t2k6,master_t1k4,dmsy26_fixed` | 92 graphs x 4 configs: ok=92 bad=0 dup=0 viol=0 each (e.g. master_t1k4: 1776 calls, 1083 FindPivots, 2419 inner calls, 1684 loop iterations with the S2/editor loop invariants checked) |
| agent01_api | agent-01 | `cd agents/agent-01/work/impl && python3 b1_api.py` | self-test (200 random multigraphs x 3 configs, certificate on returned pred edges): failures 0 |
| agent04_full | agent-04 | `cd agents/agent-04/work/impl && python3 tests_full.py` | 200 runs, 0 fails (debug + inner deadline-instance oracle; 1528 inner runs; FindPivots-B new/merge/fail = 884/77/567) |
| agent04_deep | agent-04 | `cd agents/agent-04/work/impl && python3 tests_deepinner.py 60 40` | 60 runs with l_in >= 2 (nested inner recursion), 0 fails (278 inner runs; fb new/merge/fail = 44/5/229) |
| agent04_wit | agent-04 | `cd agents/agent-04/work/impl && python3 replay_witness_agent09.py` | agent-09 FIX-BASE witness replayed in the bootstrapped mode with 4 parameter sets: all OK |
| agent09_impl | agent-09 | `cd agents/agent-09/work/impl && python3 run_tests.py` | quick suite runs=1485, fails=0 (invariant-checked, fast 5-tuple labels vs full-path mode) |
| agent09_wit | agent-09 | `cd agents/agent-09/work/impl && python3 witness_F2_replay.py` | errata witness E2: with FIX-BASE the output is correct; without FIX-BASE (and done-filter FIX-STALE) a reachable vertex is left at INF, as documented |
| agent08_impl | agent-08 | `cd agents/agent-08/work/impl && python3 test_bdmsy.py 300 5` | classic / B (suppression) / B_sink: 300 trials each OK, with check=True per-call oracle assertions |
| agent06_modes | agent-06 | `cd agents/agent-06/work && python3 tests/test_modes.py` | 1500 + 156 suite runs: wrong outputs 0 in every mode; the only assertion violations are in the deliberately naive FRESH-label mode (58), the negative control that confirms obstruction O1; deadline ("boot") and Dijkstra modes: 0 violations |

## Raw logs (verbatim tails; full logs in agents/agent-10/work/s6_runs/)

### agent01_api.log (sha256 prefix 9e82178e9c75b692)
```
=== agent01_api  (2026-09-20T07:52:10Z)  cd /research/agents/agent-01/work/impl && python3 b1_api.py
self-test done, failures: 0
elapsed 1.08s
exit=0
```

### agent01_impl.log (sha256 prefix c9b89e400a8d92a8)
```
=== agent01_impl  (2026-09-20T07:52:08Z)  cd /research/agents/agent-01/work/impl && python3 run_tests.py 4 77 master_t2k2,master_t2k6,master_t1k4,dmsy26_fixed
elapsed 1.5
master_t2k2 {'ok': 92, 'bad': 0, 'dup': 0, 'viol': 0, 'calls_checked': 949, 'fp_checked': 296, 'inner_checked': 502, 'f2_deletions': 0, 'f3_triggers': 3, 'loop_checked': 857, 's2_loop_checked': 857}
master_t2k6 {'ok': 92, 'bad': 0, 'dup': 0, 'viol': 0, 'calls_checked': 885, 'fp_checked': 290, 'inner_checked': 503, 'f2_deletions': 0, 'f3_triggers': 3, 'loop_checked': 793, 's2_loop_checked': 793}
master_t1k4 {'ok': 92, 'bad': 0, 'dup': 0, 'viol': 0, 'calls_checked': 1776, 'fp_checked': 1083, 'inner_checked': 2419, 'f2_deletions': 0, 'f3_triggers': 1, 'loop_checked': 1684, 's2_loop_checked': 1684}
dmsy26_fixed {'ok': 92, 'bad': 0, 'dup': 0, 'viol': 0, 'calls_checked': 915, 'fp_checked': 297, 'inner_checked': 0, 'f2_deletions': 0, 'f3_triggers': 2, 'loop_checked': 823, 's2_loop_checked': 823}
elapsed 1.56s
exit=0
```

### agent04_deep.log (sha256 prefix c4257cf69ecc37d2)
```
deep-inner: total 60 maxn 40 fails 0 time 0.9s
{'relax': 44431, 'valid': 28009, 'ds_insert': 13506, 'ds_delete': 9076, 'ds_pull': 1883, 'inner_runs': 278, 'fb_new': 44, 'fb_merge': 5, 'fb_fail': 229, 'fd_new': 778, 'fd_merge': 0, 'fd_fail': 60, 'calls': 2221}
elapsed 0.95s
exit=0
```

### agent04_full.log (sha256 prefix 677c4a5828965881)
```
=== agent04_full  (2026-09-20T07:52:11Z)  cd /research/agents/agent-04/work/impl && python3 tests_full.py
total 200 fails 0 time 5.4s
aggregate stats: {'relax': 112293, 'valid': 67314, 'ds_insert': 41694, 'ds_delete': 29143, 'ds_pull': 3936, 'inner_runs': 1528, 'fb_new': 884, 'fb_merge': 77, 'fb_fail': 567, 'fd_new': 1185, 'fd_merge': 0, 'fd_fail': 343, 'calls': 5664}
elapsed 5.45s
exit=0
```

### agent04_wit.log (sha256 prefix 28c0101115cb4102)
```
plain (2, 4, 2, 2) OK [Fraction(0, 1), Fraction(1, 1), Fraction(1, 1), Fraction(1, 1), Fraction(2, 1), Fraction(1, 1), Fraction(2, 1), Fraction(2, 1), Fraction(2, 1)]
boot  (1, 2, 1, 1) OK [Fraction(0, 1), Fraction(1, 1), Fraction(1, 1), Fraction(1, 1), Fraction(2, 1), Fraction(1, 1), Fraction(2, 1), Fraction(2, 1), Fraction(2, 1)]
boot  (1, 2, 2, 1) OK [Fraction(0, 1), Fraction(1, 1), Fraction(1, 1), Fraction(1, 1), Fraction(2, 1), Fraction(1, 1), Fraction(2, 1), Fraction(2, 1), Fraction(2, 1)]
boot  (2, 2, 2, 1) OK [Fraction(0, 1), Fraction(1, 1), Fraction(1, 1), Fraction(1, 1), Fraction(2, 1), Fraction(1, 1), Fraction(2, 1), Fraction(2, 1), Fraction(2, 1)]
boot  (1, 3, 1, 2) OK [Fraction(0, 1), Fraction(1, 1), Fraction(1, 1), Fraction(1, 1), Fraction(2, 1), Fraction(1, 1), Fraction(2, 1), Fraction(2, 1), Fraction(2, 1)]
boot  (2, 4, 2, 2) OK [Fraction(0, 1), Fraction(1, 1), Fraction(1, 1), Fraction(1, 1), Fraction(2, 1), Fraction(1, 1), Fraction(2, 1), Fraction(2, 1), Fraction(2, 1)]
elapsed 0.19s
exit=0
```

### agent06_modes.log (sha256 prefix 21f14b19f94bd5ab)
```
=== agent06_modes  (2026-09-20T07:53:36Z)  cd /research/agents/agent-06/work && python3 tests/test_modes.py
runs 1500 wrong 0 assertion-violations {('fresh', 'tree vertex outside U~(B,S) (Remark 3.3 violated)'): 58} secs 1.9
suite runs 156 wrong 0 viol {('fresh', 'tree vertex outside U~(B,S) (Remark 3.3 violated)'): 58, ('fresh', 'randconn_int', 'tree vertex outside U~(B,S) (Remark 3.3 violated)'): 1, ('fresh', 'rand_zero', 'tree vertex outside U~(B,S) (Remark 3.3 violated)'): 1, ('fresh', 'randconn_zero', 'tree vertex outside U~(B,S) (Remark 3.3 violated)'): 1, ('fresh', 'rand_bin', 'tree vertex outside U~(B,S) (Remark 3.3 violated)'): 1, ('fresh', 'randconn_bin', 'tree vertex outside U~(B,S) (Remark 3.3 violated)'): 1, ('fresh', 'randconn_big', 'tree vertex outside U~(B,S) (Remark 3.3 violated)'): 1, ('fresh', 'randconn_frac', 'tree vertex outside U~(B,S) (Remark 3.3 violated)'): 1, ('fresh', 'rand_mixed', 'tree vertex outside U~(B,S) (Remark 3.3 violated)'): 1, ('fresh', 'randconn_mixed', 'tree vertex outside U~(B,S) (Remark 3.3 violated)'): 1, ('fresh', 'dag', 'tree vertex outside U~(B,S) (Remark 3.3 violated)'): 1, ('fresh', 'path', 'tree vertex outside U~(B,S) (Remark 3.3 violated)'): 1, ('fresh', 'zero_sccs', 'tree vertex outside U~(B,S) (Remark 3.3 violated)'): 1, ('fresh', 'parallel', 'tree vertex outside U~(B,S) (Remark 3.3 violated)'): 1, ('fresh', 'eqtree', 'tree vertex outside U~(B,S) (Remark 3.3 violated)'): 1, ('fresh', 'isolated', 'tree vertex outside U~(B,S) (Remark 3.3 violated)'): 1}
elapsed 2.89s
exit=0
```

### agent07_b1.log (sha256 prefix 9663248e64080445)
```
   tiny/d1/suppress/raw/fixed {'inner_searches': 808, 'fb_merge': 5, 'fb_newtree': 221, 'fb_failed': 582, 'calls': 3208, 'fix_f2_fired': 0}
   tiny/d1/suppress/red/fixed {'inner_searches': 6451, 'fb_merge': 396, 'fb_newtree': 3658, 'fb_failed': 2397, 'calls': 32542, 'fix_f2_fired': 0}
   tiny/d2/sink/raw/fixed {'inner_searches': 2346, 'fb_merge': 3, 'fb_newtree': 749, 'fb_failed': 1594, 'calls': 7845, 'fix_f2_fired': 0}
   tiny/d2/sink/red/fixed {'inner_searches': 18454, 'fb_merge': 336, 'fb_newtree': 12727, 'fb_failed': 5391, 'calls': 94704, 'fix_f2_fired': 0}
   tiny/d2/suppress/raw/fixed {'inner_searches': 2349, 'fb_merge': 5, 'fb_newtree': 743, 'fb_failed': 1601, 'calls': 7826, 'fix_f2_fired': 0}
   tiny/d2/suppress/red/fixed {'inner_searches': 18375, 'fb_merge': 545, 'fb_newtree': 12317, 'fb_failed': 5513, 'calls': 92898, 'fix_f2_fired': 0}
elapsed 31.97s
exit=0
```

### agent08_impl.log (sha256 prefix b53d7156276b70ae)
```
mode=classic: 300 trials OK
  base_extract=2963, bmssp_calls=3279, ds_delete=82, ds_insert=3316, ds_merge_item=4532, ds_pull=2979, ds_pull_items=4950, fp_extract=2663, partition_items=4646, pick_scan=1857, pivot_insert=1800, pivot_reselect=15, relax_calls=43704, relax_valid=19201
mode=B: 300 trials OK
  base_extract=11689, bmssp_calls=13091, ds_delete=69, ds_insert=8619, ds_merge_item=14294, ds_pull=10080, ds_pull_items=14294, fpB_fail=1005, fpB_merge=43, fpB_tree=1663, fp_extract=5494, hit=130, inner_U=11087, inner_runs=2711, partition_items=28261, pick_scan=5594, pivot_insert=5518, pivot_reselect=15, relax_calls=112948, relax_valid=56492
mode=B_sink: 300 trials OK
  base_extract=11724, bmssp_calls=13088, ds_delete=64, ds_insert=8618, ds_merge_item=14294, ds_pull=10085, ds_pull_items=14301, fpB_fail=1002, fpB_merge=31, fpB_tree=1670, fp_extract=5500, inner_U=11106, inner_runs=2703, partition_items=28276, pick_scan=5602, pivot_insert=5525, pivot_reselect=15, relax_calls=112917, relax_valid=56593
elapsed 1.95s
exit=0
```

### agent09_impl.log (sha256 prefix ffe8d0f3d2c6a7c3)
```
=== agent09_impl  (2026-09-20T07:52:16Z)  cd /research/agents/agent-09/work/impl && python3 run_tests.py
quick: runs=1485 fails=0 time=76.9s
elapsed 76.94s
exit=0
```

### agent09_wit.log (sha256 prefix ea2ecf29a82f53d3)
```
=== agent09_wit  (2026-09-20T07:53:33Z)  cd /research/agents/agent-09/work/impl && python3 witness_F2_replay.py
FIX-BASE=True dist= ['0', '1', '1', '1', '2', '1', '2', '2', '2'] correct= True
FIX-BASE=False WRONG OUTPUT: some reachable vertex left at INF ( IndexError )
reference ['0', '1', '1', '1', '2', '1', '2', '2', '2']
elapsed 0.03s
exit=0
```


## Appendix H — S7 Novelty (agent-02)

Frozen label `S7v2`, source `/research/agents/agent-02/work/S7_novelty.md`, sha256 `3f2c6eb3a62b18ed19c2d8c65441e5c049ed3296fe056a93a1929e77188d13bb`, frozen 2026-09-20T07:51:13Z.

# S7 — Novelty check and source map for Theorem B1 (agent-02)

Version: v2, 2026-09-20 (adds arXiv 2607.19346). Must be re-run immediately before any success claim.
Companion: `source_map.md` (dated table of all primary sources).

## 1. Claim under test
Theorem B1 (master §2): deterministic, exact SSSP on directed graphs with nonnegative real weights in the
comparison-addition model, time O(n + m·√log n·(log log n · log log log n)^{1/4}) for m = O(n)
(general m: master §2, per agent-05), space O(n + m). This is claimed to be o(m √(log n log log n)),
the sparse bound of DMSY26.

## 2. Closest prior work, and what B1 takes from each

| Work | Setting | Bound (sparse) | Relation to B1 |
|---|---|---|---|
| DMSY26 = Duan–Mao–Shu–Yin, arXiv 2602.07868v2, ICALP'26 | directed, det., comp.-add. | O(m √(log n log log n)) | B1 is DMSY26 with (i) errata E1–E8 fixed and (ii) FindPivots' Fibonacci-heap local Dijkstra replaced by capped runs of the (corrected) DMSY26 core on deadline instances. Recursion, data structure D, pivot trees and time-analysis framework are DMSY26's. |
| KR = Kadria–Roditty, arXiv 2609.15247 (14 Sep 2026) | **undirected, randomized** | O(m √log n (log log n)^{1/4} (log log log n)^{1/4}) | Same bound form. KR's key idea is the prototype for B1's new ingredient: use DMSY26's BMSSP as a sub-sorting bounded local search (their BoundSSSP, Lemma 7/App. B, stated for directed graphs). KR apply it to **ball construction inside the DMSY23 bundle framework**, with fresh labels and doubling t. Their Sec. 4 names BundleDijkstra (in-ball ≠ out-ball) as the obstruction for directed graphs and derandomization as open. |
| Cai, arXiv 2609.04825 (4 Sep 2026) | directed, det. | no worst-case improvement | Instance-dependent "charged-operation" bound O(OPT √(log OPT log log OPT)), using DMSY26 as a black box (App. K). Not a worst-case competitor. |
| Hair–Li–Li–Zhang, arXiv 2607.19346 (21 Jul 2026) | directed, real (possibly negative) weights, Las Vegas randomized | m^{1+o(1)}, o(1)-factor 2^{O(√(log n log log n))} | Not comparable: randomized, and 2^{O(√(log n log log n))} ≫ √(log n log log n). For nonnegative weights they defer to Dijkstra. (Found by agent-10/agent-04; verified by agent-02.) |
| Yan, SOSA'26 (arXiv 2510.12598) | undirected, det. | O(m √(log n log log n)) | Derandomizes DMSY23. |
| DMMSY25, STOC'25 (arXiv 2504.17033) | directed, det. | O(m log^{2/3} n) | Superseded by DMSY26. |
| DMSY23, FOCS'23 (arXiv 2307.04139) | undirected, rand. | O(m √(log n log log n)) | Bundle framework used by KR. |
| Thorup'04, Hagerup'00, etc. | integer weights, word RAM | — | Different model (excluded by the goal). |

## 3. What is new in B1 (if the proofs survive review)
1. **First directed deterministic algorithm below DMSY26.** A bootstrapped FindPivots is a new
   ingredient: each local search is a capped run of the corrected core on the deadline instance G_x
   (S1 §C), with existing trees as sinks and hit-merging (S3). KR's BoundSSSP cannot be used unchanged.
   Fresh labels explore vertices outside Ũ(B,S), which breaks p ≤ |Ũ|/k and the Line-29 charging
   (agent-06 Obstruction O1: a 3-regular family forcing Θ(t) per frontier leaf per level). What makes
   the transplant correct is the deadline-instance semantics, under which the local source is complete
   even when it is incomplete in G (S1 D3).
2. **Corollary (undirected, deterministic).** An undirected graph is a directed graph with both arc
   directions (degree ×2), so B1 also gives a *deterministic* O(m √log n (log log n log log log n)^{1/4})
   algorithm for undirected graphs, matching KR's randomized bound. KR list derandomization as their
   main open obstacle. This is an immediate consequence of B1, not an extra claim needing separate proof.
3. **Errata to DMSY26** (master §9, E1–E8; E8 = FIX-RESEL found by agent-08/agent-04/agent-07). The most important is E1: stale D entries make the U_i
   overlap, so Lemma 3.7 inv. 2, Lemma 3.8 disjointness and Obs. 3.5 fail as written. Four agents found
   it independently, and agent-03 and agent-01 reproduced it with executable counts. Fixes cost O(1)
   per entry. Final distances in the published algorithm appear correct in all tests; the
   running-time proof is what breaks.

## 4. What is NOT new (to be stated in any write-up)
- Using DMSY26's BMSSP as a local subroutine is KR's idea (for undirected balls). B1's contribution is
  making it work inside directed FindPivots (deadline instances, sinks/hits, threshold-k cap,
  confinement L3+, corrected core), plus the resulting directed and deterministic bound.
- The resulting bound has the same form as KR's. The improvement over DMSY26 is a factor
  (log log n / log log log n)^{1/4} = ω(1), which is small, and purely asymptotic (agent-05 M1: the
  parameter constraints only hold for astronomically large n; below n_0 the algorithm runs Dijkstra).
  Iterated bootstrapping (agent-05 S4 §7, Lemma M, depth 3) gives a further tiny gain,
  m √log n (log log n)^{1/4} (log log log n)^{1/8} (log^{(4)} n)^{1/8}, which is also strictly below KR's
  undirected randomized bound. It is not claimed in Theorem B1.
- Nothing here approaches O(m √log n). KR's discussion shows that O(mk)-time ball construction would
  give that for undirected graphs; for directed graphs the analogue is the Q-search constraint
  k·c(k) ≤ t (S4). Open.

## 5. Searches performed (2026-09-20)
Web (general): "directed single-source shortest path comparison-addition 2026 faster than sqrt(log n log log n) arXiv";
"arXiv 2026 shortest path sorting barrier directed improvement Duan Mao Shu Yin follow-up"; "2602.07868 citing
directed SSSP improvement"; "directed SSSP real weights comparison-addition 2026 m sqrt(log n) new algorithm";
"FindPivots bootstrapping directed shortest path 2026 log log log"; "deterministic single-source shortest paths
log^{1/2} n (log log n)^{1/4} 2026"; "Duan Mao Shu Yin 2026 directed SSSP follow-up improvement arXiv BMSSP new bound
September 2026". arXiv listings: cs.DS 2026-08 and 2026-09 (all shortest-path titles).
Result: no directed nonnegative-real-weight SSSP bound below DMSY26 found. Only implementations/benchmarks of
DMMSY25 (e.g. arXiv 2511.03007, GitHub ports), negative-weight/integer results (2609.05590, 2602.16638,
2511.07859) and special classes (2608.19538).
Caveat: web search cannot rule out unindexed preprints from the last days. Re-check arXiv "new" listings
(cs.DS, cs.DM) immediately before any success claim.

## 6. Pre-claim re-check (agent-02, 2026-09-20, sandbox clock ~08:15 UTC)
- arXiv cs.DS "recent" (covers 2026-09-14 .. 2026-09-18, 139 entries). Shortest-path titles: 2609.15247 (KR,
  undirected randomized), 2609.12211 (DAG preservers lower bounds), 2609.12021 (shortest even directed cycles,
  char. 2). No directed nonnegative-real-weight SSSP improvement.
- arXiv cs.DS "new" (listing of Fri 2026-09-18; no listings are issued on Sat/Sun). No new submissions or
  cross-lists on SSSP. Replacements only: 2410.14638 (bidirectional Dijkstra instance-optimality, point-to-point),
  2509.13448 (empirical BMSSP vs Dijkstra on Lightning Network). Neither is comparable.
- arXiv cs.DM "recent" (2026-09-14 .. 2026-09-18): no shortest-path papers.
- Web search ("shortest path directed real weights 2026 new algorithm faster Duan / sorting barrier September"):
  only DMSY26, DMMSY25, PR05, negative-weight results and implementations.
- Independent novelty checks by agents 01, 03, 04, 05, 09, 10 (board) agree: no competitor.
**Conclusion:** as of 2026-09-20, no published or preprinted result gives a deterministic directed
nonnegative-real-weight SSSP bound o(m √(log n log log n)) on sparse graphs. Theorem B1 would be new. The
technique "DMSY26 BMSSP as a bounded local search" must be credited to Kadria–Roditty (2609.15247, Lemma 7).


## Appendix H2 — Dated source map (agent-02)

Frozen label `S7xmapv2`, source `/research/agents/agent-02/work/source_map.md`, sha256 `b5b8667aed4051bf9ff23101620bb80b681bcb3d7750408c6e12a5b952ad968c`, frozen 2026-09-20T07:51:13Z.

# Dated primary-source map (agent-02) — last checked 2026-09-20 (v2: + arXiv 2607.19346)

Model throughout: exact SSSP, nonnegative real weights, comparison-addition model (only + and comparisons on weights, O(1) each), unless stated.

| Date | Work | Graphs | Det/Rand | Sparse bound (m = O(n)) | General bound | Notes |
|---|---|---|---|---|---|---|
| 1959/1987 | Dijkstra + Fibonacci heap [FT87] | directed | det | O(n log n) | O(m + n log n) | produces sorted order; universally optimal for ordering [HHR+24] |
| 2005 | Pettie–Ramachandran [PR05] | undirected | det | O(n log n) worst | O(m α + min{n log n, n log log r}) | r = max/min weight ratio |
| 2023 (FOCS) | Duan–Mao–Shu–Yin [DMSY23] arXiv 2307.04139 | undirected | rand | O(m sqrt(log n log log n)) | O(sqrt(mn log n) + ...) | bundles/balls + BundleDijkstra |
| 2026 (SOSA) | Yan [Yan26] arXiv 2510.12598 | undirected | det | O(m sqrt(log n log log n)) | — | derandomizes DMSY23 |
| 2025 (STOC) | Duan–Mao–Mao–Shu–Yin [DMMSY25] arXiv 2504.17033 | directed | det | O(m log^{2/3} n) | O(m log^{2/3} n) | BMSSP + k-step Bellman–Ford pivots |
| 2026-02 (ICALP'26) | Duan–Mao–Shu–Yin [DMSY26] arXiv 2602.07868v2 | directed | det | **O(m sqrt(log n log log n))** | O(m sqrt(log n) + sqrt(mn log n log log n)) | **current directed frontier (target to beat)** |
| 2026-07-21 | Hair–Li–Li–Zhang, "Bellman-Ford in Almost-Linear Time", arXiv 2607.19346 | directed, REAL (possibly negative) weights | **Las Vegas randomized** | m^{1+o(1)} with m^{o(1)} = 2^{O(sqrt(log n loglog n))} (their Thm 1.1) | same | not a worst-case competitor for nonneg weights: 2^{O(sqrt(log n loglog n))} >> polylog, and randomized; for nonneg weights they cite Dijkstra (found by agent-10/agent-04; verified by agent-02 via arXiv HTML 2026-09-20) |
| 2026-09-04 | Bin Cai, arXiv 2609.04825 | directed | det | no worst-case improvement claimed | instance-dependent O(OPT sqrt(log OPT loglog OPT)) "charged-operation" bound | uses DMSY26 as black box (App. K); game-theoretic PSPACE interpreter for OPT; not a worst-case time competitor |
| 2026-09-14 | Kadria–Roditty, arXiv 2609.15247 | **undirected** | **rand** | O(m log^{1/2} n loglog^{1/4} n logloglog^{1/4} n) | never worse than DMSY23 | balls via BoundSSSP (Lemma 7, App. B) derived from DMSY26; bundles via active-vertex Bellman–Ford; directed and deterministic left OPEN (Sec. 4) |

## Other 2026 items seen in listings (not comparable)
- arXiv 2609.05590 (Duong): deterministic negative-weight integer SSSP — integer weights, different problem.
- arXiv 2602.16638: n^{2+o(1)} negative real weights SSSP — different problem.
- arXiv 2609.12211: lower bounds for shortest-path preservers of DAGs — different problem.
- arXiv 2608.19538: power-law graphs — special class.

## Key facts for novelty checks
1. KR's Lemma 7 (BoundSSSP) is stated for **directed** graphs of max degree Δ: after O(n) global init, computes δ(v,w) for all w with δ(v,w) ≺ B in O(Δ|U| sqrt(log|U| loglog|U|)). It restarts from fresh labels (d[v]=0, others ∞) per call and uses doubling t / increasing level. **This tool is prior art** (Sep 14 2026); any directed bootstrapping must cite it.
2. KR state (Sec. 4): "The obstruction to a directed result lies instead in BundleDijkstra ... We leave as an open problem the adaptation of BundleDijkstra to directed graphs". They do not consider bootstrapping DMSY26's FindPivots.
3. DMSY26 FindPivots (Alg. 2) uses a Fibonacci-heap local Dijkstra per frontier vertex on *global* labels, with an early stop at k reached vertices and an early stop + merge on touching an existing F̄_j. Bootstrapping this search (rather than KR's fresh-label BoundSSSP) is not in DMSY26, KR or Cai.

## Searches performed (2026-09-20)
- web: "directed single-source shortest path comparison-addition 2026 faster than sqrt(log n log log n) arXiv"
- web: "arXiv 2026 shortest path sorting barrier directed improvement Duan Mao Shu Yin follow-up"
- web: "2602.07868 citing directed SSSP improvement"
- web: "directed SSSP real weights comparison-addition 2026 m sqrt(log n) new algorithm"
- arXiv listings cs.DS 2026-08 and 2026-09 (shortest-path titles only).
Re-check before any success claim.


## Appendix E2 — S4 full derivation, review log and F1-F9 discharge table (agent-05)

Frozen label `S4xcostv5`, source `/research/agents/agent-05/work/cost_analysis.md`, sha256 `bd0bb773c8ade96144b2a159cbdc0942f16a756f333612b26af6e436086c937e`, frozen 2026-09-20T07:51:13Z.

# Independent running-time and space analysis of bootstrapped DMSY26 ("BDMSY")

Author: agent-05. Status: **independent re-derivation of the TIME and SPACE analysis only**. It is
conditional on correctness facts F1-F9 (Sec. 0), which the integrated proof document has to establish.
It is not a success claim. Version 5 (07:50 UTC by `date`). v5 resolves every item from the three
reviews (agent-09 R1-R6, agent-03 items 1-6, agent-06 M1-M4); see Sec. 12. Version 4 (~07:40 UTC). v4 cites pseudocode.md v2 line numbers, uses touched-set trees N_x, and treats suppression as primary. Version 3 (07:40 UTC). v3 adds sink-semantics accounting (tracker I10) to Sec. 3 and Sec. 6. v2 uses DMSY26's printed parameters (M = t 2^{(l-1)t}) and adds
the stale-entry deletion fix (B7).

Notation follows DMSY26 = Duan-Mao-Shu-Yin, arXiv 2602.07868v2 (Alg. 2/3/4, Lemmas 3.1-3.9, A.1, A.2).
"Line x" refers to Algorithm 3 of DMSY26. All logs are base 2 and taken as max(log x, 1).

---------------------------------------------------------------------------------------------------

## 0. What is analysed and what is assumed

**Algorithm BDMSY(t, k; t').** Precisely, this is agents/agent-04/work/pseudocode.md v2. Line
references BM.x, BC.x, FB.x, FD.x, MP.x, RX.x and SS.x point to that file. In words, it is DMSY26 BMSSP
with two changes.
1. **Size bookkeeping made consistent (Sec. 1)** and **stale-entry deletions** (B7). Thresholds are as
   printed (M_l = t 2^{(l-1)t}, Lambda_l = t^3 2^{lt}), the frontier bound is sigma_l = 4t^2 2^{lt}
   (agent-10 I2), and settled U_i and W' are deleted from D (agent-03 F1/F2/F3, agent-08, agent-02).
2. **FindPivots is replaced by FindPivots^B.** For each x in S not yet in a tree, FindPivots^B runs an
   inner search IS(x). IS(x) is a DMSY26 BMSSP with parameter t' (and its own Fibonacci-heap
   FindPivots, k' = ceil(t'/log t')), called as BMSSP'(B, {x}, l*) with top-level loop threshold
   tau = k. It runs on the global labels, and vertices of existing trees Fbar are *blocked*: edges into
   them are not relaxed but recorded as hits. Afterwards FindPivots^B classifies the search as
   SUCCESS (|U_x| >= k: new tree), MERGE (hit, |U_x| < k: U_x joins a hit tree through one hit edge) or
   FAIL (full, no hit, |U_x| < k: W_x = U_x, x joins Q). Then it partitions the trees (Lemma A.1,
   s = k) and forms P_j exactly as in Algorithm 2. (The agent-09 and agent-10 variants, where a hit
   takes precedence over size, change nothing below.)

Here l* := min{ l >= 1 : Lambda'_l >= k }, where Lambda'_l = t'^3 2^{l t'} is the inner threshold.

**Correctness facts that this analysis USES but does not prove.** The integrated proof must supply them.

- **F1** (inner search = BMSSP on a deadline instance). IS(x) executes as the DMSY26 BMSSP (with
  corrected bookkeeping) on an instance J_x in which x is complete. That instance is the
  deadline/feasible-region instance of agent-07/agent-10/agent-02. Hence the structural lemmas
  (DMSY26 3.7, 3.8, Obs. 3.5, Sec. 3.4 items 2-6) hold *inside* IS(x) with dis := dis_{J_x}.
  Relaxations of edges leaving the feasible region are invalid and cost O(1) each.
- **F2** x is in U_x. Inner partial execution implies |U_x| > tau = k. Inner full execution implies
  U_x = U~_J(B, {x}).
- **F3** Trees: Fbar vertices are pairwise disjoint within one FindPivots^B call. Every Fbar vertex
  lies in U~(B,S) of the *outer* call. Tree edges are edges of G. Every tree has >= k vertices.
- **F4** FAIL searches have |W_x| = |U_x| < k, and <W, union P_j> is a frontier for U~(B,S)
  (the analogue of Lemma 3.2).
- **F5** Main-level structure. DMSY26 Lemmas 3.7 and 3.8 hold with the corrected thresholds, in
  particular: U_i disjoint and ordered, U = disjoint union of U_i and W', and for full executions
  U = U~(B,S) and S is a subset of U. Sec. 3.4 items 5-6 hold: the U_X on one layer are disjoint, and
  each vertex's calls form a chain. Obs. 3.5 holds, and each edge (u,v) has at most one
  *insertion event* (a valid relaxation at Line 24, at Line 37, or in a base case).
- **F6** Inner searches never insert into an outer data structure D. Their relaxations are not
  insertion events.
- **F7** Every call with S nonempty has |U| >= 1. For full calls, S is a subset of U. For partial
  calls, |U| > Lambda_l.
- **F8** p_j, P_j and Q satisfy Remark 3.3: P_j is a subset of F_j, |P_j| < 3k, the P_j are disjoint,
  Q union (union P_j) = S, and each nonempty P_j contains a vertex of S.
- **F9** (for Sec. 8 only) The output mapping from the degree-reduced graph back to G is correct.

Every place below where one of F1-F9 is used is marked [Fi].

---------------------------------------------------------------------------------------------------

## 1. Parameters and size bookkeeping (main level; inner level identical with primes)

Parameters follow DMSY26 as printed; v1 of this file misread M. Fix integers t >= t_0 (an absolute
constant) and 2 <= k <= t. Let delta >= 3 be the max in/out degree after degree reduction and N the
vertex count. For l >= 1:

- M_l := t 2^{(l-1)t} (the D parameter at level l, DMSY26 Alg. 3 line 3)
- sigma_l := 4 t^2 2^{lt} (the maximum |S| of a level-l call)
- Lambda_l := t^3 2^{lt} (the loop threshold, as printed)
- level 0 (base case): sigma_0 = 4t^2 and Lambda_0 = t^3

**(B1) Frontier size.** A child of a level-l call gets S_i = Pull() (at most M_l keys) together with
{v in P_j : d[v] < B_i} for each pulled key that equals some p_j. By [F8], |P_j| < 3k.
So |S_i| <= M_l (1 + 3k) <= 4k t 2^{(l-1)t} <= 4 t^2 2^{(l-1)t} = sigma_{l-1}, using k <= t.
At the root, S = {s}. This is agent-10's resolution of agent-09's I2; only a constant changes.

**(B1') Pseudocode variant FIX-L13 (agent-04 pseudocode.md Sec. 2).** If 3k <= t, then
|S_i| <= 3k M_l <= t^2 2^{(l-1)t}, so DMSY26's |S| <= t^2 2^{lt} holds verbatim and (B2) holds without
the factor 1/4. Sec. 8.2 of the pseudocode chooses k = floor(t/(3g)), so this variant applies, and every
"4|U|/t" below may be read as "|U|/t". Constants only.

**(B2) Partial implies |U| > t|S|/4.** A partial level-l call exits with
|U| > Lambda_l = t^3 2^{lt} = t sigma_l / 4 >= t|S|/4. The factor 1/4 only changes constants at the four
places that use it: FindPivots cost in partial calls, |Q_Y| <= |S_Y| in partial calls, Line 33, and
T5,par.

**(B3) |U| = O(Lambda_l).** U is the disjoint union of the U_i and W' [F5]. The loop overshoots
Lambda_l by at most one child: |U_i| <= Ubar_{l-1}. Also |W'| <= |W| <= k|Q| <= k sigma_l <= 4 Lambda_l.
So Ubar_l <= 5 Lambda_l + Ubar_{l-1}, which gives Ubar_l <= 6 Lambda_l for t >= 3.

**(B4) D sizes and costs.** N_X <= |S| + delta |U| = O(delta t^3 2^{lt}), so N_X/M_l = O(delta t^2 2^t)
and log(N_X/M_l) = t + O(log t) = O(t) for delta <= t. Lemma 3.4's requirement "M >= log(N/M)" fails
by an additive O(log t) at l = 1, where M = t (agent-04). The amortization only needs
log(N/M) = O(M): a BST operation is charged to Theta(M) block items. Merge needs
M_{l-1} = M_l 2^{-t} < M_l/3, true for t >= 2. So **Insert is O(t) amortized, Pull and Merge are
linear, and Delete is O(1) amortized** (agent-04 S5 for Delete).

**(B5) Depth.** L := min{ l : Lambda_l >= N } <= ceil(log N / t). The root call is full.

**(B6) Base case (l = 0).** Algorithm 4 with threshold Lambda_0 = t^3, using agent-04's fix: check
the threshold before extracting, and set B' := the minimum stored value in D, else B. The BST holds
O(delta t^3) items, so each operation costs O(log t). A base call costs O((|S| + delta |U|) log t)
= O(delta |U| log t), because S is a subset of U (full) or |S| < 4|U|/t (partial).

**(B7) Stale-entry deletions (F1/F2/F3 of agent-03 = the agent-08 and agent-02 fixes).** After each
Merge, delete U_i from D, and delete W' before returning. This costs O(1) amortized per deleted key
and O(|U|) per call. Without it, G1 and G2 below are FALSE: agent-03 measured 239 U_i-overlaps and
156 double Line-24 insertions in 200 small graphs. **This analysis is for the corrected algorithm.**

---------------------------------------------------------------------------------------------------

## 2. Cost of one inner search IS(x)

Inner parameters: t', k' = ceil(t'/log t'), and the thresholds of Sec. 1 with primes, on the same
reduced graph (max degree delta). The top call is BMSSP'(B, {x}, l*) with loop threshold tau = k,
where l* = min{ l >= 1 : Lambda'_l >= k }. We assume k >= t' and Lambda'_{l*-1} <= k. For l* = 1 this
means t'^3 <= k. Both hold for the parameters of Sec. 5 whenever N >= n_0 (Sec. 5), because
t'^3 2^{t'} = polylog(k) 2^{O(sqrt(log k loglog k))} = k^{o(1)}.

**(I1) Output size.** We need Lambda'_{l*-1} <= k.
- If Lambda'_1 < k, then l* >= 2 and this is the minimality of l* (agent-03 review item 1).
- If l* = 1, it is the constraint t'^3 = Lambda'_0 <= k of Sec. 5.
In both cases |U_x| <= tau + Ubar'_{l*-1} + |W'_top| <= k + 6 Lambda'_{l*-1} + k' <= 8k. Here |W'_top| < k' because
the top inner call has |S| = 1, so |Q_top| <= 1 (agent-09 R3).
A partial search has |U_x| > k, and a full one has x in U_x [F2]. So **1 <= |U_x| <= 8k**.

**(I2) Top-level structure.** At the top call, |S| = 1 and tau = k >= t', so partial implies
|U| > t'|S| >= t'|S|/4. That is (B2) at the top call. The top D has N <= 1 + 8 delta k keys and
parameter M' = t' 2^{(l*-1)t'}. From Lambda'_{l*} = t'^3 2^{l* t'} >= k we get
M' >= k / (t'^2 2^{t'}), so log(N/M') = t' + O(log t') and top-level insertions cost O(t'). Every call
below the top is a standard BMSSP' with (B1)-(B7), so the Sec. 1 facts hold there.

**(I3) Inner cost by global summation.** Sum over all calls Y in the inner recursion tree T_x. [F1] and
[F5] (inside J_x) give the following:
- (a) The U_Y of each inner layer are disjoint subsets of U_x, so the sum over Y in T_x of |U_Y| is at
  most (l*+1)|U_x|. Each call has |U_Y| >= 1 [F7], so the number of calls is at most (l*+1)|U_x|.
  Every call has a nonempty S. The pseudocode implements FIX-STALE by deletion (BM.15, BM.29), so a
  Pull on a nonempty D returns a nonempty S_i. In the done-filter variant a filtered S_i may be
  empty. The sub-call is then skipped with B'_i := B_i and U_i := empty, or it is made and returns
  full in O(1), which is charged to one of the >= 1 discarded entries, each paid at its insertion
  (agent-09 R1; agent-06 tracker I18).
- (b) Every inner insertion event (BM.21, BM.28, BC.7 of an inner call) relaxes an out-edge of an
  inner-settled vertex: one in an inner base-case U or an inner W'. Every inner-settled vertex belongs
  to U of the inner TOP call, by the disjoint-union structure (F5 inside J_x). Vertices whose labels
  are lowered by inner FindPivots-D searches, or by 2-hop relaxations in partial inner calls, are not
  settled and create no events. Their cost is inside the per-call terms of (e): a partial inner call
  has |S_Y| <= 4|U_Y|/t' (agent-03 review item 2). Each edge has at most one event, so there are at
  most delta |U_x| events, each costing O(t').
- (c) Every inner re-selection charged to a cross edge (DMSY26 T5,full) uses an edge of E(U_x), and
  each such edge is charged at most once. That gives at most delta |U_x| charges of O(t').
- (d) The inner Q-appearances satisfy sum |Q_Y| <= |U_x| (delta + 1) + |U_x| l*/t'. This is the DMSY26
  argument inside J_x. x is never re-inserted, because no in-edge of x is validly relaxed [F1]. Each
  appearance costs O(k' log k') = O(t') in the inner FindPivots.
- (e) Direct per-call work, per vertex of U_Y, is: inner FindPivots O(log k' + delta), pivot inserts
  O(t'/k') = O(log t'), picking O(1), edge scans O(delta), re-selection-once O(t'/k'), Line 33 O(1).
  In total this is O((log t' + delta) |U_Y|). Base calls cost O(delta log t' |U_Y|) by (B6).
- (f) Edges out of U_x into infeasible or blocked vertices are scanned but never produce insertions.
  They cost O(1) per scan and are included in the O(delta) edge-scan term of (e).
- (g) The post-hoc hit/merge test scans the out-edges of U_x: O(delta |U_x|).

Summing gives

    cost(IS(x)) <= C_in |U_x| * c_in,   where   c_in := l* (log t' + delta) + delta log t' + delta t'.   (I3)

With delta = 3 and t' := ceil( sqrt( log k * log log k ) ), we have l* <= ceil(log k / t'), and

    c_in(k) = O( (log k / t') log t' + t' ) = O( sqrt( log k * log log k ) ).                          (I4)

**Remark (general delta).** In (I3) the l* * delta term is real. Every inner layer scans all
in-bound out-edges of the vertices it explores, both in the inner local Dijkstra and at Line 23.
Therefore c_in / delta >= l* + t' >= 2 sqrt(log k) for *every* choice of t'. This matters for the
general-m regime in Sec. 6, and it is where I disagree with the general-m formula of agent-01/agent-10.

---------------------------------------------------------------------------------------------------

## 3. Cost of FindPivots^B in one main call X (level l >= 1). Pseudocode lines FB.1-FB.21 and MP.1-MP.10

Line numbers refer to agents/agent-04/work/pseudocode.md v2, which is the single algorithm text.
Notation for one search, the inner run FB.6 from root x:
- U_x is its output set.
- N_x = Tlist (FB.9) is its touched set plus x. U_x is a subset of N_x.
- In the MERGE and NEW-TREE cases, N_x becomes tree vertices (FB.13, FB.16).
- In the FAIL case, N_x = U_x = W_x (FB.19; agent-04's note after FB.21).

**(3.0) Size of the touched set.** Every touch is a valid Relax from a vertex processed by the inner
run (SP; S1). There are two kinds of processed vertices: vertices placed in some inner U, which
relax at BM.19, BM.27 and BC.7, and vertices extracted by inner FindPivots-D (FD.7).
- Inner FindPivots-D in an inner call Y explores at most min(|U~_Y|, O(k'|S_Y|)) vertices.
- For partial Y this is O(k'|U_Y|/t'), by (B2) inside the inner run.
- So |N_x| <= 1 + delta * O( sum over inner calls Y of |U_Y| ) = O(delta (l_in + 1) |U_x|).
  It is also bounded by the inner work.
- The number of hits is at most the number of Relax calls, which is O(inner work). So recording the
  hit list and using only hitlist[0] at FB.12 costs O(inner work) (agent-06 M3).

**(3.1) Per-search cost.**
- cost(FB.5-FB.19 for root x) <= C_in c^B |U_x| + O(|N_x|) = O(c^B |U_x|).
  The (I3) bound covers the inner run. FB.10, FB.13 and FB.16 are linear in |N_x|, and so is the
  hit-list handling.
- Here c^B = c_in under suppression semantics, which is what pseudocode RX.4-RX.5 uses: sinks never
  enter inner structures, so U_x does not meet Z. Under the sink variant c^B = O(delta(l* log t' + t')),
  as discussed in Sec. 6. The sinks are charged per search, to their parents in that search's
  disjoint K_x (agent-09 R2).
- Skipped roots (FB.4) cost O(1).
- MakePivots and Partition cost O(|S| + sum |N_x|) = O(|S| + inner work).

**(3.2) Summation.** The N_x of MERGE and NEW-TREE searches are pairwise disjoint and disjoint from
earlier trees. FB.4 blocks roots already in trees, and suppressed relaxations never touch sinks, so a
touched vertex was not in Z [F3]. Also |U_x| <= 8k (I1), and FAIL searches have |U_x| < k. Hence

      sum over succ/merge x of |U_x| <= min( |union Fbar|, 8k |S| ),    |union Fbar| <= |U~(B,S)|,

      cost(FindPivots^B at X) <= C ( c^B min( |U~(B,S)|, 8k|S| ) + c^B k |Q_X| + |S| ).        (3.3)

- **Full X.** U~ = U_X [F5] and S is a subset of U, so the cost is at most C (c^B + 1) |U_X| + C c^B k |Q_X|.
- **Partial X.** |S| < |U_X|/t by (B2): with pseudocode FIX-L13 (3k <= t) the bound holds verbatim;
  with sigma_l = 4t^2 2^{lt} there is an extra factor 4. The cost is at most
  C (8 k c^B / t + 1) |U_X| + C c^B k |Q_X|.

**Parameter coupling.** Pseudocode Sec. 8.2 sets k := floor(t / (3 g(t))) with g(t) = Theta(c_in(k)),
so k c^B <= C_g t and t/k <= 3 g(t) + O(1). In both cases:

    cost(FindPivots^B at X) <= C' ( g |U_X| + t |Q_X| ).                                       (3.4)

This matches DMSY26's T1 = C'|U| log t + C't|Q| with log t replaced by g.

**Pivot count (MP.4-MP.8).** Every tree has at least k vertices. For new trees, |N_x| >= |U_x| >= k
(FB.15). Merges only enlarge trees. Lemma A.1 then yields edge-disjoint subtrees with at least k
vertices, hence at least k-1 edges, each. So #subtrees <= |union Fbar| / (k-1). Empty groups are
dropped (MP.8), so p <= min(|S|, #subtrees).
- Full X: p <= |U_X|/(k-1), so p t = O(g |U_X|).
- Partial X: p t <= t|S| < |U_X|.

---------------------------------------------------------------------------------------------------

## 4. Direct cost of one main call X, then global summation

**Direct cost of a non-base call X at level l.** Children are excluded. T-numbers are DMSY26's;
BM.x are the pseudocode lines.
- **T1** FindPivots^B (BM.4), P-membership pushes (BM.6) and pivot inserts (BM.7):
  C'(g |U| + t|Q_X|) + O(|S|) + O(p t) = O(g |U| + t |Q_X|).
- **T2** Picking (BM.11-BM.12) costs O(|Pl[j]|) = O(k) per pulled current pivot. BM.12 tests
  piv[j] = x, so stale pivot keys cost O(1).
  - If child Y_i is partial: O(k * #pulled pivots) <= O(k |S_{Y_i}|) <= O(k |U_{Y_i}|/t) <= O(|U_{Y_i}|).
  - If child Y_i is full: the pulled pivot lies in U_{Y_i} and is removed at BM.17. That triggers the
    re-selection at BM.23, which costs Omega(t) >= Omega(k) and pays for the picking. The exception is
    Pl[j] becoming empty, which happens at most once per j: O(kp) = O(|U|).
  - Total O(|U|).
- **T3** Pull (BM.10) costs O(|S_i|) = O(|U_i|): S_i is a subset of U_i for a full child, and
  |S_i| < 4|U_i|/t for a partial one. An unsettled pulled key can come back through the child's BM.25
  and the Merge and be pulled again later. The re-insertion is paid by the child's T6
  (O(t|S_Y|) = O(|U_Y|) for partial Y), and the re-pull by this bound (agent-03 review item 3).
  Also covered here: Merge (BM.14), the deletions (BM.15, BM.29; FIX-STALE, O(1) amortized each),
  the membership updates (BM.16-BM.18, BM.30), the scan of the out-edges of U_i and W' (BM.19, BM.27),
  and the base-case result check (BM.24a): O(delta |U| + |S|) = O(delta |U|).
- **T4, T7** Inserts at BM.21 and BM.28: one insertion event per edge, each O(t) by (B4), charged to the edge [F5].
- **T5** Re-selection at BM.23 costs O(|Pl[j]| + t) = O(t).
  - Partial X: at most sum_j |Pl[j]| <= |S| re-selections, so O(t|S|) = O(|U|) by (B2).
  - Full X: O(p t + t |E_X|) = O(g |U|) + O(t |E_X|). Here E_X = E(U_X) minus the union of E(U_i) is
    the set of cross edges, and each edge lies in E_X for at most one X (DMSY26 T5,full). This needs
    the tree edges to be edges of H with both ends in U_X [F3]. For merge edges (u,z) the endpoint z
    lies in an earlier tree, which is inside U~ = U_X.
- **T6** BM.25 costs O(t|S|). It is non-zero only for partial X, so it is O(|U|) by (B2).
- **Per-call overhead** O(1) <= O(|U|) [F7].

Direct cost:

    direct(X) <= C'' ( (g + delta) |U_X| + t |Q_X| + t |E_X| + t * #events(X) ).                 (4.1)

A base call costs O(delta log t |U_X|) (B6).

**Global facts** (using [F5], [F7], and the Q-argument below).
- **G1** For each layer l, the sum of |U_X| over calls X at layer l is at most N. There are L+1 layers.
- **G2** The sum over X of #events(X) is at most m. Each edge has at most one insertion event
  (BM.21, BM.28 or BC.7) in the whole run. This needs FIX-STALE; agent-03's experiment shows it fails
  without the fix. Relaxations inside inner searches are not
  events [F6].
- **G3** The sum over X of |E_X| is at most m.
- **G4 (Q-appearances).** The sum over all X of |Q_X| is at most N(delta + 1) + 4N L/t. This is the
  same as agent-10's I7 re-proof.
  - Partial X: |Q_X| <= |S_X| < 4|U_X|/t (B2). Summing over one layer gives at most 4N/t; over all
    layers, at most 4N L/t.
  - Full X: let Y_1, Y_2, ... be the full calls with v in Q_{Y_a}. Then v is in U_{Y_a}, so they form
    an ancestor chain [F5]. Take Y_a an ancestor of Y_{a+1}. After Y_a's FindPivots^B, v is not in
    P_{Y_a} and not in D_{Y_a}. For v to reach S_{Y_{a+1}}, it must first enter some D inside
    T(Y_a). Line 7, Line 33 and the picking at Line 13 (BM.12: v in P_j of some call Z in T(Y_a)
    implies v in S_Z) all need v in S of some call in T(Y_a) that started later (circular). A merge
    moves an entry already made in a child, and deletions (FIX-STALE) are not insertions. Line 33 of
    Y_a itself runs only after all of its descendants have returned (agent-03 review item 4). So the first entry is an insertion event on some in-edge (u', v)
    inside T(Y_a), after Y_a's FindPivots^B. The event that brought v into S_{Y_a} happened before
    Y_a started, so the events charged to different appearances are distinct.
  - Each in-edge has at most one event (G2), so there are at most indeg(v) + [v = s] <= delta + 1
    appearances. The inner searches do not change this argument [F6].
- **G5** Base calls: the sum of |U_X| over base calls is at most N (they are all on layer 0).

**Summing (4.1) over all calls:**

    T_main <= C'' [ (g + delta) (L+1) N  +  t (N(delta+1) + 4N L/t)  +  t m  +  t m ]  +  O(delta N log t)
           =  O( m t  +  N (log N / t) (g + delta)  +  N delta log t ).                             (4.2)

Here delta N = O(m) and L = O(log N / t). The global summation replaces DMSY26's per-call induction
(Lemma 3.9) and gives the same form. I checked that the two bookkeepings agree term by term.

---------------------------------------------------------------------------------------------------

## 5. Parameter choice, sparse case (m = O(n) after pruning; delta = 3, N = O(m))

Let G(x) := ceil( sqrt( log x * log log x ) ) for x >= 16. Choose

    t := ceil( (log N)^{1/2} * (log log N * log log log N)^{1/4} ),   g := C_g G(t),   k := ceil(t/g),   t' := G(k).

Checks:
- c_in(k) = O(G(k)) = O(G(t)) by (I4) and the monotonicity of G. So c_in(k) <= g for a suitable
  constant C_g.
- k c_in <= 2 C_g t, and t/k <= g.
- k >= t' because t/G(t) >> G(t) for large n. Lambda'_1 = poly(t') < k.
- k <= t.
- log t = (1/2 + o(1)) log log N, so g = Theta( sqrt( log log N * log log log N ) ).

By (4.2):

    T_main = O( m t + m (log N / t) g + m log t )
           = O( m (log n)^{1/2} (log log n * log log log n)^{1/4} ).                                   (5.1)

Here (log N / t) g = Theta( t ) by the choice of t, and m log t = O(m log log n) is lower order.

This beats the DMSY26 sparse bound O(m (log n)^{1/2} (log log n)^{1/2}) by a factor
Theta( (log log n / log log log n)^{1/4} ), which tends to infinity. The improvement is strict but
tiny in practice: for n = 2^64 the two leading factors, ignoring constants, are 15.9 vs 19.6.
That is only a sanity check. The claim is asymptotic.

**Asymptotic regime and the constant n_0 (agent-06 M1).** Correctness holds for every positive
parameter choice (pseudocode Sec. 8.2); only this time analysis needs the constraints below.
- The analysis needs t >= t_0, 2 <= k with 3k <= t, k >= t', and Lambda'_{l*-1} <= k.
  - For l* >= 2 the last constraint is the minimality of l*.
  - For l* = 1 it is t'^3 <= k. Then (I1) gives |U_x| <= k + t'^3 + k' <= 3k.
- t'^3 2^{t'} = k^{o(1)} and k -> infinity, so all constraints hold for N >= n_0, where n_0 is an
  absolute constant. Below n_0 the pseudocode's SS.7 runs binary-heap Dijkstra in O(n_0 log n_0) = O(1)
  time.
- With the literal formulas of pseudocode Sec. 8.2, a direct evaluation (script in agent-05's
  2026-09-20 session) gives:
  - the relaxed constraint set (t'^3 <= k, k >= t', 3k <= t) first holds at log2 N ~ 10^6;
  - the stronger Lambda'_1 < k (l* >= 2) first holds at log2 N ~ 10^13.
- So n_0 is astronomically large, and the improvement is **purely asymptotic** ("galactic"). This is
  typical for (log log n / log log log n)^{1/4} factors, and it must be stated honestly next to the
  theorem.

**Preprocessing and output.**
1. Prune the vertices unreachable from s by BFS in O(n + m). They get dist = inf and pred = nil.
2. Degree-reduce the reachable part (m_r >= n_r - 1) to delta = 3 in O(m): N <= n_r + 2 m_r.
3. Run the algorithm.
4. Map back. dist(v) = the len of the label of any vertex of the zero-weight cycle C_v. For pred(v),
   take the vertex e_v of C_v with the smallest (len, hops) label. Its canonical parent lies in some
   C_u, and we set pred(v) := u. The hops of e_. strictly decrease along pred, so pred is acyclic and
   rooted at s, and dis(u) + w(u,v) = dis(v). This is O(n + m) [F9].

**Total:** O( n + m (log n)^{1/2} (log log n log log log n)^{1/4} ). The n term only matters when
most vertices are isolated.

---------------------------------------------------------------------------------------------------

## 6. General m: where bootstrapping helps (CORRECTION to the peer formulas; depends on sink/suppression)

Degree-reduce to delta = Theta(min(m/n, log log n)) with N = O(m/delta), as in DMSY26. By (4.2),
T = O( m t + m (log n/t)(1 + f/delta) ) = O( m sqrt( log n (1 + f/delta) ) ), where f is the
per-vertex cost of the local search.
- **Dijkstra (DMSY26):** f_D = delta + log k, so f_D/delta = 1 + log k/delta.
- **Bootstrap, suppression semantics:** f = c_in = min over t' of [ (log k/t')(log t' + delta) + delta t' ]
  = Theta( sqrt( delta log k (delta + log log k) ) ), so f/delta = Theta( sqrt( log k (1 + log log k/delta) ) ).
- **Bootstrap, sink semantics:** f = c^B = Theta( delta min over t' of [ (log k/t') log t' + t' ] )
  = Theta( delta sqrt( log k log log k ) ), so f/delta = Theta( sqrt( log k log log k ) ).

The inner l*·delta term is real: the inner algorithm runs on the same degree-delta graph but has
log k' = Theta(LLL), so for delta >> LLL it violates DMSY26's side condition delta <= log k'.
Write LL = log log n and LLL = log log log n (log k = Theta(LL)).

**Suppression semantics.**
- delta <= LLL: T_B = O( m^{3/4} n^{1/4} (log n)^{1/2} (LL LLL)^{1/4} ).
- LLL <= delta: T_B = O( m (log n)^{1/2} LL^{1/4} ).
- This beats DMSY26 iff delta = o(sqrt(LL)).

**Sink semantics (the editor's choice, tracker I10).**
- For all delta: T_B = O( m (log n)^{1/2} (LL LLL)^{1/4} ), with no gain from larger delta.
- This beats DMSY26's m sqrt(log n (1 + LL/delta)) iff delta = o( sqrt(LL/LLL) ).

**Hybrid theorem** (choose the variant from m/n in O(1) time). With sink semantics:

    T(m,n) = O( n + m sqrt(log n) + min{ sqrt( m n log n LL ),  m sqrt(log n) (LL LLL)^{1/4} } ).

It is strictly better than DMSY26 exactly when m/n = o( sqrt(log log n / log log log n) ), which
includes all sparse graphs. With suppression semantics the second branch can be replaced by
m sqrt(log n) LL^{1/4} (1 + LLL n/m)^{1/4}, and the range widens to m/n = o(sqrt(LL)).

The agent-01/agent-10 formula O(m sqrt(log n) + min{ sqrt(mn log n LL), m^{3/4} n^{1/4} sqrt(log n)(LL LLL)^{1/4} })
takes f = sqrt(delta log k log log k) for all delta and drops the l*·delta term. Its m^{3/4} n^{1/4}
branch is valid only for delta <= LLL, and only under suppression semantics. The sparse claim
(delta = 3) is unaffected in every variant.

## 7. Iterated bootstrapping (fixed nesting depth D), with a rigorous depth-3 corollary

**Notation.** A_1 = DMSY26 BMSSP with FindPivots-D (Fibonacci heap). For j >= 1, A_{j+1} = BMSSP whose
FindPivots is FindPivots-B, and whose inner capped searches are runs of A_j. The main theorem uses
A_2 at the outer level ("depth 2": outer B, inner D). The corollary below uses A_3: outer B, inner B,
inner-inner D.

For a capped search of size K (top cap tau = K, top level l = min{ l >= 1 : Lambda_l >= K }) run by
A_j on a deadline instance with delta = O(1), let c_j(K) denote the cost per vertex of its output:
cost(run) <= c_j(K) |U_run|.

**Lemma M (per-vertex cost recursion).** For every fixed j >= 1 and K >= K_0(j):

    c_1(K) = O( sqrt( log K * log log K ) ),
    c_{j+1}(K) = O( t_j + (log K / t_j) * c_j(k_j) )   for any integers t_j, k_j with 3k_j <= t_j,
                 k_j c_j(k_j) <= C t_j, and the depth-j feasibility constraints of Sec. 5 (k_j >= t_{j+1},
                 Lambda^{(j)}_{l-1} <= k_j).

*Proof.* c_1 is (I3)-(I4). For c_{j+1}, apply the Sec. 4 global summation to one A_{j+1} run on its
deadline instance I_x (top call at level l_{j+1} ~ log K/t_j, cap K, output U_run):
- Direct per-call cost per vertex per layer: g_j + delta, where g_j := c_j(k_j) + t_j/k_j = O(c_j(k_j)).
  This is (3.4) with the inner searches of the A_{j+1} run being A_j runs of size k_j. S3 §S3.5 proves
  that FindPivots-B satisfies FP on deadline instances.
- Insertion events: at most delta |U_run|, each O(t_j) (Lemma G2 in I_x).
- Cross-edge charges: at most |E(U_run)| <= delta |U_run|, each O(t_j).
- Q-appearances: at most |U_run| (delta + 1 + 4 l_{j+1}/t_j) (G4 in I_x), each O(k_j c_j(k_j)) = O(t_j).
- Base calls: O(delta log t_j) per vertex.
Summing: cost <= C |U_run| ( (l_{j+1}+1)(g_j + delta) + delta t_j + t_j (delta + 1) + l_{j+1} + delta log t_j )
= O( |U_run| ( t_j + (log K/t_j) c_j(k_j) ) ). ∎

**Parameters for depth 3 (A_3 at the outer level; sparse, delta = 3).** Write LL = log log n,
LLL = log log log n, L4 = log log log log n.
- depth 2 (the inner algorithm A_2 on capped searches of size K):
  t_1 := ceil( (log K)^{1/2} (log log K * log log log K)^{1/4} ), k_1 := floor( t_1 / (3 G(t_1)) ).
  This gives c_2(K) = O( (log K)^{1/2} (log log K * log log log K)^{1/4} ), which is Sec. 5 run at scale K.
- depth 3 (outer):
  t_0 := ceil( sqrt( log n * c_2(t_0) ) ) = Theta( (log n)^{1/2} LL^{1/4} (LLL * L4)^{1/8} ),
  k_0 := floor( t_0 / (3 c_2(t_0)) ).
- Since log t_0 = (1/2 + o(1)) LL, we get c_2(t_0) = Theta( LL^{1/2} (LLL * L4)^{1/4} ).
- By (4.2) with g = c_2(k_0) = O(c_2(t_0)):

    T_3 = O( m t_0 + m (log n / t_0) c_2(t_0) ) = O( m (log n)^{1/2} (log log n)^{1/4} (log log log n)^{1/8} (log^{(4)} n)^{1/8} ).

This is o( m (log n)^{1/2} (LL LLL)^{1/4} ) by a factor (LLL/L4)^{1/8}, so it is also o(Kadria-Roditty's
undirected randomized bound). Via the standard reduction (each undirected edge becomes two arcs) it
gives a DETERMINISTIC undirected algorithm strictly faster than KR, conditional on the depth-3 proofs.

**What depth 3 needs beyond the main theorem.**
1. **Correctness.** FindPivots-B running inside inner instances. S1's depth induction (§D,
   multi-level) and S3 §S3.5 cover this; the formal reviewers must confirm §S3.5 explicitly.
2. **Time.** Lemma M. It uses (3.4), G2, G4 and (I1) on deadline instances. All are proved for general
   admissible instances (S2 Lemma S2.1, S3 FP7, Lemma G2), so no new argument is needed.
3. **Feasibility.** The depth-2 and depth-3 constraints hold only for N >= n_0^{(3)}, a larger but
   still absolute constant. Below it the algorithm falls back to depth 2, or to Dijkstra for tiny N.
4. **Implementation.** One array set per bootstrap depth (pseudocode Sec. 6, last note).

**General fixed depth D.** Induction with Lemma M gives

    c_D(K) = Theta_D( l_1^{1/2} l_2^{1/4} ... l_D^{1/2^D} * l_{D+1}^{1/2^D} ),   l_i = log^{(i)} K.

Check: D = 1 gives l_1^{1/2} l_2^{1/2}, and D = 2 gives l_1^{1/2} l_2^{1/4} l_3^{1/4}.
- The leading constants obey a_{j+1} = C sqrt(a_j), so they stay bounded by C^2 (agent-06).
- The thresholds n_0^{(D)} grow like a tower in D. So "depth log* n" is not claimed.
- The formal limit prod_i (log^{(i)} n)^{1/2^i} never beats sqrt(log n)(log log n)^{1/4}. Beating that
  floor needs a new local primitive (amortization_notes.md).

---------------------------------------------------------------------------------------------------

## 8. Space: O(n + m) words

- **Global:** the graph, the label array d[] (a 4-tuple per vertex), and the per-vertex record
  stacks described next.
- **Membership tables.** Lemma A.2's table from key to block node, and the "v in P_j" and "v in W"
  flags, are per call. A table of size N per active layer would cost O(N L) space, so instead each
  vertex keeps a stack of O(1)-size records. A record belongs to one active call and one role (D
  entry, P_j membership, W flag).
  - Stack discipline holds because a structure of call X is touched only while X is the deepest
    executing call. X's own lines run between its children. A child's records are converted
    (D_i merged into D_X: keep the smaller value, or relabel) or deleted before the child returns.
    Each conversion costs O(1) and the child's cleanup costs O(its own work).
  - Each vertex has O(1) records per active call. Trees F_j are only needed to build the P_j and are
    discarded afterwards. W is stored as a deduplicated list.
  - So the top of each stack is always accessible in O(1).
- **Active structures.** The active main calls form a root-to-current path, and the call at layer l
  stores O(|S_X| + delta |U_X| + |union Fbar| + |W|) = O(delta min(N, Lambda_l)) words.
  The sum over the path is at most delta (N + sum_{l < L} 3 Lambda_l) <= delta (N + 6 Lambda_{L-1})
  = O(delta N) = O(m), because Lambda_{L-1} < N and the Lambda_l grow geometrically.
  At most one inner search is active at a time. It is nested under the deepest main call's
  FindPivots^B and uses O(delta k) words plus its own geometric path. Inner Fibonacci heaps and base
  BSTs are O(k') and O(delta Lambda'_0).
- **Blocked flags** for the current FindPivots^B: one bit per vertex, cleared in O(|union Fbar|).
  Only one main FindPivots^B is active at any time.

- **Version counters (agent-06 M4).** ver[v] increases only on a strict decrease of d[v]. Each
  decrease is one Relax call, so every counter stays below the total running time, which is
  poly(n + m). Counters, edge ids and hop counts are therefore O(log n)-bit integers, i.e. ordinary
  word-RAM integers, and not weights.

Space total: **O(n + m)**.

---------------------------------------------------------------------------------------------------

## 9. Issues for the integrated document (from this independent pass)

1. **(Must fix) Size bookkeeping.** Use sigma_l = 3k t^2 2^{lt} and Lambda_l = c_1 t sigma_l, with
   thresholds Lambda_l at every level including the base, or an equivalent fix. State (B2) explicitly.
   It is used in FindPivots-partial, the Q-bound, Line 33 and T5,par.
2. **(Must state) Top cap of the inner search.** tau = k, l* = min{l >= 1 : Lambda'_l >= k}.
   Prove |U_x| <= 8k (I1) and k >= t' (needed for partial implies |U| > t'|S| at the top).
   Without |U_x| = O(k) the partial-call FindPivots bound (3.1) fails.
3. **(Must state) Inner cost needs F1 for the whole inner recursion tree.** The inner Lemma 3.9 or
   global summation uses inner Lemma 3.7/3.8 structure (U_i disjointness uses dis_J). The closure
   check R2 of agent-03 decouples correctness, but not time. The time bound still needs F1.
3b. **(Must state) x is in U_x, so |U_x| >= 1.** Otherwise the "+1 per search" overhead is not
   covered.
4. **(Correction) General-m formula.** See Sec. 6. The improvement holds only for m/n = o(sqrt(LL/LLL))
   under sink semantics, or o(sqrt(LL)) under suppression. The theorem statement must match the chosen
   semantics. Simplest option: state the sparse bound and "never worse than DMSY26".
5. **(Check) Q-bound (G4).** It relies on "inner relaxations are not insertion events" [F6] and on
   s being the only vertex with no in-edge event.
6. **(Check) T5,full.** Tree edges must be G-edges with both endpoints in U_X (full X). A merge edge
   (u,h) with h blocked is fine: h is in Fbar, which lies in U~ = U_X.
7. **(Space) Spell out per-vertex record stacks** (Sec. 8). DMSY26 does not discuss space, and a
   naive per-level table gives O(n log n / t).
8. **(Output)** Map back from the degree reduction, including pred via the minimum-(len,hops) entry
   vertex (Sec. 5), and handle unreachable vertices. Both are O(n + m).

## 10. Next (agent-05 stretch lane)

Beating (log log n)^{1/4} would need per-vertex-per-outer-level local-search cost o(sqrt(log k)).
Candidate: reuse a parent call's inner-search results (exact capped SSSP regions around frontier
vertices) in the children's FindPivots^B, amortizing with a potential equal to the number of distinct
outer levels at which a vertex is explored. I will write a separate note (amortization.md) if
something survives a first attack.

---------------------------------------------------------------------------------------------------

## 11. Empirical sanity checks of the S4 structural inequalities (finite tests, NOT a proof)

`s4check/s4_checks.py` wraps an unmodified snapshot of agent-08's bootstrapped prototype and checks
the facts this analysis relies on:
- I1: |U_x| <= 8k when l_in is minimal, and the general bound k + 6 Lambda'(l_in-1) + k_in otherwise.
- G4: per-vertex Q-appearances in full calls <= indeg + [v = s]; partial calls have sum |Q| <= sum |S|.
- PIV: p <= min(|S|, |union Fbar|/(k-1)).
- PART: partial implies |U| > Lambda(l).
- G1: each layer has sum |U_X| <= n.
- The ratio |N_x|/|U_x| is reported.

1200 randomized and adversarial trials (n up to 500) found **0 violations**. The max full-Q/indeg ratio
is exactly 1.00, so the G4 bound is attained. The max |U_x|/k with minimal l_in is 4.00.
Results and exact reproduction commands are in s4check/results.md.

---------------------------------------------------------------------------------------------------

## 12. Review log and resolutions (S4)

| review | item | resolution in v5 |
|---|---|---|
| agent-09 #1 (v3), CORRECT given F1-F9 | R1 empty S_i rule | (I3)(a): deletion variant gives nonempty Pulls; filter variant: skip, or an O(1) call charged to a discarded entry |
| | R2 per-search sink charging | Sec. 3 sink-variant bullet and (3.1): sinks charged per search to disjoint K_x |
| | R3-R5 checks | confirmed, no change (R3 wording added to (I1)) |
| | R6 theorem range vs semantics | final editor ruling is SUPPRESSION (07:37). MASTER §2's o(sqrt(log log n)) range is the suppression range, so it is consistent. The sink range o(sqrt(LL/LLL)) is kept only as a variant (Sec. 6) |
| agent-03 (3rd) (v3), CORRECT given F1-F9 | 1 l* >= 2 | (I1) restated, both cases |
| | 2 inner events only from inner-settled vertices | (I3)(b) |
| | 3 re-pulls of unsettled keys | Sec. 4 T3 |
| | 4 picking route in G4 | Sec. 4 G4 |
| | 5, 6 | confirmed |
| agent-06 #2 (v4), CORRECT given F1-F9 | M1 explicit n_0 | Sec. 5 "Asymptotic regime": n_0 absolute; literal Sec. 8.2 formulas give log2 N ~ 10^6 (relaxed) or ~10^13 (l* >= 2). The bound is purely asymptotic |
| | M2 fixed-depth wording | unchanged (Sec. 7 says fixed D; the theorem uses depth 2) |
| | M3 hit-list length | (3.0) |
| | M4 version-counter width | Sec. 8 |
| agent-03 pseudocode review | "tree-size bound with N-trees is O(t)|S| not 8k|S|" | v4 (3.2) bounds sum|U_x| <= 8k|S| (search outputs) and |union Fbar| only via inner work, so the bound is unaffected |

Status: S4 has two formal reviews (agent-09 #1, agent-06 #2) and a third review (agent-03). All say
CORRECT conditional on F1-F9, and all items are resolved above. **F1-F9 remain the obligations of
S1/S2/S3**, which are under separate review.

---------------------------------------------------------------------------------------------------

## 13. Discharge of F1-F9 (where each assumed fact is proved)

Read against S1 = agents/agent-02/work/L1_foundations.md v2.5, S2 = agents/agent-08/work/S2_core.md v1.1,
S3 = agents/agent-08/work/S3_findpivots.md v1.0, and S5/pseudocode = agents/agent-04/work/.

| fact | used for | proved in |
|---|---|---|
| F1 inner run = BMSSP on I_x, so core lemmas hold inside | (I1)-(I3) | S1 §C D1-D3 (suppression), S2 Cor. S2.3 with Lemma S2.1 (R1)-(R9) in I_x, S3 §S3.2.1. Inner edge-event uniqueness: Lemma G2 below applied in I_x |
| F2 x in U_x; partial implies \|U_x\| > k; full implies U_x = U~_J(B,{x}) | (I1), (3.0) | S3 (I-1)-(I-3), from S2 (R1), (R4) |
| F3 trees vertex-disjoint, >= k vertices, inside U~(B,S), edges of H | (3.2), pivot count, T5 | S3 FP4 (§S3.2.4) + S1 L3+ |
| F4 FAIL implies \|W_x\| < k; <W, union P_j> frontier | T1, G4 | S3 §S3.2.3 (failed-search exactness) + FP3 |
| F5 main-level structure (U = U~(B',S), disjoint U_i, per-layer disjointness, one insertion event per edge) | G1, G2, T4/T7 | S2 Lemma S2.1 (R1), (R3), (R4), (R8). Per-layer disjointness follows from (R8) by induction down the call tree. Event uniqueness is Lemma G2 below; S2 §S2.5 item 5 states it for BM.20 only |
| F6 inner runs never touch outer D's | G2, G4 | S2 (R9) + S3 FP6 |
| F7 \|U\| >= 1; full implies S ⊆ U; partial implies \|U\| > Lambda_l | call counting, (B2), (B3) | S2 Step 5 ("every iteration has U_i ≠ ∅"), (R1) with (C3), (R4) |
| F8 P_j ⊆ F_j, \|F_j\| < 3k, P_j disjoint and nonempty, Q ∪ (union P_j) = S | (B1), T2, T5 | S3 FP2, FP4 |
| F9 output map-back | Sec. 5 output | pseudocode §8.3 + S5 (agent-04), reviewed by agent-09 |

**Lemma G2 (insertion-event uniqueness; the extension of Obs. 3.5 needed by S4).** In any run of the
corrected core on an admissible instance, every edge e = (u, v) takes part in at most one *insertion
event*. An insertion event is a Relax(u, e, ·) returning True that is followed by a D.Insert of v, and it
can only happen at BM.20-21, BM.27-28 or BC.7.

*Proof.* A vertex u relaxes its out-edges at those lines only when it belongs to the U of the call
executing them:
- u is in U_i of a child at BM.19;
- u is in W' at BM.27;
- u is extracted at BC.6.

By (R8), applied recursively, the calls whose U contains u form a chain X_0 ⊃ X_1 ⊃ … ⊃ X_q, one call
per layer. At each of these events u is complete: by (R1) of the child at BM.19, by S2 Step 5 at BM.27,
and by (K4) at BC.6. So d[u] = dis(u) is the same value at all of them, and the candidate
c := d[u] ⊕ e is fixed. The events that are possible for u:
- BM.20 in X_j (j < q), with u ∈ U_{X_{j+1}}, needs c in [B_{X_{j+1}}, B_{X_j}).
- BM.28 in X_q (u ∈ W'_{X_q}) needs c in [B'_{X_q}, B_{X_q}).
- BC.7 in a base call X_q needs c ≺ B_{X_q}.

A vertex is in W' only at the last call of its chain, and base calls have no children, so at most one
of the last two applies, and only at X_q. The bounds satisfy B_{X_q} ⪯ B_{X_{q-1}} ⪯ … ⪯ B_{X_0}, so the
intervals are pairwise disjoint and c lies in at most one of them. Hence e has at most one insertion
event. This holds whether the Relax is a strict decrease or a re-confirmation (RX.7), since the
argument uses only the interval test. Relaxations inside FindPivots-B inner runs belong to a different
instance and insert only into that instance's private D's (F6), so they are not events of the host
instance. ∎

**Status.** Every fact S4 assumes is proved in S1/S2/S3/S5, which are under formal review, or in
Lemma G2 above. S4 itself is reviewed (Sec. 12). The remaining dependency for G8/G10 is the final
formal acceptance of S1/S2/S3.


## Appendix X1 — Independent proof of the corrected-core invariants (agent-02)

Frozen label `XR6`, source `/research/agents/agent-02/work/R6_core_invariants.md`, sha256 `9a3e28f74bdd788078492fab50923df7b4319484774802d1df841549cbc1d62e`, frozen 2026-09-20T07:51:13Z.

# R6: corrected-core loop invariants with STORED values — independent proof (agent-02)

v1, 2026-09-20. Purpose: an independent cross-check, for agent-08's S2 and the formal reviewers, of the
obligation R6 (agent-09) = S1 Sec. F items (1')–(3'). Line numbers refer to agent-04's
pseudocode.md v2 (BM.x = main recursion, FIX-STALE by deletion at BM.15/BM.29, FIX-EMPTY at BM.24a).
Semantics: S1 v2.4 (version-stamped walk order; all notions w.r.t. one admissible instance I).
Status: written proof, NOT reviewed.

## 0. Setting and notation
Call X = BMSSP(B, S, l) (l >= 1) on instance I. Ũ := Ũ(B, S). FindPivots (BM.4) returns Pl[1..p], Q, W
satisfying the master's FP interface. Let P_ini := ∪_j Pl[j] at BM.4 and Ũ_P := Ũ(B, P_ini). Over time
Pl[j] shrinks (BM.17). P := ∪_j Pl[j] (current). For a key y of D, val(y) is its STORED value; always
val(y) ⪰ d[y] (stored values are old labels; labels only decrease).
- D^acc := { y ∈ keys(D) : y complete and val(y) = d[y] } (then val(y) = dis(y) forever, since a
  complete label never changes).
- P̂_j := { y ∈ Pl[j] : path(y) contains no vertex of D^acc } (y itself included in path(y)).
- "Complete z covers v" means z lies on path(v).

Preconditions of X: (Pre1) ⟨∅, S⟩ is a frontier for Ũ; (Pre2) Claim C (S1 Sec. D); (Pre3) d[x] ≺ B
for x ∈ S; |S| within the size bound (FIX-SIZE).
Postconditions to prove (the corrected Lemma 3.7'): at return (B', U_ret := U ∪ W', D):
- (Q1) U_ret = Ũ(B', S), every vertex of it complete, B' ⪯ B.
- (Q2) accurate frontier: every v ∈ Ũ \ U_ret has a complete vertex of D^acc on path(v).
- (Q3) keys(D) ∩ U_ret = ∅; every key has B' ⪯ val ≺ B.
- (Q4) every x ∈ S \ U_ret is a key of D with val(x) = d[x] (at return).
- (Q5) full: D = ∅ and B' = B; partial (D ≠ ∅): |U| > τ and B' ≺ B.
The sub-calls satisfy Q1–Q5 by induction on l (the base case BC is plain Dijkstra on its own BST
with val = label for every key, see agent-04 Sec. 4 note, plus FIX-BASE; its Q1–Q5 are direct).

Two facts from FindPivots/S1 used repeatedly:
- (F-a) [FP1 + FP3] If v ∈ Ũ and path(v) contains no vertex of P_ini, then v ∈ W and v is complete
  (from the end of FindPivots on).
- (F-b) [S1 Obs. 2.1(4)' argument] For every v ∈ Ũ_P, path(v) contains a vertex of P_ini that is
  complete at the end of FindPivots. (Let y_1 be the first P_ini-vertex on path(v). If y_1 were
  incomplete, Pre1 gives a complete y' ∈ S on path(y_1) before y_1; y' ∉ P_ini by the choice of y_1,
  so y' ∈ Q, and failed-search exactness completes Ũ(B, {y'}) ∋ y_1 — contradiction.)

## 1. Confinement of the loop structures
**Lemma C0.** Throughout the loop: keys(D) ⊆ Ũ_P, P ⊆ Ũ_P, and U ⊆ Ũ_P.
*Proof.* P_ini ⊆ Ũ_P (x ∈ P_ini has dis(x) ⪯ d[x] ≺ B and x ∈ path(x)). Initial keys are pivots ⊆ P.
Inductively: S_i ⊆ keys(D) ∪ P ⊆ Ũ_P; U_i = Ũ(B'_i, S_i) (Q1 of the sub-call) and every vertex whose
path visits S_i ⊆ Ũ_P visits P_ini, so U_i ⊆ Ũ_P; keys(D_i) ⊆ Ũ(B_i, S_i) ⊆ Ũ_P (L3+ for the sub-call:
keys are S_i-vertices or touched in it). BM.21: y validly relaxed from u ∈ U_i with cand ⪰ B_i; y ∈ Ũ
by L3+ (X). If y ∉ Ũ_P, then by (F-a) y was complete since FindPivots, so validity forces
cand = d[y] = dis(y), i.e. u = p*(y) (S1 A1), and path(y) = path(u)∘e visits P_ini as u ∈ Ũ_P —
contradiction. BM.23 inserts vertices of P. ∎

## 2. Loop invariants
At the start of iteration i (U = U_1 ∪ … ∪ U_{i-1}, current bound B'_{i-1}; B'_0 from BM.8):
- (J1) U = { v ∈ Ũ_P : dis(v) ≺ B'_{i-1} }, all complete.
- (J2) Every v ∈ Ũ_P \ U has a complete vertex of D^acc ∪ P̂ on path(v).
- (J3) For every nonempty Pl[j]: piv[j] ∈ keys(D), and val(piv[j]) ⪯ dis(y) for every COMPLETE y ∈ P̂_j.
- (J4) keys(D) ∩ U = ∅ and P ∩ U = ∅; every key has B'_{i-1} ⪯ val ≺ B.

**Initialization (after BM.8).** U = ∅, keys = pivots, val(piv[j]) = d[piv[j]] = min_{Pl[j]} d.
(J1): for v ∈ Ũ_P, (F-b) gives a complete y ∈ P_ini on path(v), so dis(v) ⪰ dis(y) = d[y] ⪰
d[piv[j(y)]] ⪰ B'_0. (J2): the same y is in P̂ or path(y) contains a vertex of D^acc. (J3), (J4): direct.

**Claim P (what Pull + expansion collect).** In iteration i, S_i ⊇ { z complete : z ∈ D^acc ∪ P̂,
dis(z) ≺ B_i }, and ⟨∅, S_i⟩ is a frontier for Ũ(B_i, S_i); every x ∈ S_i has d[x] ≺ B_i and
dis(x) ⪰ B'_{i-1}.
*Proof.* Pull (BM.10) returns exactly the keys with val ≺ B_i: values of distinct keys are distinct
labels (different vertices), so the M smallest are those below the (M+1)-st, which is B_i (or B_i = B
when all keys are pulled). A complete z ∈ D^acc with dis(z) ≺ B_i has val(z) = dis(z) ≺ B_i. A complete
z ∈ P̂_j with dis(z) ≺ B_i has val(piv[j]) ⪯ dis(z) ≺ B_i by (J3), so piv[j] is pulled and BM.12 adds
z (d[z] = dis(z) ≺ B_i; BM.12 tests the current pivot, and piv[j] is current by (J3)).
Frontier: let v ∈ Ũ(B_i, S_i) with y ∈ S_i on path(v), y incomplete. y ∈ Ũ_P \ U (C0, J4), so (J2)
gives a complete z ∈ D^acc ∪ P̂ on path(y) ⊆ path(v) with dis(z) ⪯ dis(v) ≺ B_i, hence z ∈ S_i.
d[x] ≺ B_i: pulled keys have d[x] ⪯ val(x) ≺ B_i; BM.12 adds only d[v] ≺ B_i. dis(x) ⪰ B'_{i-1}: x ∈ Ũ_P \ U
and (J1). Together with S1's Claim C for the sub-call and FIX-SIZE, the sub-call's preconditions hold. ∎

**Preservation through iteration i (BM.10–BM.24).** Write U⁺ := U ∪ U_i.
(0) U_i ≠ ∅ (full: the label-minimum of S_i is complete (Obs. 2.1(2)) with dis ≺ B_i = B'_i; partial:
|U_i| > τ >= 1), and every vertex of U_i has dis ⪰ B'_{i-1} (it descends from an S_i-vertex). So
B'_i ≻ max dis(U_i) ⪰ B'_{i-1}, and U_i ∩ U = ∅.

(J1) ⊆: U_i ⊆ Ũ_P (C0), complete, dis ≺ B'_i. ⊇: let v ∈ Ũ_P \ U with dis(v) ≺ B'_i. By (J2) a complete
z ∈ D^acc ∪ P̂ lies on path(v), dis(z) ⪯ dis(v) ≺ B'_i ⪯ B_i, so z ∈ S_i by Claim P, and
v ∈ Ũ(B'_i, S_i) = U_i.

(J4) Keys after the iteration: unpulled old keys (val ⪰ B_i ⪰ B'_i), keys of D_i (val ⪰ B'_i by Q3 of
the sub-call), BM.21 keys (val = cand ⪰ B_i), BM.23 pivots (val = d[piv] ⪰ dis(piv) ⪰ B'_i by (J1) as
piv ∈ P ⊆ Ũ_P \ U⁺); Merge keeps the smaller of two values, both ⪰ B'_i. All are ≺ B (Relax bound B;
pivots are S-vertices). U_i is deleted at BM.15 after the Merge. BM.21/BM.23 cannot re-insert a vertex of
U⁺: such a vertex is complete with dis ≺ B'_i ⪯ B_i ⪯ cand, so the Relax at BM.20 is invalid; BM.23
picks from Pl[j] after BM.17 removed U_i (and U ∩ P = ∅ before). P ∩ U⁺ = ∅ by BM.17.

(J3) Let Pl[j] be nonempty after the iteration.
- If j ∈ J: BM.23 sets val(piv[j]) = d[piv[j]] = min_{Pl[j]} d ⪯ dis(y) for every complete y ∈ Pl[j].
- Otherwise piv[j] was not in U_i, and piv[j] ∈ keys(D) after the iteration: if it was pulled it lies
  in S_i \ U_i and is a key of D_i with val = d[piv[j]] (Q4 of the sub-call), merged; if not pulled
  its entry stayed (not deleted, since piv[j] ∉ U_i); if BM.22 replaced it by v, v was just inserted at
  BM.21. In all cases val_new(piv[j]) ⪯ val_old(piv[j]), and val_new(piv[j]) = d[v] ≺ d[old piv] ⪯
  val_old in the replacement case.
  Now let y ∈ P̂_j (new) be complete. Case analysis on d[y] during iteration i:
  (a) d[y] changed inside sub-call i: y ∈ Ũ_i := Ũ(B_i, S_i) (L3+ for the sub-call). y ∉ U_i (still in
      Pl[j]), so by Q2 of the sub-call a complete vertex of D_i^acc lies on path(y); after Merge it is
      a key of D with the same accurate value (the old stored value of the same key is ⪰ its label), and
      it is not deleted at BM.15 (not in U_i). So path(y) meets D^acc: y ∉ P̂_j — contradiction.
  (b) d[y] changed at BM.20 with cand ⪰ B_i: then BM.21 inserted y with val = d[y]; y complete, so
      y ∈ D^acc and y ∉ P̂_j — contradiction. (If cand ≺ B_i the Relax at BM.20 changes d[y] only if
      cand ≺ d[y]; then y ∈ Ũ_i and dis(y) ⪯ cand ≺ B_i. If y ∈ U_i it is not in Pl[j]; otherwise
      Q2 of the sub-call applies as in (a).)
  (c) d[y] unchanged during iteration i: y was complete before. We show y ∈ P̂_j (old): otherwise a
      vertex z ∈ D^acc (old) lay on path(y). If z stayed a key (not pulled; not in U_i), it is still in
      D^acc. If z was pulled and z ∉ U_i, it is re-inserted accurately via Q4 of the sub-call. If
      z ∈ U_i, let a be the last vertex of path(y) in U⁺ and b its successor (b exists, since y ∉ U⁺);
      by the exit-edge lemma below, b ∈ D^acc (new). In every case path(y) meets D^acc (new) —
      contradiction. So y ∈ P̂_j (old) and (J3 old) gives val_old(piv[j]) ⪯ dis(y), hence
      val_new(piv[j]) ⪯ dis(y).

**Exit-edge lemma (E).** After iteration i: if a ∈ U⁺, b ∉ U⁺, a = p*(b) and dis(b) ≺ B, then
b ∈ D^acc.
*Proof.* a ∈ U_{i'} for some i' <= i. At BM.19 of iteration i' the edge (a, b) was relaxed from the
complete a with bound B: valid by S1 A4, and b became complete. If dis(b) ⪰ B_{i'}, BM.21 inserted b
with val = dis(b). If dis(b) ≺ B_{i'}: b ∈ Ũ_{i'} (path(b) = path(a)∘(a,b) visits S_{i'}), b ∉ U_{i'},
so by Q2 of sub-call i' some complete z ∈ D_{i'}^acc lies on path(b). Every vertex c of path(b) before
b has dis(c) ⪯ dis(a) ≺ B'_{i'}, whereas keys of D_{i'} have val ⪰ B'_{i'} (Q3), and an accurate key has
val = dis. So z = b, and Merge makes b an accurate key of D. Afterwards b stays in D^acc: it is never
deleted (b ∉ U⁺, and BM.15 deletes only vertices of U), and whenever it is pulled in a later iteration
and not completed, Q4 of that sub-call re-inserts it with val = d[b] = dis(b). ∎

(J2) Let v ∈ Ũ_P \ U⁺. By (J2 old) a complete z ∈ D^acc ∪ P̂ lies on path(v), and z ∉ U (J4).
- z ∈ D^acc, z not pulled and z ∉ U_i: still in D^acc.
- z ∈ D^acc pulled, z ∉ U_i: re-inserted accurately (Q4).
- z ∈ P̂_j, z ∉ U_i: z ∈ Pl[j] still; either z ∈ P̂_j (new), or path(z) ⊆ path(v) meets D^acc (new).
- z ∈ U_i: let a be the last vertex of path(v) in U⁺ and b its successor (v ∉ U⁺). Then b ∈ D^acc by
  (E) (dis(b) ⪯ dis(v) ≺ B), and b lies on path(v).

## 3. After the loop (BM.24a–BM.31)
Let B' be the final bound (FIX-EMPTY: B' := B if D is empty).
- If the loop ended with D empty: by (J3) every nonempty Pl[j] has piv[j] ∈ keys(D), so P = ∅, and
  by (J2) Ũ_P ⊆ U. Hence (J1) holds with B' = B as well.
- W' := { x ∈ W \ U : d[x] ≺ B' } is complete and disjoint from Ũ_P: x ∈ Ũ_P would give dis(x) ⪯ d[x]
  ≺ B', so x ∈ U by (J1); hence path(x) avoids P_ini and (F-a) makes x complete.
- (Q1) U ∪ W' = Ũ(B', S): "⊆" by (J1) and W' ⊆ Ũ with dis ⪯ d ≺ B'. "⊇": v ∈ Ũ with dis(v) ≺ B'
  is in U if v ∈ Ũ_P; otherwise it is complete by (F-a), so d[v] = dis(v) ≺ B' and v ∈ W'.
- (Q3), (Q4): BM.25 inserts every x ∈ S \ (U ∪ W') with its current label (such x has
  d[x] ⪰ dis(x) ⪰ B', since x ∉ Ũ(B', S), and d[x] ≺ B). BM.28 inserts only cand ⪰ B', never a vertex of
  U ∪ W' (those are complete with dis ≺ B' ⪯ cand, so the Relax is invalid). BM.29 deletes W'.
  Loop keys already satisfy (J4).
- (Q2) Let v ∈ Ũ \ (U ∪ W').
  - If v ∈ Ũ_P: (J2) gives a complete z ∈ D^acc ∪ P̂ on path(v). If z ∈ D^acc it stays there (BM.29
    deletes only W' ∌ z, since W' ∩ Ũ_P = ∅; insertions only lower values). If z ∈ P̂: z ∈ S,
    z complete with dis(z) ⪰ B' (z ∉ U), so BM.25 inserts it accurately.
  - If v ∉ Ũ_P: path(v) avoids P_ini. If path(v) ∩ (U ∪ W') = ∅, Pre1 gives a complete y ∈ S on
    path(v); y ∈ Q ⊆ W (FP3). As y ∉ W', d[y] = dis(y) ⪰ B', so BM.25 inserts y accurately. Otherwise
    let a be the last vertex of path(v) in U ∪ W' and b its successor. a ∉ U, since otherwise path(b)
    would visit P_ini (C0), so a ∈ W'. BM.27–28 relax (a, b) validly (A4; dis(b) ⪯ dis(v) ≺ B), making b
    complete with cand = dis(b) ⪰ B' (b ∉ Ũ(B', S)), so b is inserted accurately.
- (Q5) If the loop ended with D empty, then B' = B and BM.25/BM.28 insert nothing (no value lies in
  [B, B)), so D = ∅. If the loop ended because |U| > τ with D ≠ ∅, then B' = B'_f ≺ B: B'_f = B would
  need B_f = B (all keys pulled in the last iteration), after which only values in [B_f, B) = ∅ could
  be inserted, so D would be empty.

## 4. Remarks
- Nothing here uses ancestor closure (A2'). It uses A1, A3 and A4, L3+/Claim C (S1), FP1–FP6, and
  sub-call Q1–Q5. So it holds under both tie semantics.
- (J3) is weaker than DMSY26's "d[p_j] ⪯ d_B[P̂_j]" in two ways: it uses the STORED value of the pivot,
  and it constrains only COMPLETE members of P̂_j. BM.22 compares CURRENT labels. That is harmless,
  because a vertex relaxed at BM.20 with cand ⪰ B_i is inserted with its current label, so if it is
  complete it leaves P̂_j (case (b)).
- The exit-edge lemma (E) is where Relax's non-strict ⪯ matters. A4 re-validates b even if a
  FindPivots search had already lowered d[b] to dis(b), so b is (re-)inserted at BM.21 with an
  accurate stored value.
- Time analysis needs, from here: U_i pairwise disjoint (step (0)); each edge enters BM.21/BM.28 at most
  once (Obs. 3.5; now valid because U_i are disjoint and every vertex's calls form a chain); keys(D)
  never contain completed vertices (J4), so no re-processing.


## Appendix X2 — Editor independent check of S2 (agent-10)

Frozen label `XedS2`, source `/research/agents/agent-10/work/editor_check_S2.md`, sha256 `689235f73289fca8e307cabb4994ade4b8610599ebe6adbe765ec67fae497ba7`, frozen 2026-09-20T07:51:13Z.

# Editor's independent check of the corrected BMSSP core (S2), FIX-STALE by deletion (agent-10)

Purpose: an independent proof sketch of the corrected Lemma 3.7' to check agent-08's S2 against. It finds one issue: agent-02's pivot invariant (3') is not maintained by the literal Line 26. A weaker invariant (J4') fixes this, and no code change is needed.

Labels: S1 v2 full walk order. The instance is admissible. X = BMSSP(B,S,l) with l ≥ 1. Preconditions: Claim C, ⟨∅,S⟩ is a frontier for Ũ := Ũ(B,S), d[x] ≺ B on S, and FP for FindPivots.

## Corrected loop (line numbers local to this note)
```
 4 for j: p_j ← argmin_{P_j} d; D.Insert(p_j, d[p_j])
 5 B'_0 ← min(B, min_j d[p_j]); U ← ∅
 6 while |U| ≤ Λ_l and D ≠ ∅:
 7   (S_i, B_i) ← D.Pull()                      # keys with the smallest STORED values; remaining stored ⪰ B_i
 8   for pulled x = p_j: S_i ← S_i ∪ {v ∈ P_j : d[v] ≺ B_i}
 9   (B'_i, U_i, D_i) ← BMSSP(B_i, S_i, l−1)
10   D.Merge(D_i)
11   delete U_i from D                           # FIX-STALE
12   remove U_i from the P_j; J ← {j : p_j ∈ U_i, P_j ≠ ∅}
13   for u ∈ U_i, (u,v): if Relax(u,v,B) and d[u]⊕e ⪰ B_i: D.Insert(v,d[v]); [optional pivot update, see (J4')]
14   for j ∈ J: p_j ← argmin_{P_j} d; D.Insert(p_j, d[p_j])
15   B' ← B'_i; U ← U ∪ U_i
16 if D = ∅: B' ← B                              # FIX-EMPTY
17 insert every x ∈ S with d[x] ∈ [B',B)
18 W' ← {x ∈ W \ U : d[x] ≺ B'}; relax the out-edges of W', inserting those with value ⪰ B'
19 delete W' from D; U ← U ∪ W'                   # FIX-STALE
```
Notation: val(y) = the stored value of key y; always val(y) ⪰ d[y]. D^acc = {keys y : y complete and val(y) = d[y]}. Ũ_P := Ũ(B, P_ini). P̂ := {v ∈ P : path(v) visits no vertex of D^acc}.

## Sub-call guarantee (the strengthened Lemma 3.7' that the induction carries)
- (R1) U complete, U = Ũ(B',S), max dis(U) ≺ B'.
- (R2) ⟨U, D^acc⟩ is a frontier for Ũ(B,S).
- (R3) Every stored value in D is ⪰ B'; keys(D) ∩ U = ∅; keys(D) ⊆ Ũ(B,S).
- (R4) B' = B ⇒ D = ∅ and U = Ũ. B' ≺ B ⇒ |U| > Λ_l.

The base case with FIX-BASE satisfies R1–R4 by the Dijkstra argument. Base-case keys are never stale: no sub-calls or FindPivots run inside it, and every label decrease re-inserts.

## Loop invariants at the start of iteration i
- (J1) ⟨U, D^acc ∪ P̂⟩ is a frontier for Ũ_P. This is equivalent to the same statement with P in place of P̂.
- (J2) keys(D) ∩ U = ∅ = P ∩ U.
- (J3) Every y ∈ (keys(D) ∪ P) \ U has dis(y) ⪰ B'_{i-1}. These are true distances; since stored ⪰ d ⪰ dis, stored values also satisfy this.
- (J4') For every v ∈ P̂: **(a)** v ∈ keys(D) with val(v) = d[v], **or (b)** the pivot p_j of v's set has val(p_j) ⪯ d[v].
- (J5) Ũ_P ∩ {dis ≺ B'_{i-1}} ⊆ U.
- (J6) keys(D) ∪ P ⊆ Ũ_P.

**Initialization.** (J4')(b) holds because p_j = argmin and it was inserted with its label. (J5) at i = 1: suppose v ∈ Ũ_P with dis(v) ≺ B'_0, and let p ∈ P_ini lie on path(v).
- If p is complete: dis(p) ⪯ dis(v) ≺ B'_0 ⪯ d[p] = dis(p), a contradiction.
- If p is incomplete: FP1 gives a complete z ∈ P_ini on path(p) ⊆ path(v), and the same contradiction follows.

So Ũ_P ∩ {dis ≺ B'_0} = ∅.

**Sub-call precondition** (Lemma 3.6 with Y = D^acc ∪ P̂, target Ũ_P). Every accurate key with d ≺ B_i has stored = d ≺ B_i, so it is pulled. Every v ∈ P̂ with d[v] ≺ B_i is pulled directly via (a), or its pivot is pulled via (b) and Line 8 picks v. Also S_i ⊆ Ũ_P by (J6). So ⟨∅,S_i⟩ is a frontier for Ũ(B_i,S_i).

**(J5) maintained.** Take y ∈ Ũ_P \ U with dis(y) ≺ B'_i. By (J1), path(y) visits a complete z ∈ D^acc ∪ P̂ with dis(z) ≺ B_i. Then z ∈ S_i, as in the precondition argument. So y ∈ Ũ(B'_i,S_i) = U_i by R1 of the child.

**(J3) maintained.** Use (J6) and (J5). A key or P-vertex outside U with dis ≺ B'_i would lie in Ũ_P ∩ {dis ≺ B'_i} ⊆ U ∪ U_i, contradicting (J2).

**(J2) maintained.**
- Line 11 deletes U_i.
- Line 13 cannot insert a U-vertex. For u' ∈ U_{i'} with i' ≤ i we have d[u'] = dis(u') ≺ B'_{i'} ⪯ B_i ⪯ cand, so the relaxation is invalid.
- D_i ∩ U = ∅. D_i ∩ U_i = ∅ holds by the child's R3. A key of D_i has dis ⪰ B'_{i-1} (child R1/R3 with (J3) on S_i), while U_{i'} has dis ≺ B'_{i-1}.
- Line 14 inserts P-vertices, and P ∩ U = ∅ after Line 12.

**(J1) maintained.** This follows the Sec. 2.5 framework with accurate entries. Let v ∈ Ũ_P \ (U ∪ U_i). The old (J1) gives a complete z ∈ D^acc ∪ P̂ on path(v).
- If z is not pulled or picked: it keeps val(z) = dis(z), because complete labels never change and stored values only decrease toward d. It is not deleted, since dis(z) ⪰ B_i ≻ dis(U_i). So z is still accurate, or z ∈ P with P̂-membership lost only because an accurate key appeared on path(z) ⊆ path(v).
- If z ∈ S_i and dis(v) ≺ B_i: v ∈ Ũ_i, so R2 of the child gives an accurate key of D_i on path(v). It stays accurate after Merge (Merge keeps the minimum, and the minimum is dis) and is not deleted (∉ U_i).
- If z ∈ S_i and dis(v) ⪰ B_i: let y be the first vertex of path(v) after z that is not in U ∪ U_i. Its canonical parent x is in U_i, because a vertex after z ∈ S_i on the path cannot lie in an earlier U_{i'}, whose dis ≺ B'_{i-1}.
  - If dis(y) ≺ B_i: y ∈ Ũ_i \ U_i, which is covered by R2 of the child.
  - Otherwise Line 13 relaxes (x,y) with cand = dis(y) ⪰ B_i, which is valid by S1 A4, and inserts y with val = dis(y). So y is accurate.
  - If z ∈ S_i \ U_i itself, R2 of the child covers z.

**(J4') maintained.** Take v ∈ P̂ after iteration i.
- **Label of v unchanged in iteration i.**
  - (a) v was a key. If v was pulled: v ∈ U_i (so v ∉ P now), or v ∈ S_i \ U_i, which the child re-inserts with its current label (child R2 plus its Line 17). Merge then keeps val(v) ⪯ d[v], so val(v) = d[v]. If v was not pulled, its entry is untouched.
  - (b) The pivot p_j was used.
    - If p_j was pulled and p_j ∈ U_i: re-selection at Line 14 gives val(new p_j) = d[new p_j] ⪯ d[v].
    - If p_j was pulled and p_j ∉ U_i: the child returns p_j in D_i with value d[p_j] ⪯ the old val(p_j), and Merge keeps the minimum, which is ⪯ d[v].
    - If p_j was not pulled: its entry is untouched.
- **Label of v decreased inside the sub-call.** By S1 L3+, v ∈ Ũ_i. Then v ∈ U_i (so v ∉ P), or path(v) visits an accurate key of D_i (so v ∉ P̂). The condition holds vacuously.
- **Label of v decreased at Line 13.** v is inserted with val(v) = d[v], so (a) holds.

**Why (J4') and not agent-02's (3') "val(p_j) ⪯ d_B[P̂_j]".** DMSY26 Line 26 updates p_j ← v only if d[p_j] ≻ d[v], which compares the pivot's CURRENT label. Suppose sub-call i lowered d[p_j] without re-inserting p_j, so p_j ∉ U_i ∪ D_i. This happens for "two-hop" vertices of partial sub-calls, or labels set by the child's FindPivots. Then v ∈ P̂_j relaxed at Line 24 with d[p_j] ⪯ d[v] ≺ val(p_j) triggers no update, and (3') fails. (J4') covers v through its own fresh key.

**Consequence.** With (J4'), the Line-26 pivot update is not needed for correctness. It can stay as a harmless optimization. If S2 wants to keep (3'), Line 26 must compare against val(p_j), the stored value. Either way the pseudocode and the proof must agree.

**(J6) maintained.** Keys come from four sources:
- pivots, which are in P;
- Line 13, where v is validly relaxed from u ∈ U_i ⊆ Ũ_P, so v ∈ Ũ by S1 L3+;
- Line 14, which inserts P-vertices;
- Merge with D_i ⊆ Ũ(B_i,S_i) ⊆ Ũ_P, because S_i ⊆ Ũ_P.

Now suppose v ∈ Ũ \ Ũ_P and v is validly relaxed. The complete S-vertex on path(v) is some q ∈ Q, so v ∈ W and v is complete. A valid relaxation into a complete vertex is an equality relaxation from p*(v), and p*(v) = u ∈ U_i ⊆ Ũ_P, so v ∈ Ũ_P.

## End of the call
**W' complete.** Take v ∈ W' incomplete. FP1 says path(v) visits a complete vertex of P_ini, so v ∈ Ũ_P. (J1) with (J3) gives dis(v) ⪰ B'. But d[v] ≺ B' ⪯ dis(v) ⪯ d[v], a contradiction. Under FIX-EMPTY, D = ∅ forces P = ∅: an empty D means every pivot entry is gone, and each nonempty P_j keeps a pivot entry, either in D or in S_i and hence returned in D_i. So Ũ_P ⊆ U.

**R1.** U ∪ W' = Ũ(B',S) by (J5) and FP1 (the part of Ũ outside Ũ_P lies in W and is complete).

**R2.** After Lines 17–19, the argument of (J1) plus two more observations gives the frontier. Accurate keys in W' that are deleted are replaced as witnesses by the Line-18 relaxations along path(v). Q-vertices q with d[q] ∈ [B',B) are inserted accurately at Line 17.

**R3.** Stored values are ⪰ B' by (J3), Line 17 and Line 18. keys ∩ U = ∅ by (J2) and Line 19. keys ⊆ Ũ by (J6) and S1 L3+.

**R4.**
- If B' = B via FIX-EMPTY, then D = ∅ at loop exit, and Lines 17–18 insert nothing: their values must be ⪰ B, while Relax requires ≺ B.
- If B' = B'_f = B otherwise, every key would have stored value ⪰ B, which is impossible, so D = ∅.
- If B' ≺ B, then D ≠ ∅ at exit, so the loop left because |U| > Λ_l.

## Verdict
The corrected core is provable from FP1–FP6, S1 (A1–A4, A2', L3+, Claim C), FIX-STALE (delete), FIX-EMPTY, FIX-BASE and (J4'). Requests for S2 (agent-08):
- State (J4') in place of (3'), or change Line 26 to compare stored values.
- Carry R2 with D^acc through the induction.
- Use (J6) wherever Lemma 3.6 needs S_i ⊆ Ũ_P.


## Appendix R1 — Formal review #1 (agent-09) of S1

Frozen label `RV09S1`, source `/research/agents/agent-09/work/review_S1_v2.md`, sha256 `29811a0a4b49b77aa83db22a2cb478788375b76078374dd3e16493531c9d260c`, frozen 2026-09-20T07:51:13Z.

# Formal review (agent-09, reviewer #1) of S1 = agents/agent-02/work/L1_foundations.md v2

Date: 2026-09-20. Scope: all sections A–G, read line by line. Empirical cross-check against my independent
prototype (agents/agent-09/work/impl, exact Fractions, explicit full-path labels as ground truth).

**Verdict: CORRECT, modulo the clarifications R1–R5 and one OPEN obligation (R6), which is delegated to S2.**
No counterexample found. Claim C, L3+, D1–D3 and Remark 4 check out on paper. They also check out
empirically: 2079 runs assert the Lemma 3.7 postconditions after every outer call and every inner top-level
call, against an oracle for the capped single-root instance, which is exactly S1's I_x under suppression semantics.
Zero failures.

## R1 (clarify): all labels must be walks from ONE common start
O1–O5, T1 and T2 are stated "for walks from a common start". The proofs of A3, D1, D2 and L3+ compare a cap
c(v) = d_0[v] with labels L_x(P), and they compare dis_I(u) ⊕ e with d[u] ⊕ e where d[u] may be an initial
label. This is legitimate because every label that ever exists represents a G-walk from the global source s:
λ_σ = d_0[x] is one, the caps are, and so are all relaxed labels. **Please state this as a standing invariant:**
"every label, cap, bound and snapshot represents a walk from s in the degree-reduced graph G". Then no
comparison mixes walks with different starts.

## R2 (clarify): the order does not have to be the edge-id order
S1 A uses edge ids in κ. Version-stamped labels that store the pred VERTEX (my prototype, and agent-01's early
version) realize the nested order κ₅(W) = (ℓ, q, v, u, κ₅(W|u)), where W|u is the prefix ending at u. This order
also satisfies O1–O5, with the same proofs: suffix invariance holds because equal (ℓ, q) at v with the same
tail u forces equal (ℓ, q) at u. So it is equally valid. Moreover, with δ = 3 degree reduction the reduced
graph is SIMPLE: each gadget vertex carries exactly one non-cycle endpoint, and self-loops are dropped. So κ₅
coincides with the vertex-sequence order there.
Suggest one sentence: "any total order on s-walks satisfying O1–O5 and realized exactly by the O(1) compare
suffices". Empirically, `impl/cmp_modes.py` gives 693/693 runs with identical op counts and labels between fast
5-tuples and explicit full-path tuples.

## R3 (gap, small): D2 must also cover non-Relax label reads
D2 proves that every valid Relax stays inside G_x. Execution equivalence, however, also needs every OTHER read
of a label or stored value in the inner run to involve only vertices of R_x ∪ {x}. These reads are:
FindPivots-D heap keys, D insert/pull/merge values, the separators B_i, the Line-13 picks d[v] < B_i, the
Line-25/26 pivot comparison, the argmin over P_j (Lines 6/28), the Line-32 test, the W' test (Line 34), and the base-case BST.
**Proposed fix (one line, also used by R4): (SP') every vertex that ever occurs in a heap, D, S, P_j, W or U
of the run is σ or was touched earlier in the run.** Proof: same induction as SP. Keys enter these structures
only after a valid relaxation, or as members of S / P_j ⊆ S / W, all of which were touched or equal σ.

## R4 (clarify): Remark 4 needs two steps written out
(a) "Every completed vertex other than the source is touched" is exactly SP' applied to U.
(b) The claim "no sink on path(v)" needs an induction along path(v) = (x = y_0, …, y_r): every y_i has
dis(y_i) = L_x(prefix) ⪯ d_0[y_i] (A3 in the outer instance) and ≺ B. So the FIRST sink y_j on the path would
make (y_0 … y_j) admissible, since condition (ii) only concerns internal vertices. That would put y_j ∈ R_x,
a sink in R_x, which contradicts "no touched sink" (by (a) together with full execution ⇒ R_x ⊆ U_x). Please write
this 3-line induction explicitly. With SUPPRESSION semantics the argument is the one in my design note L2. There
the post-hoc test "no valid edge from U_x into Z" plays the role of "no touched sink".

## R5 (clarify): Claim C for multilevel bootstrapping is an induction on depth
Section D, "Dependency order", says failed-search exactness uses correctness of BMSSP-D on I_x, "proved first,
independently". With depth ≥ 2 bootstrapping, the inner run itself uses FindPivots-B one level down. So the
statement is an induction on bootstrap depth: depth 0 is BMSSP-D; depth j uses the depth j−1 result for its
inner runs. This is the same as agent-03's obligation (e). Also note that the nested instance I_{x2} is defined
relative to H = G_{x1}, with caps = global labels at its start. D1–D3 apply verbatim, because they only use (I0)
for H and SP/SP' of the depth-1 run, and SP holds including nested runs: x2 is touched in I_{x1} or equals x1.

## R6 (OPEN — must be discharged in S2): the stored-value invariants (1')–(3') of Section F
The Claim C proof, case y ∈ P_ini, uses (1') and (3'). Section F only sketches their preservation.
Required for S2 (agent-08):
 (a) Redefine P̂_j with D^acc: "path(v) visits no complete vertex of D^acc".
 (b) Strengthen the sub-call guarantee to "⟨U_i, D_i^acc⟩ is a frontier for Ũ_i". Then prove it inductively. The
     critical sub-case is a vertex whose label a FindPivots/inner search lowered to its final value without
     inserting it anywhere. It must become an accurate D-key later: either through the Line-22/35 re-relaxation
     from its complete pred, where Relax's ⪯ re-inserts it, or it is covered by an accurate ancestor.
 (c) Merge keeps the smaller stored value. So an accurate entry of D_i stays accurate in D, because the parent's
     stale entry of the same key is ⪰ the current label, which equals the accurate value.
 (d) (3') after a sub-call that lowers labels of P_j-vertices without re-insertion. This is DMSY26's case "d[v] modified
     by the i-th sub-call" restated with D_i^acc.
Empirically, (1') holds after every returned call in my prototype. The check `check_call` item 6 is
"⟨U, D⟩ frontier using only FRESH complete live keys", and it had zero violations in 2079 runs. But this is not a proof.

## Checked and OK (no action)
- A: κ injective per start; O1–O5; the version-stamp compare is exact, including the bound-vs-same-vertex case
  that 4-tuples get wrong (my audit A4); T1, T2.
- B: A1, A3 (incl. relaxation into σ never valid), A2' (needs version stamps), A4, output paragraph.
- C: admissible walks, R_x, G_x; D1 (both inclusions); D3; Remark 1–3, 5 (sink bound
  |U_x ∩ Z| ≤ δ(|U_x \ Z| + 1): preds of sinks are non-sinks since sinks have no out-edges in G_x).
- D: L3+ (uses u = p*(v) from exact equality; x's completeness is not needed); L3; Claim C case split
  (Q vs P_ini partition S; y complete at X's start stays complete).
- G: I concur with the recommendation (TV).


## Appendix R2 — Formal review #1 (agent-09) of S2

Frozen label `RV09S2`, source `/research/agents/agent-09/work/review_S2_v1.md`, sha256 `276f5856882166650886513c9ebbf4e97c090d1308475919e57100e7c09b19c3`, frozen 2026-09-20T07:51:13Z.

# Formal review (agent-09, reviewer #1) of S2 = agents/agent-08/work/S2_core.md v1.0

**Verdict: CORRECT.** No counterexample, and no step fails. I checked every step against S1 (A1, A3, A4, L3+, SP)
and FP1–FP6. Items N1–N6 below are presentation or interface points; none changes the lemma.
This also discharges my S1 review item R6 (stored-value invariants), because S2's certification (b) replaces P̂.

## Steps I verified in full
- **S2.3 base case.**
  - (K0): every label change inside BaseCase is followed by an Insert with the same value, and re-confirmations re-insert an equal value.
  - (K1): values are strictly increasing because of T2. This also holds for S-keys that are never extracted: every remaining key is ⪰ the
    extracted minimum, and labels of different vertices are distinct.
  - (K2): no w ∈ U is validly relaxed, since cand ≻ d[u_j] ≻ d[w].
  - (K3), the maintenance through the "last U-vertex a on path(v)": relaxing a's canonical edge made b complete and
    inserted it with value dis(b), and b ∉ U, so b is still a key.
  - (K4), and the return case (D ≠ ∅ ⇒ B' ≻ d[u_last] ⪰ all of U).
- **Step 0 (A, W^c).** (A-contains-P) is FP1 applied to an incomplete x ∈ P_ini. (A-bound): labels do not change
  between Line 2 and Line 4.
- **Step 2.**
  - (S-b): for (b), p_j is pulled by PP and is the CURRENT pivot, so Line 9 adds y.
  - (C1) for the sub-call has four exhaustive cases. (C2) and (C3) follow; S_i ≠ ∅ holds because deletion semantics keep D free of U-keys.
- **Step 3.** (U-out) holds because U ⊆ {dis ≺ B'_{i−1}}.
- **Step 4.**
  - (k1)–(k4). In (k3), a complete v forces u = p*(v) through exact label equality, so v ∈ A. An incomplete v is not in W^c.
  - (J4) has three exhaustive cases.
  - (J3):
    - Case 1, sub-case dis(b) ⪰ B_i: b ∉ U, since dis(b) ⪰ dis(a) ⪰ B'_{i−1}, and Line 12 precedes Line 17.
    - Case 2c, second bullet: the chain val(final) ≺ … ≺ val(p_j(0)) ⪯ d[y] holds. Apply V1 at each change time, and use that
      d[y] is constant because y is complete.
    - Case 2c, third bullet, uses (R7) of the sub-call.
- **Step 5.** U_i ≠ ∅ (via (R4) of the sub-call), (E), W'-completeness, (R1)–(R9).
  - (R2) for W^c-vertices: the first complete S-vertex q on path(v) lies in Q. The z_j form a prefix. Line 22 covers a = 0 and Line 25 covers a ≥ 1.
  - (R4) case (i): Lines 22 and 25 insert nothing when B' = B.

## Items
- **N1 (implementation equivalence; state in S2 or S5).** S2 deletes U_i from D (Line 12). Implementations with a LAZY
  per-instance done-filter at Pull (mine, agent-06's, and agent-02's option) are equivalent, provided:
  (a) Pull never returns a done key;
  (b) the done flag is per instance, because an inner I_x has its own flags;
  (c) the loop test "D ≠ ∅" either counts only live keys, or tolerates iterations whose filtered pull is empty. In that
      case Lemma S2.1 must allow S = ∅, which trivially returns (B, ∅, ∅) and costs O(1). That O(1) is charged to the ≥ 1 discarded entry.
  My prototype uses (c) with empty sub-calls. In 2000+ runs it satisfies (R1), (R3), (R4), the fresh-key frontier (≈ R2),
  and S \ U ⊆ keys(D) (≈ R7).
- **N2 (write it out).** S2.5 item 5 cites Obs. 3.5 "through (R8)". S4's G2/G4 need the stronger *insertion-event
  uniqueness*: each edge (u, v) causes at most ONE insertion in total over Line 17 at all levels, Line 25, and BaseCase
  Line 4. Proof (3 lines): u is complete from the moment it joins some U, so cand = dis(u) ⊕ e is fixed; ver[u] no longer
  changes. Let X_0 ⊃ … ⊃ X_q be the calls whose U contains u, where X_q is where u joined (base case or W'). The insertion
  windows are disjoint:
  - [B_{X_{r+1}}, B_{X_r}) for Line 17 at X_r;
  - [B'_{X_q}, B_{X_q}) for Line 25 when u ∈ W'_{X_q};
  - (−∞, B_{X_q}) for base-case relaxations at X_q.
  Relaxations in FindPivots and inner searches never insert (FP6). Please add this as Lemma S2.4; S4 cites it.
- **N3 (spell out).** In (J3) Case 2c second bullet, write the multi-change chain explicitly. It is correct but compressed.
- **N4 (scope).** Lemma S2.1 is stated per instance. Please add one sentence that it is applied (i) to I_0 and (ii) to every
  inner I_x, and (iii) by induction on bootstrap depth, where FindPivots-B inside I_x is covered by S3's FP proof on
  deadline instances. This is the composition agent-05 asked for (S4 Sec. 7).
- **N5 (minor).** S2.0 PP asserts x ⪯ B. This uses "every stored value ≺ B", which is (R3)-for-D. Add a forward reference.
- **N6 (minor).** Line 16 re-relaxes edges that the sub-call already relaxed. Tie re-confirmations then return True, but
  the test d[u]⊕e ⪰ B_i rejects them, so they cause no insertion. This is harmless. Worth one line, because it is where
  Relax's "True on equality" meets the insertion rule.

Empirical cross-check: my independent prototype passes 1089 + 2772 invariant-checked runs (quick + full suites, suppression and
sink variants, depth 1 and 2), with 0 violations of the S2 postconditions it asserts.


## Appendix R3 — Formal review #1 (agent-09) of S3

Frozen label `RV09S3`, source `/research/agents/agent-09/work/review_S3_v1.md`, sha256 `c3caff9a5e4a3c828b21590ec035bdcfa8ee5e7d0f37e4bfda1eed097fcf7030`, frozen 2026-09-20T07:51:13Z.

# Formal review (agent-09, reviewer #1) of S3 = agents/agent-08/work/S3_findpivots.md v1.0

**Verdict: CORRECT (suppression semantics, pseudocode.md v2.x FB/FD/MP).** No gap found. Items T1–T5 are
clarifications. Checked line by line:
- **§S3.1 (FindPivots-D on any admissible instance).**
  - (D-a) heap keys = labels.
  - (D-b) extraction keys strictly increase, and no extracted vertex is re-relaxed within a search. Across searches, re-relaxation is allowed and harmless.
  - (D-c) K is an arborescence.
  - (D-d) K meets the earlier trees only in the hit vertex.
  - (D-e) |K| ≤ k−1+δ.
  - FP1: induction along path(v) from the complete Q-root. The key step "z_{j+1} not extracted earlier" uses D-b
    together with dis(z_{j+1}) ≻ dis(z_j). "Not in a tree" holds because the FD.12 test follows every valid relaxation.
  - FP2–FP6.
  - The corrected FP7(D) with Σ_T|V(T)|: I agree that MASTER's p'-form undercounts merges. S4/MASTER should adopt the §S3.1.4 form. S4's
    inner per-vertex cost is unaffected: Σ_T|V(T)| ≤ |U_Y| for full executions and ≤ (k'+δ)|S_Y| < 4(k'+δ)|U_Y|/t' for partial ones.
- **§S3.2 (FindPivots-B).**
  - (I-1)–(I-4) via S1 D1–D3 and S2 (Lemma S2.1 in I_x, with FindPivots-D satisfying FP on I_x).
  - N ⊆ Ũ, U_x ⊆ N, and N ∩ Z = ∅.
  - The tpar0 arborescence (tails in N, including the re-confirmation case; labels strictly decreasing, so x is the unique root).
  - FP1 (ii): the first sink z_j on path(v) would be hit by the complete predecessor's scan with bound B (Lemma S2.4 at the top inner call).
  - FP2–FP6, FP7(B).
- **§S3.3–3.5** are fine.

## Executable confirmation (new)
My prototype now also has a variant 'pseudo' that mirrors pseudocode FB exactly:
- tree vertices N = {x} ∪ touched (the TH hook);
- tree edges tpar0 = d[v].e read at the end of the run;
- hits recorded inside Relax (RX.4–5);
- merge with the FIRST hit;
- new tree iff (not full) or |U_x| ≥ k.
It asserts in-line: N ∩ Z = ∅, U_x ⊆ N, the tail of d[v].e lies in N, |N| ≥ k for a new tree, U_x = N for a failed search, and the hit tail lies in N.
Quick suite, 1485 runs over 15 configs incl. depth 2: 0 failures.
**Sensitivity check:** an earlier version of my variant accidentally dropped the hit records. The checker then reported
"⟨W,P⟩ frontier violated" on a 3-vertex graph (edges 0→2:1, 0→1:0, 0→2:2, 1→2:1, 1→0:1). In that run a search
succeeded, its tree took vertex 9. A later search from 7 completed 8, and its relaxation 8→9 improved 9's label but was suppressed.
Without a hit, the search was wrongly classified as FAIL. This is exactly the case that S3.2.3 (ii) handles through the hit.
So both the proof and the checker depend on hits in the same place.

## Items
- **T1.** (I-4) is used for the TOP inner call. State that Lemma S2.4 is applied with that call's bound, which is the outer B.
  The failed-search argument needs relaxations with bound B. Relaxations inside deeper inner calls with bounds B_i ≺ B
  would not suffice for vertices whose cand ⪰ B_i. l_in ≥ 1 is also used here; if l_in = 0, BC.7 scans with bound B as well.
- **T2.** S3.2.3 (i) uses exact TV semantics: d_0[q] = dis(q) ⇒ the represented walk IS path(q). Under the final ruling (TV)
  this holds. Add "(TV)" at that step so that no one reads it under T4.
- **T3.** S3.2.5: Σ|N| over tree and merge searches is ≤ Σ O(c_in(U_x)) = O(g Σ(|U_x|+1)). This bounds the MP/PT cost. In partial X,
  Σ|N| is O(g k|S|) = O(t|S|) = O(|U|), not O(k|S|). agent-03 and agent-02 made the same point. The FP7(B) total is unchanged.
  S4 (3.1) should use Σ|N| for the tree mass and Σ|U_x| ≤ 8k|S| for the inner cost.
- **T4.** p ≤ Σ(|V(T)|−1)/(k−1): with N-trees, Σ|V(T)| can exceed Σ|U_x|, but the trees stay vertex-disjoint subsets of Ũ.
  So p ≤ |Ũ|/(k−1) still holds in full executions. In partial ones, p ≤ |S| is what is used. Fine; one sentence.
- **T5.** A degenerate case worth listing in S3.3: x ∈ S touched by an EARLIER search, with its label lowered, but not in any tree.
  x's own search then runs normally on I_x with its current label. This is covered by D1–D3, since caps are the current labels.


## Appendix R4 — Formal review #1 (agent-09) of S4

Frozen label `RV09S4`, source `/research/agents/agent-09/work/review_S4_v3.md`, sha256 `ee67052654674b85afa12e98348119ac57d92bdf64c033c07bfb1bc28ee3778d`, frozen 2026-09-20T07:51:13Z.

# Formal review (agent-09, reviewer #1) of S4 = agents/agent-05/work/cost_analysis.md v3

**Verdict: CORRECT, conditional on F1–F9 as stated.** Those facts are exactly what S1/S2/S3 must supply.
I re-derived (I1)–(I4), (3.1)–(3.2), the pivot count, (4.1)–(4.2), G1–G5, the Sec. 5 parameter arithmetic
(including the n = 2^64 sanity numbers 15.9 vs 19.6), and the Sec. 8 space bound. There are no errors, only the items below.

- **R1 (state explicitly).** (I3)(a) bounds #inner calls by (l*+1)|U_x| using F7: "every call with nonempty S has |U| ≥ 1".
  With FIX-STALE as a Pull filter, a filtered S_i can be EMPTY. The pseudocode must then either skip the
  sub-call (agent-02's rule: B'_i := B_i, U_i := ∅) or charge the O(1) cost of the empty call to the ≥ 1 discarded
  entry, which was paid for at insertion. My prototype makes the empty call, which returns full in O(1). Either is fine; S4 should name the rule.
- **R2 (state).** Sec. 3, sink semantics. The same sink z can be completed by MANY later searches, and each of
  them is then a MERGE. The charging must be per search: z is charged to its canonical pred inside *that*
  search's K_x, which gives at most δ per K_x vertex, and the K_x are disjoint. The text implies this; please say "per search".
- **R3 (check, OK).** (I1)'s |W'_top| < k' follows because the top inner call has |S| = 1, so |Q_top| ≤ 1. The loop overshoot is bounded by
  Ū'_{l*−1} ≤ 6Λ'_{l*−1} < 6k by the minimality of l*. So |U_x| ≤ 8k holds.
- **R4 (check, OK).** The G4 Q-bound survives FIX-STALE's non-done stale entries (pulled "extra sources"). Y_{a+1}'s S
  comes only from D's inside T(Y_a), whose ancestor D's are not accessible, and D_{Y_a} starts with pivots only. So the
  first entry of v after Y_a's FindPivots is still an insertion event.
- **R5 (feasibility, OK).** Λ'_1 = t'^3 2^{t'} = k^{o(1)} < k, since 2^{sqrt(log k loglog k)} = k^{sqrt(loglog k / log k)}.
  Also k ≥ t' and k ≤ t hold for all large n. The constant C_g in (I4) does not depend on n.
- **R6 (theorem statement).** I agree with Sec. 9 item 4. The master theorem should state the sparse bound, plus "never
  worse than DMSY26" through the hybrid. With sink semantics the strict-improvement range is m/n = o(sqrt(LL/LLL)).
  MASTER_B1 §2 currently says o(sqrt(log log n)), which is the suppression-semantics range. Please make §2 consistent with
  the chosen semantics (editor).


## Appendix R5 — Formal review #1 (agent-09) of S5

Frozen label `RV09S5`, source `/research/agents/agent-09/work/review_S5_v1.md`, sha256 `1feae9bc5329d9f17ddfb68742482b2430580b4e9696df95bcdbf6fc3ca51bdf`, frozen 2026-09-20T07:51:13Z.

# Formal review (agent-09, reviewer #1) of S5 = agents/agent-04/work/S5_data_structure.md v1 (Secs. 1–5)

**Verdict: CORRECT.** Checked in full:
- Lemma DS for Insert, Delete, Merge and Pull.
- The (SEP) invariant under all four operations, including an R-block becoming the new first block and a Delete emptying the first block.
- The block-count bound (a): #blocks ever created ≤ 1 + O(N/M), so tree depth is O(lg(N/M+2)) with NO lower normalization.
  This is a nice simplification over DMSY26 and is what makes Delete O(1).
- The charging (b)–(f), Pull separation, the Merge precondition on stored values (BM.14), the M=1 variant, Lemma MS, and the space bound.
- The correction (A_M): lg(N/M) = O(M) instead of M ≥ log(N/M). This is right. At l = 1, lg(N/M) = t + O(lg t) > M = t.

Minor notes:
1. **Pull with many tiny or empty blocks.** Collecting M+1 entries may remove many blocks. Each removal costs
   O(lg #blocks) = O(M) by (A_M) and is charged to that block's creation, which happens once. State explicitly that
   "each block is removed from the tree at most once". It is implied by (b).
2. **Lemma MS.** Also note that D_X is EMPTY while FindPivots(X) runs. pseudocode.md creates D at BM.3 and FindPivots
   is BM.4; S2 does it in the other order. So records pushed by inner searches never interleave with X's own D-records.
   The P-records of X are pushed only at BM.6, after FindPivots.
3. **Sec. 5 item 4, W-lists.** "<= k|S| <= n' k..." is a leftover draft sentence. The final bound (charged as in item 3) is
   fine; delete the leftover.
4. The base-case BST must also use the membership stacks, because it is merged into the parent at BM.14. It does implicitly
   ("Merge-able into a block structure"). One sentence would make it explicit.


## Appendix R6 — Formal review #2 (agent-06) of S1

Frozen label `RV06S1`, source `/research/agents/agent-06/work/review_S1.md`, sha256 `08e02259dfe776118f1d39484c56c9c465e1f85479beaead73ab98cae38e3c1f`, frozen 2026-09-20T07:51:13Z.

# Formal review #2 (agent-06) of S1 = agents/agent-02/work/L1_foundations.md (v2.5)

**Verdict: CORRECT.** There is one implementation obligation (s2) that must appear in S5 or the
pseudocode, and three wording fixes. I checked it independently of agent-09's review.

## Checked
- **§A.** κ and O1–O5.
  - O2 (suffix invariance): after the common prefix (ℓ+ℓ_R, q+q_R, id(end), ids(R)), the comparison
    of P∘R vs Q∘R continues exactly as κ(P) vs κ(Q) beyond (ℓ, q, id(u)).
  - O4 (prefix-optimality) follows from O2.
  - Version-stamp compare. Equal (ℓ, q, v, e) forces the same tail u with equal (ℓ, q), and a larger
    version is a strictly smaller walk (O2). So compare realises κ on represented walks, with one
    real comparison. T1 and T2 hold.
- **§B.**
  - A1.
  - A3: see (s1) below for the precise argument for σ.
  - A2' via W^{(a)}(p*) ∘ e* = W_σ ∘ path_I(v). This gives W^{(a)}(u) = W_σ ∘ path_I(u), so u was
    complete at version a and still is.
  - A4.
- **§C.**
  - Admissibility.
  - D1: the minimising G_x-walk is admissible, because its prefix labels are
    dis_{I_x}(y_i) ⪯ D(y_i) ⪯ d_0[y_i]. The induced subgraph therefore creates no shortcut.
  - D2: induction with SP, and P_u ∘ e admissible from the display.
  - D3.
  - Remark 4 (failed-search exactness under suppression). Truncate at the first sink; its predecessor
    u is completed; Lemma S2.4 scans (u, z) with the TOP call's bound B while u is complete; so a
    hit is recorded. Then the segment of path(v) from a complete x is admissible, so D(v) = dis(v).
- **§D.** L3+: equality cand = dis(v) forces e = e*, u = p*(v), path(v) = path(u)∘e*, hence path(v)
  visits S. It does not use completeness of x. Corollary L3.

## Items
- **(s1) A3, "relaxation into σ is never valid".** The sentence "cand represents W_σ∘P∘e" is only
  literally true if d[u] was produced inside the instance. For an untouched u, cand = c(u) ⊕ e.
  The correct argument uses (I0): d[u] ⪰ dis_I(u) = L(W_σ∘P_u), so
  cand ⪰ L(W_σ∘P_u∘e) ≻ λ_σ (T1, O3). If dis_I(u) = ∞ then c(u) = ∞ and cand = ∞. Please
  reword; the conclusion stands.
- **(s2) Execution equivalence needs OWNER-AWARE membership lookups (implementation obligation).**
  D2/SP' cover label and stored-value reads. The inner run also performs integer membership lookups.
  During InnerSearch(x), a vertex v may carry P-entries of *ancestor* outer calls (pushed at their
  BM.6 and not yet popped) and D-entries of ancestor outer D's. The obligations are:
  - Pmem(v) (BM.12/17/22) must return "none" unless the top P-entry of v is owned by the *current*
    call.
  - D.Delete(u) (BM.15) and Insert/Merge must touch only entries owned by the current D.
  Otherwise the inner run could delete an outer entry, which violates FP6, or treat v as a member of
  an outer P_j, which breaks equivalence with the run on I_x. S5's membership stacks presumably do
  this. Please make "owner check" explicit in S5 Lemma MS and cite it in D2.
- **(s3) Claim C proof in §D.** It is phrased with S1's own (J2)/R6/D^acc notation, which S2 v1.1
  supersedes with the certified frontier (J1)–(J5). In the integrated document, cite S2 Step 2 (C1)
  as the proof of Claim C for sub-calls. §D's version should be a sketch/remark to avoid two
  inconsistent invariant systems. §F is historical and should be marked as superseded by S2.
- **(s4) Minor.** In D1, state explicitly that d_0[x] ≺ B (x ∈ S, so FP context (C3)); this is needed
  for x ∈ U~_{I_x}(B,{x}). In §C, name the bound used by Lemma S2.4 as "the top call's bound = the
  outer B" (Remark 4 relies on exactly that).


## Appendix R7 — Formal review #2 (agent-06) of S2

Frozen label `RV06S2`, source `/research/agents/agent-06/work/review_S2.md`, sha256 `432a70d2df86c15b077fc5414692855eff90c48006d51b4da03209f525ea58dd`, frozen 2026-09-20T07:51:13Z.

# Formal review #2 (agent-06) of S2 = agents/agent-08/work/S2_core.md (v1.1)

**Verdict: CORRECT.** I found no counterexample and no logical gap. There are 5 clarifications
(c1–c5); none changes the proof.

## Scope checked
All of S2.0–S2.6, line by line, against pseudocode v2 (BM.1–BM.31, BC.1–BC.9):
- **Base case (S2.3).**
  - (K0) holds: only BC.7 changes labels inside BaseCase, and it inserts each change.
  - (K1)/(K2): extracted values strictly increase and there is no re-extraction.
  - (K3): the last-in-U vertex a and its successor b. b was relaxed canonically when a was
    extracted and cannot have been extracted since.
  - (K4): minimality contradiction. It uses a certified y ≠ u, which exists because u is incomplete.
  - The return analysis gives (R1)–(R7).
- **l >= 1.**
  - Step 0 (A, W^c, A-closure, A-contains-P, A-bound).
  - Step 1 (J1–J5 initialisation).
  - Step 2: (S-a), (S-b), then Ũ_i ⊆ A \ U, and (C1)–(C3) for the child.
  - Step 3: (B-mono), (U-in), (U-out).
  - Step 4, keys (k1)–(k4). In (k3) the complete case uses u = p*(v) and A-closure; the incomplete
    case uses FP1; v ∉ U ∪ U_i because cand ⪰ B_i ⪰ B'_i ≻ dis(w).
  - Step 4, (J4) in all three branches.
  - Step 4, (J3):
    - Case 1: a = last vertex of path(v) in U_i. If dis(b) ≺ B_i, use (R2) of the child and Merge;
      else the BM.21 canonical insert.
    - Case 2a (R2 of the child) and Case 2b (old certified key survives BM.15).
    - Case 2c, incl. repeated BM.22 switches: val(p^(r)) ⪯ d[p^(r)] ≺ d[p^(r-1)] ⪯ … ⪯ d[y], by
      induction.
  - Step 5: termination (U_i ≠ ∅); cases (i) and (ii); (E); W' complete; (R1)–(R9).
  - The W^c-prefix argument for (R2) (a = 0 via BM.25; a >= 1 via BM.27–28 canonical relax with
    cand ⪰ B').
- **S2.4b (Lemma S2.4)** and its use for failure exactness under suppression: the induction along
  x = y_0..y_r; a sink y_i would be recorded as a hit at the BM.19/27 or BC.7 scan of y_{i-1}.
- **BM.29 redundancy.** Keys have dis ⪰ B' (J2/R3), so d ⪰ B', so no key is in W'. BM.25/BM.28
  insert only labels ⪰ B'. OK.
- I confirm the claim that **no step uses ancestor closure**. Every complete witness is obtained from
  (C2), FP1, (R1) of a child, or A4 applied to a complete vertex's canonical edge.

## Clarifications (non-blocking)
- **c1 (instance graph under suppression).** Every "b is the successor on path(v)" step (K3, Case 1,
  R2 prefix) needs b to be a vertex of the instance graph H. For I_x this means H = G_x, which
  contains no sinks. S2.1's last remark says so. Please add one sentence to Lemma S2.1: "path(·),
  p*(·) and Ũ are taken in H; for inner instances H = G_x of S1 §C, so no path passes through a sink."
  Then the A4 relaxations in K3 / Case 1 / R2 are never suppressed.
- **c2 (PP).** PP is used with STRICT ≺ x. That is fine even if stored values tied. In fact they
  never tie: val(y) is always a label of y itself, so its curr field is y. One line would help readers.
- **c3 (Observation 3.5).** S2.5 item 5 sketches the edge-once property. Please state it as
  Corollary S2.5, since S4's G2 needs it verbatim. For u, the calls containing u form a chain
  X_0 ⊃ … ⊃ X_q (by R8 per level). The possible insertion events on (u,v) are:
  - BM.21 in X_j with cand ∈ [B_{X_{j+1}}, B_{X_j});
  - BC.7 in a base X_q with cand ≺ B_{X_q};
  - BM.28 in X_q with cand ∈ [B'_{X_q}, B_{X_q}).
  cand is fixed because u is complete throughout (R1) and u's label never changes. The intervals are
  disjoint, so there is at most one event.
- **c4 (what S3 must deliver).** S2 uses FP1 in its strong form ("every v ∈ Ũ is in W and complete,
  or path(v) contains a vertex of P_ini that is complete when FindPivots returns"). For
  FindPivots-B this needs FAILURE EXACTNESS for complete roots q ∈ Q, and L3+ for FP3 (W ⊆ Ũ). Also
  note: a root q whose search failed may later be touched and put into a tree by a later search. It
  stays in Q (MP.6 excludes Q), and v ∈ W_q is complete; S3 should mention that case.
- **c5 (partial-call size claim for S4).** (R4) gives |U| > τ. S4's (B2) additionally needs τ >= t|S|
  (FIX-SIZE / FIX-L13). That is S4's responsibility, but the master should cross-reference it.

## Empirical cross-check
My independent implementation (a06_dmsy26.py; done-filter variant of FIX-STALE plus FIX-BASE) asserts
U = Ũ(B',S), completeness, S \ U ⊆ keys(D) and tree vertices ⊆ Ũ(B,S) after every outer call. This
covers plain DMSY26 and bootstrapped runs: 0 violations and 0 wrong distances in 1,656 runs.
agent-08, agent-01 and agent-09 report the same with their own checkers.


## Appendix R8 — Formal review #2 (agent-06) of S3

Frozen label `RV06S3`, source `/research/agents/agent-06/work/review_S3.md`, sha256 `3521ebdf09545e950755a4ed9ac1183a7d6ce8b9bb75a3727051e64320b1911d`, frozen 2026-09-20T07:51:13Z.

# Formal review #2 (agent-06) of S3 = agents/agent-08/work/S3_findpivots.md (v1.1), plus a delta check of S2 v1.2

**Verdict: S3 CORRECT. S2 v1.2 CORRECT (my v1.1 verdict carries over; new Lemma S2.5 checked).**
The minor items t1–t4 below are non-blocking.

## S3 checked against pseudocode v2 (RX, FD, MP, FB, TH, PT)
- **§S3.1 FindPivots-D.**
  - (D-a) heap key = current label.
  - (D-b) strict extraction order. A valid relaxation into an extracted w needs cand ⪯ d[w] ⪯ d[u'],
    but cand ≻ d[u']. This also excludes re-confirmations.
  - (D-c) kpar1 tails are extracted earlier, so they form an arborescence with |K|-1 edges of H.
  - (D-d) The FD.12 test fires at the first valid relaxation of a tree vertex, so K meets the trees
    only in the hit vertex.
  - (D-e) |K| <= k-1+δ.
  - FP1 induction along q's canonical path: A4 at each extracted z_j. An earlier extraction of
    z_{j+1} is excluded because its key would be ⪰ dis(z_{j+1}) ≻ dis(z_j), contradicting (D-b).
    The FD.19 exit gives H = ∅, so every z_j is extracted.
  - FP2–FP6.
  - The corrected FP7(D) is right: merges can make a tree absorb many searches, so the charge is per
    new tree vertex, not per tree. The master §4 wording must be updated as agent-08 says.
- **§S3.2 FindPivots-B.**
  - (I-1)–(I-4), including x ∈ U_x in both the full and the partial case.
  - N ∩ Z = ∅ (suppression), N ⊆ Ũ (L3+), U_x ⊆ N (SP').
  - §S3.2.2: re-confirmation ⇒ identical walk ⇒ same last edge, so every tpar0 tail lies in N. Labels
    strictly decrease toward the tail (T2, A3), so there are no cycles and x is the unique root.
  - §S3.2.3, the crux, i.e. the FP1 frontier via failed-search exactness:
    - (i) prefix labels = dis(z_j) ⪯ d_0[z_j] ≺ B, because λ_q represents path(q) for a complete q.
    - (ii) Take the minimal sink z_j. Its predecessor lies in U_q, and Lemma S2.4 gives a scan with the
      top call's bound B while complete. The candidate is dis(z_j) ⪯ d_0[z_j] = d[z_j] (sinks
      frozen), so RX.3 passes and a hit is recorded, a contradiction.
    - Hence the segment is admissible, v ∈ U_q, and d[v] = D(v) = dis(v).
  - FP2–FP6. FB.13 merge: tree plus tree joined by one edge, N ∩ V(T) = ∅.
  - FP7(B), including the bookkeeping term min(|Ũ|, O(gk)|S|).
- **§S3.3** degenerate cases are OK. §S3.4 (sink variant) is not needed for the theorem. §S3.5 is a
  remark.

## Minor items
- **t1 (S3.1.2).** Mention the re-confirmation case explicitly: an earlier search may already have
  set d[z_{j+1}] = dis(z_{j+1}). Then Relax is a re-confirmation (returns True), and FD.10–16 still
  put z_{j+1} into K and H. The proof is correct because "valid" includes it; say so in one clause.
- **t2 (S3.2.3 (ii)).** Say "sink labels are frozen from q's FB.5 until the end of q's run: Z does not
  change during a search (FB.14/FB.17 happen after FB.6), and suppressed relaxations change nothing".
  That is exactly what "d_0[z_j] = d[z_j]" needs.
- **t3 (FP4 with k).** p <= Σ(|V(F̄)|-1)/(k-1) needs k >= 2. The S4 regime guarantees it (n' >= n_0).
  The correctness parts of S3 hold for every k >= 1.
- **t4 (master §4).** Replace FP7(D)'s "(p' + |Q|)k(δ + log k)" by S3.1.4's
  O((Σ_T|V(T)| + |S| + k|Q|)(δ + log k)), and FP7(B) by S3.2.5's formula. S4 (I3)(e) already uses the
  corrected form (agent-05 confirmed).

## S2 v1.2 delta
- PP as an equality: fine, since stored values are distinct labels of their own keys.
- Lemma S2.5: per u the calls form a chain; all scans happen after completion with a frozen label, so
  c is fixed; the windows [B_{X_{r+1}}, B_{X_r}) and (-∞, B_{X_q}) are pairwise disjoint; W'/extraction
  occur only at X_q. Correct.
- Lazy done-filter equivalence (item 7) needs:
  - (a) Pull never returns a done key;
  - (b) flags are per instance — this matches my implementation, where inner instances use a local
    done set;
  - (c) empty filtered pulls are handled.
  Correct.


## Appendix R9 — Formal review #2 (agent-06) of S4

Frozen label `RV06S4`, source `/research/agents/agent-06/work/review_S4.md`, sha256 `2934bd961cf6b254e765423802ded1f423b7835328e160786f7254522d8fd4de`, frozen 2026-09-20T07:51:13Z.

# Formal review #2 (agent-06) of S4 = agents/agent-05/work/cost_analysis.md (v4, ~07:55 UTC)

**Verdict: CORRECT, conditional on F1–F9**, which are exactly the correctness facts S1/S2/S3 must supply.
No counterexample was found. There are 4 minor items (M1–M4), none blocking.

## What I checked line by line
- **(B1)/(B1')** Frontier size. With 3k <= t, |S_i| <= 3kM_l <= t^2 2^{(l-1)t}. Each pulled current
  pivot adds < 3k vertices, and a stale pivot key adds nothing (BM.12 checks `piv[j] = x`). OK.
- **(B2)** partial => |U| > Λ_l >= t|S| (or t|S|/4). This is used at 4 places, all listed. OK.
- **(B3)** Overshoot by one child plus W'. The bound |W'| <= k|Q| <= kσ_l <= 4Λ_l needs k <= t (true).
  Ubar_l <= 6Λ_l for t >= 3. OK.
- **(B4)** N_X <= |S| + δ|U| + (merged keys, which are out-neighbours of U or S-vertices of children,
  i.e. the same bound up to a constant), so log(N/M) = t + O(log t). OK. "log(N/M) = O(M)" suffices
  for the block-BST amortisation; I agree with the E7 restatement.
- **(B6)** Base-case BST of size O(δt^3); FIX-BASE. OK.
- **(I1)** |U_x| <= k + Ubar'_{l*-1} + |W'_top| < k + 6k + k' <= 8k. Uses Λ'_{l*-1} < k (minimality of
  l*) and |Q_top| <= |S_top| = 1. OK.
- **(I2)** Top-level D of the inner run: N/M' = O(δ t'^2 2^{t'}), so the insertion cost is O(t').
  OK. Partial => |U| > k >= t' = t'|S|. OK. Also needs k >= t' (stated).
- **(I3)**:
  - (a) Per-layer disjointness inside J_x; all inner U_Y are subsets of U_x by induction (a partial
    child's U is a subset of its parent's U). #calls <= (l*+1)|U_x| needs F7, including "S never
    empty" (FIX-STALE by delete makes Pull on a nonempty D return a nonempty set: tracker I18). OK.
  - (b) One insertion event per edge in J_x (inner Obs 3.5). OK.
  - (c) Cross-edge re-selections: the edges lie in E(U_x). OK.
  - (d) Inner Q-bound: x is never re-inserted (no valid relaxation into the source of J_x). OK.
  - (e) Per-vertex direct work, including the partial-case FindPivots-D bound
    O(|S_Y| k'(δ + log k')) = O(|U_Y|) via (B2). OK.
- **(3.0)** |N_x| = O(inner work). Every touch is a valid Relax from a processed vertex (SP). Hence
  the FB.10/FB.13/FB.16 and MakePivots/Partition costs are covered. OK.
- **(3.2)** Σ over succ/merge x of |U_x| <= Σ|N_x| <= |∪F̄| <= |Ũ|. The N_x are disjoint because
  suppression means sinks are never touched and FB.4 skips tree roots. It is also <= 8k|S|. OK.
- **Pivot count.** Full X: p <= |∪F̄|/(k-1). Partial X: p <= |S| (MP.8 drops empty groups). OK.
- **T2.** Picking in a full child is absorbed by the re-selection that the child's completion of the
  pulled pivot triggers. Empty Pl[j] happens at most once per j. OK (this also needs FIX-J at BM.23,
  now in pseudocode v2).
- **T5,full.** The charging needs F_j to be a connected tree whose vertices lie in U_X
  (full ⇒ Ũ = U). Merge edges (u,z) have z in an earlier tree, which lies in Ũ. Pieces are
  edge-disjoint. OK.
- **G4 (Q-appearances).** This is the chain argument. Line 7/Line 33/re-selection entries need v in S
  of a descendant (circular). Merges move entries made in children. So the first D-entry of v inside
  T(Y_a) after Y_a's FindPivots is an insertion event on an in-edge, and inner runs create no outer
  events (F6). OK.
- **(4.2)/(5.1)** Arithmetic: (log N/t)·g = t for t = (log N)^{1/2}(LL·LLL)^{1/4} and
  g = Θ(sqrt(LL·LLL)). The m log t term is lower order. OK.
- **Sec. 6 (general m).** I agree with the correction of my own earlier G3: the inner run pays δ per
  vertex per inner layer, so c_in/δ >= l* + t' >= 2 sqrt(log k). The improvement range under
  suppression is m/n = o(sqrt(LL)). OK.

## Minor items
- **M1 (asymptotic regime must be stated).** The constraints k >= t' and Λ'_1 = t'^3 2^{t'} < k only
  hold for astronomically large n. At n = 2^64 the formulas give t ≈ 15.9, g ≈ 3.9, k ≈ 1, while
  Λ'_1 ≈ 890. The theorem is asymptotic, so this is fine, but S4/master should say: "there is an
  absolute constant n_0 such that for N >= n_0 the parameters of Sec. 5 satisfy (I1)–(I2); for
  N < n_0 run Dijkstra (O(1) time)". Pseudocode SS.7 already has the n0 branch; make n0 explicit
  and consistent with these constraints.
- **M2 (per-depth overhead in the D=3 remark).** Sec. 7 is fine as a remark. The theorem uses only
  depth 2 (outer B, inner D), so no induction on depth is needed for the main claim. Keep the
  "fixed D" wording.
- **M3 (hit-list length).** State that |hitlist| <= #Relax calls in the run = O(inner work), so FB.12's
  use of hitlist[0] plus discarding the rest is O(inner work). Implicit in (3.0); make it explicit.
- **M4 (version counters).** ver[v] increments at most once per strict decrease, and each decrease is
  a Relax call. So the counters are O(log(total work)) = O(log n)-bit integers. That is legal word-RAM
  arithmetic; state it once (G1 model paragraph).

## Empirical cross-check (agent-06 independent implementation, a06_dmsy26.py, boot mode)
The bootstrapped mode (deadline semantics, suppression, capped inner run, local done set) passes the
exact invariant checker (U = Ũ(B',S), completeness, S\U in D, tree vertices in Ũ(B,S)) on 1,656 runs
with 0 violations and 0 wrong distances. On the O1 family, pivot insertions per leaf stay at 0.15
while fresh-label searches grow with the number of levels (obstacles.md sec. 10). These are
finite-test sanity checks only; they are not evidence for the asymptotic claim.


## Appendix R10 — Formal review #2 (agent-06) of S5 + pseudocode

Frozen label `RV06S5`, source `/research/agents/agent-06/work/review_S5_pseudocode.md`, sha256 `46bff464768751d21bbaac1ed50c09645ff81344552db7693008d9bd2b884ddc`, frozen 2026-09-20T07:51:13Z.

# Formal review #2 (agent-06) of S5 (agent-04 S5_data_structure.md v1.1) and pseudocode.md v2 (with FIX-J)

**Verdict: CORRECT.** I found no bug in the current texts. Earlier I found BM.23's missing non-empty
test; it is already fixed as FIX-J. Minor items q1–q5 follow.

## S5 checked
- **Semantics.** Stored values are labels of their own key, so they are pairwise distinct and PP is
  well defined. d[v] ⪯ s_v always.
- **Lemma DS.**
  - Blocks ever created <= 1 + O(N/M): splits after >= M/2 additions or charged to a Pull; Merge
    chunks of size ceil(M/3); one R-block per Pull.
  - Tree searches cost O(lg(N/M + 2)), and O(M) work is charged to Θ(M) items.
  - Delete is O(1) without joins. Sparse blocks are harmless because Pull removes each traversed
    block at most once, charged to its creation.
  - Merge separators: c_1 = -INF, c_i = min(c_i), old first block gets min(f) or is removed. (SEP)
    holds by the precondition (all D' values below all D values).
  - Pull separation: remaining values >= x, and R becomes the new first block with sep = -INF.
- **(A_M).** At l = 1, lg(N/M) = t + O(lg t) <= 5M, i.e. O(M). Also OK for the inner top call:
  M >= t_in because l_in >= 1.
- **Lemma MS.** LIFO owners along the call chain; during BM.14 the D_i records are topmost and popped
  as they move; lookups are owner-checked. This **discharges my S1 item (s2)**; please cite MS in
  S1 D2.
- **Space.** Geometric sum over live D's with O(1) "saturated" top levels; one Fibonacci heap live at
  a time; trees vertex-disjoint. Total O(m + n). Preprocessing and output O(m + n). The map-back
  argument (min-hop gadget vertex, tail outside the gadget, hops strictly decrease along pred) is
  correct.

## Pseudocode checked (RX, OU, BM, BC, FD, MP, FB, TH, PT, SS)
- **RX.** Suppression happens before any label change. A re-confirmation touches but does not bump ver.
- **BM.**
  - Deletion FIX-STALE at BM.15/29. Ancestors delete when U_X is returned (U_X ⊇ U_i).
  - FIX-J at BM.23; FIX-EMPTY at BM.24a.
  - BM.12 uses the current pivot only.
  - BM.22 may leave stale pivot keys, which are harmless.
- **BC.** The cap is checked before extraction, and B' := the min stored value after the final
  relaxations (FIX-BASE).
- **FD.** At FD.12 the union is a tree, because the search stops at the first tree vertex. kpar1
  tails are extracted, hence in K.
- **FB.** SP gives hitlist tails in N. tpar0 is copied at FB.10 (tails in N; acyclic by strict label
  decrease toward x). Merge uses one hit edge into one existing tree, and trees are never merged with
  each other, so ftree0[z] is valid. New trees have |N| >= |U_x| >= k. On failure, U_x = N.
- **MP.** Empty groups are dropped. S \ Q vertices all lie in trees, so FP2 holds.
- **SS.** BFS prune, self-loop drop, degree reduction, and the n0 fallback.

## Minor items
- **q1 (k >= 2).** Sec. 8.2 allows k = 1 (e.g. n = 2^64 gives k = 1). This is fine for correctness:
  every search succeeds, pieces have size [1,3), and there is no Q. But FP4/S4 use
  p <= |∪F̄|/(k-1). State "the running-time analysis assumes n' >= n_0, which gives k >= 2 and the
  S4 constraints k >= t_in, Λ_in(1) < k; below n_0 use SS.7's Dijkstra branch" (matches my S4 M1).
- **q2 (hitlist scope).** State explicitly that hitlist collects hits from EVERY Relax during
  InnerSearch(x): FD.9 (inner FindPivots-D), BM.20/28 and BC.7 at all inner levels. Failure exactness
  only needs the BM.19/27 and BC.7 scans of completed vertices (Lemma S2.4). FD.9 hits are extra and
  harmless: a hit only turns a would-be FAIL into a MERGE.
- **q3 (FB.11 precedence).** A merge is chosen even if the inner run was partial or |U_x| >= k. This
  is fine: S4 (3.2) covers both orders because N_x joins an existing tree either way. Worth one
  sentence, since the S4 text and some drafts put SUCCESS first.
- **q4 (BC with S containing stale-but-not-done keys).** BC.2 inserts x with its CURRENT label d[x]
  (<= the parent's stored value), so (K0) holds from the start. Correct as written; worth a comment,
  since the parent's stored value may be larger.
- **q5 (SS.12 notation).** `orig(d[e_v].p)` should read `orig(tail(d[e_v].e))` (labels have no
  p-field in v2). agent-02 flagged SS.6/SS.12 nits too.


## Appendix R11 — Formal review #1 (agent-09) of S3 final version

Frozen label `RV09S3fin`, source `/research/agents/agent-09/work/review_S3_v1.3_final.md`, sha256 `8384142f8ff571159990a706ec82008cee011ba5f089eb2cefb682d34503b723`, frozen 2026-09-20T08:03:05Z.

# Formal review #1 (agent-09), FINAL, of S3 v1.3 (agent-08), plus a re-read of S1 v2.6 §D

**Verdict: S3 v1.3 is CORRECT. S1 v2.6 §D is CORRECT, restored and intact.** My S3 review of v1.0 (T1–T5) carries over.

## Changes v1.0 → v1.3, all checked
- **t1.** Re-confirmation clause in the FindPivots-D induction. If an earlier search already set d[z_{j+1}] = dis(z_{j+1}),
  Relax returns True on equality, so FD.10–FD.16 still put z_{j+1} into K and H. Correct, and needed.
- **t2.** Sink labels are frozen from q's FB.5 to the end of q's run: Z changes only at FB.14/FB.17, after FB.6, and
  suppressed relaxations change nothing. Hence d[z_j] = d_0[z_j] in S3.2.3 (ii). Correct.
- **t3.** k ≥ 2 is needed only for the counting p ≤ Σ(|V(T)|−1)/(k−1). Correctness holds for k ≥ 1. Correct.
- **c4.** A failed root that is later absorbed into a tree stays in Q, since MP.6 excludes Q. W_q is unchanged and completeness persists. Correct.
- **agent-03 items.**
  - (2) U_x ⊆ N: every structure entry needs a prior valid relaxation (SP').
  - (3) There is no blocking in FindPivots-D: an earlier tree met by q's search triggers FD.12–15, so q ∉ Q.
  Both correct.
- **Theorem S3.6 (FP for FindPivots-B on any admissible host).** Correct: §S3.2 uses only host admissibility, SP/L3+
  in the host, S1 D1–D3 for a general host, and Lemma S2.1/S2.4 for the inner algorithm. The depth-D induction is then as in S1 §D.
  **Implementation note (not a proof gap).** The FROZEN pseudocode v2.3 has one sink stamp and one hitlist, i.e. depth 1.
  Depth ≥ 2 needs one (ZSTAMP, hitlist, HOOK) per depth. In RX.4–5, a would-be-valid relaxation into a depth-d sink must be recorded
  as a hit of the depth-d search. Exactly one enclosing search can own the sink, because Z_d ⊆ R_{x_{d'}} is disjoint from Z_{d'} for
  d' < d. My prototype does this for depth 2 ('pseudo2' config) and passes. This is relevant only to the depth-≥3 corollary (S4 §7), not to Theorem B1.

## S1 v2.6 §D
Present in full: Claim C, L3+ (with "hits are not relaxations"), Corollary L3, the Claim C proof (normative = S2 Step 2,
with the R6-notation sketch kept as a cross-check), the dependency order, and the multi-level induction. It matches what I reviewed in v2 and adds only the
clarifications I requested (R1–R5).

## Executable status of my N-version (agents/agent-09/work/impl)
- Strict **frozen-PC mode** (PC=1). It implements:
  - BM.15/BM.29 deletion, with no lazy filter;
  - BC.3/BC.5 cap-before-extract, so a partial base case has |U| = τ;
  - BM.24a FIX-EMPTY, BM.23 FIX-RESEL, and per-call P-membership, which is owner-aware by construction;
  - FB exactly: hits inside Relax, N-trees, tpar0, merge on the first hit;
  - version-stamped labels.
  Result: `cd impl && PC=1 python3 run_tests.py quick 13` gives 1485 runs over 15 configs (Dijkstra-FP, nested-suppress,
  sink, pseudo depth 1/2), 0 failures, with the Lemma 3.7/S2 postconditions asserted after every outer call and every inner top call.
  A full-suite PC run (seed 29) is in progress.
- The default mode (lazy done-filter) is a deliberate N-version variant of FIX-STALE and is also 0-failure.


## Appendix R12 — Formal review #1 (agent-09) of the integrated master v1

Frozen label `RV09M1`, source `/research/agents/agent-09/work/review_MASTER_v1.md`, sha256 `0275f5e4ff6348247e4b573293cfce93f78957d4a82ef6bb42ae5477fd26c79c`, frozen 2026-09-20T08:03:05Z.

# Formal review #1 (agent-09) of the INTEGRATED master: agents/agent-10/work/MASTER_B1.md v1 (08:00 UTC draft)

**Verdict: CORRECT for the sparse theorem, which is the goal-relevant statement. There is ONE consistency gap (M1) between the
general-m statement of Theorem B1 and the frozen pseudocode, plus bookkeeping items M2–M5.** After M1 is resolved, I have no objection to
the success claim, subject to the final re-runs (G11, G12).

I checked §0–§9 against my section reviews (S1 v2/v2.6 §D, S2 v1.0–v1.3, S3 v1.0/v1.3, S4 v3, S5 v1/v1.2, PC v2.3) and against the frozen texts.
§2.5, the proof assembly, is complete. The chain is: preprocessing (S5); Cor. S2.2 ⇐ Lemma S2.1 ⇐ FP1–FP6; FP for FindPivots-B on I_0
(S3 §3.2, Thm S3.6) ⇐ S1 D1–D3/SP'/Claim C/L3+ and S2 in I_x with FindPivots-D (S3 §3.1) and Lemma S2.4; output (S5/§8.3); time
(S4 with Lemma S2.5 = G2, G4, B2, I1, FP7); space. Each arrow points at a reviewed statement, and I found no circularity. The dependency order is
S1 §D; the depth induction is S1 §D and S3.6.

## M1 (MUST FIX: theorem vs algorithm text). The general-m formula of Theorem B1 is not what the frozen pseudocode computes.
- The first term of the formula needs a DMSY26 fallback. The second term needs bootstrap with degree reduction to δ = Θ(m/n). **PCv2.3 does neither.**
  Its DegreeReduce always uses δ = 3 (§8.1), and its outer FindPivots is always FindPivots-B (§8.2).
- With δ = 3 for every m, PCv2.3 runs in O(n + m√log n (LL·LLL)^{1/4}) for ALL m (S4 (4.2), N' = O(m)). That is WORSE than DMSY26's
  O(m√log n) when m/n ≥ LL.
- **Fix option A (minimal; my recommendation).** Add a driver switch. If m ≤ n·√(LL/LLL), run PCv2.3 as is. Otherwise run the CORRECTED DMSY26:
  the same BM/BC core, FindPivots-D at depth 0, DMSY26's k = ⌈t/lg t⌉ with 3k ≤ t, and DegreeReduce with δ = Θ(min(m/n, LL)).
  Correctness of the fallback is already proved: S2 + S3 §3.1 (FindPivots-D satisfies FP on EVERY admissible instance, incl. I_0).
  Its time is S4's formula with f = δ + log k (S4 §6). State the theorem as
    **T = O(n + min{ m√log n (LL·LLL)^{1/4},  m√log n + √(mn log n · LL) })**.
  This is never worse than DMSY26, and it is strictly better by ω(1) iff m/n = o(√(LL/LLL)). That range includes all sparse graphs.
  The switch compares integers only. This costs one PC line and one sentence of S4.
- **Option B.** Keep the refined formula with (1 + LLL·n/m)^{1/4}. Then PC must take δ as a parameter in DegreeReduce, the inner parameters
  must depend on δ (S4 §2 Remark), and the fallback is still needed. This is more text and more review.
- Either way, §2's sentence "T is better by an ω(1) factor exactly when m/n = o(√LL)" must match the option chosen. Under A the condition is
  o(√(LL/LLL)).

## M2 (review matrix §3 / gate §9 are out of date)
- **S3 #1 is DONE.** agent-09 CORRECT on v1.0 (07:48:19Z) and FINAL CORRECT on v1.3 incl. Thm S3.6 (07:52:23Z). So G6 is DONE.
- **PC #1.** agent-09 CONSISTENT on v2.3 = FROZEN PCv2.3 (07:49:12Z). **S5 #1:** CORRECT after agent-03's Merge fix (v1.2), acknowledged 07:48Z.
- **S1 #1.** CORRECT (v2) plus a re-read of §D in v2.6 (07:52Z).

## M3 (§7 test table, my row)
Add the strict frozen-PC mode, which follows PCv2.3 semantics exactly:
- deletion FIX-STALE (BM.15/29) instead of my lazy filter;
- BC.5 cap-before-extract;
- BM.24a;
- FB with hits recorded in Relax, N-trees and first-hit merge ('pseudo' configs).
Command: `cd /research/agents/agent-09/work/impl && PC=1 python3 run_tests.py quick 13`, which gives 1485 runs over 15 configs, 0 failures.
A full-suite PC run (seed 29) is in progress; I will post it.
The default command (`python3 run_tests.py`) is the lazy-filter N-version variant.

## M4 (Remark (ii), depth ≥ 2)
Add: "The frozen PC is depth 1. Depth ≥ 2 needs one (ZSTAMP, hitlist, HOOK) per depth, and a hit is charged to the unique enclosing search
whose sink set contains the target (S3 v1.3 review note)." This is implemented and tested in agent-04's bsssp_nested.py and my 'pseudo2'.

## M5 (small)
- §1: "versions are at most the running time" is fine. Also say that the version counters fit in O(log(n+m))-bit words, because the running time is poly(n+m).
- §0/§6: E2's evidence cell could also cite agent-06's minimal witness: 2 vertices, zero weights, parallel edges plus a self-loop, which gives
  10 reduced vertices.
- §8: add one line saying the search protocol must read titles AND abstracts. My own July scan missed 2607.19346 because of its title ("Bellman-Ford in
  Almost-Linear Time"); agents 02/04/10 caught it. The conclusion is unchanged.

## Checked and OK
- §0: summary, idea, credit to KR.
- §1: model.
- §2: the sparse statement, the comparison convention (m ≥ n−1 or additive O(n)), the honest "galactic" note with n_0 and the Dijkstra fallback, and remark (i),
  the deterministic undirected corollary, which follows by bidirecting arcs.
- §2.5: all steps.
- §4: FP1–FP7 match S3 v1.3 exactly, including the corrected FP7(D) and FP7(B) forms.
- §5: the parameters match PC §8.2. I re-checked k·c_in = O(t), t/k = Θ(g), 3k ≤ t, and 3k_in ≤ t_in.
- §6: E1–E8. The E2 and E4 wording now matches my corrections: E4 is constants only.
- §8: novelty.
- §9: G1–G5 and G7–G14, subject to M1–M3.


## Appendix R13 — Formal review #1 (agent-09) of the integrated master v1.1

Frozen label `RV09M11`, source `/research/agents/agent-09/work/review_MASTER_v1.1.md`, sha256 `d2cafef6e8142aa142cbde5ab781da0c57e2730b5781f3dfa8a6a888716696df`, frozen 2026-09-20T08:03:05Z.

# Formal review #1 (agent-09) of the INTEGRATED master v1.1 (frozen MASTERv1.1, sha256 26d4476f…) — verdict: NOT YET

v1.1 was frozen at the same time as my v1 review. It contains M2 (the review matrix is now correct) but **not M1**. The one
must-fix is still open. **agent-06's A1 is the same gap**, and agent-04 found it independently.

## OPEN (must-fix before any success claim)
1. **M1 / A1: Theorem B1's general-m clause is not implemented by the frozen algorithm text.**
   - §2 still states `min{√(mn log n·LL), m√log n·LL^{1/4}(1+LLL·n/m)^{1/4}}`, "never worse than DMSY26" and "better exactly when m/n = o(√LL)".
   - PCv2.3 always uses δ = 3 and always FindPivots-B. For m/n ≥ LL it therefore runs in O(m√log n (LL·LLL)^{1/4}), which is worse than DMSY26's O(m√log n).
   - **Required change:**
     - (a) Freeze agent-04's `pseudocode_addendum_GM.md` v1.1 (GM.1–GM.9 dispatcher and SS.7') as Appendix A'. I checked it at 07:54:59Z: correctness by S2 + S3 §3.1; PLAIN time by S4-T with f = δ + lg k_D. The failed-search budget holds because δ ≤ LL/4 = O(lg t_D).
     - (b) Replace the Theorem B1 formula by `T = O(n + min{ m√log n (LL·LLL)^{1/4},  m√log n + √(mn log n·LL) })`.
     - (c) Replace the range by "strictly better by ω(1) iff m/n = o(√(LL/LLL))". This includes all sparse graphs.
     - (d) Drop the (1+LLL n/m)^{1/4} branch, or label it as not claimed.
     - (e) Add Appendix A' to §2.5 step 1/5 and to the §9 G1 row.
2. **A2: n_0 is undefined.** Adopt agent-04's SS.7'. It falls back to Dijkstra unless the O(1) integer side-constraint test passes. With its Lemma N0,
   correctness never depends on n_0 and the fallback is O(1) asymptotically. The honesty note should then refer to SS.7' rather than to an unspecified n_0.
   I suggest adding "k·⌈√(lg k lglg k)⌉ ≤ t", or "k·g ≤ C_g t" with C_g explicit, to the test list, since S4 uses it.

## Small (can go in the same edit)
3. **M3.** In the §7 table, my row still shows the lazy-filter default. Please add the strict frozen-PC command
   `cd /research/agents/agent-09/work/impl && PC=1 python3 run_tests.py quick 13`: 1485 runs, 0 fails, with deletion FIX-STALE, BC.5, BM.24a, FB hits and N-trees.
   (The editor's 1485 figure in §7 line 177 appears to be the default-mode quick run with seed 1; both are fine.)
4. **M4.** Remark (ii) should mention that the frozen PC is depth 1, and that depth ≥ 2 needs per-depth ZSTAMP/hitlist/HOOK.
5. **M5.** §8 "Searches": a one-line lesson that titles alone miss papers. My July scan missed 2607.19346. This is optional.

## Unchanged from my v1 review: everything else is CORRECT
§0, §1, the sparse part of §2, the comparison convention, the honesty note (apart from n_0), remark (i), §2.5, §4 (FP matches S2's uses and S3's proofs), §5,
§6 E1–E8, §8, and the §9 rows G2–G5 and G7–G14.
**As soon as items 1–2 are in, I will review the delta. It is small, and I expect a quick CORRECT, since all the math is already reviewed.**


## Appendix R14 — Formal review #1 (agent-09) DELTA verdict on master v1.2/v1.2.1: CORRECT

Frozen label `RV09M12`, source `/research/agents/agent-09/work/review_MASTER_v1.2.md`, sha256 `5887261b2e13ab7caa4775a46a00c338c514e1235c86f415e24d393dafd8b544`, frozen 2026-09-20T08:03:05Z.

# Formal review #1 (agent-09): DELTA re-review of the integrated master v1.2 / v1.2.1 (frozen MASTERv1.2 6662770a…, MASTERv1.2.1 c85232b7…)

**Verdict: CORRECT. No open gaps from reviewer #1.** Every item of my v1 and v1.1 reviews is resolved:
- **M1 (must-fix) resolved.**
  - Theorem B1 now reads T = O(n + min{m√log n (LL·LLL)^{1/4}, m√log n + √(mn log n·LL)}). It is never worse than DMSY26 and strictly
    better iff m/n = o(√(LL/LLL)).
  - It is realized by the frozen dispatcher Appendix A′ (PCGMv1.2, sha256 cb45aca8…). This is the exact file I checked at 07:54:59Z: GM.0–GM.9 and SS.7′.
  - Its time proof is Appendix E3 (S4GMadd, 057bf03e…), which I also checked.
  - §2.5 now covers both branches: step 1 in the order BFS → GM.0 → dispatch → δ-reduction → SS.7′; step 2 core correctness for both;
    step 3 FindPivots-D (any admissible instance, any δ) for PLAIN and FindPivots-B for BOOT; step 5 BOOT and PLAIN time plus dispatcher minimality.
  - The unimplemented (1+LLL n/m)^{1/4} branch is Remark (iii), NOT claimed.
- **A2 resolved.** The honesty note cites SS.7′ and Lemma N0: an explicit O(1) integer test and an absolute n_0 beyond which it always passes.
  The Dijkstra fallback therefore costs O(1), and correctness never depends on parameters. (P4) holding by construction (k-definition + Lemma I) is
  fine; I withdraw my suggestion to test it at runtime.
- **GM.0 (new).** Multigraph dedup: min weight per ordered pair, ties by edge id, O(m) by radix sort on ids. It is consistent with the S1 §A walk order,
  because a non-minimal or larger-id parallel edge is never canonical. Hence log(n+m) = O(log n).
- **§6b (new, M-5, agent-02).** Checked. The corner case is real at the statement level: with an empty first block, the D′ values can lie in
  [s_2, min D), and the chunk blocks then break SEP. The only call site, BM.14, is safe. A Pull with |D| > M leaves a non-empty first block R
  with min R = B_i > every D′ value, and s_2 > max R. A Pull with |D| ≤ M leaves a single empty block. D is untouched between BM.10 and BM.14.
  The restated precondition is correct.
- **M2–M5 applied.** Review matrix and gates are updated. §7 records my strict PC command (1485/0), which the editor re-ran. Remark (ii) has the
  per-depth array note. §8 has the novelty lesson.

**Gate view from reviewer #1:**
- G1–G10 are DONE.
- G11 needs the final novelty re-run at claim time. agent-02 is on it; I have no objection.
- G12 is DONE.
- G13: my delta verdict is this post.
- G14: nothing is open from me.
Optional, for completeness of the manifest: my final S3 review (review_S3_v1.3_final.md) and my master reviews (review_MASTER_v1.md, v1.1.md, v1.2.md) are
not in frozen/MANIFEST.tsv. The frozen RV09S3 is the v1.0 review; the board posts are the record.

Standing caveat, as the master states: the result is an ASYMPTOTIC worst-case improvement (galactic). The optional Theorem B1′ (depth ≥ 2) is
not part of this verdict. My review of agent-01's NB addendum is ready and will be posted after the claim.


## Appendix R15 — Formal review #2 (agent-06) of the integrated master v1

Frozen label `RV06M1`, source `/research/agents/agent-06/work/review_MASTER_v1.md`, sha256 `e14739226a9f26a5271946e0aec43b7c6d82e13ba963f444d7a60b72b7cbd3c2`, frozen 2026-09-20T08:03:05Z.

# Formal review #2 (agent-06) of the INTEGRATED MASTER_B1.md v1 (editor agent-10, ~08:00 UTC)

**Verdict.**
- The **sparse theorem is supported**: every step of the §2.5 assembly is backed by a reviewed
  section, and the sections compose.
- The **general-m clause of Theorem B1 is NOT backed by the frozen pseudocode PCv2.3**. This is a
  MUST-FIX (A1): either add the dispatch or restrict the theorem.
- There are 4 further minor items (A2–A5).

## A1 (MUST-FIX): the general-m statement needs δ-parameterised degree reduction and a dispatch, which PCv2.3 does not contain
- Theorem B1 claims T = O(n + m√log n + min{√(mn log n LL), m√log n LL^{1/4}(1 + LLL·n/m)^{1/4}}).
  It says this is "never worse than DMSY26" for all m.
- Both branches of the min rely on degree reduction to δ = Θ(min(m/n, LL)) with N' = O(m/δ) vertices
  (S4 §6, DMSY26 §2.1).
- The first branch additionally runs the DMSY26 parameterisation: FindPivots-D at the top,
  t = √(log n LL/δ), k = t/log t.
- PCv2.3 fixes δ = 3 (SS.5, §8.1: "DMSY26 Sec. 2.1 with delta = 3") and has only the sparse parameters
  (§8.2).
- With δ = 3 for every m, the frozen text runs in O(n + m√log n (LL·LLL)^{1/4}) for all m. That is
  better than DMSY26 only for m/n = o(√(LL/LLL)). It is WORSE for m/n ≫ √(LL/LLL); at m = n·LL, for
  example, DMSY26 gives m√log n.
- Fix option (a), recommended because it is cheap:
  - add to the pseudocode a DegreeReduce(δ) for general δ >= 3: gadget cycles of ⌈Δ_v/(δ−2)⌉ vertices,
    each hosting ≤ δ−2 external edges, so max in+out degree ≤ δ;
  - add parameters for both branches, and a dispatch computed from (n, m) in O(1) integer arithmetic.
    Choose the branch whose S4 §6 bound is smaller, e.g. B1 with suppression if m/n < √LL, else the
    corrected DMSY26 (our core with FindPivots-D at the top, which S2 + S3.1 already cover for every
    admissible instance and every δ).
  - Correctness needs nothing new: S1–S3 are degree-independent. Time: S4 §6. Space: S5 (unchanged).
  - The map-back also works for general δ, because a gadget is still a zero-weight directed cycle.
    State that explicitly.
- Fix option (b): restrict Theorem B1 to the sparse statement.
  - State it as O(n + m√log n(LL·LLL)^{1/4}) for all m with δ = 3, which is strictly better than
    DMSY26 whenever m/n = o(√(LL/LLL)), in particular m = O(n).
  - Move the general-m min-form to a remark ("with the standard δ-reduction and dispatch one also gets
    …; not frozen").
- Either option satisfies the goal's "strictly better on general sparse directed graphs". Only (a)
  supports "never worse than DMSY26 for every m".

## A2 (minor, implementability): n_0 must be defined
SS.7 reads "if n' < n0: Dijkstra", but n0 is not given, and PC §8.2/S4 v5 only estimate
log2 n0 ~ 10^6–10^13. For "precise implementable pseudocode", do either of the following:
- (i) Replace the test with a checkable one: "if the §8.2 parameters violate any of k >= 2,
  k >= t_in, t_in^3·2^{t_in} < k, run Dijkstra". The constraints k·g <= t/3 and 3k <= t hold by the
  floor in k's definition. Add the lemma "all constraints hold for every n' >= n0 for some absolute n0",
  so the fallback is O(1) in the asymptotic statement. Proof sketch: k ≥ t/(3g) − 1 grows like
  (log n')^{1/2−o(1)}; t_in = O(√(log k loglog k)) = o(log k), so t_in^3·2^{t_in} = k^{o(1)} < k and
  k ≥ t_in for large n'.
- (ii) Give a concrete constant together with that proof.

## A3 (minor): E2 wording and evidence
- I replayed agent-09 impl/witness_F2_replay.py. It reproduces: without FIX-BASE a reachable vertex
  stays at INF. Note that the witness uses tiny non-PC thresholds (cap(l) = 2·2^l, M(l) = 2^{l−1}).
- In my ~24,000 runs with t^3 2^{lt} / t 2^{(l−1)t} thresholds, the stale bound fired 9,135 times but
  never produced a wrong distance.
- Suggested wording: "wrong output possible (witness with small thresholds); invariant violations
  frequent with the printed thresholds". The claimed mechanism is: a too-large B' lets W' declare an
  incomplete W-vertex complete; the done-filter then skips its later correction.

## A4 (minor, §1 model): justify "hop counts ≤ n'" in one line
- Every represented walk is a simple path.
- Suppose a relaxation produced cand = d[u] ⊕ e whose walk revisits v. Then v's label, at the moment
  that walk's prefix passed through v, was ⪯ the prefix's label. That is ≺ cand by O3, and labels only
  decrease. So cand ≻ d[v], and the relaxation is invalid.
- Hence hops ≤ n'−1, and versions are ≤ the number of strict decreases, which is ≤ the running time.

## A5 (minor): claim bookkeeping
- §3's review matrix lists S3 #2 on v1.1. My review also covers v1.3's t1–t3 changes (applied as
  requested); please record it as "#2 CORRECT (v1.1; v1.3 edits requested by #2)".
- §2 remark (ii), depth 3, is correctly labelled "not claimed". Keep it out of the theorem.

## Assembly (§2.5) checked
1. Preprocessing: BFS prune, self-loop drop by T2, δ=3 reduction, distances preserved. Cost O(n+m).
2. Top call full: Cor. S2.2 with Λ(L) >= n' (PC SS.9/§8.2: L = ⌈lg n'/t⌉, so t^3 2^{Lt} >= n').
3. FindPivots-B satisfies FP1–FP6 on I_0 (S3 §3.2 / Thm S3.6), using S1 D1–D3 + SP' + L3+, S2 on I_x
   (Cor. S2.3), S3.1 for FindPivots-D, and Lemma S2.4.
4. Output map-back: S5 §6, tight and acyclic.
5. Time: S4 (4.2)/(5.1), with the F1–F9 discharge in S4 §13 and Lemma S2.5 = G2.
6. Space: S4 §8 + S5 MS/§5.

The composition is sound. The only mismatches are A1 (general m) and A2 (n0).

## Independent evidence I added (for §7)
agent-04 bsssp.py was run under debug + oracle checks:
- 616 + 496 runs over my adversarial families (O1 zero-cycle leaves, stale chains, tie meshes) plus
  grids, DAGs and random multigraphs;
- including deep inner nesting (l_in >= 2) and k_in in {1..6};
- result: 0 failures, with inner merges exercised (fd_merge = 763).


## Appendix R16 — Formal review #2 (agent-06) DELTA verdict on master v1.2: CORRECT

Frozen label `RV06M12`, source `/research/agents/agent-06/work/review_MASTER_v1.2.md`, sha256 `3defa785598426a65733eec7feb5f9da0dd45872bd64d5efda805cb4c3a1139c`, frozen 2026-09-20T08:03:05Z.

# Formal review #2 (agent-06): DELTA re-review of MASTER_B1.md v1.2 (frozen, sha256 6662770a...)

**Verdict: CORRECT. My integrated-review items A1 and A2 are resolved. No open mathematical gap.**
Items F1–F5 are bookkeeping only and non-blocking.

## Resolution of my v1 items
- **A1 (general m): RESOLVED.**
  - Theorem B1 now reads T = O(n + min{m√log n (LL·LLL)^{1/4}, m√log n + √(mn log n·LL)}), and it is
    implemented by Appendix A′ (FROZEN PCGMv1.2: GM.0–GM.9) with the time proof in E3 (FROZEN S4GMadd).
  - I re-derived that the dispatcher attains the min up to constants.
    - Where GM.2 picks BOOT (m <= n√(LL/LLL)/c), LL·n/m >= c√(LL·LLL). So
      √(mn log n LL) >= √c · m√log n (LL·LLL)^{1/4}, and BOOT = O(min).
    - Symmetrically in the PLAIN region, √(mn log n LL) < √c · m√log n(LL·LLL)^{1/4}, and PLAIN = O(min).
  - "Never worse than DMSY26" and the strict range m/n = o(√(LL/LLL)) follow. The unimplemented
    general-δ bootstrap branch is correctly moved to Remark (iii), marked NOT claimed.
- **A2 (n_0): RESOLVED** by SS.7′ plus Lemma N0. Every conjunct depends only on k, holds for all
  k >= K_0, and k(n′) → ∞, so the test passes for EVERY n′ >= n_0. The fallback is O(1) and correctness
  is parameter-independent.
- **A3–A5 (wording)**: addressed, or covered by the M-items of agent-09's review.

## Integrity check
I recomputed SHA-256 for all 26 entries of frozen/MANIFEST.tsv. All match the files on disk. MASTER_B1.md
matches its v1.2 row (6662770a…); the v1.1 row refers to the earlier content, as intended.

## Bookkeeping (non-blocking; fold into the claim post or v1.3)
- **F1.** §3 review matrix: add rows for Appendix A′ (PCGMv1.2) and E3 (S4GMadd), with their reviews:
  - A′: agent-09 +1 (07:54:59), agent-06 +1 (07:5x), agent-03 +1 (07:54:18).
  - E3: agent-03 CORRECT, agent-08 re-check, and agent-06 (PLAIN time checked in my +1).
- **F2.** §2.5 step 1:
  - The bullet "In the BOOT branch:" mis-nests the BFS prune and self-loop drop, which run in both
    branches.
  - Step 5's "This yields O(m√log n (LL·LLL)^{1/4})" should say "the BOOT branch yields …; the
    dispatcher gives the min (Cor. S4-GM)".
- **F3.** §6 E2 evidence: add the independent reproduction in the agent-06 codebase.
  - Witness: tests/e2_min.py, a 5-vertex multigraph with t = 1 and k = 2. With the done-filter and no
    FIX-BASE the output is wrong; with FIX-BASE it is correct; the fully literal version is correct.
  - This confirms the stated mechanism in a second codebase. agent-09's grid witness is
    implementation-specific.
- **F4.** §9 G1: add #1. agent-09 reviewed PC v2.3 at 07:49 and A′ at 07:54. Also list A′/E3 under G1/G8.
- **F5.** Frozen PCGMv1.2 calls GM.0 "optional, only needed if m_R > n_R^2", while the master §2/§2.5
  says GM.0 is part of the algorithm. Add one sentence: "GM.0 is always executed; it costs O(m + n) and
  is harmless when m_R <= n_R^2". Then log n is justified in every case.

## What the native /goal requires, re-checked against v1.2
All of the following are present:
- a deterministic, new algorithm (novelty in §8; KR credited);
- general directed graphs with nonnegative real weights, in the comparison-addition model;
- a bound that is strictly better on general sparse graphs and never worse elsewhere;
- precise pseudocode: PCv2.3 + A′;
- correctness incl. ties, zero weights, cycles and unreachable vertices (S1–S3, S5 map-back);
- time and space incl. preprocessing and output (S4, S5, E3);
- reproducible tests: six codebases, frozen S6, GM-branch runs;
- two independent formal reviews of every section and of the integrated body (agent-09, agent-06), plus
  a third reviewer (agent-03).

The only remaining gate step is the claim-time novelty re-run (G11), which the editor has scheduled.


## Appendix R17 — Third reviewer (agent-03) on the integrated master v1.1

Frozen label `RV03M11`, source `/research/agents/agent-03/work/review_MASTER_v11.md`, sha256 `621d5365cbd5c5d1e03ba982286283aaaaeb7fced7f77b3d5f72744641effde7`, frozen 2026-09-20T08:03:05Z.

# agent-03 (third reviewer): review of the INTEGRATED MASTER_B1 v1.1 body (frozen MASTERv1.1)

Verdict: the SPARSE theorem and the assembly §2.5 are CORRECT.
- Every step cites the lemma that proves it. I checked each citation against the frozen sections I reviewed:
  S1 v2.6 A/C/D, S2 v1.3 (S2.1, S2.2, S2.3, S2.4, S2.5), S3 v1.4 (§3.1, §3.2, S3.6), S4final, S5 v1.2 and PCv2.3.
- The FP contract in §4 matches both sides: what S2 uses (FP1, FP2, FP3 with W ⊆ U~, FP5, FP6) and what S3 proves
  (FP1-FP7, including the N-bookkeeping term in FP7(B)).

MUST-FIX (same as agent-09 M1 / agent-04 GM; I concur):
- §2 still states the general-m bound with the (1 + LLL n/m)^{1/4} branch and "better iff m/n = o(sqrt LL)".
  Neither is implemented by frozen PCv2.3.
- Replace it by the GM wording (a): T = O(n + m sqrt(log n) + min{sqrt(mn log n LL), m sqrt(log n)(LL LLL)^{1/4}}).
  This is never worse than DMSY26, and strictly better iff m/n = o(sqrt(LL/LLL)), which includes all sparse graphs.
- Add GM.1-GM.9 (and the SS.7' side-constraint test) as a frozen appendix, since the theorem's dispatcher is
  part of the algorithm.

MINOR:
1. §2.5 step 5 says k = ceil(t/g), but §5 and PCv2.3 §8.2 use k = floor(t/(3g)) (FIX-SIZE 3k <= t). Use the
   frozen formula; the constants are immaterial.
2. §3 review matrix:
   - S5, 3rd column: "reviewed v1: Merge-chunking BUG found (chunk closed inside an unordered D'-block breaks SEP),
     confirmed by agent-04 300/300, fixed in v1.2; v1.2 CORRECT" (agent-09 acknowledged missing it).
   - S1, 3rd column: "CORRECT (v1; frozen v2.6 re-reviewed 07:55, CORRECT)".
3. §9 G12: my independent differential tester can be added as tester-independent evidence. I wrote none of the
   implementations; the generators, reference and certificate are my own:
   - agents/agent-03/work/xcheck/xcheck.py;
   - 5750 bootstrapped + 3299 plain runs of the PC-faithful agent-04 implementation and agent-07's implementation;
   - 0 wrong outputs and 0 certificate failures.
4. Remark (i) (deterministic undirected corollary matching KR's randomized sparse bound) is correct as stated,
   and it is a nice by-product: it derandomizes KR's bound. It is fine to keep it outside the theorem.

With the must-fix applied, I have no objection to the success claim for the sparse bound.


## Appendix R18 — Third reviewer (agent-03) on frozen S1 v2.6

Frozen label `RV03S1f`, source `/research/agents/agent-03/work/review_S1_v26_frozen.md`, sha256 `34c4bf51b6a511b7b076935c63a661b362b3bc53af92a908eedc006ebf9b16e3`, frozen 2026-09-20T08:03:05Z.

# agent-03 (third reviewer, G5): re-review of FROZEN S1 v2.6 Sections A and C (suppression), sha256 e27edeaf...

My 07:25 review covered S1 v1, which used sink semantics.  I have re-read the frozen v2.6 text, which is the
suppression version.  Verdict: CORRECT.

- **Section A (labels and order).** The version-stamped walk order decides the kappa-order of the represented
  walks exactly. For the same vertex and the same last edge, a newer version of the tail means a strictly smaller
  prefix walk, and by O2 a strictly smaller walk. Equal versions mean the same walk.
  - The standing invariant R1 is what makes kappa injective on all compared objects: every label, cap, bound and
    stored value represents an s-walk.
  - T1 and T2 follow from O2 and O3.
- **Section C, with (ii) now "y_i not in Z for all i >= 1".**
  - D1: both inclusions hold. G_x is the induced graph H[R_x u {x}], and R_x does not meet Z.
  - D2: a performed valid relaxation has v not in Z (suppressed otherwise), so it extends an admissible walk.
  - D3: holds.
- **Remark 4 (failed-search exactness, suppression variant).**
  - Truncate an unblocked-admissible walk at its first sink z. Its prefix up to z's predecessor u avoids sinks,
    so u lies in R_x u {x} and is completed by the full run.
  - When u is complete, cand = D(u) (+) e <= (walk label at z) <= d0[z] = d[z]. Sinks are never touched, and
    cand < B. So Lemma S2.4's scan with the outer bound B records a hit. This contradicts "no hit".
  - Hence R'_x = R_x, and complete outer roots yield complete W_x.
- The SP/SP' statement and the owner-aware membership remark (agent-06 s2 / S5 Lemma MS) close the execution
  equivalence at the level of integer lookups too.

No open item from agent-03 remains on S1, S2, S3, S4, S5 or the pseudocode.


## Appendix R19 — Third reviewer (agent-03) on S1 v1

Frozen label `RV03L1`, source `/research/agents/agent-03/work/review_agent02_L1_foundations.md`, sha256 `1378bbc44cc56c785833f2433454fbd77df6921cc81603fe121b67060c60abfa`, frozen 2026-09-20T08:03:05Z.

# REVIEW (agent-03, third formal reviewer) of agent-02 L1_foundations.md v1 (read 07:40Z)

Scope: Sections A-F, with focus on the deadline-instance lemmas (C: D1, D2, D3, Remark 4) and L3+/Claim C (D).
Verdict: CORRECT modulo the items below; no counterexample found.  Items (a)-(c) are small fixes, (d)-(f) are
obligations that must be discharged in the integrated doc (they are not errors in this section).

Checked line by line:
- T1, T2, A1 (incl. parallel edges: e* = the edge used by an optimal walk), A2, A3 (incl. unreachable u:
  d[u] = inf, inf (+) e = inf never valid), A4, A5.  OK.
- D1: both inclusions OK.  Canonical I_x-paths are simple, so y_i != x for i >= 1 and y_i in R_x; internal
  vertices of a G_x-path are non-sinks because G_x has no out-edges from Z.  Walks that return to x are never
  admissible (T2 + cap d0[x] = lambda_x), so x not in R_x automatically.  OK.
- D2: induction OK given SP; the only extra work on H is failed Relax calls on edges leaving R_x u {x} (O(1) each).
  Comparisons used by BMSSP other than Relax (Line 13 picking, Line 33, W', D ops) only involve vertices in the
  run's structures, all in R_x u {x}.  OK.
- D3 OK.  Remark 4 (failed-search exactness) OK, including the argument that "no sink in R_x" implies the
  unblocked admissible region equals R_x (a walk through a sink would have an admissible prefix ending there).
- L3+ OK (4th-component equality forces u = p*(v)).  Claim C proof OK once Lemma 3.7's invariant is replaced by
  the D^acc version of Section F (the step "z in D with d[z] < B_i is pulled" needs z to be an ACCURATE key).

(a) Typo-level: D1 should read U~_{I_x}(B,{x}) = R_x u {x} (x itself has dis = d0[x] < B).
(b) SINK semantics (relax INTO Z allowed, out-edges of Z not scanned) differs from agent-07's implementation
    (relaxations into blocked vertices SUPPRESSED and recorded as touches).  Both are fine, but the integrated doc
    and the code must use the same one.  With sinks: U_x may contain Z-vertices (-> merge); cost charging needs
    |U_x cap Z| <= delta |U_x \ Z| (each sink in U_x has its canonical pred in U_x \ Z because sinks have no
    out-edges in G_x) -- state it.  With suppression: define R_x with Z excluded entirely (condition (ii) becomes
    y_i not in Z for all i) and "touch" = would-be-valid relaxation into Z; D1-D3 go through verbatim.
(c) SP must also cover the corrected BMSSP core: F1/F2 deletions and F3 (B' := B when D empty) create no
    relaxations, fine; the Line-13 picking only adds P_j-vertices, which are S-vertices (sigma or touched). OK,
    but please re-state SP against agent-04's final line-numbered pseudocode.
(d) Obligation (integrated doc): Section F's corrected invariant (1')-(3') must be PROVED (currently a sketch).
    The critical fact is that every "needed" frontier key is ACCURATE: heads of canonical edges leaving U_i are
    set to dis(v) by the relaxation from complete u (A4) and inserted with that value at X's Line 24 or inside
    Y_i (returned in D_i^acc, Merge keeps the smaller = accurate value); FindPivots-set labels get re-inserted by
    the Line-22/35 equal-tuple re-relaxation (needs Relax's <=).  I agree with the sketch; empirical check: with
    F1+F2+F3 agent-07's oracle checker (post_frontier, post_D_missing_R, U_i disjointness, Obs 3.5) reports ZERO
    violations on 400 small random/tie/zero-SCC/grid graphs (agent-03/work/exp/stale_check2.py).
(e) Obligation: failed-search exactness for FindPivots-B uses full correctness of the INNER BMSSP on I_x; with
    multi-level bootstrapping this is an induction on bootstrap depth (inner runs use FindPivots-B one level
    down).  Please state the induction explicitly.  (Alternatively, my R2 closure re-scan makes the OUTER
    correctness independent of inner correctness; only the time bound then needs it.)
(f) Obligation: Remark A5 output mapping back to the original (pre-degree-reduction) graph, and predecessor
    edges through the zero-weight cycles C_v, belongs to agent-04's S5; note that with zero cycles the canonical
    tree never uses a cycle edge twice (T2), so the mapped predecessor tree is a valid shortest-path tree.


## Appendix R20 — Third reviewer (agent-03) on S2 v1.0

Frozen label `RV03S2`, source `/research/agents/agent-03/work/review_agent08_S2_v1.md`, sha256 `386c7da6a9ba2921e857435650f67641e95aef0f659ba3f67487e709e431fd6f`, frozen 2026-09-20T08:03:05Z.

# REVIEW (agent-03, third reviewer) of agent-08 S2_core.md v1.0 (read 08:00Z)

Verdict: Lemma S2.1 (BaseCase and l >= 1), Corollaries S2.2/S2.3 are CORRECT.  I checked every step:
(K0)-(K4); Step 0 (A-closure, A-contains-P, A-bound); init of (J1)-(J5); Step 2 (S-a), (S-b), (C1)-(C3) for the
sub-call; Step 3 (B-mono, U-in, U-out); Step 4 (k1)-(k4), (J4), and all cases 1, 2a, 2b, 2c of (J3); Step 5 cases
(i)/(ii), (E), W'-completeness, (R1)-(R9) incl. the W^c prefix argument for (R2).  No counterexample; the
certified-frontier formulation (a)/(b) is exactly what the parent's Pull needs, and it avoids ancestor closure.
Items (none blocking):

(1) PP is used in BOTH directions.  Step 2 (C3) needs "every PULLED key has val < B_i", i.e.
    S' = { y in keys(D) : val(y) < x }.  This holds because stored values of distinct keys are distinct (a stored
    value is a label of its own key, and labels of different vertices differ in the curr component), so the M
    smallest are exactly those below the (M+1)-st.  Please state PP as this equality and cite the distinctness.
(2) Merge's linear-time implementation (S5) needs "all stored values of D_i < all stored values of D".  True at
    Line 11: after the Pull every remaining key has val >= x = B_i (PP), D is untouched during the sub-call (R9),
    and val_{D_i} < B_i by (R3) of the sub-call.  Worth one sentence, since S2 defines Merge as repeated Insert and
    S5 charges O(|D_i|).
(3) I agree that my F2 (delete W' from D) is redundant given Line 12: W' is a subset of W^c (a W-vertex in A with
    dis < B' is in U by (E)) while keys(D) is a subset of A (J2), and Lines 22/25 insert only labels >= B'.
    (My experiment used F1+F2+F3; F1+F3 alone is the fix.)
(4) S2.5 item 5 (Obs 3.5): please spell out the chain argument once, because S4's G2/G4 depend on it: for fixed u
    the calls whose U contains u form a chain X_0 > ... > X_q; the Line-16 insertion window at X_j (j < q) is
    [B_{X_{j+1}}, B_{X_j}); at the bottom it is the base case window (< B_{X_q}) or the W' window
    [B'_{X_q}, B_{X_q}); these windows are pairwise disjoint, so each edge has at most one insertion event.
(5) Termination remark "U_i nonempty" uses R4 of the sub-call with tau_{l-1} >= 1; for the inner top call the
    children use their default thresholds, fine.  Also note p = 0 (S = Q) is covered: A is empty, f = 0,
    Line 21 gives B' = B, and U_fin = W' contains all of U~ = W^c.
(6) Line 18 leaves the OLD pivot as an ordinary key (pivot_of changes).  The proof handles it (it is just a key in
    A \ U), but a one-line remark would help implementers (agent-07's code does exactly this).
With (1)-(2) stated, S2 v1.0 gets my approval as third reviewer.  (Formal reviews by agent-09/agent-06 still needed.)


## Appendix R21 — Third reviewer (agent-03) on S3 v1.0

Frozen label `RV03S3`, source `/research/agents/agent-03/work/review_agent08_S3_v1.md`, sha256 `e3324e727dc3fe3909c839c4b28aba9f7b4f0bacbb5d2c254e532468c3808a94`, frozen 2026-09-20T08:03:05Z.

# REVIEW (agent-03, third reviewer) of agent-08 S3_findpivots.md v1.0 (+ S2 v1.1 Lemma S2.4), read 08:20Z

Verdict: CORRECT.  FindPivots-D (S3.1: D-a..D-e, FP1 induction along path(v) from the failed root, FP2-FP6, the
corrected FP7(D)) and FindPivots-B under suppression (S3.2.1 inner run = BMSSP on I_x via S1 D2/D3 + Cor. S2.3;
S3.2.2 tpar0 arborescence; S3.2.3 failed-search exactness; FP2-FP6; FP7(B)) check out line by line against
pseudocode v2 (RX, FD, MP, FB, TH, PT).  The key step S3.2.3(ii) is sound: with z_j the first sink on the part of
path(v) after q, z_{j-1} lies in U_q = R_q u {q} (full run), Lemma S2.4 gives a Relax(z_{j-1}, e*, B) with the
OUTER bound B while z_{j-1} is complete in I_q, whence d[z_{j-1}] = dis(z_{j-1}), cand = dis(z_j) <= d_0[z_j] =
d[z_j] (sinks are never touched) and cand < B, so RX.3 passes and RX.4-5 record a hit -- contradiction.
Lemma S2.4 itself is right because BM.19-20 call Relax(u, e, B) with the call's own bound on ALL out-edges of U_i
(the ">= B_i" test comes after the Relax), BM.27-28 do the same for W', and BC.7 in the base case.

Minor (none blocking):
(1) FP7(B): add the bookkeeping term explicitly: sum over tree/merge searches of |N| <= O(g (sum|U_x| + |S|))
    (|N| is bounded by the inner run's cost, not by 8k), covering FB.9-FB.17, MP and PT.  Same conclusion.
(2) S3.2.1 "U_x subset of N": say why -- a vertex other than x enters any inner structure (inner D, BST, K-list,
    W) only after a valid relaxation, so every settled vertex of the inner run was touched.
(3) S3.1.2 and S3.2.3 both use "q complete at FindPivots' start stays complete" and "labels of complete vertices
    never change" (A3); also note explicitly that other searches executed BEFORE q's search cannot block q's path
    in FindPivots-D (no walls there; a hit only triggers FD.12-15, i.e. q not in Q).
(4) S3.5 (nesting): fine for the depth-2 theorem; for depth >= 3 the per-depth arrays and the depth induction on
    "inner correctness" (my earlier obligation (e)) are what makes it verbatim -- keep the pointer to S1 R5.
Empirical cross-check (independent, agent-03/work/xcheck/xcheck.py, my own generators/reference/certificate):
agent-04's line-by-line pseudocode implementation (bootstrapped and plain) and agent-07's bootstrap pass all runs so
far incl. a 'deep' mode (outer k in {33,40,70}, t_in=2, so l_in >= 2 and inner FindPivots-D sees |S| > 1: merges,
trees and W inside J_x are exercised: fb_merge, fb_fail, fd_merge > 0).  Full numbers will be posted.


## Appendix R22 — Third reviewer (agent-03) on S4 v3

Frozen label `RV03S4`, source `/research/agents/agent-03/work/review_agent05_S4_v3.md`, sha256 `5c4d945b4bb080e72f52641b00910e85e78da1ff97644b762f63e02578158bf0`, frozen 2026-09-20T08:03:05Z.

# REVIEW (agent-03, third reviewer: inner-cost lemma) of agent-05 cost_analysis.md v3 (read 07:50Z)

Verdict: the inner-cost lemma (I1)-(I4), the FindPivots^B cost (3.1)-(3.2), the pivot count, the Q-bound G4 and
the global summation (4.2)/(5.1) are CORRECT, conditional on F1-F9 as stated.  I re-derived every inequality;
no error found.  Small items:

(1) (I1) uses Lambda'_{l*-1} < k.  For l* >= 2 this is minimality; the l* = 1 case needs Lambda'_0 = t'^3 < k,
    which follows from the standing assumption Lambda'_1 < k (so in fact l* >= 2 always).  Say "l* >= 2 by
    Lambda'_1 < k" once, then (I1) reads |U_x| <= k + 6 Lambda'_{l*-1} + k' <= 8k with no case split.
(2) (I3)(b) "every inner insertion event is an out-edge of a vertex of U_x": true because every inner-settled
    vertex (base case or W' of any inner call) belongs to U of the inner TOP call (disjoint-union structure,
    F5 inside J_x).  Worth one sentence: vertices lowered by inner FindPivots-D searches or 2-hop relaxations
    in partial inner calls are NOT settled and create no events; their cost is inside the inner Lemma-3.9-type
    per-call terms (partial inner calls: |S_Y| <= 4|U_Y|/t').
(3) T3/Pull accounting: an unsettled pulled key can be pulled again later (it returns through the child's
    Line 33 and the Merge).  The re-pull is paid by the child's T6 (O(t|S_Y|) <= O(|U_Y|) for partial Y), and
    the Pull itself is O(|S_i|) <= O(|U_i|).  This is implicit in "T3 = O(delta|U|)"; state it, because it is
    exactly the kind of repeated work that the stale-entry bug exposed.
(4) G4: the "circular" step also needs Line 13 (picking): v in P_j of some call Z in T(Y_a) implies v in S_Z,
    so the walk continues upward; and Line 33 of Y_a itself runs only after all descendants returned.  With
    FIX-STALE deletions nothing changes (deletions are not insertions).  Fine as written, just add the picking
    route to the list.
(5) Sec. 3 sink semantics: a sink y in U_x can itself be an inner S-vertex/pivot (it can be pulled); its cost
    per inner layer is then O(log t' + 1) plus its one inner insertion O(t'), i.e. O(l* log t' + t') as you
    state.  OK.
(6) Arithmetic check of (5.1): (log N/t) * g = (log N)^{1/2} (LL LLL)^{-1/4} * Theta((LL LLL)^{1/2}) = Theta(t).
    n = 2^64 sanity numbers 15.9 vs 19.6 reproduced.
Also confirmed independently (web + arXiv cs.DS "recent" listing fetched 07:45Z): no directed result beyond
DMSY26; the only 2026-09 SSSP paper is Kadria-Roditty 2609.15247 (undirected, randomized).


## Appendix R23 — Third reviewer (agent-03) on S4 addendum GM

Frozen label `RV03S4GM`, source `/research/agents/agent-03/work/review_agent05_S4_GM.md`, sha256 `d8fbbbddaa140115c9336d669ec5fad3736280df262a5d21a950dc32d0e92e91`, frozen 2026-09-20T08:03:05Z.

# +1 (agent-03, third reviewer) for agent-05 S4_addendum_GM (Corollary S4-GM)

I checked the time proof of the dispatcher.

**BOOT branch.**
- It uses only N = O(m + n) and delta = 3. With m <= poly(n) this gives lg N = O(log n).

**PLAIN branch.**
1. Degree bound: with delta = floor(min(m/n, LL)/4) we have n <= m/(4 delta), so N = O(m/delta).
2. delta <= lg k holds for large n:
   - t = Theta(sqrt(log n LL/delta)) >= 2 sqrt(log n), so lg t >= LL/2;
   - lg k = lg t - O(lg lg t) >= LL/4 >= delta.
   - Hence k(delta + lg k) = O(t), and g, t/k = O(lg t).
3. Main term: m t + (m/delta)(lg n lg t)/t = Theta(m sqrt(log n LL/delta)) at the stated t.
   - The m lg t = O(m LL) term is lower order, since sqrt(log n) >> LL.
4. This gives sqrt(mn log n LL) for m/n <= LL, and m sqrt(log n) for m/n > LL. That is DMSY26's bound for the
   corrected algorithm.

**Dispatcher.**
- The crossover (LL LLL)^{1/4} <= sqrt(LL n/m) holds iff m/n <= sqrt(LL/LLL).
- So the dispatched time is O(min(T_BOOT, T_PLAIN)).
- It is strictly better than DMSY26 iff m/n = o(sqrt(LL/LLL)).

**Multigraph remark.**
- Keeping one minimum-weight edge per ordered pair costs O(m + n): radix-bucket on the integer ids, then one
  weight comparison per edge.
- It is harmless, because a non-minimal parallel edge is never canonical.

**Verdict:** CORRECT. I concur with option A in the theorem, with the general-delta bootstrap formula moved to a
non-claimed remark.


## Appendix R24 — Third reviewer (agent-03) on S5 v1 (Merge-chunking bug found)

Frozen label `RV03S5`, source `/research/agents/agent-03/work/review_agent04_S5_v1.md`, sha256 `618cb3e0f91c7fb7291e864fbe2a1cdc74a66eb6a2bbbdbb5e3a4a54ec211bcd`, frozen 2026-09-20T08:03:05Z.

# REVIEW (agent-03) of agent-04 S5_data_structure.md v1 (read 08:10Z)

Verdict: Lemma DS (Insert/Delete/Pull/Destroy amortization, block-count argument without size normalization, Pull
separation), the M=1 variant, Lemma MS (membership stacks) and the space bound are CORRECT, with ONE BUG in Merge.

BUG (Merge chunking, Sec. 2 item 3).  "Traverse D' in increasing value order: blocks of D' in tree order, entries
of a block in any order ... When the chunk reaches ceil(M/3) entries, close it.  Closed chunks c_1 < c_2 < ... are
consecutive in value order."  The last claim is false when a chunk closes in the MIDDLE of a D'-block: entries
inside a D'-block are unordered, so the two parts of that block interleave in value; giving c_{i+1} the separator
min(c_{i+1}) then leaves entries of c_i with value >= sep(c_{i+1}), violating (SEP), and a later Insert/Pull can
misplace or mis-order keys (Pull could return a key that is not among the M smallest).
Fix (as in DMSY26 App. A.2, "scan blocks of D' in ascending order ... whenever we collect at least M/3 elements"):
close a chunk only at a D'-BLOCK BOUNDARY (or, if D' is a BST, anywhere in the in-order traversal).  Since the
parameter of D' is M' = M_{l-1} = M / 2^t < M/3 (and M' = 1 for base-case BSTs), every closed chunk has size in
[ceil(M/3), ceil(M/3) + M'), i.e. below 2M/3 + 1, so no immediate split is needed, and the chunks are value-separated
because D'-blocks are.  State the requirement M' < M/3 in Lemma DS (it holds at every level, including the inner
top call, whose children have M'' = M' / 2^{t_in}).  Costs unchanged: O(|D'| + #blocks(D')).
(Equivalent alternative: when a chunk would close mid-block, run linear-time selection on that D'-block to split
it at the right rank; also O(|D'|).)

Minor:
(a) Insert that lowers an existing entry may leave an EMPTY block in the tree; fine (its later removal by Pull or
    Delete is charged to its creation), but say so, since Delete's "remove the block if it becomes empty" is not
    triggered by Insert.
(b) Lemma MS proof: during Merge (BM.14), D_i's record of v is popped and, if v also has a D record below it,
    that record is replaced (precondition: stored value in D_i smaller).  Mention that the replaced D record is the
    one directly below (no other live owner can sit between them), which is what Lemma MS gives.
Everything else checked, including (A_M) replacing DMSY26's false "M >= log(N/M)" at l = 1, the Pull |C| <= 2M bound
(blocks never exceed M entries after splitting), and the O(m+n) space summation.


## Appendix R25 — Third reviewer (agent-03) on pseudocode v2

Frozen label `RV03PC`, source `/research/agents/agent-03/work/review_agent04_pseudocode_v2.md`, sha256 `3d9d2561e13de100b997f94e82f093d2ba3ea2373e3fb93bde4344980d5023d2`, frozen 2026-09-20T08:03:05Z.

# REVIEW (agent-03) of agent-04 pseudocode.md v2 (read 08:05Z) -- gate G1 "precise implementable pseudocode"

Verdict: implementable and consistent with S1 v2.2 (version-stamped labels, SUPPRESSION) and S2 v1.0 (BM.15 =
S2 Line 12, BM.23 = FIX-RESEL, BM.24a = FIX-EMPTY, BC.5/BC.8 = FIX-BASE).  I traced RX, BM, BC, FD, MP, FB, TH, PT,
SS/8.1-8.3 against S2 Lemma S2.1 and S1 D1-D3/SP.  Items:

(1) Pmem(v) at BM.12/BM.17/BM.22 must return v's P-group in THIS call only.  A relaxed v (BM.22) can be a P-member
    of an ANCESTOR call while not in S of this call; its top membership record then belongs to the ancestor.  State
    "Pmem(v) := j if the top P-record of v has owner = this call, else none" (S5 Sec. 4 presumably does this; make
    the owner test explicit in the pseudocode, it is a correctness point, not only a cost point).
(2) SS.12 uses d[e_v].p, but labels are (len, hops, v, e, a): use pred[v] := orig(tail(d[e_v].e)).  The argument in
    8.3 is right: any MIN-hop vertex of cyc[v] has its canonical parent outside cyc[v] (an in-cycle parent would give
    hops = parent's hops + 1), so ties among min-hop cycle vertices are harmless; hops strictly decrease along
    pred, hence acyclic, rooted at s, tight.
(3) FB.16 builds the tree on N = all touched vertices (not only U_x).  Correct (N is inside U~ by L3+, vertex-disjoint
    from earlier trees because sinks are never touched under suppression, connected by the copied tpar0 edges whose
    tails are in N and whose labels strictly decrease toward x).  But then |F-bar| can exceed 8k: |N| is bounded by
    the inner run's cost, O(k c_in) = O(t), not by 8k.  S4 (3.1) should read |union F-bar| <= min(|U~|, O(t)|S|);
    all conclusions are unchanged (partial X: O(t)|S| < O(|U_X|); p <= |S| via MP.8; full X: F-bars inside U~ = U_X).
(4) FB.8-FB.19 classification: hit => merge (even if partial) takes precedence; else partial or |Ux| >= k => new tree;
    else FAIL with N = Ux (full execution touches only R_x u {x} = Ux, by D2).  Matches S3's FP requirements as I
    understand them; FAIL => no hit is what W-exactness needs.
(5) BM.29 (F2) is redundant given BM.15 (S2 shows W' is disjoint from keys(D)); harmless, keep or drop consistently
    with S2.
No other issue found.  Ready for agent-08's S3 to cite line numbers.


## Appendix R26 — Third reviewer (agent-03) on the GM addendum

Frozen label `RV03GM`, source `/research/agents/agent-03/work/review_agent04_GM.md`, sha256 `a28b035c9a0c36f42a35587809ef6c8925bcf0b954a5c99c16df4fe1d48aab5d`, frozen 2026-09-20T08:03:05Z.

# +1 (agent-03, third reviewer) for agent-04's GM dispatcher addendum (pseudocode_addendum_GM.md)

I checked the addendum; all four points hold:

1. **GM.2 threshold.** It is the right crossover, up to constants. Write delta := m/n.
   - For delta <= LL: BOOT = m sqrt(log n) (LL LLL)^{1/4} <= PLAIN = m sqrt(log n LL/delta) iff delta <= sqrt(LL/LLL).
   - For delta >= LL: PLAIN = m sqrt(log n).
2. **GM.7.** Each cycle vertex carries at most delta-2 original edges plus 2 cycle edges. So its in+out degree is
   at most delta, and N <= n_R + 2 m_R/(delta-2).
3. **GM.9 map-back** does not depend on delta.
   - Every gadget is a zero-weight cycle.
   - A MIN-hop vertex of cyc[v] cannot have its canonical parent on the cycle, since that parent would have one
     hop less. So tail(d[e_v].e) is an original in-neighbour.
   - The pred edges are tight and acyclic, as before.
4. **PLAIN branch** = corrected DMSY26 (BM/BC + FindPivots-D).
   - Correctness: S2 Lemma S2.1 + S3 §3.1, which hold on any admissible instance and for any degree.
   - Time: S4-T with f = delta + lg k_D. This is DMSY26's O(m sqrt(log n) + sqrt(mn log n LL)).
   - DMSY26's side condition delta <= lg k is not needed once f = delta + lg k is carried explicitly.

**Conclusion.** Reviewed text plus GM fully supports Theorem B1 in the form
T = O(n + m sqrt(log n) + min{sqrt(mn log n LL), m sqrt(log n) (LL LLL)^{1/4}}).
This is never worse than DMSY26. It is strictly better iff m/n = o(sqrt(LL/LLL)), which includes all sparse graphs.

**Recommendation.** Adopt wording (a). Drop the unimplemented (1 + LLL n/m)^{1/4} general-delta branch. The
goal-relevant sparse claim is unaffected either way.


## Appendix R27 — agent-03 tester-independent differential cross-check

Frozen label `RV03xc`, source `/research/agents/agent-03/work/post_03_xcheck.md`, sha256 `c8fc6ba76d0999412d04f4b7e5b90998c32134594498e9f9edfc9fc663eee579`, frozen 2026-09-20T08:03:05Z.

# agent-03 INDEPENDENT differential tests (gate G12): 0 wrong outputs, 0 certificate failures

Tester: agent-03, who wrote none of the tested implementations. The graph generators, the exact reference (a
binary-heap Dijkstra on ints and Fractions) and the oracle-free certificate checker are all my own code:
agents/agent-03/work/xcheck/xcheck.py.

The certificate checks that:
- dist[s] = 0;
- the triangle inequality holds on every edge with a reachable tail;
- no reachable vertex points to an unreachable one;
- every pred edge is tight;
- the pred graph is acyclic and rooted at s;
- unreachable vertices are exactly those with dist = None.

Targets:
- A4 = agent-04 impl/bsssp.py, the line-by-line implementation of pseudocode.md v2.x, bootstrapped, run with
  debug=True and its own inner deadline-instance oracle asserts;
- A4p = the same with plain=True (corrected DMSY26, no bootstrapping);
- A4fast = A4 with debug=False;
- A7 = agent-07 sssp_dmsy26 with InnerParams (bootstrap).

Graph families (mine):
- random sparse digraphs;
- zero-weight SCCs;
- heavy parallel edges plus self-loops;
- BF-hard label churn (a path plus long early edges);
- "frontier regions": many roots with small overlapping regions and later improvements, which forces
  hits, merges and failed searches;
- unreachable halves;
- bidirected grids;
- star plus path.

Weights: ints 0..9, positive, all zero, 0/1, {0,2,2,4} (ties), Fractions, huge (10^12 to 10^15), tiny
(1/10^6).

Parameter modes:
- small: t in {2,3}, k in 1..4, t_in in {2,3}, k_in in 1..3, degree reduction with probability 0.7;
- deep: outer k in {33,40,70}, t_in = 2. Then l_in >= 2, so the inner FindPivots-D sees |S| > 1 and inner
  merges, trees and W sets inside J_x are exercised;
- asym: the Sec. 8.2 formulas.

Coverage (A4 counters): inner runs, fb_new, fb_merge and fb_fail are all > 0, and fd_merge > 0 in deep mode.

| run | graphs | max n | A4 | A4p | A4fast | A7 |
|---|---|---|---|---|---|---|
| small, seed 101 | 2000 | 40 | 2000 ok | 2000 ok | – | 2000 ok |
| small, seed 505 (latest code, after the S5 v1.2 Merge fix) | 1500 | 40 | 1500 ok | 1500 ok | – | 1500 ok |
| deep, seed 202 | 300 | 150 | 300 ok | – | – | 300 ok |
| deep, seed 404 | 150 | 800 | – | – | 150 ok | 150 ok |
| deep, seed 606 (latest code) | 300 | 300 | 299 ok + 1 exc* | 299 ok + 1 exc* | – | 300 ok |
| asym, seed 303 | 200 | 600 | 196 ok + 4 exc* | – | 200 ok | – |

(*) Every exception is a Python RecursionError inside agent-04's DEBUG-ONLY helper Solver.complete(v, memo), which
recurses along canonical paths. It is hit on the long-path family (n ~ 300-600 after degree reduction). The
algorithm itself is fine: the same graphs pass with debug=False (A4fast), and they also pass with debug=True after
sys.setrecursionlimit(100000), including all of agent-04's internal oracle assertions (checked on seed 606, graph
99). @agent-04: please make complete() iterative or raise the recursion limit in the test drivers. This is not an
algorithm issue.

Total: 5750 graph-runs of the bootstrapped algorithm and 3299 of the plain algorithm. There were 0 wrong
distances and 0 certificate failures.

Reproduce:
    cd /research/agents/agent-03/work/xcheck
    python3 xcheck.py 505 1500 A4,A4p,A7 40 small
    python3 xcheck.py 606 300 A4,A4p,A7 300 deep
