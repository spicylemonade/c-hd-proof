# PAPER_CHD v2.0: Directed SSSP in O(n + m + m·lg(m/n) + m^{1/3}(n lg n)^{2/3}) time, formalized for d ≤ lg^{3/4} n

Final paper version for /research/final/PAPER.md. Integrated by agent-03.

STATUS (2026-09-21 ~00:00 UTC). The formal statements of §1 (Theorem 1 and Corollary 2) build with the standard axioms only
([propext, Classical.choice, Quot.sound]) in agent-10's frozen integration build #33 (Frontier.CHD.Final). Corollary 2' and the
formal space statement are corollaries in files outside that closure (FinalExtras, FinalSpace; std axioms, verified 23:03 UTC).
They are claimed as formal only once the post-freeze build #34 that adds them to the root has been audited.
- GOAL.md's acceptance pipeline is in progress (§9.2 item 6): kernel replay PASSED (agent-09); fresh-copy rebuild PASSED and
  REVIEW_1 ACCEPTED (agent-07); REVIEW_2 (agent-02) pending.
- This text is final/PAPER.md only once that pipeline passes. Until then it is a candidate.
- Theorem 3 (the full density range) is a paper-level statement and is NOT claimed as formalized.

Authors:
- agent-09: card C-HD, FindPivots-HD, DS'.
- agent-03: integration, §4.3 Lemma L, the §5 time analysis (handled ranges, home charging), §6 parameters, §8 novelty.

Formalization, by lane:
- agent-01: Layer A; level body.
- agent-02: labels; scans; merge.
- agent-03: time-analysis lemmas; tree layer; PT; base case; finalization.
- agent-04: D layer.
- agent-05: pull.
- agent-06: master cost; post-half.
- agent-08: spine and loop.
- agent-09: FindPivots, B-L2.
- agent-10: dispatcher, L6, final assembly.
Reviewers: agent-07 (reviewer #1) and agent-02 (reviewer #2).

Inherited background: the B1 draft (/research/background/PRIOR_B1_UNVERIFIED_DRAFT.md; UNVERIFIED; a different team's text),
namely S1 (labels, Claim C, L3+), S2 (corrected core, Lemma S2.1) and S5 (data structure D). Everything used is re-verified;
the formal chain of §9 does not rely on the draft.
- S1 §D and S2 were checked line by line by agent-02 (REVIEW #2 round 2, board 11:16, no error).
- The interface points C1–C5 where C-HD touches the core are handled in §4.
Line numbers BM.x, BC.x, MP.x and PT.x refer to B1 pseudocode PCv2.3 (B1 Appendix A). FH.x refers to §3.3 below.

## 1. Model, problem, theorem
- Input: a directed multigraph G = (V, E), n = |V|, m = |E|, source s, weights w: E → R_{≥0}. Parallel edges, self-loops, zero
  weights, zero cycles and unreachable vertices are allowed.
- Output: for each v, dis_G(s,v), or ⊤ if v is unreachable. A labeled vector; no order is required.
- Model: comparison–addition on weights (one comparison or addition of reals = 1 step). Unit-cost word RAM on O(log n)-bit words
  for indices, counters, pointers and ids. No floor, hashing or bit tricks on reals.
- Deterministic worst case. All input reading, preprocessing and output are charged.

Formal model (Frontier.CostModel, "CostModel v2"). A deep-embedded RAM with a word cap (n+m+2)^{e+1}, e = 160, and real
registers that are only compared and added.
- Every statement, test and allocated cell is charged.
- The input is read from arrays and the output (reach, dist) is materialized.
- `Program.Exact` means dist(v) is the infimum over walks, i.e. exact labeled distances.
- `RunsWithin G s T` means the unique terminating run costs at most T.

**Theorem 1 (formal: Frontier.CHD.Final.chd_exact_within, chd_CHDTarget).**
- Let F(n) = ⌊⌊log₂ n⌋^{3/4}⌋, computed as Nat.sqrt(Nat.sqrt((Nat.log 2 n)^3)). The inner floor matters: e.g. at log₂ n = 21.9,
  ⌊21^{3/4}⌋ = 9 while ⌊21.9^{3/4}⌋ = 10.
- Let chdProgram = chdProg 160 psC coreC; it is one uniform, closed and deterministic program.
- Then chdProgram is exact on every directed graph with nonnegative real weights and every source, and every run costs at most
  C·Tdisp_F(n, m), with the explicit constant C = bodyC KcC + 65536·9 + 100.
- Here Tdisp_F(n, m) is:
  - Tchd(n, m) = n + m + m·ln(m/(n+1) + 2) + m^{1/3}·(n·ln(n+2))^{2/3}, if m ≤ n·F(n);
  - (n+1)(m+1), otherwise (verified Bellman–Ford fallback).
- The program's own dispatcher test runs C-HD when log₂ n ≥ 16 and ⌈m/n⌉ ≤ F(n) ≈ lg^{3/4} n, and Bellman–Ford otherwise. The
  C·Tchd bound still holds for every n with m ≤ n·F(n): for log₂ n < 16 the Bellman–Ford cost is absorbed by the term 65536·9 (§6).

**Corollary 2 (formal: Frontier.CHD.Final.chd_gateC : Frontier.GateC).**
- Take the profile μ(n) = n·⌊ln(n+2)^{3/4}⌋; eventually n·√ln(n+2) ≤ μ(n) ≤ n·ln(n+2).
- Along μ, the bound satisfies C·Tdisp_F(n, μ(n)) / (n·ln(n+2)) → 0. At d = ln^{3/4} n it is O(n·lg^{11/12} n).
- In this window the best previously known deterministic directed comparison–addition bound is Θ(n lg n). It is the minimum of:
  - Dijkstra, O(m + n lg n);
  - DMM+25, O(m lg^{2/3} n);
  - DMSY26, O(m√lg n + √(mn lg n lglg n)).
- Formal comparison (post-freeze, build #34: agent-01's Frontier.CHD.FinalCompare.chd_beats_known; std axioms, re-checked by
  agent-03 at 23:25). The witness bound T = C·Tdisp_F, valid on every graph, satisfies T(n, μ(n))/b(n, μ(n)) → 0 for each of the
  three bound EXPRESSIONS b, taken with constant 1 and L = ln(n+2):
  - m + n·L;
  - m·L^{2/3};
  - m·√L + √(m·n·L·ln L).
  That these are the best known bounds is the novelty review (§8), not a formal statement.

**Corollary 2' (strong form, all graphs in the range; formal, post-freeze build #34: Frontier.CHD.FinalExtras.chd_auditGateC :
Frontier.Audit.GateC Frontier.Audit.ramModel).**
- Status: FinalExtras is outside the frozen closure of build #33. It compiles with std axioms (agent-10, 23:03) and enters the
  root at build #34. Corollary 2' is claimed as formal only once build #34 is audited.
- Same witness chdProgram; the implication from CHDTarget F is agent-09's independent AuditGateC.chdTarget_imp_auditGateC.
- Audit's own specification: Solves means the decoded output equals Audit's walk-infimum distance adist, and time is the charged
  cost of the unique terminating run.
- Put f(n) = max(1, F(n)). Then f(n) ≥ sqlg(n) = max(1, ⌊√⌊log₂ n⌋⌋).
- For every constant K there is N such that EVERY graph with n ≥ N and m ≤ n·f(n), with every source, has
  K·time ≤ n·lg(n), where lg(n) = max(1, ⌊log₂ n⌋).
- So the o(n lg n) bound holds uniformly over all graphs of average degree ≤ f(n), not only along the profile μ.

**Theorem 3 (paper level, NOT formalized beyond Theorem 1's range).**
- The C-HD algorithm of §3 runs in O(Tchd(n, m)) for every m, by §5–§6.
- Hence it is o(n lg n) for every d = m/n ∈ [c·√lg n, o(lg n / lg lg n)].
- The formalized program switches to Bellman–Ford above d = F(n). The kernel-checked improvement therefore covers d ≤ F(n); the
  range F(n) < d = o(lg n / lglg n) rests on this paper's analysis only.

**Space.**
- Formally, space ≤ cost ≤ C·Tdisp_F: agent-05's Frontier.CHD.FinalSpace.chd_space_within and agent-01's
  Frontier.CHD.FinalExtras.chd_space, both from the model invariant RAMAudit.run_space_le_cost. Both are post-freeze files for
  build #34, as for Corollary 2'. Within frozen #33 the same bound is L6.chdProg_space (NamedWitness), stated for chdProg e ps core
  under CoreSpec.
- The formalized DS' preallocates Θ(Tnat) cells (§7), which is superlinear in the Gate-C window.
- An O(n + m)-space variant (a reallocating implementation) is sketched in §7 and is NOT formalized.

## 2. Preprocessing (cost O(n + m + m lg δ)); this is L6 v2 (agent-10), the canonical layout (COORD G2-5 D6)
- P1. Keep-set, no BFS. keep(v) :⇔ v = s or v has a non-loop in-edge. One O(n + m) pass.
  - A vertex outside keep has no non-loop in-edge, so it is unreachable from s. Its output is ⊤ and its out-edges are dropped.
  - |keep| ≤ m + 1. The core's parameters are computed from (cn, cm) := (min(n, m+1), m).
- P2. Dedup. For kept u and each v ≠ u, keep the FIRST minimum-weight edge u → v; self-loops are dropped. The result is SIMPLE and
  distance-preserving. This is needed by HD1 (§3.3) and by the prefix fact (P).
- P3. Degree reduction by OUT-degree CHAINS. δ := max(3, ⌈2m/n⌉) is computed from the input (n, m).
  - A kept u of kept out-degree d_u becomes c_u = max(1, ⌈d_u/(δ−1)⌉) virtual vertices x = off[u] + q, q < c_u.
  - A non-last chunk holds exactly δ − 1 real out-edges plus the zero-weight chain edge x → x+1. The last chunk holds the remaining
    real edges.
  - Every real edge u → v enters gRep[v] := off[v], the FIRST chunk of v.
  - Out-degrees are ≤ δ. IN-DEGREES ARE UNBOUNDED; Σ_x indeg(x) = gM ≤ 2m (proved: L6/Sizes; the chain edges number
    ≤ m/(δ−1), so gM ≤ 1.5m for δ ≥ 3, but only gM ≤ 2m is used). N := gN ≤ 2cn vertices (L6/Sizes).
  - Every chunk of v has distance dis(v), and gRep[v] has the fewest hops.
  - Everything in §5 that uses "degree ≤ δ" uses OUT-degrees only: relaxation targets (B4'), FindPivots scans, base-case inserts.
- P4. Out-lists: a static CSR range [gSt[x], gSt[x+1]) per virtual vertex x.
  - Each range is sorted by the key (w(e), head e), chain edge included. Heads in a range are distinct, so the order is strict and
    agrees with κ for a common prefix label. Cost: O(Σ deg lg deg) = O(m lg δ) comparisons (agent-06's verified merge sort).
  - A MUTABLE singly linked live list (head gHd[x], successor gNxt) initially lists the whole range in order.
  - FH.9 unlinks the slot being scanned through the scanner's predecessor slot, in O(1). This is equivalent to the doubly linked
    list of v1.2, because FH.9 deletes only the slot under the scan.
- P5. Output. reach[v] := gKeep[v] · gReach[gRep v] and dist[v] := gDist[gRep v] = d[gRep v].len. O(n + m).

## 3. The algorithm
### 3.1 Labels and order (inherited, B1 S1 §A)
- A label is ∞ or a 5-tuple (len, hops, v, e, a): len real, hops int, v the vertex, e the last edge, a = ver[tail e] at write time.
- The order ≺ realizes the full walk order κ exactly, with one real comparison plus O(1) integer comparisons.
- Relax(u, e, B): cand := d[u] ⊕ e = (d[u].len + w(e), d[u].hops+1, head e, e, ver[u]).
  - Valid iff cand ⪯ d[v] and cand ≺ B.
  - A strict decrease writes d[v] and increments ver[v]; equality is a re-confirmation.
  - Facts used: T1 (monotone), T2 (strict growth), A1 (canonical tree and strict increase along canonical paths), A3 (upper bounds,
    labels non-increasing), A4 (canonical relaxation).
- PREFIX FACT (P). For fixed u, e ↦ d[u] ⊕ e is strictly increasing along the sorted Out(u), by T1 and the key order
  (w, id head, id e), which the label compares as (len, hops, v, e). So for every bound β, {e ∈ Out(u) : d[u] ⊕ e ≺ β} is a PREFIX
  of Out(u). (agent-02 C5: agent-08's Lean key must use the same order.)

### 3.2 The core: B1 PCv2.3 BM.1–BM.31 and BC.1–BC.9 (inherited verbatim), with these changes
- M1 (pointer scans over the STATIC range; two lists, agent-01 11:43, reviewer O8).
  - The main recursion's scans (BC.7, BM.19–21, BM.27) run over the static CSR range [gSt[u], gSt[u+1]), with a pointer ptr[u] into
    it. FindPivots-HD (§3.3) scans the mutable live list gHd/gNxt.
  - BC.7 (u extracted in a base call with bound B) and BM.27 (u ∈ W' of a call with bound B): scan the range from its start while
    d[u] ⊕ e ≺ B, calling Relax(u,e,B) and inserting as in PCv2.3. Afterwards set ptr[u] to the first slot with d[u] ⊕ e ⪰ B.
  - BM.19–21 for u ∈ U_i (child bound B_i, own bound B): scan from ptr[u] while d[u] ⊕ e ≺ B, calling Relax and inserting when
    valid (every scanned e has d[u] ⊕ e ⪰ B_i, see §4.4). Advance ptr[u] past the scanned slots.
  - The static range still contains edges deleted by FH.9. By Lemma L(a) they are invalid forever, so relaxing them is a no-op, and
    the pointer scans each slot at most once per call chain (O(m) extra in total, §4.4).
- M2 (edge deletion). Performed only at FH.9: an edge (u,v) scanned in a FindPivots search with d[v] ≺ L_X is unlinked from the
  live list of u. No other deletion rule is used (agent-02 R2-1: the "flag all in-edges" rule of C_HD_PROOF v1/v2 is dropped).
- M3 (FindPivots-HD) replaces FindPivots (BM.4); §3.3.
- M4 (data structure DS') replaces S5's D; §3.4.
- M5 (parameters); §6.
- M6 (BM.22 omitted). The optional pivot switch BM.22 is dropped. S2.5 item 6 shows that removing it keeps every invariant. agent-01's
  kernel-checked L4 relation omits it, and agent-07 checked the BM.22-free variant exact on 8000 runs.
- No dispatcher to DMSY26 is used (agent-02 R2-6). The formal dispatcher (Frontier.CHD.Dispatch.dispatchProg) runs the verified
  Bellman–Ford program (BF.prog, cost ≤ 9(n+1)(m+1)) whenever log2 n < 16 OR m > n·F(n). For log2 n < 16 this is O(1). Outside
  the window the Gate-C target makes no claim beyond the fallback bound (§6).
### 3.3 FindPivots-HD (author agent-09; CHD_SEC_FINDPIVOTS.md v1, reproduced with agent-02's fixes R2-2/R2-3)
Search "heap" H = an UNSORTED ARRAY with a position table: Insert and DecreaseKey O(1), ExtractMin O(|H|).
L_X := d_B[S] = min({B} ∪ {d[x] : x ∈ S}), computed in O(|S|). By Obs. 2.1(2) (S1 §E: the minimum of a frontier is complete),
L_X = dis_B(S).
```
FH.1  compute L_X ; id := new id ; trees := [] ; Wlist := [] ; Q := []
FH.2  for x in S:
FH.3    if fmark[x] = id: continue                                  # x already lies in a tree of this invocation
FH.4    sid := new id ; H := {x} ; K := [x] ; val := {x} ; kst[x] := sid ; kpar[x] := none
FH.5    while H ≠ ∅ and |K| < k:
FH.6      u := H.ExtractMin()
FH.7      for e = (u,v) in Out(u), in list order:
FH.8        c := d[u] ⊕ e ; if not (c ≺ B): break                  # range stop, by (P)
FH.9        if d[v] ≺ L_X: delete e from Out(u) ; continue         # PERMANENT DELETION (Lemma L)
FH.10       if fmark[v] = id:                                       # CONTACT with an existing tree (any tree vertex, valid or not)
FH.11         Relax(u, e, B)                                        # may improve d[v]; result not needed
FH.12         T := tree(v) ; add K and the edges {kpar[y] : y ∈ K \ {x}} ∪ {(u,e)} to T ; fmark := id on K
FH.13         goto NEXT
FH.14       ok := Relax(u, e, B)
FH.15       if kst[v] ≠ sid:                                        # v new for this search
FH.16         kst[v] := sid ; K.append(v) ; kpar[v] := u              # first-discovery parent (edge e recorded)
FH.17         if ok: val := val ∪ {v} ; H.Insert(v)                 # explored member
FH.18         (otherwise v is a LEAF: counted in K, never extracted, label unchanged)
FH.19         if |K| ≥ k: break
FH.20       else if ok:                                             # v ∈ K already and validly (re)relaxed
FH.21         val := val ∪ {v}                                        # kpar stays FIRST-DISCOVERY (never re-set)
FH.22         if v ∈ H: H.DecreaseKey(v) else H.Insert(v)           # includes LEAF PROMOTION
FH.23   if |K| ≥ k: create tree T := (K, {kpar[y] : y ∈ K \ {x}}) ; fmark := id on K ; trees.append(T)
FH.24   else: W_x := val ; Wlist.append(W_x) ; Q.append(x)          # failed search: H = ∅ and |K| < k
FH.25 NEXT:
FH.26 return MakePivots(S, Q, trees, Wlist, k)                     # B1 MP.1–MP.10 (PT pieces of size in [k,3k); empty groups dropped)
```
Local facts (agent-09 §2):
- (H-a) heap keys equal current labels;
- (H-b) extraction keys strictly increase, and extracted vertices are never validly relaxed again in the same search (T2);
- (H-c) K is a tree of graph edges rooted at x, and kpar tails were extracted earlier;
- (H-d) the trees of one invocation are pairwise vertex-disjoint, and the FH.12 union is again a tree;
- (H-e) |K| ≤ k.

### 3.4 Data structure DS' (author agent-09; CHD_SEC_DS.md v1.1). Summary of the parts used below
- Representation. Blocks are unsorted entry lists with disjoint value intervals, in increasing order. They are indexed by a
  SEPARATOR STACK searched by binary search (v1.5, D2: the code has no balanced tree; BSearch.lean, cost O(lg #blocks); the
  Layer-A model DBlocks charges bsCost(#blocks) per search). There is ONE global live pointer live[v] per vertex; an entry is
  live iff live[key] points to it. Keys(D) := {v : live[v] ∈ a block of D}.
- Insert(v,c) in structure D. Let live[v] = entry e0.
  - If e0 lies in D with value ⪯ c: no change.
  - Otherwise e0 becomes stale. This includes an entry in an ANCESTOR's structure (agent-03's rule EA; same effect). A new entry is
    prepended to the block owning c, found by binary search over the separator stack.
  - (v1.6, agent-02 R-1) Insert NEVER splits (DLazy.insertL; insRAM_spec refines exactly this). Splits are lazy and front-only: they
    happen inside Pull's front preparation (DLazy.prep; agent-05's prepTop/splitStep). They are paid by the potential Ψ below, since
    a full Pull pays M.
  - Cost O(lg #blocks).
- Delete: O(1), makes the entry stale.
- Pull = prep, then select (v1.6). prep gathers front blocks, discarding stale entries and splitting the front block lazily, until
  M+1 live entries are held. select picks the M smallest by BFPRT, and the remainder becomes the new first block. PP (S2.0) holds on
  LIVE entries.
- Merge(D'): splices D''s blocks into groups of ≥ M/3 live entries and links them in front; the last small group is spliced onto
  D's first block. No entry is visited.
  - Cost O(1 + |D'|/M' + #groups·lg #blocks) = O(1 + |D'|/M') for l ≥ 2.
  - (v1.5, D1) There is no base-case BST. A base call runs bounded Dijkstra on an indexed binary heap (IHeap) and, at its return,
    inserts its leftover heap keys with their labels into a FRESH level-0 DS' structure (BaseDH: newC M_0 B, then one Insert per
    key). Level 1 then merges an ordinary DS' structure. Each conversion Insert is prepaid by the heap charge
    (DC.bins ≥ DCb.bins + DC.ins 0 + 3; BMTeleLoop.baseDH_tele).
- Block count (v1.5, D2: the potential argument Ψ, tracker O29; agent-01 DPsi/BMTele/BMTeleLoop). With thr M := max(1, ⌊M/3⌋),
  nsm := #blocks with fewer than thr M entries and Ψ(D) := M·nsm + 2·#entries:
  - #blocks ≤ nsm + #entries/thr M (big blocks hold ≥ thr M entries);
  - a new structure has Ψ = M; Insert: Ψ' ≤ Ψ + 2; a full Pull: Ψ' + M ≤ Ψ, a short Pull resets Ψ' = M;
    Merge (M ≥ 3): Ψ' ≤ Ψ + M + 2·#entries(D') (grouping leaves at most one small group).
  - Along one call's loop, Ψ + 2·(remaining placements of the call's subtree) ≤ 2M_l + 2E_max(l), where E_max(l) is the level-l
    placement budget of (B4') (Fits; agent-01 TraceFits from agent-03's ownSum_le/ucap_le). Hence #blocks = O(E_max(l)/M_l + 1)
    at every Insert, and one Insert costs O(lg(E_max(l)/M_l) + 1): insBound(M, 2M + 2E) ≤ 211·log2(8ρ + 8) + 441 for E ≤ ρM
    (BMTeleParams.insBound_le). With M_l = t·2^{(l−1)t}, τ_l = t^3·2^{lt}, E_max(l) = (3(L+1) + 3δ)·2τ_l this is O(t) in the
    Lean window.
  - The family potential potM(active) + 2·stale(others) telescopes along the whole run (bmsspDL_tele_top): the concrete run's
    cost is at most the cost of the literal run with the amortized charges (pull 735|S'| + 950, delete 5|ks| + 1, merge 14,
    new 3, insert DC.ins l).
  (v1.4 used "every non-first block had ≥ M/3 live entries at creation"; that fails for the leftover block of a full Pull and
  the last group of a Merge, which is why the potential is needed.)
- Semantic equivalence with S5 (agent-09 DS' §4; agent-03 N5.0 "persistence"). During a child's run the ancestors' structures are not
  read (R9, FP6). Every key inserted inside a child's subtree is, at the child's return, in U_i or in keys(D_i). So after BM.14–BM.15
  the parent's live key set and live values coincide with S5's keep-smaller Merge plus FIX-STALE deletion.
- agent-02 C4: stale entries are invisible to keys(D), IsEmpty (BM.9, BM.24a, BC.3), PP and BC.8's min.
- (v2.0, agent-04; formal: KeyLists.LL, DRI.kl) IsEmpty in O(1) despite stale entries.
  - Each level keeps a circular doubly-linked list of its live keys.
  - Insert unlinks the key from whatever list holds it; this may be an ancestor's list (rule EA), and unlinking needs no level.
    Insert then links the key at level l.
  - Delete and Pull unlink. Merge splices the child's list into the parent's in O(1).
  - IsEmpty is next[sentinel] = sentinel.
  - Per-level counters would fail: an Insert may supersede an entry whose recorded level is stale after a Merge, and relabelling
    would cost Θ(|D'|), which breaks Merge's O(1 + |D'|/M').

## 4. Correctness
### 4.1 The inherited core lemma
Lemma S2.1 (B1 S2; checked by agent-02). Every call X satisfying (C1)–(C3) terminates, and its return satisfies (R1)–(R9). This holds
for ANY FindPivots routine with FP1, FP2, FP3 (only W ⊆ Ũ is used), FP5, FP6, and ANY D implementing the S2.0 interface
(Insert-keep-min, Delete, Merge with the value precondition, Pull with the PP equality and x ⪯ B, (V1), (V2)).
Cor. S2.2: the top call BMSSP(∞, {x_s}, L) with Λ_L ≥ N is full, and it makes every reachable vertex complete.
C-HD changes only four things:
- FindPivots, handled in §4.2 and §4.3;
- the scanning order and extent of the core's relaxation loops, in §4.4;
- adjacency lists, by deletions, in §4.3;
- the implementation of D, in §3.4 / C4.
Lemma S2.4 of B1 is FALSE under prefix scans but is not used here (agent-02 C3). S2.5 (one insertion event per edge) uses from it
only "all scans of u happen after u is complete", which still holds.

### 4.2 FindPivots-HD satisfies FP1, FP2, FP3, FP5, FP6 (agent-09 §4, with agent-02's fixes)
FP1 (frontier). Let v ∈ Ũ. By (C2), path(v) contains q ∈ S that is complete at FindPivots' start (and stays complete, A3).
- If q ∉ Q, then q lies in some P_j (FP2), and we are done.
- If q ∈ Q, then q's OWN search ended at FH.24: FH.13 was never taken, FH.19 never fired, and H = ∅ at the end. (agent-02 R2-2: this
  holds even if q was later absorbed into another search's tree.)
- Let q = z_0, …, z_r = v be path(v). Induction: each z_j is extracted in q's search with d[z_j] = dis(z_j).
- For the step, take e* = (z_j, z_{j+1}). Then d[z_j] ⊕ e* = dis(z_{j+1}) ⪯ dis(v) ≺ B, so e* lies in the scanned prefix (P).
- e* was never deleted, by Lemma L(b) below: e* is canonical.
- FH.9 does not fire: dis(z_{j+1}) ⪰ dis(q) ⪰ L_X.
- FH.10 does not fire. Otherwise q's search would have ended at FH.13.
- Relax(z_j, e*, B) is valid (A4). So z_{j+1} enters val and H, at FH.17 or FH.22.
- By (H-b), z_{j+1} was not extracted before. Since H = ∅ at the end, it is extracted later with label dis(z_{j+1}).
- Hence v ∈ W_q and v is complete. ∎
FP2. P_1..P_p and Q partition S, and each is nonempty. MP assigns each x ∈ S \ Q to the first piece containing it; every such x lies in
a tree (FH.3, FH.12 or FH.23); empty groups are dropped (MP.8). Q is excluded from every P_j (B1 c4).
FP3. W = ∪_{x∈Q} W_x, where W_x = val ∋ x has size ≤ |K| < k. W ⊆ Ũ because val-vertices are x or touched (L3+).
FP5 (SP). Every Relax at FH.11, FH.14 or FH.20 has an extracted tail, which is x or was touched earlier. Leaves are never extracted
unless promoted by a valid relaxation (FH.22).
FP6. No D operation is performed.
Lemma F2 (foreign leaves; agent-09). Let v be a tree vertex of X's FindPivots with v ∉ Ũ_X.
- Then v is a leaf that was never promoted, v is complete, and L_X ⪯ d[v] = dis(v) ≺ B_X.
- Such v is not in S (S ⊆ Ũ_X), so it belongs to no P_j (agent-02 R2-3).
Proof. It is a leaf because explored vertices are touched and hence lie in Ũ_X (L3+). The range comes from FH.9 not firing and from
invalid-and-in-range. Completeness comes from (C1). Promotion would be a valid relaxation into a complete vertex; by A4 that is
canonical, so u = p*(v) ∈ Ũ_X would force v ∈ Ũ_X. ∎

### 4.3 Lemma L (deletions). Suppose FH.9 deletes e = (u,v) in call X' at time τ. Then:
 (a) for all later labels, d'[u] ⊕ e ≻ d'[v], so e is never again a valid relaxation;
 (b) dis(u) ≻ dis(v); in particular e is not the canonical edge of v (A1: dis(p*(v)) ≺ dis(v)), so no canonical edge is ever deleted;
 (c) no Relax-valid event of the unmodified algorithm is lost. Every insertion event (BM.21, BM.28, BC.7) and every FindPivots
     relaxation needs a valid relaxation, so the core's executions with and without deletions coincide on all labels, all D
     operations and all FindPivots outputs.
Proof.
- u was extracted in X', so u ∈ S_{X'} ∪ touched ⊆ Ũ_{X'} (L3+). Then path(u) visits some y ∈ S_{X'}, and
  dis(u) ⪰ dis(y) ⪰ dis_B(S_{X'}) = L_{X'}.
- At τ, dis(v) ⪯ d[v] ≺ L_{X'}. This gives (b).
- Later labels satisfy d'[u] ⪰ dis(u) ≻ d[v] ⪰ d'[v] (A3), so d'[u] ⊕ e ≻ d'[u] ≻ d'[v] by T2. This gives (a).
- (c) follows from (a): a Relax call on e would have returned False and changed nothing.
This replaces agent-09's open "L_X monotonicity" obligation (agent-02 R2-5): FP1 needs only (b), which is proved directly. ∎

### 4.4 Lemma H0' (pointer scans are faithful; v1.3, two lists)
Setting. ptr[u] indexes the STATIC CSR range [gSt[u], gSt[u+1]), which is sorted by the key of P4. FH.9 unlinks edges only from the
mutable FindPivots list gHd/gNxt, so it never touches the static range or ptr[u].

Claim. For every u and every call X on u's chain X_0 ⊃ … ⊃ X_q (the calls whose U contains u; S2.5), consider the moment before X's
BM.19 (or BM.27 / BC.7) scan of u. Then ptr[u] is the first slot of the static range with d[u] ⊕ e ⪰ β, where:
- β = B_{child} at BM.19;
- ptr[u] is the range start at BM.27 and BC.7, which is correct since those scan from the start.

Consequences.
- The M1 scan calls Relax exactly on the static-range edges e with d[u] ⊕ e ∈ [β, B_X).
- Edges deleted by FH.9 may still be in that window. By Lemma L(a) they are invalid forever, so Relax on them is a no-op.
- PCv2.3's scan of Out(u) differs only by calling Relax on edges with cand ≺ β and with cand ⪰ B_X.
  - The first kind are valid re-confirmations or invalid, and never insert, since the BM.20 test fails.
  - The second kind are invalid.
- Hence the executions coincide on labels and D operations.
- Each slot is passed by the pointer at most once over u's chain, so the extra work is O(m) in total.

Proof.
- u is complete at every such scan (S2.5), so c_e := d[u] ⊕ e = dis(u) ⊕ e is fixed.
  - (v1.6, agent-02 audit A-1) In the RAM refinement this is an EXPLICIT premise of winScanD_spec, wScanD_spec and relW_spec:
    ∀ u ∈ row, d u = dis u ∧ d u ≠ ⊤.
  - The spine supplies it from Layer A: for U_i from the sub-call's CallPost; for W' from BM's loop invariant (W' ⊆ Complete).
  - For the base call it comes from BInv.complete and BInv.UUK (BaseCall0.baseC_fin).
  - Without it BM.27's pointer claim is false: an x → y relaxation inside W' after y's scan would leave ptr[y] stale.
- The first scan of u is the settling one: BC.7 if u is extracted in a base call, or BM.27 if u ∈ W'_{X_q}. It scans the prefix
  {c_e ≺ B_{X_q}} from the range start and leaves ptr[u] at the first c_e ⪰ B_{X_q}.
- At X_{r−1} (r ≤ q), BM.19 scans from ptr[u] while c_e ≺ B_{X_{r−1}} and leaves ptr[u] at the first c_e ⪰ B_{X_{r−1}}.
- By (P) (the static range is sorted) and the bound chain B_{X_q} ⪯ … ⪯ B_{X_0} (PP), the pointer invariant holds.
- The static range never changes, so there is no deletion case.
- Scans in FindPivots (FH.7) use the mutable list and never move ptr[u]. ∎
Note: agent-02 C2 lists the three proof steps of S2 that use scans of canonical edges (S2.3 (K3), Step 4 Case 1, Step 5 (R2)).
Each canonical edge lies in the relaxed window [β, B_X) or in the settling prefix, and by Lemma L(b) it is never deleted from the
FindPivots list either.

### 4.5 Output
By Cor. S2.2 every reachable vertex of the reduced graph is complete at the end. Unreachable vertices keep ∞. P5 maps labels back as
in B1 §8.3. Since the order ≺ refines (len, hops), the len-component of a complete label is the real distance. ∎(correctness)
## 5. Running time (Lemma 3.9-HD). Author agent-03. Replaces B1 S4.4–S4.6 for C-HD.
Parameters (§6): t ≥ t_0, k := ⌈√t⌉ with 3k ≤ t (FIX-L13), M_l = t·2^{(l−1)t}, Λ_l = t^3·2^{lt}, Λ_0 = t^3,
L := ⌊lg N / t⌋ + 1 (v1.5, D6: the code's LF; v1.4 took min{l : Λ_l ≥ N}). Then Lt > lg N, so Λ_L > t^3·N/2 ≥ 2048·N > N
(t ≥ 16), and L ≤ lg N/t + 1. Degrees are ≤ δ = Θ(d). N = O(n) is the number of reduced vertices.
Size facts inherited from B1 S4.1, with δ in place of 3:
- (B1) |S_X| ≤ t^2·2^{lt} for a level-l call;
- (B2) partial ⇒ |U_X| > t|S_X|;
- (B3) |U_X| ≤ 2Λ_l;
- (B4') [corrected per agent-07 P-1] Under DS', Merge splices blocks of descendants, so D_X's blocks may hold entries (live or stale)
  that were inserted anywhere in X's subtree: relaxation targets of U_X (≤ δ|U_X|, one event per edge), pivots and re-selections.
  - Every group contains an S-vertex, so p_Y ≤ |S_Y|, and Σ_{Y⊆X, one layer} |S_Y| ≤ |U_X| by (B2) and full S ⊆ U.
  - Hence Σ_{Y⊆X} p_Y ≤ (l+1)|U_X|.
  - Re-selections are ≤ Σ p + 2δ|U_X| by 5.3: cross and foreign-leaf edges with tail in U_X.
  - Foreign leaves never enter P, so they need no separate count, and BM.25 re-inserts (≤ Σ_{partial Y⊆X} |S_Y| ≤ l|U_X|/t).
  Hence E_{D_X} = O(|S_X| + (δ + l)|U_X|), and lg(E_{D_X}/M_l) ≤ t + O(lg t + lg δ + lg L). In the Lean-target window
  (m ≤ n·F(n)), lg L ≤ lglg n ≤ t, so Insert costs O(t).

### 5.1 Handled ranges (N1). Define B_low(X) := the parent's B' just before X's iteration (B'_0 from BM.8), and put
H(X) := [B_low(X), B'_X).
(a) H(child) ⊆ H(parent). (b) Siblings' H are disjoint and ordered. (c) Two calls of one layer have disjoint H.
(d) U_X ⊆ dis^{−1}(H(X)); a FULL call has H(X) = [B_low(X), B_X).
Proof.
- Monotonicity (J5) and BM.24a give the upper end.
- For the lower end, B'_0(Z) ⪰ B_low(Z): (S-a) at Z's parent gives dis(S_Z) ⪰ B_low(Z), and BM.8 takes a min over pivots of S_Z
  (and B_Z ≻ d[y] ⪰ dis(y) for y ∈ S_Z ≠ ∅).
- (d) follows from (R1) and (S-a). ∎
Also L_X = dis_B(S_X) ⪰ B_low(X) by (S-a), so foreign leaves (F2) satisfy dis(v) ∈ [L_X, B_X) ⊆ [B_low(X), B_X).

### 5.2 Pivot bound with foreign leaves (N3)
- Partial X: p_X ≤ |S_X| < |U_X|/t.
- FULL X: the trees of X are vertex-disjoint (H-d); their non-foreign vertices lie in Ũ_X = U_X; the foreign ones form O_X.
  So Σ_T |V(T)| ≤ |U_X| + |O_X|, and p_X ≤ Σ_T (|V(T)|−1)/(k−1) (PT pieces, MP.8).
- For full X ≠ X' of one layer, U_X ∩ U_{X'} = ∅ (5.1(c,d)). Also O_X ∩ O_{X'} = ∅: a foreign leaf is complete, so its dis is fixed,
  and it lies in both H(X) and H(X'), which are disjoint.
- Hence Σ_{full X in a layer} (|U_X| + |O_X|) ≤ 2N and Σ_{full X in a layer} p_X ≤ 2N/(k−1).

### 5.3 Re-selection charging with foreign leaves (N4; replaces B1 T5 "F_j ⊆ U_X", which fails under contact-at-leaf)
Setting: X full, children Y_1..Y_f.
- Homes: h(u) = r if u ∈ U_{Y_r}; h(u) = 0 if u ∈ W'_X.
- A foreign v ∈ O_X gets h(v) = r if dis(v) ∈ H(Y_r); h(v) = −1 if dis(v) ≺ B'_0; h(v) = f+1 if dis(v) ⪰ B'_f.
(i) g_j (the number of BM.23 re-selections of group j) ≤ 1 + c_j, where c_j = #edges of the PT piece F_j whose endpoints have
    different homes. Each re-selection at iteration r removes a pivot of home r (BM.18), and there is at most one per (j, r). Removing
    the c_j edges leaves c_j + 1 single-home components.
(ii) Every tree edge (u,e) has an extracted tail u ∈ U_X.
  - Different-home edges with both ends in U_X lie in E_X := E(U_X) \ ∪_r E(U_{Y_r}), and Σ_X |E_X| ≤ m (B1 G3).
  - A different-home edge (u,v) with v ∈ O_X can occur at ONE full call only. At a proper full descendant X' ⊂ Y_r containing u in U:
    v ∈ O_{X'} gives dis(v) ∈ H(X') ⊆ H(Y_r) = home of u at X, so the edge would not be different-home at X.
  Hence Σ_{full X} Σ_j g_j ≤ Σ_X p_X + 2m.
Partial X: at most |S_X| re-selections (B1 T5 partial).

### 5.4 Direct cost of one call X at level l ≥ 1 (children excluded). Constant C'' independent of n, m, δ, t.
 T1  FindPivots-HD (FH.1–FH.26), by HD1:
     - L_X, the FH.2 loop and MakePivots/PT: O(|S_X| + Σ_T |V(T)|).
     - Successful and contact searches: O(k·(Σ_T |V(T)| + |S_X|)), by HD1 classes (c),(d),(e) with |K| ≤ k.
       [Each tree or contact search adds |K| new tree vertices and costs O(|K|·k).]
     - Failed searches: O(k^2) each, i.e. O(k^2 |Q_X|).
     - Deletions (FH.9): O(1) each, O(m) globally.
     With 5.2: full X gives O(k(|U_X| + |O_X|) + k^2|Q_X|). Partial X gives Σ_T |V(T)| ≤ k|S_X|, hence O(k^2|S_X|) = O(|U_X|) by (B2)
     and k^2 ≤ 2t.
 T1' BM.6–BM.7: O(|P|) + p_X·O(t + lg δ).
 T2  Picking (BM.11–BM.12): O(k) per pulled current pivot.
     - Partial child: O(k|S_i|) ≤ O(|U_i|).
     - Full child: absorbed by the O(t) re-selection triggered at BM.18/BM.23, since k ≤ t.
     - Groups emptied: O(kp_X) once. (B1 T2.)
 T3  Pull (BM.10): O(|S_i|) = O(|U_i|) (full child: S_i ⊆ U_i; partial: (B2)), plus stale discards (charged to their creating
     Insert/Delete).
     Merge (BM.14, DS'): O(1 + |D_i|/M_{l−1}). For l = 1 the child's structure is the level-0 DS' structure built at the base
     return (v1.5, D1), so Merge is the same block-linking Merge; the conversion Inserts were prepaid in the base call.
     BM.15 deletions, BM.16–18 and BM.30 membership updates: O(|U_i|) + O(|P|).
     BM.19 pointer scans: O(|U_i|) + #edges relaxed (4.4). BM.24a and BM.26: O(1 + |W|).
     BM.27 scans: O(1 + deg(u)) per u ∈ W'_X. Each vertex is in W' of at most one call (W'_X ⊆ U_X and W'_X ∩ U_{Y_r} = ∅ for every
     child), so this is O(m + N) globally. (agent-02 R2-8: not charged to the failed search.)
 T4/T7 Insertion events (BM.21, BM.28): O(t + lg δ) each (5 intro, (B4)); at most one per edge globally (S2.5 = B1 G2).
 T5  Re-selections (BM.23): O(k + t + lg δ) = O(t) each; counted in 5.3.
 T6  BM.25: O((t + lg δ)|S_X|). Nonzero only for partial X, so O(|U_X|) by (B2), under the SIDE CONDITION lg δ ≤ t (agent-07 P-3).
     - Lean-target window: lg δ = O(lglg n) ≤ t.
     - Case t = t_0 of §6: Σ_{partial} (t_0 + lg δ)|S| ≤ (N L/t_0)·O(lg δ), with L ≤ lg N/t_0 + 1 and N lg N ≤ t_0^{3/2} m,
       which is O(m lg δ).
 T0  Overhead O(1) ≤ O(|U_X|), since U_X ≠ ∅ (S2 Step 5).
Base call (l = 0): bounded Dijkstra on an indexed binary heap (IHeap, agent-06; v1.5, D1) over ≤ |S| + δΛ_0 entries, O(lg(tδ))
per operation, followed by one prepaid DS' Insert per leftover key into a fresh level-0 structure (§3.4).
- Each vertex is extracted once globally (it is then in U), and its prefix is scanned once (BC.7).
- Each edge has at most one BC.7 insertion event (G2).
- (v1.6, agent-02 R-2) With the D1 prepayment DC.bins ≥ DCb.bins + DC.ins 0 + 3, every heap insertion is charged
  O(lg(tδ)) + DC.ins 0 = O(t + lg δ), which includes its later conversion Insert.
  - The conversions number at most Σ_base (|S| + #BC.7 insertion events) ≤ N + m. This uses Σ_base |S| ≤ N, from (B2) and fullness,
    and (G2).
  - Base-call total: O((N + m)(t + lg δ)).
  - It enters §5.6 only through the m·t and m·lg(tδ) terms, and it needs N = O(m + 1). That comes from preprocessing: |keep| ≤ m + 1
    (P1) and N = gN ≤ 2cn ≤ 2(m + 1) (P3; L6/Sizes). So N·t ≤ 2(m + 1)·t is within the m·t term of §5.6.

### 5.5 Global facts
- (G1) Per layer Σ_X |U_X| ≤ N (5.1(c,d)); there are L+1 layers, and #calls ≤ (L+1)N.
- (G2) Σ #insertion events ≤ m.
- (G3) Σ_X |E_X| ≤ m.
- (G4, IN-DEGREE-FREE; v1.3) Σ_X |Q_X| ≤ gM + 1 + N·L/t. In-degrees are unbounded after P3, so B1's N(δ+1) form is not used.
  - Full calls: each Q-appearance of v in a full call X gets the WITNESS wit X v, the in-edge of the latest INSERTING relaxation
    event into v (BM.21, BM.28, BC.7) before X starts (reviewer O22(a); the predecessor edge of d[v] is NOT injective). Distinct
    appearances get distinct events, and every edge has at most one inserting event (G2), so Σ_full |Q_X| ≤ Σ_v indeg(v) + 1 = gM + 1.
    The +1 is the source s, which may lie in Q of one full call with no inserting event (O22(b); CostAggregate's src exemption).
  - Partial calls: |Q_X| ≤ |S_X| < |U_X|/t, so Σ_partial |Q_X| ≤ N·L/t.
  - FindPivots-HD writes labels but performs no D operation. This includes the FH.11 contact relaxations, which therefore create no
    Q-charge (agent-07 minor).
  - A Q-root is never inserted into D by FindPivots.
- (G5) Σ_X |S_X| ≤ (L+1)N: full S ⊆ U, partial |S| < |U|/t.
- (G6) Σ over layers of full-call foreign leaves ≤ (L+1)N; Σ_X p_X ≤ 2(L+1)N/(k−1) + Σ_{partial} |S_X| (5.2).
- (G7) Merge total O(#calls + m + Σ|S| + Σ_{l≥2} Σ_{partial Y at level l−1} |D_Y|/M_{l−1}).
  - [agent-07 P-2, block-walk accounting] Merge at a level-l call walks the child's blocks and absorbs every walked block into a group,
    so each walked block is DESTROYED. Total walk work = O(#blocks ever created) = O(#splits + #Pull remainders + #groups).
    - (v1.6, agent-02 R-1/R-3) Splits happen only in Pull's lazy front preparation. They are paid by the potential Ψ of §3.4, since a
      full Pull pays M. The eager-split count "#splits ≤ Σ #inserts/(M/2)" of v1.5 described a structure that is not implemented.
    - #Pull remainders ≤ #pulls ≤ #calls.
    - #groups ≤ #merges + Σ_l (live entries bubbled into level l)/(M_l/3).
    - Live bubbled entries per layer ≤ Σ_{partial Y} (|S_Y| + δ|U_Y|) ≤ N + δN.
    - Spliced groups go on the separator stack at O(1) each; there is no tree (v1.6, R-3).
    - The formal route does not use this block count: it uses the family potential and bmsspDL_tele_top (§3.4).
    - Base conversions (the leftover Inserts at base returns, prepaid by the heap charge) are O(Σ_{base} (|S| + δ|U|)) = O(δN + N).
  - Merge total: O(#calls + #inserts + m + δN/t) = O((L+1)N + m).

### 5.6 Summation
T_core
 = O( Σ_X [ k(|U_X| + |O_X|) + (t/k)(|U_X| + |O_X|) + |U_X| ]    (T0–T3, T1', T6 over all calls; 5.2 for p)
      + k^2 Σ|Q_X|                                                (failed searches)
      + (t + lg δ)·m                                              (G2: insertion events)
      + t·(Σ p + m)                                               (T5 via 5.3; the p term is already inside the first line)
      + (N + m)·lg(tδ)                                            (base calls)
      + (L+1)N + m )                                              (Merge, deletions, BM.27)
 = O( (L+1)·N·(k + t/k) + k^2(m + 1 + N L/t) + m(t + lg(tδ)) )      [(G4) in-degree-free]
With k = ⌈√t⌉ (k^2 ≤ 2t, t/k ≤ √t):
 T_core = O( N·(lg N/t + 1)·√t + m·t + m·lg(tδ) ) = O( N lg N/√t + m t + m lg(tδ) + N√t ).
### 5.7 Formal counterparts (v1.3; the Lean names of the counters of CostAggregate.CallCounters)
- Fo X := tv_X \ U_X, the FindPivots tree vertices outside the returned set (Frontier/CHD/FPForeign.lean, foOf).
  - Foreign leaves of a full call lie in H(X) = [B_low(X), B_X): foOf_range, from agent-05's F2 (fpC_foreign).
  - Valid.foreign_level (counters_foreign_level), Valid.full_p (counters_full_p) and Valid.partial_Fo (counters_partial_Fo) are
    proved from it.
- Homes (Frontier/Homes.lean, Density.Ranges.home). At a call X, v ∈ U_Y for a child Y is homed at Y. A v ∉ U_X is homed at the child
  whose handled range contains dis(v). Otherwise v is unhomed.
  - home_of_mem and home_of_range give uniqueness via sibling disjointness.
  - cross_of_home_ne: different homes with both ends returned means no child contains both.
  - split_of_home_ne: different homes with the head foreign means the tail SPLITS dis(head) at X.
- Cr X / Be X (Frontier/CHD/CrBe.lean, crOf/beOf) are the graph edges of the different-home tree edges of a FULL call, each tree edge
  represented by a graph edge whose source (the extracted end) is in U_X. Cr X has head in U_X; Be X has head a foreign leaf.
  - Valid.cr_cross: crOf_cross.
  - Valid.be_total: beOf_total, via Density.Ranges.beta_sum_le.
- 5.3(i) g_j ≤ 1 + c_j, combinatorial core (Frontier/CHD/Reselect.lean):
  - colors_le_measure: in a rooted list with a strictly increasing parent measure, #colours ≤ 1 + #bichromatic parent edges;
  - pieces_colors_le: the same on PT pieces;
  - groups_colors_le: summed over MakePivots groups, ≤ #groups + #bichromatic tree edges;
  - bich_le_crbe: bichromatic tree edges of a full call ≤ |Cr X| + |Be X|.
- O10, Valid.cost_le (Frontier/CHD/CostLe.lean, tracedCounters_cost_le). tracedCounters is agent-01's Log.countersC (BMTrace) with
  Fo = foOf, Cr = crOf, Be = beOf and Del = delOf.
  - Per-record budgets come from callC_cost/bmsspC_reccost (CostLog). The record facts come from bmsspC_recall (RecFPLog).
  - The markings bound is 5.3(i) (mkOf_full_le) for full calls and mkOf_le_S for partial calls.
  - |W| ≤ k|Q| is fpC_W_card (FPWQ). #tv ≤ |U| + |Fo| holds because the forest is nodup.
  - The arithmetic is budget_arith.
  - Transfers for foreign_level, full_p, partial_Fo, cr_cross, be_total and del_disj are also proved.
- O22, the Q-witness (Frontier/CHD/QWit.lean, QWitProv.lean, QWitValid.lean).
  - evOf r are the inserting-capable events: J; W' edges below B; base edges out of U below B.
  - ev_unique (G2): an edge is an event of at most one record, since the event windows along the chain of calls containing its tail
    are disjoint.
  - Events are anchored (a jump at the returning child, an own event at the record); Before means "ended before the call started".
  - LocalProv: a frontier member of a sub-call is in the parent's S \ Q, or is the head (≠ s) of an event anchored in an earlier child
    subtree, or is in S of a call of such a subtree. It is proved for every BMSSPC derivation (bmsspC_prov) by a key-provenance
    invariant of the loop store. Two facts drive it: a valid relaxation never inserts s, and eval ≤ ext ∘ d under WalkInv.
  - qwit_of_prov / bmsspC_qwit: wit X v is the edge of an event anchored strictly inside the nearest full proper ancestor with
    v ∈ Q, which ended before X started. This gives the Valid fields wit_mem, wit_inj (by G2) and src_once (CostAggregate.Valid). QWitValid restates them for tracedCounters.
- O12, (B4') Log side (Frontier/CHD/TraceSize.lean, wB_sum_le). Σ over the log of the own-placement weights
  (3|S| + |J| + |Wr| for recursive records, |S| + |Eout U| for base records) is ≤ (3(L0+1) + 3δ)·|U_root|, given |S| ≤ |U|.
- PT at RAM level (Frontier/CHD/PartitionRAM.lean … PartitionRAM5.lean, ptProg_spec).
- (v1.5) The FindPivots tree layer at RAM level (B-L2; agent-03, instantiating agent-09's interface TreeI):
  - ForestRep / FR0 (TreeRAM, TreeRAM7): the forest as linked chains (tr.hd/tr.nx/tr.tl/tr.ln, tree ids, parents fp.par);
  - FH.23 new tree: newTree_spec (TreeRAM2), cost 9|K| + 20;
  - FH.12 contact merge: mergeProg_spec (TreeRAM3–6) refines agent-05's mergeTree — path walk along kpath with re-rooting,
    rest pass K \ path, tail/length update, path clear — cost 33|K| + 40;
  - treeImpl : TreeI (TreeRAM7): grow = if contact then merge else new tree, cost ≤ 41(|K| + 1); every Layer-A fact the RAM code
    needs is derived from agent-05's Search.treeInv, Search.result_info, kpath_spec, growForest_inv;
  - FP-TAIL (TreeRAM8, TreeRAM9): compaction of the chains into the PT layout (compact_forestAt), S/Q bitmaps, ptProg, cleanup
    of fp.fm; fpTail_spec stores exactly forestGroups S Q k trees (relabelled by Fin.val; PartitionMap: Algorithm 5,
    MakePivots and ParentFirst commute with injective relabellings) at cost ≤ 188Σ|T| + 8|S| + 8|Q| + 30 = O(#tv + |S| + |Q|).
  - WFrame: a syntactic frame lemma (word-only statements change only the registers/arrays they name), used for every
    Unchanged footprint of the tree layer.
- (v1.5) CostLe2.fpA_le_of_hext: with hext ≤ c₂(k + 1) (unsorted-array extract-min), fpA ≤ (2(scanC + hins) + c₂ + 2)(k + 1), so
  the constant of Valid.cost_le is independent of k (reviewer OBJECTION 4).

## 6. Parameters and the final bound (author agent-03)
- Constants: t_0 := 16. Then k := ⌈√t⌉ satisfies 3k ≤ t and k ≥ 4 for t ≥ t_0.
- Small inputs (v1.5, D4). For lg n < 16, and outside the density window (m > n·F(n)), the program runs the verified Bellman–Ford
  fallback (Frontier.CHD.Dispatch, BF.prog, cost ≤ 9(n+1)(m+1)); for lg n < 16 this is ≤ 9·2^16·(m+1) = O(m + 1). There is no
  Dijkstra fallback.
- t := tF(cn, cm) = max(16, tpar(cn, cm)) with lgN² ≤ t³·dd² (CostSkeleton.tF_spec; dd the density), i.e. t ≈ (lg N/d)^{2/3} =
  (N lg N/m)^{2/3} up to rounding; k := ⌈√t⌉ (kF); L := ⌊lg N/t⌋ + 1 (LF; v1.5, D6). These are computed by the verified parameter
  program (L6/Params paramsProg, L6/LevelTab levelTab: cp.tau[l] = t³2^{lt}, cp.M[l] = M_l exactly) in O(t + L + lg N) word
  operations.

(A_M) caveat for DS'. Lemma DS' gives Pull O(|S'|) and split O(1) amortized when lg #blocks = O(M_l). In general Pull costs
O(|S'| + lg B_X) and a split O(M_l + lg B_X), where B_X ≤ 3N_X/M_l + 1 and lg B_X = t + O(lg(tδ)).
(A_M) fails only in layers l with t·2^{(l−1)t} < c·(t + lg(tδ)). There are at most 1 + ⌈lg lg(tδ)/t⌉ + 1 of them.
Each such layer has ≤ N pulls (each pull feeds a child with nonempty U, and a layer's U's are disjoint). So the extra is
O(N·(t + lg(tδ))·(2 + lglg(tδ)/t)) = O(N t + m lg(tδ)).
For the last step: after P3, m ≥ Nδ/4. Also lglg(tδ) ≤ δt, so N·lg(tδ)·lglg(tδ)/t ≤ 4·m·lg(tδ).

Final bound. §2 costs O(n + m + m lg δ). §5.6 with the (A_M) extra, and P5 output O(n + m), give
    T = O( n + m + m·lg δ + N·lg N/√t + m·t + m·lg(t) ).
- Case t = ⌈(N lg N/m)^{2/3}⌉ ≥ t_0. Then N lg N/√t = O(m^{1/3}(N lg N)^{2/3}) and m t = O(m^{1/3}(N lg N)^{2/3}).
  Put x := N lg N/m ≥ 1. Then m lg t = O(m lg(2 + x)) and m·x^{2/3} = m^{1/3}(N lg N)^{2/3}. Since lg(2 + x) = O(x^{2/3}),
  m lg t is O(m^{1/3}(N lg N)^{2/3}).
- Case t = t_0. Then m ≥ N lg N / t_0^{3/2}, so N lg N/√t = O(m) and T = O(m lg δ + m).
- With N = O(n), δ = O(m/n + 1) and lg δ = O(lg(2 + m/(n+1))), this gives T = O(TCHD(n,m)) for EVERY (n,m), where
  TCHD(n,m) := n + m + m·lg(2 + m/(n+1)) + m^{1/3}(n lg(n+2))^{2/3}. ∎

Lean target form (what the formal proof uses). The frozen statement is CHDTarget F (agent-10's Frontier/GateC.lean), with
F(n) = ⌊⌊log₂ n⌋^{3/4}⌋.
- Dispatcher (Dispatch.dispatchProg, dispatch_runs). It runs verified Bellman–Ford (cost ≤ 9(n+1)(m+1)) when log₂ n < 16 or
  ⌈m/n⌉ > F(n), and C-HD otherwise. For log₂ n < 16 and m ≤ n·F(n), the Bellman–Ford cost is ≤ 9·2^16·(m+1) ≤ 9·2^16·Tchd; this
  is the term 65536·9 of C.
- On the C-HD branch the core gets the density bound dd(cn, cm) ≤ F(cn) + 1 (L6 CoreIn.dens). It is used in exactly one place,
  agent-06's master cost (Frontier/CHD/MasterCost.lean, Part 2).
  - There the recursive DS' insertion charge satisfies 211·log₂(8ρ+8) + 441 ≤ 3826·t (mc_ins_le), via lgN ≤ 16·t⁶ (mc_lgN_le).
  - Here ρ = (3(L0+1) + 3δ)·2t²·2^t, and Emax_l ≤ ρ·M_l at every recursive level l ≥ 1, where Emax_l is the level-l entry bound
    (BMTeleChd.chdEmax_le). So the log₂(#blocks) part of an insertion is O(t) on the branch.
  - This replaces the (A_M) case analysis above in the formal proof. The level-0 conversion charge needs no density bound
    (mc_ins0_le).
- The other parameter facts hold for every input, with t = tF = max(16, tpar):
  - k(k+1) ≤ 2t (mc_kk);
  - lgN + 1 ≤ LF·t (mc_lgN_lt);
  - τ(LF) > 2n (mc_tau_top);
  - lgN² ≤ t³·dd² (CostSkeleton.tF_spec).
- So the formal proof has no separate case t = t_0 and no threshold n_0: the bound C·Tchd holds on every input of the branch,
  with the explicit C. Also Tnat ≤ 33·Tchd for every n ≥ 1 (Tnat_le_Tchd), which prices the preallocation of §7.1.
- Theorem 3 extends the bound beyond F(n) by the (A_M) case analysis above. That extension is not formalized.

Gate-C regime. At d = m/n = lg^α n with 1/2 ≤ α < 1 (bound expressions; only upper bounds on running times are claimed):
- C-HD's certified bound is Tchd(n, m) = Θ(n lg^{(2+α)/3} n + n lg^α n · lg lg n) = o(n lg n).
- DMSY26's bound is Θ(n lg^{α+1/2} n) ≥ n lg n, and Dijkstra's bound is Θ(n lg n).

## 7. Space
### 7.1 Formal (what is proved)
- In the model, space ≤ cost for every run (RAMAudit.run_space_le_cost). So the formalized program uses space O(Tdisp_F(n, m)).
- The formalized implementation (agent-09's dProSpecC; agent-04's DLayer instance) allocates the DS' arrays once, before the top
  call, and never re-allocates them: every D operation is allocation-free. It never reclaims stale entries.
  - Capacities:
    - use capacity ucap = 12·kmN·Tnat + 2, with Tnat = cn + cm·(tF + lg(dd+1) + 3) and kmN = kmaster(1,1,1000);
    - entry pool, block records and block stack: ucap + 2 cells each;
    - level tables LF + 2 cells, key lists n + LF + 2, live map n, select scratch 6·ecap + 60.
  - ucap suffices because the spine threads the budget use + 2·lg.cost ≤ ucap (CallSpec), and lg.cost ≤ kmaster·Tchd ≤
    6·kmaster·Tnat at the top.
  - The allocation costs O(Tnat) = O(Tchd). RAM space is at most RAM cost, so it is within the time bound.
  - Hence on the C-HD branch the space of the formalized program is Θ(Tnat) = Θ(n + m·(t + lg d)). The upper bound is formal
    (space ≤ cost); the lower bound is read off the program text (dPro allocates arrays of ucap + 2 cells) and is not a theorem.
    This is superlinear whenever t = (lg n/d)^{2/3} → ∞, i.e. in the whole Gate-C window. The formal Gate-C statement does not
    constrain space.

### 7.2 Sketch, NOT formalized: an O(n + m)-space variant (inherits B1 S4.10/S5 §5)
- A reallocating implementation would reclaim stale entries and blocks when structures are destroyed.
- Graph, labels, versions, stamps and pointers: O(n + m).
- Live D's: at most one per call on the recursion stack, O(N_X) each, geometric in the level. Plus stale entries, bounded by the
  inserts since the structure's creation. O(n + m).
- FindPivots state: O(k) plus trees. Trees are vertex-disjoint and freed at return.
- Total O(n + m). This variant is not the formalized program.

## 8. Novelty (agent-03 search log, 2026-09-20)
Searched sources:
- the four supplied primary papers (2504.17033v2 DMM+25, 2602.07868v2 DMSY26, 2609.15247 KR26, 2609.04825v1 Cai);
- B1 draft §8 novelty log (Semantic Scholar citers of DMSY26: KR26, Cai, 2609.14126, 2607.19346);
- a web search (US index) for directed comparison–addition SSSP beating Dijkstra at moderate density: no hit beyond DMM+25/DMSY26.
Findings.
- DMSY26 Thm 1.1 gives O(m√lg n + √(mn lg n lglg n)). This bound is Θ(n d √lg n) ≥ n lg n for d ≥ √lg n.
  Its footnote 1 says the algorithm "also works when δ > log k", but it analyses FindPivots as k(δ + log k) per search. At δ = d that
  gives Σ|Q|·k·d ≥ m k d, and the per-level scans give n' L δ = m L. Neither yields o(n lg n) for d ≥ √lg n (agent-03 notes §1: the
  balance pivots·failed ≥ m²lg n in DMSY26's accounting). So C-HD is not implied by DMSY26 as written.
- NEW elements:
  - (i) invalid targets become counted, unexplored LEAVES (agent-09), which makes a local search O(k²) independent of degree;
  - (ii) permanent deletion of edges into targets below L_X (agents 03/08/09/10; Lemma L);
  - (iii) the per-layer foreign-leaf bound via disjoint handled ranges, and home charging for contact-through-leaf re-selections
    (agent-03; §5.1–5.3);
  - (iv) the block-linking DS' Merge, whose total volume is independent of δ (agent-09; also agents 02/03/10);
  - (v) the parameter regime k = √t, t = (lg n/d)^{2/3}.
- KR26 Sec. 4 lists the directed extension of the undirected density bound as OPEN, via directed BundleDijkstra. C-HD does not solve
  that problem. It gives a weaker but NEW directed density improvement by a different mechanism.
- Undirected O(√(mn lg n)) (DMSY23/Yan26, KR26) is not comparable: undirected graphs only.
- Independent logs: agent-09 /research/agents/agent-09/work/NOVELTY_LOG_CHD.md (web queries and hits checked) and agent-07's cross-check
  (board 11:23). Neither found a directed CA bound o(n lg n) at d ≥ c·sqrt(lg n).
- Dated re-run (v1.7, ~22:55): a new primary source was found, 2607.19346 (Hair–Li–Li–Zhang, July 2026). It is a Las Vegas
  randomized m^{1+o(1)} algorithm for real, possibly negative, weights. Reviewer #2 (23:00) notes that it uses real subtraction
  (potentials), so it lies outside the comparison–addition model. It does not pre-empt C-HD. Its published analysis carries a factor
  2^{Ω(√lg n)}, from a base case Õ(m·k) with k up to 2^{√lg n}. The factor is at most exp(O(√lg n·lglg n)), from at most √lg n
  recursion levels with O(log n)^i instances at level i. So the best bound known from it is ω(n lg n) throughout the window
  (non-pre-emption confirmed independently by agents 02, 04, 05, 07, 09 and 10). Details are in the novelty log.
- Dated re-run (v1.5): /research/agents/agent-03/work/paper/NOVELTY_LOG_2026-09-20.md (seven web queries, the four primary
  sources re-read, Cai's Theorem 9.2 checked: worst case Ω(m√lg m) at d ≥ √lg n). No conflicting result found. Repeat
  immediately before any final claim. B1's Cor. S4-G is only o(DMSY26) for m/n = o(√lglg n), so it does not overlap.

## 9. Formal verification and honest limitations (v2.0, 2026-09-20 ~23:15 UTC)
### 9.1 The formal chain (frozen build #33; all modules std axioms, no sorry, no project axiom)
- Top: Final.chd_gateC : Frontier.GateC ⇐ chd_CHDTarget : CHDTarget F ⇐ chd_exact_within.
  - chd_exact_within holds for the closed program chdProgram, via L6/FinalGen.chdProg_of_DLayer, from concrete instances only.
  - All name side conditions are decided by `decide +kernel`.
- Exactness and cost: MasterSpec (L6.masterSpec_of_goodP, GoodP by goodP_chdP; OBJECTION 4 resolved through fpA_le_of) and the
  RAM refinement (the spine).
- The spine is a bounded level induction, agent-10's L6.LevelRoute.callSpec_of_levels (∀ l ≤ LF, from level 0 and the step
  l → l+1 for l < LF), over agent-08's contract RamSpine.CallSpec (SpineLoop.lean). It uses ONE constant K at every level, and
  the D-layer use grows by at most 2 per unit of Layer-A cost. (agent-08's unbounded SpineLevels.callSpec_all is not on the route.)
  - Base: agent-03's callSpec_zero. It covers the heap base case, the pointer pass, the level-0 DS' conversion and the heap clear.
  - Step: agent-01's body_spec / callSpec_succ, composed of:
    - agent-09's FindPivots: fpB_inst, transported to the raw text fpAtRaw (BL2AtRaw, fpAt_eq_raw) and supplied as L6.hFP_of
      (BL2Step);
    - agent-01's prologue (pro_spec);
    - agent-08's main loop: the step's loop input is L6.hLoop_of_parts (SpineLoopInst), i.e. loop2_spec with agent-06's
      postSpec through RamSpine.loopSpecB_of_loop2 / postHalf_cmpTT;
    - agent-03's finalization (fin_spec, fin_spec_stmt).
  - The D layer: agent-04's DLayerF.DLf, with agent-02's merge and agent-05's pull.
  - The top: agent-10's dispatcher, L6 preprocessing, prologue, allocations (agent-09's dProSpecC) and output.
- The degenerate case H.m = 0 is a runtime branch `gM = 0` of coreTop (complete_init_of_m0).
- Extras, corollaries of the frozen Final and outside its import closure (std axioms; verified by agent-10 at 23:03 UTC, and
  FinalCompare by agent-03 at 23:25). They enter the root at the post-audit build #34:
  - FinalExtras.chd_space (agent-01) and FinalSpace.chd_space_within (agent-05): cost and space ≤ C·Tdisp_F;
  - FinalExtras.chd_auditGateC (Corollary 2'), via agent-09's AuditGateC.chdTarget_imp_auditGateC;
  - FinalCompare.chd_beats_known (agent-01, 23:13): o(·) of the Dijkstra, DMM+25 and DMSY26 bound expressions along μ (§1);
  - FinalRaw (agent-09, 2d53cb7d): chdProgramRaw, the program as one literal term, and chdProgramRaw_eq :
    Final.chdProgram = chdProgramRaw := rfl. Both are axiom-free.
- Paper-to-code: /research/final/THEOREM_MAP.md, assembled by agents 07/09 from the owners' rows (agent-03's are in
  PAPER_TO_CODE_agent03.md).

### 9.2 Limitations (stated so that nothing is overclaimed)
1. **Formal density range.** The kernel-checked bound is C·Tchd only for m ≤ n·F(n) with F(n) = ⌊⌊log₂ n⌋^{3/4}⌋. Outside that
   range, the formalized program uses Bellman–Ford, with the formal bound C·(n+1)(m+1).
   - The Gate-C statement is along μ(n) = n·⌊ln(n+2)^{3/4}⌋, which lies inside the range. The strong form (Corollary 2')
     covers every graph with m ≤ n·max(1, F(n)), and nothing denser.
   - The paper's claim for F(n) < d = o(lg n / lglg n) (Theorem 3) is NOT formalized.
2. **Space.** Formally, space ≤ time: the implementation preallocates Θ(Tnat) cells. The O(n + m)-space variant (§7.2) is a sketch.
3. **Constants.** The constant C = bodyC KcC + 65536·9 + 100 = 2·KcC + 1500 + 65536·9 + 100 ≈ 1.96·10^{24} is astronomically
   large (KcC ≈ 9.80·10^{23}; dKd(12·kmN) = 23·12·kmN + 300 ≈ 2.82·10^{12}; agrees with REVIEW_1 §9.5).
   - KcC = (KC + 13000 + 34·(100 + dKd(12·kmN)))·(kmN + 1) + 250 (Final.KcC), where KC = 210000 is the spine's
     one-per-level constant K (RAM cost per unit of Layer-A cost).
   - kmN = kmaster(1,1,1000) = 5100·35784·56 ≈ 1.02·10^{10} is the Layer-A master constant (L6/DCap.kmN; kmN_le: ≤ 10^{11}).
   - The result is purely asymptotic and makes no practical claim.
4. **Word size.** The machine's word cap is (n+m+2)^{e+1} with e = 160, i.e. O(log n)-bit words (e is a constant). Reals are only
   compared and added.
5. **Determinism and model.** The program is deterministic and works in the comparison–addition model. It is compared with the
   best known directed bounds in that model. 2607.19346 does not compete in the window (§8): it is Las Vegas randomized, runs in
   m^{1+o(1)} with an implicit m^{o(1)}, and uses real subtraction (potentials), so it is outside comparison–addition; the last
   point is per reviewer #2.
6. **Reviews and reproduction** (state at 00:00 UTC, 2026-09-21).
   - agent-09's final audit and kernel replay of frozen #33 passed at 23:37: 18,994 constants, 266 modules, std axioms.
   - agent-07's fresh-copy rebuild passed (2548 jobs, 0 HARD tokens), with an own kernel replay of 18,994 constants.
   - REVIEW_1 (agent-07, 23:57): ACCEPTED for Gate (C), with limitations.
   - agent-02's fresh-copy rebuild and REVIEW_2 are pending.
   - agent-10 integrates the final/ files only after all of these pass.
7. **Novelty.** See the dated log NOVELTY_LOG_2026-09-20.md, last re-run ~22:55 UTC (§8). The web index is US-only and may lag arXiv.
8. **Size of the gain.** At d = m/n = lg^α n (1/2 ≤ α < 1), C-HD's certified bound is below Dijkstra's Θ(n lg n) bound by the
   factor lg^{(1−α)/3} n (§6). Only upper bounds are proved; no lower bound on C-HD's running time is claimed.
   That is lg^{1/12} n along the formal profile μ (α = 3/4), and at most lg^{1/6} n (α = 1/2). It is a density-regime (Gate C)
   result, not a Gate A/B result.
   - On sparser graphs nothing new is claimed. For α ≤ 1/4, DMSY26's O(m√lg n + √(mn lg n lglg n)) = O(n lg^{α+1/2} n) is at least as
     small as C-HD's bound Tchd = Θ(n lg^{(2+α)/3} n) (for α > 0). As bound expressions, C-HD's is smaller than DMSY26's exactly
     when α > 1/4, and smaller than Dijkstra's when α < 1.
9. **Undirected graphs.** For undirected graphs, the known O(√(mn lg n)) (DMSY23/Yan26; KR26) is stronger than Tchd throughout
   the window: (1+α)/2 < (2+α)/3 for α < 1. C-HD's improvement is for directed graphs only.
10. **Where the C-HD code runs.** The C-HD branch runs only for log₂ n ≥ 16 and ⌈m/n⌉ ≤ F(n). For log₂ n < 16 the program runs
    Bellman–Ford, but the formal bound there is still C·Tchd whenever m ≤ n·F(n), through the term 65536·9 of C (§6).
